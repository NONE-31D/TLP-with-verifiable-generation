use core::time;
use std::collections::hash_map::DefaultHasher;
use std::fs::File;
use std::fs::OpenOptions;
use std::hash::Hasher;
use std::io::Write;
use std::hash::Hash;

use std::{marker::PhantomData, time::Instant};
use std::env;


use ark_crypto_primitives::snark::{CircuitSpecificSetupSNARK, SNARK};
use ark_r1cs_std::{
    prelude::*,
    fields::fp::FpVar, 
    R1CSVar,
};
use ark_relations::r1cs::{ConstraintSynthesizer, ConstraintSystemRef, SynthesisError, Namespace, ConstraintLayer};
use ark_bls12_381::{
    Bls12_381, Fq, Fr,
};
use ark_ec::{
    pairing::Pairing,
    short_weierstrass::{Projective, SWCurveConfig},
};
use ark_ff::{
    field_hashers::{DefaultFieldHasher, HashToField},
    Field, PrimeField, 
    BigInteger, BigInt,
};
use ark_groth16::{
    Groth16, 
};
use ark_std::{
    rand::{Rng, RngCore, SeedableRng},
    test_rng, UniformRand,
};

use rug::{Assign, Integer};

use rsa::bignat::{
    constraints::{
        BigNatCircuitParams,
        BigNatVar
    },
    BigNat, fit_nat_to_limbs, nat_to_limbs, limbs_to_nat, nat_to_f, f_to_nat,
    
};


use num_prime::RandPrime;
use num_bigint::{BigUint, };

// util쪽으로 뺄 지 고민중... 
fn u64_vec_to_field_vec<E> (u64_limbs: &Vec<u64>) -> Vec<E::ScalarField> 
where E: Pairing,
{
    u64_limbs.iter()//.rev()
    .map(|int64| <E as Pairing>::ScalarField::from(*int64))
    .collect::<Vec<E::ScalarField>>()
}


// fn time_analysis(time_list:Vec<Instant>) -> () {
//     let mut prev = time_list[0];
//     for (i, time) in time_list.iter().enumerate() {
//         let gap = *time - prev;
//         println!("{i}st gap: {:?}", gap);
//         prev = *time;
//     }

// }



const lambda: usize = 2048;
const test_lambda: usize = 1024;

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct BigNat512TestParams;

impl BigNatCircuitParams for BigNat512TestParams {
    const LIMB_WIDTH: usize = 64;
    const N_LIMBS: usize = lambda/64;
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct BigNatTestParams;

impl BigNatCircuitParams for BigNatTestParams {
    const LIMB_WIDTH: usize = 64;
    const N_LIMBS: usize = test_lambda/64;
}

trait BigIntTrait<const N: usize> {
    fn to_u64_le(&self) -> Vec<u64>;
}

impl<const N: usize> BigIntTrait<N> for BigInt<N> {
    fn to_u64_le(&self) -> Vec<u64> {
        let mut array_map: Vec<u64> = self.0.iter().map(|limb| limb.clone()).collect();
        array_map.reverse();
        array_map

    }
}



trait BigNatTrait<ConstraintF: PrimeField, P: BigNatCircuitParams> {
    // 아 네이밍센스 실화인가 에반데 
    fn alloc_from_u64_limbs(
        cs: impl Into<Namespace<ConstraintF>>,
        u64_limbs: &Vec<u64>,
        word_size: BigNat,
        mode: AllocationMode,
    ) -> Result<BigNatVar<ConstraintF, P>, SynthesisError>;

    fn alloc_from_limbs(
        cs: impl Into<Namespace<ConstraintF>>,
        limbs: &Vec<ConstraintF>,
        word_size: BigNat,
        mode: AllocationMode,
    ) -> Result<BigNatVar<ConstraintF, P>, SynthesisError>;
}

impl<ConstraintF: PrimeField, P: BigNatCircuitParams> BigNatTrait<ConstraintF, P> for BigNatVar<ConstraintF, P> {
    fn alloc_from_u64_limbs(
        cs: impl Into<Namespace<ConstraintF>>,
        u64_limbs: &Vec<u64>,
        word_size: BigNat,
        mode: AllocationMode,
    ) -> Result<BigNatVar<ConstraintF, P>, SynthesisError> {
        let limbs = u64_limbs.iter().rev()
            .map(|int64| ConstraintF::from_bigint(ConstraintF::BigInt::from(*int64)).unwrap())
            .collect::<Vec<ConstraintF>>();
        Self::alloc_from_limbs(cs, &limbs, word_size, mode)
    }

    fn alloc_from_limbs(
        cs: impl Into<Namespace<ConstraintF>>,
        limbs: &Vec<ConstraintF>,
        word_size: BigNat,
        mode: AllocationMode,
    ) -> Result<BigNatVar<ConstraintF, P>, SynthesisError> {
        assert_eq!(limbs.len(), P::N_LIMBS);
        let limb_vars = Vec::<FpVar<ConstraintF>>::new_variable(
            cs,
            || Ok(&limbs[..]),
            mode,
        )?;
        Ok(BigNatVar {
            limbs: limb_vars,
            value: limbs_to_nat::<ConstraintF>(limbs, P::LIMB_WIDTH),
            word_size: word_size,
            _params: PhantomData,
        })
    }
}

// scheme-relationR에서 사용될 서킷
// relationR(S_2, CT; S_3, m) { // where CT=(S_1, C)
//   S_2 = f_{tau+1}(S_3) // S_2 = S_3^2
//   C = S_3 + m mod |F|
// }
#[derive(Clone)]
#[derive(Debug)]
struct VDCCircuit<F: Field> {
    S_2: Option<Vec<F>>,
    CT: Option<(Vec<F>, Vec<F>)>,
    S_3: Option<Vec<F>>,
    m: Option<Vec<F>>,
    N: Option<Vec<F>>
}

impl<ConstraintF: Field + PrimeField> ConstraintSynthesizer<ConstraintF> for VDCCircuit<ConstraintF> {
    fn generate_constraints(
        self,
        cs: ConstraintSystemRef<ConstraintF>,
    ) -> Result<(), SynthesisError> {
        let S_2_var = BigNatVar::<ConstraintF, BigNat512TestParams>::alloc_from_limbs(
            ark_relations::ns!(cs, "S_2"),
            &self.S_2.clone().unwrap(),
            BigNat::from(1) << BigNat512TestParams::LIMB_WIDTH as u32 - 1,
            AllocationMode::Input,
        ).unwrap();

        let (S_1, C) = self.CT.unwrap();
        let S_1_var = BigNatVar::<ConstraintF, BigNat512TestParams>::alloc_from_limbs(
            ark_relations::ns!(cs, "S_1"),
            &S_1,
            BigNat::from(1) << BigNat512TestParams::LIMB_WIDTH as u32 - 1,
            AllocationMode::Input,
        ).unwrap();

        let C_var = BigNatVar::<ConstraintF, BigNat512TestParams>::alloc_from_limbs(
            ark_relations::ns!(cs, "C"),
            &C,
            BigNat::from(1) << BigNat512TestParams::LIMB_WIDTH as u32 - 1,
            AllocationMode::Input,
        ).unwrap();

        let S_3_var = BigNatVar::<ConstraintF, BigNat512TestParams>::alloc_from_limbs(
            ark_relations::ns!(cs, "S_3"),
            &self.S_3.clone().unwrap(),
            BigNat::from(1) << BigNat512TestParams::LIMB_WIDTH as u32 - 1,
            AllocationMode::Witness,
        ).unwrap();

        let m_var = BigNatVar::<ConstraintF, BigNat512TestParams>::alloc_from_limbs(
            ark_relations::ns!(cs, "m"),
            &self.m.unwrap(),
            BigNat::from(1) << BigNat512TestParams::LIMB_WIDTH as u32 - 1,
            AllocationMode::Witness,
        ).unwrap();

        let n_var = BigNatVar::<ConstraintF, BigNat512TestParams>::alloc_from_limbs(
            ark_relations::ns!(cs, "m"),
            &self.N.unwrap(),
            BigNat::from(1) << BigNat512TestParams::LIMB_WIDTH as u32 - 1,
            AllocationMode::Witness,
        ).unwrap();
        let mut vec = vec![0u64;lambda/64 - 1];
                vec.extend_from_slice(&vec![2u64]);
                
        // let two_const = BigNatVar::<ConstraintF, BigNat512TestParams>::alloc_from_u64_limbs(
        //     ark_relations::ns!(cs, "n"),
        //     &vec,
        //     BigNat::from(lambda/64),
        //     AllocationMode::Constant,
        // ).unwrap();

        // let mut vec1 = vec![0u64;lambda/64 - 1];
        //         vec1.extend_from_slice(&vec![1u64]);
                
        // let one_const = BigNatVar::<ConstraintF, BigNat512TestParams>::alloc_from_u64_limbs(
        //     ark_relations::ns!(cs, "n"),
        //     &vec1,
        //     BigNat::from(lambda/64),
        //     AllocationMode::Constant,
        // ).unwrap();

        // relation R - R_1 체크
        let result1 = S_3_var.mult_mod(&S_3_var, &n_var).unwrap();  
        // println!("S_3_var {:?}", &self.S_3.clone().unwrap());
        println!("result1 {:?}", result1.value());
        println!("S_2_var {:?}", S_2_var.value());
        S_2_var.enforce_equal(&result1).unwrap();

        // relation R - R_2 체크
        let result2 = m_var.add_mod(&S_3_var, &n_var).unwrap(); //.mult_mod(&one_const, &n_var).unwrap();
        C_var.enforce_equal(&result2).unwrap();
        // println!("result2 {:?}", result2.value());
        // println!("C_var {:?}", result2.value());
    
    
        println!("Number of constraints: {}", cs.num_constraints());

        // println!("result2 {:?}", result2.value());
        // println!("C_var {:?}", C_var.value());
        // println!("C_var {:?}", C_var.value());

        Ok(())
    }
}



fn vdc_test(
    should_satisfy: bool,
    tau: u32,
    _lambda: usize,
) {
    println!("===== Verifiable Delay Function - Algorithm 2 ");

    let mut rng = rand::thread_rng();

    let mut f = OpenOptions::new().append(true).open("data7").expect("cannot open file");
    f.write_all(format!("\n\nlambda bit: {:?}\n", lambda).as_bytes()).expect("write failed");

    println!("MODULUS_BIT_SIZE: {:?}", Fr::MODULUS_BIT_SIZE);


    // setup time analysis 
    // let mut set_time_list:Vec<Instant> = vec![];

    // SETUP 
    println!("Setup >>>>>>>>>>>>>>>>>");
    let start_time = Instant::now();
    // let tau = 100u32;  // 이거 바꿔서 성능실험 필요 
    f.write_all(format!("tau: {:?}\n", tau).as_bytes()).expect("write failed");
    println!("{:?}", tau);

    // set_time_list.push(Instant::now());

    // 이거 128비트 람다로 바꿔서 두개 뽑고 곱하기.. 
    // 여기서 시간 튀는게 너무 심함. >> 표준 시간으로 실험데이터 정리해서 넣기 
    let p: BigUint = rng.gen_prime(lambda/2, None);
    let q: BigUint = rng.gen_prime(lambda/2, None);
    // set_time_list.push(Instant::now());

    // let mut p = Integer::new();
    // let mut q = Integer::new();

    let phi_N = (p.clone() - 1u32) * (q.clone() - 1u32);
    f.write_all(format!("bit of phi_N: {:?}\n", phi_N.bits()).as_bytes()).expect("write failed");

    // set_time_list.push(Instant::now());
    let mut N: BigUint = p*q; 
    f.write_all(format!("bit of N: {:?}\n", N.bits()).as_bytes()).expect("write failed");
    // set_time_list.push(Instant::now());
    // N.set_bit(lambda as u64 - 1, true);
    let bit_size: u64 = lambda as u64;
    // set_time_list.push(Instant::now());
    // println!("bit_size: {:?}", bit_size);
    // println!("Fr modulus bit_size: {:?}", Fr::MODULUS_BIT_SIZE);

    let start_time = Instant::now();
    let m_field = Fr::rand(&mut rng);
    let mut m = BigUint::from(m_field);
    // bits 이용해서 비트사이즈 N의 비트사이즈로 수정 
    m.set_bit(bit_size - 1, true);
    m = m % N.clone();
    // set_time_list.push(Instant::now());
    // println!("m: {:?}", m);

    let g = Fr::rand(&mut rng);
    // println!("{:?}", g);
    // set_time_list.push(Instant::now());
    let two = BigUint::from(2u32);
    let mut two_exp_t: BigUint = BigUint::from(2u32).pow(tau) % phi_N.clone(); 
    let mut two_exp_t_plus_1 = BigUint::from(2u32).pow(tau+1) % phi_N.clone();
    // set_time_list.push(Instant::now());
    // println!("{:?}", Fr::from(2));
    // println!("two_exp_t: {:?}", two_exp_t);
    // println!("two_exp_t * 2: {:?}", (two_exp_t.clone() * 2u32) % phi_N.clone());
    // println!("two_exp_t + 1: {:?}", two_exp_t_plus_1);

    let mut P_1 = BigUint::from(g);
    // set_time_list.push(Instant::now());
    let mut P_2 = P_1.modpow(&two_exp_t_plus_1, &N);
    // set_time_list.push(Instant::now());
    let mut P_3 = P_1.modpow(&two_exp_t, &N);

    // P_1.set_bit(bit_size - 1, true);
    // P_2.set_bit(bit_size - 1, true);
    // P_3.set_bit(bit_size - 1, true);
    // set_time_list.push(Instant::now());
    // time_analysis(set_time_list.clone());
    // println!("P_1: {:?}", P_1);
    // println!("P_2: {:?}", P_2);
    // println!("P_3: {:?}", P_3);
    println!("P_2: {:?}", P_2);
    let P_tmp = P_3.modpow(&BigUint::from(2u32), &N);
    println!("P_tmp: {:?}", P_tmp);
    
    let pp = (P_1.clone(), P_2.clone(), P_3.clone());

    let end_time = Instant::now();
    let elapsed_time = end_time.duration_since(start_time);


    f.write_all(format!("Setup time: {:?}\n", elapsed_time.as_micros()).as_bytes()).expect("write failed");

    println!("Generate >>>>>>>>>>>>>>>>>");
    let start_time = Instant::now();
    // 
    let r_bit_vec: Vec<u32> = (0..bit_size / 32).map(|_| rng.gen_range(0..(u32::MAX))).collect();
    let r: BigUint = BigUint::new(r_bit_vec.clone()) % N.clone();
    let s_bit_vec: Vec<u32> = (0..bit_size / 32).map(|_| rng.gen_range(0..(u32::MAX))).collect();
    let s: BigUint = BigUint::new(s_bit_vec.clone()) % N.clone();
    
    let N_vec = N.to_u64_digits();
    let r_vec = r.to_u64_digits();
    let s_vec = s.to_u64_digits();


    // println!("{:?}", N);
    // println!("{:?}", N_vec);
    // println!("{:?}", r_vec);
    //println!("s_vec: {:?}", s_vec);

    let R_1 = P_1.clone().modpow(&r, &N);
    let R_2 = P_2.clone().modpow(&r, &N);

    let mut hasher = DefaultHasher::new();
    R_1.hash(&mut hasher);
    R_2.hash(&mut hasher);
    let c = BigUint::from(hasher.finish()); 
    println!("c in gen {:?}", c);

    let k = r.clone() + c.clone() * s.clone();

    // println!("c_bit: {:?}", c.bits());



    let S_1 = P_1.clone().modpow(&s, &N);
    let S_2 = P_2.clone().modpow(&s, &N);
    let S_3 = P_3.clone().modpow(&s, &N);

    // println!("S_1: {:?}", S_1);
    // println!("S_3: {:?}", S_3);
    println!("S_2: {:?}", S_2);
    let S_tmp = S_3.clone().modpow(&BigUint::from(2u32), &N);
    println!("S_tmp: {:?}\n", S_tmp);
    

    let C = (m.clone() + S_3.clone()) % N.clone();
    // println!("C: {:?}", C);
    // println!("m + s_3: {:?}",   (m.clone() + S_3.clone()) % N.clone());
    // println!("C_bit: {:?}", C.bits());
    

    let mut S_2_vec = S_2.to_u64_digits();
    let mut S_1_vec = S_1.to_u64_digits();
    let mut S_3_vec = S_3.to_u64_digits();
    let mut c_vec = C.to_u64_digits();
    let mut m_vec = m.to_u64_digits();
    let mut n_vec = N.to_u64_digits();

    println!("m_vec: {:?}", m_vec.len());
    // // println!("S_1: {:?}", S_1);
    // println!("S_2_vec{:?}", S_2_vec);
    // // println!("S_3_vec{:?}", S_3_vec);

    let end_puzzle_gen_time = Instant::now();
    f.write_all(format!("Generation time - puzzle gen: {:?}\n", end_puzzle_gen_time.duration_since(start_time).as_micros()).as_bytes()).expect("write failed");


    let vdc_circuit = VDCCircuit {
        S_2: Some(u64_vec_to_field_vec::<Bls12_381>(&S_2_vec)),
        CT: Some((u64_vec_to_field_vec::<Bls12_381>(&S_1_vec), u64_vec_to_field_vec::<Bls12_381>(&c_vec))), 
        S_3: Some(u64_vec_to_field_vec::<Bls12_381>(&S_3_vec)),
        m: Some(u64_vec_to_field_vec::<Bls12_381>(&m_vec)),
        N: Some(u64_vec_to_field_vec::<Bls12_381>(&n_vec)),
    };
    

    let start_groth16_prove: Instant = Instant::now();    
    let (pk, vk) = Groth16::<Bls12_381>::setup(vdc_circuit.clone(), &mut rng).unwrap();
    let start_groth16_prove_setup: Instant = Instant::now();    
    f.write_all(format!("Generation time - setup groth16: {:?}\n", start_groth16_prove_setup.duration_since(start_groth16_prove).as_micros()).as_bytes()).expect("write failed");
    let pvk = Groth16::<Bls12_381>::process_vk(&vk).unwrap();
    let start_groth16_prove_pvk: Instant = Instant::now();    
    f.write_all(format!("Generation time - groth16 making pvk : {:?}\n", start_groth16_prove_pvk.duration_since(start_groth16_prove_setup).as_micros()).as_bytes()).expect("write failed");
    let proof = Groth16::<Bls12_381>::prove(
        &pk,
        vdc_circuit,
        &mut rng,
    )
    .unwrap();
    let end_groth16_prove: Instant = Instant::now();    
    f.write_all(format!("Generation time - groth16 prove: {:?}\n", end_groth16_prove.duration_since(start_groth16_prove_pvk).as_micros()).as_bytes()).expect("write failed");
    
    let end_time = Instant::now();
    let elapsed_time = end_time.duration_since(start_time);

    f.write_all(format!("Generation time: {:?}\n", elapsed_time.as_micros()).as_bytes()).expect("write failed");
    

    // Verify Gen 
    println!("Verify Generation >>>>>>>>>>>>>>>>>");
    let start_time: Instant = Instant::now();    

    // let start_hash: Instant = Instant::now();    
    let mut hasher2 = DefaultHasher::new();
    R_1.hash(&mut hasher2);
    R_2.hash(&mut hasher2);
    let mut c = BigUint::from(hasher2.finish());
    // let fin_hash: Instant = Instant::now();    
    // f.write_all(format!("Verify Generation time - hash: {:?}\n", fin_hash.duration_since(start_hash).as_micros()).as_bytes()).expect("write failed");

    let start_p_1_check: Instant = Instant::now();    
    println!("c in vergen {:?}", c);
    let p_1_k = P_1.modpow(&k, &N);
    let p_2_k = P_2.modpow(&k, &N);

    let r1_s1_c = (R_1 * S_1.modpow(&c, &N)) % N.clone();
    let r2_s2_c = (R_2 * S_2.modpow(&c, &N)) % N.clone();

    assert_eq!(p_1_k, r1_s1_c);
    assert_eq!(p_2_k, r2_s2_c);
    let end_p_1_check: Instant = Instant::now();    
    f.write_all(format!("Verify Generation time - p1, p2 check: {:?}\n", end_p_1_check.duration_since(start_p_1_check).as_micros()).as_bytes()).expect("write failed");


    let mut public_input = vec![];
    
    public_input.extend_from_slice(&u64_vec_to_field_vec::<Bls12_381>(&S_2_vec));
    public_input.extend_from_slice(&u64_vec_to_field_vec::<Bls12_381>(&S_1_vec));
    public_input.extend_from_slice(&u64_vec_to_field_vec::<Bls12_381>(&c_vec));

    let start_groth16_check: Instant = Instant::now();    
    let result = Groth16::<Bls12_381>::verify_with_processed_vk(&pvk, &public_input, &proof).unwrap();
    assert_eq!(should_satisfy, result);
    let end_groth16_check: Instant = Instant::now();    
    f.write_all(format!("Verify Generation time - groth16 check: {:?}\n", end_groth16_check.duration_since(start_groth16_check).as_micros()).as_bytes()).expect("write failed");

    let end_time = Instant::now();
    let elapsed_time = end_time.duration_since(start_time);


    f.write_all(format!("Verify Generation time: {:?}\n", elapsed_time.as_micros()).as_bytes()).expect("write failed");
    

    // Solve
    println!("Solve >>>>>>>>>>>>>>>>>");
    let start_time = Instant::now();
    let mut S_1_prime = S_1.clone();
    // S_1_prime.set_bit(lambda as u64 - 1, true);
    for i in 0..tau {
        // let tmp = S_1_prime.clone();
        S_1_prime = S_1_prime.modpow(&two, &N);// %N.clone(); //(&two, &N);
        // assert_eq!((tmp.clone() * tmp.clone()) % N.clone(), S_1_prime, "panics at {}", i);
    }
    
    assert_eq!(S_1_prime, S_3);
    println!("S_3      : {:?}", S_3);
    println!("S_1_prime: {:?}", S_1_prime);
    
    let m_prime = (C.clone() + N.clone() - S_1_prime.clone()) % N.clone();
    let m_correct = (C.clone() + N.clone() - S_3.clone()) % N.clone();


    println!("m        : {:?}", m);
    println!("m_prime  : {:?}", m_prime);
    // println!("m_correct: {:?}", m_correct);


    let end_time = Instant::now();
    let elapsed_time = end_time.duration_since(start_time);
    f.write_all(format!("Solve time: {:?}\n", elapsed_time.as_micros()).as_bytes()).expect("write failed");

    assert_eq!(S_1_prime, S_3);
    assert_eq!(m, m_correct);

    // let m_correct = if C.clone() > N {C.clone() - S_3.clone()} else {C.clone() + N.clone() - S_3.clone()};

    // println!("{:?}", BigUint::from(m));
    // println!("{:?}", C);
    // println!("m        : {:?}", m);
    // println!("m_prime  : {:?}", m_prime);
    // println!("m_correct: {:?}", m_correct);


    





}





// 기존이랑 같은 relation 증명할 서킷 - 근데 FpVar로만 진행 
#[derive(Clone)]
struct Groth16Circuit <F: Field> {
    S_2: Option<F>,
    CT: Option<(Option<F>, Option<F>)>,
    S_3: Option<F>,
    m: Option<F>,
    N: Option<F>,
}

impl<ConstraintF: Field + PrimeField> ConstraintSynthesizer<ConstraintF> for Groth16Circuit<ConstraintF> {
    fn generate_constraints(self, cs: ConstraintSystemRef<ConstraintF>) -> Result<(), SynthesisError> {
        let mut s_2_value = self.S_2;
        let mut s_2 = FpVar::new_input(cs.clone(), || s_2_value.ok_or(SynthesisError::AssignmentMissing))?;

        let (mut s_1_value, mut c_value) = self.CT.unwrap();
        let mut s_1 = FpVar::new_input(cs.clone(), || s_1_value.ok_or(SynthesisError::AssignmentMissing))?;
        
        let mut large_c =
            FpVar::new_input(cs.clone(), || c_value.ok_or(SynthesisError::AssignmentMissing))?;

        let mut s_3_value = self.S_3;
        let mut s_3 = 
            FpVar::new_witness(cs.clone(), || s_3_value.ok_or(SynthesisError::AssignmentMissing))?;
        
        let mut m_value = self.m;
        let mut m =
            FpVar::new_witness(cs.clone(), || m_value.ok_or(SynthesisError::AssignmentMissing))?;
        
        let mut n_value = self.N;
        let mut n =
            FpVar::new_witness(cs.clone(), || n_value.ok_or(SynthesisError::AssignmentMissing))?;
        
        
        println!("check s3^2 = s^2");
        // let mut r1 = s_3.square().unwrap();
        // r1.

        s_3.square_equals(&s_2).unwrap();
        let res = s_3 + m;
        large_c.enforce_equal(&res).unwrap();
        println!("check finished");

        println!("Number of constraints: {}", cs.num_constraints());

        
        Ok(())
    }
}





// x^2 증명할 서킷 
#[derive(Clone)]
struct SquaringCircuit<F: Field> {
    x: Option<Vec<F>>,
    x2: Option<Vec<F>>,
    o: Option<Vec<F>>,
    n: Option<Vec<F>>,
}

impl<ConstraintF: Field + PrimeField> ConstraintSynthesizer<ConstraintF> for SquaringCircuit<ConstraintF> {
    fn generate_constraints(
        self,
        cs: ConstraintSystemRef<ConstraintF>,
    ) -> Result<(), SynthesisError> {
        let x_var = BigNatVar::<ConstraintF, BigNatTestParams>::alloc_from_limbs(
            ark_relations::ns!(cs, "x"),
            &self.x.unwrap(),
            BigNat::from(1) << BigNatTestParams::LIMB_WIDTH as u32 - 1,
            // BigNat::from(7),
            AllocationMode::Witness,
        ).unwrap();
        let x2_var = BigNatVar::<ConstraintF, BigNatTestParams>::alloc_from_limbs(
            ark_relations::ns!(cs, "x2"),
            &self.x2.unwrap(),
            BigNat::from(1) << BigNatTestParams::LIMB_WIDTH as u32 - 1,
            // BigNat::from(7),
            AllocationMode::Witness,
        ).unwrap();

        let n_var = BigNatVar::<ConstraintF, BigNatTestParams>::alloc_from_limbs(
            ark_relations::ns!(cs, "n"),
            &self.n.unwrap(),
            BigNat::from(1) << BigNatTestParams::LIMB_WIDTH as u32 - 1,
            AllocationMode::Witness,
        ).unwrap();
        
        let o_var = BigNatVar::<ConstraintF, BigNatTestParams>::alloc_from_limbs(
            ark_relations::ns!(cs, "o"),
            &self.o.unwrap(),
            BigNat::from(1) << BigNatTestParams::LIMB_WIDTH as u32 - 1,
            AllocationMode::Input,
        ).unwrap();

        let result = x_var.mult_mod(&x_var, &n_var).unwrap();
        let result2 = x_var.add_mod(&o_var, &n_var).unwrap();
        o_var.enforce_equal(&result).unwrap();
        x2_var.enforce_equal(&result2).unwrap();

        println!("result2: {:?}", result2.value());
        println!("x2_var: {:?}", x2_var.value());


        println!("Number of constraints: {}", cs.num_constraints());

        Ok(())
    }
}



fn groth16_pow_mod_test(
    vec1: Vec<u64>,
    vec2: Vec<u64>,
    vec3: Vec<u64>,
    modvec: Vec<u64>,
    should_satisfy: bool,
) {
    println!("===== groth16 quadratic residue proving ");
    let mut rng = ark_std::rand::rngs::StdRng::seed_from_u64(test_rng().next_u64());
    
    let x = u64_vec_to_field_vec::<Bls12_381>(&vec1);
    let x2 = u64_vec_to_field_vec::<Bls12_381>(&vec2);
    let output = u64_vec_to_field_vec::<Bls12_381>(&vec3); 
    let modulus = u64_vec_to_field_vec::<Bls12_381>(&modvec); 

    let sqrt_circuit = SquaringCircuit {
        x: Some(x),
        x2: Some(x2),
        o: Some(output),
        n: Some(modulus),
    };

    let start_groth16_prove: Instant = Instant::now();   

    let (pk, vk) = Groth16::<Bls12_381>::setup(sqrt_circuit.clone(), &mut rng).unwrap();
    let start_groth16_prove_setup: Instant = Instant::now();    
    println!("Verify Generation time - setup groth16: {:?}\n", start_groth16_prove_setup.duration_since(start_groth16_prove).as_micros());
    let pvk = Groth16::<Bls12_381>::process_vk(&vk).unwrap();
    let start_groth16_prove_pvk: Instant = Instant::now();    
    println!("Verify Generation time - groth16 making pvk : {:?}\n", start_groth16_prove_pvk.duration_since(start_groth16_prove_setup).as_micros());
    let proof = Groth16::<Bls12_381>::prove(
        &pk,
        sqrt_circuit,
        &mut rng,
    )
    .unwrap();
    let end_groth16_prove: Instant = Instant::now();    
    println!("Verify Generation time - groth16 prove: {:?}\n", end_groth16_prove.duration_since(start_groth16_prove_pvk).as_micros());
    
    // println!("{:?}", proof);

    let result = Groth16::<Bls12_381>::verify_with_processed_vk(&pvk, &u64_vec_to_field_vec::<Bls12_381>(&vec3), &proof).unwrap();
    // let result = Groth16::<Bls12_381>::verify_proof(&pvk, &proof, &u64_vec_to_field_vec::<Bls12_381>(&vec3)).unwrap();
    let end_groth16_verify: Instant = Instant::now();    
    println!("Verify Generation time - groth16 verify: {:?}\n", end_groth16_verify.duration_since(end_groth16_prove).as_micros());


    assert_eq!(should_satisfy, result);

}

fn groth16_test(
    should_satisfy: bool,
) {
    println!("===== groth16 test ");
    let mut rng = ark_std::rand::rngs::StdRng::seed_from_u64(test_rng().next_u64());
    
    let S_3 = Fr::rand(&mut rng);
    let S_2 = S_3*S_3;
    let S_1 = Fr::rand(&mut rng);
    let m = Fr::rand(&mut rng);
    let N = Fr::from(5);
    let C = S_3 + m;


    let circuit = Groth16Circuit {
        S_2: Some(S_2),
        CT: Some((Some(S_1), Some(C))),
        S_3: Some(S_3),
        m: Some(m),
        N: Some(N),
    };

    let (pk, vk) = Groth16::<Bls12_381>::setup(circuit.clone(), &mut rng).unwrap();
    let pvk = Groth16::<Bls12_381>::process_vk(&vk).unwrap();
    let proof = Groth16::<Bls12_381>::prove(
        &pk,
        circuit,
        &mut rng,
    )
    .unwrap();
    
    println!("{:?}", proof);

    let result = Groth16::<Bls12_381>::verify_with_processed_vk(&pvk, &vec![S_2, S_1, C], &proof).unwrap();
    // let result = Groth16::<Bls12_381>::verify_proof(&pvk, &proof, &u64_vec_to_field_vec::<Bls12_381>(&vec3)).unwrap();
    assert_eq!(should_satisfy, result);

}



fn main() {
    println!("hello world!");
    env::set_var("RUST_BACKTRACE", "1");

    // groth16_pow_mod_test(
    //     vec![1,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0], // 2^512+1
    //     vec![2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0], // vec1^2
    //     vec![1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0], // 1
    //     vec![0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0], // 2^512
    //     true,
    // );

    // groth16_test(true);
    // vdc_test(true, 20000, 2048);
    
    
    for i in (10000..=100000).step_by(10000){
        vdc_test(true, i, 2048);
    }

}
