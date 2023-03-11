use bellperson::{gadgets::num::AllocatedNum, ConstraintSystem, SynthesisError};
use ff::PrimeField;
use flate2::{write::ZlibEncoder, Compression};
use nova_snark::{
  traits::{
    circuit::{StepCircuit, TrivialTestCircuit},
    Group,
  },
  CompressedSNARK, PublicParams, RecursiveSNARK,
};
use std::time::Instant;

type G1 = pasta_curves::pallas::Point;
type G2 = pasta_curves::vesta::Point;

// (x_i_plus_1, y_i_plus_1) <-- (y_i, x_i + y_i)
#[derive(Clone, Debug)]
struct FiboIteration<F: PrimeField> {
  x_i: F,
  y_i: F,
  x_i_plus_1: F,
  y_i_plus_1: F,
}

impl<F: PrimeField> FiboIteration<F> {
    // generate trace
  fn new(num_iters: usize, x_0: &F, y_0: &F) -> (Vec<F>, Vec<Self>) {
    let mut res = Vec::new();
    let mut x_i = *x_0;
    let mut y_i = *y_0;
    for _i in 0..num_iters {
      let x_i_plus_1 = y_i;
      let y_i_plus_1 = x_i + y_i;
      res.push(Self {
            x_i,
            y_i,
            x_i_plus_1,
            y_i_plus_1
      });
      x_i = x_i_plus_1;
      y_i = y_i_plus_1;
    }
    let z0 = vec![*x_0, *y_0];
      (z0, res)
    }
}


#[derive(Clone, Debug)]
struct FiboCircuit<F: PrimeField> {
  seq: Vec<FiboIteration<F>>,
}

impl<F: PrimeField> StepCircuit<F> for FiboCircuit<F> {
  fn arity(&self) -> usize {
    2
  }

  fn synthesize<CS: ConstraintSystem<F>>(
    &self,
    cs: &mut CS,
    z: &[AllocatedNum<F>],
  ) -> Result<Vec<AllocatedNum<F>>, SynthesisError> {
    let mut z_out: Result<Vec<AllocatedNum<F>>, SynthesisError> =
      Err(SynthesisError::AssignmentMissing);

    let x_0 = z[0].clone();
    let y_0 = z[1].clone();

    let mut x_i = x_0;
    let mut y_i = y_0;
    for i in 0..self.seq.len() {
      // TODO: try to remove y_i_plus_1 assign and directly output x_i + y_i in z_out
      let y_i_plus_1 = 
        AllocatedNum::alloc(cs.namespace(||format!("y_i_plus_1_{i}")), ||{
            Ok(self.seq[i].y_i_plus_1)
        })?;
      let dummy = 
        AllocatedNum::alloc(cs.namespace(||format!("one_{i}")), ||{
            Ok(F::one())
        })?;

      cs.enforce(||format!("y_i_plus_1_{i} * 1 = x_i_{i} + y_i_{i}"), 
        |lc| lc + y_i_plus_1.get_variable(),
        |lc| lc + dummy.get_variable(),
        |lc| lc + x_i.get_variable() + y_i.get_variable(),
      );
      if i == self.seq.len() - 1 {
        z_out = Ok(vec![y_i.clone(), y_i_plus_1.clone()]);
      }

      // update x_i and y_i for the next iteration
      x_i = y_i;
      y_i = y_i_plus_1;
    }
    z_out
  }

  fn output(&self, z: &[F]) -> Vec<F> {
    // sanity check
    debug_assert_eq!(z[0], self.seq[0].x_i);
    debug_assert_eq!(z[1], self.seq[0].y_i);

    // compute output using advice
    vec![
      self.seq[self.seq.len() - 1].x_i_plus_1,
      self.seq[self.seq.len() - 1].y_i_plus_1,
    ]
  }

}

fn main() {
  println!("Nova based Fibonacci function");
  println!("=========================================================");

  let num_steps = 10;
  for num_iters_per_step in [2048, 4096, 8192, 16384, 32768, 65535] {
    let circuit_primary = FiboCircuit {
      seq: vec![
        FiboIteration {
          x_i: <G1 as Group>::Scalar::zero(),
          y_i: <G1 as Group>::Scalar::zero(),
          x_i_plus_1: <G1 as Group>::Scalar::zero(),
          y_i_plus_1: <G1 as Group>::Scalar::zero(),
        };
        num_iters_per_step
      ],
    };

    let circuit_secondary = TrivialTestCircuit::default();

    println!("Proving {num_iters_per_step} iterations of Fibonacci sequence per step");
    // (SS1) produce public parameters
    let start = Instant::now();
    println!("Producing public parameters...");
    let pp = PublicParams::<
      G1,
      G2,
      FiboCircuit<<G1 as Group>::Scalar>,
      TrivialTestCircuit<<G2 as Group>::Scalar>,
    >::setup(circuit_primary, circuit_secondary.clone());
    println!("PublicParams::setup, took {:?} ", start.elapsed());
    println!(
      "Number of constraints per step (primary circuit): {}",
      pp.num_constraints().0
    );
    println!(
      "Number of constraints per step (secondary circuit): {}",
      pp.num_constraints().1
    );

    println!(
      "Number of variables per step (primary circuit): {}",
      pp.num_variables().0
    );
    println!(
      "Number of variables per step (secondary circuit): {}",
      pp.num_variables().1
    );

    // (SS2) produce non-deterministic advice
    let (z0_primary, fibo_iterations) = FiboIteration::new(
      num_iters_per_step * num_steps,
      &<G1 as Group>::Scalar::zero(),
      &<G1 as Group>::Scalar::one(),
    );
    let fibo_circuits = (0..num_steps)
      .map(|i| FiboCircuit {
        seq: (0..num_iters_per_step)
          .map(|j| FiboIteration {
            x_i: fibo_iterations[i * num_iters_per_step + j].x_i,
            y_i: fibo_iterations[i * num_iters_per_step + j].y_i,
            x_i_plus_1: fibo_iterations[i * num_iters_per_step + j].x_i_plus_1,
            y_i_plus_1: fibo_iterations[i * num_iters_per_step + j].y_i_plus_1,
          })
          .collect::<Vec<_>>(),
      })
      .collect::<Vec<_>>();

    let z0_secondary = vec![<G2 as Group>::Scalar::zero()];


    // (SS3) produce a recursive SNARK
    type C1 = FiboCircuit<<G1 as Group>::Scalar>;
    type C2 = TrivialTestCircuit<<G2 as Group>::Scalar>;
    println!("Generating a RecursiveSNARK...");
    let mut recursive_snark: Option<RecursiveSNARK<G1, G2, C1, C2>> = None;
    for (i, circuit_primary) in fibo_circuits.iter().take(num_steps).enumerate() {
      let start = Instant::now();
      let res = RecursiveSNARK::prove_step(
        &pp,
        recursive_snark,
        circuit_primary.clone(),
        circuit_secondary.clone(),
        z0_primary.clone(),
        z0_secondary.clone(),
      );
      assert!(res.is_ok());
      println!(
        "RecursiveSNARK::prove_step {}: {:?}, took {:?} ",
        i,
        res.is_ok(),
        start.elapsed()
      );
      recursive_snark = Some(res.unwrap());
    }

    assert!(recursive_snark.is_some());
    let recursive_snark = recursive_snark.unwrap();

    // (SS4) verify the recursive SNARK
    println!("Verifying a RecursiveSNARK...");
    let start = Instant::now();
    let res = recursive_snark.verify(&pp, num_steps, z0_primary.clone(), z0_secondary.clone());
    println!(
      "RecursiveSNARK::verify: {:?}, took {:?}",
      res.is_ok(),
      start.elapsed()
    );
    assert!(res.is_ok());

    // (SS5) produce a compressed SNARK
    println!("Generating a CompressedSNARK using Spartan with IPA-PC...");
    let (pk, vk) = CompressedSNARK::<_, _, _, _, S1, S2>::setup(&pp);

    let start = Instant::now();
    type EE1 = nova_snark::provider::ipa_pc::EvaluationEngine<G1>;
    type EE2 = nova_snark::provider::ipa_pc::EvaluationEngine<G2>;
    type S1 = nova_snark::spartan::RelaxedR1CSSNARK<G1, EE1>;
    type S2 = nova_snark::spartan::RelaxedR1CSSNARK<G2, EE2>;

    let res = CompressedSNARK::<_, _, _, _, S1, S2>::prove(&pp, &pk, &recursive_snark);
    println!(
      "CompressedSNARK::prove: {:?}, took {:?}",
      res.is_ok(),
      start.elapsed()
    );
    assert!(res.is_ok());
    let compressed_snark = res.unwrap();

    let mut encoder = ZlibEncoder::new(Vec::new(), Compression::default());
    bincode::serialize_into(&mut encoder, &compressed_snark).unwrap();
    let compressed_snark_encoded = encoder.finish().unwrap();
    println!(
      "CompressedSNARK::len {:?} bytes",
      compressed_snark_encoded.len()
    );

    // (SS6) verify the compressed SNARK
    println!("Verifying a CompressedSNARK...");
    let start = Instant::now();
    let res = compressed_snark.verify(&vk, num_steps, z0_primary, z0_secondary);
    println!(
      "CompressedSNARK::verify: {:?}, took {:?}",
      res.is_ok(),
      start.elapsed()
    );
    assert!(res.is_ok());
    println!("=========================================================");

  }
}
