use std::fmt::Debug;
use std::marker::PhantomData;

use p3_air::{Air, AirBuilder, BaseAir};
use p3_field::{AbstractField, Field, PrimeField32};
use p3_matrix::Matrix;
use p3_matrix::dense::RowMajorMatrix;

use p3_challenger::{HashChallenger, SerializingChallenger32};
use p3_circle::CirclePcs;
use p3_commit::ExtensionMmcs;
use p3_field::extension::BinomialExtensionField;
use p3_fri::FriConfig;
use p3_keccak::Keccak256Hash;
use p3_merkle_tree::FieldMerkleTreeMmcs;
use p3_mersenne_31::Mersenne31;
use p3_symmetric::{CompressionFunctionFromHasher, SerializingHasher32};
use p3_uni_stark::{prove, verify, StarkConfig};
use tracing_forest::util::LevelFilter;
use tracing_forest::ForestLayer;
use tracing_subscriber::layer::SubscriberExt;
use tracing_subscriber::util::SubscriberInitExt;
use tracing_subscriber::{EnvFilter, Registry};

const CommitteeSize : usize = 5;
const AuxPointX: u32 = 310816354;
const AuxPointY: u32 = 2077510353;
const MinusOne: u32 = 2^31 -1 -1;
const ATE: u32 = MinusOne;
const DTE: u32 = 6;

pub struct Plonky3Sum {
    pub apk_x: u32,
    pub apk_y: u32,
    pub pk_x : [u32; CommitteeSize],
    pub pk_y : [u32; CommitteeSize],
    pub participated: [u8; CommitteeSize],
}

impl<F: PrimeField32> BaseAir<F> for Plonky3Sum {
    fn width(&self) -> usize {
        6 // index bit map, Px,Py, kacc_x, k_aacy
    }
}

impl<AB: AirBuilder> Air<AB> for Plonky3Sum where AB::F :  PrimeField32, {
    fn eval(&self, builder: &mut AB) {
        let main = builder.main();
        let local = main.row_slice(0);
        let next = main.row_slice(1);

        let index = 0;
        let selector_bit = 1;
        let pk_x = 2;
        let pk_y = 3;
        let kacc_x = 4;
        let kacc_y = 5;

        let a_edwards = AB::F::from_canonical_u32(ATE);
        let aux_point_x = AB::F::from_canonical_u32(AuxPointX);
        let aux_point_y = AB::F::from_canonical_u32(AuxPointY);

        // Enforce starting values
        builder.when_first_row().assert_eq(local[index], AB::Expr::zero());
        builder.when_first_row().assert_eq(local[selector_bit], AB::Expr::zero());
        builder.when_first_row().assert_eq(local[kacc_x], aux_point_x);
        builder.when_first_row().assert_eq(local[kacc_y], aux_point_y);

        // Enforce all kown values in first 3 columns        
        //builder.when_transition().assert_eq(local[selector_bit],self.participated[local[index].as_canonical_u32()]);
        //builder.when_transition().assert_eq(local[pk_x],self.pk_x[local[index].as_canonical_u32()]);
        //builder.when_transition().assert_eq(local[pk_y],self.pk_y[local[index]]);
        
        // Enforce state transition constraints
        //index should grow one by one
        builder.when_transition().assert_eq(next[index], local[index] + AB::Expr::one());

        //x coordinate of accumulation should be correct
        builder.when_transition().assert_eq(local[selector_bit]*(next[kacc_x] * (local[kacc_y]*local[pk_y] + AB::Expr::from(a_edwards) * local[kacc_x]*local[pk_x]) - local[kacc_x]*local[kacc_y] - local[pk_y]*local[pk_x]) + (AB::Expr::one()-local[selector_bit])*(next[kacc_x]-local[kacc_x]), AB::Expr::zero());
        //y coordinate of accumulation should be correct
        builder.when_transition().assert_eq(local[selector_bit]*(next[kacc_y] * (local[kacc_x]*local[pk_y] - local[kacc_y]*local[pk_x]) - local[kacc_x]*local[kacc_y] + local[pk_y]*local[pk_x]) + (AB::Expr::one()-local[selector_bit])*(next[kacc_y]-local[kacc_y]), AB::Expr::zero());

       // Constrain the final value
       let apk_x = AB::F::from_canonical_u32(self.apk_x);
       let apk_y = AB::F::from_canonical_u32(self.apk_y);

       let final_value_x = (apk_x*apk_y + aux_point_y*aux_point_x)/(apk_y*aux_point_y + a_edwards * apk_x * aux_point_x);
       let final_value_y = (apk_x*apk_y - aux_point_y*aux_point_x)/(apk_x*aux_point_y - apk_y*aux_point_x);
        builder.when_last_row().assert_eq(local[kacc_x], final_value_x);
        builder.when_last_row().assert_eq(local[kacc_x], final_value_y);
    }
}

pub fn generate_apk_trace<F: Field+PrimeField32>(pk_x : [u32; CommitteeSize],
     pk_y : [u32; CommitteeSize], participated: [u8; CommitteeSize]) -> RowMajorMatrix<F> {

    let a_edwards = F::from_canonical_u32(ATE);

    let mut last_accumulation_x : F = F::from_canonical_u32(AuxPointX);
    let mut last_accumulation_y : F = F::from_canonical_u32(AuxPointY);
    
    let mut values = Vec::with_capacity(CommitteeSize * 6);
    values.push(F::zero()); //index
    values.push(F::zero()); //selector
    values.push(F::zero()); //value for pk_x[0] is ignored.
    values.push(F::zero()); //value for pk_y[0] is ignored.
    values.push(last_accumulation_x);
    values.push(last_accumulation_y);
    for i in 0..CommitteeSize + 1 {
        //get  accumulation before pushing
        values.push(F::from_canonical_u32(i.try_into().unwrap()));
        values.push(F::from_canonical_u8(participated[i-1]));
        values.push(F::from_canonical_u32(pk_x[i-1]));
        values.push(F::from_canonical_u32(pk_y[i-1]));
        if participated[i-1] == 1 {
            let new_acc_x = (last_accumulation_x*last_accumulation_y + F::from_canonical_u32(pk_y[i-1])*F::from_canonical_u32(pk_x[i-1]))/(last_accumulation_y*F::from_canonical_u32(pk_y[i-1]) + a_edwards * last_accumulation_x * F::from_canonical_u32(pk_x[i-1]));
            let  new_acc_y = (last_accumulation_x*last_accumulation_y - F::from_canonical_u32(pk_y[i-1])*F::from_canonical_u32(pk_x[i-1]))/(last_accumulation_x*F::from_canonical_u32(pk_y[i-1]) - last_accumulation_y*F::from_canonical_u32(pk_x[i-1]));
            values.push(new_acc_x);
            values.push(new_acc_y);
            last_accumulation_x = new_acc_x;
            last_accumulation_y = new_acc_y;
        } else {
            values.push(last_accumulation_x);
            values.push(last_accumulation_y);
        }
    }

    RowMajorMatrix::new(values, 6)
}
fn main() -> Result<(), impl Debug> { let env_filter =
    EnvFilter::builder()
    .with_default_directive(LevelFilter::INFO.into())
    .from_env_lossy();

    Registry::default()
        .with(env_filter)
        .with(ForestLayer::default())
        .init();

    type Val = Mersenne31;
    type Challenge = BinomialExtensionField<Val, 3>;

    type ByteHash = Keccak256Hash;
    type FieldHash = SerializingHasher32<ByteHash>;
    let byte_hash = ByteHash {};
    let field_hash = FieldHash::new(Keccak256Hash {});

    type MyCompress = CompressionFunctionFromHasher<u8, ByteHash, 2, 32>;
    let compress = MyCompress::new(byte_hash);

    type ValMmcs = FieldMerkleTreeMmcs<Val, u8, FieldHash, MyCompress, 32>;
    let val_mmcs = ValMmcs::new(field_hash, compress);

    type ChallengeMmcs = ExtensionMmcs<Val, Challenge, ValMmcs>;
    let challenge_mmcs = ChallengeMmcs::new(val_mmcs.clone());

    type Challenger = SerializingChallenger32<Val, HashChallenger<u8, ByteHash, 32>>;

    let fri_config = FriConfig {
        log_blowup: 1,
        num_queries: 100,
        proof_of_work_bits: 16,
        mmcs: challenge_mmcs,
    };

    type Pcs = CirclePcs<Val, ValMmcs, ChallengeMmcs>;
    let pcs = Pcs {
        mmcs: val_mmcs,
        fri_config,
        _phantom: PhantomData,
    };

    type MyConfig = StarkConfig<Pcs, Challenge, Challenger>;
    let config = MyConfig::new(pcs);

    let pk_x = [1452990225,1415979279,2387338,761104766,346876432];
    let pk_y = [221038753,1396649897,1532407746,8593518,1281517386];

                                      let apk_x = 445907341;
                                      let apk_y =  511523144;
                                      let participated : [u8; CommitteeSize] = [1,0,1,1,0];

                                      

    let air = Plonky3Sum { apk_x, apk_y, pk_x, pk_y, participated };
    let trace = generate_apk_trace::<Val>(pk_x, pk_y, participated);

    let mut challenger = Challenger::from_hasher(vec![], byte_hash);
    let proof = prove(&config, &air, &mut challenger, trace, &vec![]);

    let mut challenger = Challenger::from_hasher(vec![], byte_hash);
    verify(&config, &air, &mut challenger, &proof, &vec![])
}
