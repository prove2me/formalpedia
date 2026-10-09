-- Prove2me | solution 1 for Helfgott.squarefree_harmonic_log_upper_bound
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-08T23:57:21.494912+00:00
-- url     : https://prove2.me/submissions/7859eb87-2445-44ae-937a-478fedeb7dfa

import Theorems.Thm_Helfgott_squarefree_harmonic_numeric_group000_checked
import Theorems.Thm_Helfgott_squarefree_harmonic_numeric_group001_checked
import Mathlib.Algebra.BigOperators.Intervals
import Definitions.Def_Helfgott_MobiusFiniteTable1200001
import Mathlib.Tactic
import Definitions.Def_Helfgott_MobiusFiniteCertificate
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Theorems.Thm_Helfgott_mobiusValuePair000_checked
import Mathlib.Data.Nat.Factorization.Root
import Mathlib.Data.Nat.Sqrt
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Cast.Order.Field
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Nat.Totient
import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
import Mathlib.NumberTheory.LSeries.HurwitzZetaValues
import Mathlib.NumberTheory.ZetaValues
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Data.Rat.BigOperators
import Mathlib.NumberTheory.AbelSummation
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Complex.ExponentialBounds

section
set_option autoImplicit false
open Finset Nat
open scoped BigOperators
namespace Helfgott

lemma squarefree_initial_sum_Ico_join {R : Type*} [AddCommMonoid R]
    (f : ℕ → R) (lo mid hi : ℕ) (hlo : lo ≤ mid) (hhi : mid ≤ hi)
    (a b : R) (ha : (∑ n ∈ Ico lo mid, f n) = a)
    (hb : (∑ n ∈ Ico mid hi, f n) = b) :
    (∑ n ∈ Ico lo hi, f n) = a + b :=
  (Finset.sum_Ico_consecutive f hlo hhi).symm.trans (congrArg₂ (· + ·) ha hb)

end Helfgott
end

section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
open Finset Nat
open scoped BigOperators
namespace Helfgott

private theorem squarefreeInitCount_0_512_from_group : (∑ n ∈ Ico 0 512, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (314 : ℤ) := squarefree_harmonic_numeric_group000_checked.1.1

private theorem squarefreeInitUpper_0_512_from_group : (∑ n ∈ Ico 0 512, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (4839841 : ℕ) := squarefree_harmonic_numeric_group000_checked.1.2

private theorem squarefreeInitCount_512_1024_from_group : (∑ n ∈ Ico 512 1024, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (310 : ℤ) := squarefree_harmonic_numeric_group000_checked.2.1.1

private theorem squarefreeInitUpper_512_1024_from_group : (∑ n ∈ Ico 512 1024, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (418705 : ℕ) := squarefree_harmonic_numeric_group000_checked.2.1.2

private theorem squarefreeInitCount_1024_1536_from_group : (∑ n ∈ Ico 1024 1536, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (313 : ℤ) := squarefree_harmonic_numeric_group000_checked.2.2.1.1

private theorem squarefreeInitUpper_1024_1536_from_group : (∑ n ∈ Ico 1024 1536, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (247623 : ℕ) := squarefree_harmonic_numeric_group000_checked.2.2.1.2

private theorem squarefreeInitCount_1536_2048_from_group : (∑ n ∈ Ico 1536 2048, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (308 : ℤ) := squarefree_harmonic_numeric_group000_checked.2.2.2.1.1

private theorem squarefreeInitUpper_1536_2048_from_group : (∑ n ∈ Ico 1536 2048, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (173112 : ℕ) := squarefree_harmonic_numeric_group000_checked.2.2.2.1.2

private theorem squarefreeInitCount_2048_2560_from_group : (∑ n ∈ Ico 2048 2560, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (312 : ℤ) := squarefree_harmonic_numeric_group000_checked.2.2.2.2.1.1

private theorem squarefreeInitUpper_2048_2560_from_group : (∑ n ∈ Ico 2048 2560, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (136122 : ℕ) := squarefree_harmonic_numeric_group000_checked.2.2.2.2.1.2

private theorem squarefreeInitCount_2560_3072_from_group : (∑ n ∈ Ico 2560 3072, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (312 : ℤ) := squarefree_harmonic_numeric_group000_checked.2.2.2.2.2.1.1

private theorem squarefreeInitUpper_2560_3072_from_group : (∑ n ∈ Ico 2560 3072, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (111228 : ℕ) := squarefree_harmonic_numeric_group000_checked.2.2.2.2.2.1.2

private theorem squarefreeInitCount_3072_3584_from_group : (∑ n ∈ Ico 3072 3584, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (312 : ℤ) := squarefree_harmonic_numeric_group000_checked.2.2.2.2.2.2.1.1

private theorem squarefreeInitUpper_3072_3584_from_group : (∑ n ∈ Ico 3072 3584, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (94141 : ℕ) := squarefree_harmonic_numeric_group000_checked.2.2.2.2.2.2.1.2

private theorem squarefreeInitCount_3584_4096_from_group : (∑ n ∈ Ico 3584 4096, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (310 : ℤ) := squarefree_harmonic_numeric_group000_checked.2.2.2.2.2.2.2.1.1

private theorem squarefreeInitUpper_3584_4096_from_group : (∑ n ∈ Ico 3584 4096, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (80988 : ℕ) := squarefree_harmonic_numeric_group000_checked.2.2.2.2.2.2.2.1.2

private theorem squarefreeInitCount_4096_4608_from_group : (∑ n ∈ Ico 4096 4608, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (311 : ℤ) := squarefree_harmonic_numeric_group000_checked.2.2.2.2.2.2.2.2.1.1

private theorem squarefreeInitUpper_4096_4608_from_group : (∑ n ∈ Ico 4096 4608, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (71713 : ℕ) := squarefree_harmonic_numeric_group000_checked.2.2.2.2.2.2.2.2.1.2

private theorem squarefreeInitCount_4608_5120_from_group : (∑ n ∈ Ico 4608 5120, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (311 : ℤ) := squarefree_harmonic_numeric_group000_checked.2.2.2.2.2.2.2.2.2.1

private theorem squarefreeInitUpper_4608_5120_from_group : (∑ n ∈ Ico 4608 5120, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (64173 : ℕ) := squarefree_harmonic_numeric_group000_checked.2.2.2.2.2.2.2.2.2.2

private theorem squarefreeInitCount_5120_5632_from_group : (∑ n ∈ Ico 5120 5632, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (309 : ℤ) := squarefree_harmonic_numeric_group001_checked.1.1

private theorem squarefreeInitUpper_5120_5632_from_group : (∑ n ∈ Ico 5120 5632, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (57674 : ℕ) := squarefree_harmonic_numeric_group001_checked.1.2

private theorem squarefreeInitCount_5632_6144_from_group : (∑ n ∈ Ico 5632 6144, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (314 : ℤ) := squarefree_harmonic_numeric_group001_checked.2.1.1

private theorem squarefreeInitUpper_5632_6144_from_group : (∑ n ∈ Ico 5632 6144, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (53506 : ℕ) := squarefree_harmonic_numeric_group001_checked.2.1.2

private theorem squarefreeInitCount_6144_6656_from_group : (∑ n ∈ Ico 6144 6656, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (310 : ℤ) := squarefree_harmonic_numeric_group001_checked.2.2.1.1

private theorem squarefreeInitUpper_6144_6656_from_group : (∑ n ∈ Ico 6144 6656, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (48628 : ℕ) := squarefree_harmonic_numeric_group001_checked.2.2.1.2

private theorem squarefreeInitCount_6656_7168_from_group : (∑ n ∈ Ico 6656 7168, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (310 : ℤ) := squarefree_harmonic_numeric_group001_checked.2.2.2.1.1

private theorem squarefreeInitUpper_6656_7168_from_group : (∑ n ∈ Ico 6656 7168, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (45038 : ℕ) := squarefree_harmonic_numeric_group001_checked.2.2.2.1.2

private theorem squarefreeInitCount_7168_7680_from_group : (∑ n ∈ Ico 7168 7680, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (315 : ℤ) := squarefree_harmonic_numeric_group001_checked.2.2.2.2.1.1

private theorem squarefreeInitUpper_7168_7680_from_group : (∑ n ∈ Ico 7168 7680, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (42602 : ℕ) := squarefree_harmonic_numeric_group001_checked.2.2.2.2.1.2

private theorem squarefreeInitCount_7680_8192_from_group : (∑ n ∈ Ico 7680 8192, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (311 : ℤ) := squarefree_harmonic_numeric_group001_checked.2.2.2.2.2.1.1

private theorem squarefreeInitUpper_7680_8192_from_group : (∑ n ∈ Ico 7680 8192, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (39365 : ℕ) := squarefree_harmonic_numeric_group001_checked.2.2.2.2.2.1.2

private theorem squarefreeInitCount_8192_8704_from_group : (∑ n ∈ Ico 8192 8704, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (312 : ℤ) := squarefree_harmonic_numeric_group001_checked.2.2.2.2.2.2.1.1

private theorem squarefreeInitUpper_8192_8704_from_group : (∑ n ∈ Ico 8192 8704, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (37105 : ℕ) := squarefree_harmonic_numeric_group001_checked.2.2.2.2.2.2.1.2

private theorem squarefreeInitCount_8704_9216_from_group : (∑ n ∈ Ico 8704 9216, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (314 : ℤ) := squarefree_harmonic_numeric_group001_checked.2.2.2.2.2.2.2.1.1

private theorem squarefreeInitUpper_8704_9216_from_group : (∑ n ∈ Ico 8704 9216, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (35205 : ℕ) := squarefree_harmonic_numeric_group001_checked.2.2.2.2.2.2.2.1.2

private theorem squarefreeInitCount_9216_9728_from_group : (∑ n ∈ Ico 9216 9728, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (311 : ℤ) := squarefree_harmonic_numeric_group001_checked.2.2.2.2.2.2.2.2.1.1

private theorem squarefreeInitUpper_9216_9728_from_group : (∑ n ∈ Ico 9216 9728, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (32995 : ℕ) := squarefree_harmonic_numeric_group001_checked.2.2.2.2.2.2.2.2.1.2

private theorem squarefreeInitCount_9728_10001_from_group : (∑ n ∈ Ico 9728 10001, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (164 : ℤ) := squarefree_harmonic_numeric_group001_checked.2.2.2.2.2.2.2.2.2.1

private theorem squarefreeInitUpper_9728_10001_from_group : (∑ n ∈ Ico 9728 10001, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (16714 : ℕ) := squarefree_harmonic_numeric_group001_checked.2.2.2.2.2.2.2.2.2.2


private theorem squarefreeInitCountJoin_0_1024 : (∑ n ∈ Ico 0 1024, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (624 : ℤ) := by
  exact (squarefree_initial_sum_Ico_join (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) 0 512 1024
    (by norm_num) (by norm_num) (314 : ℤ) (310 : ℤ) squarefreeInitCount_0_512_from_group squarefreeInitCount_512_1024_from_group).trans (by norm_num)


private theorem squarefreeInitCountJoin_1536_2560 : (∑ n ∈ Ico 1536 2560, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (620 : ℤ) := by
  exact (squarefree_initial_sum_Ico_join (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) 1536 2048 2560
    (by norm_num) (by norm_num) (308 : ℤ) (312 : ℤ) squarefreeInitCount_1536_2048_from_group squarefreeInitCount_2048_2560_from_group).trans (by norm_num)


private theorem squarefreeInitCountJoin_1024_2560 : (∑ n ∈ Ico 1024 2560, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (933 : ℤ) := by
  exact (squarefree_initial_sum_Ico_join (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) 1024 1536 2560
    (by norm_num) (by norm_num) (313 : ℤ) (620 : ℤ) squarefreeInitCount_1024_1536_from_group squarefreeInitCountJoin_1536_2560).trans (by norm_num)


private theorem squarefreeInitCountJoin_0_2560 : (∑ n ∈ Ico 0 2560, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (1557 : ℤ) := by
  exact (squarefree_initial_sum_Ico_join (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) 0 1024 2560
    (by norm_num) (by norm_num) (624 : ℤ) (933 : ℤ) squarefreeInitCountJoin_0_1024 squarefreeInitCountJoin_1024_2560).trans (by norm_num)


private theorem squarefreeInitCountJoin_2560_3584 : (∑ n ∈ Ico 2560 3584, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (624 : ℤ) := by
  exact (squarefree_initial_sum_Ico_join (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) 2560 3072 3584
    (by norm_num) (by norm_num) (312 : ℤ) (312 : ℤ) squarefreeInitCount_2560_3072_from_group squarefreeInitCount_3072_3584_from_group).trans (by norm_num)


private theorem squarefreeInitCountJoin_4096_5120 : (∑ n ∈ Ico 4096 5120, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (622 : ℤ) := by
  exact (squarefree_initial_sum_Ico_join (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) 4096 4608 5120
    (by norm_num) (by norm_num) (311 : ℤ) (311 : ℤ) squarefreeInitCount_4096_4608_from_group squarefreeInitCount_4608_5120_from_group).trans (by norm_num)


private theorem squarefreeInitCountJoin_3584_5120 : (∑ n ∈ Ico 3584 5120, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (932 : ℤ) := by
  exact (squarefree_initial_sum_Ico_join (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) 3584 4096 5120
    (by norm_num) (by norm_num) (310 : ℤ) (622 : ℤ) squarefreeInitCount_3584_4096_from_group squarefreeInitCountJoin_4096_5120).trans (by norm_num)


private theorem squarefreeInitCountJoin_2560_5120 : (∑ n ∈ Ico 2560 5120, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (1556 : ℤ) := by
  exact (squarefree_initial_sum_Ico_join (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) 2560 3584 5120
    (by norm_num) (by norm_num) (624 : ℤ) (932 : ℤ) squarefreeInitCountJoin_2560_3584 squarefreeInitCountJoin_3584_5120).trans (by norm_num)


private theorem squarefreeInitCountJoin_0_5120 : (∑ n ∈ Ico 0 5120, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (3113 : ℤ) := by
  exact (squarefree_initial_sum_Ico_join (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) 0 2560 5120
    (by norm_num) (by norm_num) (1557 : ℤ) (1556 : ℤ) squarefreeInitCountJoin_0_2560 squarefreeInitCountJoin_2560_5120).trans (by norm_num)


private theorem squarefreeInitCountJoin_5120_6144 : (∑ n ∈ Ico 5120 6144, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (623 : ℤ) := by
  exact (squarefree_initial_sum_Ico_join (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) 5120 5632 6144
    (by norm_num) (by norm_num) (309 : ℤ) (314 : ℤ) squarefreeInitCount_5120_5632_from_group squarefreeInitCount_5632_6144_from_group).trans (by norm_num)


private theorem squarefreeInitCountJoin_6656_7680 : (∑ n ∈ Ico 6656 7680, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (625 : ℤ) := by
  exact (squarefree_initial_sum_Ico_join (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) 6656 7168 7680
    (by norm_num) (by norm_num) (310 : ℤ) (315 : ℤ) squarefreeInitCount_6656_7168_from_group squarefreeInitCount_7168_7680_from_group).trans (by norm_num)


private theorem squarefreeInitCountJoin_6144_7680 : (∑ n ∈ Ico 6144 7680, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (935 : ℤ) := by
  exact (squarefree_initial_sum_Ico_join (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) 6144 6656 7680
    (by norm_num) (by norm_num) (310 : ℤ) (625 : ℤ) squarefreeInitCount_6144_6656_from_group squarefreeInitCountJoin_6656_7680).trans (by norm_num)


private theorem squarefreeInitCountJoin_5120_7680 : (∑ n ∈ Ico 5120 7680, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (1558 : ℤ) := by
  exact (squarefree_initial_sum_Ico_join (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) 5120 6144 7680
    (by norm_num) (by norm_num) (623 : ℤ) (935 : ℤ) squarefreeInitCountJoin_5120_6144 squarefreeInitCountJoin_6144_7680).trans (by norm_num)


private theorem squarefreeInitCountJoin_7680_8704 : (∑ n ∈ Ico 7680 8704, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (623 : ℤ) := by
  exact (squarefree_initial_sum_Ico_join (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) 7680 8192 8704
    (by norm_num) (by norm_num) (311 : ℤ) (312 : ℤ) squarefreeInitCount_7680_8192_from_group squarefreeInitCount_8192_8704_from_group).trans (by norm_num)


private theorem squarefreeInitCountJoin_9216_10001 : (∑ n ∈ Ico 9216 10001, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (475 : ℤ) := by
  exact (squarefree_initial_sum_Ico_join (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) 9216 9728 10001
    (by norm_num) (by norm_num) (311 : ℤ) (164 : ℤ) squarefreeInitCount_9216_9728_from_group squarefreeInitCount_9728_10001_from_group).trans (by norm_num)


private theorem squarefreeInitCountJoin_8704_10001 : (∑ n ∈ Ico 8704 10001, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (789 : ℤ) := by
  exact (squarefree_initial_sum_Ico_join (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) 8704 9216 10001
    (by norm_num) (by norm_num) (314 : ℤ) (475 : ℤ) squarefreeInitCount_8704_9216_from_group squarefreeInitCountJoin_9216_10001).trans (by norm_num)


private theorem squarefreeInitCountJoin_7680_10001 : (∑ n ∈ Ico 7680 10001, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (1412 : ℤ) := by
  exact (squarefree_initial_sum_Ico_join (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) 7680 8704 10001
    (by norm_num) (by norm_num) (623 : ℤ) (789 : ℤ) squarefreeInitCountJoin_7680_8704 squarefreeInitCountJoin_8704_10001).trans (by norm_num)


private theorem squarefreeInitCountJoin_5120_10001 : (∑ n ∈ Ico 5120 10001, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (2970 : ℤ) := by
  exact (squarefree_initial_sum_Ico_join (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) 5120 7680 10001
    (by norm_num) (by norm_num) (1558 : ℤ) (1412 : ℤ) squarefreeInitCountJoin_5120_7680 squarefreeInitCountJoin_7680_10001).trans (by norm_num)


private theorem squarefreeInitCountJoin_0_10001 : (∑ n ∈ Ico 0 10001, (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) n) = (6083 : ℤ) := by
  exact (squarefree_initial_sum_Ico_join (fun n : ℕ => ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) 0 5120 10001
    (by norm_num) (by norm_num) (3113 : ℤ) (2970 : ℤ) squarefreeInitCountJoin_0_5120 squarefreeInitCountJoin_5120_10001).trans (by norm_num)


private theorem squarefreeInitUpperJoin_0_1024 : (∑ n ∈ Ico 0 1024, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (5258546 : ℕ) := by
  exact (squarefree_initial_sum_Ico_join (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) 0 512 1024
    (by norm_num) (by norm_num) (4839841 : ℕ) (418705 : ℕ) squarefreeInitUpper_0_512_from_group squarefreeInitUpper_512_1024_from_group).trans (by norm_num)


private theorem squarefreeInitUpperJoin_1536_2560 : (∑ n ∈ Ico 1536 2560, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (309234 : ℕ) := by
  exact (squarefree_initial_sum_Ico_join (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) 1536 2048 2560
    (by norm_num) (by norm_num) (173112 : ℕ) (136122 : ℕ) squarefreeInitUpper_1536_2048_from_group squarefreeInitUpper_2048_2560_from_group).trans (by norm_num)


private theorem squarefreeInitUpperJoin_1024_2560 : (∑ n ∈ Ico 1024 2560, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (556857 : ℕ) := by
  exact (squarefree_initial_sum_Ico_join (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) 1024 1536 2560
    (by norm_num) (by norm_num) (247623 : ℕ) (309234 : ℕ) squarefreeInitUpper_1024_1536_from_group squarefreeInitUpperJoin_1536_2560).trans (by norm_num)


private theorem squarefreeInitUpperJoin_0_2560 : (∑ n ∈ Ico 0 2560, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (5815403 : ℕ) := by
  exact (squarefree_initial_sum_Ico_join (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) 0 1024 2560
    (by norm_num) (by norm_num) (5258546 : ℕ) (556857 : ℕ) squarefreeInitUpperJoin_0_1024 squarefreeInitUpperJoin_1024_2560).trans (by norm_num)


private theorem squarefreeInitUpperJoin_2560_3584 : (∑ n ∈ Ico 2560 3584, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (205369 : ℕ) := by
  exact (squarefree_initial_sum_Ico_join (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) 2560 3072 3584
    (by norm_num) (by norm_num) (111228 : ℕ) (94141 : ℕ) squarefreeInitUpper_2560_3072_from_group squarefreeInitUpper_3072_3584_from_group).trans (by norm_num)


private theorem squarefreeInitUpperJoin_4096_5120 : (∑ n ∈ Ico 4096 5120, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (135886 : ℕ) := by
  exact (squarefree_initial_sum_Ico_join (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) 4096 4608 5120
    (by norm_num) (by norm_num) (71713 : ℕ) (64173 : ℕ) squarefreeInitUpper_4096_4608_from_group squarefreeInitUpper_4608_5120_from_group).trans (by norm_num)


private theorem squarefreeInitUpperJoin_3584_5120 : (∑ n ∈ Ico 3584 5120, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (216874 : ℕ) := by
  exact (squarefree_initial_sum_Ico_join (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) 3584 4096 5120
    (by norm_num) (by norm_num) (80988 : ℕ) (135886 : ℕ) squarefreeInitUpper_3584_4096_from_group squarefreeInitUpperJoin_4096_5120).trans (by norm_num)


private theorem squarefreeInitUpperJoin_2560_5120 : (∑ n ∈ Ico 2560 5120, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (422243 : ℕ) := by
  exact (squarefree_initial_sum_Ico_join (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) 2560 3584 5120
    (by norm_num) (by norm_num) (205369 : ℕ) (216874 : ℕ) squarefreeInitUpperJoin_2560_3584 squarefreeInitUpperJoin_3584_5120).trans (by norm_num)


private theorem squarefreeInitUpperJoin_0_5120 : (∑ n ∈ Ico 0 5120, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (6237646 : ℕ) := by
  exact (squarefree_initial_sum_Ico_join (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) 0 2560 5120
    (by norm_num) (by norm_num) (5815403 : ℕ) (422243 : ℕ) squarefreeInitUpperJoin_0_2560 squarefreeInitUpperJoin_2560_5120).trans (by norm_num)


private theorem squarefreeInitUpperJoin_5120_6144 : (∑ n ∈ Ico 5120 6144, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (111180 : ℕ) := by
  exact (squarefree_initial_sum_Ico_join (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) 5120 5632 6144
    (by norm_num) (by norm_num) (57674 : ℕ) (53506 : ℕ) squarefreeInitUpper_5120_5632_from_group squarefreeInitUpper_5632_6144_from_group).trans (by norm_num)


private theorem squarefreeInitUpperJoin_6656_7680 : (∑ n ∈ Ico 6656 7680, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (87640 : ℕ) := by
  exact (squarefree_initial_sum_Ico_join (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) 6656 7168 7680
    (by norm_num) (by norm_num) (45038 : ℕ) (42602 : ℕ) squarefreeInitUpper_6656_7168_from_group squarefreeInitUpper_7168_7680_from_group).trans (by norm_num)


private theorem squarefreeInitUpperJoin_6144_7680 : (∑ n ∈ Ico 6144 7680, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (136268 : ℕ) := by
  exact (squarefree_initial_sum_Ico_join (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) 6144 6656 7680
    (by norm_num) (by norm_num) (48628 : ℕ) (87640 : ℕ) squarefreeInitUpper_6144_6656_from_group squarefreeInitUpperJoin_6656_7680).trans (by norm_num)


private theorem squarefreeInitUpperJoin_5120_7680 : (∑ n ∈ Ico 5120 7680, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (247448 : ℕ) := by
  exact (squarefree_initial_sum_Ico_join (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) 5120 6144 7680
    (by norm_num) (by norm_num) (111180 : ℕ) (136268 : ℕ) squarefreeInitUpperJoin_5120_6144 squarefreeInitUpperJoin_6144_7680).trans (by norm_num)


private theorem squarefreeInitUpperJoin_7680_8704 : (∑ n ∈ Ico 7680 8704, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (76470 : ℕ) := by
  exact (squarefree_initial_sum_Ico_join (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) 7680 8192 8704
    (by norm_num) (by norm_num) (39365 : ℕ) (37105 : ℕ) squarefreeInitUpper_7680_8192_from_group squarefreeInitUpper_8192_8704_from_group).trans (by norm_num)


private theorem squarefreeInitUpperJoin_9216_10001 : (∑ n ∈ Ico 9216 10001, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (49709 : ℕ) := by
  exact (squarefree_initial_sum_Ico_join (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) 9216 9728 10001
    (by norm_num) (by norm_num) (32995 : ℕ) (16714 : ℕ) squarefreeInitUpper_9216_9728_from_group squarefreeInitUpper_9728_10001_from_group).trans (by norm_num)


private theorem squarefreeInitUpperJoin_8704_10001 : (∑ n ∈ Ico 8704 10001, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (84914 : ℕ) := by
  exact (squarefree_initial_sum_Ico_join (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) 8704 9216 10001
    (by norm_num) (by norm_num) (35205 : ℕ) (49709 : ℕ) squarefreeInitUpper_8704_9216_from_group squarefreeInitUpperJoin_9216_10001).trans (by norm_num)


private theorem squarefreeInitUpperJoin_7680_10001 : (∑ n ∈ Ico 7680 10001, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (161384 : ℕ) := by
  exact (squarefree_initial_sum_Ico_join (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) 7680 8704 10001
    (by norm_num) (by norm_num) (76470 : ℕ) (84914 : ℕ) squarefreeInitUpperJoin_7680_8704 squarefreeInitUpperJoin_8704_10001).trans (by norm_num)


private theorem squarefreeInitUpperJoin_5120_10001 : (∑ n ∈ Ico 5120 10001, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (408832 : ℕ) := by
  exact (squarefree_initial_sum_Ico_join (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) 5120 7680 10001
    (by norm_num) (by norm_num) (247448 : ℕ) (161384 : ℕ) squarefreeInitUpperJoin_5120_7680 squarefreeInitUpperJoin_7680_10001).trans (by norm_num)


private theorem squarefreeInitUpperJoin_0_10001 : (∑ n ∈ Ico 0 10001, (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) n) = (6646478 : ℕ) := by
  exact (squarefree_initial_sum_Ico_join (fun n : ℕ => mobiusHarmonicCeil 1000000 n (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) 0 5120 10001
    (by norm_num) (by norm_num) (6237646 : ℕ) (408832 : ℕ) squarefreeInitUpperJoin_0_5120 squarefreeInitUpperJoin_5120_10001).trans (by norm_num)


theorem squarefree_harmonic_initial_numeric_checks :
    (∑ n ∈ Ico 0 10001, ((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2) = (6083 : ℤ) ∧
    (∑ n ∈ Ico 0 10001, mobiusHarmonicCeil 1000000 n
      (((mobiusTreeValue 16 mobiusTable1200001) n) ^ 2)) ≤ 6650000 := by
  refine ⟨squarefreeInitCountJoin_0_10001, ?_⟩
  exact squarefreeInitUpperJoin_0_10001.le.trans (by norm_num)

end Helfgott
end

section
section
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 2400000
namespace Helfgott

-- A proper small divisor disqualifies every composite; only the prime cases need membership.
def mobiusSmallPrimeCompletenessCheck : Bool :=
  (List.range 1101).all (fun n =>
    decide (n < 2) ||
      ([2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31] : List ℕ).any
        (fun d => decide (2 ≤ d) && decide (d < n) && (n % d == 0)) ||
      decide (n ∈ mobiusSmallPrimes))

lemma mobiusSmallPrimeCompletenessCheck_checked :
    mobiusSmallPrimeCompletenessCheck = true := by decide +kernel

lemma mobiusSmallPrimes_complete_fast :
    ∀ p : Fin 1101, Nat.Prime p.val → p.val ∈ mobiusSmallPrimes := by
  intro p hp
  have hc := List.all_eq_true.mp mobiusSmallPrimeCompletenessCheck_checked
    p.val (by simpa using p.isLt)
  have fields : p.val < 2 ∨
      (∃ d ∈ ([2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31] : List ℕ),
        2 ≤ d ∧ d < p.val ∧ p.val % d = 0) ∨ p.val ∈ mobiusSmallPrimes := by
    simpa [mobiusSmallPrimeCompletenessCheck, List.any_eq_true, Bool.or_assoc, or_assoc,
      Bool.and_assoc, and_assoc] using hc
  rcases fields with hsmall | hdiv | hmem
  · have hp2 := hp.two_le
    omega
  · obtain ⟨d, hdL, hd2, hdp, hdmod⟩ := hdiv
    exact False.elim ((Nat.not_prime_of_dvd_of_lt (Nat.dvd_of_mod_eq_zero hdmod) hd2 hdp) hp)
  · exact hmem

end Helfgott
end

section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2400000
open Nat ArithmeticFunction
open scoped BigOperators

namespace Helfgott

lemma mobiusSmallPrimes_sound : ∀ p ∈ mobiusSmallPrimes, Nat.Prime p := by
  simp only [mobiusSmallPrimes, List.forall_mem_cons]
  exact ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, ⟨by norm_num, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

lemma mobiusSmallPrimes_complete :
    ∀ p : Fin 1101, Nat.Prime p.val → p.val ∈ mobiusSmallPrimes :=
  mobiusSmallPrimes_complete_fast

lemma mobiusSmallPrimeCheck_sound (n : ℕ) (hn : n < 1200001)
    (hc : mobiusSmallPrimeCheck n = true) : Nat.Prime n := by
  have hcfields : 2 ≤ n ∧ mobiusSmallPrimes.all (fun p =>
      if p * p ≤ n then !(n % p == 0) else true) = true := by
    simpa [mobiusSmallPrimeCheck] using hc
  have hn2 : 2 ≤ n := hcfields.1
  by_contra hnot
  let p := n.minFac
  have hpp : Nat.Prime p := Nat.minFac_prime (by omega)
  have hpsq : p ^ 2 ≤ n := Nat.minFac_sq_le_self (by omega) hnot
  have hpbound : p < 1101 := by nlinarith
  have hmem : p ∈ mobiusSmallPrimes := mobiusSmallPrimes_complete ⟨p, hpbound⟩ hpp
  have hall : mobiusSmallPrimes.all (fun p =>
      if p * p ≤ n then !(n % p == 0) else true) = true :=
    hcfields.2
  have hpcheck := List.all_eq_true.mp hall p hmem
  have hdiv : n % p = 0 := Nat.mod_eq_zero_of_dvd (Nat.minFac_dvd n)
  simp [show p * p ≤ n by simpa [pow_two] using hpsq, hdiv] at hpcheck

end Helfgott
end

section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2400000
open Nat ArithmeticFunction
open scoped BigOperators

namespace Helfgott

theorem moebius_of_local_checks (g : ℕ → ℤ) (B : ℕ) (hB : B ≤ 1200001)
    (hc : ∀ n < B, ∃ p, mobiusLocalCheck g n p = true) :
    ∀ n < B, g n = moebius n := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hnB
    obtain ⟨p, hpcheck⟩ := hc n hnB
    by_cases hn0 : n = 0
    · subst n
      simpa [mobiusLocalCheck] using hpcheck
    by_cases hn1 : n = 1
    · subst n
      simpa [mobiusLocalCheck] using hpcheck
    by_cases hp0 : p = 0
    · subst p
      have hh : mobiusSmallPrimeCheck n = true ∧ g n = -1 := by
        simpa [mobiusLocalCheck, hn0, hn1] using hpcheck
      have hp := mobiusSmallPrimeCheck_sound n (lt_of_lt_of_le hnB hB) hh.1
      rw [hh.2, moebius_apply_prime hp]
    have hfields : p ∈ mobiusSmallPrimes ∧ p < n ∧ n % p = 0 ∧
        g n = (if (n / p) % p == 0 then 0 else -g (n / p)) := by
      simpa [mobiusLocalCheck, hn0, hn1, hp0, Bool.and_assoc, and_assoc] using hpcheck
    obtain ⟨hpL, hpn, hdiv, hvalue⟩ := hfields
    have hpp := mobiusSmallPrimes_sound p hpL
    have hnp : p ∣ n := Nat.dvd_of_mod_eq_zero hdiv
    have hprod : p * (n / p) = n := Nat.mul_div_cancel' hnp
    have hp2 : 2 ≤ p := hpp.two_le
    have hquot : n / p < n := Nat.div_lt_self (Nat.pos_of_ne_zero hn0) (by omega)
    have hrec := ih (n / p) hquot (lt_trans hquot hnB)
    by_cases hq : (n / p) % p = 0
    · have hpsq : p ^ 2 ∣ n := by
        rw [← hprod, pow_two]
        exact Nat.mul_dvd_mul_left p (Nat.dvd_of_mod_eq_zero hq)
      have hnsq : ¬Squarefree n := by
        intro hs
        have hp2 := hs.squarefree_of_dvd hpsq
        have hf := (Nat.squarefree_pow_iff hpp.ne_one (by norm_num : (2 : ℕ) ≠ 0)).mp hp2
        norm_num at hf
      rw [moebius_eq_zero_of_not_squarefree hnsq]
      simpa [hq] using hvalue
    · have hcop : Nat.Coprime p (n / p) := hpp.coprime_iff_not_dvd.mpr
        (fun hd => hq (Nat.mod_eq_zero_of_dvd hd))
      rw [← hprod, isMultiplicative_moebius.map_mul_of_coprime hcop, moebius_apply_prime hpp]
      simpa [hprod, hq, hrec] using hvalue

lemma mobiusTreeCheck_local_sound (g : ℕ → ℤ) (B d offset : ℕ) (tree : MobiusCertTree)
    (hc : mobiusTreeCheck g B d offset tree = true) :
    ∀ n, offset ≤ n → n < offset + 32 * 2 ^ d → n < B →
      ∃ p, mobiusLocalCheck g n p = true := by
  induction d generalizing offset tree with
  | zero =>
    intro n hlo hup hnB
    have hoff : ¬B ≤ offset := by omega
    cases tree with
    | leaf muDigits factorDigits =>
      have hh : mobiusLeafCheck g B offset factorDigits = true := by
        simpa [mobiusTreeCheck, hoff] using hc
      have hk : n - offset ∈ List.range 32 := by
        simp only [List.mem_range]
        simp only [pow_zero, mul_one] at hup
        omega
      have hlocal := List.all_eq_true.mp hh (n - offset) hk
      have he : offset + (n - offset) = n := Nat.add_sub_of_le hlo
      simp only [mobiusLeafCheck] at hh
      rw [he, if_pos hnB] at hlocal
      exact ⟨_, hlocal⟩
    | branch l r => simp [mobiusTreeCheck, hoff] at hc
  | succ d ih =>
    intro n hlo hup hnB
    have hoff : ¬B ≤ offset := by omega
    cases tree with
    | leaf muDigits factorDigits => simp [mobiusTreeCheck, hoff] at hc
    | branch l r =>
      have hh : mobiusTreeCheck g B d offset l = true ∧
          mobiusTreeCheck g B d (offset + 32 * 2 ^ d) r = true := by
        simpa [mobiusTreeCheck, hoff] using hc
      have hspan : 32 * 2 ^ (d + 1) = 32 * 2 ^ d + 32 * 2 ^ d := by
        rw [pow_succ]
        ring
      rw [hspan] at hup
      by_cases hsplit : n < offset + 32 * 2 ^ d
      · exact ih offset l hh.1 n hlo hsplit hnB
      · exact ih (offset + 32 * 2 ^ d) r hh.2 n (by omega) (by omega) hnB

theorem mobiusTreeCheck_sound (B d : ℕ) (tree : MobiusCertTree)
    (hB : B ≤ 1200001) (hcapacity : B ≤ 32 * 2 ^ d)
    (hc : mobiusTreeCheck (mobiusTreeValue d tree) B d 0 tree = true) :
    ∀ n < B, mobiusTreeValue d tree n = moebius n := by
  apply moebius_of_local_checks _ B hB
  intro n hn
  exact mobiusTreeCheck_local_sound _ B d 0 tree hc n (Nat.zero_le n)
    (by simpa using lt_of_lt_of_le hn hcapacity) hn

end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 2400000
open Finset Nat ArithmeticFunction
open scoped BigOperators Classical

namespace Helfgott

lemma mobiusHarmonicCeil_bound (Q n : ℕ) (s : ℤ) (hQ : 0 < Q) :
    |(s : ℝ)| / (n : ℝ) ≤ (mobiusHarmonicCeil Q n s : ℝ) / (Q : ℝ) := by
  by_cases hn : n = 0
  · simp [hn, mobiusHarmonicCeil]
  have hnpos : 0 < n := Nat.pos_of_ne_zero hn
  have hmod := Nat.mod_lt (s.natAbs * Q + n - 1) hnpos
  have hdiv := Nat.div_add_mod (s.natAbs * Q + n - 1) n
  rw [Nat.mul_comm n ((s.natAbs * Q + n - 1) / n)] at hdiv
  have hmul : s.natAbs * Q ≤ ((s.natAbs * Q + n - 1) / n) * n := by
    omega
  have hcast : |(s : ℝ)| * (Q : ℝ) ≤
      (((s.natAbs * Q + n - 1) / n : ℕ) : ℝ) * (n : ℝ) := by
    have hcast0 : (s.natAbs : ℝ) * (Q : ℝ) ≤
        (((s.natAbs * Q + n - 1) / n : ℕ) : ℝ) * (n : ℝ) := by
      exact_mod_cast hmul
    simpa only [Nat.cast_natAbs, Int.cast_abs] using hcast0
  have hnR : (0 : ℝ) < n := by exact_mod_cast hnpos
  have hQR : (0 : ℝ) < Q := by exact_mod_cast hQ
  rw [mobiusHarmonicCeil, if_neg hn]
  exact (div_le_div_iff₀ hnR hQR).mpr hcast

lemma prefix_of_local_checks (g M : ℕ → ℤ) (B : ℕ)
    (hc : ∀ n < B, mobiusPrefixLocalCheck g M n = true) :
    ∀ n < B, M n = ∑ d ∈ Finset.range (n + 1), g d := by
  intro n
  induction n with
  | zero =>
    intro hn
    have hh := hc 0 hn
    simpa [mobiusPrefixLocalCheck] using hh
  | succ n ih =>
    intro hn
    have hh := hc (n + 1) hn
    have hs : M (n + 1) = M n + g (n + 1) := by
      simpa [mobiusPrefixLocalCheck] using hh
    rw [hs, ih (by omega), Finset.sum_range_succ (f := g) (n := n + 1)]

lemma mobiusHarmonicTreeCheck_local_sound (g M : ℕ → ℤ) (Q B d offset : ℕ)
    (tree : MobiusHarmonicTree)
    (hc : mobiusHarmonicTreeCheck g M Q B d offset tree = true) :
    ∀ n, offset ≤ n → n < offset + 32 * 2 ^ d → n < B →
      mobiusPrefixLocalCheck g M n = true := by
  induction d generalizing offset tree with
  | zero =>
    intro n hlo hup hnB
    have hoff : ¬B ≤ offset := by omega
    cases tree with
    | leaf digits upper =>
      have hh : mobiusHarmonicLeafCheck g M Q B offset upper = true := by
        simpa [mobiusHarmonicTreeCheck, hoff] using hc
      have hall : (List.range 32).all (fun k =>
          if offset + k < B then mobiusPrefixLocalCheck g M (offset + k) else true) = true :=
        (Bool.and_eq_true_iff.mp hh).1
      have hk : n - offset ∈ List.range 32 := by
        simp only [List.mem_range]
        simp only [pow_zero, mul_one] at hup
        omega
      have hlocal := List.all_eq_true.mp hall (n - offset) hk
      have he : offset + (n - offset) = n := Nat.add_sub_of_le hlo
      rwa [he, if_pos hnB] at hlocal
    | branch upper l r => simp [mobiusHarmonicTreeCheck, hoff] at hc
  | succ d ih =>
    intro n hlo hup hnB
    have hoff : ¬B ≤ offset := by omega
    cases tree with
    | leaf digits upper => simp [mobiusHarmonicTreeCheck, hoff] at hc
    | branch upper l r =>
      have hh : mobiusHarmonicTreeCheck g M Q B d offset l = true ∧
          mobiusHarmonicTreeCheck g M Q B d (offset + 32 * 2 ^ d) r = true ∧
          upper = mobiusHarmonicUpper l + mobiusHarmonicUpper r := by
        simpa [mobiusHarmonicTreeCheck, hoff, Bool.and_assoc, and_assoc] using hc
      have hspan : 32 * 2 ^ (d + 1) = 32 * 2 ^ d + 32 * 2 ^ d := by
        rw [pow_succ]
        ring
      rw [hspan] at hup
      by_cases hsplit : n < offset + 32 * 2 ^ d
      · exact ih offset l hh.1 n hlo hsplit hnB
      · exact ih (offset + 32 * 2 ^ d) r hh.2.1 n (by omega) (by omega) hnB

lemma mobiusHarmonicTreeCheck_bound (g M : ℕ → ℤ) (Q B d offset : ℕ)
    (tree : MobiusHarmonicTree) (hQ : 0 < Q)
    (hc : mobiusHarmonicTreeCheck g M Q B d offset tree = true) :
    (∑ k ∈ Finset.range (32 * 2 ^ d),
      if offset + k < B then |(M (offset + k) : ℝ)| / (offset + k : ℕ) else 0) ≤
      (mobiusHarmonicUpper tree : ℝ) / (Q : ℝ) := by
  induction d generalizing offset tree with
  | zero =>
    by_cases hoff : B ≤ offset
    · have hu : mobiusHarmonicUpper tree = 0 := by
        cases tree <;> simpa [mobiusHarmonicTreeCheck, hoff, mobiusHarmonicUpper] using hc
      rw [hu]
      apply le_of_eq
      simp only [Nat.cast_zero, zero_div]
      apply Finset.sum_eq_zero
      intro k hk
      rw [if_neg (by omega)]
    cases tree with
    | branch upper l r => simp [mobiusHarmonicTreeCheck, hoff] at hc
    | leaf digits upper =>
      have hh : mobiusHarmonicLeafCheck g M Q B offset upper = true := by
        simpa [mobiusHarmonicTreeCheck, hoff] using hc
      have huL : ((List.range 32).map (fun k =>
          if offset + k < B then mobiusHarmonicCeil Q (offset + k) (M (offset + k))
          else 0)).sum = upper := by
        simpa using (Bool.and_eq_true_iff.mp hh).2
      have hu : (∑ k ∈ Finset.range 32,
          if offset + k < B then mobiusHarmonicCeil Q (offset + k) (M (offset + k))
          else 0) = upper := by
        rw [← huL]
        have hset : (List.range 32).toFinset = Finset.range 32 := by
          ext k
          simp only [List.mem_toFinset, List.mem_range, Finset.mem_range]
        simpa only [hset] using List.sum_toFinset (fun k =>
          if offset + k < B then mobiusHarmonicCeil Q (offset + k) (M (offset + k))
          else 0) (List.nodup_range (n := 32))
      have huR : (∑ k ∈ Finset.range 32,
          if offset + k < B then (mobiusHarmonicCeil Q (offset + k) (M (offset + k)) : ℝ)
          else 0) = (upper : ℝ) := by exact_mod_cast hu
      simp only [pow_zero, mul_one, mobiusHarmonicUpper]
      calc
        _ ≤ (∑ k ∈ Finset.range 32,
            if offset + k < B then
              (mobiusHarmonicCeil Q (offset + k) (M (offset + k)) : ℝ) else 0) / (Q : ℝ) := by
          rw [Finset.sum_div]
          apply Finset.sum_le_sum
          intro k hk
          by_cases hkB : offset + k < B
          · simp only [if_pos hkB]
            exact mobiusHarmonicCeil_bound Q (offset + k) (M (offset + k)) hQ
          · simp [hkB]
        _ = _ := by rw [huR]
  | succ d ih =>
    by_cases hoff : B ≤ offset
    · have hu : mobiusHarmonicUpper tree = 0 := by
        cases tree <;> simpa [mobiusHarmonicTreeCheck, hoff, mobiusHarmonicUpper] using hc
      rw [hu]
      apply le_of_eq
      simp only [Nat.cast_zero, zero_div]
      apply Finset.sum_eq_zero
      intro k hk
      rw [if_neg (by omega)]
    cases tree with
    | leaf digits upper => simp [mobiusHarmonicTreeCheck, hoff] at hc
    | branch upper l r =>
      have hh : mobiusHarmonicTreeCheck g M Q B d offset l = true ∧
          mobiusHarmonicTreeCheck g M Q B d (offset + 32 * 2 ^ d) r = true ∧
          upper = mobiusHarmonicUpper l + mobiusHarmonicUpper r := by
        simpa [mobiusHarmonicTreeCheck, hoff, Bool.and_assoc, and_assoc] using hc
      have hspan : 32 * 2 ^ (d + 1) = 32 * 2 ^ d + 32 * 2 ^ d := by
        rw [pow_succ]
        ring
      rw [hspan, Finset.sum_range_add]
      have hl := ih offset l hh.1
      have hr := ih (offset + 32 * 2 ^ d) r hh.2.1
      have hr' : (∑ k ∈ Finset.range (32 * 2 ^ d),
          if offset + (32 * 2 ^ d + k) < B then
            |(M (offset + (32 * 2 ^ d + k)) : ℝ)| / (offset + (32 * 2 ^ d + k) : ℕ)
          else 0) ≤ (mobiusHarmonicUpper r : ℝ) / (Q : ℝ) := by
        simpa [Nat.add_assoc] using hr
      calc
        _ ≤ (mobiusHarmonicUpper l : ℝ) / (Q : ℝ) +
            (mobiusHarmonicUpper r : ℝ) / (Q : ℝ) := add_le_add hl hr'
        _ = _ := by simp only [mobiusHarmonicUpper, hh.2.2, Nat.cast_add, add_div]

theorem moebius_finite_harmonic_certificate (B dm dh Q : ℕ)
    (muTree : MobiusCertTree) (hTree : MobiusHarmonicTree)
    (hB : B ≤ 1200001) (hmCapacity : B ≤ 32 * 2 ^ dm)
    (hhCapacity : B ≤ 32 * 2 ^ dh) (hQ : 0 < Q)
    (hm : mobiusTreeCheck (mobiusTreeValue dm muTree) B dm 0 muTree = true)
    (hh : mobiusHarmonicTreeCheck (mobiusTreeValue dm muTree)
      (mobiusPrefixValue dh hTree) Q B dh 0 hTree = true) :
    (∑ n ∈ Finset.Ico 1 B,
      |∑ d ∈ Finset.Icc 1 n, ((moebius d : ℤ) : ℝ)| / (n : ℝ)) ≤
      (mobiusHarmonicUpper hTree : ℝ) / (Q : ℝ) := by
  let g := mobiusTreeValue dm muTree
  let M := mobiusPrefixValue dh hTree
  have hg : ∀ n < B, g n = moebius n := mobiusTreeCheck_sound B dm muTree hB hmCapacity hm
  have hp : ∀ n < B, M n = ∑ d ∈ Finset.range (n + 1), g d := by
    apply prefix_of_local_checks g M B
    intro n hn
    exact mobiusHarmonicTreeCheck_local_sound g M Q B dh 0 hTree hh n (Nat.zero_le _)
      (by simpa using lt_of_lt_of_le hn hhCapacity) hn
  have hM (n : ℕ) (hn : n < B) :
      (M n : ℝ) = ∑ d ∈ Finset.Icc 1 n, ((moebius d : ℤ) : ℝ) := by
    have ht : M n = ∑ d ∈ Finset.range (n + 1), moebius d := by
      rw [hp n hn]
      apply Finset.sum_congr rfl
      intro d hd
      exact hg d (by have h := Finset.mem_range.mp hd; omega)
    rw [Finset.sum_range_eq_add_Ico (fun d => moebius d) (Nat.zero_lt_succ n),
      ArithmeticFunction.map_zero, zero_add] at ht
    simp only [Nat.succ_eq_add_one, Finset.Ico_add_one_right_eq_Icc] at ht
    exact_mod_cast ht
  have hb := mobiusHarmonicTreeCheck_bound g M Q B dh 0 hTree hQ hh
  simp only [zero_add] at hb
  have heq : (∑ n ∈ Finset.range (32 * 2 ^ dh),
      if n < B then |(M n : ℝ)| / (n : ℝ) else 0) =
      ∑ n ∈ Finset.range B, |(M n : ℝ)| / (n : ℝ) := by
    symm
    calc
      _ = ∑ n ∈ Finset.range B, if n < B then |(M n : ℝ)| / (n : ℝ) else 0 := by
        apply Finset.sum_congr rfl
        intro n hn
        rw [if_pos (Finset.mem_range.mp hn)]
      _ = _ := Finset.sum_subset (Finset.range_mono hhCapacity) (by
        intro n hn hnB
        rw [if_neg (by simpa only [Finset.mem_range] using hnB)])
  rw [heq] at hb
  calc
    _ = ∑ n ∈ Finset.Ico 1 B, |(M n : ℝ)| / (n : ℝ) := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [hM n (Finset.mem_Ico.mp hn).2]
    _ = ∑ n ∈ Finset.range B, |(M n : ℝ)| / (n : ℝ) := by
      apply Finset.sum_subset (by intro n hn; simp only [Finset.mem_Ico, Finset.mem_range] at *; omega)
      intro n hn hnI
      have hnB := Finset.mem_range.mp hn
      have hn0 : n = 0 := by simp only [Finset.mem_Ico] at hnI; omega
      simp [hn0]
    _ ≤ _ := hb

end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 2400000
open Finset Nat ArithmeticFunction Real MeasureTheory
open scoped BigOperators Classical Interval

namespace Helfgott

lemma moebius_abs_summatory_single_interval (n : ℕ) (hn : 1 ≤ n) :
    (∫ t in (n : ℝ)..(n + 1 : ℕ),
      |∑ d ∈ Finset.Icc 1 ⌊t⌋₊, ((moebius d : ℤ) : ℝ)| / t) =
      |∑ d ∈ Finset.Icc 1 n, ((moebius d : ℤ) : ℝ)| *
        Real.log (((n + 1 : ℕ) : ℝ) / (n : ℝ)) := by
  have hnp : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hsucc : (0 : ℝ) < (n + 1 : ℕ) := by positivity
  calc
    _ = ∫ t in (n : ℝ)..(n + 1 : ℕ),
        |∑ d ∈ Finset.Icc 1 n, ((moebius d : ℤ) : ℝ)| * t⁻¹ := by
      apply intervalIntegral.integral_congr_Ioo_of_le (by exact_mod_cast Nat.le_succ n)
      intro t ht
      have ht0 : 0 ≤ t := by linarith [ht.1]
      have hf : ⌊t⌋₊ = n := (Nat.floor_eq_iff ht0).mpr ⟨ht.1.le, by
        exact_mod_cast ht.2⟩
      dsimp only
      rw [hf]
      simp only [div_eq_mul_inv]
    _ = _ := by
      rw [intervalIntegral.integral_const_mul, integral_inv_of_pos hnp hsucc]

theorem moebius_finite_initial_integral_certificate (B : ℕ) (hB : 1 ≤ B) :
    (∫ t in (1 : ℝ)..(B : ℝ),
      |∑ d ∈ Finset.Icc 1 ⌊t⌋₊, ((moebius d : ℤ) : ℝ)| / t) =
      (∑ n ∈ Finset.Ico 1 B,
        |∑ d ∈ Finset.Icc 1 n, ((moebius d : ℤ) : ℝ)| *
          Real.log (((n + 1 : ℕ) : ℝ) / (n : ℝ))) ∧
    (∫ t in (1 : ℝ)..(B : ℝ),
      |∑ d ∈ Finset.Icc 1 ⌊t⌋₊, ((moebius d : ℤ) : ℝ)| / t) ≤
      ∑ n ∈ Finset.Ico 1 B,
        |∑ d ∈ Finset.Icc 1 n, ((moebius d : ℤ) : ℝ)| / (n : ℝ) := by
  have hi (n : ℕ) (hn : n ∈ Finset.Ico 1 B) :
      IntervalIntegrable (fun t : ℝ =>
        |∑ d ∈ Finset.Icc 1 ⌊t⌋₊, ((moebius d : ℤ) : ℝ)| / t)
        volume (n : ℝ) (n + 1 : ℕ) := by
    have hn1 := (Finset.mem_Ico.mp hn).1
    have hnp : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    have hle : (n : ℝ) ≤ (n + 1 : ℕ) := by exact_mod_cast Nat.le_succ n
    have hb : IntervalIntegrable (fun t : ℝ => t⁻¹) volume (n : ℝ) (n + 1 : ℕ) := by
      apply intervalIntegral.intervalIntegrable_inv (f := fun t : ℝ => t)
      · intro t ht
        simp only [Set.uIcc_of_le hle, Set.mem_Icc] at ht
        exact (hnp.trans_le ht.1).ne'
      · exact continuous_id.continuousOn
    apply (hb.const_mul |∑ d ∈ Finset.Icc 1 n, ((moebius d : ℤ) : ℝ)|).congr_uIoo
    intro t ht
    simp only [Set.uIoo_of_le hle, Set.mem_Ioo] at ht
    have ht0 : 0 ≤ t := by linarith [ht.1]
    have hf : ⌊t⌋₊ = n := (Nat.floor_eq_iff ht0).mpr ⟨ht.1.le, by exact_mod_cast ht.2⟩
    dsimp only
    rw [hf]
    simp only [div_eq_mul_inv]
  have hs := intervalIntegral.sum_integral_adjacent_intervals_Ico (a := fun n : ℕ => (n : ℝ))
    hB (fun n hn => hi n (Finset.mem_Ico.mpr hn))
  simp only [Nat.cast_one] at hs
  have hid :
      (∫ t in (1 : ℝ)..(B : ℝ),
        |∑ d ∈ Finset.Icc 1 ⌊t⌋₊, ((moebius d : ℤ) : ℝ)| / t) =
        ∑ n ∈ Finset.Ico 1 B,
          |∑ d ∈ Finset.Icc 1 n, ((moebius d : ℤ) : ℝ)| *
            Real.log (((n + 1 : ℕ) : ℝ) / (n : ℝ)) := by
    rw [← hs]
    apply Finset.sum_congr rfl
    intro n hn
    exact moebius_abs_summatory_single_interval n (Finset.mem_Ico.mp hn).1
  refine ⟨hid, ?_⟩
  rw [hid]
  apply Finset.sum_le_sum
  intro n hn
  have hnp : (0 : ℝ) < n := by exact_mod_cast (by have h := (Finset.mem_Ico.mp hn).1; omega : 0 < n)
  have hsucc : (0 : ℝ) < (n + 1 : ℕ) := by positivity
  have hlog := Real.log_le_sub_one_of_pos (div_pos hsucc hnp)
  calc
    _ ≤ |∑ d ∈ Finset.Icc 1 n, ((moebius d : ℤ) : ℝ)| *
        (((n + 1 : ℕ) : ℝ) / (n : ℝ) - 1) :=
      mul_le_mul_of_nonneg_left hlog (abs_nonneg _)
    _ = _ := by push_cast; field_simp; ring

end Helfgott
end

section
set_option autoImplicit false
open Finset Nat ArithmeticFunction Real MeasureTheory
open scoped BigOperators Classical Interval

namespace Helfgott

theorem moebius_initial_integral_of_finite_certificate_complete (B dm dh Q : ℕ)
    (muTree : MobiusCertTree) (hTree : MobiusHarmonicTree)
    (hBpos : 1 ≤ B) (hB : B ≤ 1200001) (hmCapacity : B ≤ 32 * 2 ^ dm)
    (hhCapacity : B ≤ 32 * 2 ^ dh) (hQ : 0 < Q)
    (hm : mobiusTreeCheck (mobiusTreeValue dm muTree) B dm 0 muTree = true)
    (hh : mobiusHarmonicTreeCheck (mobiusTreeValue dm muTree)
      (mobiusPrefixValue dh hTree) Q B dh 0 hTree = true) :
    (∫ t in (1 : ℝ)..(B : ℝ),
      |∑ d ∈ Finset.Icc 1 ⌊t⌋₊, ((moebius d : ℤ) : ℝ)| / t) ≤
      (mobiusHarmonicUpper hTree : ℝ) / (Q : ℝ) :=
  (moebius_finite_initial_integral_certificate B hBpos).2.trans
    (moebius_finite_harmonic_certificate B dm dh Q muTree hTree hB hmCapacity hhCapacity hQ hm hh)

end Helfgott
end
end

section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option Elab.async false
open Finset Nat ArithmeticFunction Real
open scoped BigOperators Classical
namespace Helfgott

lemma squarefree_harmonic_sum_zero_remove {R : Type*} [AddCommMonoid R]
    (f : ℕ → R) (hf : f 0 = 0) (N : ℕ) :
    (∑ n ∈ Ico 0 (N + 1), f n) = ∑ n ∈ Icc 1 N, f n := by
  rw [show Ico 0 (N + 1) = Icc 0 N by
    ext n; simp only [mem_Ico, mem_Icc]; omega]
  rw [← Finset.insert_Icc_succ_left_eq_Icc (Nat.zero_le N)]
  rw [Finset.sum_insert (by simp), hf, zero_add]
  rfl

theorem squarefree_harmonic_initial_of_certificate
    (N d Q U count : ℕ) (tree : MobiusCertTree)
    (hB : N + 1 ≤ 1200001) (hcapacity : N + 1 ≤ 32 * 2 ^ d) (hQ : 0 < Q)
    (hcheck : mobiusTreeCheck (mobiusTreeValue d tree) (N + 1) d 0 tree = true)
    (hcount : (∑ n ∈ Ico 0 (N + 1), (mobiusTreeValue d tree n) ^ 2) =
      (count : ℤ))
    (hupper : (∑ n ∈ Ico 0 (N + 1), mobiusHarmonicCeil Q n
      ((mobiusTreeValue d tree n) ^ 2)) ≤ U) :
    (∑ n ∈ Icc 1 N, ((moebius n : ℤ) : ℝ) ^ 2) = (count : ℝ) ∧
    (∑ n ∈ Icc 1 N, ((moebius n : ℤ) : ℝ) ^ 2 / (n : ℝ)) ≤ (U : ℝ) / (Q : ℝ) := by
  have hmu := mobiusTreeCheck_sound (N + 1) d tree hB hcapacity hcheck
  have hg0 : mobiusTreeValue d tree 0 = 0 := by simpa using hmu 0 (by omega)
  have hc : (∑ n ∈ Icc 1 N, (mobiusTreeValue d tree n) ^ 2) = (count : ℤ) := by
    rw [← squarefree_harmonic_sum_zero_remove
      (fun n => (mobiusTreeValue d tree n) ^ 2) (by simp [hg0]) N]
    exact hcount
  have hu : (∑ n ∈ Icc 1 N, mobiusHarmonicCeil Q n
      ((mobiusTreeValue d tree n) ^ 2)) ≤ U := by
    rw [← squarefree_harmonic_sum_zero_remove
      (fun n => mobiusHarmonicCeil Q n ((mobiusTreeValue d tree n) ^ 2))
      (by simp [mobiusHarmonicCeil]) N]
    exact hupper
  constructor
  · have hci : (∑ n ∈ Icc 1 N, (moebius n : ℤ) ^ 2) = (count : ℤ) := by
      calc
        _ = ∑ n ∈ Icc 1 N, (mobiusTreeValue d tree n) ^ 2 := by
          apply Finset.sum_congr rfl
          intro n hn
          rw [hmu n (by have hn' := (Finset.mem_Icc.mp hn).2; omega)]
        _ = _ := hc
    have hr := congrArg (fun z : ℤ => (z : ℝ)) hci
    push_cast at hr
    exact hr
  · calc
      _ ≤ ∑ n ∈ Icc 1 N, (mobiusHarmonicCeil Q n
          ((mobiusTreeValue d tree n) ^ 2) : ℝ) / (Q : ℝ) := by
        apply Finset.sum_le_sum
        intro n hn
        have hh := mobiusHarmonicCeil_bound Q n ((mobiusTreeValue d tree n) ^ 2) hQ
        have hnB : n < N + 1 := by have hn' := (Finset.mem_Icc.mp hn).2; omega
        rw [hmu n hnB] at hh ⊢
        simpa only [Int.cast_pow,
          abs_of_nonneg (sq_nonneg (((moebius n : ℤ) : ℝ)))] using hh
      _ ≤ (U : ℝ) / (Q : ℝ) := by
        rw [← Finset.sum_div]
        have huR : (∑ n ∈ Icc 1 N, (mobiusHarmonicCeil Q n
          ((mobiusTreeValue d tree n) ^ 2) : ℝ)) ≤ (U : ℝ) := by
          exact_mod_cast hu
        exact div_le_div_of_nonneg_right huR (Nat.cast_nonneg Q)

theorem squarefree_harmonic_initial_of_values (N Q U count : ℕ) (g : ℕ → ℤ)
    (hQ : 0 < Q) (hmu : ∀ n ≤ N, g n = moebius n)
    (hcount : (∑ n ∈ Ico 0 (N + 1), g n ^ 2) = (count : ℤ))
    (hupper : (∑ n ∈ Ico 0 (N + 1), mobiusHarmonicCeil Q n (g n ^ 2)) ≤ U) :
    (∑ n ∈ Icc 1 N, ((moebius n : ℤ) : ℝ) ^ 2) = (count : ℝ) ∧
    (∑ n ∈ Icc 1 N, ((moebius n : ℤ) : ℝ) ^ 2 / (n : ℝ)) ≤ (U : ℝ) / (Q : ℝ) := by
  have hg0 : g 0 = 0 := by simpa using hmu 0 (Nat.zero_le N)
  have hc : (∑ n ∈ Icc 1 N, (g n) ^ 2) = (count : ℤ) := by
    rw [← squarefree_harmonic_sum_zero_remove
      (fun n => (g n) ^ 2) (by simp [hg0]) N]
    exact hcount
  have hu : (∑ n ∈ Icc 1 N, mobiusHarmonicCeil Q n
      ((g n) ^ 2)) ≤ U := by
    rw [← squarefree_harmonic_sum_zero_remove
      (fun n => mobiusHarmonicCeil Q n ((g n) ^ 2))
      (by simp [mobiusHarmonicCeil]) N]
    exact hupper
  constructor
  · have hci : (∑ n ∈ Icc 1 N, (moebius n : ℤ) ^ 2) = (count : ℤ) := by
      calc
        _ = ∑ n ∈ Icc 1 N, (g n) ^ 2 := by
          apply Finset.sum_congr rfl
          intro n hn
          rw [hmu n (Finset.mem_Icc.mp hn).2]
        _ = _ := hc
    have hr := congrArg (fun z : ℤ => (z : ℝ)) hci
    push_cast at hr
    exact hr
  · calc
      _ ≤ ∑ n ∈ Icc 1 N, (mobiusHarmonicCeil Q n
          ((g n) ^ 2) : ℝ) / (Q : ℝ) := by
        apply Finset.sum_le_sum
        intro n hn
        have hh := mobiusHarmonicCeil_bound Q n ((g n) ^ 2) hQ
        have hnB : n ≤ N := (Finset.mem_Icc.mp hn).2
        rw [hmu n hnB] at hh ⊢
        simpa only [Int.cast_pow,
          abs_of_nonneg (sq_nonneg (((moebius n : ℤ) : ℝ)))] using hh
      _ ≤ (U : ℝ) / (Q : ℝ) := by
        rw [← Finset.sum_div]
        have huR : (∑ n ∈ Icc 1 N, (mobiusHarmonicCeil Q n
          ((g n) ^ 2) : ℝ)) ≤ (U : ℝ) := by
          exact_mod_cast hu
        exact div_le_div_of_nonneg_right huR (Nat.cast_nonneg Q)


end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 2400000
open Finset Nat ArithmeticFunction
namespace Helfgott

theorem mobius_table_prefix_16384_of_checked_pair : ∀ n < 16384,
    mobiusTreeValue 16 mobiusTable1200001 n = moebius n := by
  apply moebius_of_local_checks (mobiusTreeValue 16 mobiusTable1200001) 16384 (by norm_num)
  intro n hn
  apply mobiusTreeCheck_local_sound _ 1200001 9 0
    (MobiusCertTree.branch mobiusTableBlock000 mobiusTableBlock001)
      mobiusValuePair000_checked n (Nat.zero_le n)
  · simpa using hn
  · omega

end Helfgott
end

section
set_option autoImplicit false
open Finset Nat ArithmeticFunction Real
open scoped BigOperators Classical
namespace Helfgott

theorem squarefree_harmonic_initial_10000_groups_reuse :
    (∑ n ∈ Icc 1 10000, ((moebius n : ℤ) : ℝ) ^ 2) = 6083 ∧
    (∑ n ∈ Icc 1 10000, ((moebius n : ℤ) : ℝ) ^ 2 / (n : ℝ)) ≤ 665 / 100 := by
  have hmu : ∀ n ≤ 10000, mobiusTreeValue 16 mobiusTable1200001 n = moebius n := by
    intro n hn
    exact mobius_table_prefix_16384_of_checked_pair n (by omega)
  have h := squarefree_harmonic_initial_of_values 10000 1000000 6650000 6083
    (mobiusTreeValue 16 mobiusTable1200001) (by norm_num) hmu
    squarefree_harmonic_initial_numeric_checks.1 squarefree_harmonic_initial_numeric_checks.2
  convert h using 1 <;> norm_num

end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 2200000
open Finset Nat ArithmeticFunction
open scoped BigOperators Classical

namespace Helfgott

lemma floorRoot_two_eq_one_iff_squarefree (n : ℕ) (hn : n ≠ 0) :
    Nat.floorRoot 2 n = 1 ↔ Squarefree n := by
  constructor
  · intro hroot
    rw [Nat.squarefree_iff_prime_squarefree]
    intro p hp hdvd
    have h : p ∣ Nat.floorRoot 2 n := Nat.pow_dvd_iff_dvd_floorRoot.mp (by simpa [pow_two] using hdvd)
    rw [hroot] at h
    exact hp.ne_one (Nat.dvd_one.mp h)
  · intro hsf
    have h := hsf (Nat.floorRoot 2 n) (by simpa [pow_two] using Nat.floorRoot_pow_dvd (n:=2) (a:=n))
    exact Nat.isUnit_iff.mp h

lemma moebius_divisor_sum (n : ℕ) (hn : n ≠ 0) :
    (∑ d ∈ n.divisors,moebius d) = if n=1 then 1 else 0 := by
  have h := congrArg (fun f : ArithmeticFunction ℤ => f n) moebius_mul_coe_zeta
  rw [ArithmeticFunction.coe_mul_zeta_apply] at h
  simpa [ArithmeticFunction.one_apply,hn] using h

theorem moebius_square_divisor_expansion (n : ℕ) (hn : n ≠ 0) :
    (moebius n)^2 = ∑ d ∈ n.divisors,if d^2 ∣ n then moebius d else 0 := by
  have hroot0 : Nat.floorRoot 2 n ≠ 0 := Nat.floorRoot_ne_zero.mpr ⟨by norm_num,hn⟩
  have he : n.divisors.filter (fun d => d^2 ∣ n) = (Nat.floorRoot 2 n).divisors := by
    ext d
    simp only [Finset.mem_filter,Nat.mem_divisors]
    constructor
    · rintro ⟨⟨hd,hn0⟩,hsq⟩
      exact ⟨Nat.pow_dvd_iff_dvd_floorRoot.mp hsq,hroot0⟩
    · rintro ⟨hd,hr0⟩
      have hsq := Nat.pow_dvd_iff_dvd_floorRoot.mpr hd
      exact ⟨⟨dvd_trans (dvd_pow_self d (by norm_num : 2 ≠ 0)) hsq,hn⟩,hsq⟩
  rw [←Finset.sum_filter,he,moebius_divisor_sum _ hroot0,moebius_sq]
  simp only [floorRoot_two_eq_one_iff_squarefree n hn]

lemma coprime_moebius_divisor_expansion (q n : ℕ) (hq : q ≠ 0) :
    (∑ e ∈ q.divisors,if e ∣ n then moebius e else 0) =
      if Nat.Coprime n q then 1 else 0 := by
  have he : q.divisors.filter (fun e => e ∣ n) = (Nat.gcd n q).divisors := by
    ext e
    simp only [Finset.mem_filter,Nat.mem_divisors]
    have hg : Nat.gcd n q ≠ 0 := Nat.gcd_ne_zero_right hq
    constructor
    · rintro ⟨⟨heq,hq0⟩,hen⟩
      exact ⟨Nat.dvd_gcd hen heq,hg⟩
    · rintro ⟨heg,hg0⟩
      exact ⟨⟨dvd_trans heg (Nat.gcd_dvd_right n q),hq⟩,dvd_trans heg (Nat.gcd_dvd_left n q)⟩
  rw [←Finset.sum_filter,he,moebius_divisor_sum _ (Nat.gcd_ne_zero_right hq)]

theorem squarefree_coprime_pointwise_expansion (q n : ℕ) (hq : q ≠ 0) (hn : n ≠ 0) :
    (if Nat.Coprime n q then ((moebius n : ℤ) : ℝ)^2 else 0) =
      (∑ d ∈ n.divisors,if d^2 ∣ n ∧ Nat.Coprime d q then ((moebius d : ℤ) : ℝ) else 0)*
      (∑ e ∈ q.divisors,if e ∣ n then ((moebius e : ℤ) : ℝ) else 0) := by
  have hcop : (∑ e ∈ q.divisors,if e ∣ n then ((moebius e : ℤ) : ℝ) else 0) =
      if Nat.Coprime n q then 1 else 0 := by
    exact_mod_cast coprime_moebius_divisor_expansion q n hq
  rw [hcop]
  by_cases h : Nat.Coprime n q
  · simp only [if_pos h,mul_one]
    have he : (∑ d ∈ n.divisors,if d^2 ∣ n ∧ Nat.Coprime d q then ((moebius d : ℤ) : ℝ) else 0) =
        ∑ d ∈ n.divisors,if d^2 ∣ n then ((moebius d : ℤ) : ℝ) else 0 := by
      apply Finset.sum_congr rfl
      intro d hd
      have hdc : Nat.Coprime d q := h.of_dvd_left (Nat.dvd_of_mem_divisors hd)
      by_cases hs : d^2 ∣ n <;> simp [hs,hdc]
    rw [he]
    exact_mod_cast moebius_square_divisor_expansion n hn
  · simp [h]

end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 2200000
open Finset Nat ArithmeticFunction
open scoped BigOperators Classical

namespace Helfgott

lemma squarefree_square_divisor_sum_cap (q n N : ℕ) (hn : 0<n) (hnN : n≤N) :
    (∑ d ∈ n.divisors,if d^2 ∣ n ∧ Nat.Coprime d q then ((moebius d : ℤ) : ℝ) else 0) =
      ∑ d ∈ Finset.Icc 1 N.sqrt,if d^2 ∣ n ∧ Nat.Coprime d q then ((moebius d : ℤ) : ℝ) else 0 := by
  rw [←Finset.sum_filter,←Finset.sum_filter]
  congr 1
  ext d
  simp only [Finset.mem_filter,Nat.mem_divisors,Finset.mem_Icc]
  constructor
  · rintro ⟨⟨hd,hn0⟩,hsq,hcop⟩
    have hdpos : 0<d := Nat.pos_of_dvd_of_pos hd hn
    have hdN : d≤N.sqrt := Nat.le_sqrt.mpr (by simpa [pow_two] using (Nat.le_of_dvd hn hsq).trans hnN)
    exact ⟨⟨hdpos,hdN⟩,hsq,hcop⟩
  · rintro ⟨⟨hdpos,hdN⟩,hsq,hcop⟩
    exact ⟨⟨dvd_trans (dvd_pow_self d (by norm_num : 2 ≠ 0)) hsq,hn.ne'⟩,hsq,hcop⟩

theorem squarefree_coprime_count_exact (q N : ℕ) (hq : q ≠ 0) :
    (∑ n ∈ Finset.Icc 1 N,if Nat.Coprime n q then ((moebius n : ℤ) : ℝ)^2 else 0) =
      ∑ d ∈ Finset.Icc 1 N.sqrt,if Nat.Coprime d q then
        ((moebius d : ℤ) : ℝ)*(∑ e ∈ q.divisors,((moebius e : ℤ) : ℝ)*((N/(d^2*e) : ℕ) : ℝ)) else 0 := by
  have hp (n : ℕ) (hn : n∈Finset.Icc 1 N) :
      (if Nat.Coprime n q then ((moebius n : ℤ) : ℝ)^2 else 0) =
        ∑ d ∈ Finset.Icc 1 N.sqrt,∑ e ∈ q.divisors,
          if d^2 ∣ n ∧ Nat.Coprime d q ∧ e ∣ n then
            ((moebius d : ℤ) : ℝ)*((moebius e : ℤ) : ℝ) else 0 := by
    rw [squarefree_coprime_pointwise_expansion q n hq (by have := (Finset.mem_Icc.mp hn).1;omega),
      squarefree_square_divisor_sum_cap q n N (Finset.mem_Icc.mp hn).1 (Finset.mem_Icc.mp hn).2,
      Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro d hd
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro e he
    by_cases hs : d^2 ∣ n <;> by_cases hc : Nat.Coprime d q <;> by_cases he : e ∣ n <;>
      simp [hs,hc,he]
  rw [Finset.sum_congr rfl hp,Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d hd
  rw [Finset.sum_comm]
  by_cases hc : Nat.Coprime d q
  · rw [if_pos hc]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro e he
    have hde : Nat.Coprime (d^2) e := (hc.pow_left 2).of_dvd_right (Nat.dvd_of_mem_divisors he)
    have hdvd (n : ℕ) : (d^2 ∣ n ∧ Nat.Coprime d q ∧ e ∣ n) ↔ d^2*e ∣ n := by
      constructor
      · rintro ⟨hsq,hc,he⟩
        rw [←hde.lcm_eq_mul]
        exact Nat.lcm_dvd hsq he
      · intro h
        rw [←hde.lcm_eq_mul] at h
        exact ⟨(Nat.lcm_dvd_iff.mp h).1,hc,(Nat.lcm_dvd_iff.mp h).2⟩
    simp_rw [hdvd]
    rw [←Finset.sum_filter]
    simp only [Finset.sum_const,smul_eq_mul]
    have hi : (Finset.Icc 1 N).filter (fun n => d^2*e ∣ n) =
        (Finset.Ioc 0 N).filter (fun n => d^2*e ∣ n) := by congr 1
    rw [hi,Nat.Ioc_filter_dvd_card_eq_div]
    ring
  · simp [hc]

end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 1800000
open Finset Nat ArithmeticFunction
open scoped BigOperators Classical

namespace Helfgott

theorem finite_divisor_weight_square_energy (M U : ℕ) (c : ℕ → ℝ) :
    (∑ n ∈ Finset.Icc 1 M,(∑ d ∈ Finset.Icc 1 U,if d ∣ n then c d else 0)^2) =
      ∑ d ∈ Finset.Icc 1 U,∑ e ∈ Finset.Icc 1 U,c d*c e*((M/(Nat.lcm d e) : ℕ) : ℝ) := by
  have hpoint (n : ℕ) : (∑ d ∈ Finset.Icc 1 U,if d ∣ n then c d else 0)^2 =
      ∑ d ∈ Finset.Icc 1 U,∑ e ∈ Finset.Icc 1 U,
        if Nat.lcm d e ∣ n then c d*c e else 0 := by
    rw [pow_two,Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro d hd
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro e he
    by_cases hdvd : d ∣ n <;> by_cases hevd : e ∣ n <;>
      simp [hdvd,hevd,Nat.lcm_dvd_iff]
  simp_rw [hpoint]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d hd
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e he
  rw [←Finset.sum_filter]
  simp only [Finset.sum_const,smul_eq_mul]
  have hi : (Finset.Icc 1 M).filter (fun n => Nat.lcm d e ∣ n) =
      (Finset.Ioc 0 M).filter (fun n => Nat.lcm d e ∣ n) := by
    congr 1
  rw [hi,Nat.Ioc_filter_dvd_card_eq_div]
  ring

end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 2200000
open Finset Nat Real
open scoped BigOperators Classical

namespace Helfgott

lemma nat_div_cast_error_le_one (M k : ℕ) (hk : 0 < k) :
    |((M/k : ℕ) : ℝ)-(M : ℝ)/(k : ℝ)| ≤ 1 := by
  have hlo : ((M/k : ℕ) : ℝ) ≤ (M : ℝ)/(k : ℝ) := Nat.cast_div_le
  have hmod : ((M%k : ℕ) : ℝ) < (k : ℝ) := by exact_mod_cast Nat.mod_lt M hk
  have he : (k : ℝ)*((M/k : ℕ) : ℝ)+((M%k : ℕ) : ℝ)=(M : ℝ) := by exact_mod_cast Nat.div_add_mod M k
  rw [abs_of_nonpos (sub_nonpos.mpr hlo)]
  have hkR : (0 : ℝ)<k := by exact_mod_cast hk
  have hupper : (M : ℝ)/(k : ℝ) ≤ ((M/k : ℕ) : ℝ)+1 := (div_le_iff₀ hkR).mpr (by nlinarith)
  linarith

theorem finite_divisor_weight_square_energy_approximation (M U : ℕ) (c : ℕ → ℝ) :
    |(∑ n ∈ Finset.Icc 1 M,(∑ d ∈ Finset.Icc 1 U,if d ∣ n then c d else 0)^2)-
      (M : ℝ)*(∑ d ∈ Finset.Icc 1 U,∑ e ∈ Finset.Icc 1 U,c d*c e/(Nat.lcm d e : ℝ))| ≤
        (∑ d ∈ Finset.Icc 1 U,|c d|)^2 := by
  rw [finite_divisor_weight_square_energy]
  have he : (∑ d ∈ Finset.Icc 1 U,∑ e ∈ Finset.Icc 1 U,c d*c e*((M/(Nat.lcm d e) : ℕ) : ℝ))-
      (M : ℝ)*(∑ d ∈ Finset.Icc 1 U,∑ e ∈ Finset.Icc 1 U,c d*c e/(Nat.lcm d e : ℝ)) =
      ∑ d ∈ Finset.Icc 1 U,∑ e ∈ Finset.Icc 1 U,c d*c e*
        (((M/(Nat.lcm d e) : ℕ) : ℝ)-(M : ℝ)/(Nat.lcm d e : ℝ)) := by
    rw [Finset.mul_sum,←Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro d hd
    rw [Finset.mul_sum,←Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro e he
    ring
  rw [he]
  calc
    _ ≤ ∑ d ∈ Finset.Icc 1 U,|∑ e ∈ Finset.Icc 1 U,c d*c e*
        (((M/(Nat.lcm d e) : ℕ) : ℝ)-(M : ℝ)/(Nat.lcm d e : ℝ))| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ d ∈ Finset.Icc 1 U,∑ e ∈ Finset.Icc 1 U,|c d| * |c e| := by
      apply Finset.sum_le_sum
      intro d hd
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      apply Finset.sum_le_sum
      intro e he
      have hk : 0 < Nat.lcm d e := Nat.lcm_pos (Finset.mem_Icc.mp hd).1 (Finset.mem_Icc.mp he).1
      rw [abs_mul,abs_mul]
      exact mul_le_of_le_one_right (mul_nonneg (abs_nonneg _) (abs_nonneg _)) (nat_div_cast_error_le_one M _ hk)
    _ = _ := by rw [pow_two,Finset.sum_mul];apply Finset.sum_congr rfl;intro d hd;rw [Finset.mul_sum]

theorem finite_divisor_weight_leading_quadratic_nonneg (U : ℕ) (c : ℕ → ℝ) :
    0 ≤ ∑ d ∈ Finset.Icc 1 U,∑ e ∈ Finset.Icc 1 U,c d*c e/(Nat.lcm d e : ℝ) := by
  let M := U.factorial
  have hM : (0:ℝ)<M := by exact_mod_cast Nat.factorial_pos U
  have hexact : (∑ d ∈ Finset.Icc 1 U,∑ e ∈ Finset.Icc 1 U,c d*c e*((M/(Nat.lcm d e) : ℕ) : ℝ)) =
      (M : ℝ)*(∑ d ∈ Finset.Icc 1 U,∑ e ∈ Finset.Icc 1 U,c d*c e/(Nat.lcm d e : ℝ)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d hd
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro e he
    have hdM : d ∣ M := Nat.dvd_factorial (Finset.mem_Icc.mp hd).1 (Finset.mem_Icc.mp hd).2
    have heM : e ∣ M := Nat.dvd_factorial (Finset.mem_Icc.mp he).1 (Finset.mem_Icc.mp he).2
    rw [Nat.cast_div (Nat.lcm_dvd hdM heM)] <;> try exact_mod_cast (Nat.lcm_pos (Finset.mem_Icc.mp hd).1 (Finset.mem_Icc.mp he).1).ne'
    ring
  have h := finite_divisor_weight_square_energy M U c
  rw [hexact] at h
  have hnonneg : 0 ≤ (∑ n ∈ Finset.Icc 1 M,(∑ d ∈ Finset.Icc 1 U,if d ∣ n then c d else 0)^2) :=
    Finset.sum_nonneg (fun n hn => sq_nonneg _)
  rw [h] at hnonneg
  exact nonneg_of_mul_nonneg_right hnonneg hM

end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 2200000
open Finset Nat ArithmeticFunction
open scoped BigOperators Classical

namespace Helfgott

lemma moebius_reciprocal_divisor_sum_totient (q : ℕ) (hq : q ≠ 0) :
    (∑ e ∈ q.divisors,((moebius e : ℤ) : ℝ)/(e : ℝ)) = (q.totient : ℝ)/(q : ℝ) := by
  have hinv := ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq.mp
    (show ∀ (n : ℕ),n>0 → ∑ i ∈ n.divisors,(i.totient : ℝ) = (n : ℝ) from
      fun n hn => by exact_mod_cast Nat.sum_totient n) q (Nat.pos_of_ne_zero hq)
  rw [Nat.sum_divisorsAntidiagonal (f:=fun x y => ((moebius x : ℤ) : ℝ)*(y : ℝ))] at hinv
  apply (eq_div_iff (show (q : ℝ) ≠ 0 by exact_mod_cast hq)).mpr
  rw [Finset.sum_mul]
  calc
    _ = ∑ e ∈ q.divisors,((moebius e : ℤ) : ℝ)*((q/e : ℕ) : ℝ) := by
      apply Finset.sum_congr rfl
      intro e he
      have he0 : e ≠ 0 := (Nat.pos_of_mem_divisors he).ne'
      rw [Nat.cast_div (Nat.dvd_of_mem_divisors he) (by exact_mod_cast he0)]
      ring
    _ = _ := hinv

theorem squarefree_coprime_count_truncated_error (q N : ℕ) (hq : q ≠ 0) :
    |(∑ n ∈ Finset.Icc 1 N,if Nat.Coprime n q then ((moebius n : ℤ) : ℝ)^2 else 0)-
      (N : ℝ)*((q.totient : ℝ)/(q : ℝ))*
        (∑ d ∈ Finset.Icc 1 N.sqrt,if Nat.Coprime d q then ((moebius d : ℤ) : ℝ)/(d : ℝ)^2 else 0)| ≤
      (N.sqrt : ℝ)*(∑ e ∈ q.divisors,|((moebius e : ℤ) : ℝ)|) := by
  rw [squarefree_coprime_count_exact q N hq]
  have herr : (∑ d ∈ Finset.Icc 1 N.sqrt,if Nat.Coprime d q then
        ((moebius d : ℤ) : ℝ)*(∑ e ∈ q.divisors,((moebius e : ℤ) : ℝ)*((N/(d^2*e) : ℕ) : ℝ)) else 0)-
      (N : ℝ)*((q.totient : ℝ)/(q : ℝ))*
        (∑ d ∈ Finset.Icc 1 N.sqrt,if Nat.Coprime d q then ((moebius d : ℤ) : ℝ)/(d : ℝ)^2 else 0) =
      ∑ d ∈ Finset.Icc 1 N.sqrt,∑ e ∈ q.divisors,
        if Nat.Coprime d q then ((moebius d : ℤ) : ℝ)*((moebius e : ℤ) : ℝ)*
          (((N/(d^2*e) : ℕ) : ℝ)-(N : ℝ)/((d : ℝ)^2*(e : ℝ))) else 0 := by
    rw [←moebius_reciprocal_divisor_sum_totient q hq,Finset.mul_sum,←Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro d hd
    by_cases hc : Nat.Coprime d q
    · simp only [if_pos hc,Finset.mul_sum,Finset.sum_mul,←Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro e he
      ring
    · simp [hc]
  rw [herr]
  calc
    _ ≤ ∑ d ∈ Finset.Icc 1 N.sqrt,|∑ e ∈ q.divisors,
        if Nat.Coprime d q then ((moebius d : ℤ) : ℝ)*((moebius e : ℤ) : ℝ)*
          (((N/(d^2*e) : ℕ) : ℝ)-(N : ℝ)/((d : ℝ)^2*(e : ℝ))) else 0| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ d ∈ Finset.Icc 1 N.sqrt,∑ e ∈ q.divisors,|((moebius e : ℤ) : ℝ)| := by
      apply Finset.sum_le_sum
      intro d hd
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      apply Finset.sum_le_sum
      intro e he
      by_cases hc : Nat.Coprime d q
      · rw [if_pos hc,abs_mul,abs_mul]
        have hdpos := (Finset.mem_Icc.mp hd).1
        have hepos := Nat.pos_of_mem_divisors he
        have herr1 : |((N/(d^2*e) : ℕ) : ℝ)-(N : ℝ)/((d : ℝ)^2*(e : ℝ))| ≤ 1 := by
          simpa only [Nat.cast_mul,Nat.cast_pow] using nat_div_cast_error_le_one N (d^2*e) (Nat.mul_pos (pow_pos hdpos 2) hepos)
        have hmu : |((moebius d : ℤ) : ℝ)| ≤ 1 := by exact_mod_cast abs_moebius_le_one (n:=d)
        calc
          _ ≤ (1*|((moebius e : ℤ) : ℝ)|)*1 :=
            mul_le_mul (mul_le_mul_of_nonneg_right hmu (abs_nonneg _)) herr1 (abs_nonneg _) (by positivity)
          _ = _ := by ring
      · simp [hc]
    _ = _ := by simp [Finset.sum_const,Nat.card_Icc,smul_eq_mul]

end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 2200000
open Finset Nat ArithmeticFunction Real
open scoped BigOperators Classical

namespace Helfgott

lemma principal_character_nat_value (q n : ℕ) :
    (1 : DirichletCharacter ℂ q) n = if Nat.Coprime n q then 1 else 0 := by
  by_cases hc : Nat.Coprime n q
  · rw [if_pos hc]
    exact MulChar.one_apply ((ZMod.isUnit_iff_coprime n q).mpr hc)
  · rw [if_neg hc]
    exact MulChar.map_nonunit _ (fun h => hc ((ZMod.isUnit_iff_coprime n q).mp h))

lemma principal_LSeries_at_two (q : ℕ) (hq : q ≠ 0) :
    LSeries (fun n : ℕ => (1 : DirichletCharacter ℂ q) n) 2 =
      ((Real.pi : ℂ)^2/6)*∏ p ∈ q.primeFactors,(1-1/(p : ℂ)^2) := by
  letI : NeZero q := ⟨hq⟩
  have h := DirichletCharacter.LSeries_changeLevel (Nat.one_dvd q)
    (1 : DirichletCharacter ℂ 1) (s:=2) (by norm_num)
  rw [DirichletCharacter.changeLevel_one,DirichletCharacter.LSeries_modOne_eq,
    LSeries_one_eq_riemannZeta (by norm_num),riemannZeta_two] at h
  rw [h]
  congr 1
  apply Finset.prod_congr rfl
  intro p hp
  rw [principal_character_nat_value]
  try simp only [Nat.coprime_one_right,if_true,one_mul]
  rw [Complex.cpow_neg]
  norm_num [Complex.cpow_natCast]

lemma principal_moebius_LSeries_at_two (q : ℕ) :
    LSeries (fun n : ℕ => (1 : DirichletCharacter ℂ q) n * (moebius n : ℂ)) 2 =
      ((∑' n : ℕ,if Nat.Coprime n q then ((moebius n : ℤ) : ℝ)/(n : ℝ)^2 else 0) : ℂ) := by
  rw [LSeries]
  apply tsum_congr
  intro n
  by_cases hn : n=0
  · subst n
    simp [LSeries.term]
  · rw [LSeries.term_of_ne_zero hn,principal_character_nat_value]
    norm_num [Complex.cpow_natCast]
    split_ifs <;> push_cast <;> ring

theorem squarefree_coprime_density_series (q : ℕ) (hq : q ≠ 0) :
    (∑' n : ℕ,if Nat.Coprime n q then ((moebius n : ℤ) : ℝ)/(n : ℝ)^2 else 0) =
      (6/Real.pi^2)*∏ p ∈ q.primeFactors,(1-1/(p : ℝ)^2)⁻¹ := by
  have h := DirichletCharacter.LSeries.mul_mu_eq_one (1 : DirichletCharacter ℂ q) (s:=2) (by norm_num)
  change LSeries (fun n : ℕ => (1 : DirichletCharacter ℂ q) n) 2 *
    LSeries (fun n : ℕ => (1 : DirichletCharacter ℂ q) n * (moebius n : ℂ)) 2 = 1 at h
  rw [principal_LSeries_at_two q hq,principal_moebius_LSeries_at_two] at h
  have hr : ((Real.pi^2/6)*(∏ p ∈ q.primeFactors,(1-1/(p : ℝ)^2)))*
      (∑' n : ℕ,if Nat.Coprime n q then ((moebius n : ℤ) : ℝ)/(n : ℝ)^2 else 0) = 1 := by
    apply Complex.ofReal_injective
    push_cast
    simpa only [apply_ite,Complex.ofReal_div,Complex.ofReal_pow,
      Complex.ofReal_intCast,Complex.ofReal_natCast,Complex.ofReal_zero] using h
  have hp0 : (∏ p ∈ q.primeFactors,(1-1/(p : ℝ)^2)) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro p hp
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
    have hsq : (1 : ℝ)<(p : ℝ)^2 := by nlinarith
    have hinv : 1/(p : ℝ)^2 < 1 := (div_lt_one (by positivity)).mpr hsq
    linarith
  rw [Finset.prod_inv_distrib]
  have hpi : Real.pi^2 ≠ 0 := pow_ne_zero 2 Real.pi_ne_zero
  have hx : (∑' n : ℕ,if Nat.Coprime n q then ((moebius n : ℤ) : ℝ)/(n : ℝ)^2 else 0) =
      1/((Real.pi^2/6)*(∏ p ∈ q.primeFactors,(1-1/(p : ℝ)^2))) := by
    apply (eq_div_iff (mul_ne_zero (div_ne_zero hpi (by norm_num)) hp0)).mpr
    simpa only [mul_comm] using hr
  rw [hx]
  field_simp [hpi,hp0]

end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 2200000
open Finset Nat ArithmeticFunction Real
open scoped BigOperators Classical

namespace Helfgott

lemma shifted_reciprocal_square_sum_le (D K : ℕ) (hD : 1≤D) :
    (∑ n ∈ Finset.range K,1/((n+D+1 : ℕ) : ℝ)^2) ≤ 1/(D : ℝ) := by
  have hpoint (n : ℕ) : 1/((n+D+1 : ℕ) : ℝ)^2 ≤
      1/((n+D : ℕ) : ℝ)-1/((n+D+1 : ℕ) : ℝ) := by
    have hpos : (0 : ℝ)<((n+D : ℕ) : ℝ) := by exact_mod_cast (show 0<n+D by omega)
    push_cast
    field_simp
    nlinarith
  calc
    _ ≤ ∑ n ∈ Finset.range K,(1/((n+D : ℕ) : ℝ)-1/((n+D+1 : ℕ) : ℝ)) := Finset.sum_le_sum (fun n hn => hpoint n)
    _ = 1/(D : ℝ)-1/((K+D : ℕ) : ℝ) := by
      simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm,add_assoc,add_comm,add_left_comm] using Finset.sum_range_sub' (fun n : ℕ => 1/((n+D : ℕ) : ℝ)) K
    _ ≤ _ := sub_le_self _ (by positivity)

lemma shifted_reciprocal_square_tsum_le (D : ℕ) (hD : 1≤D) :
    (∑' n : ℕ,1/((n+D+1 : ℕ) : ℝ)^2) ≤ 1/(D : ℝ) :=
  Real.tsum_le_of_sum_range_le (fun n => by positivity) (fun K => shifted_reciprocal_square_sum_le D K hD)

lemma coprime_moebius_reciprocal_square_norm_le (q n : ℕ) :
    ‖(if Nat.Coprime n q then ((moebius n : ℤ) : ℝ)/(n : ℝ)^2 else 0)‖ ≤ 1/(n : ℝ)^2 := by
  by_cases hc : Nat.Coprime n q
  · rw [if_pos hc,Real.norm_eq_abs,abs_div]
    rw [show |(n : ℝ)^2| = (n : ℝ)^2 from abs_of_nonneg (sq_nonneg _)]
    exact div_le_div_of_nonneg_right (by exact_mod_cast abs_moebius_le_one (n:=n)) (sq_nonneg _)
  · rw [if_neg hc,norm_zero]
    positivity

lemma coprime_moebius_reciprocal_square_summable (q : ℕ) :
    Summable (fun n : ℕ => if Nat.Coprime n q then ((moebius n : ℤ) : ℝ)/(n : ℝ)^2 else 0) := by
  exact Summable.of_norm_bounded hasSum_zeta_two.summable (fun n => coprime_moebius_reciprocal_square_norm_le q n)

lemma reciprocal_square_tsum_le_two : (∑' n : ℕ,1/(n : ℝ)^2) ≤ 2 := by
  have h := hasSum_zeta_two.summable.sum_add_tsum_nat_add 2
  norm_num [Finset.sum_range_succ] at h
  have ht := shifted_reciprocal_square_tsum_le 1 (by norm_num)
  norm_num [add_assoc] at ht
  simp only [one_div]
  linarith

lemma coprime_moebius_density_norm_le_two (q : ℕ) (hq : q ≠ 0) :
    |(6/Real.pi^2)*∏ p ∈ q.primeFactors,(1-1/(p : ℝ)^2)⁻¹| ≤ 2 := by
  rw [←squarefree_coprime_density_series q hq]
  have hf := coprime_moebius_reciprocal_square_summable q
  calc
    _ ≤ ∑' n : ℕ,‖if Nat.Coprime n q then ((moebius n : ℤ) : ℝ)/(n : ℝ)^2 else 0‖ := by
      simpa only [Real.norm_eq_abs] using norm_tsum_le_tsum_norm hf.norm
    _ ≤ ∑' n : ℕ,1/(n : ℝ)^2 := hf.norm.tsum_le_tsum
      (fun n => coprime_moebius_reciprocal_square_norm_le q n) hasSum_zeta_two.summable
    _ ≤ _ := reciprocal_square_tsum_le_two

theorem coprime_moebius_density_tail_error (q D : ℕ) (hq : q ≠ 0) (hD : 1≤D) :
    |(6/Real.pi^2)*∏ p ∈ q.primeFactors,(1-1/(p : ℝ)^2)⁻¹-
      (∑ n ∈ Finset.Icc 1 D,if Nat.Coprime n q then ((moebius n : ℤ) : ℝ)/(n : ℝ)^2 else 0)| ≤ 1/(D : ℝ) := by
  let f : ℕ → ℝ := fun n => if Nat.Coprime n q then ((moebius n : ℤ) : ℝ)/(n : ℝ)^2 else 0
  have hf : Summable f := coprime_moebius_reciprocal_square_summable q
  have hs : (∑ n ∈ Finset.range (D+1),f n) = ∑ n ∈ Finset.Icc 1 D,f n := by
    rw [Finset.range_eq_Ico]
    have he : Finset.Ico 0 (D+1) = insert 0 (Finset.Icc 1 D) := by ext n;simp;omega
    rw [he,Finset.sum_insert (by simp)]
    simp [f]
  rw [←squarefree_coprime_density_series q hq]
  change |(∑' n : ℕ,f n)-(∑ n ∈ Finset.Icc 1 D,f n)| ≤ _
  have he := hf.sum_add_tsum_nat_add (D+1)
  rw [hs] at he
  have herr : (∑' n : ℕ,f n)-(∑ n ∈ Finset.Icc 1 D,f n) = ∑' n : ℕ,f (n+(D+1)) := by linarith
  rw [herr]
  have htail : Summable (fun n : ℕ => f (n+(D+1))) := hf.comp_injective (fun n m h => by omega)
  have hnorm : Summable (fun n : ℕ => 1/((n+D+1 : ℕ) : ℝ)^2) :=
    hasSum_zeta_two.summable.comp_injective (fun n m h => by omega)
  calc
    _ ≤ ∑' n : ℕ,‖f (n+(D+1))‖ := by simpa only [Real.norm_eq_abs] using norm_tsum_le_tsum_norm htail.norm
    _ ≤ ∑' n : ℕ,1/((n+D+1 : ℕ) : ℝ)^2 :=
      htail.norm.tsum_le_tsum (fun n => by simpa [f,Nat.add_assoc] using coprime_moebius_reciprocal_square_norm_le q (n+(D+1))) hnorm
    _ ≤ _ := shifted_reciprocal_square_tsum_le D hD

end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 2200000
open Finset Nat ArithmeticFunction Real
open scoped BigOperators Classical

namespace Helfgott

theorem squarefree_coprime_rational_floor_error (q N e : ℕ) (hq : q ≠ 0) (he : 1≤e) :
    |(∑ d ∈ Finset.Icc 1 (N/e).sqrt,if Nat.Coprime d q then
        ((moebius d : ℤ) : ℝ)*((N/(d^2*e) : ℕ) : ℝ) else 0)-
      ((N : ℝ)/(e : ℝ))*((6/Real.pi^2)*∏ p ∈ q.primeFactors,(1-1/(p : ℝ)^2)⁻¹)| ≤
      3*Real.sqrt ((N : ℝ)/(e : ℝ)) := by
  let X : ℝ := (N : ℝ)/(e : ℝ)
  let D : ℕ := (N/e).sqrt
  let C : ℝ := (6/Real.pi^2)*∏ p ∈ q.primeFactors,(1-1/(p : ℝ)^2)⁻¹
  have hX : 0≤X := by dsimp [X];positivity
  have heR : (0 : ℝ)<e := by exact_mod_cast he
  have hfloorlo : ((N/e : ℕ) : ℝ) ≤ X := Nat.cast_div_le
  have hfloorhi : X ≤ ((N/e : ℕ) : ℝ)+1 := by
    have h := nat_div_cast_error_le_one N e he
    rw [abs_of_nonpos (sub_nonpos.mpr hfloorlo)] at h
    linarith
  have hDlo : (D : ℝ)^2≤X := (show (D : ℝ)^2 ≤ ((N/e : ℕ) : ℝ) by exact_mod_cast Nat.sqrt_le' (N/e)).trans hfloorlo
  have hDhi : X≤((D : ℝ)+1)^2 := by
    have h : ((N/e : ℕ) : ℝ)+1 ≤ ((D : ℝ)+1)^2 := by
      have hn := Nat.lt_succ_sqrt' (N/e)
      have hn' : N/e+1 ≤ (D+1)^2 := by simpa [D,Nat.succ_eq_add_one] using hn
      exact_mod_cast hn'
    exact hfloorhi.trans h
  have hsqrtlo : (D : ℝ) ≤ Real.sqrt X := by
    have hs := Real.sqrt_sq (show 0≤(D : ℝ) by positivity)
    simpa only [hs] using Real.sqrt_le_sqrt hDlo
  have hsqrthi : Real.sqrt X≤(D : ℝ)+1 := by
    simpa only [Real.sqrt_sq (show 0≤(D : ℝ)+1 by positivity)] using Real.sqrt_le_sqrt hDhi
  have hC : |C|≤2 := coprime_moebius_density_norm_le_two q hq
  change |(∑ d ∈ Finset.Icc 1 D,if Nat.Coprime d q then
        ((moebius d : ℤ) : ℝ)*((N/(d^2*e) : ℕ) : ℝ) else 0)-X*C|≤3*Real.sqrt X
  by_cases hD0 : D=0
  · rw [hD0]
    simp only [Finset.Icc_eq_empty_of_lt (by norm_num : (0:ℕ)<1),Finset.sum_empty,zero_sub,abs_neg,abs_mul,abs_of_nonneg hX]
    have hroot1 : Real.sqrt X≤1 := by simpa only [hD0,Nat.cast_zero,zero_add] using hsqrthi
    have hXroot : X≤Real.sqrt X := by nlinarith [Real.sq_sqrt hX,Real.sqrt_nonneg X]
    have hbound : X*|C|≤X*2 := mul_le_mul_of_nonneg_left hC hX
    nlinarith [Real.sqrt_nonneg X]
  · have hD : 1≤D := Nat.pos_of_ne_zero hD0
    have hDR : (0 : ℝ)<D := by exact_mod_cast hD
    have herr : |(∑ d ∈ Finset.Icc 1 D,if Nat.Coprime d q then
          ((moebius d : ℤ) : ℝ)*((N/(d^2*e) : ℕ) : ℝ) else 0)-
        X*(∑ d ∈ Finset.Icc 1 D,if Nat.Coprime d q then ((moebius d : ℤ) : ℝ)/(d : ℝ)^2 else 0)|≤(D : ℝ) := by
      rw [Finset.mul_sum,←Finset.sum_sub_distrib]
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      calc
        _ ≤ ∑ d ∈ Finset.Icc 1 D,(1 : ℝ) := by
          apply Finset.sum_le_sum
          intro d hd
          by_cases hc : Nat.Coprime d q
          · rw [if_pos hc,if_pos hc]
            have hdR : (d : ℝ)≠0 := by exact_mod_cast (Nat.ne_of_gt (Finset.mem_Icc.mp hd).1)
            have hr : ((moebius d : ℤ) : ℝ)*((N/(d^2*e) : ℕ) : ℝ)-X*(((moebius d : ℤ) : ℝ)/(d : ℝ)^2) =
                ((moebius d : ℤ) : ℝ)*(((N/(d^2*e) : ℕ) : ℝ)-(N : ℝ)/((d^2*e : ℕ) : ℝ)) := by
              dsimp only [X]
              push_cast
              field_simp <;> ring
            rw [hr,abs_mul]
            have hmu : |((moebius d : ℤ) : ℝ)|≤1 := by exact_mod_cast abs_moebius_le_one (n:=d)
            exact mul_le_one₀ hmu (abs_nonneg _) (nat_div_cast_error_le_one N _ (Nat.mul_pos (pow_pos (Finset.mem_Icc.mp hd).1 2) he))
          · simp [if_neg hc]
        _ = _ := by simp [Nat.card_Icc]
    have htail := coprime_moebius_density_tail_error q D hq hD
    change |C-(∑ d ∈ Finset.Icc 1 D,if Nat.Coprime d q then ((moebius d : ℤ) : ℝ)/(d : ℝ)^2 else 0)|≤1/(D : ℝ) at htail
    have hbound : |(∑ d ∈ Finset.Icc 1 D,if Nat.Coprime d q then
          ((moebius d : ℤ) : ℝ)*((N/(d^2*e) : ℕ) : ℝ) else 0)-X*C|≤(D : ℝ)+X/(D : ℝ) := by
      have heq (S : ℝ) : (∑ d ∈ Finset.Icc 1 D,if Nat.Coprime d q then
          ((moebius d : ℤ) : ℝ)*((N/(d^2*e) : ℕ) : ℝ) else 0)-X*C =
          ((∑ d ∈ Finset.Icc 1 D,if Nat.Coprime d q then
          ((moebius d : ℤ) : ℝ)*((N/(d^2*e) : ℕ) : ℝ) else 0)-X*S)+X*(S-C) := by ring
      rw [heq (∑ d ∈ Finset.Icc 1 D,if Nat.Coprime d q then ((moebius d : ℤ) : ℝ)/(d : ℝ)^2 else 0)]
      refine (abs_add_le _ _).trans (add_le_add herr ?_)
      rw [abs_mul,abs_of_nonneg hX,abs_sub_comm]
      simpa only [div_eq_mul_inv,one_mul] using mul_le_mul_of_nonneg_left htail hX
    refine hbound.trans ?_
    have hrootD : Real.sqrt X≤2*(D : ℝ) := by
      have h1 : (1 : ℝ)≤D := by exact_mod_cast hD
      linarith
    have hxdiv : X/(D : ℝ)≤2*Real.sqrt X := (div_le_iff₀ hDR).mpr (by nlinarith [Real.sq_sqrt hX,Real.sqrt_nonneg X])
    linarith

end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 2400000
open Finset Nat ArithmeticFunction Real
open scoped BigOperators Classical

namespace Helfgott

lemma squarefree_coprime_count_reordered (q N : ℕ) (hq : q ≠ 0) :
    (∑ n ∈ Finset.Icc 1 N,if Nat.Coprime n q then ((moebius n : ℤ) : ℝ)^2 else 0) =
      ∑ e ∈ q.divisors,((moebius e : ℤ) : ℝ)*
        (∑ d ∈ Finset.Icc 1 (N/e).sqrt,if Nat.Coprime d q then
          ((moebius d : ℤ) : ℝ)*((N/(d^2*e) : ℕ) : ℝ) else 0) := by
  rw [squarefree_coprime_count_exact q N hq]
  have hdist : (∑ d ∈ Finset.Icc 1 N.sqrt,if Nat.Coprime d q then
        ((moebius d : ℤ) : ℝ)*(∑ e ∈ q.divisors,((moebius e : ℤ) : ℝ)*((N/(d^2*e) : ℕ) : ℝ)) else 0) =
      ∑ d ∈ Finset.Icc 1 N.sqrt,∑ e ∈ q.divisors,
        ((moebius e : ℤ) : ℝ)*(if Nat.Coprime d q then ((moebius d : ℤ) : ℝ)*((N/(d^2*e) : ℕ) : ℝ) else 0) := by
    apply Finset.sum_congr rfl
    intro d hd
    by_cases hc : Nat.Coprime d q
    · rw [if_pos hc,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro e he
      rw [if_pos hc]
      ring
    · simp [if_neg hc]
  rw [hdist,Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e he
  rw [←Finset.mul_sum]
  congr 1
  symm
  apply Finset.sum_subset
  · intro d hd
    exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hd).1,
      (Finset.mem_Icc.mp hd).2.trans (Nat.sqrt_le_sqrt (Nat.div_le_self N e))⟩
  · intro d hd hnot
    have hdlarge : (N/e).sqrt<d := by
      have hd1 := (Finset.mem_Icc.mp hd).1
      have hnot' : ¬(1≤d ∧ d≤(N/e).sqrt) := by simpa only [Finset.mem_Icc] using hnot
      omega
    have hd2 : N/e<d^2 := Nat.sqrt_lt'.mp hdlarge
    have hdiv : N/(d^2*e)=(N/e)/d^2 := by rw [Nat.div_div_eq_div_mul,Nat.mul_comm]
    rw [hdiv,Nat.div_eq_of_lt hd2]
    simp

lemma squarefree_coprime_density_normalization (q : ℕ) (hq : q ≠ 0) :
    ((q.totient : ℝ)/(q : ℝ))*((6/Real.pi^2)*∏ p ∈ q.primeFactors,(1-1/(p : ℝ)^2)⁻¹) =
      (6/Real.pi^2)*∏ p ∈ q.primeFactors,(p : ℝ)/((p : ℝ)+1) := by
  have htot : (q.totient : ℝ)=(q : ℝ)*∏ p ∈ q.primeFactors,(1-(p : ℝ)⁻¹) := by
    have h := congrArg (fun r : ℚ => (r : ℝ)) (Nat.totient_eq_mul_prod_factors q)
    push_cast at h
    exact h
  have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast hq
  rw [htot,mul_div_cancel_left₀ _ hqR]
  have hprod : (∏ p ∈ q.primeFactors,(1-(p : ℝ)⁻¹))*(∏ p ∈ q.primeFactors,(1-1/(p : ℝ)^2)⁻¹) =
      ∏ p ∈ q.primeFactors,(p : ℝ)/((p : ℝ)+1) := by
    rw [←Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro p hp
    have hp2 : (2 : ℝ)≤p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
    have hp0 : (p : ℝ) ≠ 0 := by linarith
    have hp1 : (p : ℝ)-1 ≠ 0 := by linarith
    have hpp : (p : ℝ)+1 ≠ 0 := by linarith
    have hden : 1-1/(p : ℝ)^2 ≠ 0 := by
      have hsq : (1 : ℝ)<(p : ℝ)^2 := by nlinarith
      have hi : 1/(p : ℝ)^2<1 := (div_lt_one (by positivity)).mpr hsq
      linarith
    rw [←div_eq_mul_inv]
    apply (div_eq_iff hden).mpr
    field_simp [hp0,hpp] <;> ring
  calc
    _ = (6/Real.pi^2)*((∏ p ∈ q.primeFactors,(1-(p : ℝ)⁻¹))*(∏ p ∈ q.primeFactors,(1-1/(p : ℝ)^2)⁻¹)) := by ring
    _ = _ := by rw [hprod]

theorem squarefree_coprime_count_square_root_error (q N : ℕ) (hq : q ≠ 0) :
    |(∑ n ∈ Finset.Icc 1 N,if Nat.Coprime n q then ((moebius n : ℤ) : ℝ)^2 else 0)-
      (N : ℝ)*(6/Real.pi^2)*(∏ p ∈ q.primeFactors,(p : ℝ)/((p : ℝ)+1))| ≤
      3*Real.sqrt (N : ℝ)*(∑ e ∈ q.divisors,|((moebius e : ℤ) : ℝ)|/Real.sqrt (e : ℝ)) := by
  let C : ℝ := (6/Real.pi^2)*∏ p ∈ q.primeFactors,(1-1/(p : ℝ)^2)⁻¹
  have hmain : (N : ℝ)*(6/Real.pi^2)*(∏ p ∈ q.primeFactors,(p : ℝ)/((p : ℝ)+1)) =
      ∑ e ∈ q.divisors,((moebius e : ℤ) : ℝ)*((N : ℝ)/(e : ℝ))*C := by
    have h := squarefree_coprime_density_normalization q hq
    change ((q.totient : ℝ)/(q : ℝ))*C = _ at h
    rw [mul_assoc,←h,←moebius_reciprocal_divisor_sum_totient q hq,Finset.sum_mul,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro e he
    ring
  rw [squarefree_coprime_count_reordered q N hq,hmain,←Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ e ∈ q.divisors,|((moebius e : ℤ) : ℝ)*
        (∑ d ∈ Finset.Icc 1 (N/e).sqrt,if Nat.Coprime d q then
          ((moebius d : ℤ) : ℝ)*((N/(d^2*e) : ℕ) : ℝ) else 0)-((moebius e : ℤ) : ℝ)*((N : ℝ)/(e : ℝ))*C| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ e ∈ q.divisors,|((moebius e : ℤ) : ℝ)| * (3*Real.sqrt ((N : ℝ)/(e : ℝ))) := by
      apply Finset.sum_le_sum
      intro e he
      have hepos := Nat.pos_of_mem_divisors he
      have herr := squarefree_coprime_rational_floor_error q N e hq hepos
      change |(∑ d ∈ Finset.Icc 1 (N/e).sqrt,if Nat.Coprime d q then
          ((moebius d : ℤ) : ℝ)*((N/(d^2*e) : ℕ) : ℝ) else 0)-((N : ℝ)/(e : ℝ))*C| ≤ _ at herr
      rw [mul_assoc,←mul_sub,abs_mul]
      exact mul_le_mul_of_nonneg_left herr (abs_nonneg _)
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro e he
      rw [Real.sqrt_div (by positivity)]
      ring

end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 2400000
open Finset Nat Real MeasureTheory
open scoped BigOperators Classical Interval

namespace Helfgott

lemma log_weight_sum_zero_remove (c : ℕ → ℝ) (N : ℕ) :
    (∑ d ∈ Finset.Icc 0 N, c d * Real.log (d : ℝ) ^ 2) =
      ∑ d ∈ Finset.Icc 1 N, c d * Real.log (d : ℝ) ^ 2 := by
  rw [← Finset.insert_Icc_succ_left_eq_Icc (Nat.zero_le N)]
  rw [Finset.sum_insert (by simp)]
  simp only [Nat.cast_zero, Real.log_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0),
    mul_zero, zero_add]
  rfl

lemma log_weight_sum_Ioc_difference (c : ℕ → ℝ) (A N : ℕ) (hAN : A ≤ N) :
    (∑ d ∈ Finset.Ioc A N, c d) =
      (∑ d ∈ Finset.Icc 1 N, c d) - ∑ d ∈ Finset.Icc 1 A, c d := by
  have h := Finset.sum_Ioc_consecutive c (Nat.zero_le A) hAN
  simp only [← Finset.Icc_succ_left_eq_Ioc, Order.succ_eq_add_one, zero_add] at h
  simp only [← Finset.Icc_succ_left_eq_Ioc, Order.succ_eq_add_one] at ⊢
  linarith

lemma hasDerivAt_log_inv_sq (t : ℝ) (ht : 1 < t) :
    HasDerivAt (fun t : ℝ => (Real.log t ^ 2)⁻¹)
      (-(2 / (t * Real.log t ^ 3))) t := by
  have ht0 : t ≠ 0 := by linarith
  have hl0 : Real.log t ≠ 0 := (Real.log_pos ht).ne'
  have hd := ((Real.hasDerivAt_log ht0).pow 2).inv (pow_ne_zero 2 hl0)
  convert hd using 1
  all_goals first | rfl | (simp only [Pi.pow_apply]; field_simp [hl0, ht0]; ring)

lemma log_weight_deriv_continuous (a x : ℝ) (ha : 1 < a) :
    ContinuousOn (fun t : ℝ => -(2 / (t * Real.log t ^ 3))) (Set.Icc a x) := by
  have ht0 : ∀ t ∈ Set.Icc a x, t ≠ 0 := by
    intro t ht; linarith [ht.1]
  have hl : ContinuousOn Real.log (Set.Icc a x) :=
    Real.continuousOn_log.mono (fun t ht => ht0 t ht)
  have hl0 : ∀ t ∈ Set.Icc a x, Real.log t ≠ 0 := by
    intro t ht; exact (Real.log_pos (lt_of_lt_of_le ha ht.1)).ne'
  exact (continuousOn_const.div (continuousOn_id.mul (hl.pow 3))
    (fun t ht => mul_ne_zero (ht0 t ht) (pow_ne_zero 3 (hl0 t ht)))).neg

lemma log_weight_kernel_intervalIntegrable (c : ℕ → ℝ) (a x : ℝ)
    (ha : 1 < a) (hax : a ≤ x) :
    IntervalIntegrable (fun t : ℝ =>
      (∑ d ∈ Finset.Icc 1 ⌊t⌋₊, c d * Real.log (d : ℝ) ^ 2) /
        (t * Real.log t ^ 3)) volume a x := by
  have hf : ContinuousOn (fun t : ℝ => (t * Real.log t ^ 3)⁻¹) (Set.Icc a x) := by
    have ht0 : ∀ t ∈ Set.Icc a x, t ≠ 0 := by intro t ht; linarith [ht.1]
    have hl : ContinuousOn Real.log (Set.Icc a x) :=
      Real.continuousOn_log.mono (fun t ht => ht0 t ht)
    exact (continuousOn_id.mul (hl.pow 3)).inv₀ (fun t ht =>
      mul_ne_zero (ht0 t ht) (pow_ne_zero 3 (Real.log_pos (lt_of_lt_of_le ha ht.1)).ne'))
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le hax]
  have h := integrableOn_mul_sum_Icc (fun d => c d * Real.log (d : ℝ) ^ 2)
    (by linarith : 0 ≤ a) hf.integrableOn_Icc (m := 1)
  simpa only [div_eq_mul_inv, mul_comm] using h

theorem log_squared_weight_removal_identity (c : ℕ → ℝ) (a x : ℝ)
    (ha : 1 < a) (hax : a ≤ x) :
    (∑ d ∈ Finset.Icc 1 ⌊x⌋₊, c d) =
      (∑ d ∈ Finset.Icc 1 ⌊a⌋₊, c d) -
        (∑ d ∈ Finset.Icc 1 ⌊a⌋₊, c d * Real.log (d : ℝ) ^ 2) / Real.log a ^ 2 +
        (∑ d ∈ Finset.Icc 1 ⌊x⌋₊, c d * Real.log (d : ℝ) ^ 2) / Real.log x ^ 2 +
        2 * ∫ t in a..x,
          (∑ d ∈ Finset.Icc 1 ⌊t⌋₊, c d * Real.log (d : ℝ) ^ 2) /
            (t * Real.log t ^ 3) := by
  have hd : ∀ t ∈ Set.Icc a x,
      DifferentiableAt ℝ (fun t : ℝ => (Real.log t ^ 2)⁻¹) t := by
    intro t ht; exact (hasDerivAt_log_inv_sq t (lt_of_lt_of_le ha ht.1)).differentiableAt
  have hdv : ∀ t ∈ Set.Icc a x,
      deriv (fun t : ℝ => (Real.log t ^ 2)⁻¹) t = -(2 / (t * Real.log t ^ 3)) := by
    intro t ht; exact (hasDerivAt_log_inv_sq t (lt_of_lt_of_le ha ht.1)).deriv
  have hi : IntegrableOn (deriv (fun t : ℝ => (Real.log t ^ 2)⁻¹)) (Set.Icc a x) :=
    ((log_weight_deriv_continuous a x ha).integrableOn_Icc).congr_fun
      (fun t ht => (hdv t ht).symm) measurableSet_Icc
  have h := sum_mul_eq_sub_sub_integral_mul
    (fun d => c d * Real.log (d : ℝ) ^ 2) (by linarith : 0 ≤ a) hax hd hi
  simp_rw [log_weight_sum_zero_remove c] at h
  have hleft :
      (∑ d ∈ Finset.Ioc ⌊a⌋₊ ⌊x⌋₊,
        (Real.log (d : ℝ) ^ 2)⁻¹ * (c d * Real.log (d : ℝ) ^ 2)) =
      (∑ d ∈ Finset.Icc 1 ⌊x⌋₊, c d) - ∑ d ∈ Finset.Icc 1 ⌊a⌋₊, c d := by
    rw [← log_weight_sum_Ioc_difference c _ _ (Nat.floor_le_floor hax)]
    apply Finset.sum_congr rfl
    intro d hd
    have hda : a < (d : ℝ) := (Nat.floor_lt (by linarith : 0 ≤ a)).mp (Finset.mem_Ioc.mp hd).1
    have hl : Real.log (d : ℝ) ≠ 0 := (Real.log_pos (lt_trans ha hda)).ne'
    field_simp
  rw [hleft] at h
  have hint :
      (∫ t in Set.Ioc a x, deriv (fun t : ℝ => (Real.log t ^ 2)⁻¹) t *
        ∑ d ∈ Finset.Icc 1 ⌊t⌋₊, c d * Real.log (d : ℝ) ^ 2) =
      -(2 * ∫ t in a..x,
        (∑ d ∈ Finset.Icc 1 ⌊t⌋₊, c d * Real.log (d : ℝ) ^ 2) /
          (t * Real.log t ^ 3)) := by
    rw [← intervalIntegral.integral_of_le hax]
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le hax] at ht
    dsimp only
    rw [hdv t ht]
    ring
  rw [hint] at h
  simp only [div_eq_mul_inv, mul_comm ((Real.log _) ^ 2)⁻¹] at h ⊢
  linarith

lemma log_squared_weight_removal_bound (c : ℕ → ℝ) (a x : ℝ)
    (ha : 1 < a) (hax : a ≤ x) :
    |∑ d ∈ Finset.Icc 1 ⌊x⌋₊, c d| ≤
      |(∑ d ∈ Finset.Icc 1 ⌊a⌋₊, c d) -
        (∑ d ∈ Finset.Icc 1 ⌊a⌋₊, c d * Real.log (d : ℝ) ^ 2) / Real.log a ^ 2| +
        |∑ d ∈ Finset.Icc 1 ⌊x⌋₊, c d * Real.log (d : ℝ) ^ 2| / Real.log x ^ 2 +
        2 * ∫ t in a..x,
          |∑ d ∈ Finset.Icc 1 ⌊t⌋₊, c d * Real.log (d : ℝ) ^ 2| /
            (t * Real.log t ^ 3) := by
  let M : ℝ → ℝ := fun t => ∑ d ∈ Finset.Icc 1 ⌊t⌋₊, c d
  let W : ℝ → ℝ := fun t => ∑ d ∈ Finset.Icc 1 ⌊t⌋₊, c d * Real.log (d : ℝ) ^ 2
  have hden : ∀ t ∈ Set.Icc a x, 0 < t * Real.log t ^ 3 := by
    intro t ht
    exact mul_pos (by linarith [ht.1]) (pow_pos (Real.log_pos (lt_of_lt_of_le ha ht.1)) 3)
  have hrem : |∫ t in a..x, W t / (t * Real.log t ^ 3)| ≤
      ∫ t in a..x, |W t| / (t * Real.log t ^ 3) := by
    calc
      _ ≤ ∫ t in a..x, |W t / (t * Real.log t ^ 3)| :=
        intervalIntegral.abs_integral_le_integral_abs hax
      _ = _ := by
        apply intervalIntegral.integral_congr
        intro t ht
        rw [Set.uIcc_of_le hax] at ht
        dsimp only
        rw [abs_div, abs_of_pos (hden t ht)]
  have hid := log_squared_weight_removal_identity c a x ha hax
  change M x = (M a - W a / Real.log a ^ 2) + W x / Real.log x ^ 2 +
    2 * ∫ t in a..x, W t / (t * Real.log t ^ 3) at hid
  change |M x| ≤ |M a - W a / Real.log a ^ 2| + |W x| / Real.log x ^ 2 +
    2 * ∫ t in a..x, |W t| / (t * Real.log t ^ 3)
  rw [hid]
  have h1 := abs_add_le (M a - W a / Real.log a ^ 2) (W x / Real.log x ^ 2)
  have h2 := abs_add_le ((M a - W a / Real.log a ^ 2) + W x / Real.log x ^ 2)
    (2 * ∫ t in a..x, W t / (t * Real.log t ^ 3))
  have hW : |W x / Real.log x ^ 2| = |W x| / Real.log x ^ 2 := by
    rw [abs_div, abs_of_pos (pow_pos (Real.log_pos (lt_of_lt_of_le ha hax)) 2)]
  have h3 : |2 * ∫ t in a..x, W t / (t * Real.log t ^ 3)| ≤
      2 * ∫ t in a..x, |W t| / (t * Real.log t ^ 3) := by
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    exact mul_le_mul_of_nonneg_left hrem (by norm_num)
  rw [hW] at h1
  linarith

theorem log_squared_weight_removal_certificate (c : ℕ → ℝ) (a x : ℝ)
    (ha : 1 < a) (hax : a ≤ x) :
    IntervalIntegrable (fun t : ℝ =>
      (∑ d ∈ Finset.Icc 1 ⌊t⌋₊, c d * Real.log (d : ℝ) ^ 2) /
        (t * Real.log t ^ 3)) volume a x ∧
    (∑ d ∈ Finset.Icc 1 ⌊x⌋₊, c d) =
      (∑ d ∈ Finset.Icc 1 ⌊a⌋₊, c d) -
        (∑ d ∈ Finset.Icc 1 ⌊a⌋₊, c d * Real.log (d : ℝ) ^ 2) / Real.log a ^ 2 +
        (∑ d ∈ Finset.Icc 1 ⌊x⌋₊, c d * Real.log (d : ℝ) ^ 2) / Real.log x ^ 2 +
        2 * ∫ t in a..x,
          (∑ d ∈ Finset.Icc 1 ⌊t⌋₊, c d * Real.log (d : ℝ) ^ 2) /
            (t * Real.log t ^ 3) ∧
    |∑ d ∈ Finset.Icc 1 ⌊x⌋₊, c d| ≤
      |(∑ d ∈ Finset.Icc 1 ⌊a⌋₊, c d) -
        (∑ d ∈ Finset.Icc 1 ⌊a⌋₊, c d * Real.log (d : ℝ) ^ 2) / Real.log a ^ 2| +
        |∑ d ∈ Finset.Icc 1 ⌊x⌋₊, c d * Real.log (d : ℝ) ^ 2| / Real.log x ^ 2 +
        2 * ∫ t in a..x,
          |∑ d ∈ Finset.Icc 1 ⌊t⌋₊, c d * Real.log (d : ℝ) ^ 2| /
            (t * Real.log t ^ 3) := by
  exact ⟨log_weight_kernel_intervalIntegrable c a x ha hax,
    log_squared_weight_removal_identity c a x ha hax,
    log_squared_weight_removal_bound c a x ha hax⟩

end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option Elab.async false
open Finset Nat ArithmeticFunction Real MeasureTheory
open scoped BigOperators Classical Interval

namespace Helfgott

lemma harmonic_tail_sum_zero_remove (c : ℕ → ℝ) (hc : c 0 = 0) (N : ℕ) :
    (∑ n ∈ Icc 0 N, c n) = ∑ n ∈ Icc 1 N, c n := by
  rw [← Finset.insert_Icc_succ_left_eq_Icc (Nat.zero_le N)]
  rw [Finset.sum_insert (by simp)]
  simp only [hc, zero_add]
  rfl

lemma harmonic_tail_abel_identity (c : ℕ → ℝ) (hc : c 0 = 0) (a x : ℝ)
    (ha : 0 < a) (hax : a ≤ x) :
    (∑ n ∈ Icc 1 ⌊x⌋₊, c n / (n : ℝ)) =
      (∑ n ∈ Icc 1 ⌊a⌋₊, c n / (n : ℝ)) +
      (∑ n ∈ Icc 1 ⌊x⌋₊, c n) / x -
      (∑ n ∈ Icc 1 ⌊a⌋₊, c n) / a +
      ∫ t in a..x, (∑ n ∈ Icc 1 ⌊t⌋₊, c n) / t ^ 2 := by
  have hd : ∀ t ∈ Set.Icc a x, DifferentiableAt ℝ (fun t : ℝ => t⁻¹) t := by
    intro t ht
    exact (hasDerivAt_inv (by linarith [ht.1] : t ≠ 0)).differentiableAt
  have hcder : ContinuousOn (fun t : ℝ => -(t ^ 2)⁻¹) (Set.Icc a x) :=
    ((continuousOn_id.pow 2).inv₀
      (fun t ht => pow_ne_zero 2 (by change t ≠ 0; linarith [ht.1]))).neg
  have hi : IntegrableOn (deriv (fun t : ℝ => t⁻¹)) (Set.Icc a x) := by
    simpa only [deriv_inv'] using hcder.integrableOn_Icc
  have h := sum_mul_eq_sub_sub_integral_mul c ha.le hax hd hi
  simp_rw [harmonic_tail_sum_zero_remove c hc] at h
  have hleft : (∑ n ∈ Ioc ⌊a⌋₊ ⌊x⌋₊, (n : ℝ)⁻¹ * c n) =
      (∑ n ∈ Icc 1 ⌊x⌋₊, c n / (n : ℝ)) -
        ∑ n ∈ Icc 1 ⌊a⌋₊, c n / (n : ℝ) := by
    rw [← log_weight_sum_Ioc_difference (fun n => c n / (n : ℝ))
      _ _ (Nat.floor_le_floor hax)]
    apply Finset.sum_congr rfl
    intro n hn
    rw [div_eq_mul_inv, mul_comm]
  rw [hleft] at h
  have hint : (∫ t in Set.Ioc a x, deriv (fun t : ℝ => t⁻¹) t *
      ∑ n ∈ Icc 1 ⌊t⌋₊, c n) =
        -(∫ t in a..x, (∑ n ∈ Icc 1 ⌊t⌋₊, c n) / t ^ 2) := by
    rw [← intervalIntegral.integral_of_le hax]
    simp_rw [deriv_inv, neg_mul, mul_comm ((_)⁻¹), ← div_eq_mul_inv]
    exact intervalIntegral.integral_neg
  rw [hint] at h
  simp only [div_eq_mul_inv, mul_comm] at h ⊢
  linarith

lemma squarefree_count_upper_real (t : ℝ) (ht : 0 ≤ t) :
    (∑ n ∈ Icc 1 ⌊t⌋₊, ((moebius n : ℤ) : ℝ) ^ 2) ≤
      (6 / Real.pi ^ 2) * t + 3 * Real.sqrt t := by
  have h := squarefree_coprime_count_square_root_error 1 ⌊t⌋₊ (by norm_num)
  simp only [Nat.coprime_one_right_iff, if_true, Nat.primeFactors_one,
    Finset.prod_empty, mul_one, Nat.divisors_one, Finset.sum_singleton,
    ArithmeticFunction.moebius_apply_one, Int.cast_one, abs_one, Nat.cast_one,
    Real.sqrt_one, div_one] at h
  have hN : (⌊t⌋₊ : ℝ) ≤ t := Nat.floor_le ht
  have hs : Real.sqrt (⌊t⌋₊ : ℝ) ≤ Real.sqrt t := Real.sqrt_le_sqrt hN
  have hρ : 0 ≤ (6 / Real.pi ^ 2 : ℝ) := by positivity
  have hf := (le_abs_self ((∑ n ∈ Icc 1 ⌊t⌋₊, ((moebius n : ℤ) : ℝ) ^ 2) -
    (⌊t⌋₊ : ℝ) * (6 / Real.pi ^ 2))).trans h
  nlinarith

lemma hasDerivAt_squarefree_harmonic_majorant (ρ b t : ℝ) (ht : 0 < t) :
    HasDerivAt (fun u : ℝ => ρ * Real.log u - 2 * b / Real.sqrt u)
      ((ρ * t + b * Real.sqrt t) / t ^ 2) t := by
  have ht0 := ht.ne'
  have hs0 := (Real.sqrt_pos.mpr ht).ne'
  have hs2 := Real.sq_sqrt ht.le
  have hd := ((Real.hasDerivAt_log ht0).const_mul ρ).sub
    (((Real.hasDerivAt_sqrt ht0).inv hs0).const_mul (2 * b))
  convert hd using 1 <;> (try dsimp) <;>
    first | rfl | (field_simp [ht0, hs0] <;>
      linear_combination b * (Real.sqrt t ^ 2 + t) * hs2)

theorem squarefree_harmonic_tail_bound (a x : ℝ) (ha : 0 < a) (hax : a ≤ x) :
    (∑ n ∈ Icc 1 ⌊x⌋₊, ((moebius n : ℤ) : ℝ) ^ 2 / (n : ℝ)) ≤
      (6 / Real.pi ^ 2) * Real.log x +
      ((∑ n ∈ Icc 1 ⌊a⌋₊, ((moebius n : ℤ) : ℝ) ^ 2 / (n : ℝ)) -
        (6 / Real.pi ^ 2) * Real.log a + (6 / Real.pi ^ 2) -
        (∑ n ∈ Icc 1 ⌊a⌋₊, ((moebius n : ℤ) : ℝ) ^ 2) / a +
        6 / Real.sqrt a) := by
  let ρ : ℝ := 6 / Real.pi ^ 2
  let Q : ℝ → ℝ := fun t => ∑ n ∈ Icc 1 ⌊t⌋₊, ((moebius n : ℤ) : ℝ) ^ 2
  have hx : 0 < x := lt_of_lt_of_le ha hax
  have hcont : ContinuousOn (fun t : ℝ => (ρ * t + 3 * Real.sqrt t) / t ^ 2)
      (Set.Icc a x) :=
    ((continuousOn_const.mul continuousOn_id).add
      (continuousOn_const.mul Real.continuous_sqrt.continuousOn)).div
      (continuousOn_id.pow 2) (fun t ht => pow_ne_zero 2 (by linarith [ht.1]))
  have hqint : IntervalIntegrable (fun t : ℝ => Q t / t ^ 2) volume a x := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hax]
    have hinv : ContinuousOn (fun t : ℝ => (t ^ 2)⁻¹) (Set.Icc a x) :=
      (continuousOn_id.pow 2).inv₀
        (fun t ht => pow_ne_zero 2 (by change t ≠ 0; linarith [ht.1]))
    have hi := integrableOn_mul_sum_Icc (fun n => ((moebius n : ℤ) : ℝ) ^ 2)
      ha.le hinv.integrableOn_Icc (m := 1)
    simpa only [div_eq_mul_inv, mul_comm] using hi
  have himono : (∫ t in a..x, Q t / t ^ 2) ≤
      ∫ t in a..x, (ρ * t + 3 * Real.sqrt t) / t ^ 2 := by
    apply intervalIntegral.integral_mono_on hax hqint (hcont.intervalIntegrable_of_Icc hax)
    intro t ht
    exact div_le_div_of_nonneg_right (squarefree_count_upper_real t (by linarith [ht.1]))
      (sq_nonneg t)
  have hderiv : ∀ t ∈ Set.uIcc a x,
      HasDerivAt (fun u : ℝ => ρ * Real.log u - 6 / Real.sqrt u)
        ((ρ * t + 3 * Real.sqrt t) / t ^ 2) t := by
    intro t ht
    rw [Set.uIcc_of_le hax] at ht
    simpa only [mul_one, show (2 : ℝ) * 3 = 6 by norm_num] using
      hasDerivAt_squarefree_harmonic_majorant ρ 3 t (by linarith [ht.1])
  have hieval := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    (hcont.intervalIntegrable_of_Icc hax)
  rw [hieval] at himono
  have hpoint : Q x / x ≤ ρ + 3 / Real.sqrt x := by
    calc
      _ ≤ (ρ * x + 3 * Real.sqrt x) / x :=
        div_le_div_of_nonneg_right (squarefree_count_upper_real x hx.le) hx.le
      _ = _ := by
        have hs0 := (Real.sqrt_pos.mpr hx).ne'
        have hs2 := Real.sq_sqrt hx.le
        field_simp [hx.ne', hs0]
        nlinarith [hs2]
  have hid := harmonic_tail_abel_identity (fun n => ((moebius n : ℤ) : ℝ) ^ 2)
    (by simp) a x ha hax
  change (∑ n ∈ Icc 1 ⌊x⌋₊, ((moebius n : ℤ) : ℝ) ^ 2 / (n : ℝ)) =
    (∑ n ∈ Icc 1 ⌊a⌋₊, ((moebius n : ℤ) : ℝ) ^ 2 / (n : ℝ)) +
      Q x / x - Q a / a + ∫ t in a..x, Q t / t ^ 2 at hid
  have hnonneg : 0 ≤ 3 / Real.sqrt x := by positivity
  have hdiv : 6 / Real.sqrt x = 2 * (3 / Real.sqrt x) := by ring
  rw [hdiv] at himono
  change _ ≤ ρ * Real.log x +
    ((∑ n ∈ Icc 1 ⌊a⌋₊, ((moebius n : ℤ) : ℝ) ^ 2 / (n : ℝ)) -
      ρ * Real.log a + ρ - Q a / a + 6 / Real.sqrt a)
  linarith

end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option Elab.async false
open Finset Nat ArithmeticFunction Real MeasureTheory
open scoped BigOperators Classical Interval

namespace Helfgott

lemma squarefree_density_lower_604 : (604 / 1000 : ℝ) ≤ 6 / Real.pi ^ 2 := by
  have hp := Real.pi_lt_d2
  have hp0 := Real.pi_pos
  apply (le_div_iff₀ (sq_pos_of_pos hp0)).mpr
  nlinarith

lemma squarefree_harmonic_log_10000_lower : (46 / 5 : ℝ) ≤ Real.log 10000 := by
  have hs := Real.exp_bound' (x := (3 / 10 : ℝ)) (by norm_num) (by norm_num)
    (n := 5) (by norm_num)
  norm_num [Finset.sum_range_succ, Nat.factorial] at hs
  have hs' : Real.exp (3 / 10 : ℝ) ≤ 27 / 20 := by linarith
  have he : Real.exp 1 ≤ (2719 / 1000 : ℝ) := by
    have he' := Real.exp_one_lt_d9
    linarith
  have he2 : Real.exp (2 : ℝ) ≤ (2719 / 1000 : ℝ) ^ 2 := by
    rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
    nlinarith [Real.exp_pos (1 : ℝ)]
  have hexp : Real.exp (23 / 10 : ℝ) ≤ 10 := by
    rw [show (23 / 10 : ℝ) = 2 + 3 / 10 by norm_num, Real.exp_add]
    have hm := mul_le_mul he2 hs' (Real.exp_pos (3 / 10 : ℝ)).le
      (by positivity : (0 : ℝ) ≤ (2719 / 1000) ^ 2)
    norm_num at hm
    linarith
  have hlog : (23 / 10 : ℝ) ≤ Real.log 10 :=
    (Real.le_log_iff_exp_le (by norm_num : (0 : ℝ) < 10)).mpr hexp
  have hlog4 : Real.log (10000 : ℝ) = 4 * Real.log 10 := by
    rw [show (10000 : ℝ) = 10 ^ (4 : ℕ) by norm_num, Real.log_pow]
    norm_num
  rw [hlog4]
  linarith

theorem squarefree_harmonic_log_bound_of_initial
    (hcount : (∑ n ∈ Icc 1 10000, ((moebius n : ℤ) : ℝ) ^ 2) = 6083)
    (hbaseline : (∑ n ∈ Icc 1 10000,
      ((moebius n : ℤ) : ℝ) ^ 2 / (n : ℝ)) ≤ 665 / 100)
    (x : ℝ) (hx : 10000 ≤ x) :
    (∑ n ∈ Icc 1 ⌊x⌋₊, ((moebius n : ℤ) : ℝ) ^ 2 / (n : ℝ)) ≤
      (6 / Real.pi ^ 2) * Real.log x + 583 / 500 := by
  have htail := squarefree_harmonic_tail_bound 10000 x (by norm_num) hx
  norm_num only [Nat.floor_ofNat] at htail
  rw [hcount] at htail
  have hl := squarefree_harmonic_log_10000_lower
  have hρ := squarefree_density_lower_604
  have hmul : (604 / 1000 : ℝ) * (46 / 5 - 1) ≤
      (6 / Real.pi ^ 2) * (Real.log 10000 - 1) :=
    mul_le_mul hρ (by linarith) (by norm_num) (by positivity)
  have hb :
      (∑ n ∈ Icc 1 10000, ((moebius n : ℤ) : ℝ) ^ 2 / (n : ℝ)) -
        (6 / Real.pi ^ 2) * Real.log 10000 + (6 / Real.pi ^ 2) -
        (6083 : ℝ) / 10000 + 3 / 50 ≤ 583 / 500 := by
    nlinarith
  linarith

end Helfgott
end

section
set_option autoImplicit false
open Finset Nat ArithmeticFunction Real
open scoped BigOperators Classical
namespace Helfgott

theorem squarefree_harmonic_log_upper_bound_complete (x : ℝ) (hx : 10000 ≤ x) :
    (∑ n ∈ Icc 1 ⌊x⌋₊, ((moebius n : ℤ) : ℝ) ^ 2 / (n : ℝ)) ≤
      (6 / Real.pi ^ 2) * Real.log x + 583 / 500 := by
  exact squarefree_harmonic_log_bound_of_initial
    squarefree_harmonic_initial_10000_groups_reuse.1 squarefree_harmonic_initial_10000_groups_reuse.2 x hx

end Helfgott
end

open Helfgott Finset Nat ArithmeticFunction Real
open scoped BigOperators Classical

theorem solution  (x : ℝ) (hx : 10000 ≤ x) :
    (∑ n ∈ Icc 1 ⌊x⌋₊, ((moebius n : ℤ) : ℝ) ^ 2 / (n : ℝ)) ≤
      (6 / Real.pi ^ 2) * Real.log x + 583 / 500 := Helfgott.squarefree_harmonic_log_upper_bound_complete x hx
#print axioms solution
