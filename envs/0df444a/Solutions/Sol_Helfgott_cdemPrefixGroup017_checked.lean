-- Prove2me | solution 1 for Helfgott.cdemPrefixGroup017_checked
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-09T01:49:01.611184+00:00
-- url     : https://prove2.me/submissions/c979a126-38d8-4d08-ad27-4fb5bd110a85

import Definitions.Def_Helfgott_MobiusFiniteTable1200001
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Finset
open scoped BigOperators
namespace Helfgott
private theorem cdemPrefixStats_69632_69696 :
    (∑ n ∈ Ico 69632 69696, mobiusTreeValue 16 mobiusTable1200001 n) = (-4 : ℤ) ∧
    (∑ n ∈ Ico 69632 69696, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 69632 69696, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-287175 : ℤ) ∧
    (∑ n ∈ Ico 69632 69696, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-5743557271470692666562258045 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_69696_69760 :
    (∑ n ∈ Ico 69696 69760, mobiusTreeValue 16 mobiusTable1200001 n) = (-4 : ℤ) ∧
    (∑ n ∈ Ico 69696 69760, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 69696 69760, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-286932 : ℤ) ∧
    (∑ n ∈ Ico 69696 69760, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-5738674489422841271892453872 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_69632_69760 :
    (∑ n ∈ Ico 69632 69760, mobiusTreeValue 16 mobiusTable1200001 n) = (-8 : ℤ) ∧
    (∑ n ∈ Ico 69632 69760, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 69632 69760, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-574107 : ℤ) ∧
    (∑ n ∈ Ico 69632 69760, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-11482231760893533938454711917 : ℤ) := by
  rcases cdemPrefixStats_69632_69696 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_69696_69760 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 69632 ≤ 69696) (by norm_num : 69696 ≤ 69760), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 69632 ≤ 69696) (by norm_num : 69696 ≤ 69760), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 69632 ≤ 69696) (by norm_num : 69696 ≤ 69760), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 69632 ≤ 69696) (by norm_num : 69696 ≤ 69760), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_69760_69824 :
    (∑ n ∈ Ico 69760 69824, mobiusTreeValue 16 mobiusTable1200001 n) = (-6 : ℤ) ∧
    (∑ n ∈ Ico 69760 69824, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 69760 69824, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-429864 : ℤ) ∧
    (∑ n ∈ Ico 69760 69824, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-8597304092437063608054837496 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_69824_69888 :
    (∑ n ∈ Ico 69824 69888, mobiusTreeValue 16 mobiusTable1200001 n) = (-3 : ℤ) ∧
    (∑ n ∈ Ico 69824 69888, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 69824 69888, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-214829 : ℤ) ∧
    (∑ n ∈ Ico 69824 69888, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-4296638727730946396579119470 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_69760_69888 :
    (∑ n ∈ Ico 69760 69888, mobiusTreeValue 16 mobiusTable1200001 n) = (-9 : ℤ) ∧
    (∑ n ∈ Ico 69760 69888, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 69760 69888, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-644693 : ℤ) ∧
    (∑ n ∈ Ico 69760 69888, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-12893942820168010004633956966 : ℤ) := by
  rcases cdemPrefixStats_69760_69824 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_69824_69888 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 69760 ≤ 69824) (by norm_num : 69824 ≤ 69888), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 69760 ≤ 69824) (by norm_num : 69824 ≤ 69888), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 69760 ≤ 69824) (by norm_num : 69824 ≤ 69888), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 69760 ≤ 69824) (by norm_num : 69824 ≤ 69888), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_69632_69888 :
    (∑ n ∈ Ico 69632 69888, mobiusTreeValue 16 mobiusTable1200001 n) = (-17 : ℤ) ∧
    (∑ n ∈ Ico 69632 69888, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (155 : ℕ) ∧
    (∑ n ∈ Ico 69632 69888, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-1218800 : ℤ) ∧
    (∑ n ∈ Ico 69632 69888, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-24376174581061543943088668883 : ℤ) := by
  rcases cdemPrefixStats_69632_69760 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_69760_69888 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 69632 ≤ 69760) (by norm_num : 69760 ≤ 69888), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 69632 ≤ 69760) (by norm_num : 69760 ≤ 69888), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 69632 ≤ 69760) (by norm_num : 69760 ≤ 69888), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 69632 ≤ 69760) (by norm_num : 69760 ≤ 69888), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_69888_69952 :
    (∑ n ∈ Ico 69888 69952, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 69888 69952, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 69888 69952, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (71657 : ℤ) ∧
    (∑ n ∈ Ico 69888 69952, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1433090157829086385221487929 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_69952_70016 :
    (∑ n ∈ Ico 69952 70016, mobiusTreeValue 16 mobiusTable1200001 n) = (-2 : ℤ) ∧
    (∑ n ∈ Ico 69952 70016, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (42 : ℕ) ∧
    (∑ n ∈ Ico 69952 70016, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-142846 : ℤ) ∧
    (∑ n ∈ Ico 69952 70016, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-2856937777189062698820842520 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_69888_70016 :
    (∑ n ∈ Ico 69888 70016, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 69888 70016, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (81 : ℕ) ∧
    (∑ n ∈ Ico 69888 70016, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-71189 : ℤ) ∧
    (∑ n ∈ Ico 69888 70016, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-1423847619359976313599354591 : ℤ) := by
  rcases cdemPrefixStats_69888_69952 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_69952_70016 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 69888 ≤ 69952) (by norm_num : 69952 ≤ 70016), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 69888 ≤ 69952) (by norm_num : 69952 ≤ 70016), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 69888 ≤ 69952) (by norm_num : 69952 ≤ 70016), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 69888 ≤ 69952) (by norm_num : 69952 ≤ 70016), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_70016_70080 :
    (∑ n ∈ Ico 70016 70080, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 70016 70080, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (36 : ℕ) ∧
    (∑ n ∈ Ico 70016 70080, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (24 : ℤ) ∧
    (∑ n ∈ Ico 70016 70080, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (509251046896835465691497 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_70080_70144 :
    (∑ n ∈ Ico 70080 70144, mobiusTreeValue 16 mobiusTable1200001 n) = (-9 : ℤ) ∧
    (∑ n ∈ Ico 70080 70144, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 70080 70144, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-641682 : ℤ) ∧
    (∑ n ∈ Ico 70080 70144, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-12833717437392163981592689670 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_70016_70144 :
    (∑ n ∈ Ico 70016 70144, mobiusTreeValue 16 mobiusTable1200001 n) = (-9 : ℤ) ∧
    (∑ n ∈ Ico 70016 70144, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 70016 70144, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-641658 : ℤ) ∧
    (∑ n ∈ Ico 70016 70144, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-12833208186345267146126998173 : ℤ) := by
  rcases cdemPrefixStats_70016_70080 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_70080_70144 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 70016 ≤ 70080) (by norm_num : 70080 ≤ 70144), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 70016 ≤ 70080) (by norm_num : 70080 ≤ 70144), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 70016 ≤ 70080) (by norm_num : 70080 ≤ 70144), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 70016 ≤ 70080) (by norm_num : 70080 ≤ 70144), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_69888_70144 :
    (∑ n ∈ Ico 69888 70144, mobiusTreeValue 16 mobiusTable1200001 n) = (-10 : ℤ) ∧
    (∑ n ∈ Ico 69888 70144, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (158 : ℕ) ∧
    (∑ n ∈ Ico 69888 70144, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-712847 : ℤ) ∧
    (∑ n ∈ Ico 69888 70144, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-14257055805705243459726352764 : ℤ) := by
  rcases cdemPrefixStats_69888_70016 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_70016_70144 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 69888 ≤ 70016) (by norm_num : 70016 ≤ 70144), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 69888 ≤ 70016) (by norm_num : 70016 ≤ 70144), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 69888 ≤ 70016) (by norm_num : 70016 ≤ 70144), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 69888 ≤ 70016) (by norm_num : 70016 ≤ 70144), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_69632_70144 :
    (∑ n ∈ Ico 69632 70144, mobiusTreeValue 16 mobiusTable1200001 n) = (-27 : ℤ) ∧
    (∑ n ∈ Ico 69632 70144, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (313 : ℕ) ∧
    (∑ n ∈ Ico 69632 70144, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-1931647 : ℤ) ∧
    (∑ n ∈ Ico 69632 70144, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-38633230386766787402815021647 : ℤ) := by
  rcases cdemPrefixStats_69632_69888 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_69888_70144 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 69632 ≤ 69888) (by norm_num : 69888 ≤ 70144), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 69632 ≤ 69888) (by norm_num : 69888 ≤ 70144), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 69632 ≤ 69888) (by norm_num : 69888 ≤ 70144), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 69632 ≤ 69888) (by norm_num : 69888 ≤ 70144), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_70144_70208 :
    (∑ n ∈ Ico 70144 70208, mobiusTreeValue 16 mobiusTable1200001 n) = (-10 : ℤ) ∧
    (∑ n ∈ Ico 70144 70208, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 70144 70208, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-712282 : ℤ) ∧
    (∑ n ∈ Ico 70144 70208, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-14245725081275552631832295207 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_70208_70272 :
    (∑ n ∈ Ico 70208 70272, mobiusTreeValue 16 mobiusTable1200001 n) = (3 : ℤ) ∧
    (∑ n ∈ Ico 70208 70272, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 70208 70272, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (213482 : ℤ) ∧
    (∑ n ∈ Ico 70208 70272, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (4269651736356716581413188599 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_70144_70272 :
    (∑ n ∈ Ico 70144 70272, mobiusTreeValue 16 mobiusTable1200001 n) = (-7 : ℤ) ∧
    (∑ n ∈ Ico 70144 70272, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 70144 70272, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-498800 : ℤ) ∧
    (∑ n ∈ Ico 70144 70272, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-9976073344918836050419106608 : ℤ) := by
  rcases cdemPrefixStats_70144_70208 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_70208_70272 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 70144 ≤ 70208) (by norm_num : 70208 ≤ 70272), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 70144 ≤ 70208) (by norm_num : 70208 ≤ 70272), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 70144 ≤ 70208) (by norm_num : 70208 ≤ 70272), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 70144 ≤ 70208) (by norm_num : 70208 ≤ 70272), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_70272_70336 :
    (∑ n ∈ Ico 70272 70336, mobiusTreeValue 16 mobiusTable1200001 n) = (4 : ℤ) ∧
    (∑ n ∈ Ico 70272 70336, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 70272 70336, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (284449 : ℤ) ∧
    (∑ n ∈ Ico 70272 70336, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (5689011281064689914608449845 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_70336_70400 :
    (∑ n ∈ Ico 70336 70400, mobiusTreeValue 16 mobiusTable1200001 n) = (-5 : ℤ) ∧
    (∑ n ∈ Ico 70336 70400, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 70336 70400, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-355070 : ℤ) ∧
    (∑ n ∈ Ico 70336 70400, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-7101504374399894213498969600 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_70272_70400 :
    (∑ n ∈ Ico 70272 70400, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 70272 70400, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 70272 70400, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-70621 : ℤ) ∧
    (∑ n ∈ Ico 70272 70400, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-1412493093335204298890519755 : ℤ) := by
  rcases cdemPrefixStats_70272_70336 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_70336_70400 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 70272 ≤ 70336) (by norm_num : 70336 ≤ 70400), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 70272 ≤ 70336) (by norm_num : 70336 ≤ 70400), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 70272 ≤ 70336) (by norm_num : 70336 ≤ 70400), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 70272 ≤ 70336) (by norm_num : 70336 ≤ 70400), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_70144_70400 :
    (∑ n ∈ Ico 70144 70400, mobiusTreeValue 16 mobiusTable1200001 n) = (-8 : ℤ) ∧
    (∑ n ∈ Ico 70144 70400, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (154 : ℕ) ∧
    (∑ n ∈ Ico 70144 70400, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-569421 : ℤ) ∧
    (∑ n ∈ Ico 70144 70400, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-11388566438254040349309626363 : ℤ) := by
  rcases cdemPrefixStats_70144_70272 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_70272_70400 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 70144 ≤ 70272) (by norm_num : 70272 ≤ 70400), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 70144 ≤ 70272) (by norm_num : 70272 ≤ 70400), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 70144 ≤ 70272) (by norm_num : 70272 ≤ 70400), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 70144 ≤ 70272) (by norm_num : 70272 ≤ 70400), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_70400_70464 :
    (∑ n ∈ Ico 70400 70464, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 70400 70464, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 70400 70464, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-70779 : ℤ) ∧
    (∑ n ∈ Ico 70400 70464, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-1415555021393962501516937636 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_70464_70528 :
    (∑ n ∈ Ico 70464 70528, mobiusTreeValue 16 mobiusTable1200001 n) = (-5 : ℤ) ∧
    (∑ n ∈ Ico 70464 70528, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 70464 70528, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-354736 : ℤ) ∧
    (∑ n ∈ Ico 70464 70528, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-7094754653317896495881540011 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_70400_70528 :
    (∑ n ∈ Ico 70400 70528, mobiusTreeValue 16 mobiusTable1200001 n) = (-6 : ℤ) ∧
    (∑ n ∈ Ico 70400 70528, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 70400 70528, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-425515 : ℤ) ∧
    (∑ n ∈ Ico 70400 70528, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-8510309674711858997398477647 : ℤ) := by
  rcases cdemPrefixStats_70400_70464 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_70464_70528 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 70400 ≤ 70464) (by norm_num : 70464 ≤ 70528), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 70400 ≤ 70464) (by norm_num : 70464 ≤ 70528), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 70400 ≤ 70464) (by norm_num : 70464 ≤ 70528), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 70400 ≤ 70464) (by norm_num : 70464 ≤ 70528), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_70528_70592 :
    (∑ n ∈ Ico 70528 70592, mobiusTreeValue 16 mobiusTable1200001 n) = (-8 : ℤ) ∧
    (∑ n ∈ Ico 70528 70592, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 70528 70592, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-566762 : ℤ) ∧
    (∑ n ∈ Ico 70528 70592, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-11335338444557424423346598011 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_70592_70656 :
    (∑ n ∈ Ico 70592 70656, mobiusTreeValue 16 mobiusTable1200001 n) = (5 : ℤ) ∧
    (∑ n ∈ Ico 70592 70656, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 70592 70656, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (353932 : ℤ) ∧
    (∑ n ∈ Ico 70592 70656, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (7078683639852388286160124219 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_70528_70656 :
    (∑ n ∈ Ico 70528 70656, mobiusTreeValue 16 mobiusTable1200001 n) = (-3 : ℤ) ∧
    (∑ n ∈ Ico 70528 70656, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 70528 70656, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-212830 : ℤ) ∧
    (∑ n ∈ Ico 70528 70656, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-4256654804705036137186473792 : ℤ) := by
  rcases cdemPrefixStats_70528_70592 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_70592_70656 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 70528 ≤ 70592) (by norm_num : 70592 ≤ 70656), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 70528 ≤ 70592) (by norm_num : 70592 ≤ 70656), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 70528 ≤ 70592) (by norm_num : 70592 ≤ 70656), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 70528 ≤ 70592) (by norm_num : 70592 ≤ 70656), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_70400_70656 :
    (∑ n ∈ Ico 70400 70656, mobiusTreeValue 16 mobiusTable1200001 n) = (-9 : ℤ) ∧
    (∑ n ∈ Ico 70400 70656, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (155 : ℕ) ∧
    (∑ n ∈ Ico 70400 70656, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-638345 : ℤ) ∧
    (∑ n ∈ Ico 70400 70656, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-12766964479416895134584951439 : ℤ) := by
  rcases cdemPrefixStats_70400_70528 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_70528_70656 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 70400 ≤ 70528) (by norm_num : 70528 ≤ 70656), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 70400 ≤ 70528) (by norm_num : 70528 ≤ 70656), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 70400 ≤ 70528) (by norm_num : 70528 ≤ 70656), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 70400 ≤ 70528) (by norm_num : 70528 ≤ 70656), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_70144_70656 :
    (∑ n ∈ Ico 70144 70656, mobiusTreeValue 16 mobiusTable1200001 n) = (-17 : ℤ) ∧
    (∑ n ∈ Ico 70144 70656, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (309 : ℕ) ∧
    (∑ n ∈ Ico 70144 70656, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-1207766 : ℤ) ∧
    (∑ n ∈ Ico 70144 70656, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-24155530917670935483894577802 : ℤ) := by
  rcases cdemPrefixStats_70144_70400 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_70400_70656 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 70144 ≤ 70400) (by norm_num : 70400 ≤ 70656), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 70144 ≤ 70400) (by norm_num : 70400 ≤ 70656), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 70144 ≤ 70400) (by norm_num : 70400 ≤ 70656), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 70144 ≤ 70400) (by norm_num : 70400 ≤ 70656), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_69632_70656 :
    (∑ n ∈ Ico 69632 70656, mobiusTreeValue 16 mobiusTable1200001 n) = (-44 : ℤ) ∧
    (∑ n ∈ Ico 69632 70656, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (622 : ℕ) ∧
    (∑ n ∈ Ico 69632 70656, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-3139413 : ℤ) ∧
    (∑ n ∈ Ico 69632 70656, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-62788761304437722886709599449 : ℤ) := by
  rcases cdemPrefixStats_69632_70144 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_70144_70656 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 69632 ≤ 70144) (by norm_num : 70144 ≤ 70656), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 69632 ≤ 70144) (by norm_num : 70144 ≤ 70656), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 69632 ≤ 70144) (by norm_num : 70144 ≤ 70656), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 69632 ≤ 70144) (by norm_num : 70144 ≤ 70656), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_70656_70720 :
    (∑ n ∈ Ico 70656 70720, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 70656 70720, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 70656 70720, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (70738 : ℤ) ∧
    (∑ n ∈ Ico 70656 70720, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1414766667793606356305887865 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_70720_70784 :
    (∑ n ∈ Ico 70720 70784, mobiusTreeValue 16 mobiusTable1200001 n) = (8 : ℤ) ∧
    (∑ n ∈ Ico 70720 70784, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 70720 70784, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (565563 : ℤ) ∧
    (∑ n ∈ Ico 70720 70784, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (11311316852609744997359261988 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_70656_70784 :
    (∑ n ∈ Ico 70656 70784, mobiusTreeValue 16 mobiusTable1200001 n) = (9 : ℤ) ∧
    (∑ n ∈ Ico 70656 70784, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (79 : ℕ) ∧
    (∑ n ∈ Ico 70656 70784, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (636301 : ℤ) ∧
    (∑ n ∈ Ico 70656 70784, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (12726083520403351353665149853 : ℤ) := by
  rcases cdemPrefixStats_70656_70720 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_70720_70784 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 70656 ≤ 70720) (by norm_num : 70720 ≤ 70784), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 70656 ≤ 70720) (by norm_num : 70720 ≤ 70784), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 70656 ≤ 70720) (by norm_num : 70720 ≤ 70784), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 70656 ≤ 70720) (by norm_num : 70720 ≤ 70784), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_70784_70848 :
    (∑ n ∈ Ico 70784 70848, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 70784 70848, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 70784 70848, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-70358 : ℤ) ∧
    (∑ n ∈ Ico 70784 70848, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-1407185111730917475374041836 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_70848_70912 :
    (∑ n ∈ Ico 70848 70912, mobiusTreeValue 16 mobiusTable1200001 n) = (5 : ℤ) ∧
    (∑ n ∈ Ico 70848 70912, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 70848 70912, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (352560 : ℤ) ∧
    (∑ n ∈ Ico 70848 70912, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (7051290053012238294142422348 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_70784_70912 :
    (∑ n ∈ Ico 70784 70912, mobiusTreeValue 16 mobiusTable1200001 n) = (4 : ℤ) ∧
    (∑ n ∈ Ico 70784 70912, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (76 : ℕ) ∧
    (∑ n ∈ Ico 70784 70912, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (282202 : ℤ) ∧
    (∑ n ∈ Ico 70784 70912, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (5644104941281320818768380512 : ℤ) := by
  rcases cdemPrefixStats_70784_70848 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_70848_70912 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 70784 ≤ 70848) (by norm_num : 70848 ≤ 70912), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 70784 ≤ 70848) (by norm_num : 70848 ≤ 70912), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 70784 ≤ 70848) (by norm_num : 70848 ≤ 70912), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 70784 ≤ 70848) (by norm_num : 70848 ≤ 70912), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_70656_70912 :
    (∑ n ∈ Ico 70656 70912, mobiusTreeValue 16 mobiusTable1200001 n) = (13 : ℤ) ∧
    (∑ n ∈ Ico 70656 70912, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (155 : ℕ) ∧
    (∑ n ∈ Ico 70656 70912, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (918503 : ℤ) ∧
    (∑ n ∈ Ico 70656 70912, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (18370188461684672172433530365 : ℤ) := by
  rcases cdemPrefixStats_70656_70784 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_70784_70912 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 70656 ≤ 70784) (by norm_num : 70784 ≤ 70912), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 70656 ≤ 70784) (by norm_num : 70784 ≤ 70912), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 70656 ≤ 70784) (by norm_num : 70784 ≤ 70912), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 70656 ≤ 70784) (by norm_num : 70784 ≤ 70912), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_70912_70976 :
    (∑ n ∈ Ico 70912 70976, mobiusTreeValue 16 mobiusTable1200001 n) = (-8 : ℤ) ∧
    (∑ n ∈ Ico 70912 70976, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 70912 70976, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-563842 : ℤ) ∧
    (∑ n ∈ Ico 70912 70976, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-11276917516528637786368139911 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_70976_71040 :
    (∑ n ∈ Ico 70976 71040, mobiusTreeValue 16 mobiusTable1200001 n) = (-11 : ℤ) ∧
    (∑ n ∈ Ico 70976 71040, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 70976 71040, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-774568 : ℤ) ∧
    (∑ n ∈ Ico 70976 71040, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-15491491245733717661090232697 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_70912_71040 :
    (∑ n ∈ Ico 70912 71040, mobiusTreeValue 16 mobiusTable1200001 n) = (-19 : ℤ) ∧
    (∑ n ∈ Ico 70912 71040, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (81 : ℕ) ∧
    (∑ n ∈ Ico 70912 71040, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-1338410 : ℤ) ∧
    (∑ n ∈ Ico 70912 71040, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-26768408762262355447458372608 : ℤ) := by
  rcases cdemPrefixStats_70912_70976 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_70976_71040 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 70912 ≤ 70976) (by norm_num : 70976 ≤ 71040), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 70912 ≤ 70976) (by norm_num : 70976 ≤ 71040), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 70912 ≤ 70976) (by norm_num : 70976 ≤ 71040), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 70912 ≤ 70976) (by norm_num : 70976 ≤ 71040), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_71040_71104 :
    (∑ n ∈ Ico 71040 71104, mobiusTreeValue 16 mobiusTable1200001 n) = (5 : ℤ) ∧
    (∑ n ∈ Ico 71040 71104, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 71040 71104, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (352041 : ℤ) ∧
    (∑ n ∈ Ico 71040 71104, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (7040840826100426289974072791 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_71104_71168 :
    (∑ n ∈ Ico 71104 71168, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 71104 71168, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 71104 71168, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-70109 : ℤ) ∧
    (∑ n ∈ Ico 71104 71168, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-1402180755120612891458904614 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_71040_71168 :
    (∑ n ∈ Ico 71040 71168, mobiusTreeValue 16 mobiusTable1200001 n) = (4 : ℤ) ∧
    (∑ n ∈ Ico 71040 71168, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (76 : ℕ) ∧
    (∑ n ∈ Ico 71040 71168, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (281932 : ℤ) ∧
    (∑ n ∈ Ico 71040 71168, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (5638660070979813398515168177 : ℤ) := by
  rcases cdemPrefixStats_71040_71104 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_71104_71168 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 71040 ≤ 71104) (by norm_num : 71104 ≤ 71168), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 71040 ≤ 71104) (by norm_num : 71104 ≤ 71168), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 71040 ≤ 71104) (by norm_num : 71104 ≤ 71168), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 71040 ≤ 71104) (by norm_num : 71104 ≤ 71168), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_70912_71168 :
    (∑ n ∈ Ico 70912 71168, mobiusTreeValue 16 mobiusTable1200001 n) = (-15 : ℤ) ∧
    (∑ n ∈ Ico 70912 71168, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (157 : ℕ) ∧
    (∑ n ∈ Ico 70912 71168, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-1056478 : ℤ) ∧
    (∑ n ∈ Ico 70912 71168, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-21129748691282542048943204431 : ℤ) := by
  rcases cdemPrefixStats_70912_71040 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_71040_71168 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 70912 ≤ 71040) (by norm_num : 71040 ≤ 71168), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 70912 ≤ 71040) (by norm_num : 71040 ≤ 71168), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 70912 ≤ 71040) (by norm_num : 71040 ≤ 71168), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 70912 ≤ 71040) (by norm_num : 71040 ≤ 71168), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_70656_71168 :
    (∑ n ∈ Ico 70656 71168, mobiusTreeValue 16 mobiusTable1200001 n) = (-2 : ℤ) ∧
    (∑ n ∈ Ico 70656 71168, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (312 : ℕ) ∧
    (∑ n ∈ Ico 70656 71168, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-137975 : ℤ) ∧
    (∑ n ∈ Ico 70656 71168, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-2759560229597869876509674066 : ℤ) := by
  rcases cdemPrefixStats_70656_70912 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_70912_71168 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 70656 ≤ 70912) (by norm_num : 70912 ≤ 71168), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 70656 ≤ 70912) (by norm_num : 70912 ≤ 71168), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 70656 ≤ 70912) (by norm_num : 70912 ≤ 71168), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 70656 ≤ 70912) (by norm_num : 70912 ≤ 71168), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_71168_71232 :
    (∑ n ∈ Ico 71168 71232, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 71168 71232, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 71168 71232, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-87 : ℤ) ∧
    (∑ n ∈ Ico 71168 71232, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-1775102166311434286438792 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_71232_71296 :
    (∑ n ∈ Ico 71232 71296, mobiusTreeValue 16 mobiusTable1200001 n) = (-3 : ℤ) ∧
    (∑ n ∈ Ico 71232 71296, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 71232 71296, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-210291 : ℤ) ∧
    (∑ n ∈ Ico 71232 71296, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-4205859840249205693453646946 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_71168_71296 :
    (∑ n ∈ Ico 71168 71296, mobiusTreeValue 16 mobiusTable1200001 n) = (-3 : ℤ) ∧
    (∑ n ∈ Ico 71168 71296, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 71168 71296, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-210378 : ℤ) ∧
    (∑ n ∈ Ico 71168 71296, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-4207634942415517127740085738 : ℤ) := by
  rcases cdemPrefixStats_71168_71232 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_71232_71296 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 71168 ≤ 71232) (by norm_num : 71232 ≤ 71296), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 71168 ≤ 71232) (by norm_num : 71232 ≤ 71296), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 71168 ≤ 71232) (by norm_num : 71232 ≤ 71296), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 71168 ≤ 71232) (by norm_num : 71232 ≤ 71296), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_71296_71360 :
    (∑ n ∈ Ico 71296 71360, mobiusTreeValue 16 mobiusTable1200001 n) = (-9 : ℤ) ∧
    (∑ n ∈ Ico 71296 71360, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 71296 71360, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-630811 : ℤ) ∧
    (∑ n ∈ Ico 71296 71360, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-12616331097929586743869565282 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_71360_71424 :
    (∑ n ∈ Ico 71360 71424, mobiusTreeValue 16 mobiusTable1200001 n) = (-13 : ℤ) ∧
    (∑ n ∈ Ico 71360 71424, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 71360 71424, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-910550 : ℤ) ∧
    (∑ n ∈ Ico 71360 71424, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-18211168680343681947439174137 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_71296_71424 :
    (∑ n ∈ Ico 71296 71424, mobiusTreeValue 16 mobiusTable1200001 n) = (-22 : ℤ) ∧
    (∑ n ∈ Ico 71296 71424, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 71296 71424, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-1541361 : ℤ) ∧
    (∑ n ∈ Ico 71296 71424, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-30827499778273268691308739419 : ℤ) := by
  rcases cdemPrefixStats_71296_71360 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_71360_71424 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 71296 ≤ 71360) (by norm_num : 71360 ≤ 71424), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 71296 ≤ 71360) (by norm_num : 71360 ≤ 71424), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 71296 ≤ 71360) (by norm_num : 71360 ≤ 71424), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 71296 ≤ 71360) (by norm_num : 71360 ≤ 71424), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_71168_71424 :
    (∑ n ∈ Ico 71168 71424, mobiusTreeValue 16 mobiusTable1200001 n) = (-25 : ℤ) ∧
    (∑ n ∈ Ico 71168 71424, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (155 : ℕ) ∧
    (∑ n ∈ Ico 71168 71424, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-1751739 : ℤ) ∧
    (∑ n ∈ Ico 71168 71424, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-35035134720688785819048825157 : ℤ) := by
  rcases cdemPrefixStats_71168_71296 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_71296_71424 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 71168 ≤ 71296) (by norm_num : 71296 ≤ 71424), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 71168 ≤ 71296) (by norm_num : 71296 ≤ 71424), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 71168 ≤ 71296) (by norm_num : 71296 ≤ 71424), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 71168 ≤ 71296) (by norm_num : 71296 ≤ 71424), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_71424_71488 :
    (∑ n ∈ Ico 71424 71488, mobiusTreeValue 16 mobiusTable1200001 n) = (-2 : ℤ) ∧
    (∑ n ∈ Ico 71424 71488, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 71424 71488, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-139885 : ℤ) ∧
    (∑ n ∈ Ico 71424 71488, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-2797731303455574391164406812 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_71488_71552 :
    (∑ n ∈ Ico 71488 71552, mobiusTreeValue 16 mobiusTable1200001 n) = (-2 : ℤ) ∧
    (∑ n ∈ Ico 71488 71552, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 71488 71552, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-139640 : ℤ) ∧
    (∑ n ∈ Ico 71488 71552, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-2792823986913471545590553644 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_71424_71552 :
    (∑ n ∈ Ico 71424 71552, mobiusTreeValue 16 mobiusTable1200001 n) = (-4 : ℤ) ∧
    (∑ n ∈ Ico 71424 71552, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 71424 71552, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-279525 : ℤ) ∧
    (∑ n ∈ Ico 71424 71552, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-5590555290369045936754960456 : ℤ) := by
  rcases cdemPrefixStats_71424_71488 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_71488_71552 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 71424 ≤ 71488) (by norm_num : 71488 ≤ 71552), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 71424 ≤ 71488) (by norm_num : 71488 ≤ 71552), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 71424 ≤ 71488) (by norm_num : 71488 ≤ 71552), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 71424 ≤ 71488) (by norm_num : 71488 ≤ 71552), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_71552_71616 :
    (∑ n ∈ Ico 71552 71616, mobiusTreeValue 16 mobiusTable1200001 n) = (5 : ℤ) ∧
    (∑ n ∈ Ico 71552 71616, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 71552 71616, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (349211 : ℤ) ∧
    (∑ n ∈ Ico 71552 71616, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (6984294780838502002897487805 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_71616_71680 :
    (∑ n ∈ Ico 71616 71680, mobiusTreeValue 16 mobiusTable1200001 n) = (5 : ℤ) ∧
    (∑ n ∈ Ico 71616 71680, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 71616 71680, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (348906 : ℤ) ∧
    (∑ n ∈ Ico 71616 71680, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (6978231365235645007926780320 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_71552_71680 :
    (∑ n ∈ Ico 71552 71680, mobiusTreeValue 16 mobiusTable1200001 n) = (10 : ℤ) ∧
    (∑ n ∈ Ico 71552 71680, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (80 : ℕ) ∧
    (∑ n ∈ Ico 71552 71680, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (698117 : ℤ) ∧
    (∑ n ∈ Ico 71552 71680, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (13962526146074147010824268125 : ℤ) := by
  rcases cdemPrefixStats_71552_71616 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_71616_71680 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 71552 ≤ 71616) (by norm_num : 71616 ≤ 71680), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 71552 ≤ 71616) (by norm_num : 71616 ≤ 71680), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 71552 ≤ 71616) (by norm_num : 71616 ≤ 71680), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 71552 ≤ 71616) (by norm_num : 71616 ≤ 71680), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_71424_71680 :
    (∑ n ∈ Ico 71424 71680, mobiusTreeValue 16 mobiusTable1200001 n) = (6 : ℤ) ∧
    (∑ n ∈ Ico 71424 71680, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (158 : ℕ) ∧
    (∑ n ∈ Ico 71424 71680, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (418592 : ℤ) ∧
    (∑ n ∈ Ico 71424 71680, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (8371970855705101074069307669 : ℤ) := by
  rcases cdemPrefixStats_71424_71552 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_71552_71680 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 71424 ≤ 71552) (by norm_num : 71552 ≤ 71680), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 71424 ≤ 71552) (by norm_num : 71552 ≤ 71680), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 71424 ≤ 71552) (by norm_num : 71552 ≤ 71680), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 71424 ≤ 71552) (by norm_num : 71552 ≤ 71680), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_71168_71680 :
    (∑ n ∈ Ico 71168 71680, mobiusTreeValue 16 mobiusTable1200001 n) = (-19 : ℤ) ∧
    (∑ n ∈ Ico 71168 71680, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (313 : ℕ) ∧
    (∑ n ∈ Ico 71168 71680, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-1333147 : ℤ) ∧
    (∑ n ∈ Ico 71168 71680, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-26663163864983684744979517488 : ℤ) := by
  rcases cdemPrefixStats_71168_71424 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_71424_71680 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 71168 ≤ 71424) (by norm_num : 71424 ≤ 71680), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 71168 ≤ 71424) (by norm_num : 71424 ≤ 71680), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 71168 ≤ 71424) (by norm_num : 71424 ≤ 71680), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 71168 ≤ 71424) (by norm_num : 71424 ≤ 71680), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_70656_71680 :
    (∑ n ∈ Ico 70656 71680, mobiusTreeValue 16 mobiusTable1200001 n) = (-21 : ℤ) ∧
    (∑ n ∈ Ico 70656 71680, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (625 : ℕ) ∧
    (∑ n ∈ Ico 70656 71680, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-1471122 : ℤ) ∧
    (∑ n ∈ Ico 70656 71680, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-29422724094581554621489191554 : ℤ) := by
  rcases cdemPrefixStats_70656_71168 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_71168_71680 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 70656 ≤ 71168) (by norm_num : 71168 ≤ 71680), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 70656 ≤ 71168) (by norm_num : 71168 ≤ 71680), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 70656 ≤ 71168) (by norm_num : 71168 ≤ 71680), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 70656 ≤ 71168) (by norm_num : 71168 ≤ 71680), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_69632_71680 :
    (∑ n ∈ Ico 69632 71680, mobiusTreeValue 16 mobiusTable1200001 n) = (-65 : ℤ) ∧
    (∑ n ∈ Ico 69632 71680, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (1247 : ℕ) ∧
    (∑ n ∈ Ico 69632 71680, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-4610535 : ℤ) ∧
    (∑ n ∈ Ico 69632 71680, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-92211485399019277508198791003 : ℤ) := by
  rcases cdemPrefixStats_69632_70656 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_70656_71680 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 69632 ≤ 70656) (by norm_num : 70656 ≤ 71680), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 69632 ≤ 70656) (by norm_num : 70656 ≤ 71680), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 69632 ≤ 70656) (by norm_num : 70656 ≤ 71680), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 69632 ≤ 70656) (by norm_num : 70656 ≤ 71680), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_71680_71744 :
    (∑ n ∈ Ico 71680 71744, mobiusTreeValue 16 mobiusTable1200001 n) = (10 : ℤ) ∧
    (∑ n ∈ Ico 71680 71744, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 71680 71744, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (697127 : ℤ) ∧
    (∑ n ∈ Ico 71680 71744, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (13942646627915471345251659395 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_71744_71808 :
    (∑ n ∈ Ico 71744 71808, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 71744 71808, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 71744 71808, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-88 : ℤ) ∧
    (∑ n ∈ Ico 71744 71808, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-1766281209082833203991678 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_71680_71808 :
    (∑ n ∈ Ico 71680 71808, mobiusTreeValue 16 mobiusTable1200001 n) = (10 : ℤ) ∧
    (∑ n ∈ Ico 71680 71808, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (80 : ℕ) ∧
    (∑ n ∈ Ico 71680 71808, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (697039 : ℤ) ∧
    (∑ n ∈ Ico 71680 71808, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (13940880346706388512047667717 : ℤ) := by
  rcases cdemPrefixStats_71680_71744 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_71744_71808 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 71680 ≤ 71744) (by norm_num : 71744 ≤ 71808), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 71680 ≤ 71744) (by norm_num : 71744 ≤ 71808), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 71680 ≤ 71744) (by norm_num : 71744 ≤ 71808), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 71680 ≤ 71744) (by norm_num : 71744 ≤ 71808), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_71808_71872 :
    (∑ n ∈ Ico 71808 71872, mobiusTreeValue 16 mobiusTable1200001 n) = (-7 : ℤ) ∧
    (∑ n ∈ Ico 71808 71872, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 71808 71872, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-487211 : ℤ) ∧
    (∑ n ∈ Ico 71808 71872, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-9744302242515671266592040833 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_71872_71936 :
    (∑ n ∈ Ico 71872 71936, mobiusTreeValue 16 mobiusTable1200001 n) = (-9 : ℤ) ∧
    (∑ n ∈ Ico 71872 71936, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 71872 71936, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-625977 : ℤ) ∧
    (∑ n ∈ Ico 71872 71936, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-12519648483550903567423555465 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_71808_71936 :
    (∑ n ∈ Ico 71808 71936, mobiusTreeValue 16 mobiusTable1200001 n) = (-16 : ℤ) ∧
    (∑ n ∈ Ico 71808 71936, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (80 : ℕ) ∧
    (∑ n ∈ Ico 71808 71936, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-1113188 : ℤ) ∧
    (∑ n ∈ Ico 71808 71936, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-22263950726066574834015596298 : ℤ) := by
  rcases cdemPrefixStats_71808_71872 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_71872_71936 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 71808 ≤ 71872) (by norm_num : 71872 ≤ 71936), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 71808 ≤ 71872) (by norm_num : 71872 ≤ 71936), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 71808 ≤ 71872) (by norm_num : 71872 ≤ 71936), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 71808 ≤ 71872) (by norm_num : 71872 ≤ 71936), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_71680_71936 :
    (∑ n ∈ Ico 71680 71936, mobiusTreeValue 16 mobiusTable1200001 n) = (-6 : ℤ) ∧
    (∑ n ∈ Ico 71680 71936, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (160 : ℕ) ∧
    (∑ n ∈ Ico 71680 71936, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-416149 : ℤ) ∧
    (∑ n ∈ Ico 71680 71936, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-8323070379360186321967928581 : ℤ) := by
  rcases cdemPrefixStats_71680_71808 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_71808_71936 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 71680 ≤ 71808) (by norm_num : 71808 ≤ 71936), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 71680 ≤ 71808) (by norm_num : 71808 ≤ 71936), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 71680 ≤ 71808) (by norm_num : 71808 ≤ 71936), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 71680 ≤ 71808) (by norm_num : 71808 ≤ 71936), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_71936_72000 :
    (∑ n ∈ Ico 71936 72000, mobiusTreeValue 16 mobiusTable1200001 n) = (2 : ℤ) ∧
    (∑ n ∈ Ico 71936 72000, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (36 : ℕ) ∧
    (∑ n ∈ Ico 71936 72000, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (138917 : ℤ) ∧
    (∑ n ∈ Ico 71936 72000, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (2778355938940016435701353282 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_72000_72064 :
    (∑ n ∈ Ico 72000 72064, mobiusTreeValue 16 mobiusTable1200001 n) = (7 : ℤ) ∧
    (∑ n ∈ Ico 72000 72064, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 72000 72064, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (486068 : ℤ) ∧
    (∑ n ∈ Ico 72000 72064, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (9721392687915141398894382084 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_71936_72064 :
    (∑ n ∈ Ico 71936 72064, mobiusTreeValue 16 mobiusTable1200001 n) = (9 : ℤ) ∧
    (∑ n ∈ Ico 71936 72064, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (75 : ℕ) ∧
    (∑ n ∈ Ico 71936 72064, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (624985 : ℤ) ∧
    (∑ n ∈ Ico 71936 72064, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (12499748626855157834595735366 : ℤ) := by
  rcases cdemPrefixStats_71936_72000 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_72000_72064 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 71936 ≤ 72000) (by norm_num : 72000 ≤ 72064), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 71936 ≤ 72000) (by norm_num : 72000 ≤ 72064), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 71936 ≤ 72000) (by norm_num : 72000 ≤ 72064), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 71936 ≤ 72000) (by norm_num : 72000 ≤ 72064), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_72064_72128 :
    (∑ n ∈ Ico 72064 72128, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 72064 72128, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 72064 72128, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (69422 : ℤ) ∧
    (∑ n ∈ Ico 72064 72128, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1388482672741762597467203877 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_72128_72192 :
    (∑ n ∈ Ico 72128 72192, mobiusTreeValue 16 mobiusTable1200001 n) = (5 : ℤ) ∧
    (∑ n ∈ Ico 72128 72192, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 72128 72192, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (346394 : ℤ) ∧
    (∑ n ∈ Ico 72128 72192, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (6927914625056582508314592805 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_72064_72192 :
    (∑ n ∈ Ico 72064 72192, mobiusTreeValue 16 mobiusTable1200001 n) = (6 : ℤ) ∧
    (∑ n ∈ Ico 72064 72192, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 72064 72192, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (415816 : ℤ) ∧
    (∑ n ∈ Ico 72064 72192, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (8316397297798345105781796682 : ℤ) := by
  rcases cdemPrefixStats_72064_72128 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_72128_72192 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 72064 ≤ 72128) (by norm_num : 72128 ≤ 72192), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 72064 ≤ 72128) (by norm_num : 72128 ≤ 72192), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 72064 ≤ 72128) (by norm_num : 72128 ≤ 72192), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 72064 ≤ 72128) (by norm_num : 72128 ≤ 72192), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_71936_72192 :
    (∑ n ∈ Ico 71936 72192, mobiusTreeValue 16 mobiusTable1200001 n) = (15 : ℤ) ∧
    (∑ n ∈ Ico 71936 72192, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (153 : ℕ) ∧
    (∑ n ∈ Ico 71936 72192, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (1040801 : ℤ) ∧
    (∑ n ∈ Ico 71936 72192, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (20816145924653502940377532048 : ℤ) := by
  rcases cdemPrefixStats_71936_72064 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_72064_72192 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 71936 ≤ 72064) (by norm_num : 72064 ≤ 72192), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 71936 ≤ 72064) (by norm_num : 72064 ≤ 72192), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 71936 ≤ 72064) (by norm_num : 72064 ≤ 72192), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 71936 ≤ 72064) (by norm_num : 72064 ≤ 72192), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_71680_72192 :
    (∑ n ∈ Ico 71680 72192, mobiusTreeValue 16 mobiusTable1200001 n) = (9 : ℤ) ∧
    (∑ n ∈ Ico 71680 72192, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (313 : ℕ) ∧
    (∑ n ∈ Ico 71680 72192, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (624652 : ℤ) ∧
    (∑ n ∈ Ico 71680 72192, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (12493075545293316618409603467 : ℤ) := by
  rcases cdemPrefixStats_71680_71936 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_71936_72192 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 71680 ≤ 71936) (by norm_num : 71936 ≤ 72192), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 71680 ≤ 71936) (by norm_num : 71936 ≤ 72192), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 71680 ≤ 71936) (by norm_num : 71936 ≤ 72192), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 71680 ≤ 71936) (by norm_num : 71936 ≤ 72192), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_72192_72256 :
    (∑ n ∈ Ico 72192 72256, mobiusTreeValue 16 mobiusTable1200001 n) = (-4 : ℤ) ∧
    (∑ n ∈ Ico 72192 72256, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 72192 72256, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-276933 : ℤ) ∧
    (∑ n ∈ Ico 72192 72256, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-5538670870958412984499922236 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_72256_72320 :
    (∑ n ∈ Ico 72256 72320, mobiusTreeValue 16 mobiusTable1200001 n) = (6 : ℤ) ∧
    (∑ n ∈ Ico 72256 72320, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 72256 72320, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (414873 : ℤ) ∧
    (∑ n ∈ Ico 72256 72320, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (8297493498532850473650962927 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_72192_72320 :
    (∑ n ∈ Ico 72192 72320, mobiusTreeValue 16 mobiusTable1200001 n) = (2 : ℤ) ∧
    (∑ n ∈ Ico 72192 72320, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (80 : ℕ) ∧
    (∑ n ∈ Ico 72192 72320, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (137940 : ℤ) ∧
    (∑ n ∈ Ico 72192 72320, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (2758822627574437489151040691 : ℤ) := by
  rcases cdemPrefixStats_72192_72256 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_72256_72320 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 72192 ≤ 72256) (by norm_num : 72256 ≤ 72320), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 72192 ≤ 72256) (by norm_num : 72256 ≤ 72320), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 72192 ≤ 72256) (by norm_num : 72256 ≤ 72320), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 72192 ≤ 72256) (by norm_num : 72256 ≤ 72320), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_72320_72384 :
    (∑ n ∈ Ico 72320 72384, mobiusTreeValue 16 mobiusTable1200001 n) = (2 : ℤ) ∧
    (∑ n ∈ Ico 72320 72384, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (36 : ℕ) ∧
    (∑ n ∈ Ico 72320 72384, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (138421 : ℤ) ∧
    (∑ n ∈ Ico 72320 72384, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (2768409728244717381082148067 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_72384_72448 :
    (∑ n ∈ Ico 72384 72448, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 72384 72448, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 72384 72448, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (68995 : ℤ) ∧
    (∑ n ∈ Ico 72384 72448, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1379976191816148082248512831 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_72320_72448 :
    (∑ n ∈ Ico 72320 72448, mobiusTreeValue 16 mobiusTable1200001 n) = (3 : ℤ) ∧
    (∑ n ∈ Ico 72320 72448, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 72320 72448, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (207416 : ℤ) ∧
    (∑ n ∈ Ico 72320 72448, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (4148385920060865463330660898 : ℤ) := by
  rcases cdemPrefixStats_72320_72384 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_72384_72448 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 72320 ≤ 72384) (by norm_num : 72384 ≤ 72448), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 72320 ≤ 72384) (by norm_num : 72384 ≤ 72448), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 72320 ≤ 72384) (by norm_num : 72384 ≤ 72448), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 72320 ≤ 72384) (by norm_num : 72384 ≤ 72448), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_72192_72448 :
    (∑ n ∈ Ico 72192 72448, mobiusTreeValue 16 mobiusTable1200001 n) = (5 : ℤ) ∧
    (∑ n ∈ Ico 72192 72448, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (157 : ℕ) ∧
    (∑ n ∈ Ico 72192 72448, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (345356 : ℤ) ∧
    (∑ n ∈ Ico 72192 72448, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (6907208547635302952481701589 : ℤ) := by
  rcases cdemPrefixStats_72192_72320 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_72320_72448 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 72192 ≤ 72320) (by norm_num : 72320 ≤ 72448), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 72192 ≤ 72320) (by norm_num : 72320 ≤ 72448), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 72192 ≤ 72320) (by norm_num : 72320 ≤ 72448), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 72192 ≤ 72320) (by norm_num : 72320 ≤ 72448), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_72448_72512 :
    (∑ n ∈ Ico 72448 72512, mobiusTreeValue 16 mobiusTable1200001 n) = (2 : ℤ) ∧
    (∑ n ∈ Ico 72448 72512, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 72448 72512, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (137890 : ℤ) ∧
    (∑ n ∈ Ico 72448 72512, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (2757783704004477699834838801 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_72512_72576 :
    (∑ n ∈ Ico 72512 72576, mobiusTreeValue 16 mobiusTable1200001 n) = (-5 : ℤ) ∧
    (∑ n ∈ Ico 72512 72576, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (35 : ℕ) ∧
    (∑ n ∈ Ico 72512 72576, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-344624 : ℤ) ∧
    (∑ n ∈ Ico 72512 72576, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-6892559588633900135245467422 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_72448_72576 :
    (∑ n ∈ Ico 72448 72576, mobiusTreeValue 16 mobiusTable1200001 n) = (-3 : ℤ) ∧
    (∑ n ∈ Ico 72448 72576, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (73 : ℕ) ∧
    (∑ n ∈ Ico 72448 72576, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-206734 : ℤ) ∧
    (∑ n ∈ Ico 72448 72576, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-4134775884629422435410628621 : ℤ) := by
  rcases cdemPrefixStats_72448_72512 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_72512_72576 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 72448 ≤ 72512) (by norm_num : 72512 ≤ 72576), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 72448 ≤ 72512) (by norm_num : 72512 ≤ 72576), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 72448 ≤ 72512) (by norm_num : 72512 ≤ 72576), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 72448 ≤ 72512) (by norm_num : 72512 ≤ 72576), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_72576_72640 :
    (∑ n ∈ Ico 72576 72640, mobiusTreeValue 16 mobiusTable1200001 n) = (6 : ℤ) ∧
    (∑ n ∈ Ico 72576 72640, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 72576 72640, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (413189 : ℤ) ∧
    (∑ n ∈ Ico 72576 72640, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (8263836806815110954587436739 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_72640_72704 :
    (∑ n ∈ Ico 72640 72704, mobiusTreeValue 16 mobiusTable1200001 n) = (-8 : ℤ) ∧
    (∑ n ∈ Ico 72640 72704, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 72640 72704, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-550557 : ℤ) ∧
    (∑ n ∈ Ico 72640 72704, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-11011245793742987085682637672 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_72576_72704 :
    (∑ n ∈ Ico 72576 72704, mobiusTreeValue 16 mobiusTable1200001 n) = (-2 : ℤ) ∧
    (∑ n ∈ Ico 72576 72704, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (80 : ℕ) ∧
    (∑ n ∈ Ico 72576 72704, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-137368 : ℤ) ∧
    (∑ n ∈ Ico 72576 72704, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-2747408986927876131095200933 : ℤ) := by
  rcases cdemPrefixStats_72576_72640 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_72640_72704 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 72576 ≤ 72640) (by norm_num : 72640 ≤ 72704), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 72576 ≤ 72640) (by norm_num : 72640 ≤ 72704), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 72576 ≤ 72640) (by norm_num : 72640 ≤ 72704), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 72576 ≤ 72640) (by norm_num : 72640 ≤ 72704), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_72448_72704 :
    (∑ n ∈ Ico 72448 72704, mobiusTreeValue 16 mobiusTable1200001 n) = (-5 : ℤ) ∧
    (∑ n ∈ Ico 72448 72704, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (153 : ℕ) ∧
    (∑ n ∈ Ico 72448 72704, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-344102 : ℤ) ∧
    (∑ n ∈ Ico 72448 72704, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-6882184871557298566505829554 : ℤ) := by
  rcases cdemPrefixStats_72448_72576 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_72576_72704 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 72448 ≤ 72576) (by norm_num : 72576 ≤ 72704), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 72448 ≤ 72576) (by norm_num : 72576 ≤ 72704), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 72448 ≤ 72576) (by norm_num : 72576 ≤ 72704), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 72448 ≤ 72576) (by norm_num : 72576 ≤ 72704), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_72192_72704 :
    (∑ n ∈ Ico 72192 72704, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 72192 72704, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (310 : ℕ) ∧
    (∑ n ∈ Ico 72192 72704, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (1254 : ℤ) ∧
    (∑ n ∈ Ico 72192 72704, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (25023676078004385975872035 : ℤ) := by
  rcases cdemPrefixStats_72192_72448 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_72448_72704 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 72192 ≤ 72448) (by norm_num : 72448 ≤ 72704), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 72192 ≤ 72448) (by norm_num : 72448 ≤ 72704), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 72192 ≤ 72448) (by norm_num : 72448 ≤ 72704), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 72192 ≤ 72448) (by norm_num : 72448 ≤ 72704), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_71680_72704 :
    (∑ n ∈ Ico 71680 72704, mobiusTreeValue 16 mobiusTable1200001 n) = (9 : ℤ) ∧
    (∑ n ∈ Ico 71680 72704, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (623 : ℕ) ∧
    (∑ n ∈ Ico 71680 72704, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (625906 : ℤ) ∧
    (∑ n ∈ Ico 71680 72704, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (12518099221371321004385475502 : ℤ) := by
  rcases cdemPrefixStats_71680_72192 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_72192_72704 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 71680 ≤ 72192) (by norm_num : 72192 ≤ 72704), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 71680 ≤ 72192) (by norm_num : 72192 ≤ 72704), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 71680 ≤ 72192) (by norm_num : 72192 ≤ 72704), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 71680 ≤ 72192) (by norm_num : 72192 ≤ 72704), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_72704_72768 :
    (∑ n ∈ Ico 72704 72768, mobiusTreeValue 16 mobiusTable1200001 n) = (-2 : ℤ) ∧
    (∑ n ∈ Ico 72704 72768, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 72704 72768, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-137452 : ℤ) ∧
    (∑ n ∈ Ico 72704 72768, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-2749065138768381342344081436 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_72768_72832 :
    (∑ n ∈ Ico 72768 72832, mobiusTreeValue 16 mobiusTable1200001 n) = (2 : ℤ) ∧
    (∑ n ∈ Ico 72768 72832, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 72768 72832, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (137492 : ℤ) ∧
    (∑ n ∈ Ico 72768 72832, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (2749913149025680470874850702 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_72704_72832 :
    (∑ n ∈ Ico 72704 72832, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 72704 72832, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (80 : ℕ) ∧
    (∑ n ∈ Ico 72704 72832, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (40 : ℤ) ∧
    (∑ n ∈ Ico 72704 72832, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (848010257299128530769266 : ℤ) := by
  rcases cdemPrefixStats_72704_72768 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_72768_72832 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 72704 ≤ 72768) (by norm_num : 72768 ≤ 72832), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 72704 ≤ 72768) (by norm_num : 72768 ≤ 72832), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 72704 ≤ 72768) (by norm_num : 72768 ≤ 72832), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 72704 ≤ 72768) (by norm_num : 72768 ≤ 72832), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_72832_72896 :
    (∑ n ∈ Ico 72832 72896, mobiusTreeValue 16 mobiusTable1200001 n) = (-11 : ℤ) ∧
    (∑ n ∈ Ico 72832 72896, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 72832 72896, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-754677 : ℤ) ∧
    (∑ n ∈ Ico 72832 72896, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-15093699419020449855347116543 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_72896_72960 :
    (∑ n ∈ Ico 72896 72960, mobiusTreeValue 16 mobiusTable1200001 n) = (-7 : ℤ) ∧
    (∑ n ∈ Ico 72896 72960, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 72896 72960, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-479858 : ℤ) ∧
    (∑ n ∈ Ico 72896 72960, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-9597210975831512280962089990 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_72832_72960 :
    (∑ n ∈ Ico 72832 72960, mobiusTreeValue 16 mobiusTable1200001 n) = (-18 : ℤ) ∧
    (∑ n ∈ Ico 72832 72960, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (76 : ℕ) ∧
    (∑ n ∈ Ico 72832 72960, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-1234535 : ℤ) ∧
    (∑ n ∈ Ico 72832 72960, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-24690910394851962136309206533 : ℤ) := by
  rcases cdemPrefixStats_72832_72896 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_72896_72960 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 72832 ≤ 72896) (by norm_num : 72896 ≤ 72960), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 72832 ≤ 72896) (by norm_num : 72896 ≤ 72960), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 72832 ≤ 72896) (by norm_num : 72896 ≤ 72960), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 72832 ≤ 72896) (by norm_num : 72896 ≤ 72960), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_72704_72960 :
    (∑ n ∈ Ico 72704 72960, mobiusTreeValue 16 mobiusTable1200001 n) = (-18 : ℤ) ∧
    (∑ n ∈ Ico 72704 72960, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (156 : ℕ) ∧
    (∑ n ∈ Ico 72704 72960, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-1234495 : ℤ) ∧
    (∑ n ∈ Ico 72704 72960, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-24690062384594663007778437267 : ℤ) := by
  rcases cdemPrefixStats_72704_72832 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_72832_72960 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 72704 ≤ 72832) (by norm_num : 72832 ≤ 72960), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 72704 ≤ 72832) (by norm_num : 72832 ≤ 72960), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 72704 ≤ 72832) (by norm_num : 72832 ≤ 72960), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 72704 ≤ 72832) (by norm_num : 72832 ≤ 72960), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_72960_73024 :
    (∑ n ∈ Ico 72960 73024, mobiusTreeValue 16 mobiusTable1200001 n) = (-2 : ℤ) ∧
    (∑ n ∈ Ico 72960 73024, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 72960 73024, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-136888 : ℤ) ∧
    (∑ n ∈ Ico 72960 73024, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-2737850198201644129043992205 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_73024_73088 :
    (∑ n ∈ Ico 73024 73088, mobiusTreeValue 16 mobiusTable1200001 n) = (-2 : ℤ) ∧
    (∑ n ∈ Ico 73024 73088, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 73024 73088, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-136911 : ℤ) ∧
    (∑ n ∈ Ico 73024 73088, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-2738262956417738585674893657 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_72960_73088 :
    (∑ n ∈ Ico 72960 73088, mobiusTreeValue 16 mobiusTable1200001 n) = (-4 : ℤ) ∧
    (∑ n ∈ Ico 72960 73088, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (76 : ℕ) ∧
    (∑ n ∈ Ico 72960 73088, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-273799 : ℤ) ∧
    (∑ n ∈ Ico 72960 73088, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-5476113154619382714718885862 : ℤ) := by
  rcases cdemPrefixStats_72960_73024 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_73024_73088 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 72960 ≤ 73024) (by norm_num : 73024 ≤ 73088), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 72960 ≤ 73024) (by norm_num : 73024 ≤ 73088), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 72960 ≤ 73024) (by norm_num : 73024 ≤ 73088), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 72960 ≤ 73024) (by norm_num : 73024 ≤ 73088), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_73088_73152 :
    (∑ n ∈ Ico 73088 73152, mobiusTreeValue 16 mobiusTable1200001 n) = (11 : ℤ) ∧
    (∑ n ∈ Ico 73088 73152, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 73088 73152, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (752277 : ℤ) ∧
    (∑ n ∈ Ico 73088 73152, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (15045597322798703453613388576 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_73152_73216 :
    (∑ n ∈ Ico 73152 73216, mobiusTreeValue 16 mobiusTable1200001 n) = (11 : ℤ) ∧
    (∑ n ∈ Ico 73152 73216, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 73152 73216, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (751526 : ℤ) ∧
    (∑ n ∈ Ico 73152 73216, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (15030664747425457035943174518 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_73088_73216 :
    (∑ n ∈ Ico 73088 73216, mobiusTreeValue 16 mobiusTable1200001 n) = (22 : ℤ) ∧
    (∑ n ∈ Ico 73088 73216, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (76 : ℕ) ∧
    (∑ n ∈ Ico 73088 73216, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (1503803 : ℤ) ∧
    (∑ n ∈ Ico 73088 73216, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (30076262070224160489556563094 : ℤ) := by
  rcases cdemPrefixStats_73088_73152 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_73152_73216 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 73088 ≤ 73152) (by norm_num : 73152 ≤ 73216), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 73088 ≤ 73152) (by norm_num : 73152 ≤ 73216), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 73088 ≤ 73152) (by norm_num : 73152 ≤ 73216), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 73088 ≤ 73152) (by norm_num : 73152 ≤ 73216), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_72960_73216 :
    (∑ n ∈ Ico 72960 73216, mobiusTreeValue 16 mobiusTable1200001 n) = (18 : ℤ) ∧
    (∑ n ∈ Ico 72960 73216, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (152 : ℕ) ∧
    (∑ n ∈ Ico 72960 73216, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (1230004 : ℤ) ∧
    (∑ n ∈ Ico 72960 73216, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (24600148915604777774837677232 : ℤ) := by
  rcases cdemPrefixStats_72960_73088 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_73088_73216 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 72960 ≤ 73088) (by norm_num : 73088 ≤ 73216), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 72960 ≤ 73088) (by norm_num : 73088 ≤ 73216), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 72960 ≤ 73088) (by norm_num : 73088 ≤ 73216), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 72960 ≤ 73088) (by norm_num : 73088 ≤ 73216), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_72704_73216 :
    (∑ n ∈ Ico 72704 73216, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 72704 73216, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (308 : ℕ) ∧
    (∑ n ∈ Ico 72704 73216, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-4491 : ℤ) ∧
    (∑ n ∈ Ico 72704 73216, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-89913468989885232940760035 : ℤ) := by
  rcases cdemPrefixStats_72704_72960 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_72960_73216 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 72704 ≤ 72960) (by norm_num : 72960 ≤ 73216), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 72704 ≤ 72960) (by norm_num : 72960 ≤ 73216), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 72704 ≤ 72960) (by norm_num : 72960 ≤ 73216), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 72704 ≤ 72960) (by norm_num : 72960 ≤ 73216), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_73216_73280 :
    (∑ n ∈ Ico 73216 73280, mobiusTreeValue 16 mobiusTable1200001 n) = (9 : ℤ) ∧
    (∑ n ∈ Ico 73216 73280, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 73216 73280, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (614237 : ℤ) ∧
    (∑ n ∈ Ico 73216 73280, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (12284826494841416054155176314 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_73280_73344 :
    (∑ n ∈ Ico 73280 73344, mobiusTreeValue 16 mobiusTable1200001 n) = (-6 : ℤ) ∧
    (∑ n ∈ Ico 73280 73344, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 73280 73344, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-409328 : ℤ) ∧
    (∑ n ∈ Ico 73280 73344, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-8186580822760545627106636204 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_73216_73344 :
    (∑ n ∈ Ico 73216 73344, mobiusTreeValue 16 mobiusTable1200001 n) = (3 : ℤ) ∧
    (∑ n ∈ Ico 73216 73344, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (79 : ℕ) ∧
    (∑ n ∈ Ico 73216 73344, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (204909 : ℤ) ∧
    (∑ n ∈ Ico 73216 73344, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (4098245672080870427048540110 : ℤ) := by
  rcases cdemPrefixStats_73216_73280 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_73280_73344 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 73216 ≤ 73280) (by norm_num : 73280 ≤ 73344), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 73216 ≤ 73280) (by norm_num : 73280 ≤ 73344), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 73216 ≤ 73280) (by norm_num : 73280 ≤ 73344), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 73216 ≤ 73280) (by norm_num : 73280 ≤ 73344), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_73344_73408 :
    (∑ n ∈ Ico 73344 73408, mobiusTreeValue 16 mobiusTable1200001 n) = (-2 : ℤ) ∧
    (∑ n ∈ Ico 73344 73408, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 73344 73408, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-136401 : ℤ) ∧
    (∑ n ∈ Ico 73344 73408, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-2728045179747203791607553167 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_73408_73472 :
    (∑ n ∈ Ico 73408 73472, mobiusTreeValue 16 mobiusTable1200001 n) = (-3 : ℤ) ∧
    (∑ n ∈ Ico 73408 73472, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 73408 73472, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-203961 : ℤ) ∧
    (∑ n ∈ Ico 73408 73472, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-4079182337289248472060681231 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_73344_73472 :
    (∑ n ∈ Ico 73344 73472, mobiusTreeValue 16 mobiusTable1200001 n) = (-5 : ℤ) ∧
    (∑ n ∈ Ico 73344 73472, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (75 : ℕ) ∧
    (∑ n ∈ Ico 73344 73472, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-340362 : ℤ) ∧
    (∑ n ∈ Ico 73344 73472, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-6807227517036452263668234398 : ℤ) := by
  rcases cdemPrefixStats_73344_73408 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_73408_73472 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 73344 ≤ 73408) (by norm_num : 73408 ≤ 73472), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 73344 ≤ 73408) (by norm_num : 73408 ≤ 73472), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 73344 ≤ 73408) (by norm_num : 73408 ≤ 73472), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 73344 ≤ 73408) (by norm_num : 73408 ≤ 73472), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_73216_73472 :
    (∑ n ∈ Ico 73216 73472, mobiusTreeValue 16 mobiusTable1200001 n) = (-2 : ℤ) ∧
    (∑ n ∈ Ico 73216 73472, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (154 : ℕ) ∧
    (∑ n ∈ Ico 73216 73472, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-135453 : ℤ) ∧
    (∑ n ∈ Ico 73216 73472, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-2708981844955581836619694288 : ℤ) := by
  rcases cdemPrefixStats_73216_73344 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_73344_73472 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 73216 ≤ 73344) (by norm_num : 73344 ≤ 73472), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 73216 ≤ 73344) (by norm_num : 73344 ≤ 73472), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 73216 ≤ 73344) (by norm_num : 73344 ≤ 73472), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 73216 ≤ 73344) (by norm_num : 73344 ≤ 73472), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_73472_73536 :
    (∑ n ∈ Ico 73472 73536, mobiusTreeValue 16 mobiusTable1200001 n) = (3 : ℤ) ∧
    (∑ n ∈ Ico 73472 73536, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 73472 73536, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (204116 : ℤ) ∧
    (∑ n ∈ Ico 73472 73536, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (4082354318686767266421049361 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_73536_73600 :
    (∑ n ∈ Ico 73536 73600, mobiusTreeValue 16 mobiusTable1200001 n) = (-2 : ℤ) ∧
    (∑ n ∈ Ico 73536 73600, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 73536 73600, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-135915 : ℤ) ∧
    (∑ n ∈ Ico 73536 73600, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-2718296685365857417247803133 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_73472_73600 :
    (∑ n ∈ Ico 73472 73600, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 73472 73600, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (79 : ℕ) ∧
    (∑ n ∈ Ico 73472 73600, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (68201 : ℤ) ∧
    (∑ n ∈ Ico 73472 73600, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1364057633320909849173246228 : ℤ) := by
  rcases cdemPrefixStats_73472_73536 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_73536_73600 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 73472 ≤ 73536) (by norm_num : 73536 ≤ 73600), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 73472 ≤ 73536) (by norm_num : 73536 ≤ 73600), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 73472 ≤ 73536) (by norm_num : 73536 ≤ 73600), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 73472 ≤ 73536) (by norm_num : 73536 ≤ 73600), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_73600_73664 :
    (∑ n ∈ Ico 73600 73664, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 73600 73664, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 73600 73664, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (67998 : ℤ) ∧
    (∑ n ∈ Ico 73600 73664, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1359949861634211234126212034 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_73664_73728 :
    (∑ n ∈ Ico 73664 73728, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 73664 73728, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 73664 73728, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (30 : ℤ) ∧
    (∑ n ∈ Ico 73664 73728, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (588850609464216693671542 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_73600_73728 :
    (∑ n ∈ Ico 73600 73728, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 73600 73728, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (79 : ℕ) ∧
    (∑ n ∈ Ico 73600 73728, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (68028 : ℤ) ∧
    (∑ n ∈ Ico 73600 73728, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1360538712243675450819883576 : ℤ) := by
  rcases cdemPrefixStats_73600_73664 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_73664_73728 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 73600 ≤ 73664) (by norm_num : 73664 ≤ 73728), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 73600 ≤ 73664) (by norm_num : 73664 ≤ 73728), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 73600 ≤ 73664) (by norm_num : 73664 ≤ 73728), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 73600 ≤ 73664) (by norm_num : 73664 ≤ 73728), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_73472_73728 :
    (∑ n ∈ Ico 73472 73728, mobiusTreeValue 16 mobiusTable1200001 n) = (2 : ℤ) ∧
    (∑ n ∈ Ico 73472 73728, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (158 : ℕ) ∧
    (∑ n ∈ Ico 73472 73728, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (136229 : ℤ) ∧
    (∑ n ∈ Ico 73472 73728, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (2724596345564585299993129804 : ℤ) := by
  rcases cdemPrefixStats_73472_73600 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_73600_73728 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 73472 ≤ 73600) (by norm_num : 73600 ≤ 73728), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 73472 ≤ 73600) (by norm_num : 73600 ≤ 73728), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 73472 ≤ 73600) (by norm_num : 73600 ≤ 73728), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 73472 ≤ 73600) (by norm_num : 73600 ≤ 73728), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_73216_73728 :
    (∑ n ∈ Ico 73216 73728, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 73216 73728, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (312 : ℕ) ∧
    (∑ n ∈ Ico 73216 73728, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (776 : ℤ) ∧
    (∑ n ∈ Ico 73216 73728, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (15614500609003463373435516 : ℤ) := by
  rcases cdemPrefixStats_73216_73472 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_73472_73728 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 73216 ≤ 73472) (by norm_num : 73472 ≤ 73728), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 73216 ≤ 73472) (by norm_num : 73472 ≤ 73728), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 73216 ≤ 73472) (by norm_num : 73472 ≤ 73728), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 73216 ≤ 73472) (by norm_num : 73472 ≤ 73728), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_72704_73728 :
    (∑ n ∈ Ico 72704 73728, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 72704 73728, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (620 : ℕ) ∧
    (∑ n ∈ Ico 72704 73728, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-3715 : ℤ) ∧
    (∑ n ∈ Ico 72704 73728, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-74298968380881769567324519 : ℤ) := by
  rcases cdemPrefixStats_72704_73216 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_73216_73728 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 72704 ≤ 73216) (by norm_num : 73216 ≤ 73728), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 72704 ≤ 73216) (by norm_num : 73216 ≤ 73728), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 72704 ≤ 73216) (by norm_num : 73216 ≤ 73728), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 72704 ≤ 73216) (by norm_num : 73216 ≤ 73728), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_71680_73728 :
    (∑ n ∈ Ico 71680 73728, mobiusTreeValue 16 mobiusTable1200001 n) = (9 : ℤ) ∧
    (∑ n ∈ Ico 71680 73728, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (1243 : ℕ) ∧
    (∑ n ∈ Ico 71680 73728, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (622191 : ℤ) ∧
    (∑ n ∈ Ico 71680 73728, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (12443800252990439234818150983 : ℤ) := by
  rcases cdemPrefixStats_71680_72704 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_72704_73728 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 71680 ≤ 72704) (by norm_num : 72704 ≤ 73728), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 71680 ≤ 72704) (by norm_num : 72704 ≤ 73728), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 71680 ≤ 72704) (by norm_num : 72704 ≤ 73728), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 71680 ≤ 72704) (by norm_num : 72704 ≤ 73728), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_69632_73728 :
    (∑ n ∈ Ico 69632 73728, mobiusTreeValue 16 mobiusTable1200001 n) = (-56 : ℤ) ∧
    (∑ n ∈ Ico 69632 73728, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (2490 : ℕ) ∧
    (∑ n ∈ Ico 69632 73728, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-3988344 : ℤ) ∧
    (∑ n ∈ Ico 69632 73728, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-79767685146028838273380640020 : ℤ) := by
  rcases cdemPrefixStats_69632_71680 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_71680_73728 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 69632 ≤ 71680) (by norm_num : 71680 ≤ 73728), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 69632 ≤ 71680) (by norm_num : 71680 ≤ 73728), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 69632 ≤ 71680) (by norm_num : 71680 ≤ 73728), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 69632 ≤ 71680) (by norm_num : 71680 ≤ 73728), hR1, hR2] <;> norm_num

theorem cdemPrefixGroup017_checked_complete :
    (∑ n ∈ Ico 69632 73728, mobiusTreeValue 16 mobiusTable1200001 n) = (-56 : ℤ) ∧
    (∑ n ∈ Ico 69632 73728, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (2490 : ℕ) ∧
    (∑ n ∈ Ico 69632 73728, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-3988344 : ℤ) ∧
    (∑ n ∈ Ico 69632 73728, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-79767685146028838273380640020 : ℤ) := cdemPrefixStats_69632_73728
end Helfgott
#print axioms Helfgott.cdemPrefixGroup017_checked_complete

open Helfgott Finset
open scoped BigOperators

theorem solution :
    (∑ n ∈ Ico 69632 73728, mobiusTreeValue 16 mobiusTable1200001 n) = (-56 : ℤ) ∧
    (∑ n ∈ Ico 69632 73728, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (2490 : ℕ) ∧
    (∑ n ∈ Ico 69632 73728, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-3988344 : ℤ) ∧
    (∑ n ∈ Ico 69632 73728, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-79767685146028838273380640020 : ℤ) := Helfgott.cdemPrefixGroup017_checked_complete
#print axioms solution
