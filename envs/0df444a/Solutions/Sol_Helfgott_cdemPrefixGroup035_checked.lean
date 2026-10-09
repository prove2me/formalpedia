-- Prove2me | solution 1 for Helfgott.cdemPrefixGroup035_checked
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-09T02:33:46.676653+00:00
-- url     : https://prove2.me/submissions/12a02632-97a8-47be-8352-c8ddc8a433d1

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
private theorem cdemPrefixStats_143360_143424 :
    (∑ n ∈ Ico 143360 143424, mobiusTreeValue 16 mobiusTable1200001 n) = (6 : ℤ) ∧
    (∑ n ∈ Ico 143360 143424, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 143360 143424, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (209204 : ℤ) ∧
    (∑ n ∈ Ico 143360 143424, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (4184153906839433862523093280 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_143424_143488 :
    (∑ n ∈ Ico 143424 143488, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 143424 143488, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 143424 143488, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (22 : ℤ) ∧
    (∑ n ∈ Ico 143424 143488, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (500585333255485835329044 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_143360_143488 :
    (∑ n ∈ Ico 143360 143488, mobiusTreeValue 16 mobiusTable1200001 n) = (6 : ℤ) ∧
    (∑ n ∈ Ico 143360 143488, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (76 : ℕ) ∧
    (∑ n ∈ Ico 143360 143488, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (209226 : ℤ) ∧
    (∑ n ∈ Ico 143360 143488, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (4184654492172689348358422324 : ℤ) := by
  rcases cdemPrefixStats_143360_143424 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_143424_143488 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 143360 ≤ 143424) (by norm_num : 143424 ≤ 143488), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 143360 ≤ 143424) (by norm_num : 143424 ≤ 143488), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 143360 ≤ 143424) (by norm_num : 143424 ≤ 143488), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 143360 ≤ 143424) (by norm_num : 143424 ≤ 143488), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_143488_143552 :
    (∑ n ∈ Ico 143488 143552, mobiusTreeValue 16 mobiusTable1200001 n) = (-11 : ℤ) ∧
    (∑ n ∈ Ico 143488 143552, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 143488 143552, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-383255 : ℤ) ∧
    (∑ n ∈ Ico 143488 143552, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-7665175193725514346562712547 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_143552_143616 :
    (∑ n ∈ Ico 143552 143616, mobiusTreeValue 16 mobiusTable1200001 n) = (8 : ℤ) ∧
    (∑ n ∈ Ico 143552 143616, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 143552 143616, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (278561 : ℤ) ∧
    (∑ n ∈ Ico 143552 143616, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (5571263525878584409189960935 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_143488_143616 :
    (∑ n ∈ Ico 143488 143616, mobiusTreeValue 16 mobiusTable1200001 n) = (-3 : ℤ) ∧
    (∑ n ∈ Ico 143488 143616, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (79 : ℕ) ∧
    (∑ n ∈ Ico 143488 143616, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-104694 : ℤ) ∧
    (∑ n ∈ Ico 143488 143616, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-2093911667846929937372751612 : ℤ) := by
  rcases cdemPrefixStats_143488_143552 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_143552_143616 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 143488 ≤ 143552) (by norm_num : 143552 ≤ 143616), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 143488 ≤ 143552) (by norm_num : 143552 ≤ 143616), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 143488 ≤ 143552) (by norm_num : 143552 ≤ 143616), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 143488 ≤ 143552) (by norm_num : 143552 ≤ 143616), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_143360_143616 :
    (∑ n ∈ Ico 143360 143616, mobiusTreeValue 16 mobiusTable1200001 n) = (3 : ℤ) ∧
    (∑ n ∈ Ico 143360 143616, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (155 : ℕ) ∧
    (∑ n ∈ Ico 143360 143616, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (104532 : ℤ) ∧
    (∑ n ∈ Ico 143360 143616, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (2090742824325759410985670712 : ℤ) := by
  rcases cdemPrefixStats_143360_143488 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_143488_143616 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 143360 ≤ 143488) (by norm_num : 143488 ≤ 143616), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 143360 ≤ 143488) (by norm_num : 143488 ≤ 143616), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 143360 ≤ 143488) (by norm_num : 143488 ≤ 143616), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 143360 ≤ 143488) (by norm_num : 143488 ≤ 143616), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_143616_143680 :
    (∑ n ∈ Ico 143616 143680, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 143616 143680, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (35 : ℕ) ∧
    (∑ n ∈ Ico 143616 143680, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-34774 : ℤ) ∧
    (∑ n ∈ Ico 143616 143680, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-695472630718934679292953660 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_143680_143744 :
    (∑ n ∈ Ico 143680 143744, mobiusTreeValue 16 mobiusTable1200001 n) = (-2 : ℤ) ∧
    (∑ n ∈ Ico 143680 143744, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 143680 143744, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-69596 : ℤ) ∧
    (∑ n ∈ Ico 143680 143744, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-1391962795010879047234851036 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_143616_143744 :
    (∑ n ∈ Ico 143616 143744, mobiusTreeValue 16 mobiusTable1200001 n) = (-3 : ℤ) ∧
    (∑ n ∈ Ico 143616 143744, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (75 : ℕ) ∧
    (∑ n ∈ Ico 143616 143744, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-104370 : ℤ) ∧
    (∑ n ∈ Ico 143616 143744, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-2087435425729813726527804696 : ℤ) := by
  rcases cdemPrefixStats_143616_143680 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_143680_143744 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 143616 ≤ 143680) (by norm_num : 143680 ≤ 143744), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 143616 ≤ 143680) (by norm_num : 143680 ≤ 143744), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 143616 ≤ 143680) (by norm_num : 143680 ≤ 143744), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 143616 ≤ 143680) (by norm_num : 143680 ≤ 143744), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_143744_143808 :
    (∑ n ∈ Ico 143744 143808, mobiusTreeValue 16 mobiusTable1200001 n) = (9 : ℤ) ∧
    (∑ n ∈ Ico 143744 143808, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 143744 143808, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (313021 : ℤ) ∧
    (∑ n ∈ Ico 143744 143808, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (6260579114213428342604561017 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_143808_143872 :
    (∑ n ∈ Ico 143808 143872, mobiusTreeValue 16 mobiusTable1200001 n) = (6 : ℤ) ∧
    (∑ n ∈ Ico 143808 143872, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 143808 143872, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (208563 : ℤ) ∧
    (∑ n ∈ Ico 143808 143872, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (4171262847009537421364156091 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_143744_143872 :
    (∑ n ∈ Ico 143744 143872, mobiusTreeValue 16 mobiusTable1200001 n) = (15 : ℤ) ∧
    (∑ n ∈ Ico 143744 143872, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (79 : ℕ) ∧
    (∑ n ∈ Ico 143744 143872, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (521584 : ℤ) ∧
    (∑ n ∈ Ico 143744 143872, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (10431841961222965763968717108 : ℤ) := by
  rcases cdemPrefixStats_143744_143808 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_143808_143872 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 143744 ≤ 143808) (by norm_num : 143808 ≤ 143872), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 143744 ≤ 143808) (by norm_num : 143808 ≤ 143872), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 143744 ≤ 143808) (by norm_num : 143808 ≤ 143872), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 143744 ≤ 143808) (by norm_num : 143808 ≤ 143872), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_143616_143872 :
    (∑ n ∈ Ico 143616 143872, mobiusTreeValue 16 mobiusTable1200001 n) = (12 : ℤ) ∧
    (∑ n ∈ Ico 143616 143872, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (154 : ℕ) ∧
    (∑ n ∈ Ico 143616 143872, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (417214 : ℤ) ∧
    (∑ n ∈ Ico 143616 143872, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (8344406535493152037440912412 : ℤ) := by
  rcases cdemPrefixStats_143616_143744 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_143744_143872 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 143616 ≤ 143744) (by norm_num : 143744 ≤ 143872), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 143616 ≤ 143744) (by norm_num : 143744 ≤ 143872), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 143616 ≤ 143744) (by norm_num : 143744 ≤ 143872), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 143616 ≤ 143744) (by norm_num : 143744 ≤ 143872), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_143360_143872 :
    (∑ n ∈ Ico 143360 143872, mobiusTreeValue 16 mobiusTable1200001 n) = (15 : ℤ) ∧
    (∑ n ∈ Ico 143360 143872, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (309 : ℕ) ∧
    (∑ n ∈ Ico 143360 143872, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (521746 : ℤ) ∧
    (∑ n ∈ Ico 143360 143872, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (10435149359818911448426583124 : ℤ) := by
  rcases cdemPrefixStats_143360_143616 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_143616_143872 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 143360 ≤ 143616) (by norm_num : 143616 ≤ 143872), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 143360 ≤ 143616) (by norm_num : 143616 ≤ 143872), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 143360 ≤ 143616) (by norm_num : 143616 ≤ 143872), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 143360 ≤ 143616) (by norm_num : 143616 ≤ 143872), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_143872_143936 :
    (∑ n ∈ Ico 143872 143936, mobiusTreeValue 16 mobiusTable1200001 n) = (5 : ℤ) ∧
    (∑ n ∈ Ico 143872 143936, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 143872 143936, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (173699 : ℤ) ∧
    (∑ n ∈ Ico 143872 143936, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (3473988063879575210699490683 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_143936_144000 :
    (∑ n ∈ Ico 143936 144000, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 143936 144000, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 143936 144000, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (4 : ℤ) ∧
    (∑ n ∈ Ico 143936 144000, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (111028960015582050804164 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_143872_144000 :
    (∑ n ∈ Ico 143872 144000, mobiusTreeValue 16 mobiusTable1200001 n) = (5 : ℤ) ∧
    (∑ n ∈ Ico 143872 144000, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 143872 144000, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (173703 : ℤ) ∧
    (∑ n ∈ Ico 143872 144000, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (3474099092839590792750294847 : ℤ) := by
  rcases cdemPrefixStats_143872_143936 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_143936_144000 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 143872 ≤ 143936) (by norm_num : 143936 ≤ 144000), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 143872 ≤ 143936) (by norm_num : 143936 ≤ 144000), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 143872 ≤ 143936) (by norm_num : 143936 ≤ 144000), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 143872 ≤ 143936) (by norm_num : 143936 ≤ 144000), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_144000_144064 :
    (∑ n ∈ Ico 144000 144064, mobiusTreeValue 16 mobiusTable1200001 n) = (-4 : ℤ) ∧
    (∑ n ∈ Ico 144000 144064, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 144000 144064, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-138891 : ℤ) ∧
    (∑ n ∈ Ico 144000 144064, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-2777811477616744276772493006 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_144064_144128 :
    (∑ n ∈ Ico 144064 144128, mobiusTreeValue 16 mobiusTable1200001 n) = (11 : ℤ) ∧
    (∑ n ∈ Ico 144064 144128, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 144064 144128, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (381682 : ℤ) ∧
    (∑ n ∈ Ico 144064 144128, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (7633766064479195908408921002 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_144000_144128 :
    (∑ n ∈ Ico 144000 144128, mobiusTreeValue 16 mobiusTable1200001 n) = (7 : ℤ) ∧
    (∑ n ∈ Ico 144000 144128, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 144000 144128, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (242791 : ℤ) ∧
    (∑ n ∈ Ico 144000 144128, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (4855954586862451631636427996 : ℤ) := by
  rcases cdemPrefixStats_144000_144064 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_144064_144128 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 144000 ≤ 144064) (by norm_num : 144064 ≤ 144128), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 144000 ≤ 144064) (by norm_num : 144064 ≤ 144128), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 144000 ≤ 144064) (by norm_num : 144064 ≤ 144128), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 144000 ≤ 144064) (by norm_num : 144064 ≤ 144128), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_143872_144128 :
    (∑ n ∈ Ico 143872 144128, mobiusTreeValue 16 mobiusTable1200001 n) = (12 : ℤ) ∧
    (∑ n ∈ Ico 143872 144128, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (154 : ℕ) ∧
    (∑ n ∈ Ico 143872 144128, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (416494 : ℤ) ∧
    (∑ n ∈ Ico 143872 144128, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (8330053679702042424386722843 : ℤ) := by
  rcases cdemPrefixStats_143872_144000 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_144000_144128 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 143872 ≤ 144000) (by norm_num : 144000 ≤ 144128), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 143872 ≤ 144000) (by norm_num : 144000 ≤ 144128), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 143872 ≤ 144000) (by norm_num : 144000 ≤ 144128), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 143872 ≤ 144000) (by norm_num : 144000 ≤ 144128), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_144128_144192 :
    (∑ n ∈ Ico 144128 144192, mobiusTreeValue 16 mobiusTable1200001 n) = (-5 : ℤ) ∧
    (∑ n ∈ Ico 144128 144192, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 144128 144192, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-173462 : ℤ) ∧
    (∑ n ∈ Ico 144128 144192, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-3469311622596661872630478431 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_144192_144256 :
    (∑ n ∈ Ico 144192 144256, mobiusTreeValue 16 mobiusTable1200001 n) = (2 : ℤ) ∧
    (∑ n ∈ Ico 144192 144256, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 144192 144256, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (69343 : ℤ) ∧
    (∑ n ∈ Ico 144192 144256, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1386866389087549261210247215 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_144128_144256 :
    (∑ n ∈ Ico 144128 144256, mobiusTreeValue 16 mobiusTable1200001 n) = (-3 : ℤ) ∧
    (∑ n ∈ Ico 144128 144256, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (79 : ℕ) ∧
    (∑ n ∈ Ico 144128 144256, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-104119 : ℤ) ∧
    (∑ n ∈ Ico 144128 144256, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-2082445233509112611420231216 : ℤ) := by
  rcases cdemPrefixStats_144128_144192 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_144192_144256 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 144128 ≤ 144192) (by norm_num : 144192 ≤ 144256), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 144128 ≤ 144192) (by norm_num : 144192 ≤ 144256), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 144128 ≤ 144192) (by norm_num : 144192 ≤ 144256), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 144128 ≤ 144192) (by norm_num : 144192 ≤ 144256), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_144256_144320 :
    (∑ n ∈ Ico 144256 144320, mobiusTreeValue 16 mobiusTable1200001 n) = (-6 : ℤ) ∧
    (∑ n ∈ Ico 144256 144320, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 144256 144320, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-207893 : ℤ) ∧
    (∑ n ∈ Ico 144256 144320, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-4157937024346497785323252853 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_144320_144384 :
    (∑ n ∈ Ico 144320 144384, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 144320 144384, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 144320 144384, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-34634 : ℤ) ∧
    (∑ n ∈ Ico 144320 144384, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-692587909142554882496187391 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_144256_144384 :
    (∑ n ∈ Ico 144256 144384, mobiusTreeValue 16 mobiusTable1200001 n) = (-7 : ℤ) ∧
    (∑ n ∈ Ico 144256 144384, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 144256 144384, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-242527 : ℤ) ∧
    (∑ n ∈ Ico 144256 144384, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-4850524933489052667819440244 : ℤ) := by
  rcases cdemPrefixStats_144256_144320 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_144320_144384 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 144256 ≤ 144320) (by norm_num : 144320 ≤ 144384), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 144256 ≤ 144320) (by norm_num : 144320 ≤ 144384), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 144256 ≤ 144320) (by norm_num : 144320 ≤ 144384), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 144256 ≤ 144320) (by norm_num : 144320 ≤ 144384), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_144128_144384 :
    (∑ n ∈ Ico 144128 144384, mobiusTreeValue 16 mobiusTable1200001 n) = (-10 : ℤ) ∧
    (∑ n ∈ Ico 144128 144384, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (156 : ℕ) ∧
    (∑ n ∈ Ico 144128 144384, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-346646 : ℤ) ∧
    (∑ n ∈ Ico 144128 144384, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-6932970166998165279239671460 : ℤ) := by
  rcases cdemPrefixStats_144128_144256 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_144256_144384 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 144128 ≤ 144256) (by norm_num : 144256 ≤ 144384), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 144128 ≤ 144256) (by norm_num : 144256 ≤ 144384), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 144128 ≤ 144256) (by norm_num : 144256 ≤ 144384), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 144128 ≤ 144256) (by norm_num : 144256 ≤ 144384), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_143872_144384 :
    (∑ n ∈ Ico 143872 144384, mobiusTreeValue 16 mobiusTable1200001 n) = (2 : ℤ) ∧
    (∑ n ∈ Ico 143872 144384, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (310 : ℕ) ∧
    (∑ n ∈ Ico 143872 144384, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (69848 : ℤ) ∧
    (∑ n ∈ Ico 143872 144384, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1397083512703877145147051383 : ℤ) := by
  rcases cdemPrefixStats_143872_144128 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_144128_144384 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 143872 ≤ 144128) (by norm_num : 144128 ≤ 144384), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 143872 ≤ 144128) (by norm_num : 144128 ≤ 144384), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 143872 ≤ 144128) (by norm_num : 144128 ≤ 144384), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 143872 ≤ 144128) (by norm_num : 144128 ≤ 144384), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_143360_144384 :
    (∑ n ∈ Ico 143360 144384, mobiusTreeValue 16 mobiusTable1200001 n) = (17 : ℤ) ∧
    (∑ n ∈ Ico 143360 144384, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (619 : ℕ) ∧
    (∑ n ∈ Ico 143360 144384, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (591594 : ℤ) ∧
    (∑ n ∈ Ico 143360 144384, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (11832232872522788593573634507 : ℤ) := by
  rcases cdemPrefixStats_143360_143872 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_143872_144384 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 143360 ≤ 143872) (by norm_num : 143872 ≤ 144384), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 143360 ≤ 143872) (by norm_num : 143872 ≤ 144384), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 143360 ≤ 143872) (by norm_num : 143872 ≤ 144384), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 143360 ≤ 143872) (by norm_num : 143872 ≤ 144384), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_144384_144448 :
    (∑ n ∈ Ico 144384 144448, mobiusTreeValue 16 mobiusTable1200001 n) = (-8 : ℤ) ∧
    (∑ n ∈ Ico 144384 144448, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 144384 144448, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-276927 : ℤ) ∧
    (∑ n ∈ Ico 144384 144448, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-5538665425710076269627349593 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_144448_144512 :
    (∑ n ∈ Ico 144448 144512, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 144448 144512, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 144448 144512, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-32 : ℤ) ∧
    (∑ n ∈ Ico 144448 144512, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-646735121050980628267326 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_144384_144512 :
    (∑ n ∈ Ico 144384 144512, mobiusTreeValue 16 mobiusTable1200001 n) = (-8 : ℤ) ∧
    (∑ n ∈ Ico 144384 144512, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (80 : ℕ) ∧
    (∑ n ∈ Ico 144384 144512, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-276959 : ℤ) ∧
    (∑ n ∈ Ico 144384 144512, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-5539312160831127250255616919 : ℤ) := by
  rcases cdemPrefixStats_144384_144448 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_144448_144512 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 144384 ≤ 144448) (by norm_num : 144448 ≤ 144512), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 144384 ≤ 144448) (by norm_num : 144448 ≤ 144512), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 144384 ≤ 144448) (by norm_num : 144448 ≤ 144512), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 144384 ≤ 144448) (by norm_num : 144448 ≤ 144512), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_144512_144576 :
    (∑ n ∈ Ico 144512 144576, mobiusTreeValue 16 mobiusTable1200001 n) = (-2 : ℤ) ∧
    (∑ n ∈ Ico 144512 144576, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 144512 144576, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-69183 : ℤ) ∧
    (∑ n ∈ Ico 144512 144576, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-1383709659026653347959573869 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_144576_144640 :
    (∑ n ∈ Ico 144576 144640, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 144576 144640, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 144576 144640, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (34580 : ℤ) ∧
    (∑ n ∈ Ico 144576 144640, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (691634695365400022249039405 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_144512_144640 :
    (∑ n ∈ Ico 144512 144640, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 144512 144640, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 144512 144640, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-34603 : ℤ) ∧
    (∑ n ∈ Ico 144512 144640, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-692074963661253325710534464 : ℤ) := by
  rcases cdemPrefixStats_144512_144576 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_144576_144640 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 144512 ≤ 144576) (by norm_num : 144576 ≤ 144640), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 144512 ≤ 144576) (by norm_num : 144576 ≤ 144640), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 144512 ≤ 144576) (by norm_num : 144576 ≤ 144640), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 144512 ≤ 144576) (by norm_num : 144576 ≤ 144640), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_144384_144640 :
    (∑ n ∈ Ico 144384 144640, mobiusTreeValue 16 mobiusTable1200001 n) = (-9 : ℤ) ∧
    (∑ n ∈ Ico 144384 144640, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (157 : ℕ) ∧
    (∑ n ∈ Ico 144384 144640, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-311562 : ℤ) ∧
    (∑ n ∈ Ico 144384 144640, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-6231387124492380575966151383 : ℤ) := by
  rcases cdemPrefixStats_144384_144512 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_144512_144640 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 144384 ≤ 144512) (by norm_num : 144512 ≤ 144640), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 144384 ≤ 144512) (by norm_num : 144512 ≤ 144640), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 144384 ≤ 144512) (by norm_num : 144512 ≤ 144640), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 144384 ≤ 144512) (by norm_num : 144512 ≤ 144640), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_144640_144704 :
    (∑ n ∈ Ico 144640 144704, mobiusTreeValue 16 mobiusTable1200001 n) = (-12 : ℤ) ∧
    (∑ n ∈ Ico 144640 144704, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 144640 144704, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-414732 : ℤ) ∧
    (∑ n ∈ Ico 144640 144704, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-8294735114502029297852052088 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_144704_144768 :
    (∑ n ∈ Ico 144704 144768, mobiusTreeValue 16 mobiusTable1200001 n) = (8 : ℤ) ∧
    (∑ n ∈ Ico 144704 144768, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 144704 144768, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (276363 : ℤ) ∧
    (∑ n ∈ Ico 144704 144768, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (5527314586992556554910362798 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_144640_144768 :
    (∑ n ∈ Ico 144640 144768, mobiusTreeValue 16 mobiusTable1200001 n) = (-4 : ℤ) ∧
    (∑ n ∈ Ico 144640 144768, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 144640 144768, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-138369 : ℤ) ∧
    (∑ n ∈ Ico 144640 144768, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-2767420527509472742941689290 : ℤ) := by
  rcases cdemPrefixStats_144640_144704 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_144704_144768 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 144640 ≤ 144704) (by norm_num : 144704 ≤ 144768), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 144640 ≤ 144704) (by norm_num : 144704 ≤ 144768), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 144640 ≤ 144704) (by norm_num : 144704 ≤ 144768), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 144640 ≤ 144704) (by norm_num : 144704 ≤ 144768), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_144768_144832 :
    (∑ n ∈ Ico 144768 144832, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 144768 144832, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 144768 144832, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (34544 : ℤ) ∧
    (∑ n ∈ Ico 144768 144832, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (690831941921326492260412642 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_144832_144896 :
    (∑ n ∈ Ico 144832 144896, mobiusTreeValue 16 mobiusTable1200001 n) = (-2 : ℤ) ∧
    (∑ n ∈ Ico 144832 144896, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 144832 144896, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-69012 : ℤ) ∧
    (∑ n ∈ Ico 144832 144896, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-1380295568881037847766277648 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_144768_144896 :
    (∑ n ∈ Ico 144768 144896, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 144768 144896, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 144768 144896, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-34468 : ℤ) ∧
    (∑ n ∈ Ico 144768 144896, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-689463626959711355505865006 : ℤ) := by
  rcases cdemPrefixStats_144768_144832 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_144832_144896 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 144768 ≤ 144832) (by norm_num : 144832 ≤ 144896), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 144768 ≤ 144832) (by norm_num : 144832 ≤ 144896), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 144768 ≤ 144832) (by norm_num : 144832 ≤ 144896), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 144768 ≤ 144832) (by norm_num : 144832 ≤ 144896), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_144640_144896 :
    (∑ n ∈ Ico 144640 144896, mobiusTreeValue 16 mobiusTable1200001 n) = (-5 : ℤ) ∧
    (∑ n ∈ Ico 144640 144896, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (155 : ℕ) ∧
    (∑ n ∈ Ico 144640 144896, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-172837 : ℤ) ∧
    (∑ n ∈ Ico 144640 144896, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-3456884154469184098447554296 : ℤ) := by
  rcases cdemPrefixStats_144640_144768 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_144768_144896 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 144640 ≤ 144768) (by norm_num : 144768 ≤ 144896), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 144640 ≤ 144768) (by norm_num : 144768 ≤ 144896), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 144640 ≤ 144768) (by norm_num : 144768 ≤ 144896), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 144640 ≤ 144768) (by norm_num : 144768 ≤ 144896), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_144384_144896 :
    (∑ n ∈ Ico 144384 144896, mobiusTreeValue 16 mobiusTable1200001 n) = (-14 : ℤ) ∧
    (∑ n ∈ Ico 144384 144896, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (312 : ℕ) ∧
    (∑ n ∈ Ico 144384 144896, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-484399 : ℤ) ∧
    (∑ n ∈ Ico 144384 144896, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-9688271278961564674413705679 : ℤ) := by
  rcases cdemPrefixStats_144384_144640 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_144640_144896 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 144384 ≤ 144640) (by norm_num : 144640 ≤ 144896), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 144384 ≤ 144640) (by norm_num : 144640 ≤ 144896), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 144384 ≤ 144640) (by norm_num : 144640 ≤ 144896), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 144384 ≤ 144640) (by norm_num : 144640 ≤ 144896), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_144896_144960 :
    (∑ n ∈ Ico 144896 144960, mobiusTreeValue 16 mobiusTable1200001 n) = (4 : ℤ) ∧
    (∑ n ∈ Ico 144896 144960, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 144896 144960, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (137956 : ℤ) ∧
    (∑ n ∈ Ico 144896 144960, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (2759115078988071270024629866 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_144960_145024 :
    (∑ n ∈ Ico 144960 145024, mobiusTreeValue 16 mobiusTable1200001 n) = (-2 : ℤ) ∧
    (∑ n ∈ Ico 144960 145024, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 144960 145024, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-68992 : ℤ) ∧
    (∑ n ∈ Ico 144960 145024, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-1379871657104699978820994854 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_144896_145024 :
    (∑ n ∈ Ico 144896 145024, mobiusTreeValue 16 mobiusTable1200001 n) = (2 : ℤ) ∧
    (∑ n ∈ Ico 144896 145024, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 144896 145024, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (68964 : ℤ) ∧
    (∑ n ∈ Ico 144896 145024, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1379243421883371291203635012 : ℤ) := by
  rcases cdemPrefixStats_144896_144960 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_144960_145024 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 144896 ≤ 144960) (by norm_num : 144960 ≤ 145024), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 144896 ≤ 144960) (by norm_num : 144960 ≤ 145024), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 144896 ≤ 144960) (by norm_num : 144960 ≤ 145024), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 144896 ≤ 144960) (by norm_num : 144960 ≤ 145024), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_145024_145088 :
    (∑ n ∈ Ico 145024 145088, mobiusTreeValue 16 mobiusTable1200001 n) = (4 : ℤ) ∧
    (∑ n ∈ Ico 145024 145088, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 145024 145088, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (137835 : ℤ) ∧
    (∑ n ∈ Ico 145024 145088, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (2756728701857033136671096649 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_145088_145152 :
    (∑ n ∈ Ico 145088 145152, mobiusTreeValue 16 mobiusTable1200001 n) = (6 : ℤ) ∧
    (∑ n ∈ Ico 145088 145152, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (36 : ℕ) ∧
    (∑ n ∈ Ico 145088 145152, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (206731 : ℤ) ∧
    (∑ n ∈ Ico 145088 145152, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (4134718451964306350032732562 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_145024_145152 :
    (∑ n ∈ Ico 145024 145152, mobiusTreeValue 16 mobiusTable1200001 n) = (10 : ℤ) ∧
    (∑ n ∈ Ico 145024 145152, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (74 : ℕ) ∧
    (∑ n ∈ Ico 145024 145152, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (344566 : ℤ) ∧
    (∑ n ∈ Ico 145024 145152, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (6891447153821339486703829211 : ℤ) := by
  rcases cdemPrefixStats_145024_145088 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_145088_145152 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 145024 ≤ 145088) (by norm_num : 145088 ≤ 145152), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 145024 ≤ 145088) (by norm_num : 145088 ≤ 145152), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 145024 ≤ 145088) (by norm_num : 145088 ≤ 145152), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 145024 ≤ 145088) (by norm_num : 145088 ≤ 145152), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_144896_145152 :
    (∑ n ∈ Ico 144896 145152, mobiusTreeValue 16 mobiusTable1200001 n) = (12 : ℤ) ∧
    (∑ n ∈ Ico 144896 145152, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (152 : ℕ) ∧
    (∑ n ∈ Ico 144896 145152, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (413530 : ℤ) ∧
    (∑ n ∈ Ico 144896 145152, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (8270690575704710777907464223 : ℤ) := by
  rcases cdemPrefixStats_144896_145024 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_145024_145152 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 144896 ≤ 145024) (by norm_num : 145024 ≤ 145152), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 144896 ≤ 145024) (by norm_num : 145024 ≤ 145152), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 144896 ≤ 145024) (by norm_num : 145024 ≤ 145152), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 144896 ≤ 145024) (by norm_num : 145024 ≤ 145152), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_145152_145216 :
    (∑ n ∈ Ico 145152 145216, mobiusTreeValue 16 mobiusTable1200001 n) = (-9 : ℤ) ∧
    (∑ n ∈ Ico 145152 145216, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 145152 145216, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-309878 : ℤ) ∧
    (∑ n ∈ Ico 145152 145216, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-6197716122058371579312903992 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_145216_145280 :
    (∑ n ∈ Ico 145216 145280, mobiusTreeValue 16 mobiusTable1200001 n) = (8 : ℤ) ∧
    (∑ n ∈ Ico 145216 145280, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 145216 145280, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (275413 : ℤ) ∧
    (∑ n ∈ Ico 145216 145280, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (5508318852311868145526075967 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_145152_145280 :
    (∑ n ∈ Ico 145152 145280, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 145152 145280, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (79 : ℕ) ∧
    (∑ n ∈ Ico 145152 145280, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-34465 : ℤ) ∧
    (∑ n ∈ Ico 145152 145280, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-689397269746503433786828025 : ℤ) := by
  rcases cdemPrefixStats_145152_145216 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_145216_145280 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 145152 ≤ 145216) (by norm_num : 145216 ≤ 145280), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 145152 ≤ 145216) (by norm_num : 145216 ≤ 145280), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 145152 ≤ 145216) (by norm_num : 145216 ≤ 145280), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 145152 ≤ 145216) (by norm_num : 145216 ≤ 145280), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_145280_145344 :
    (∑ n ∈ Ico 145280 145344, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 145280 145344, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 145280 145344, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-34404 : ℤ) ∧
    (∑ n ∈ Ico 145280 145344, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-688131924109207330976451663 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_145344_145408 :
    (∑ n ∈ Ico 145344 145408, mobiusTreeValue 16 mobiusTable1200001 n) = (-2 : ℤ) ∧
    (∑ n ∈ Ico 145344 145408, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 145344 145408, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-68790 : ℤ) ∧
    (∑ n ∈ Ico 145344 145408, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-1375818605108648089240076159 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_145280_145408 :
    (∑ n ∈ Ico 145280 145408, mobiusTreeValue 16 mobiusTable1200001 n) = (-3 : ℤ) ∧
    (∑ n ∈ Ico 145280 145408, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (79 : ℕ) ∧
    (∑ n ∈ Ico 145280 145408, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-103194 : ℤ) ∧
    (∑ n ∈ Ico 145280 145408, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-2063950529217855420216527822 : ℤ) := by
  rcases cdemPrefixStats_145280_145344 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_145344_145408 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 145280 ≤ 145344) (by norm_num : 145344 ≤ 145408), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 145280 ≤ 145344) (by norm_num : 145344 ≤ 145408), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 145280 ≤ 145344) (by norm_num : 145344 ≤ 145408), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 145280 ≤ 145344) (by norm_num : 145344 ≤ 145408), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_145152_145408 :
    (∑ n ∈ Ico 145152 145408, mobiusTreeValue 16 mobiusTable1200001 n) = (-4 : ℤ) ∧
    (∑ n ∈ Ico 145152 145408, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (158 : ℕ) ∧
    (∑ n ∈ Ico 145152 145408, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-137659 : ℤ) ∧
    (∑ n ∈ Ico 145152 145408, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-2753347798964358854003355847 : ℤ) := by
  rcases cdemPrefixStats_145152_145280 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_145280_145408 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 145152 ≤ 145280) (by norm_num : 145280 ≤ 145408), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 145152 ≤ 145280) (by norm_num : 145280 ≤ 145408), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 145152 ≤ 145280) (by norm_num : 145280 ≤ 145408), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 145152 ≤ 145280) (by norm_num : 145280 ≤ 145408), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_144896_145408 :
    (∑ n ∈ Ico 144896 145408, mobiusTreeValue 16 mobiusTable1200001 n) = (8 : ℤ) ∧
    (∑ n ∈ Ico 144896 145408, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (310 : ℕ) ∧
    (∑ n ∈ Ico 144896 145408, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (275871 : ℤ) ∧
    (∑ n ∈ Ico 144896 145408, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (5517342776740351923904108376 : ℤ) := by
  rcases cdemPrefixStats_144896_145152 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_145152_145408 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 144896 ≤ 145152) (by norm_num : 145152 ≤ 145408), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 144896 ≤ 145152) (by norm_num : 145152 ≤ 145408), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 144896 ≤ 145152) (by norm_num : 145152 ≤ 145408), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 144896 ≤ 145152) (by norm_num : 145152 ≤ 145408), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_144384_145408 :
    (∑ n ∈ Ico 144384 145408, mobiusTreeValue 16 mobiusTable1200001 n) = (-6 : ℤ) ∧
    (∑ n ∈ Ico 144384 145408, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (622 : ℕ) ∧
    (∑ n ∈ Ico 144384 145408, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-208528 : ℤ) ∧
    (∑ n ∈ Ico 144384 145408, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-4170928502221212750509597303 : ℤ) := by
  rcases cdemPrefixStats_144384_144896 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_144896_145408 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 144384 ≤ 144896) (by norm_num : 144896 ≤ 145408), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 144384 ≤ 144896) (by norm_num : 144896 ≤ 145408), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 144384 ≤ 144896) (by norm_num : 144896 ≤ 145408), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 144384 ≤ 144896) (by norm_num : 144896 ≤ 145408), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_143360_145408 :
    (∑ n ∈ Ico 143360 145408, mobiusTreeValue 16 mobiusTable1200001 n) = (11 : ℤ) ∧
    (∑ n ∈ Ico 143360 145408, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (1241 : ℕ) ∧
    (∑ n ∈ Ico 143360 145408, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (383066 : ℤ) ∧
    (∑ n ∈ Ico 143360 145408, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (7661304370301575843064037204 : ℤ) := by
  rcases cdemPrefixStats_143360_144384 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_144384_145408 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 143360 ≤ 144384) (by norm_num : 144384 ≤ 145408), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 143360 ≤ 144384) (by norm_num : 144384 ≤ 145408), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 143360 ≤ 144384) (by norm_num : 144384 ≤ 145408), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 143360 ≤ 144384) (by norm_num : 144384 ≤ 145408), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_145408_145472 :
    (∑ n ∈ Ico 145408 145472, mobiusTreeValue 16 mobiusTable1200001 n) = (-5 : ℤ) ∧
    (∑ n ∈ Ico 145408 145472, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 145408 145472, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-171843 : ℤ) ∧
    (∑ n ∈ Ico 145408 145472, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-3436912573620965907605955766 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_145472_145536 :
    (∑ n ∈ Ico 145472 145536, mobiusTreeValue 16 mobiusTable1200001 n) = (-3 : ℤ) ∧
    (∑ n ∈ Ico 145472 145536, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 145472 145536, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-103098 : ℤ) ∧
    (∑ n ∈ Ico 145472 145536, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-2062039920328510516032923517 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_145408_145536 :
    (∑ n ∈ Ico 145408 145536, mobiusTreeValue 16 mobiusTable1200001 n) = (-8 : ℤ) ∧
    (∑ n ∈ Ico 145408 145536, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (76 : ℕ) ∧
    (∑ n ∈ Ico 145408 145536, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-274941 : ℤ) ∧
    (∑ n ∈ Ico 145408 145536, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-5498952493949476423638879283 : ℤ) := by
  rcases cdemPrefixStats_145408_145472 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_145472_145536 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 145408 ≤ 145472) (by norm_num : 145472 ≤ 145536), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 145408 ≤ 145472) (by norm_num : 145472 ≤ 145536), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 145408 ≤ 145472) (by norm_num : 145472 ≤ 145536), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 145408 ≤ 145472) (by norm_num : 145472 ≤ 145536), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_145536_145600 :
    (∑ n ∈ Ico 145536 145600, mobiusTreeValue 16 mobiusTable1200001 n) = (-6 : ℤ) ∧
    (∑ n ∈ Ico 145536 145600, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 145536 145600, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-206081 : ℤ) ∧
    (∑ n ∈ Ico 145536 145600, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-4121653055209954157739958440 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_145600_145664 :
    (∑ n ∈ Ico 145600 145664, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 145600 145664, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 145600 145664, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (34330 : ℤ) ∧
    (∑ n ∈ Ico 145600 145664, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (686530249495494543420056535 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_145536_145664 :
    (∑ n ∈ Ico 145536 145664, mobiusTreeValue 16 mobiusTable1200001 n) = (-5 : ℤ) ∧
    (∑ n ∈ Ico 145536 145664, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (81 : ℕ) ∧
    (∑ n ∈ Ico 145536 145664, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-171751 : ℤ) ∧
    (∑ n ∈ Ico 145536 145664, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-3435122805714459614319901905 : ℤ) := by
  rcases cdemPrefixStats_145536_145600 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_145600_145664 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 145536 ≤ 145600) (by norm_num : 145600 ≤ 145664), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 145536 ≤ 145600) (by norm_num : 145600 ≤ 145664), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 145536 ≤ 145600) (by norm_num : 145600 ≤ 145664), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 145536 ≤ 145600) (by norm_num : 145600 ≤ 145664), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_145408_145664 :
    (∑ n ∈ Ico 145408 145664, mobiusTreeValue 16 mobiusTable1200001 n) = (-13 : ℤ) ∧
    (∑ n ∈ Ico 145408 145664, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (157 : ℕ) ∧
    (∑ n ∈ Ico 145408 145664, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-446692 : ℤ) ∧
    (∑ n ∈ Ico 145408 145664, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-8934075299663936037958781188 : ℤ) := by
  rcases cdemPrefixStats_145408_145536 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_145536_145664 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 145408 ≤ 145536) (by norm_num : 145536 ≤ 145664), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 145408 ≤ 145536) (by norm_num : 145536 ≤ 145664), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 145408 ≤ 145536) (by norm_num : 145536 ≤ 145664), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 145408 ≤ 145536) (by norm_num : 145536 ≤ 145664), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_145664_145728 :
    (∑ n ∈ Ico 145664 145728, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 145664 145728, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 145664 145728, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-34329 : ℤ) ∧
    (∑ n ∈ Ico 145664 145728, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-686534975282011975087334232 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_145728_145792 :
    (∑ n ∈ Ico 145728 145792, mobiusTreeValue 16 mobiusTable1200001 n) = (6 : ℤ) ∧
    (∑ n ∈ Ico 145728 145792, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 145728 145792, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (205818 : ℤ) ∧
    (∑ n ∈ Ico 145728 145792, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (4116445151731085548977878658 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_145664_145792 :
    (∑ n ∈ Ico 145664 145792, mobiusTreeValue 16 mobiusTable1200001 n) = (5 : ℤ) ∧
    (∑ n ∈ Ico 145664 145792, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 145664 145792, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (171489 : ℤ) ∧
    (∑ n ∈ Ico 145664 145792, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (3429910176449073573890544426 : ℤ) := by
  rcases cdemPrefixStats_145664_145728 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_145728_145792 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 145664 ≤ 145728) (by norm_num : 145728 ≤ 145792), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 145664 ≤ 145728) (by norm_num : 145728 ≤ 145792), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 145664 ≤ 145728) (by norm_num : 145728 ≤ 145792), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 145664 ≤ 145728) (by norm_num : 145728 ≤ 145792), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_145792_145856 :
    (∑ n ∈ Ico 145792 145856, mobiusTreeValue 16 mobiusTable1200001 n) = (2 : ℤ) ∧
    (∑ n ∈ Ico 145792 145856, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 145792 145856, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (68571 : ℤ) ∧
    (∑ n ∈ Ico 145792 145856, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1371431711803937475970047844 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_145856_145920 :
    (∑ n ∈ Ico 145856 145920, mobiusTreeValue 16 mobiusTable1200001 n) = (11 : ℤ) ∧
    (∑ n ∈ Ico 145856 145920, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 145856 145920, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (376976 : ℤ) ∧
    (∑ n ∈ Ico 145856 145920, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (7539598581142224078656125683 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_145792_145920 :
    (∑ n ∈ Ico 145792 145920, mobiusTreeValue 16 mobiusTable1200001 n) = (13 : ℤ) ∧
    (∑ n ∈ Ico 145792 145920, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (79 : ℕ) ∧
    (∑ n ∈ Ico 145792 145920, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (445547 : ℤ) ∧
    (∑ n ∈ Ico 145792 145920, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (8911030292946161554626173527 : ℤ) := by
  rcases cdemPrefixStats_145792_145856 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_145856_145920 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 145792 ≤ 145856) (by norm_num : 145856 ≤ 145920), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 145792 ≤ 145856) (by norm_num : 145856 ≤ 145920), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 145792 ≤ 145856) (by norm_num : 145856 ≤ 145920), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 145792 ≤ 145856) (by norm_num : 145856 ≤ 145920), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_145664_145920 :
    (∑ n ∈ Ico 145664 145920, mobiusTreeValue 16 mobiusTable1200001 n) = (18 : ℤ) ∧
    (∑ n ∈ Ico 145664 145920, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (156 : ℕ) ∧
    (∑ n ∈ Ico 145664 145920, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (617036 : ℤ) ∧
    (∑ n ∈ Ico 145664 145920, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (12340940469395235128516717953 : ℤ) := by
  rcases cdemPrefixStats_145664_145792 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_145792_145920 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 145664 ≤ 145792) (by norm_num : 145792 ≤ 145920), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 145664 ≤ 145792) (by norm_num : 145792 ≤ 145920), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 145664 ≤ 145792) (by norm_num : 145792 ≤ 145920), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 145664 ≤ 145792) (by norm_num : 145792 ≤ 145920), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_145408_145920 :
    (∑ n ∈ Ico 145408 145920, mobiusTreeValue 16 mobiusTable1200001 n) = (5 : ℤ) ∧
    (∑ n ∈ Ico 145408 145920, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (313 : ℕ) ∧
    (∑ n ∈ Ico 145408 145920, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (170344 : ℤ) ∧
    (∑ n ∈ Ico 145408 145920, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (3406865169731299090557936765 : ℤ) := by
  rcases cdemPrefixStats_145408_145664 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_145664_145920 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 145408 ≤ 145664) (by norm_num : 145664 ≤ 145920), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 145408 ≤ 145664) (by norm_num : 145664 ≤ 145920), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 145408 ≤ 145664) (by norm_num : 145664 ≤ 145920), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 145408 ≤ 145664) (by norm_num : 145664 ≤ 145920), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_145920_145984 :
    (∑ n ∈ Ico 145920 145984, mobiusTreeValue 16 mobiusTable1200001 n) = (-2 : ℤ) ∧
    (∑ n ∈ Ico 145920 145984, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 145920 145984, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-68503 : ℤ) ∧
    (∑ n ∈ Ico 145920 145984, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-1370041334216612245650001381 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_145984_146048 :
    (∑ n ∈ Ico 145984 146048, mobiusTreeValue 16 mobiusTable1200001 n) = (5 : ℤ) ∧
    (∑ n ∈ Ico 145984 146048, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 145984 146048, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (171190 : ℤ) ∧
    (∑ n ∈ Ico 145984 146048, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (3423836856436348286776140232 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_145920_146048 :
    (∑ n ∈ Ico 145920 146048, mobiusTreeValue 16 mobiusTable1200001 n) = (3 : ℤ) ∧
    (∑ n ∈ Ico 145920 146048, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (79 : ℕ) ∧
    (∑ n ∈ Ico 145920 146048, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (102687 : ℤ) ∧
    (∑ n ∈ Ico 145920 146048, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (2053795522219736041126138851 : ℤ) := by
  rcases cdemPrefixStats_145920_145984 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_145984_146048 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 145920 ≤ 145984) (by norm_num : 145984 ≤ 146048), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 145920 ≤ 145984) (by norm_num : 145984 ≤ 146048), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 145920 ≤ 145984) (by norm_num : 145984 ≤ 146048), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 145920 ≤ 145984) (by norm_num : 145984 ≤ 146048), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_146048_146112 :
    (∑ n ∈ Ico 146048 146112, mobiusTreeValue 16 mobiusTable1200001 n) = (-3 : ℤ) ∧
    (∑ n ∈ Ico 146048 146112, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 146048 146112, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-102744 : ℤ) ∧
    (∑ n ∈ Ico 146048 146112, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-2054887683632437178469805298 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_146112_146176 :
    (∑ n ∈ Ico 146112 146176, mobiusTreeValue 16 mobiusTable1200001 n) = (4 : ℤ) ∧
    (∑ n ∈ Ico 146112 146176, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 146112 146176, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (136818 : ℤ) ∧
    (∑ n ∈ Ico 146112 146176, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (2736441267235495180515406937 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_146048_146176 :
    (∑ n ∈ Ico 146048 146176, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 146048 146176, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 146048 146176, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (34074 : ℤ) ∧
    (∑ n ∈ Ico 146048 146176, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (681553583603058002045601639 : ℤ) := by
  rcases cdemPrefixStats_146048_146112 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_146112_146176 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 146048 ≤ 146112) (by norm_num : 146112 ≤ 146176), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 146048 ≤ 146112) (by norm_num : 146112 ≤ 146176), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 146048 ≤ 146112) (by norm_num : 146112 ≤ 146176), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 146048 ≤ 146112) (by norm_num : 146112 ≤ 146176), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_145920_146176 :
    (∑ n ∈ Ico 145920 146176, mobiusTreeValue 16 mobiusTable1200001 n) = (4 : ℤ) ∧
    (∑ n ∈ Ico 145920 146176, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (156 : ℕ) ∧
    (∑ n ∈ Ico 145920 146176, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (136761 : ℤ) ∧
    (∑ n ∈ Ico 145920 146176, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (2735349105822794043171740490 : ℤ) := by
  rcases cdemPrefixStats_145920_146048 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_146048_146176 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 145920 ≤ 146048) (by norm_num : 146048 ≤ 146176), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 145920 ≤ 146048) (by norm_num : 146048 ≤ 146176), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 145920 ≤ 146048) (by norm_num : 146048 ≤ 146176), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 145920 ≤ 146048) (by norm_num : 146048 ≤ 146176), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_146176_146240 :
    (∑ n ∈ Ico 146176 146240, mobiusTreeValue 16 mobiusTable1200001 n) = (-8 : ℤ) ∧
    (∑ n ∈ Ico 146176 146240, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 146176 146240, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-273564 : ℤ) ∧
    (∑ n ∈ Ico 146176 146240, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-5471357549477198771217998309 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_146240_146304 :
    (∑ n ∈ Ico 146240 146304, mobiusTreeValue 16 mobiusTable1200001 n) = (8 : ℤ) ∧
    (∑ n ∈ Ico 146240 146304, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 146240 146304, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (273446 : ℤ) ∧
    (∑ n ∈ Ico 146240 146304, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (5468982340571896061595057757 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_146176_146304 :
    (∑ n ∈ Ico 146176 146304, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 146176 146304, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (76 : ℕ) ∧
    (∑ n ∈ Ico 146176 146304, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-118 : ℤ) ∧
    (∑ n ∈ Ico 146176 146304, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-2375208905302709622940552 : ℤ) := by
  rcases cdemPrefixStats_146176_146240 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_146240_146304 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 146176 ≤ 146240) (by norm_num : 146240 ≤ 146304), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 146176 ≤ 146240) (by norm_num : 146240 ≤ 146304), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 146176 ≤ 146240) (by norm_num : 146240 ≤ 146304), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 146176 ≤ 146240) (by norm_num : 146240 ≤ 146304), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_146304_146368 :
    (∑ n ∈ Ico 146304 146368, mobiusTreeValue 16 mobiusTable1200001 n) = (-4 : ℤ) ∧
    (∑ n ∈ Ico 146304 146368, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (36 : ℕ) ∧
    (∑ n ∈ Ico 146304 146368, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-136717 : ℤ) ∧
    (∑ n ∈ Ico 146304 146368, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-2734406826927133113968306106 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_146368_146432 :
    (∑ n ∈ Ico 146368 146432, mobiusTreeValue 16 mobiusTable1200001 n) = (-4 : ℤ) ∧
    (∑ n ∈ Ico 146368 146432, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 146368 146432, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-136640 : ℤ) ∧
    (∑ n ∈ Ico 146368 146432, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-2732823691252600674739285481 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_146304_146432 :
    (∑ n ∈ Ico 146304 146432, mobiusTreeValue 16 mobiusTable1200001 n) = (-8 : ℤ) ∧
    (∑ n ∈ Ico 146304 146432, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (76 : ℕ) ∧
    (∑ n ∈ Ico 146304 146432, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-273357 : ℤ) ∧
    (∑ n ∈ Ico 146304 146432, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-5467230518179733788707591587 : ℤ) := by
  rcases cdemPrefixStats_146304_146368 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_146368_146432 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 146304 ≤ 146368) (by norm_num : 146368 ≤ 146432), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 146304 ≤ 146368) (by norm_num : 146368 ≤ 146432), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 146304 ≤ 146368) (by norm_num : 146368 ≤ 146432), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 146304 ≤ 146368) (by norm_num : 146368 ≤ 146432), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_146176_146432 :
    (∑ n ∈ Ico 146176 146432, mobiusTreeValue 16 mobiusTable1200001 n) = (-8 : ℤ) ∧
    (∑ n ∈ Ico 146176 146432, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (152 : ℕ) ∧
    (∑ n ∈ Ico 146176 146432, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-273475 : ℤ) ∧
    (∑ n ∈ Ico 146176 146432, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-5469605727085036498330532139 : ℤ) := by
  rcases cdemPrefixStats_146176_146304 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_146304_146432 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 146176 ≤ 146304) (by norm_num : 146304 ≤ 146432), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 146176 ≤ 146304) (by norm_num : 146304 ≤ 146432), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 146176 ≤ 146304) (by norm_num : 146304 ≤ 146432), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 146176 ≤ 146304) (by norm_num : 146304 ≤ 146432), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_145920_146432 :
    (∑ n ∈ Ico 145920 146432, mobiusTreeValue 16 mobiusTable1200001 n) = (-4 : ℤ) ∧
    (∑ n ∈ Ico 145920 146432, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (308 : ℕ) ∧
    (∑ n ∈ Ico 145920 146432, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-136714 : ℤ) ∧
    (∑ n ∈ Ico 145920 146432, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-2734256621262242455158791649 : ℤ) := by
  rcases cdemPrefixStats_145920_146176 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_146176_146432 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 145920 ≤ 146176) (by norm_num : 146176 ≤ 146432), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 145920 ≤ 146176) (by norm_num : 146176 ≤ 146432), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 145920 ≤ 146176) (by norm_num : 146176 ≤ 146432), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 145920 ≤ 146176) (by norm_num : 146176 ≤ 146432), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_145408_146432 :
    (∑ n ∈ Ico 145408 146432, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 145408 146432, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (621 : ℕ) ∧
    (∑ n ∈ Ico 145408 146432, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (33630 : ℤ) ∧
    (∑ n ∈ Ico 145408 146432, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (672608548469056635399145116 : ℤ) := by
  rcases cdemPrefixStats_145408_145920 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_145920_146432 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 145408 ≤ 145920) (by norm_num : 145920 ≤ 146432), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 145408 ≤ 145920) (by norm_num : 145920 ≤ 146432), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 145408 ≤ 145920) (by norm_num : 145920 ≤ 146432), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 145408 ≤ 145920) (by norm_num : 145920 ≤ 146432), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_146432_146496 :
    (∑ n ∈ Ico 146432 146496, mobiusTreeValue 16 mobiusTable1200001 n) = (4 : ℤ) ∧
    (∑ n ∈ Ico 146432 146496, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 146432 146496, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (136573 : ℤ) ∧
    (∑ n ∈ Ico 146432 146496, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (2731559319138146954331995099 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_146496_146560 :
    (∑ n ∈ Ico 146496 146560, mobiusTreeValue 16 mobiusTable1200001 n) = (-12 : ℤ) ∧
    (∑ n ∈ Ico 146496 146560, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (36 : ℕ) ∧
    (∑ n ∈ Ico 146496 146560, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-409479 : ℤ) ∧
    (∑ n ∈ Ico 146496 146560, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-8189747415998275150383622433 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_146432_146560 :
    (∑ n ∈ Ico 146432 146560, mobiusTreeValue 16 mobiusTable1200001 n) = (-8 : ℤ) ∧
    (∑ n ∈ Ico 146432 146560, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (76 : ℕ) ∧
    (∑ n ∈ Ico 146432 146560, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-272906 : ℤ) ∧
    (∑ n ∈ Ico 146432 146560, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-5458188096860128196051627334 : ℤ) := by
  rcases cdemPrefixStats_146432_146496 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_146496_146560 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 146432 ≤ 146496) (by norm_num : 146496 ≤ 146560), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 146432 ≤ 146496) (by norm_num : 146496 ≤ 146560), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 146432 ≤ 146496) (by norm_num : 146496 ≤ 146560), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 146432 ≤ 146496) (by norm_num : 146496 ≤ 146560), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_146560_146624 :
    (∑ n ∈ Ico 146560 146624, mobiusTreeValue 16 mobiusTable1200001 n) = (14 : ℤ) ∧
    (∑ n ∈ Ico 146560 146624, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 146560 146624, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (477503 : ℤ) ∧
    (∑ n ∈ Ico 146560 146624, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (9550181766769557418781876979 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_146624_146688 :
    (∑ n ∈ Ico 146624 146688, mobiusTreeValue 16 mobiusTable1200001 n) = (-5 : ℤ) ∧
    (∑ n ∈ Ico 146624 146688, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 146624 146688, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-170443 : ℤ) ∧
    (∑ n ∈ Ico 146624 146688, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-3408892641321671239544277886 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_146560_146688 :
    (∑ n ∈ Ico 146560 146688, mobiusTreeValue 16 mobiusTable1200001 n) = (9 : ℤ) ∧
    (∑ n ∈ Ico 146560 146688, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (79 : ℕ) ∧
    (∑ n ∈ Ico 146560 146688, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (307060 : ℤ) ∧
    (∑ n ∈ Ico 146560 146688, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (6141289125447886179237599093 : ℤ) := by
  rcases cdemPrefixStats_146560_146624 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_146624_146688 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 146560 ≤ 146624) (by norm_num : 146624 ≤ 146688), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 146560 ≤ 146624) (by norm_num : 146624 ≤ 146688), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 146560 ≤ 146624) (by norm_num : 146624 ≤ 146688), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 146560 ≤ 146624) (by norm_num : 146624 ≤ 146688), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_146432_146688 :
    (∑ n ∈ Ico 146432 146688, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 146432 146688, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (155 : ℕ) ∧
    (∑ n ∈ Ico 146432 146688, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (34154 : ℤ) ∧
    (∑ n ∈ Ico 146432 146688, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (683101028587757983185971759 : ℤ) := by
  rcases cdemPrefixStats_146432_146560 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_146560_146688 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 146432 ≤ 146560) (by norm_num : 146560 ≤ 146688), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 146432 ≤ 146560) (by norm_num : 146560 ≤ 146688), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 146432 ≤ 146560) (by norm_num : 146560 ≤ 146688), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 146432 ≤ 146560) (by norm_num : 146560 ≤ 146688), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_146688_146752 :
    (∑ n ∈ Ico 146688 146752, mobiusTreeValue 16 mobiusTable1200001 n) = (7 : ℤ) ∧
    (∑ n ∈ Ico 146688 146752, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 146688 146752, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (238547 : ℤ) ∧
    (∑ n ∈ Ico 146688 146752, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (4770964469561874639051393498 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_146752_146816 :
    (∑ n ∈ Ico 146752 146816, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 146752 146816, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 146752 146816, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (49 : ℤ) ∧
    (∑ n ∈ Ico 146752 146816, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (993311877185521797383682 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_146688_146816 :
    (∑ n ∈ Ico 146688 146816, mobiusTreeValue 16 mobiusTable1200001 n) = (7 : ℤ) ∧
    (∑ n ∈ Ico 146688 146816, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (79 : ℕ) ∧
    (∑ n ∈ Ico 146688 146816, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (238596 : ℤ) ∧
    (∑ n ∈ Ico 146688 146816, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (4771957781439060160848777180 : ℤ) := by
  rcases cdemPrefixStats_146688_146752 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_146752_146816 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 146688 ≤ 146752) (by norm_num : 146752 ≤ 146816), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 146688 ≤ 146752) (by norm_num : 146752 ≤ 146816), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 146688 ≤ 146752) (by norm_num : 146752 ≤ 146816), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 146688 ≤ 146752) (by norm_num : 146752 ≤ 146816), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_146816_146880 :
    (∑ n ∈ Ico 146816 146880, mobiusTreeValue 16 mobiusTable1200001 n) = (-10 : ℤ) ∧
    (∑ n ∈ Ico 146816 146880, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 146816 146880, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-340529 : ℤ) ∧
    (∑ n ∈ Ico 146816 146880, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-6810703892578759021683952292 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_146880_146944 :
    (∑ n ∈ Ico 146880 146944, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 146880 146944, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 146880 146944, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (8 : ℤ) ∧
    (∑ n ∈ Ico 146880 146944, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (125050526199084033297585 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_146816_146944 :
    (∑ n ∈ Ico 146816 146944, mobiusTreeValue 16 mobiusTable1200001 n) = (-10 : ℤ) ∧
    (∑ n ∈ Ico 146816 146944, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (76 : ℕ) ∧
    (∑ n ∈ Ico 146816 146944, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-340521 : ℤ) ∧
    (∑ n ∈ Ico 146816 146944, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-6810578842052559937650654707 : ℤ) := by
  rcases cdemPrefixStats_146816_146880 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_146880_146944 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 146816 ≤ 146880) (by norm_num : 146880 ≤ 146944), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 146816 ≤ 146880) (by norm_num : 146880 ≤ 146944), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 146816 ≤ 146880) (by norm_num : 146880 ≤ 146944), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 146816 ≤ 146880) (by norm_num : 146880 ≤ 146944), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_146688_146944 :
    (∑ n ∈ Ico 146688 146944, mobiusTreeValue 16 mobiusTable1200001 n) = (-3 : ℤ) ∧
    (∑ n ∈ Ico 146688 146944, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (155 : ℕ) ∧
    (∑ n ∈ Ico 146688 146944, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-101925 : ℤ) ∧
    (∑ n ∈ Ico 146688 146944, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-2038621060613499776801877527 : ℤ) := by
  rcases cdemPrefixStats_146688_146816 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_146816_146944 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 146688 ≤ 146816) (by norm_num : 146816 ≤ 146944), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 146688 ≤ 146816) (by norm_num : 146816 ≤ 146944), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 146688 ≤ 146816) (by norm_num : 146816 ≤ 146944), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 146688 ≤ 146816) (by norm_num : 146816 ≤ 146944), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_146432_146944 :
    (∑ n ∈ Ico 146432 146944, mobiusTreeValue 16 mobiusTable1200001 n) = (-2 : ℤ) ∧
    (∑ n ∈ Ico 146432 146944, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (310 : ℕ) ∧
    (∑ n ∈ Ico 146432 146944, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-67771 : ℤ) ∧
    (∑ n ∈ Ico 146432 146944, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-1355520032025741793615905768 : ℤ) := by
  rcases cdemPrefixStats_146432_146688 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_146688_146944 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 146432 ≤ 146688) (by norm_num : 146688 ≤ 146944), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 146432 ≤ 146688) (by norm_num : 146688 ≤ 146944), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 146432 ≤ 146688) (by norm_num : 146688 ≤ 146944), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 146432 ≤ 146688) (by norm_num : 146688 ≤ 146944), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_146944_147008 :
    (∑ n ∈ Ico 146944 147008, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 146944 147008, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 146944 147008, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (62 : ℤ) ∧
    (∑ n ∈ Ico 146944 147008, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1162062004037749270785397 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_147008_147072 :
    (∑ n ∈ Ico 147008 147072, mobiusTreeValue 16 mobiusTable1200001 n) = (4 : ℤ) ∧
    (∑ n ∈ Ico 147008 147072, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 147008 147072, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (136024 : ℤ) ∧
    (∑ n ∈ Ico 147008 147072, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (2720496294513504086392518566 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_146944_147072 :
    (∑ n ∈ Ico 146944 147072, mobiusTreeValue 16 mobiusTable1200001 n) = (4 : ℤ) ∧
    (∑ n ∈ Ico 146944 147072, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 146944 147072, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (136086 : ℤ) ∧
    (∑ n ∈ Ico 146944 147072, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (2721658356517541835663303963 : ℤ) := by
  rcases cdemPrefixStats_146944_147008 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_147008_147072 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 146944 ≤ 147008) (by norm_num : 147008 ≤ 147072), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 146944 ≤ 147008) (by norm_num : 147008 ≤ 147072), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 146944 ≤ 147008) (by norm_num : 147008 ≤ 147072), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 146944 ≤ 147008) (by norm_num : 147008 ≤ 147072), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_147072_147136 :
    (∑ n ∈ Ico 147072 147136, mobiusTreeValue 16 mobiusTable1200001 n) = (7 : ℤ) ∧
    (∑ n ∈ Ico 147072 147136, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 147072 147136, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (237874 : ℤ) ∧
    (∑ n ∈ Ico 147072 147136, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (4757530780116249503818753792 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_147136_147200 :
    (∑ n ∈ Ico 147136 147200, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 147136 147200, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 147136 147200, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (33962 : ℤ) ∧
    (∑ n ∈ Ico 147136 147200, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (679278553565375498249258286 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_147072_147200 :
    (∑ n ∈ Ico 147072 147200, mobiusTreeValue 16 mobiusTable1200001 n) = (8 : ℤ) ∧
    (∑ n ∈ Ico 147072 147200, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 147072 147200, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (271836 : ℤ) ∧
    (∑ n ∈ Ico 147072 147200, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (5436809333681625002068012078 : ℤ) := by
  rcases cdemPrefixStats_147072_147136 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_147136_147200 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 147072 ≤ 147136) (by norm_num : 147136 ≤ 147200), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 147072 ≤ 147136) (by norm_num : 147136 ≤ 147200), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 147072 ≤ 147136) (by norm_num : 147136 ≤ 147200), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 147072 ≤ 147136) (by norm_num : 147136 ≤ 147200), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_146944_147200 :
    (∑ n ∈ Ico 146944 147200, mobiusTreeValue 16 mobiusTable1200001 n) = (12 : ℤ) ∧
    (∑ n ∈ Ico 146944 147200, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (156 : ℕ) ∧
    (∑ n ∈ Ico 146944 147200, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (407922 : ℤ) ∧
    (∑ n ∈ Ico 146944 147200, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (8158467690199166837731316041 : ℤ) := by
  rcases cdemPrefixStats_146944_147072 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_147072_147200 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 146944 ≤ 147072) (by norm_num : 147072 ≤ 147200), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 146944 ≤ 147072) (by norm_num : 147072 ≤ 147200), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 146944 ≤ 147072) (by norm_num : 147072 ≤ 147200), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 146944 ≤ 147072) (by norm_num : 147072 ≤ 147200), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_147200_147264 :
    (∑ n ∈ Ico 147200 147264, mobiusTreeValue 16 mobiusTable1200001 n) = (-11 : ℤ) ∧
    (∑ n ∈ Ico 147200 147264, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 147200 147264, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-373561 : ℤ) ∧
    (∑ n ∈ Ico 147200 147264, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-7471285211073334340626674035 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_147264_147328 :
    (∑ n ∈ Ico 147264 147328, mobiusTreeValue 16 mobiusTable1200001 n) = (-9 : ℤ) ∧
    (∑ n ∈ Ico 147264 147328, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 147264 147328, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-305487 : ℤ) ∧
    (∑ n ∈ Ico 147264 147328, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-6109850523806972060137714702 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_147200_147328 :
    (∑ n ∈ Ico 147200 147328, mobiusTreeValue 16 mobiusTable1200001 n) = (-20 : ℤ) ∧
    (∑ n ∈ Ico 147200 147328, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (80 : ℕ) ∧
    (∑ n ∈ Ico 147200 147328, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-679048 : ℤ) ∧
    (∑ n ∈ Ico 147200 147328, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-13581135734880306400764388737 : ℤ) := by
  rcases cdemPrefixStats_147200_147264 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_147264_147328 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 147200 ≤ 147264) (by norm_num : 147264 ≤ 147328), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 147200 ≤ 147264) (by norm_num : 147264 ≤ 147328), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 147200 ≤ 147264) (by norm_num : 147264 ≤ 147328), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 147200 ≤ 147264) (by norm_num : 147264 ≤ 147328), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_147328_147392 :
    (∑ n ∈ Ico 147328 147392, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 147328 147392, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 147328 147392, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-33940 : ℤ) ∧
    (∑ n ∈ Ico 147328 147392, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-678794526784188430866123672 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_147392_147456 :
    (∑ n ∈ Ico 147392 147456, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 147392 147456, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 147392 147456, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (33894 : ℤ) ∧
    (∑ n ∈ Ico 147392 147456, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (677901454003070540726879619 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_147328_147456 :
    (∑ n ∈ Ico 147328 147456, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 147328 147456, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 147328 147456, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-46 : ℤ) ∧
    (∑ n ∈ Ico 147328 147456, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-893072781117890139244053 : ℤ) := by
  rcases cdemPrefixStats_147328_147392 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_147392_147456 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 147328 ≤ 147392) (by norm_num : 147392 ≤ 147456), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 147328 ≤ 147392) (by norm_num : 147392 ≤ 147456), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 147328 ≤ 147392) (by norm_num : 147392 ≤ 147456), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 147328 ≤ 147392) (by norm_num : 147392 ≤ 147456), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_147200_147456 :
    (∑ n ∈ Ico 147200 147456, mobiusTreeValue 16 mobiusTable1200001 n) = (-20 : ℤ) ∧
    (∑ n ∈ Ico 147200 147456, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (158 : ℕ) ∧
    (∑ n ∈ Ico 147200 147456, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-679094 : ℤ) ∧
    (∑ n ∈ Ico 147200 147456, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-13582028807661424290903632790 : ℤ) := by
  rcases cdemPrefixStats_147200_147328 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_147328_147456 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 147200 ≤ 147328) (by norm_num : 147328 ≤ 147456), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 147200 ≤ 147328) (by norm_num : 147328 ≤ 147456), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 147200 ≤ 147328) (by norm_num : 147328 ≤ 147456), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 147200 ≤ 147328) (by norm_num : 147328 ≤ 147456), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_146944_147456 :
    (∑ n ∈ Ico 146944 147456, mobiusTreeValue 16 mobiusTable1200001 n) = (-8 : ℤ) ∧
    (∑ n ∈ Ico 146944 147456, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (314 : ℕ) ∧
    (∑ n ∈ Ico 146944 147456, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-271172 : ℤ) ∧
    (∑ n ∈ Ico 146944 147456, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-5423561117462257453172316749 : ℤ) := by
  rcases cdemPrefixStats_146944_147200 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_147200_147456 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 146944 ≤ 147200) (by norm_num : 147200 ≤ 147456), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 146944 ≤ 147200) (by norm_num : 147200 ≤ 147456), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 146944 ≤ 147200) (by norm_num : 147200 ≤ 147456), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 146944 ≤ 147200) (by norm_num : 147200 ≤ 147456), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_146432_147456 :
    (∑ n ∈ Ico 146432 147456, mobiusTreeValue 16 mobiusTable1200001 n) = (-10 : ℤ) ∧
    (∑ n ∈ Ico 146432 147456, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (624 : ℕ) ∧
    (∑ n ∈ Ico 146432 147456, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-338943 : ℤ) ∧
    (∑ n ∈ Ico 146432 147456, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-6779081149487999246788222517 : ℤ) := by
  rcases cdemPrefixStats_146432_146944 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_146944_147456 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 146432 ≤ 146944) (by norm_num : 146944 ≤ 147456), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 146432 ≤ 146944) (by norm_num : 146944 ≤ 147456), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 146432 ≤ 146944) (by norm_num : 146944 ≤ 147456), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 146432 ≤ 146944) (by norm_num : 146944 ≤ 147456), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_145408_147456 :
    (∑ n ∈ Ico 145408 147456, mobiusTreeValue 16 mobiusTable1200001 n) = (-9 : ℤ) ∧
    (∑ n ∈ Ico 145408 147456, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (1245 : ℕ) ∧
    (∑ n ∈ Ico 145408 147456, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-305313 : ℤ) ∧
    (∑ n ∈ Ico 145408 147456, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-6106472601018942611389077401 : ℤ) := by
  rcases cdemPrefixStats_145408_146432 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_146432_147456 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 145408 ≤ 146432) (by norm_num : 146432 ≤ 147456), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 145408 ≤ 146432) (by norm_num : 146432 ≤ 147456), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 145408 ≤ 146432) (by norm_num : 146432 ≤ 147456), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 145408 ≤ 146432) (by norm_num : 146432 ≤ 147456), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_143360_147456 :
    (∑ n ∈ Ico 143360 147456, mobiusTreeValue 16 mobiusTable1200001 n) = (2 : ℤ) ∧
    (∑ n ∈ Ico 143360 147456, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (2486 : ℕ) ∧
    (∑ n ∈ Ico 143360 147456, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (77753 : ℤ) ∧
    (∑ n ∈ Ico 143360 147456, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1554831769282633231674959803 : ℤ) := by
  rcases cdemPrefixStats_143360_145408 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_145408_147456 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 143360 ≤ 145408) (by norm_num : 145408 ≤ 147456), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 143360 ≤ 145408) (by norm_num : 145408 ≤ 147456), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 143360 ≤ 145408) (by norm_num : 145408 ≤ 147456), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 143360 ≤ 145408) (by norm_num : 145408 ≤ 147456), hR1, hR2] <;> norm_num

theorem cdemPrefixGroup035_checked_complete :
    (∑ n ∈ Ico 143360 147456, mobiusTreeValue 16 mobiusTable1200001 n) = (2 : ℤ) ∧
    (∑ n ∈ Ico 143360 147456, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (2486 : ℕ) ∧
    (∑ n ∈ Ico 143360 147456, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (77753 : ℤ) ∧
    (∑ n ∈ Ico 143360 147456, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1554831769282633231674959803 : ℤ) := cdemPrefixStats_143360_147456
end Helfgott
#print axioms Helfgott.cdemPrefixGroup035_checked_complete

open Helfgott Finset
open scoped BigOperators

theorem solution :
    (∑ n ∈ Ico 143360 147456, mobiusTreeValue 16 mobiusTable1200001 n) = (2 : ℤ) ∧
    (∑ n ∈ Ico 143360 147456, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (2486 : ℕ) ∧
    (∑ n ∈ Ico 143360 147456, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (77753 : ℤ) ∧
    (∑ n ∈ Ico 143360 147456, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1554831769282633231674959803 : ℤ) := Helfgott.cdemPrefixGroup035_checked_complete
#print axioms solution
