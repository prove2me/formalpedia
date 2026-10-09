-- Prove2me | solution 1 for Helfgott.cdemPrefixGroup022_checked
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-09T01:57:16.630028+00:00
-- url     : https://prove2.me/submissions/d611cd48-2e53-422d-b3bf-b781778b08b5

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
private theorem cdemPrefixStats_90112_90176 :
    (∑ n ∈ Ico 90112 90176, mobiusTreeValue 16 mobiusTable1200001 n) = (4 : ℤ) ∧
    (∑ n ∈ Ico 90112 90176, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 90112 90176, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (221918 : ℤ) ∧
    (∑ n ∈ Ico 90112 90176, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (4438390803743711529351069628 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_90176_90240 :
    (∑ n ∈ Ico 90176 90240, mobiusTreeValue 16 mobiusTable1200001 n) = (-8 : ℤ) ∧
    (∑ n ∈ Ico 90176 90240, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (42 : ℕ) ∧
    (∑ n ∈ Ico 90176 90240, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-443500 : ℤ) ∧
    (∑ n ∈ Ico 90176 90240, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-8870113965588368414559310611 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_90112_90240 :
    (∑ n ∈ Ico 90112 90240, mobiusTreeValue 16 mobiusTable1200001 n) = (-4 : ℤ) ∧
    (∑ n ∈ Ico 90112 90240, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (80 : ℕ) ∧
    (∑ n ∈ Ico 90112 90240, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-221582 : ℤ) ∧
    (∑ n ∈ Ico 90112 90240, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-4431723161844656885208240983 : ℤ) := by
  rcases cdemPrefixStats_90112_90176 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_90176_90240 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 90112 ≤ 90176) (by norm_num : 90176 ≤ 90240), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 90112 ≤ 90176) (by norm_num : 90176 ≤ 90240), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 90112 ≤ 90176) (by norm_num : 90176 ≤ 90240), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 90112 ≤ 90176) (by norm_num : 90176 ≤ 90240), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_90240_90304 :
    (∑ n ∈ Ico 90240 90304, mobiusTreeValue 16 mobiusTable1200001 n) = (8 : ℤ) ∧
    (∑ n ∈ Ico 90240 90304, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 90240 90304, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (443094 : ℤ) ∧
    (∑ n ∈ Ico 90240 90304, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (8861921902371360637503547163 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_90304_90368 :
    (∑ n ∈ Ico 90304 90368, mobiusTreeValue 16 mobiusTable1200001 n) = (14 : ℤ) ∧
    (∑ n ∈ Ico 90304 90368, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 90304 90368, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (774875 : ℤ) ∧
    (∑ n ∈ Ico 90304 90368, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (15497661464487885256132336193 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_90240_90368 :
    (∑ n ∈ Ico 90240 90368, mobiusTreeValue 16 mobiusTable1200001 n) = (22 : ℤ) ∧
    (∑ n ∈ Ico 90240 90368, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (76 : ℕ) ∧
    (∑ n ∈ Ico 90240 90368, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (1217969 : ℤ) ∧
    (∑ n ∈ Ico 90240 90368, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (24359583366859245893635883356 : ℤ) := by
  rcases cdemPrefixStats_90240_90304 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_90304_90368 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 90240 ≤ 90304) (by norm_num : 90304 ≤ 90368), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 90240 ≤ 90304) (by norm_num : 90304 ≤ 90368), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 90240 ≤ 90304) (by norm_num : 90304 ≤ 90368), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 90240 ≤ 90304) (by norm_num : 90304 ≤ 90368), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_90112_90368 :
    (∑ n ∈ Ico 90112 90368, mobiusTreeValue 16 mobiusTable1200001 n) = (18 : ℤ) ∧
    (∑ n ∈ Ico 90112 90368, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (156 : ℕ) ∧
    (∑ n ∈ Ico 90112 90368, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (996387 : ℤ) ∧
    (∑ n ∈ Ico 90112 90368, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (19927860205014589008427642373 : ℤ) := by
  rcases cdemPrefixStats_90112_90240 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_90240_90368 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 90112 ≤ 90240) (by norm_num : 90240 ≤ 90368), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 90112 ≤ 90240) (by norm_num : 90240 ≤ 90368), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 90112 ≤ 90240) (by norm_num : 90240 ≤ 90368), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 90112 ≤ 90240) (by norm_num : 90240 ≤ 90368), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_90368_90432 :
    (∑ n ∈ Ico 90368 90432, mobiusTreeValue 16 mobiusTable1200001 n) = (-7 : ℤ) ∧
    (∑ n ∈ Ico 90368 90432, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 90368 90432, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-387257 : ℤ) ∧
    (∑ n ∈ Ico 90368 90432, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-7745186206186316036432467978 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_90432_90496 :
    (∑ n ∈ Ico 90432 90496, mobiusTreeValue 16 mobiusTable1200001 n) = (5 : ℤ) ∧
    (∑ n ∈ Ico 90432 90496, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 90432 90496, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (276203 : ℤ) ∧
    (∑ n ∈ Ico 90432 90496, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (5524176914212760234883566770 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_90368_90496 :
    (∑ n ∈ Ico 90368 90496, mobiusTreeValue 16 mobiusTable1200001 n) = (-2 : ℤ) ∧
    (∑ n ∈ Ico 90368 90496, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 90368 90496, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-111054 : ℤ) ∧
    (∑ n ∈ Ico 90368 90496, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-2221009291973555801548901208 : ℤ) := by
  rcases cdemPrefixStats_90368_90432 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_90432_90496 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 90368 ≤ 90432) (by norm_num : 90432 ≤ 90496), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 90368 ≤ 90432) (by norm_num : 90432 ≤ 90496), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 90368 ≤ 90432) (by norm_num : 90432 ≤ 90496), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 90368 ≤ 90432) (by norm_num : 90432 ≤ 90496), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_90496_90560 :
    (∑ n ∈ Ico 90496 90560, mobiusTreeValue 16 mobiusTable1200001 n) = (-9 : ℤ) ∧
    (∑ n ∈ Ico 90496 90560, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 90496 90560, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-497156 : ℤ) ∧
    (∑ n ∈ Ico 90496 90560, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-9943201606846322320154180340 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_90560_90624 :
    (∑ n ∈ Ico 90560 90624, mobiusTreeValue 16 mobiusTable1200001 n) = (10 : ℤ) ∧
    (∑ n ∈ Ico 90560 90624, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 90560 90624, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (552021 : ℤ) ∧
    (∑ n ∈ Ico 90560 90624, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (11040464505809429532269020906 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_90496_90624 :
    (∑ n ∈ Ico 90496 90624, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 90496 90624, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 90496 90624, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (54865 : ℤ) ∧
    (∑ n ∈ Ico 90496 90624, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1097262898963107212114840566 : ℤ) := by
  rcases cdemPrefixStats_90496_90560 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_90560_90624 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 90496 ≤ 90560) (by norm_num : 90560 ≤ 90624), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 90496 ≤ 90560) (by norm_num : 90560 ≤ 90624), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 90496 ≤ 90560) (by norm_num : 90560 ≤ 90624), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 90496 ≤ 90560) (by norm_num : 90560 ≤ 90624), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_90368_90624 :
    (∑ n ∈ Ico 90368 90624, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 90368 90624, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (155 : ℕ) ∧
    (∑ n ∈ Ico 90368 90624, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-56189 : ℤ) ∧
    (∑ n ∈ Ico 90368 90624, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-1123746393010448589434060642 : ℤ) := by
  rcases cdemPrefixStats_90368_90496 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_90496_90624 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 90368 ≤ 90496) (by norm_num : 90496 ≤ 90624), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 90368 ≤ 90496) (by norm_num : 90496 ≤ 90624), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 90368 ≤ 90496) (by norm_num : 90496 ≤ 90624), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 90368 ≤ 90496) (by norm_num : 90496 ≤ 90624), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_90112_90624 :
    (∑ n ∈ Ico 90112 90624, mobiusTreeValue 16 mobiusTable1200001 n) = (17 : ℤ) ∧
    (∑ n ∈ Ico 90112 90624, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (311 : ℕ) ∧
    (∑ n ∈ Ico 90112 90624, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (940198 : ℤ) ∧
    (∑ n ∈ Ico 90112 90624, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (18804113812004140418993581731 : ℤ) := by
  rcases cdemPrefixStats_90112_90368 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_90368_90624 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 90112 ≤ 90368) (by norm_num : 90368 ≤ 90624), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 90112 ≤ 90368) (by norm_num : 90368 ≤ 90624), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 90112 ≤ 90368) (by norm_num : 90368 ≤ 90624), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 90112 ≤ 90368) (by norm_num : 90368 ≤ 90624), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_90624_90688 :
    (∑ n ∈ Ico 90624 90688, mobiusTreeValue 16 mobiusTable1200001 n) = (2 : ℤ) ∧
    (∑ n ∈ Ico 90624 90688, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 90624 90688, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (110268 : ℤ) ∧
    (∑ n ∈ Ico 90624 90688, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (2205399508152511974122097708 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_90688_90752 :
    (∑ n ∈ Ico 90688 90752, mobiusTreeValue 16 mobiusTable1200001 n) = (6 : ℤ) ∧
    (∑ n ∈ Ico 90688 90752, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 90688 90752, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (330677 : ℤ) ∧
    (∑ n ∈ Ico 90688 90752, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (6613635483870879129933455044 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_90624_90752 :
    (∑ n ∈ Ico 90624 90752, mobiusTreeValue 16 mobiusTable1200001 n) = (8 : ℤ) ∧
    (∑ n ∈ Ico 90624 90752, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 90624 90752, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (440945 : ℤ) ∧
    (∑ n ∈ Ico 90624 90752, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (8819034992023391104055552752 : ℤ) := by
  rcases cdemPrefixStats_90624_90688 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_90688_90752 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 90624 ≤ 90688) (by norm_num : 90688 ≤ 90752), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 90624 ≤ 90688) (by norm_num : 90688 ≤ 90752), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 90624 ≤ 90688) (by norm_num : 90688 ≤ 90752), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 90624 ≤ 90688) (by norm_num : 90688 ≤ 90752), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_90752_90816 :
    (∑ n ∈ Ico 90752 90816, mobiusTreeValue 16 mobiusTable1200001 n) = (2 : ℤ) ∧
    (∑ n ∈ Ico 90752 90816, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 90752 90816, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (110172 : ℤ) ∧
    (∑ n ∈ Ico 90752 90816, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (2203395575618687620997310765 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_90816_90880 :
    (∑ n ∈ Ico 90816 90880, mobiusTreeValue 16 mobiusTable1200001 n) = (-5 : ℤ) ∧
    (∑ n ∈ Ico 90816 90880, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 90816 90880, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-275224 : ℤ) ∧
    (∑ n ∈ Ico 90816 90880, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-5504510109273386391244710127 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_90752_90880 :
    (∑ n ∈ Ico 90752 90880, mobiusTreeValue 16 mobiusTable1200001 n) = (-3 : ℤ) ∧
    (∑ n ∈ Ico 90752 90880, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (79 : ℕ) ∧
    (∑ n ∈ Ico 90752 90880, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-165052 : ℤ) ∧
    (∑ n ∈ Ico 90752 90880, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-3301114533654698770247399362 : ℤ) := by
  rcases cdemPrefixStats_90752_90816 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_90816_90880 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 90752 ≤ 90816) (by norm_num : 90816 ≤ 90880), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 90752 ≤ 90816) (by norm_num : 90816 ≤ 90880), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 90752 ≤ 90816) (by norm_num : 90816 ≤ 90880), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 90752 ≤ 90816) (by norm_num : 90816 ≤ 90880), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_90624_90880 :
    (∑ n ∈ Ico 90624 90880, mobiusTreeValue 16 mobiusTable1200001 n) = (5 : ℤ) ∧
    (∑ n ∈ Ico 90624 90880, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (157 : ℕ) ∧
    (∑ n ∈ Ico 90624 90880, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (275893 : ℤ) ∧
    (∑ n ∈ Ico 90624 90880, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (5517920458368692333808153390 : ℤ) := by
  rcases cdemPrefixStats_90624_90752 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_90752_90880 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 90624 ≤ 90752) (by norm_num : 90752 ≤ 90880), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 90624 ≤ 90752) (by norm_num : 90752 ≤ 90880), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 90624 ≤ 90752) (by norm_num : 90752 ≤ 90880), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 90624 ≤ 90752) (by norm_num : 90752 ≤ 90880), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_90880_90944 :
    (∑ n ∈ Ico 90880 90944, mobiusTreeValue 16 mobiusTable1200001 n) = (-6 : ℤ) ∧
    (∑ n ∈ Ico 90880 90944, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 90880 90944, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-329919 : ℤ) ∧
    (∑ n ∈ Ico 90880 90944, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-6598421336152327618752862476 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_90944_91008 :
    (∑ n ∈ Ico 90944 91008, mobiusTreeValue 16 mobiusTable1200001 n) = (11 : ℤ) ∧
    (∑ n ∈ Ico 90944 91008, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 90944 91008, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (604600 : ℤ) ∧
    (∑ n ∈ Ico 90944 91008, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (12092092187199694305423711926 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_90880_91008 :
    (∑ n ∈ Ico 90880 91008, mobiusTreeValue 16 mobiusTable1200001 n) = (5 : ℤ) ∧
    (∑ n ∈ Ico 90880 91008, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (79 : ℕ) ∧
    (∑ n ∈ Ico 90880 91008, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (274681 : ℤ) ∧
    (∑ n ∈ Ico 90880 91008, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (5493670851047366686670849450 : ℤ) := by
  rcases cdemPrefixStats_90880_90944 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_90944_91008 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 90880 ≤ 90944) (by norm_num : 90944 ≤ 91008), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 90880 ≤ 90944) (by norm_num : 90944 ≤ 91008), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 90880 ≤ 90944) (by norm_num : 90944 ≤ 91008), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 90880 ≤ 90944) (by norm_num : 90944 ≤ 91008), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_91008_91072 :
    (∑ n ∈ Ico 91008 91072, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 91008 91072, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 91008 91072, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-55046 : ℤ) ∧
    (∑ n ∈ Ico 91008 91072, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-1100964027656445809631660441 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_91072_91136 :
    (∑ n ∈ Ico 91072 91136, mobiusTreeValue 16 mobiusTable1200001 n) = (-2 : ℤ) ∧
    (∑ n ∈ Ico 91072 91136, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 91072 91136, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-109701 : ℤ) ∧
    (∑ n ∈ Ico 91072 91136, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-2194040577342222598081484933 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_91008_91136 :
    (∑ n ∈ Ico 91008 91136, mobiusTreeValue 16 mobiusTable1200001 n) = (-3 : ℤ) ∧
    (∑ n ∈ Ico 91008 91136, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (79 : ℕ) ∧
    (∑ n ∈ Ico 91008 91136, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-164747 : ℤ) ∧
    (∑ n ∈ Ico 91008 91136, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-3295004604998668407713145374 : ℤ) := by
  rcases cdemPrefixStats_91008_91072 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_91072_91136 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 91008 ≤ 91072) (by norm_num : 91072 ≤ 91136), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 91008 ≤ 91072) (by norm_num : 91072 ≤ 91136), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 91008 ≤ 91072) (by norm_num : 91072 ≤ 91136), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 91008 ≤ 91072) (by norm_num : 91072 ≤ 91136), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_90880_91136 :
    (∑ n ∈ Ico 90880 91136, mobiusTreeValue 16 mobiusTable1200001 n) = (2 : ℤ) ∧
    (∑ n ∈ Ico 90880 91136, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (158 : ℕ) ∧
    (∑ n ∈ Ico 90880 91136, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (109934 : ℤ) ∧
    (∑ n ∈ Ico 90880 91136, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (2198666246048698278957704076 : ℤ) := by
  rcases cdemPrefixStats_90880_91008 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_91008_91136 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 90880 ≤ 91008) (by norm_num : 91008 ≤ 91136), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 90880 ≤ 91008) (by norm_num : 91008 ≤ 91136), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 90880 ≤ 91008) (by norm_num : 91008 ≤ 91136), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 90880 ≤ 91008) (by norm_num : 91008 ≤ 91136), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_90624_91136 :
    (∑ n ∈ Ico 90624 91136, mobiusTreeValue 16 mobiusTable1200001 n) = (7 : ℤ) ∧
    (∑ n ∈ Ico 90624 91136, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (315 : ℕ) ∧
    (∑ n ∈ Ico 90624 91136, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (385827 : ℤ) ∧
    (∑ n ∈ Ico 90624 91136, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (7716586704417390612765857466 : ℤ) := by
  rcases cdemPrefixStats_90624_90880 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_90880_91136 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 90624 ≤ 90880) (by norm_num : 90880 ≤ 91136), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 90624 ≤ 90880) (by norm_num : 90880 ≤ 91136), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 90624 ≤ 90880) (by norm_num : 90880 ≤ 91136), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 90624 ≤ 90880) (by norm_num : 90880 ≤ 91136), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_90112_91136 :
    (∑ n ∈ Ico 90112 91136, mobiusTreeValue 16 mobiusTable1200001 n) = (24 : ℤ) ∧
    (∑ n ∈ Ico 90112 91136, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (626 : ℕ) ∧
    (∑ n ∈ Ico 90112 91136, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (1326025 : ℤ) ∧
    (∑ n ∈ Ico 90112 91136, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (26520700516421531031759439197 : ℤ) := by
  rcases cdemPrefixStats_90112_90624 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_90624_91136 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 90112 ≤ 90624) (by norm_num : 90624 ≤ 91136), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 90112 ≤ 90624) (by norm_num : 90624 ≤ 91136), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 90112 ≤ 90624) (by norm_num : 90624 ≤ 91136), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 90112 ≤ 90624) (by norm_num : 90624 ≤ 91136), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_91136_91200 :
    (∑ n ∈ Ico 91136 91200, mobiusTreeValue 16 mobiusTable1200001 n) = (-4 : ℤ) ∧
    (∑ n ∈ Ico 91136 91200, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 91136 91200, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-219417 : ℤ) ∧
    (∑ n ∈ Ico 91136 91200, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-4388347020134321854293744529 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_91200_91264 :
    (∑ n ∈ Ico 91200 91264, mobiusTreeValue 16 mobiusTable1200001 n) = (3 : ℤ) ∧
    (∑ n ∈ Ico 91200 91264, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 91200 91264, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (164513 : ℤ) ∧
    (∑ n ∈ Ico 91200 91264, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (3290338847840556038242394752 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_91136_91264 :
    (∑ n ∈ Ico 91136 91264, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 91136 91264, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (79 : ℕ) ∧
    (∑ n ∈ Ico 91136 91264, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-54904 : ℤ) ∧
    (∑ n ∈ Ico 91136 91264, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-1098008172293765816051349777 : ℤ) := by
  rcases cdemPrefixStats_91136_91200 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_91200_91264 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 91136 ≤ 91200) (by norm_num : 91200 ≤ 91264), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 91136 ≤ 91200) (by norm_num : 91200 ≤ 91264), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 91136 ≤ 91200) (by norm_num : 91200 ≤ 91264), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 91136 ≤ 91200) (by norm_num : 91200 ≤ 91264), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_91264_91328 :
    (∑ n ∈ Ico 91264 91328, mobiusTreeValue 16 mobiusTable1200001 n) = (-3 : ℤ) ∧
    (∑ n ∈ Ico 91264 91328, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 91264 91328, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-164281 : ℤ) ∧
    (∑ n ∈ Ico 91264 91328, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-3285642316531059596090397908 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_91328_91392 :
    (∑ n ∈ Ico 91328 91392, mobiusTreeValue 16 mobiusTable1200001 n) = (-3 : ℤ) ∧
    (∑ n ∈ Ico 91328 91392, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 91328 91392, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-164105 : ℤ) ∧
    (∑ n ∈ Ico 91328 91392, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-3282119676379626906627652850 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_91264_91392 :
    (∑ n ∈ Ico 91264 91392, mobiusTreeValue 16 mobiusTable1200001 n) = (-6 : ℤ) ∧
    (∑ n ∈ Ico 91264 91392, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 91264 91392, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-328386 : ℤ) ∧
    (∑ n ∈ Ico 91264 91392, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-6567761992910686502718050758 : ℤ) := by
  rcases cdemPrefixStats_91264_91328 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_91328_91392 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 91264 ≤ 91328) (by norm_num : 91328 ≤ 91392), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 91264 ≤ 91328) (by norm_num : 91328 ≤ 91392), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 91264 ≤ 91328) (by norm_num : 91328 ≤ 91392), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 91264 ≤ 91328) (by norm_num : 91328 ≤ 91392), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_91136_91392 :
    (∑ n ∈ Ico 91136 91392, mobiusTreeValue 16 mobiusTable1200001 n) = (-7 : ℤ) ∧
    (∑ n ∈ Ico 91136 91392, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (157 : ℕ) ∧
    (∑ n ∈ Ico 91136 91392, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-383290 : ℤ) ∧
    (∑ n ∈ Ico 91136 91392, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-7665770165204452318769400535 : ℤ) := by
  rcases cdemPrefixStats_91136_91264 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_91264_91392 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 91136 ≤ 91264) (by norm_num : 91264 ≤ 91392), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 91136 ≤ 91264) (by norm_num : 91264 ≤ 91392), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 91136 ≤ 91264) (by norm_num : 91264 ≤ 91392), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 91136 ≤ 91264) (by norm_num : 91264 ≤ 91392), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_91392_91456 :
    (∑ n ∈ Ico 91392 91456, mobiusTreeValue 16 mobiusTable1200001 n) = (-11 : ℤ) ∧
    (∑ n ∈ Ico 91392 91456, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 91392 91456, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-601664 : ℤ) ∧
    (∑ n ∈ Ico 91392 91456, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-12033407538474490901165480365 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_91456_91520 :
    (∑ n ∈ Ico 91456 91520, mobiusTreeValue 16 mobiusTable1200001 n) = (2 : ℤ) ∧
    (∑ n ∈ Ico 91456 91520, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 91456 91520, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (109229 : ℤ) ∧
    (∑ n ∈ Ico 91456 91520, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (2184597477827922859734484280 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_91392_91520 :
    (∑ n ∈ Ico 91392 91520, mobiusTreeValue 16 mobiusTable1200001 n) = (-9 : ℤ) ∧
    (∑ n ∈ Ico 91392 91520, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (79 : ℕ) ∧
    (∑ n ∈ Ico 91392 91520, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-492435 : ℤ) ∧
    (∑ n ∈ Ico 91392 91520, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-9848810060646568041430996085 : ℤ) := by
  rcases cdemPrefixStats_91392_91456 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_91456_91520 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 91392 ≤ 91456) (by norm_num : 91456 ≤ 91520), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 91392 ≤ 91456) (by norm_num : 91456 ≤ 91520), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 91392 ≤ 91456) (by norm_num : 91456 ≤ 91520), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 91392 ≤ 91456) (by norm_num : 91456 ≤ 91520), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_91520_91584 :
    (∑ n ∈ Ico 91520 91584, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 91520 91584, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 91520 91584, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-54502 : ℤ) ∧
    (∑ n ∈ Ico 91520 91584, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-1090032868394574618565559197 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_91584_91648 :
    (∑ n ∈ Ico 91584 91648, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 91584 91648, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 91584 91648, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-54660 : ℤ) ∧
    (∑ n ∈ Ico 91584 91648, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-1093215775763861316768805784 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_91520_91648 :
    (∑ n ∈ Ico 91520 91648, mobiusTreeValue 16 mobiusTable1200001 n) = (-2 : ℤ) ∧
    (∑ n ∈ Ico 91520 91648, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (76 : ℕ) ∧
    (∑ n ∈ Ico 91520 91648, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-109162 : ℤ) ∧
    (∑ n ∈ Ico 91520 91648, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-2183248644158435935334364981 : ℤ) := by
  rcases cdemPrefixStats_91520_91584 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_91584_91648 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 91520 ≤ 91584) (by norm_num : 91584 ≤ 91648), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 91520 ≤ 91584) (by norm_num : 91584 ≤ 91648), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 91520 ≤ 91584) (by norm_num : 91584 ≤ 91648), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 91520 ≤ 91584) (by norm_num : 91584 ≤ 91648), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_91392_91648 :
    (∑ n ∈ Ico 91392 91648, mobiusTreeValue 16 mobiusTable1200001 n) = (-11 : ℤ) ∧
    (∑ n ∈ Ico 91392 91648, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (155 : ℕ) ∧
    (∑ n ∈ Ico 91392 91648, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-601597 : ℤ) ∧
    (∑ n ∈ Ico 91392 91648, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-12032058704805003976765361066 : ℤ) := by
  rcases cdemPrefixStats_91392_91520 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_91520_91648 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 91392 ≤ 91520) (by norm_num : 91520 ≤ 91648), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 91392 ≤ 91520) (by norm_num : 91520 ≤ 91648), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 91392 ≤ 91520) (by norm_num : 91520 ≤ 91648), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 91392 ≤ 91520) (by norm_num : 91520 ≤ 91648), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_91136_91648 :
    (∑ n ∈ Ico 91136 91648, mobiusTreeValue 16 mobiusTable1200001 n) = (-18 : ℤ) ∧
    (∑ n ∈ Ico 91136 91648, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (312 : ℕ) ∧
    (∑ n ∈ Ico 91136 91648, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-984887 : ℤ) ∧
    (∑ n ∈ Ico 91136 91648, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-19697828870009456295534761601 : ℤ) := by
  rcases cdemPrefixStats_91136_91392 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_91392_91648 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 91136 ≤ 91392) (by norm_num : 91392 ≤ 91648), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 91136 ≤ 91392) (by norm_num : 91392 ≤ 91648), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 91136 ≤ 91392) (by norm_num : 91392 ≤ 91648), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 91136 ≤ 91392) (by norm_num : 91392 ≤ 91648), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_91648_91712 :
    (∑ n ∈ Ico 91648 91712, mobiusTreeValue 16 mobiusTable1200001 n) = (6 : ℤ) ∧
    (∑ n ∈ Ico 91648 91712, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 91648 91712, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (327249 : ℤ) ∧
    (∑ n ∈ Ico 91648 91712, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (6545026480568028954239679312 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_91712_91776 :
    (∑ n ∈ Ico 91712 91776, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 91712 91776, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 91712 91776, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (54457 : ℤ) ∧
    (∑ n ∈ Ico 91712 91776, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1089110586561262404870360838 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_91648_91776 :
    (∑ n ∈ Ico 91648 91776, mobiusTreeValue 16 mobiusTable1200001 n) = (7 : ℤ) ∧
    (∑ n ∈ Ico 91648 91776, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (75 : ℕ) ∧
    (∑ n ∈ Ico 91648 91776, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (381706 : ℤ) ∧
    (∑ n ∈ Ico 91648 91776, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (7634137067129291359110040150 : ℤ) := by
  rcases cdemPrefixStats_91648_91712 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_91712_91776 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 91648 ≤ 91712) (by norm_num : 91712 ≤ 91776), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 91648 ≤ 91712) (by norm_num : 91712 ≤ 91776), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 91648 ≤ 91712) (by norm_num : 91712 ≤ 91776), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 91648 ≤ 91712) (by norm_num : 91712 ≤ 91776), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_91776_91840 :
    (∑ n ∈ Ico 91776 91840, mobiusTreeValue 16 mobiusTable1200001 n) = (-9 : ℤ) ∧
    (∑ n ∈ Ico 91776 91840, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 91776 91840, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-490091 : ℤ) ∧
    (∑ n ∈ Ico 91776 91840, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-9801904459234724862059693030 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_91840_91904 :
    (∑ n ∈ Ico 91840 91904, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 91840 91904, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 91840 91904, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-54519 : ℤ) ∧
    (∑ n ∈ Ico 91840 91904, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-1090449267120566355945452184 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_91776_91904 :
    (∑ n ∈ Ico 91776 91904, mobiusTreeValue 16 mobiusTable1200001 n) = (-10 : ℤ) ∧
    (∑ n ∈ Ico 91776 91904, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 91776 91904, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-544610 : ℤ) ∧
    (∑ n ∈ Ico 91776 91904, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-10892353726355291218005145214 : ℤ) := by
  rcases cdemPrefixStats_91776_91840 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_91840_91904 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 91776 ≤ 91840) (by norm_num : 91840 ≤ 91904), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 91776 ≤ 91840) (by norm_num : 91840 ≤ 91904), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 91776 ≤ 91840) (by norm_num : 91840 ≤ 91904), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 91776 ≤ 91840) (by norm_num : 91840 ≤ 91904), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_91648_91904 :
    (∑ n ∈ Ico 91648 91904, mobiusTreeValue 16 mobiusTable1200001 n) = (-3 : ℤ) ∧
    (∑ n ∈ Ico 91648 91904, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (153 : ℕ) ∧
    (∑ n ∈ Ico 91648 91904, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-162904 : ℤ) ∧
    (∑ n ∈ Ico 91648 91904, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-3258216659225999858895105064 : ℤ) := by
  rcases cdemPrefixStats_91648_91776 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_91776_91904 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 91648 ≤ 91776) (by norm_num : 91776 ≤ 91904), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 91648 ≤ 91776) (by norm_num : 91776 ≤ 91904), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 91648 ≤ 91776) (by norm_num : 91776 ≤ 91904), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 91648 ≤ 91776) (by norm_num : 91776 ≤ 91904), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_91904_91968 :
    (∑ n ∈ Ico 91904 91968, mobiusTreeValue 16 mobiusTable1200001 n) = (-5 : ℤ) ∧
    (∑ n ∈ Ico 91904 91968, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 91904 91968, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-271809 : ℤ) ∧
    (∑ n ∈ Ico 91904 91968, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-5436294513516904318069208353 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_91968_92032 :
    (∑ n ∈ Ico 91968 92032, mobiusTreeValue 16 mobiusTable1200001 n) = (4 : ℤ) ∧
    (∑ n ∈ Ico 91968 92032, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 91968 92032, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (217350 : ℤ) ∧
    (∑ n ∈ Ico 91968 92032, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (4347093989801888209013245510 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_91904_92032 :
    (∑ n ∈ Ico 91904 92032, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 91904 92032, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (81 : ℕ) ∧
    (∑ n ∈ Ico 91904 92032, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-54459 : ℤ) ∧
    (∑ n ∈ Ico 91904 92032, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-1089200523715016109055962843 : ℤ) := by
  rcases cdemPrefixStats_91904_91968 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_91968_92032 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 91904 ≤ 91968) (by norm_num : 91968 ≤ 92032), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 91904 ≤ 91968) (by norm_num : 91968 ≤ 92032), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 91904 ≤ 91968) (by norm_num : 91968 ≤ 92032), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 91904 ≤ 91968) (by norm_num : 91968 ≤ 92032), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_92032_92096 :
    (∑ n ∈ Ico 92032 92096, mobiusTreeValue 16 mobiusTable1200001 n) = (-5 : ℤ) ∧
    (∑ n ∈ Ico 92032 92096, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 92032 92096, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-271558 : ℤ) ∧
    (∑ n ∈ Ico 92032 92096, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-5431252936632709978525008611 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_92096_92160 :
    (∑ n ∈ Ico 92096 92160, mobiusTreeValue 16 mobiusTable1200001 n) = (9 : ℤ) ∧
    (∑ n ∈ Ico 92096 92160, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 92096 92160, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (488461 : ℤ) ∧
    (∑ n ∈ Ico 92096 92160, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (9769347299989966522354163332 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_92032_92160 :
    (∑ n ∈ Ico 92032 92160, mobiusTreeValue 16 mobiusTable1200001 n) = (4 : ℤ) ∧
    (∑ n ∈ Ico 92032 92160, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (76 : ℕ) ∧
    (∑ n ∈ Ico 92032 92160, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (216903 : ℤ) ∧
    (∑ n ∈ Ico 92032 92160, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (4338094363357256543829154721 : ℤ) := by
  rcases cdemPrefixStats_92032_92096 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_92096_92160 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 92032 ≤ 92096) (by norm_num : 92096 ≤ 92160), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 92032 ≤ 92096) (by norm_num : 92096 ≤ 92160), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 92032 ≤ 92096) (by norm_num : 92096 ≤ 92160), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 92032 ≤ 92096) (by norm_num : 92096 ≤ 92160), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_91904_92160 :
    (∑ n ∈ Ico 91904 92160, mobiusTreeValue 16 mobiusTable1200001 n) = (3 : ℤ) ∧
    (∑ n ∈ Ico 91904 92160, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (157 : ℕ) ∧
    (∑ n ∈ Ico 91904 92160, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (162444 : ℤ) ∧
    (∑ n ∈ Ico 91904 92160, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (3248893839642240434773191878 : ℤ) := by
  rcases cdemPrefixStats_91904_92032 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_92032_92160 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 91904 ≤ 92032) (by norm_num : 92032 ≤ 92160), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 91904 ≤ 92032) (by norm_num : 92032 ≤ 92160), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 91904 ≤ 92032) (by norm_num : 92032 ≤ 92160), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 91904 ≤ 92032) (by norm_num : 92032 ≤ 92160), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_91648_92160 :
    (∑ n ∈ Ico 91648 92160, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 91648 92160, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (310 : ℕ) ∧
    (∑ n ∈ Ico 91648 92160, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-460 : ℤ) ∧
    (∑ n ∈ Ico 91648 92160, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-9322819583759424121913186 : ℤ) := by
  rcases cdemPrefixStats_91648_91904 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_91904_92160 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 91648 ≤ 91904) (by norm_num : 91904 ≤ 92160), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 91648 ≤ 91904) (by norm_num : 91904 ≤ 92160), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 91648 ≤ 91904) (by norm_num : 91904 ≤ 92160), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 91648 ≤ 91904) (by norm_num : 91904 ≤ 92160), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_91136_92160 :
    (∑ n ∈ Ico 91136 92160, mobiusTreeValue 16 mobiusTable1200001 n) = (-18 : ℤ) ∧
    (∑ n ∈ Ico 91136 92160, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (622 : ℕ) ∧
    (∑ n ∈ Ico 91136 92160, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-985347 : ℤ) ∧
    (∑ n ∈ Ico 91136 92160, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-19707151689593215719656674787 : ℤ) := by
  rcases cdemPrefixStats_91136_91648 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_91648_92160 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 91136 ≤ 91648) (by norm_num : 91648 ≤ 92160), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 91136 ≤ 91648) (by norm_num : 91648 ≤ 92160), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 91136 ≤ 91648) (by norm_num : 91648 ≤ 92160), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 91136 ≤ 91648) (by norm_num : 91648 ≤ 92160), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_90112_92160 :
    (∑ n ∈ Ico 90112 92160, mobiusTreeValue 16 mobiusTable1200001 n) = (6 : ℤ) ∧
    (∑ n ∈ Ico 90112 92160, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (1248 : ℕ) ∧
    (∑ n ∈ Ico 90112 92160, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (340678 : ℤ) ∧
    (∑ n ∈ Ico 90112 92160, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (6813548826828315312102764410 : ℤ) := by
  rcases cdemPrefixStats_90112_91136 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_91136_92160 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 90112 ≤ 91136) (by norm_num : 91136 ≤ 92160), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 90112 ≤ 91136) (by norm_num : 91136 ≤ 92160), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 90112 ≤ 91136) (by norm_num : 91136 ≤ 92160), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 90112 ≤ 91136) (by norm_num : 91136 ≤ 92160), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_92160_92224 :
    (∑ n ∈ Ico 92160 92224, mobiusTreeValue 16 mobiusTable1200001 n) = (-10 : ℤ) ∧
    (∑ n ∈ Ico 92160 92224, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 92160 92224, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-542249 : ℤ) ∧
    (∑ n ∈ Ico 92160 92224, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-10845116712432808356646392477 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_92224_92288 :
    (∑ n ∈ Ico 92224 92288, mobiusTreeValue 16 mobiusTable1200001 n) = (-3 : ℤ) ∧
    (∑ n ∈ Ico 92224 92288, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 92224 92288, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-162684 : ℤ) ∧
    (∑ n ∈ Ico 92224 92288, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-3253724405888986474672599463 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_92160_92288 :
    (∑ n ∈ Ico 92160 92288, mobiusTreeValue 16 mobiusTable1200001 n) = (-13 : ℤ) ∧
    (∑ n ∈ Ico 92160 92288, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 92160 92288, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-704933 : ℤ) ∧
    (∑ n ∈ Ico 92160 92288, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-14098841118321794831318991940 : ℤ) := by
  rcases cdemPrefixStats_92160_92224 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_92224_92288 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 92160 ≤ 92224) (by norm_num : 92224 ≤ 92288), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 92160 ≤ 92224) (by norm_num : 92224 ≤ 92288), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 92160 ≤ 92224) (by norm_num : 92224 ≤ 92288), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 92160 ≤ 92224) (by norm_num : 92224 ≤ 92288), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_92288_92352 :
    (∑ n ∈ Ico 92288 92352, mobiusTreeValue 16 mobiusTable1200001 n) = (2 : ℤ) ∧
    (∑ n ∈ Ico 92288 92352, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 92288 92352, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (108358 : ℤ) ∧
    (∑ n ∈ Ico 92288 92352, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (2167152444373425222708346957 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_92352_92416 :
    (∑ n ∈ Ico 92352 92416, mobiusTreeValue 16 mobiusTable1200001 n) = (-12 : ℤ) ∧
    (∑ n ∈ Ico 92352 92416, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 92352 92416, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-649406 : ℤ) ∧
    (∑ n ∈ Ico 92352 92416, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-12988196431611638307589949489 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_92288_92416 :
    (∑ n ∈ Ico 92288 92416, mobiusTreeValue 16 mobiusTable1200001 n) = (-10 : ℤ) ∧
    (∑ n ∈ Ico 92288 92416, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (80 : ℕ) ∧
    (∑ n ∈ Ico 92288 92416, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-541048 : ℤ) ∧
    (∑ n ∈ Ico 92288 92416, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-10821043987238213084881602532 : ℤ) := by
  rcases cdemPrefixStats_92288_92352 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_92352_92416 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 92288 ≤ 92352) (by norm_num : 92352 ≤ 92416), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 92288 ≤ 92352) (by norm_num : 92352 ≤ 92416), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 92288 ≤ 92352) (by norm_num : 92352 ≤ 92416), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 92288 ≤ 92352) (by norm_num : 92352 ≤ 92416), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_92160_92416 :
    (∑ n ∈ Ico 92160 92416, mobiusTreeValue 16 mobiusTable1200001 n) = (-23 : ℤ) ∧
    (∑ n ∈ Ico 92160 92416, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (157 : ℕ) ∧
    (∑ n ∈ Ico 92160 92416, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-1245981 : ℤ) ∧
    (∑ n ∈ Ico 92160 92416, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-24919885105560007916200594472 : ℤ) := by
  rcases cdemPrefixStats_92160_92288 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_92288_92416 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 92160 ≤ 92288) (by norm_num : 92288 ≤ 92416), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 92160 ≤ 92288) (by norm_num : 92288 ≤ 92416), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 92160 ≤ 92288) (by norm_num : 92288 ≤ 92416), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 92160 ≤ 92288) (by norm_num : 92288 ≤ 92416), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_92416_92480 :
    (∑ n ∈ Ico 92416 92480, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 92416 92480, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 92416 92480, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-54015 : ℤ) ∧
    (∑ n ∈ Ico 92416 92480, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-1080332095822800472175970242 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_92480_92544 :
    (∑ n ∈ Ico 92480 92544, mobiusTreeValue 16 mobiusTable1200001 n) = (3 : ℤ) ∧
    (∑ n ∈ Ico 92480 92544, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 92480 92544, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (162014 : ℤ) ∧
    (∑ n ∈ Ico 92480 92544, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (3240345219790663318524450331 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_92416_92544 :
    (∑ n ∈ Ico 92416 92544, mobiusTreeValue 16 mobiusTable1200001 n) = (2 : ℤ) ∧
    (∑ n ∈ Ico 92416 92544, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 92416 92544, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (107999 : ℤ) ∧
    (∑ n ∈ Ico 92416 92544, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (2160013123967862846348480089 : ℤ) := by
  rcases cdemPrefixStats_92416_92480 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_92480_92544 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 92416 ≤ 92480) (by norm_num : 92480 ≤ 92544), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 92416 ≤ 92480) (by norm_num : 92480 ≤ 92544), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 92416 ≤ 92480) (by norm_num : 92480 ≤ 92544), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 92416 ≤ 92480) (by norm_num : 92480 ≤ 92544), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_92544_92608 :
    (∑ n ∈ Ico 92544 92608, mobiusTreeValue 16 mobiusTable1200001 n) = (-2 : ℤ) ∧
    (∑ n ∈ Ico 92544 92608, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 92544 92608, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-108008 : ℤ) ∧
    (∑ n ∈ Ico 92544 92608, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-2160200353930509561286758374 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_92608_92672 :
    (∑ n ∈ Ico 92608 92672, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 92608 92672, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 92608 92672, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (144 : ℤ) ∧
    (∑ n ∈ Ico 92608 92672, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (2901611369253773672413313 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_92544_92672 :
    (∑ n ∈ Ico 92544 92672, mobiusTreeValue 16 mobiusTable1200001 n) = (-2 : ℤ) ∧
    (∑ n ∈ Ico 92544 92672, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (80 : ℕ) ∧
    (∑ n ∈ Ico 92544 92672, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-107864 : ℤ) ∧
    (∑ n ∈ Ico 92544 92672, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-2157298742561255787614345061 : ℤ) := by
  rcases cdemPrefixStats_92544_92608 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_92608_92672 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 92544 ≤ 92608) (by norm_num : 92608 ≤ 92672), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 92544 ≤ 92608) (by norm_num : 92608 ≤ 92672), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 92544 ≤ 92608) (by norm_num : 92608 ≤ 92672), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 92544 ≤ 92608) (by norm_num : 92608 ≤ 92672), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_92416_92672 :
    (∑ n ∈ Ico 92416 92672, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 92416 92672, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (158 : ℕ) ∧
    (∑ n ∈ Ico 92416 92672, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (135 : ℤ) ∧
    (∑ n ∈ Ico 92416 92672, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (2714381406607058734135028 : ℤ) := by
  rcases cdemPrefixStats_92416_92544 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_92544_92672 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 92416 ≤ 92544) (by norm_num : 92544 ≤ 92672), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 92416 ≤ 92544) (by norm_num : 92544 ≤ 92672), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 92416 ≤ 92544) (by norm_num : 92544 ≤ 92672), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 92416 ≤ 92544) (by norm_num : 92544 ≤ 92672), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_92160_92672 :
    (∑ n ∈ Ico 92160 92672, mobiusTreeValue 16 mobiusTable1200001 n) = (-23 : ℤ) ∧
    (∑ n ∈ Ico 92160 92672, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (315 : ℕ) ∧
    (∑ n ∈ Ico 92160 92672, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-1245846 : ℤ) ∧
    (∑ n ∈ Ico 92160 92672, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-24917170724153400857466459444 : ℤ) := by
  rcases cdemPrefixStats_92160_92416 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_92416_92672 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 92160 ≤ 92416) (by norm_num : 92416 ≤ 92672), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 92160 ≤ 92416) (by norm_num : 92416 ≤ 92672), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 92160 ≤ 92416) (by norm_num : 92416 ≤ 92672), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 92160 ≤ 92416) (by norm_num : 92416 ≤ 92672), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_92672_92736 :
    (∑ n ∈ Ico 92672 92736, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 92672 92736, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 92672 92736, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (88 : ℤ) ∧
    (∑ n ∈ Ico 92672 92736, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1803456519134324102885974 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_92736_92800 :
    (∑ n ∈ Ico 92736 92800, mobiusTreeValue 16 mobiusTable1200001 n) = (-12 : ℤ) ∧
    (∑ n ∈ Ico 92736 92800, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (36 : ℕ) ∧
    (∑ n ∈ Ico 92736 92800, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-646817 : ℤ) ∧
    (∑ n ∈ Ico 92736 92800, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-12936471348071853332705446129 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_92672_92800 :
    (∑ n ∈ Ico 92672 92800, mobiusTreeValue 16 mobiusTable1200001 n) = (-12 : ℤ) ∧
    (∑ n ∈ Ico 92672 92800, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (74 : ℕ) ∧
    (∑ n ∈ Ico 92672 92800, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-646729 : ℤ) ∧
    (∑ n ∈ Ico 92672 92800, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-12934667891552719008602560155 : ℤ) := by
  rcases cdemPrefixStats_92672_92736 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_92736_92800 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 92672 ≤ 92736) (by norm_num : 92736 ≤ 92800), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 92672 ≤ 92736) (by norm_num : 92736 ≤ 92800), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 92672 ≤ 92736) (by norm_num : 92736 ≤ 92800), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 92672 ≤ 92736) (by norm_num : 92736 ≤ 92800), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_92800_92864 :
    (∑ n ∈ Ico 92800 92864, mobiusTreeValue 16 mobiusTable1200001 n) = (-14 : ℤ) ∧
    (∑ n ∈ Ico 92800 92864, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 92800 92864, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-753953 : ℤ) ∧
    (∑ n ∈ Ico 92800 92864, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-15079220460270276518775948094 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_92864_92928 :
    (∑ n ∈ Ico 92864 92928, mobiusTreeValue 16 mobiusTable1200001 n) = (8 : ℤ) ∧
    (∑ n ∈ Ico 92864 92928, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (42 : ℕ) ∧
    (∑ n ∈ Ico 92864 92928, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (430662 : ℤ) ∧
    (∑ n ∈ Ico 92864 92928, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (8613345461607098756134106594 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_92800_92928 :
    (∑ n ∈ Ico 92800 92928, mobiusTreeValue 16 mobiusTable1200001 n) = (-6 : ℤ) ∧
    (∑ n ∈ Ico 92800 92928, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (80 : ℕ) ∧
    (∑ n ∈ Ico 92800 92928, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-323291 : ℤ) ∧
    (∑ n ∈ Ico 92800 92928, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-6465874998663177762641841500 : ℤ) := by
  rcases cdemPrefixStats_92800_92864 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_92864_92928 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 92800 ≤ 92864) (by norm_num : 92864 ≤ 92928), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 92800 ≤ 92864) (by norm_num : 92864 ≤ 92928), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 92800 ≤ 92864) (by norm_num : 92864 ≤ 92928), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 92800 ≤ 92864) (by norm_num : 92864 ≤ 92928), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_92672_92928 :
    (∑ n ∈ Ico 92672 92928, mobiusTreeValue 16 mobiusTable1200001 n) = (-18 : ℤ) ∧
    (∑ n ∈ Ico 92672 92928, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (154 : ℕ) ∧
    (∑ n ∈ Ico 92672 92928, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-970020 : ℤ) ∧
    (∑ n ∈ Ico 92672 92928, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-19400542890215896771244401655 : ℤ) := by
  rcases cdemPrefixStats_92672_92800 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_92800_92928 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 92672 ≤ 92800) (by norm_num : 92800 ≤ 92928), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 92672 ≤ 92800) (by norm_num : 92800 ≤ 92928), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 92672 ≤ 92800) (by norm_num : 92800 ≤ 92928), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 92672 ≤ 92800) (by norm_num : 92800 ≤ 92928), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_92928_92992 :
    (∑ n ∈ Ico 92928 92992, mobiusTreeValue 16 mobiusTable1200001 n) = (-2 : ℤ) ∧
    (∑ n ∈ Ico 92928 92992, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 92928 92992, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-107511 : ℤ) ∧
    (∑ n ∈ Ico 92928 92992, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-2150271519568837970216067725 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_92992_93056 :
    (∑ n ∈ Ico 92992 93056, mobiusTreeValue 16 mobiusTable1200001 n) = (2 : ℤ) ∧
    (∑ n ∈ Ico 92992 93056, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 92992 93056, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (107606 : ℤ) ∧
    (∑ n ∈ Ico 92992 93056, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (2152132098878075275654911796 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_92928_93056 :
    (∑ n ∈ Ico 92928 93056, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 92928 93056, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 92928 93056, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (95 : ℤ) ∧
    (∑ n ∈ Ico 92928 93056, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1860579309237305438844071 : ℤ) := by
  rcases cdemPrefixStats_92928_92992 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_92992_93056 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 92928 ≤ 92992) (by norm_num : 92992 ≤ 93056), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 92928 ≤ 92992) (by norm_num : 92992 ≤ 93056), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 92928 ≤ 92992) (by norm_num : 92992 ≤ 93056), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 92928 ≤ 92992) (by norm_num : 92992 ≤ 93056), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_93056_93120 :
    (∑ n ∈ Ico 93056 93120, mobiusTreeValue 16 mobiusTable1200001 n) = (-2 : ℤ) ∧
    (∑ n ∈ Ico 93056 93120, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 93056 93120, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-107374 : ℤ) ∧
    (∑ n ∈ Ico 93056 93120, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-2147477535531763808261751232 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_93120_93184 :
    (∑ n ∈ Ico 93120 93184, mobiusTreeValue 16 mobiusTable1200001 n) = (-6 : ℤ) ∧
    (∑ n ∈ Ico 93120 93184, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 93120 93184, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-322073 : ℤ) ∧
    (∑ n ∈ Ico 93120 93184, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-6441581441216001879961724288 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_93056_93184 :
    (∑ n ∈ Ico 93056 93184, mobiusTreeValue 16 mobiusTable1200001 n) = (-8 : ℤ) ∧
    (∑ n ∈ Ico 93056 93184, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 93056 93184, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-429447 : ℤ) ∧
    (∑ n ∈ Ico 93056 93184, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-8589058976747765688223475520 : ℤ) := by
  rcases cdemPrefixStats_93056_93120 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_93120_93184 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 93056 ≤ 93120) (by norm_num : 93120 ≤ 93184), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 93056 ≤ 93120) (by norm_num : 93120 ≤ 93184), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 93056 ≤ 93120) (by norm_num : 93120 ≤ 93184), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 93056 ≤ 93120) (by norm_num : 93120 ≤ 93184), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_92928_93184 :
    (∑ n ∈ Ico 92928 93184, mobiusTreeValue 16 mobiusTable1200001 n) = (-8 : ℤ) ∧
    (∑ n ∈ Ico 92928 93184, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (156 : ℕ) ∧
    (∑ n ∈ Ico 92928 93184, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-429352 : ℤ) ∧
    (∑ n ∈ Ico 92928 93184, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-8587198397438528382784631449 : ℤ) := by
  rcases cdemPrefixStats_92928_93056 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_93056_93184 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 92928 ≤ 93056) (by norm_num : 93056 ≤ 93184), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 92928 ≤ 93056) (by norm_num : 93056 ≤ 93184), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 92928 ≤ 93056) (by norm_num : 93056 ≤ 93184), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 92928 ≤ 93056) (by norm_num : 93056 ≤ 93184), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_92672_93184 :
    (∑ n ∈ Ico 92672 93184, mobiusTreeValue 16 mobiusTable1200001 n) = (-26 : ℤ) ∧
    (∑ n ∈ Ico 92672 93184, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (310 : ℕ) ∧
    (∑ n ∈ Ico 92672 93184, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-1399372 : ℤ) ∧
    (∑ n ∈ Ico 92672 93184, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-27987741287654425154029033104 : ℤ) := by
  rcases cdemPrefixStats_92672_92928 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_92928_93184 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 92672 ≤ 92928) (by norm_num : 92928 ≤ 93184), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 92672 ≤ 92928) (by norm_num : 92928 ≤ 93184), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 92672 ≤ 92928) (by norm_num : 92928 ≤ 93184), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 92672 ≤ 92928) (by norm_num : 92928 ≤ 93184), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_92160_93184 :
    (∑ n ∈ Ico 92160 93184, mobiusTreeValue 16 mobiusTable1200001 n) = (-49 : ℤ) ∧
    (∑ n ∈ Ico 92160 93184, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (625 : ℕ) ∧
    (∑ n ∈ Ico 92160 93184, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-2645218 : ℤ) ∧
    (∑ n ∈ Ico 92160 93184, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-52904912011807826011495492548 : ℤ) := by
  rcases cdemPrefixStats_92160_92672 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_92672_93184 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 92160 ≤ 92672) (by norm_num : 92672 ≤ 93184), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 92160 ≤ 92672) (by norm_num : 92672 ≤ 93184), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 92160 ≤ 92672) (by norm_num : 92672 ≤ 93184), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 92160 ≤ 92672) (by norm_num : 92672 ≤ 93184), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_93184_93248 :
    (∑ n ∈ Ico 93184 93248, mobiusTreeValue 16 mobiusTable1200001 n) = (-7 : ℤ) ∧
    (∑ n ∈ Ico 93184 93248, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 93184 93248, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-375420 : ℤ) ∧
    (∑ n ∈ Ico 93184 93248, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-7508497076121485932794385243 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_93248_93312 :
    (∑ n ∈ Ico 93248 93312, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 93248 93312, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 93248 93312, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-53654 : ℤ) ∧
    (∑ n ∈ Ico 93248 93312, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-1073076044721398245138939980 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_93184_93312 :
    (∑ n ∈ Ico 93184 93312, mobiusTreeValue 16 mobiusTable1200001 n) = (-8 : ℤ) ∧
    (∑ n ∈ Ico 93184 93312, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 93184 93312, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-429074 : ℤ) ∧
    (∑ n ∈ Ico 93184 93312, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-8581573120842884177933325223 : ℤ) := by
  rcases cdemPrefixStats_93184_93248 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_93248_93312 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 93184 ≤ 93248) (by norm_num : 93248 ≤ 93312), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 93184 ≤ 93248) (by norm_num : 93248 ≤ 93312), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 93184 ≤ 93248) (by norm_num : 93248 ≤ 93312), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 93184 ≤ 93248) (by norm_num : 93248 ≤ 93312), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_93312_93376 :
    (∑ n ∈ Ico 93312 93376, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 93312 93376, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 93312 93376, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (53444 : ℤ) ∧
    (∑ n ∈ Ico 93312 93376, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1068919012722377447437921185 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_93376_93440 :
    (∑ n ∈ Ico 93376 93440, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 93376 93440, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 93376 93440, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-53594 : ℤ) ∧
    (∑ n ∈ Ico 93376 93440, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-1071901852547914455310245700 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_93312_93440 :
    (∑ n ∈ Ico 93312 93440, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 93312 93440, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 93312 93440, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-150 : ℤ) ∧
    (∑ n ∈ Ico 93312 93440, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-2982839825537007872324515 : ℤ) := by
  rcases cdemPrefixStats_93312_93376 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_93376_93440 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 93312 ≤ 93376) (by norm_num : 93376 ≤ 93440), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 93312 ≤ 93376) (by norm_num : 93376 ≤ 93440), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 93312 ≤ 93376) (by norm_num : 93376 ≤ 93440), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 93312 ≤ 93376) (by norm_num : 93376 ≤ 93440), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_93184_93440 :
    (∑ n ∈ Ico 93184 93440, mobiusTreeValue 16 mobiusTable1200001 n) = (-8 : ℤ) ∧
    (∑ n ∈ Ico 93184 93440, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (156 : ℕ) ∧
    (∑ n ∈ Ico 93184 93440, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-429224 : ℤ) ∧
    (∑ n ∈ Ico 93184 93440, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-8584555960668421185805649738 : ℤ) := by
  rcases cdemPrefixStats_93184_93312 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_93312_93440 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 93184 ≤ 93312) (by norm_num : 93312 ≤ 93440), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 93184 ≤ 93312) (by norm_num : 93312 ≤ 93440), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 93184 ≤ 93312) (by norm_num : 93312 ≤ 93440), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 93184 ≤ 93312) (by norm_num : 93312 ≤ 93440), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_93440_93504 :
    (∑ n ∈ Ico 93440 93504, mobiusTreeValue 16 mobiusTable1200001 n) = (-4 : ℤ) ∧
    (∑ n ∈ Ico 93440 93504, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 93440 93504, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-213856 : ℤ) ∧
    (∑ n ∈ Ico 93440 93504, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-4277136138181283916707225233 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_93504_93568 :
    (∑ n ∈ Ico 93504 93568, mobiusTreeValue 16 mobiusTable1200001 n) = (3 : ℤ) ∧
    (∑ n ∈ Ico 93504 93568, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 93504 93568, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (160396 : ℤ) ∧
    (∑ n ∈ Ico 93504 93568, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (3208007182782418219545672564 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_93440_93568 :
    (∑ n ∈ Ico 93440 93568, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 93440 93568, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 93440 93568, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-53460 : ℤ) ∧
    (∑ n ∈ Ico 93440 93568, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-1069128955398865697161552669 : ℤ) := by
  rcases cdemPrefixStats_93440_93504 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_93504_93568 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 93440 ≤ 93504) (by norm_num : 93504 ≤ 93568), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 93440 ≤ 93504) (by norm_num : 93504 ≤ 93568), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 93440 ≤ 93504) (by norm_num : 93504 ≤ 93568), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 93440 ≤ 93504) (by norm_num : 93504 ≤ 93568), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_93568_93632 :
    (∑ n ∈ Ico 93568 93632, mobiusTreeValue 16 mobiusTable1200001 n) = (-3 : ℤ) ∧
    (∑ n ∈ Ico 93568 93632, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 93568 93632, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-160244 : ℤ) ∧
    (∑ n ∈ Ico 93568 93632, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-3204910826958196916913964291 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_93632_93696 :
    (∑ n ∈ Ico 93632 93696, mobiusTreeValue 16 mobiusTable1200001 n) = (13 : ℤ) ∧
    (∑ n ∈ Ico 93632 93696, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 93632 93696, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (693996 : ℤ) ∧
    (∑ n ∈ Ico 93632 93696, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (13880014329122384990894775542 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_93568_93696 :
    (∑ n ∈ Ico 93568 93696, mobiusTreeValue 16 mobiusTable1200001 n) = (10 : ℤ) ∧
    (∑ n ∈ Ico 93568 93696, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (76 : ℕ) ∧
    (∑ n ∈ Ico 93568 93696, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (533752 : ℤ) ∧
    (∑ n ∈ Ico 93568 93696, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (10675103502164188073980811251 : ℤ) := by
  rcases cdemPrefixStats_93568_93632 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_93632_93696 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 93568 ≤ 93632) (by norm_num : 93632 ≤ 93696), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 93568 ≤ 93632) (by norm_num : 93632 ≤ 93696), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 93568 ≤ 93632) (by norm_num : 93632 ≤ 93696), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 93568 ≤ 93632) (by norm_num : 93632 ≤ 93696), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_93440_93696 :
    (∑ n ∈ Ico 93440 93696, mobiusTreeValue 16 mobiusTable1200001 n) = (9 : ℤ) ∧
    (∑ n ∈ Ico 93440 93696, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (153 : ℕ) ∧
    (∑ n ∈ Ico 93440 93696, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (480292 : ℤ) ∧
    (∑ n ∈ Ico 93440 93696, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (9605974546765322376819258582 : ℤ) := by
  rcases cdemPrefixStats_93440_93568 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_93568_93696 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 93440 ≤ 93568) (by norm_num : 93568 ≤ 93696), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 93440 ≤ 93568) (by norm_num : 93568 ≤ 93696), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 93440 ≤ 93568) (by norm_num : 93568 ≤ 93696), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 93440 ≤ 93568) (by norm_num : 93568 ≤ 93696), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_93184_93696 :
    (∑ n ∈ Ico 93184 93696, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 93184 93696, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (309 : ℕ) ∧
    (∑ n ∈ Ico 93184 93696, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (51068 : ℤ) ∧
    (∑ n ∈ Ico 93184 93696, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1021418586096901191013608844 : ℤ) := by
  rcases cdemPrefixStats_93184_93440 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_93440_93696 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 93184 ≤ 93440) (by norm_num : 93440 ≤ 93696), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 93184 ≤ 93440) (by norm_num : 93440 ≤ 93696), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 93184 ≤ 93440) (by norm_num : 93440 ≤ 93696), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 93184 ≤ 93440) (by norm_num : 93440 ≤ 93696), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_93696_93760 :
    (∑ n ∈ Ico 93696 93760, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 93696 93760, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 93696 93760, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-85 : ℤ) ∧
    (∑ n ∈ Ico 93696 93760, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-1798598837090188131318469 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_93760_93824 :
    (∑ n ∈ Ico 93760 93824, mobiusTreeValue 16 mobiusTable1200001 n) = (2 : ℤ) ∧
    (∑ n ∈ Ico 93760 93824, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 93760 93824, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (106609 : ℤ) ∧
    (∑ n ∈ Ico 93760 93824, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (2132207169005283238518087415 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_93696_93824 :
    (∑ n ∈ Ico 93696 93824, mobiusTreeValue 16 mobiusTable1200001 n) = (2 : ℤ) ∧
    (∑ n ∈ Ico 93696 93824, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (80 : ℕ) ∧
    (∑ n ∈ Ico 93696 93824, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (106524 : ℤ) ∧
    (∑ n ∈ Ico 93696 93824, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (2130408570168193050386768946 : ℤ) := by
  rcases cdemPrefixStats_93696_93760 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_93760_93824 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 93696 ≤ 93760) (by norm_num : 93760 ≤ 93824), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 93696 ≤ 93760) (by norm_num : 93760 ≤ 93824), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 93696 ≤ 93760) (by norm_num : 93760 ≤ 93824), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 93696 ≤ 93760) (by norm_num : 93760 ≤ 93824), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_93824_93888 :
    (∑ n ∈ Ico 93824 93888, mobiusTreeValue 16 mobiusTable1200001 n) = (4 : ℤ) ∧
    (∑ n ∈ Ico 93824 93888, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 93824 93888, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (213069 : ℤ) ∧
    (∑ n ∈ Ico 93824 93888, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (4261382788213358137325196149 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_93888_93952 :
    (∑ n ∈ Ico 93888 93952, mobiusTreeValue 16 mobiusTable1200001 n) = (-14 : ℤ) ∧
    (∑ n ∈ Ico 93888 93952, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 93888 93952, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-745307 : ℤ) ∧
    (∑ n ∈ Ico 93888 93952, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-14906269835872704284667436176 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_93824_93952 :
    (∑ n ∈ Ico 93824 93952, mobiusTreeValue 16 mobiusTable1200001 n) = (-10 : ℤ) ∧
    (∑ n ∈ Ico 93824 93952, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 93824 93952, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-532238 : ℤ) ∧
    (∑ n ∈ Ico 93824 93952, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-10644887047659346147342240027 : ℤ) := by
  rcases cdemPrefixStats_93824_93888 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_93888_93952 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 93824 ≤ 93888) (by norm_num : 93888 ≤ 93952), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 93824 ≤ 93888) (by norm_num : 93888 ≤ 93952), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 93824 ≤ 93888) (by norm_num : 93888 ≤ 93952), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 93824 ≤ 93888) (by norm_num : 93888 ≤ 93952), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_93696_93952 :
    (∑ n ∈ Ico 93696 93952, mobiusTreeValue 16 mobiusTable1200001 n) = (-8 : ℤ) ∧
    (∑ n ∈ Ico 93696 93952, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (158 : ℕ) ∧
    (∑ n ∈ Ico 93696 93952, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-425714 : ℤ) ∧
    (∑ n ∈ Ico 93696 93952, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-8514478477491153096955471081 : ℤ) := by
  rcases cdemPrefixStats_93696_93824 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_93824_93952 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 93696 ≤ 93824) (by norm_num : 93824 ≤ 93952), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 93696 ≤ 93824) (by norm_num : 93824 ≤ 93952), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 93696 ≤ 93824) (by norm_num : 93824 ≤ 93952), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 93696 ≤ 93824) (by norm_num : 93824 ≤ 93952), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_93952_94016 :
    (∑ n ∈ Ico 93952 94016, mobiusTreeValue 16 mobiusTable1200001 n) = (-3 : ℤ) ∧
    (∑ n ∈ Ico 93952 94016, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 93952 94016, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-159532 : ℤ) ∧
    (∑ n ∈ Ico 93952 94016, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-3190651332265938000189909474 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_94016_94080 :
    (∑ n ∈ Ico 94016 94080, mobiusTreeValue 16 mobiusTable1200001 n) = (-9 : ℤ) ∧
    (∑ n ∈ Ico 94016 94080, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 94016 94080, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-478445 : ℤ) ∧
    (∑ n ∈ Ico 94016 94080, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-9568971360396860102742287292 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_93952_94080 :
    (∑ n ∈ Ico 93952 94080, mobiusTreeValue 16 mobiusTable1200001 n) = (-12 : ℤ) ∧
    (∑ n ∈ Ico 93952 94080, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (80 : ℕ) ∧
    (∑ n ∈ Ico 93952 94080, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-637977 : ℤ) ∧
    (∑ n ∈ Ico 93952 94080, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-12759622692662798102932196766 : ℤ) := by
  rcases cdemPrefixStats_93952_94016 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_94016_94080 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 93952 ≤ 94016) (by norm_num : 94016 ≤ 94080), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 93952 ≤ 94016) (by norm_num : 94016 ≤ 94080), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 93952 ≤ 94016) (by norm_num : 94016 ≤ 94080), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 93952 ≤ 94016) (by norm_num : 94016 ≤ 94080), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_94080_94144 :
    (∑ n ∈ Ico 94080 94144, mobiusTreeValue 16 mobiusTable1200001 n) = (-2 : ℤ) ∧
    (∑ n ∈ Ico 94080 94144, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 94080 94144, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-106222 : ℤ) ∧
    (∑ n ∈ Ico 94080 94144, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-2124427458783178992950481263 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_94144_94208 :
    (∑ n ∈ Ico 94144 94208, mobiusTreeValue 16 mobiusTable1200001 n) = (2 : ℤ) ∧
    (∑ n ∈ Ico 94144 94208, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 94144 94208, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (106091 : ℤ) ∧
    (∑ n ∈ Ico 94144 94208, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (2121845147197427111351348927 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_94080_94208 :
    (∑ n ∈ Ico 94080 94208, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 94080 94208, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (76 : ℕ) ∧
    (∑ n ∈ Ico 94080 94208, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-131 : ℤ) ∧
    (∑ n ∈ Ico 94080 94208, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-2582311585751881599132336 : ℤ) := by
  rcases cdemPrefixStats_94080_94144 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_94144_94208 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 94080 ≤ 94144) (by norm_num : 94144 ≤ 94208), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 94080 ≤ 94144) (by norm_num : 94144 ≤ 94208), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 94080 ≤ 94144) (by norm_num : 94144 ≤ 94208), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 94080 ≤ 94144) (by norm_num : 94144 ≤ 94208), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_93952_94208 :
    (∑ n ∈ Ico 93952 94208, mobiusTreeValue 16 mobiusTable1200001 n) = (-12 : ℤ) ∧
    (∑ n ∈ Ico 93952 94208, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (156 : ℕ) ∧
    (∑ n ∈ Ico 93952 94208, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-638108 : ℤ) ∧
    (∑ n ∈ Ico 93952 94208, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-12762205004248549984531329102 : ℤ) := by
  rcases cdemPrefixStats_93952_94080 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_94080_94208 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 93952 ≤ 94080) (by norm_num : 94080 ≤ 94208), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 93952 ≤ 94080) (by norm_num : 94080 ≤ 94208), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 93952 ≤ 94080) (by norm_num : 94080 ≤ 94208), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 93952 ≤ 94080) (by norm_num : 94080 ≤ 94208), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_93696_94208 :
    (∑ n ∈ Ico 93696 94208, mobiusTreeValue 16 mobiusTable1200001 n) = (-20 : ℤ) ∧
    (∑ n ∈ Ico 93696 94208, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (314 : ℕ) ∧
    (∑ n ∈ Ico 93696 94208, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-1063822 : ℤ) ∧
    (∑ n ∈ Ico 93696 94208, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-21276683481739703081486800183 : ℤ) := by
  rcases cdemPrefixStats_93696_93952 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_93952_94208 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 93696 ≤ 93952) (by norm_num : 93952 ≤ 94208), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 93696 ≤ 93952) (by norm_num : 93952 ≤ 94208), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 93696 ≤ 93952) (by norm_num : 93952 ≤ 94208), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 93696 ≤ 93952) (by norm_num : 93952 ≤ 94208), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_93184_94208 :
    (∑ n ∈ Ico 93184 94208, mobiusTreeValue 16 mobiusTable1200001 n) = (-19 : ℤ) ∧
    (∑ n ∈ Ico 93184 94208, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (623 : ℕ) ∧
    (∑ n ∈ Ico 93184 94208, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-1012754 : ℤ) ∧
    (∑ n ∈ Ico 93184 94208, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-20255264895642801890473191339 : ℤ) := by
  rcases cdemPrefixStats_93184_93696 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_93696_94208 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 93184 ≤ 93696) (by norm_num : 93696 ≤ 94208), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 93184 ≤ 93696) (by norm_num : 93696 ≤ 94208), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 93184 ≤ 93696) (by norm_num : 93696 ≤ 94208), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 93184 ≤ 93696) (by norm_num : 93696 ≤ 94208), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_92160_94208 :
    (∑ n ∈ Ico 92160 94208, mobiusTreeValue 16 mobiusTable1200001 n) = (-68 : ℤ) ∧
    (∑ n ∈ Ico 92160 94208, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (1248 : ℕ) ∧
    (∑ n ∈ Ico 92160 94208, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-3657972 : ℤ) ∧
    (∑ n ∈ Ico 92160 94208, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-73160176907450627901968683887 : ℤ) := by
  rcases cdemPrefixStats_92160_93184 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_93184_94208 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 92160 ≤ 93184) (by norm_num : 93184 ≤ 94208), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 92160 ≤ 93184) (by norm_num : 93184 ≤ 94208), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 92160 ≤ 93184) (by norm_num : 93184 ≤ 94208), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 92160 ≤ 93184) (by norm_num : 93184 ≤ 94208), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_90112_94208 :
    (∑ n ∈ Ico 90112 94208, mobiusTreeValue 16 mobiusTable1200001 n) = (-62 : ℤ) ∧
    (∑ n ∈ Ico 90112 94208, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (2496 : ℕ) ∧
    (∑ n ∈ Ico 90112 94208, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-3317294 : ℤ) ∧
    (∑ n ∈ Ico 90112 94208, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-66346628080622312589865919477 : ℤ) := by
  rcases cdemPrefixStats_90112_92160 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_92160_94208 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 90112 ≤ 92160) (by norm_num : 92160 ≤ 94208), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 90112 ≤ 92160) (by norm_num : 92160 ≤ 94208), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 90112 ≤ 92160) (by norm_num : 92160 ≤ 94208), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 90112 ≤ 92160) (by norm_num : 92160 ≤ 94208), hR1, hR2] <;> norm_num

theorem cdemPrefixGroup022_checked_complete :
    (∑ n ∈ Ico 90112 94208, mobiusTreeValue 16 mobiusTable1200001 n) = (-62 : ℤ) ∧
    (∑ n ∈ Ico 90112 94208, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (2496 : ℕ) ∧
    (∑ n ∈ Ico 90112 94208, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-3317294 : ℤ) ∧
    (∑ n ∈ Ico 90112 94208, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-66346628080622312589865919477 : ℤ) := cdemPrefixStats_90112_94208
end Helfgott
#print axioms Helfgott.cdemPrefixGroup022_checked_complete

open Helfgott Finset
open scoped BigOperators

theorem solution :
    (∑ n ∈ Ico 90112 94208, mobiusTreeValue 16 mobiusTable1200001 n) = (-62 : ℤ) ∧
    (∑ n ∈ Ico 90112 94208, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (2496 : ℕ) ∧
    (∑ n ∈ Ico 90112 94208, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-3317294 : ℤ) ∧
    (∑ n ∈ Ico 90112 94208, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-66346628080622312589865919477 : ℤ) := Helfgott.cdemPrefixGroup022_checked_complete
#print axioms solution
