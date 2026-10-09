-- Prove2me | solution 1 for Helfgott.cdemPrefixGroup013_checked
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-09T01:40:33.169331+00:00
-- url     : https://prove2.me/submissions/11bf8342-446b-458c-a1e7-a583342dde68

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
private theorem cdemPrefixStats_53248_53312 :
    (∑ n ∈ Ico 53248 53312, mobiusTreeValue 16 mobiusTable1200001 n) = (2 : ℤ) ∧
    (∑ n ∈ Ico 53248 53312, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 53248 53312, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (187769 : ℤ) ∧
    (∑ n ∈ Ico 53248 53312, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (3755374364749159551124233855 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_53312_53376 :
    (∑ n ∈ Ico 53312 53376, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 53312 53376, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 53312 53376, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-326 : ℤ) ∧
    (∑ n ∈ Ico 53312 53376, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-6500773938226500802558474 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_53248_53376 :
    (∑ n ∈ Ico 53248 53376, mobiusTreeValue 16 mobiusTable1200001 n) = (2 : ℤ) ∧
    (∑ n ∈ Ico 53248 53376, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 53248 53376, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (187443 : ℤ) ∧
    (∑ n ∈ Ico 53248 53376, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (3748873590810933050321675381 : ℤ) := by
  rcases cdemPrefixStats_53248_53312 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_53312_53376 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 53248 ≤ 53312) (by norm_num : 53312 ≤ 53376), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 53248 ≤ 53312) (by norm_num : 53312 ≤ 53376), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 53248 ≤ 53312) (by norm_num : 53312 ≤ 53376), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 53248 ≤ 53312) (by norm_num : 53312 ≤ 53376), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_53376_53440 :
    (∑ n ∈ Ico 53376 53440, mobiusTreeValue 16 mobiusTable1200001 n) = (-5 : ℤ) ∧
    (∑ n ∈ Ico 53376 53440, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 53376 53440, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-468266 : ℤ) ∧
    (∑ n ∈ Ico 53376 53440, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-9365366212557895141758801932 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_53440_53504 :
    (∑ n ∈ Ico 53440 53504, mobiusTreeValue 16 mobiusTable1200001 n) = (4 : ℤ) ∧
    (∑ n ∈ Ico 53440 53504, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 53440 53504, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (374107 : ℤ) ∧
    (∑ n ∈ Ico 53440 53504, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (7482159260613431065635171060 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_53376_53504 :
    (∑ n ∈ Ico 53376 53504, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 53376 53504, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 53376 53504, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-94159 : ℤ) ∧
    (∑ n ∈ Ico 53376 53504, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-1883206951944464076123630872 : ℤ) := by
  rcases cdemPrefixStats_53376_53440 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_53440_53504 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 53376 ≤ 53440) (by norm_num : 53440 ≤ 53504), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 53376 ≤ 53440) (by norm_num : 53440 ≤ 53504), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 53376 ≤ 53440) (by norm_num : 53440 ≤ 53504), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 53376 ≤ 53440) (by norm_num : 53440 ≤ 53504), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_53248_53504 :
    (∑ n ∈ Ico 53248 53504, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 53248 53504, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (155 : ℕ) ∧
    (∑ n ∈ Ico 53248 53504, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (93284 : ℤ) ∧
    (∑ n ∈ Ico 53248 53504, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1865666638866468974198044509 : ℤ) := by
  rcases cdemPrefixStats_53248_53376 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_53376_53504 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 53248 ≤ 53376) (by norm_num : 53376 ≤ 53504), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 53248 ≤ 53376) (by norm_num : 53376 ≤ 53504), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 53248 ≤ 53376) (by norm_num : 53376 ≤ 53504), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 53248 ≤ 53376) (by norm_num : 53376 ≤ 53504), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_53504_53568 :
    (∑ n ∈ Ico 53504 53568, mobiusTreeValue 16 mobiusTable1200001 n) = (4 : ℤ) ∧
    (∑ n ∈ Ico 53504 53568, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 53504 53568, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (373577 : ℤ) ∧
    (∑ n ∈ Ico 53504 53568, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (7471608924634160104311550705 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_53568_53632 :
    (∑ n ∈ Ico 53568 53632, mobiusTreeValue 16 mobiusTable1200001 n) = (-8 : ℤ) ∧
    (∑ n ∈ Ico 53568 53632, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (36 : ℕ) ∧
    (∑ n ∈ Ico 53568 53632, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-746221 : ℤ) ∧
    (∑ n ∈ Ico 53568 53632, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-14924504192770399359261945940 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_53504_53632 :
    (∑ n ∈ Ico 53504 53632, mobiusTreeValue 16 mobiusTable1200001 n) = (-4 : ℤ) ∧
    (∑ n ∈ Ico 53504 53632, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (76 : ℕ) ∧
    (∑ n ∈ Ico 53504 53632, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-372644 : ℤ) ∧
    (∑ n ∈ Ico 53504 53632, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-7452895268136239254950395235 : ℤ) := by
  rcases cdemPrefixStats_53504_53568 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_53568_53632 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 53504 ≤ 53568) (by norm_num : 53568 ≤ 53632), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 53504 ≤ 53568) (by norm_num : 53568 ≤ 53632), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 53504 ≤ 53568) (by norm_num : 53568 ≤ 53632), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 53504 ≤ 53568) (by norm_num : 53568 ≤ 53632), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_53632_53696 :
    (∑ n ∈ Ico 53632 53696, mobiusTreeValue 16 mobiusTable1200001 n) = (2 : ℤ) ∧
    (∑ n ∈ Ico 53632 53696, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 53632 53696, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (186150 : ℤ) ∧
    (∑ n ∈ Ico 53632 53696, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (3723037384051484337133083948 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_53696_53760 :
    (∑ n ∈ Ico 53696 53760, mobiusTreeValue 16 mobiusTable1200001 n) = (2 : ℤ) ∧
    (∑ n ∈ Ico 53696 53760, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 53696 53760, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (185997 : ℤ) ∧
    (∑ n ∈ Ico 53696 53760, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (3719959414866255296522597643 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_53632_53760 :
    (∑ n ∈ Ico 53632 53760, mobiusTreeValue 16 mobiusTable1200001 n) = (4 : ℤ) ∧
    (∑ n ∈ Ico 53632 53760, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 53632 53760, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (372147 : ℤ) ∧
    (∑ n ∈ Ico 53632 53760, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (7442996798917739633655681591 : ℤ) := by
  rcases cdemPrefixStats_53632_53696 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_53696_53760 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 53632 ≤ 53696) (by norm_num : 53696 ≤ 53760), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 53632 ≤ 53696) (by norm_num : 53696 ≤ 53760), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 53632 ≤ 53696) (by norm_num : 53696 ≤ 53760), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 53632 ≤ 53696) (by norm_num : 53696 ≤ 53760), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_53504_53760 :
    (∑ n ∈ Ico 53504 53760, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 53504 53760, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (154 : ℕ) ∧
    (∑ n ∈ Ico 53504 53760, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-497 : ℤ) ∧
    (∑ n ∈ Ico 53504 53760, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-9898469218499621294713644 : ℤ) := by
  rcases cdemPrefixStats_53504_53632 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_53632_53760 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 53504 ≤ 53632) (by norm_num : 53632 ≤ 53760), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 53504 ≤ 53632) (by norm_num : 53632 ≤ 53760), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 53504 ≤ 53632) (by norm_num : 53632 ≤ 53760), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 53504 ≤ 53632) (by norm_num : 53632 ≤ 53760), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_53248_53760 :
    (∑ n ∈ Ico 53248 53760, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 53248 53760, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (309 : ℕ) ∧
    (∑ n ∈ Ico 53248 53760, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (92787 : ℤ) ∧
    (∑ n ∈ Ico 53248 53760, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1855768169647969352903330865 : ℤ) := by
  rcases cdemPrefixStats_53248_53504 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_53504_53760 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 53248 ≤ 53504) (by norm_num : 53504 ≤ 53760), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 53248 ≤ 53504) (by norm_num : 53504 ≤ 53760), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 53248 ≤ 53504) (by norm_num : 53504 ≤ 53760), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 53248 ≤ 53504) (by norm_num : 53504 ≤ 53760), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_53760_53824 :
    (∑ n ∈ Ico 53760 53824, mobiusTreeValue 16 mobiusTable1200001 n) = (6 : ℤ) ∧
    (∑ n ∈ Ico 53760 53824, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (42 : ℕ) ∧
    (∑ n ∈ Ico 53760 53824, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (558101 : ℤ) ∧
    (∑ n ∈ Ico 53760 53824, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (11162095648925851018314776828 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_53824_53888 :
    (∑ n ∈ Ico 53824 53888, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 53824 53888, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 53824 53888, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-92710 : ℤ) ∧
    (∑ n ∈ Ico 53824 53888, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-1854183853239461921474776933 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_53760_53888 :
    (∑ n ∈ Ico 53760 53888, mobiusTreeValue 16 mobiusTable1200001 n) = (5 : ℤ) ∧
    (∑ n ∈ Ico 53760 53888, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (79 : ℕ) ∧
    (∑ n ∈ Ico 53760 53888, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (465391 : ℤ) ∧
    (∑ n ∈ Ico 53760 53888, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (9307911795686389096839999895 : ℤ) := by
  rcases cdemPrefixStats_53760_53824 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_53824_53888 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 53760 ≤ 53824) (by norm_num : 53824 ≤ 53888), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 53760 ≤ 53824) (by norm_num : 53824 ≤ 53888), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 53760 ≤ 53824) (by norm_num : 53824 ≤ 53888), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 53760 ≤ 53824) (by norm_num : 53824 ≤ 53888), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_53888_53952 :
    (∑ n ∈ Ico 53888 53952, mobiusTreeValue 16 mobiusTable1200001 n) = (3 : ℤ) ∧
    (∑ n ∈ Ico 53888 53952, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 53888 53952, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (278362 : ℤ) ∧
    (∑ n ∈ Ico 53888 53952, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (5567239217569256560718053422 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_53952_54016 :
    (∑ n ∈ Ico 53952 54016, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 53952 54016, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 53952 54016, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-92431 : ℤ) ∧
    (∑ n ∈ Ico 53952 54016, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-1848660949217461626386762852 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_53888_54016 :
    (∑ n ∈ Ico 53888 54016, mobiusTreeValue 16 mobiusTable1200001 n) = (2 : ℤ) ∧
    (∑ n ∈ Ico 53888 54016, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 53888 54016, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (185931 : ℤ) ∧
    (∑ n ∈ Ico 53888 54016, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (3718578268351794934331290570 : ℤ) := by
  rcases cdemPrefixStats_53888_53952 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_53952_54016 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 53888 ≤ 53952) (by norm_num : 53952 ≤ 54016), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 53888 ≤ 53952) (by norm_num : 53952 ≤ 54016), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 53888 ≤ 53952) (by norm_num : 53952 ≤ 54016), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 53888 ≤ 53952) (by norm_num : 53952 ≤ 54016), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_53760_54016 :
    (∑ n ∈ Ico 53760 54016, mobiusTreeValue 16 mobiusTable1200001 n) = (7 : ℤ) ∧
    (∑ n ∈ Ico 53760 54016, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (157 : ℕ) ∧
    (∑ n ∈ Ico 53760 54016, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (651322 : ℤ) ∧
    (∑ n ∈ Ico 53760 54016, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (13026490064038184031171290465 : ℤ) := by
  rcases cdemPrefixStats_53760_53888 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_53888_54016 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 53760 ≤ 53888) (by norm_num : 53888 ≤ 54016), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 53760 ≤ 53888) (by norm_num : 53888 ≤ 54016), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 53760 ≤ 53888) (by norm_num : 53888 ≤ 54016), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 53760 ≤ 53888) (by norm_num : 53888 ≤ 54016), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_54016_54080 :
    (∑ n ∈ Ico 54016 54080, mobiusTreeValue 16 mobiusTable1200001 n) = (2 : ℤ) ∧
    (∑ n ∈ Ico 54016 54080, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 54016 54080, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (185328 : ℤ) ∧
    (∑ n ∈ Ico 54016 54080, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (3706544745584894368520708444 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_54080_54144 :
    (∑ n ∈ Ico 54080 54144, mobiusTreeValue 16 mobiusTable1200001 n) = (6 : ℤ) ∧
    (∑ n ∈ Ico 54080 54144, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 54080 54144, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (554047 : ℤ) ∧
    (∑ n ∈ Ico 54080 54144, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (11080943290943006452568950738 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_54016_54144 :
    (∑ n ∈ Ico 54016 54144, mobiusTreeValue 16 mobiusTable1200001 n) = (8 : ℤ) ∧
    (∑ n ∈ Ico 54016 54144, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 54016 54144, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (739375 : ℤ) ∧
    (∑ n ∈ Ico 54016 54144, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (14787488036527900821089659182 : ℤ) := by
  rcases cdemPrefixStats_54016_54080 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_54080_54144 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 54016 ≤ 54080) (by norm_num : 54080 ≤ 54144), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 54016 ≤ 54080) (by norm_num : 54080 ≤ 54144), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 54016 ≤ 54080) (by norm_num : 54080 ≤ 54144), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 54016 ≤ 54080) (by norm_num : 54080 ≤ 54144), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_54144_54208 :
    (∑ n ∈ Ico 54144 54208, mobiusTreeValue 16 mobiusTable1200001 n) = (6 : ℤ) ∧
    (∑ n ∈ Ico 54144 54208, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 54144 54208, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (553856 : ℤ) ∧
    (∑ n ∈ Ico 54144 54208, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (11077197384181750363187802268 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_54208_54272 :
    (∑ n ∈ Ico 54208 54272, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 54208 54272, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 54208 54272, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (92236 : ℤ) ∧
    (∑ n ∈ Ico 54208 54272, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1844678483148944356196391862 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_54144_54272 :
    (∑ n ∈ Ico 54144 54272, mobiusTreeValue 16 mobiusTable1200001 n) = (7 : ℤ) ∧
    (∑ n ∈ Ico 54144 54272, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (79 : ℕ) ∧
    (∑ n ∈ Ico 54144 54272, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (646092 : ℤ) ∧
    (∑ n ∈ Ico 54144 54272, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (12921875867330694719384194130 : ℤ) := by
  rcases cdemPrefixStats_54144_54208 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_54208_54272 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 54144 ≤ 54208) (by norm_num : 54208 ≤ 54272), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 54144 ≤ 54208) (by norm_num : 54208 ≤ 54272), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 54144 ≤ 54208) (by norm_num : 54208 ≤ 54272), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 54144 ≤ 54208) (by norm_num : 54208 ≤ 54272), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_54016_54272 :
    (∑ n ∈ Ico 54016 54272, mobiusTreeValue 16 mobiusTable1200001 n) = (15 : ℤ) ∧
    (∑ n ∈ Ico 54016 54272, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (157 : ℕ) ∧
    (∑ n ∈ Ico 54016 54272, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (1385467 : ℤ) ∧
    (∑ n ∈ Ico 54016 54272, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (27709363903858595540473853312 : ℤ) := by
  rcases cdemPrefixStats_54016_54144 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_54144_54272 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 54016 ≤ 54144) (by norm_num : 54144 ≤ 54272), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 54016 ≤ 54144) (by norm_num : 54144 ≤ 54272), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 54016 ≤ 54144) (by norm_num : 54144 ≤ 54272), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 54016 ≤ 54144) (by norm_num : 54144 ≤ 54272), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_53760_54272 :
    (∑ n ∈ Ico 53760 54272, mobiusTreeValue 16 mobiusTable1200001 n) = (22 : ℤ) ∧
    (∑ n ∈ Ico 53760 54272, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (314 : ℕ) ∧
    (∑ n ∈ Ico 53760 54272, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (2036789 : ℤ) ∧
    (∑ n ∈ Ico 53760 54272, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (40735853967896779571645143777 : ℤ) := by
  rcases cdemPrefixStats_53760_54016 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_54016_54272 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 53760 ≤ 54016) (by norm_num : 54016 ≤ 54272), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 53760 ≤ 54016) (by norm_num : 54016 ≤ 54272), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 53760 ≤ 54016) (by norm_num : 54016 ≤ 54272), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 53760 ≤ 54016) (by norm_num : 54016 ≤ 54272), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_53248_54272 :
    (∑ n ∈ Ico 53248 54272, mobiusTreeValue 16 mobiusTable1200001 n) = (23 : ℤ) ∧
    (∑ n ∈ Ico 53248 54272, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (623 : ℕ) ∧
    (∑ n ∈ Ico 53248 54272, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (2129576 : ℤ) ∧
    (∑ n ∈ Ico 53248 54272, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (42591622137544748924548474642 : ℤ) := by
  rcases cdemPrefixStats_53248_53760 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_53760_54272 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 53248 ≤ 53760) (by norm_num : 53760 ≤ 54272), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 53248 ≤ 53760) (by norm_num : 53760 ≤ 54272), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 53248 ≤ 53760) (by norm_num : 53760 ≤ 54272), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 53248 ≤ 53760) (by norm_num : 53760 ≤ 54272), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_54272_54336 :
    (∑ n ∈ Ico 54272 54336, mobiusTreeValue 16 mobiusTable1200001 n) = (-7 : ℤ) ∧
    (∑ n ∈ Ico 54272 54336, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 54272 54336, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-644589 : ℤ) ∧
    (∑ n ∈ Ico 54272 54336, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-12891821484988974127525314195 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_54336_54400 :
    (∑ n ∈ Ico 54336 54400, mobiusTreeValue 16 mobiusTable1200001 n) = (-7 : ℤ) ∧
    (∑ n ∈ Ico 54336 54400, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 54336 54400, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-644005 : ℤ) ∧
    (∑ n ∈ Ico 54336 54400, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-12880194318221532212949842494 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_54272_54400 :
    (∑ n ∈ Ico 54272 54400, mobiusTreeValue 16 mobiusTable1200001 n) = (-14 : ℤ) ∧
    (∑ n ∈ Ico 54272 54400, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 54272 54400, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-1288594 : ℤ) ∧
    (∑ n ∈ Ico 54272 54400, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-25772015803210506340475156689 : ℤ) := by
  rcases cdemPrefixStats_54272_54336 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_54336_54400 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 54272 ≤ 54336) (by norm_num : 54336 ≤ 54400), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 54272 ≤ 54336) (by norm_num : 54336 ≤ 54400), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 54272 ≤ 54336) (by norm_num : 54336 ≤ 54400), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 54272 ≤ 54336) (by norm_num : 54336 ≤ 54400), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_54400_54464 :
    (∑ n ∈ Ico 54400 54464, mobiusTreeValue 16 mobiusTable1200001 n) = (-5 : ℤ) ∧
    (∑ n ∈ Ico 54400 54464, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 54400 54464, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-459565 : ℤ) ∧
    (∑ n ∈ Ico 54400 54464, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-9191310228442037505601382650 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_54464_54528 :
    (∑ n ∈ Ico 54464 54528, mobiusTreeValue 16 mobiusTable1200001 n) = (-9 : ℤ) ∧
    (∑ n ∈ Ico 54464 54528, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 54464 54528, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-825834 : ℤ) ∧
    (∑ n ∈ Ico 54464 54528, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-16516760313069080345849428243 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_54400_54528 :
    (∑ n ∈ Ico 54400 54528, mobiusTreeValue 16 mobiusTable1200001 n) = (-14 : ℤ) ∧
    (∑ n ∈ Ico 54400 54528, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 54400 54528, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-1285399 : ℤ) ∧
    (∑ n ∈ Ico 54400 54528, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-25708070541511117851450810893 : ℤ) := by
  rcases cdemPrefixStats_54400_54464 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_54464_54528 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 54400 ≤ 54464) (by norm_num : 54464 ≤ 54528), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 54400 ≤ 54464) (by norm_num : 54464 ≤ 54528), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 54400 ≤ 54464) (by norm_num : 54464 ≤ 54528), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 54400 ≤ 54464) (by norm_num : 54464 ≤ 54528), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_54272_54528 :
    (∑ n ∈ Ico 54272 54528, mobiusTreeValue 16 mobiusTable1200001 n) = (-28 : ℤ) ∧
    (∑ n ∈ Ico 54272 54528, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (156 : ℕ) ∧
    (∑ n ∈ Ico 54272 54528, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-2573993 : ℤ) ∧
    (∑ n ∈ Ico 54272 54528, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-51480086344721624191925967582 : ℤ) := by
  rcases cdemPrefixStats_54272_54400 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_54400_54528 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 54272 ≤ 54400) (by norm_num : 54400 ≤ 54528), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 54272 ≤ 54400) (by norm_num : 54400 ≤ 54528), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 54272 ≤ 54400) (by norm_num : 54400 ≤ 54528), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 54272 ≤ 54400) (by norm_num : 54400 ≤ 54528), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_54528_54592 :
    (∑ n ∈ Ico 54528 54592, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 54528 54592, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 54528 54592, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (91753 : ℤ) ∧
    (∑ n ∈ Ico 54528 54592, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1835062431341482079037788483 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_54592_54656 :
    (∑ n ∈ Ico 54592 54656, mobiusTreeValue 16 mobiusTable1200001 n) = (-6 : ℤ) ∧
    (∑ n ∈ Ico 54592 54656, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 54592 54656, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-549035 : ℤ) ∧
    (∑ n ∈ Ico 54592 54656, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-10980800225093387033959262227 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_54528_54656 :
    (∑ n ∈ Ico 54528 54656, mobiusTreeValue 16 mobiusTable1200001 n) = (-5 : ℤ) ∧
    (∑ n ∈ Ico 54528 54656, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 54528 54656, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-457282 : ℤ) ∧
    (∑ n ∈ Ico 54528 54656, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-9145737793751904954921473744 : ℤ) := by
  rcases cdemPrefixStats_54528_54592 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_54592_54656 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 54528 ≤ 54592) (by norm_num : 54592 ≤ 54656), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 54528 ≤ 54592) (by norm_num : 54592 ≤ 54656), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 54528 ≤ 54592) (by norm_num : 54592 ≤ 54656), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 54528 ≤ 54592) (by norm_num : 54592 ≤ 54656), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_54656_54720 :
    (∑ n ∈ Ico 54656 54720, mobiusTreeValue 16 mobiusTable1200001 n) = (7 : ℤ) ∧
    (∑ n ∈ Ico 54656 54720, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 54656 54720, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (640052 : ℤ) ∧
    (∑ n ∈ Ico 54656 54720, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (12801054656550771125302158919 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_54720_54784 :
    (∑ n ∈ Ico 54720 54784, mobiusTreeValue 16 mobiusTable1200001 n) = (2 : ℤ) ∧
    (∑ n ∈ Ico 54720 54784, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (36 : ℕ) ∧
    (∑ n ∈ Ico 54720 54784, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (182918 : ℤ) ∧
    (∑ n ∈ Ico 54720 54784, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (3658372533306533583325487977 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_54656_54784 :
    (∑ n ∈ Ico 54656 54784, mobiusTreeValue 16 mobiusTable1200001 n) = (9 : ℤ) ∧
    (∑ n ∈ Ico 54656 54784, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 54656 54784, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (822970 : ℤ) ∧
    (∑ n ∈ Ico 54656 54784, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (16459427189857304708627646896 : ℤ) := by
  rcases cdemPrefixStats_54656_54720 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_54720_54784 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 54656 ≤ 54720) (by norm_num : 54720 ≤ 54784), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 54656 ≤ 54720) (by norm_num : 54720 ≤ 54784), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 54656 ≤ 54720) (by norm_num : 54720 ≤ 54784), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 54656 ≤ 54720) (by norm_num : 54720 ≤ 54784), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_54528_54784 :
    (∑ n ∈ Ico 54528 54784, mobiusTreeValue 16 mobiusTable1200001 n) = (4 : ℤ) ∧
    (∑ n ∈ Ico 54528 54784, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (154 : ℕ) ∧
    (∑ n ∈ Ico 54528 54784, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (365688 : ℤ) ∧
    (∑ n ∈ Ico 54528 54784, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (7313689396105399753706173152 : ℤ) := by
  rcases cdemPrefixStats_54528_54656 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_54656_54784 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 54528 ≤ 54656) (by norm_num : 54656 ≤ 54784), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 54528 ≤ 54656) (by norm_num : 54656 ≤ 54784), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 54528 ≤ 54656) (by norm_num : 54656 ≤ 54784), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 54528 ≤ 54656) (by norm_num : 54656 ≤ 54784), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_54272_54784 :
    (∑ n ∈ Ico 54272 54784, mobiusTreeValue 16 mobiusTable1200001 n) = (-24 : ℤ) ∧
    (∑ n ∈ Ico 54272 54784, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (310 : ℕ) ∧
    (∑ n ∈ Ico 54272 54784, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-2208305 : ℤ) ∧
    (∑ n ∈ Ico 54272 54784, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-44166396948616224438219794430 : ℤ) := by
  rcases cdemPrefixStats_54272_54528 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_54528_54784 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 54272 ≤ 54528) (by norm_num : 54528 ≤ 54784), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 54272 ≤ 54528) (by norm_num : 54528 ≤ 54784), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 54272 ≤ 54528) (by norm_num : 54528 ≤ 54784), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 54272 ≤ 54528) (by norm_num : 54528 ≤ 54784), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_54784_54848 :
    (∑ n ∈ Ico 54784 54848, mobiusTreeValue 16 mobiusTable1200001 n) = (-4 : ℤ) ∧
    (∑ n ∈ Ico 54784 54848, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 54784 54848, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-364564 : ℤ) ∧
    (∑ n ∈ Ico 54784 54848, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-7291283704631822080015537516 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_54848_54912 :
    (∑ n ∈ Ico 54848 54912, mobiusTreeValue 16 mobiusTable1200001 n) = (4 : ℤ) ∧
    (∑ n ∈ Ico 54848 54912, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 54848 54912, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (364522 : ℤ) ∧
    (∑ n ∈ Ico 54848 54912, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (7290522942408407857974976302 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_54784_54912 :
    (∑ n ∈ Ico 54784 54912, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 54784 54912, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (80 : ℕ) ∧
    (∑ n ∈ Ico 54784 54912, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-42 : ℤ) ∧
    (∑ n ∈ Ico 54784 54912, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-760762223414222040561214 : ℤ) := by
  rcases cdemPrefixStats_54784_54848 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_54848_54912 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 54784 ≤ 54848) (by norm_num : 54848 ≤ 54912), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 54784 ≤ 54848) (by norm_num : 54848 ≤ 54912), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 54784 ≤ 54848) (by norm_num : 54848 ≤ 54912), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 54784 ≤ 54848) (by norm_num : 54848 ≤ 54912), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_54912_54976 :
    (∑ n ∈ Ico 54912 54976, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 54912 54976, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 54912 54976, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (180 : ℤ) ∧
    (∑ n ∈ Ico 54912 54976, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (3645044132861820727404657 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_54976_55040 :
    (∑ n ∈ Ico 54976 55040, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 54976 55040, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 54976 55040, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (90627 : ℤ) ∧
    (∑ n ∈ Ico 54976 55040, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1812563700002856266648021878 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_54912_55040 :
    (∑ n ∈ Ico 54912 55040, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 54912 55040, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 54912 55040, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (90807 : ℤ) ∧
    (∑ n ∈ Ico 54912 55040, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1816208744135718087375426535 : ℤ) := by
  rcases cdemPrefixStats_54912_54976 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_54976_55040 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 54912 ≤ 54976) (by norm_num : 54976 ≤ 55040), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 54912 ≤ 54976) (by norm_num : 54976 ≤ 55040), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 54912 ≤ 54976) (by norm_num : 54976 ≤ 55040), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 54912 ≤ 54976) (by norm_num : 54976 ≤ 55040), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_54784_55040 :
    (∑ n ∈ Ico 54784 55040, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 54784 55040, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (157 : ℕ) ∧
    (∑ n ∈ Ico 54784 55040, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (90765 : ℤ) ∧
    (∑ n ∈ Ico 54784 55040, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1815447981912303865334865321 : ℤ) := by
  rcases cdemPrefixStats_54784_54912 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_54912_55040 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 54784 ≤ 54912) (by norm_num : 54912 ≤ 55040), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 54784 ≤ 54912) (by norm_num : 54912 ≤ 55040), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 54784 ≤ 54912) (by norm_num : 54912 ≤ 55040), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 54784 ≤ 54912) (by norm_num : 54912 ≤ 55040), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_55040_55104 :
    (∑ n ∈ Ico 55040 55104, mobiusTreeValue 16 mobiusTable1200001 n) = (-3 : ℤ) ∧
    (∑ n ∈ Ico 55040 55104, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 55040 55104, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-272620 : ℤ) ∧
    (∑ n ∈ Ico 55040 55104, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-5452393326263750938392048764 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_55104_55168 :
    (∑ n ∈ Ico 55104 55168, mobiusTreeValue 16 mobiusTable1200001 n) = (4 : ℤ) ∧
    (∑ n ∈ Ico 55104 55168, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (42 : ℕ) ∧
    (∑ n ∈ Ico 55104 55168, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (362320 : ℤ) ∧
    (∑ n ∈ Ico 55104 55168, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (7246433359552363796943585717 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_55040_55168 :
    (∑ n ∈ Ico 55040 55168, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 55040 55168, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (81 : ℕ) ∧
    (∑ n ∈ Ico 55040 55168, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (89700 : ℤ) ∧
    (∑ n ∈ Ico 55040 55168, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1794040033288612858551536953 : ℤ) := by
  rcases cdemPrefixStats_55040_55104 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_55104_55168 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 55040 ≤ 55104) (by norm_num : 55104 ≤ 55168), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 55040 ≤ 55104) (by norm_num : 55104 ≤ 55168), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 55040 ≤ 55104) (by norm_num : 55104 ≤ 55168), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 55040 ≤ 55104) (by norm_num : 55104 ≤ 55168), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_55168_55232 :
    (∑ n ∈ Ico 55168 55232, mobiusTreeValue 16 mobiusTable1200001 n) = (-8 : ℤ) ∧
    (∑ n ∈ Ico 55168 55232, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 55168 55232, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-724276 : ℤ) ∧
    (∑ n ∈ Ico 55168 55232, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-14485502630011802919082621468 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_55232_55296 :
    (∑ n ∈ Ico 55232 55296, mobiusTreeValue 16 mobiusTable1200001 n) = (3 : ℤ) ∧
    (∑ n ∈ Ico 55232 55296, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 55232 55296, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (271334 : ℤ) ∧
    (∑ n ∈ Ico 55232 55296, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (5426787526978654104611812193 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_55168_55296 :
    (∑ n ∈ Ico 55168 55296, mobiusTreeValue 16 mobiusTable1200001 n) = (-5 : ℤ) ∧
    (∑ n ∈ Ico 55168 55296, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 55168 55296, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-452942 : ℤ) ∧
    (∑ n ∈ Ico 55168 55296, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-9058715103033148814470809275 : ℤ) := by
  rcases cdemPrefixStats_55168_55232 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_55232_55296 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 55168 ≤ 55232) (by norm_num : 55232 ≤ 55296), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 55168 ≤ 55232) (by norm_num : 55232 ≤ 55296), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 55168 ≤ 55232) (by norm_num : 55232 ≤ 55296), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 55168 ≤ 55232) (by norm_num : 55232 ≤ 55296), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_55040_55296 :
    (∑ n ∈ Ico 55040 55296, mobiusTreeValue 16 mobiusTable1200001 n) = (-4 : ℤ) ∧
    (∑ n ∈ Ico 55040 55296, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (158 : ℕ) ∧
    (∑ n ∈ Ico 55040 55296, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-363242 : ℤ) ∧
    (∑ n ∈ Ico 55040 55296, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-7264675069744535955919272322 : ℤ) := by
  rcases cdemPrefixStats_55040_55168 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_55168_55296 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 55040 ≤ 55168) (by norm_num : 55168 ≤ 55296), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 55040 ≤ 55168) (by norm_num : 55168 ≤ 55296), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 55040 ≤ 55168) (by norm_num : 55168 ≤ 55296), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 55040 ≤ 55168) (by norm_num : 55168 ≤ 55296), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_54784_55296 :
    (∑ n ∈ Ico 54784 55296, mobiusTreeValue 16 mobiusTable1200001 n) = (-3 : ℤ) ∧
    (∑ n ∈ Ico 54784 55296, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (315 : ℕ) ∧
    (∑ n ∈ Ico 54784 55296, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-272477 : ℤ) ∧
    (∑ n ∈ Ico 54784 55296, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-5449227087832232090584407001 : ℤ) := by
  rcases cdemPrefixStats_54784_55040 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_55040_55296 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 54784 ≤ 55040) (by norm_num : 55040 ≤ 55296), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 54784 ≤ 55040) (by norm_num : 55040 ≤ 55296), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 54784 ≤ 55040) (by norm_num : 55040 ≤ 55296), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 54784 ≤ 55040) (by norm_num : 55040 ≤ 55296), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_54272_55296 :
    (∑ n ∈ Ico 54272 55296, mobiusTreeValue 16 mobiusTable1200001 n) = (-27 : ℤ) ∧
    (∑ n ∈ Ico 54272 55296, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (625 : ℕ) ∧
    (∑ n ∈ Ico 54272 55296, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-2480782 : ℤ) ∧
    (∑ n ∈ Ico 54272 55296, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-49615624036448456528804201431 : ℤ) := by
  rcases cdemPrefixStats_54272_54784 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_54784_55296 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 54272 ≤ 54784) (by norm_num : 54784 ≤ 55296), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 54272 ≤ 54784) (by norm_num : 54784 ≤ 55296), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 54272 ≤ 54784) (by norm_num : 54784 ≤ 55296), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 54272 ≤ 54784) (by norm_num : 54784 ≤ 55296), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_53248_55296 :
    (∑ n ∈ Ico 53248 55296, mobiusTreeValue 16 mobiusTable1200001 n) = (-4 : ℤ) ∧
    (∑ n ∈ Ico 53248 55296, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (1248 : ℕ) ∧
    (∑ n ∈ Ico 53248 55296, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-351206 : ℤ) ∧
    (∑ n ∈ Ico 53248 55296, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-7024001898903707604255726789 : ℤ) := by
  rcases cdemPrefixStats_53248_54272 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_54272_55296 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 53248 ≤ 54272) (by norm_num : 54272 ≤ 55296), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 53248 ≤ 54272) (by norm_num : 54272 ≤ 55296), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 53248 ≤ 54272) (by norm_num : 54272 ≤ 55296), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 53248 ≤ 54272) (by norm_num : 54272 ≤ 55296), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_55296_55360 :
    (∑ n ∈ Ico 55296 55360, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 55296 55360, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 55296 55360, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-90305 : ℤ) ∧
    (∑ n ∈ Ico 55296 55360, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-1806127746506571191601234110 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_55360_55424 :
    (∑ n ∈ Ico 55360 55424, mobiusTreeValue 16 mobiusTable1200001 n) = (11 : ℤ) ∧
    (∑ n ∈ Ico 55360 55424, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 55360 55424, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (992779 : ℤ) ∧
    (∑ n ∈ Ico 55360 55424, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (19855629042619298693514274112 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_55296_55424 :
    (∑ n ∈ Ico 55296 55424, mobiusTreeValue 16 mobiusTable1200001 n) = (10 : ℤ) ∧
    (∑ n ∈ Ico 55296 55424, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 55296 55424, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (902474 : ℤ) ∧
    (∑ n ∈ Ico 55296 55424, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (18049501296112727501913040002 : ℤ) := by
  rcases cdemPrefixStats_55296_55360 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_55360_55424 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 55296 ≤ 55360) (by norm_num : 55360 ≤ 55424), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 55296 ≤ 55360) (by norm_num : 55360 ≤ 55424), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 55296 ≤ 55360) (by norm_num : 55360 ≤ 55424), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 55296 ≤ 55360) (by norm_num : 55360 ≤ 55424), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_55424_55488 :
    (∑ n ∈ Ico 55424 55488, mobiusTreeValue 16 mobiusTable1200001 n) = (8 : ℤ) ∧
    (∑ n ∈ Ico 55424 55488, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (36 : ℕ) ∧
    (∑ n ∈ Ico 55424 55488, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (721103 : ℤ) ∧
    (∑ n ∈ Ico 55424 55488, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (14422180155351384910015965141 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_55488_55552 :
    (∑ n ∈ Ico 55488 55552, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 55488 55552, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 55488 55552, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (5 : ℤ) ∧
    (∑ n ∈ Ico 55488 55552, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (130385342138579045033835 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_55424_55552 :
    (∑ n ∈ Ico 55424 55552, mobiusTreeValue 16 mobiusTable1200001 n) = (8 : ℤ) ∧
    (∑ n ∈ Ico 55424 55552, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (74 : ℕ) ∧
    (∑ n ∈ Ico 55424 55552, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (721108 : ℤ) ∧
    (∑ n ∈ Ico 55424 55552, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (14422310540693523489060998976 : ℤ) := by
  rcases cdemPrefixStats_55424_55488 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_55488_55552 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 55424 ≤ 55488) (by norm_num : 55488 ≤ 55552), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 55424 ≤ 55488) (by norm_num : 55488 ≤ 55552), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 55424 ≤ 55488) (by norm_num : 55488 ≤ 55552), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 55424 ≤ 55488) (by norm_num : 55488 ≤ 55552), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_55296_55552 :
    (∑ n ∈ Ico 55296 55552, mobiusTreeValue 16 mobiusTable1200001 n) = (18 : ℤ) ∧
    (∑ n ∈ Ico 55296 55552, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (152 : ℕ) ∧
    (∑ n ∈ Ico 55296 55552, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (1623582 : ℤ) ∧
    (∑ n ∈ Ico 55296 55552, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (32471811836806250990974038978 : ℤ) := by
  rcases cdemPrefixStats_55296_55424 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_55424_55552 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 55296 ≤ 55424) (by norm_num : 55424 ≤ 55552), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 55296 ≤ 55424) (by norm_num : 55424 ≤ 55552), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 55296 ≤ 55424) (by norm_num : 55424 ≤ 55552), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 55296 ≤ 55424) (by norm_num : 55424 ≤ 55552), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_55552_55616 :
    (∑ n ∈ Ico 55552 55616, mobiusTreeValue 16 mobiusTable1200001 n) = (9 : ℤ) ∧
    (∑ n ∈ Ico 55552 55616, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 55552 55616, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (809701 : ℤ) ∧
    (∑ n ∈ Ico 55552 55616, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (16194107797493696353995858968 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_55616_55680 :
    (∑ n ∈ Ico 55616 55680, mobiusTreeValue 16 mobiusTable1200001 n) = (-4 : ℤ) ∧
    (∑ n ∈ Ico 55616 55680, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 55616 55680, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-359452 : ℤ) ∧
    (∑ n ∈ Ico 55616 55680, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-7189039422910647677415845679 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_55552_55680 :
    (∑ n ∈ Ico 55552 55680, mobiusTreeValue 16 mobiusTable1200001 n) = (5 : ℤ) ∧
    (∑ n ∈ Ico 55552 55680, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (79 : ℕ) ∧
    (∑ n ∈ Ico 55552 55680, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (450249 : ℤ) ∧
    (∑ n ∈ Ico 55552 55680, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (9005068374583048676580013289 : ℤ) := by
  rcases cdemPrefixStats_55552_55616 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_55616_55680 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 55552 ≤ 55616) (by norm_num : 55616 ≤ 55680), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 55552 ≤ 55616) (by norm_num : 55616 ≤ 55680), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 55552 ≤ 55616) (by norm_num : 55616 ≤ 55680), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 55552 ≤ 55616) (by norm_num : 55616 ≤ 55680), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_55680_55744 :
    (∑ n ∈ Ico 55680 55744, mobiusTreeValue 16 mobiusTable1200001 n) = (-12 : ℤ) ∧
    (∑ n ∈ Ico 55680 55744, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 55680 55744, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-1077071 : ℤ) ∧
    (∑ n ∈ Ico 55680 55744, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-21541473912050034812887699770 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_55744_55808 :
    (∑ n ∈ Ico 55744 55808, mobiusTreeValue 16 mobiusTable1200001 n) = (4 : ℤ) ∧
    (∑ n ∈ Ico 55744 55808, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (36 : ℕ) ∧
    (∑ n ∈ Ico 55744 55808, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (358596 : ℤ) ∧
    (∑ n ∈ Ico 55744 55808, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (7171931844332342798293907695 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_55680_55808 :
    (∑ n ∈ Ico 55680 55808, mobiusTreeValue 16 mobiusTable1200001 n) = (-8 : ℤ) ∧
    (∑ n ∈ Ico 55680 55808, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (76 : ℕ) ∧
    (∑ n ∈ Ico 55680 55808, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-718475 : ℤ) ∧
    (∑ n ∈ Ico 55680 55808, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-14369542067717692014593792075 : ℤ) := by
  rcases cdemPrefixStats_55680_55744 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_55744_55808 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 55680 ≤ 55744) (by norm_num : 55744 ≤ 55808), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 55680 ≤ 55744) (by norm_num : 55744 ≤ 55808), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 55680 ≤ 55744) (by norm_num : 55744 ≤ 55808), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 55680 ≤ 55744) (by norm_num : 55744 ≤ 55808), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_55552_55808 :
    (∑ n ∈ Ico 55552 55808, mobiusTreeValue 16 mobiusTable1200001 n) = (-3 : ℤ) ∧
    (∑ n ∈ Ico 55552 55808, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (155 : ℕ) ∧
    (∑ n ∈ Ico 55552 55808, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-268226 : ℤ) ∧
    (∑ n ∈ Ico 55552 55808, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-5364473693134643338013778786 : ℤ) := by
  rcases cdemPrefixStats_55552_55680 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_55680_55808 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 55552 ≤ 55680) (by norm_num : 55680 ≤ 55808), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 55552 ≤ 55680) (by norm_num : 55680 ≤ 55808), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 55552 ≤ 55680) (by norm_num : 55680 ≤ 55808), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 55552 ≤ 55680) (by norm_num : 55680 ≤ 55808), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_55296_55808 :
    (∑ n ∈ Ico 55296 55808, mobiusTreeValue 16 mobiusTable1200001 n) = (15 : ℤ) ∧
    (∑ n ∈ Ico 55296 55808, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (307 : ℕ) ∧
    (∑ n ∈ Ico 55296 55808, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (1355356 : ℤ) ∧
    (∑ n ∈ Ico 55296 55808, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (27107338143671607652960260192 : ℤ) := by
  rcases cdemPrefixStats_55296_55552 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_55552_55808 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 55296 ≤ 55552) (by norm_num : 55552 ≤ 55808), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 55296 ≤ 55552) (by norm_num : 55552 ≤ 55808), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 55296 ≤ 55552) (by norm_num : 55552 ≤ 55808), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 55296 ≤ 55552) (by norm_num : 55552 ≤ 55808), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_55808_55872 :
    (∑ n ∈ Ico 55808 55872, mobiusTreeValue 16 mobiusTable1200001 n) = (-6 : ℤ) ∧
    (∑ n ∈ Ico 55808 55872, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 55808 55872, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-537377 : ℤ) ∧
    (∑ n ∈ Ico 55808 55872, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-10747585319029957546925040222 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_55872_55936 :
    (∑ n ∈ Ico 55872 55936, mobiusTreeValue 16 mobiusTable1200001 n) = (-6 : ℤ) ∧
    (∑ n ∈ Ico 55872 55936, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 55872 55936, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-536303 : ℤ) ∧
    (∑ n ∈ Ico 55872 55936, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-10726125189152988547676895073 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_55808_55936 :
    (∑ n ∈ Ico 55808 55936, mobiusTreeValue 16 mobiusTable1200001 n) = (-12 : ℤ) ∧
    (∑ n ∈ Ico 55808 55936, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (76 : ℕ) ∧
    (∑ n ∈ Ico 55808 55936, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-1073680 : ℤ) ∧
    (∑ n ∈ Ico 55808 55936, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-21473710508182946094601935295 : ℤ) := by
  rcases cdemPrefixStats_55808_55872 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_55872_55936 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 55808 ≤ 55872) (by norm_num : 55872 ≤ 55936), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 55808 ≤ 55872) (by norm_num : 55872 ≤ 55936), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 55808 ≤ 55872) (by norm_num : 55872 ≤ 55936), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 55808 ≤ 55872) (by norm_num : 55872 ≤ 55936), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_55936_56000 :
    (∑ n ∈ Ico 55936 56000, mobiusTreeValue 16 mobiusTable1200001 n) = (-8 : ℤ) ∧
    (∑ n ∈ Ico 55936 56000, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 55936 56000, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-714831 : ℤ) ∧
    (∑ n ∈ Ico 55936 56000, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-14296630914408731986900144414 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_56000_56064 :
    (∑ n ∈ Ico 56000 56064, mobiusTreeValue 16 mobiusTable1200001 n) = (-3 : ℤ) ∧
    (∑ n ∈ Ico 56000 56064, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 56000 56064, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-268115 : ℤ) ∧
    (∑ n ∈ Ico 56000 56064, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-5362268910081762444475610323 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_55936_56064 :
    (∑ n ∈ Ico 55936 56064, mobiusTreeValue 16 mobiusTable1200001 n) = (-11 : ℤ) ∧
    (∑ n ∈ Ico 55936 56064, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (79 : ℕ) ∧
    (∑ n ∈ Ico 55936 56064, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-982946 : ℤ) ∧
    (∑ n ∈ Ico 55936 56064, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-19658899824490494431375754737 : ℤ) := by
  rcases cdemPrefixStats_55936_56000 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_56000_56064 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 55936 ≤ 56000) (by norm_num : 56000 ≤ 56064), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 55936 ≤ 56000) (by norm_num : 56000 ≤ 56064), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 55936 ≤ 56000) (by norm_num : 56000 ≤ 56064), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 55936 ≤ 56000) (by norm_num : 56000 ≤ 56064), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_55808_56064 :
    (∑ n ∈ Ico 55808 56064, mobiusTreeValue 16 mobiusTable1200001 n) = (-23 : ℤ) ∧
    (∑ n ∈ Ico 55808 56064, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (155 : ℕ) ∧
    (∑ n ∈ Ico 55808 56064, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-2056626 : ℤ) ∧
    (∑ n ∈ Ico 55808 56064, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-41132610332673440525977690032 : ℤ) := by
  rcases cdemPrefixStats_55808_55936 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_55936_56064 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 55808 ≤ 55936) (by norm_num : 55936 ≤ 56064), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 55808 ≤ 55936) (by norm_num : 55936 ≤ 56064), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 55808 ≤ 55936) (by norm_num : 55936 ≤ 56064), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 55808 ≤ 55936) (by norm_num : 55936 ≤ 56064), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_56064_56128 :
    (∑ n ∈ Ico 56064 56128, mobiusTreeValue 16 mobiusTable1200001 n) = (-2 : ℤ) ∧
    (∑ n ∈ Ico 56064 56128, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 56064 56128, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-178279 : ℤ) ∧
    (∑ n ∈ Ico 56064 56128, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-3565634225980279819011751289 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_56128_56192 :
    (∑ n ∈ Ico 56128 56192, mobiusTreeValue 16 mobiusTable1200001 n) = (-2 : ℤ) ∧
    (∑ n ∈ Ico 56128 56192, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 56128 56192, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-177829 : ℤ) ∧
    (∑ n ∈ Ico 56128 56192, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-3556623803776556968462908512 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_56064_56192 :
    (∑ n ∈ Ico 56064 56192, mobiusTreeValue 16 mobiusTable1200001 n) = (-4 : ℤ) ∧
    (∑ n ∈ Ico 56064 56192, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (76 : ℕ) ∧
    (∑ n ∈ Ico 56064 56192, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-356108 : ℤ) ∧
    (∑ n ∈ Ico 56064 56192, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-7122258029756836787474659801 : ℤ) := by
  rcases cdemPrefixStats_56064_56128 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_56128_56192 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 56064 ≤ 56128) (by norm_num : 56128 ≤ 56192), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 56064 ≤ 56128) (by norm_num : 56128 ≤ 56192), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 56064 ≤ 56128) (by norm_num : 56128 ≤ 56192), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 56064 ≤ 56128) (by norm_num : 56128 ≤ 56192), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_56192_56256 :
    (∑ n ∈ Ico 56192 56256, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 56192 56256, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 56192 56256, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-88768 : ℤ) ∧
    (∑ n ∈ Ico 56192 56256, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-1775403868602787913015035834 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_56256_56320 :
    (∑ n ∈ Ico 56256 56320, mobiusTreeValue 16 mobiusTable1200001 n) = (3 : ℤ) ∧
    (∑ n ∈ Ico 56256 56320, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 56256 56320, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (266440 : ℤ) ∧
    (∑ n ∈ Ico 56256 56320, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (5328848557432772857762751934 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_56192_56320 :
    (∑ n ∈ Ico 56192 56320, mobiusTreeValue 16 mobiusTable1200001 n) = (2 : ℤ) ∧
    (∑ n ∈ Ico 56192 56320, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (80 : ℕ) ∧
    (∑ n ∈ Ico 56192 56320, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (177672 : ℤ) ∧
    (∑ n ∈ Ico 56192 56320, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (3553444688829984944747716100 : ℤ) := by
  rcases cdemPrefixStats_56192_56256 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_56256_56320 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 56192 ≤ 56256) (by norm_num : 56256 ≤ 56320), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 56192 ≤ 56256) (by norm_num : 56256 ≤ 56320), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 56192 ≤ 56256) (by norm_num : 56256 ≤ 56320), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 56192 ≤ 56256) (by norm_num : 56256 ≤ 56320), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_56064_56320 :
    (∑ n ∈ Ico 56064 56320, mobiusTreeValue 16 mobiusTable1200001 n) = (-2 : ℤ) ∧
    (∑ n ∈ Ico 56064 56320, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (156 : ℕ) ∧
    (∑ n ∈ Ico 56064 56320, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-178436 : ℤ) ∧
    (∑ n ∈ Ico 56064 56320, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-3568813340926851842726943701 : ℤ) := by
  rcases cdemPrefixStats_56064_56192 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_56192_56320 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 56064 ≤ 56192) (by norm_num : 56192 ≤ 56320), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 56064 ≤ 56192) (by norm_num : 56192 ≤ 56320), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 56064 ≤ 56192) (by norm_num : 56192 ≤ 56320), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 56064 ≤ 56192) (by norm_num : 56192 ≤ 56320), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_55808_56320 :
    (∑ n ∈ Ico 55808 56320, mobiusTreeValue 16 mobiusTable1200001 n) = (-25 : ℤ) ∧
    (∑ n ∈ Ico 55808 56320, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (311 : ℕ) ∧
    (∑ n ∈ Ico 55808 56320, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-2235062 : ℤ) ∧
    (∑ n ∈ Ico 55808 56320, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-44701423673600292368704633733 : ℤ) := by
  rcases cdemPrefixStats_55808_56064 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_56064_56320 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 55808 ≤ 56064) (by norm_num : 56064 ≤ 56320), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 55808 ≤ 56064) (by norm_num : 56064 ≤ 56320), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 55808 ≤ 56064) (by norm_num : 56064 ≤ 56320), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 55808 ≤ 56064) (by norm_num : 56064 ≤ 56320), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_55296_56320 :
    (∑ n ∈ Ico 55296 56320, mobiusTreeValue 16 mobiusTable1200001 n) = (-10 : ℤ) ∧
    (∑ n ∈ Ico 55296 56320, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (618 : ℕ) ∧
    (∑ n ∈ Ico 55296 56320, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-879706 : ℤ) ∧
    (∑ n ∈ Ico 55296 56320, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-17594085529928684715744373541 : ℤ) := by
  rcases cdemPrefixStats_55296_55808 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_55808_56320 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 55296 ≤ 55808) (by norm_num : 55808 ≤ 56320), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 55296 ≤ 55808) (by norm_num : 55808 ≤ 56320), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 55296 ≤ 55808) (by norm_num : 55808 ≤ 56320), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 55296 ≤ 55808) (by norm_num : 55808 ≤ 56320), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_56320_56384 :
    (∑ n ∈ Ico 56320 56384, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 56320 56384, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 56320 56384, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (30 : ℤ) ∧
    (∑ n ∈ Ico 56320 56384, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (661658825249605146062465 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_56384_56448 :
    (∑ n ∈ Ico 56384 56448, mobiusTreeValue 16 mobiusTable1200001 n) = (-4 : ℤ) ∧
    (∑ n ∈ Ico 56384 56448, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 56384 56448, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-354639 : ℤ) ∧
    (∑ n ∈ Ico 56384 56448, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-7092826107622262022424044886 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_56320_56448 :
    (∑ n ∈ Ico 56320 56448, mobiusTreeValue 16 mobiusTable1200001 n) = (-4 : ℤ) ∧
    (∑ n ∈ Ico 56320 56448, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (76 : ℕ) ∧
    (∑ n ∈ Ico 56320 56448, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-354609 : ℤ) ∧
    (∑ n ∈ Ico 56320 56448, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-7092164448797012417277982421 : ℤ) := by
  rcases cdemPrefixStats_56320_56384 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_56384_56448 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 56320 ≤ 56384) (by norm_num : 56384 ≤ 56448), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 56320 ≤ 56384) (by norm_num : 56384 ≤ 56448), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 56320 ≤ 56384) (by norm_num : 56384 ≤ 56448), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 56320 ≤ 56384) (by norm_num : 56384 ≤ 56448), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_56448_56512 :
    (∑ n ∈ Ico 56448 56512, mobiusTreeValue 16 mobiusTable1200001 n) = (-14 : ℤ) ∧
    (∑ n ∈ Ico 56448 56512, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 56448 56512, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-1239168 : ℤ) ∧
    (∑ n ∈ Ico 56448 56512, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-24783525586044878715636310558 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_56512_56576 :
    (∑ n ∈ Ico 56512 56576, mobiusTreeValue 16 mobiusTable1200001 n) = (-11 : ℤ) ∧
    (∑ n ∈ Ico 56512 56576, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 56512 56576, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-972832 : ℤ) ∧
    (∑ n ∈ Ico 56512 56576, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-19456724514838923920481241885 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_56448_56576 :
    (∑ n ∈ Ico 56448 56576, mobiusTreeValue 16 mobiusTable1200001 n) = (-25 : ℤ) ∧
    (∑ n ∈ Ico 56448 56576, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 56448 56576, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-2212000 : ℤ) ∧
    (∑ n ∈ Ico 56448 56576, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-44240250100883802636117552443 : ℤ) := by
  rcases cdemPrefixStats_56448_56512 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_56512_56576 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 56448 ≤ 56512) (by norm_num : 56512 ≤ 56576), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 56448 ≤ 56512) (by norm_num : 56512 ≤ 56576), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 56448 ≤ 56512) (by norm_num : 56512 ≤ 56576), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 56448 ≤ 56512) (by norm_num : 56512 ≤ 56576), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_56320_56576 :
    (∑ n ∈ Ico 56320 56576, mobiusTreeValue 16 mobiusTable1200001 n) = (-29 : ℤ) ∧
    (∑ n ∈ Ico 56320 56576, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (153 : ℕ) ∧
    (∑ n ∈ Ico 56320 56576, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-2566609 : ℤ) ∧
    (∑ n ∈ Ico 56320 56576, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-51332414549680815053395534864 : ℤ) := by
  rcases cdemPrefixStats_56320_56448 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_56448_56576 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 56320 ≤ 56448) (by norm_num : 56448 ≤ 56576), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 56320 ≤ 56448) (by norm_num : 56448 ≤ 56576), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 56320 ≤ 56448) (by norm_num : 56448 ≤ 56576), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 56320 ≤ 56448) (by norm_num : 56448 ≤ 56576), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_56576_56640 :
    (∑ n ∈ Ico 56576 56640, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 56576 56640, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 56576 56640, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (88461 : ℤ) ∧
    (∑ n ∈ Ico 56576 56640, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1769155457752905440570220870 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_56640_56704 :
    (∑ n ∈ Ico 56640 56704, mobiusTreeValue 16 mobiusTable1200001 n) = (-6 : ℤ) ∧
    (∑ n ∈ Ico 56640 56704, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 56640 56704, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-529389 : ℤ) ∧
    (∑ n ∈ Ico 56640 56704, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-10587892175284289659385026693 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_56576_56704 :
    (∑ n ∈ Ico 56576 56704, mobiusTreeValue 16 mobiusTable1200001 n) = (-5 : ℤ) ∧
    (∑ n ∈ Ico 56576 56704, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 56576 56704, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-440928 : ℤ) ∧
    (∑ n ∈ Ico 56576 56704, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-8818736717531384218814805823 : ℤ) := by
  rcases cdemPrefixStats_56576_56640 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_56640_56704 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 56576 ≤ 56640) (by norm_num : 56640 ≤ 56704), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 56576 ≤ 56640) (by norm_num : 56640 ≤ 56704), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 56576 ≤ 56640) (by norm_num : 56640 ≤ 56704), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 56576 ≤ 56640) (by norm_num : 56640 ≤ 56704), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_56704_56768 :
    (∑ n ∈ Ico 56704 56768, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 56704 56768, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 56704 56768, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-25 : ℤ) ∧
    (∑ n ∈ Ico 56704 56768, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-434133643452797129269587 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_56768_56832 :
    (∑ n ∈ Ico 56768 56832, mobiusTreeValue 16 mobiusTable1200001 n) = (-8 : ℤ) ∧
    (∑ n ∈ Ico 56768 56832, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 56768 56832, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-704292 : ℤ) ∧
    (∑ n ∈ Ico 56768 56832, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-14085872086952142009711788270 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_56704_56832 :
    (∑ n ∈ Ico 56704 56832, mobiusTreeValue 16 mobiusTable1200001 n) = (-8 : ℤ) ∧
    (∑ n ∈ Ico 56704 56832, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 56704 56832, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-704317 : ℤ) ∧
    (∑ n ∈ Ico 56704 56832, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-14086306220595594806841057857 : ℤ) := by
  rcases cdemPrefixStats_56704_56768 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_56768_56832 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 56704 ≤ 56768) (by norm_num : 56768 ≤ 56832), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 56704 ≤ 56768) (by norm_num : 56768 ≤ 56832), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 56704 ≤ 56768) (by norm_num : 56768 ≤ 56832), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 56704 ≤ 56768) (by norm_num : 56768 ≤ 56832), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_56576_56832 :
    (∑ n ∈ Ico 56576 56832, mobiusTreeValue 16 mobiusTable1200001 n) = (-13 : ℤ) ∧
    (∑ n ∈ Ico 56576 56832, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (155 : ℕ) ∧
    (∑ n ∈ Ico 56576 56832, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-1145245 : ℤ) ∧
    (∑ n ∈ Ico 56576 56832, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-22905042938126979025655863680 : ℤ) := by
  rcases cdemPrefixStats_56576_56704 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_56704_56832 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 56576 ≤ 56704) (by norm_num : 56704 ≤ 56832), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 56576 ≤ 56704) (by norm_num : 56704 ≤ 56832), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 56576 ≤ 56704) (by norm_num : 56704 ≤ 56832), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 56576 ≤ 56704) (by norm_num : 56704 ≤ 56832), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_56320_56832 :
    (∑ n ∈ Ico 56320 56832, mobiusTreeValue 16 mobiusTable1200001 n) = (-42 : ℤ) ∧
    (∑ n ∈ Ico 56320 56832, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (308 : ℕ) ∧
    (∑ n ∈ Ico 56320 56832, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-3711854 : ℤ) ∧
    (∑ n ∈ Ico 56320 56832, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-74237457487807794079051398544 : ℤ) := by
  rcases cdemPrefixStats_56320_56576 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_56576_56832 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 56320 ≤ 56576) (by norm_num : 56576 ≤ 56832), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 56320 ≤ 56576) (by norm_num : 56576 ≤ 56832), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 56320 ≤ 56576) (by norm_num : 56576 ≤ 56832), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 56320 ≤ 56576) (by norm_num : 56576 ≤ 56832), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_56832_56896 :
    (∑ n ∈ Ico 56832 56896, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 56832 56896, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 56832 56896, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-31 : ℤ) ∧
    (∑ n ∈ Ico 56832 56896, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-588982288039476921042497 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_56896_56960 :
    (∑ n ∈ Ico 56896 56960, mobiusTreeValue 16 mobiusTable1200001 n) = (-19 : ℤ) ∧
    (∑ n ∈ Ico 56896 56960, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 56896 56960, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-1668818 : ℤ) ∧
    (∑ n ∈ Ico 56896 56960, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-33376575785988285246836439531 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_56832_56960 :
    (∑ n ∈ Ico 56832 56960, mobiusTreeValue 16 mobiusTable1200001 n) = (-19 : ℤ) ∧
    (∑ n ∈ Ico 56832 56960, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (79 : ℕ) ∧
    (∑ n ∈ Ico 56832 56960, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-1668849 : ℤ) ∧
    (∑ n ∈ Ico 56832 56960, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-33377164768276324723757482028 : ℤ) := by
  rcases cdemPrefixStats_56832_56896 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_56896_56960 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 56832 ≤ 56896) (by norm_num : 56896 ≤ 56960), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 56832 ≤ 56896) (by norm_num : 56896 ≤ 56960), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 56832 ≤ 56896) (by norm_num : 56896 ≤ 56960), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 56832 ≤ 56896) (by norm_num : 56896 ≤ 56960), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_56960_57024 :
    (∑ n ∈ Ico 56960 57024, mobiusTreeValue 16 mobiusTable1200001 n) = (-7 : ℤ) ∧
    (∑ n ∈ Ico 56960 57024, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 56960 57024, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-613967 : ℤ) ∧
    (∑ n ∈ Ico 56960 57024, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-12279379368225427864334751089 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_57024_57088 :
    (∑ n ∈ Ico 57024 57088, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 57024 57088, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 57024 57088, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (87701 : ℤ) ∧
    (∑ n ∈ Ico 57024 57088, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1754048732408367487343003247 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_56960_57088 :
    (∑ n ∈ Ico 56960 57088, mobiusTreeValue 16 mobiusTable1200001 n) = (-6 : ℤ) ∧
    (∑ n ∈ Ico 56960 57088, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (76 : ℕ) ∧
    (∑ n ∈ Ico 56960 57088, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-526266 : ℤ) ∧
    (∑ n ∈ Ico 56960 57088, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-10525330635817060376991747842 : ℤ) := by
  rcases cdemPrefixStats_56960_57024 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_57024_57088 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 56960 ≤ 57024) (by norm_num : 57024 ≤ 57088), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 56960 ≤ 57024) (by norm_num : 57024 ≤ 57088), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 56960 ≤ 57024) (by norm_num : 57024 ≤ 57088), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 56960 ≤ 57024) (by norm_num : 57024 ≤ 57088), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_56832_57088 :
    (∑ n ∈ Ico 56832 57088, mobiusTreeValue 16 mobiusTable1200001 n) = (-25 : ℤ) ∧
    (∑ n ∈ Ico 56832 57088, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (155 : ℕ) ∧
    (∑ n ∈ Ico 56832 57088, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-2195115 : ℤ) ∧
    (∑ n ∈ Ico 56832 57088, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-43902495404093385100749229870 : ℤ) := by
  rcases cdemPrefixStats_56832_56960 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_56960_57088 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 56832 ≤ 56960) (by norm_num : 56960 ≤ 57088), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 56832 ≤ 56960) (by norm_num : 56960 ≤ 57088), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 56832 ≤ 56960) (by norm_num : 56960 ≤ 57088), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 56832 ≤ 56960) (by norm_num : 56960 ≤ 57088), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_57088_57152 :
    (∑ n ∈ Ico 57088 57152, mobiusTreeValue 16 mobiusTable1200001 n) = (-5 : ℤ) ∧
    (∑ n ∈ Ico 57088 57152, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 57088 57152, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-437729 : ℤ) ∧
    (∑ n ∈ Ico 57088 57152, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-8754636180200419303167981440 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_57152_57216 :
    (∑ n ∈ Ico 57152 57216, mobiusTreeValue 16 mobiusTable1200001 n) = (8 : ℤ) ∧
    (∑ n ∈ Ico 57152 57216, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 57152 57216, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (699683 : ℤ) ∧
    (∑ n ∈ Ico 57152 57216, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (13993722732153309870431620581 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_57088_57216 :
    (∑ n ∈ Ico 57088 57216, mobiusTreeValue 16 mobiusTable1200001 n) = (3 : ℤ) ∧
    (∑ n ∈ Ico 57088 57216, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (79 : ℕ) ∧
    (∑ n ∈ Ico 57088 57216, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (261954 : ℤ) ∧
    (∑ n ∈ Ico 57088 57216, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (5239086551952890567263639141 : ℤ) := by
  rcases cdemPrefixStats_57088_57152 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_57152_57216 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 57088 ≤ 57152) (by norm_num : 57152 ≤ 57216), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 57088 ≤ 57152) (by norm_num : 57152 ≤ 57216), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 57088 ≤ 57152) (by norm_num : 57152 ≤ 57216), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 57088 ≤ 57152) (by norm_num : 57152 ≤ 57216), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_57216_57280 :
    (∑ n ∈ Ico 57216 57280, mobiusTreeValue 16 mobiusTable1200001 n) = (4 : ℤ) ∧
    (∑ n ∈ Ico 57216 57280, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 57216 57280, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (349811 : ℤ) ∧
    (∑ n ∈ Ico 57216 57280, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (6996266112173469831225569432 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_57280_57344 :
    (∑ n ∈ Ico 57280 57344, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 57280 57344, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 57280 57344, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-146 : ℤ) ∧
    (∑ n ∈ Ico 57280 57344, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-2983790284108279854351700 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_57216_57344 :
    (∑ n ∈ Ico 57216 57344, mobiusTreeValue 16 mobiusTable1200001 n) = (4 : ℤ) ∧
    (∑ n ∈ Ico 57216 57344, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (76 : ℕ) ∧
    (∑ n ∈ Ico 57216 57344, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (349665 : ℤ) ∧
    (∑ n ∈ Ico 57216 57344, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (6993282321889361551371217732 : ℤ) := by
  rcases cdemPrefixStats_57216_57280 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_57280_57344 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 57216 ≤ 57280) (by norm_num : 57280 ≤ 57344), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 57216 ≤ 57280) (by norm_num : 57280 ≤ 57344), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 57216 ≤ 57280) (by norm_num : 57280 ≤ 57344), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 57216 ≤ 57280) (by norm_num : 57280 ≤ 57344), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_57088_57344 :
    (∑ n ∈ Ico 57088 57344, mobiusTreeValue 16 mobiusTable1200001 n) = (7 : ℤ) ∧
    (∑ n ∈ Ico 57088 57344, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (155 : ℕ) ∧
    (∑ n ∈ Ico 57088 57344, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (611619 : ℤ) ∧
    (∑ n ∈ Ico 57088 57344, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (12232368873842252118634856873 : ℤ) := by
  rcases cdemPrefixStats_57088_57216 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_57216_57344 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 57088 ≤ 57216) (by norm_num : 57216 ≤ 57344), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 57088 ≤ 57216) (by norm_num : 57216 ≤ 57344), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 57088 ≤ 57216) (by norm_num : 57216 ≤ 57344), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 57088 ≤ 57216) (by norm_num : 57216 ≤ 57344), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_56832_57344 :
    (∑ n ∈ Ico 56832 57344, mobiusTreeValue 16 mobiusTable1200001 n) = (-18 : ℤ) ∧
    (∑ n ∈ Ico 56832 57344, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (310 : ℕ) ∧
    (∑ n ∈ Ico 56832 57344, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-1583496 : ℤ) ∧
    (∑ n ∈ Ico 56832 57344, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-31670126530251132982114372997 : ℤ) := by
  rcases cdemPrefixStats_56832_57088 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_57088_57344 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 56832 ≤ 57088) (by norm_num : 57088 ≤ 57344), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 56832 ≤ 57088) (by norm_num : 57088 ≤ 57344), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 56832 ≤ 57088) (by norm_num : 57088 ≤ 57344), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 56832 ≤ 57088) (by norm_num : 57088 ≤ 57344), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_56320_57344 :
    (∑ n ∈ Ico 56320 57344, mobiusTreeValue 16 mobiusTable1200001 n) = (-60 : ℤ) ∧
    (∑ n ∈ Ico 56320 57344, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (618 : ℕ) ∧
    (∑ n ∈ Ico 56320 57344, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-5295350 : ℤ) ∧
    (∑ n ∈ Ico 56320 57344, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-105907584018058927061165771541 : ℤ) := by
  rcases cdemPrefixStats_56320_56832 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_56832_57344 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 56320 ≤ 56832) (by norm_num : 56832 ≤ 57344), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 56320 ≤ 56832) (by norm_num : 56832 ≤ 57344), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 56320 ≤ 56832) (by norm_num : 56832 ≤ 57344), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 56320 ≤ 56832) (by norm_num : 56832 ≤ 57344), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_55296_57344 :
    (∑ n ∈ Ico 55296 57344, mobiusTreeValue 16 mobiusTable1200001 n) = (-70 : ℤ) ∧
    (∑ n ∈ Ico 55296 57344, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (1236 : ℕ) ∧
    (∑ n ∈ Ico 55296 57344, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-6175056 : ℤ) ∧
    (∑ n ∈ Ico 55296 57344, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-123501669547987611776910145082 : ℤ) := by
  rcases cdemPrefixStats_55296_56320 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_56320_57344 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 55296 ≤ 56320) (by norm_num : 56320 ≤ 57344), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 55296 ≤ 56320) (by norm_num : 56320 ≤ 57344), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 55296 ≤ 56320) (by norm_num : 56320 ≤ 57344), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 55296 ≤ 56320) (by norm_num : 56320 ≤ 57344), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_53248_57344 :
    (∑ n ∈ Ico 53248 57344, mobiusTreeValue 16 mobiusTable1200001 n) = (-74 : ℤ) ∧
    (∑ n ∈ Ico 53248 57344, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (2484 : ℕ) ∧
    (∑ n ∈ Ico 53248 57344, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-6526262 : ℤ) ∧
    (∑ n ∈ Ico 53248 57344, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-130525671446891319381165871871 : ℤ) := by
  rcases cdemPrefixStats_53248_55296 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_55296_57344 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 53248 ≤ 55296) (by norm_num : 55296 ≤ 57344), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 53248 ≤ 55296) (by norm_num : 55296 ≤ 57344), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 53248 ≤ 55296) (by norm_num : 55296 ≤ 57344), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 53248 ≤ 55296) (by norm_num : 55296 ≤ 57344), hR1, hR2] <;> norm_num

theorem cdemPrefixGroup013_checked_complete :
    (∑ n ∈ Ico 53248 57344, mobiusTreeValue 16 mobiusTable1200001 n) = (-74 : ℤ) ∧
    (∑ n ∈ Ico 53248 57344, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (2484 : ℕ) ∧
    (∑ n ∈ Ico 53248 57344, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-6526262 : ℤ) ∧
    (∑ n ∈ Ico 53248 57344, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-130525671446891319381165871871 : ℤ) := cdemPrefixStats_53248_57344
end Helfgott
#print axioms Helfgott.cdemPrefixGroup013_checked_complete

open Helfgott Finset
open scoped BigOperators

theorem solution :
    (∑ n ∈ Ico 53248 57344, mobiusTreeValue 16 mobiusTable1200001 n) = (-74 : ℤ) ∧
    (∑ n ∈ Ico 53248 57344, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (2484 : ℕ) ∧
    (∑ n ∈ Ico 53248 57344, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-6526262 : ℤ) ∧
    (∑ n ∈ Ico 53248 57344, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-130525671446891319381165871871 : ℤ) := Helfgott.cdemPrefixGroup013_checked_complete
#print axioms solution
