-- Prove2me | solution 1 for Helfgott.cdemPrefixGroup048_checked
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-09T02:58:26.299623+00:00
-- url     : https://prove2.me/submissions/d0b5a236-cfbd-41f4-8513-1b89350d237f

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
private theorem cdemPrefixStats_196608_196672 :
    (∑ n ∈ Ico 196608 196672, mobiusTreeValue 16 mobiusTable1200001 n) = (4 : ℤ) ∧
    (∑ n ∈ Ico 196608 196672, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 196608 196672, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (101705 : ℤ) ∧
    (∑ n ∈ Ico 196608 196672, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (2034125020531519010801956171 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_196672_196736 :
    (∑ n ∈ Ico 196672 196736, mobiusTreeValue 16 mobiusTable1200001 n) = (-11 : ℤ) ∧
    (∑ n ∈ Ico 196672 196736, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 196672 196736, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-279613 : ℤ) ∧
    (∑ n ∈ Ico 196672 196736, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-5592388850716613218401004077 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_196608_196736 :
    (∑ n ∈ Ico 196608 196736, mobiusTreeValue 16 mobiusTable1200001 n) = (-7 : ℤ) ∧
    (∑ n ∈ Ico 196608 196736, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (79 : ℕ) ∧
    (∑ n ∈ Ico 196608 196736, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-177908 : ℤ) ∧
    (∑ n ∈ Ico 196608 196736, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-3558263830185094207599047906 : ℤ) := by
  rcases cdemPrefixStats_196608_196672 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_196672_196736 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 196608 ≤ 196672) (by norm_num : 196672 ≤ 196736), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 196608 ≤ 196672) (by norm_num : 196672 ≤ 196736), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 196608 ≤ 196672) (by norm_num : 196672 ≤ 196736), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 196608 ≤ 196672) (by norm_num : 196672 ≤ 196736), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_196736_196800 :
    (∑ n ∈ Ico 196736 196800, mobiusTreeValue 16 mobiusTable1200001 n) = (5 : ℤ) ∧
    (∑ n ∈ Ico 196736 196800, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 196736 196800, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (127054 : ℤ) ∧
    (∑ n ∈ Ico 196736 196800, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (2541107513148493392938764384 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_196800_196864 :
    (∑ n ∈ Ico 196800 196864, mobiusTreeValue 16 mobiusTable1200001 n) = (3 : ℤ) ∧
    (∑ n ∈ Ico 196800 196864, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 196800 196864, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (76191 : ℤ) ∧
    (∑ n ∈ Ico 196800 196864, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1523861045954351580669159308 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_196864_196928 :
    (∑ n ∈ Ico 196864 196928, mobiusTreeValue 16 mobiusTable1200001 n) = (-9 : ℤ) ∧
    (∑ n ∈ Ico 196864 196928, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 196864 196928, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-228557 : ℤ) ∧
    (∑ n ∈ Ico 196864 196928, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-4571209310704665790222516117 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_196800_196928 :
    (∑ n ∈ Ico 196800 196928, mobiusTreeValue 16 mobiusTable1200001 n) = (-6 : ℤ) ∧
    (∑ n ∈ Ico 196800 196928, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 196800 196928, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-152366 : ℤ) ∧
    (∑ n ∈ Ico 196800 196928, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-3047348264750314209553356809 : ℤ) := by
  rcases cdemPrefixStats_196800_196864 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_196864_196928 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 196800 ≤ 196864) (by norm_num : 196864 ≤ 196928), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 196800 ≤ 196864) (by norm_num : 196864 ≤ 196928), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 196800 ≤ 196864) (by norm_num : 196864 ≤ 196928), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 196800 ≤ 196864) (by norm_num : 196864 ≤ 196928), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_196736_196928 :
    (∑ n ∈ Ico 196736 196928, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 196736 196928, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (117 : ℕ) ∧
    (∑ n ∈ Ico 196736 196928, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-25312 : ℤ) ∧
    (∑ n ∈ Ico 196736 196928, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-506240751601820816614592425 : ℤ) := by
  rcases cdemPrefixStats_196736_196800 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_196800_196928 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 196736 ≤ 196800) (by norm_num : 196800 ≤ 196928), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 196736 ≤ 196800) (by norm_num : 196800 ≤ 196928), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 196736 ≤ 196800) (by norm_num : 196800 ≤ 196928), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 196736 ≤ 196800) (by norm_num : 196800 ≤ 196928), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_196608_196928 :
    (∑ n ∈ Ico 196608 196928, mobiusTreeValue 16 mobiusTable1200001 n) = (-8 : ℤ) ∧
    (∑ n ∈ Ico 196608 196928, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (196 : ℕ) ∧
    (∑ n ∈ Ico 196608 196928, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-203220 : ℤ) ∧
    (∑ n ∈ Ico 196608 196928, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-4064504581786915024213640331 : ℤ) := by
  rcases cdemPrefixStats_196608_196736 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_196736_196928 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 196608 ≤ 196736) (by norm_num : 196736 ≤ 196928), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 196608 ≤ 196736) (by norm_num : 196736 ≤ 196928), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 196608 ≤ 196736) (by norm_num : 196736 ≤ 196928), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 196608 ≤ 196736) (by norm_num : 196736 ≤ 196928), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_196928_196992 :
    (∑ n ∈ Ico 196928 196992, mobiusTreeValue 16 mobiusTable1200001 n) = (15 : ℤ) ∧
    (∑ n ∈ Ico 196928 196992, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 196928 196992, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (380818 : ℤ) ∧
    (∑ n ∈ Ico 196928 196992, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (7616486511232056916226303882 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_196992_197056 :
    (∑ n ∈ Ico 196992 197056, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 196992 197056, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 196992 197056, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-25389 : ℤ) ∧
    (∑ n ∈ Ico 196992 197056, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-507786818376094207074821326 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_196928_197056 :
    (∑ n ∈ Ico 196928 197056, mobiusTreeValue 16 mobiusTable1200001 n) = (14 : ℤ) ∧
    (∑ n ∈ Ico 196928 197056, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (76 : ℕ) ∧
    (∑ n ∈ Ico 196928 197056, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (355429 : ℤ) ∧
    (∑ n ∈ Ico 196928 197056, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (7108699692855962709151482556 : ℤ) := by
  rcases cdemPrefixStats_196928_196992 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_196992_197056 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 196928 ≤ 196992) (by norm_num : 196992 ≤ 197056), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 196928 ≤ 196992) (by norm_num : 196992 ≤ 197056), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 196928 ≤ 196992) (by norm_num : 196992 ≤ 197056), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 196928 ≤ 196992) (by norm_num : 196992 ≤ 197056), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_197056_197120 :
    (∑ n ∈ Ico 197056 197120, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 197056 197120, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 197056 197120, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-25372 : ℤ) ∧
    (∑ n ∈ Ico 197056 197120, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-507392741591773566849013690 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_197120_197184 :
    (∑ n ∈ Ico 197120 197184, mobiusTreeValue 16 mobiusTable1200001 n) = (3 : ℤ) ∧
    (∑ n ∈ Ico 197120 197184, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 197120 197184, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (76095 : ℤ) ∧
    (∑ n ∈ Ico 197120 197184, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1521928425785648765297995080 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_197184_197248 :
    (∑ n ∈ Ico 197184 197248, mobiusTreeValue 16 mobiusTable1200001 n) = (-3 : ℤ) ∧
    (∑ n ∈ Ico 197184 197248, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 197184 197248, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-76050 : ℤ) ∧
    (∑ n ∈ Ico 197184 197248, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-1521030760508962708839295928 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_197120_197248 :
    (∑ n ∈ Ico 197120 197248, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 197120 197248, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 197120 197248, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (45 : ℤ) ∧
    (∑ n ∈ Ico 197120 197248, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (897665276686056458699152 : ℤ) := by
  rcases cdemPrefixStats_197120_197184 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_197184_197248 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 197120 ≤ 197184) (by norm_num : 197184 ≤ 197248), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 197120 ≤ 197184) (by norm_num : 197184 ≤ 197248), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 197120 ≤ 197184) (by norm_num : 197184 ≤ 197248), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 197120 ≤ 197184) (by norm_num : 197184 ≤ 197248), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_197056_197248 :
    (∑ n ∈ Ico 197056 197248, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 197056 197248, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (117 : ℕ) ∧
    (∑ n ∈ Ico 197056 197248, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-25327 : ℤ) ∧
    (∑ n ∈ Ico 197056 197248, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-506495076315087510390314538 : ℤ) := by
  rcases cdemPrefixStats_197056_197120 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_197120_197248 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 197056 ≤ 197120) (by norm_num : 197120 ≤ 197248), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 197056 ≤ 197120) (by norm_num : 197120 ≤ 197248), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 197056 ≤ 197120) (by norm_num : 197120 ≤ 197248), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 197056 ≤ 197120) (by norm_num : 197120 ≤ 197248), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_196928_197248 :
    (∑ n ∈ Ico 196928 197248, mobiusTreeValue 16 mobiusTable1200001 n) = (13 : ℤ) ∧
    (∑ n ∈ Ico 196928 197248, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (193 : ℕ) ∧
    (∑ n ∈ Ico 196928 197248, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (330102 : ℤ) ∧
    (∑ n ∈ Ico 196928 197248, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (6602204616540875198761168018 : ℤ) := by
  rcases cdemPrefixStats_196928_197056 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_197056_197248 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 196928 ≤ 197056) (by norm_num : 197056 ≤ 197248), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 196928 ≤ 197056) (by norm_num : 197056 ≤ 197248), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 196928 ≤ 197056) (by norm_num : 197056 ≤ 197248), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 196928 ≤ 197056) (by norm_num : 197056 ≤ 197248), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_196608_197248 :
    (∑ n ∈ Ico 196608 197248, mobiusTreeValue 16 mobiusTable1200001 n) = (5 : ℤ) ∧
    (∑ n ∈ Ico 196608 197248, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (389 : ℕ) ∧
    (∑ n ∈ Ico 196608 197248, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (126882 : ℤ) ∧
    (∑ n ∈ Ico 196608 197248, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (2537700034753960174547527687 : ℤ) := by
  rcases cdemPrefixStats_196608_196928 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_196928_197248 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 196608 ≤ 196928) (by norm_num : 196928 ≤ 197248), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 196608 ≤ 196928) (by norm_num : 196928 ≤ 197248), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 196608 ≤ 196928) (by norm_num : 196928 ≤ 197248), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 196608 ≤ 196928) (by norm_num : 196928 ≤ 197248), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_197248_197312 :
    (∑ n ∈ Ico 197248 197312, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 197248 197312, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 197248 197312, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-25350 : ℤ) ∧
    (∑ n ∈ Ico 197248 197312, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-506999114913829954576679900 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_197312_197376 :
    (∑ n ∈ Ico 197312 197376, mobiusTreeValue 16 mobiusTable1200001 n) = (-6 : ℤ) ∧
    (∑ n ∈ Ico 197312 197376, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 197312 197376, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-152004 : ℤ) ∧
    (∑ n ∈ Ico 197312 197376, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-3040157966664145979592288758 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_197248_197376 :
    (∑ n ∈ Ico 197248 197376, mobiusTreeValue 16 mobiusTable1200001 n) = (-7 : ℤ) ∧
    (∑ n ∈ Ico 197248 197376, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 197248 197376, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-177354 : ℤ) ∧
    (∑ n ∈ Ico 197248 197376, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-3547157081577975934168968658 : ℤ) := by
  rcases cdemPrefixStats_197248_197312 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_197312_197376 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 197248 ≤ 197312) (by norm_num : 197312 ≤ 197376), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 197248 ≤ 197312) (by norm_num : 197312 ≤ 197376), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 197248 ≤ 197312) (by norm_num : 197312 ≤ 197376), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 197248 ≤ 197312) (by norm_num : 197312 ≤ 197376), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_197376_197440 :
    (∑ n ∈ Ico 197376 197440, mobiusTreeValue 16 mobiusTable1200001 n) = (6 : ℤ) ∧
    (∑ n ∈ Ico 197376 197440, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 197376 197440, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (151946 : ℤ) ∧
    (∑ n ∈ Ico 197376 197440, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (3039003064062301448058550634 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_197440_197504 :
    (∑ n ∈ Ico 197440 197504, mobiusTreeValue 16 mobiusTable1200001 n) = (-3 : ℤ) ∧
    (∑ n ∈ Ico 197440 197504, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 197440 197504, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-75960 : ℤ) ∧
    (∑ n ∈ Ico 197440 197504, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-1519215576283522809061290696 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_197504_197568 :
    (∑ n ∈ Ico 197504 197568, mobiusTreeValue 16 mobiusTable1200001 n) = (11 : ℤ) ∧
    (∑ n ∈ Ico 197504 197568, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 197504 197568, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (278429 : ℤ) ∧
    (∑ n ∈ Ico 197504 197568, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (5568674445628347495017308778 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_197440_197568 :
    (∑ n ∈ Ico 197440 197568, mobiusTreeValue 16 mobiusTable1200001 n) = (8 : ℤ) ∧
    (∑ n ∈ Ico 197440 197568, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 197440 197568, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (202469 : ℤ) ∧
    (∑ n ∈ Ico 197440 197568, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (4049458869344824685956018082 : ℤ) := by
  rcases cdemPrefixStats_197440_197504 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_197504_197568 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 197440 ≤ 197504) (by norm_num : 197504 ≤ 197568), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 197440 ≤ 197504) (by norm_num : 197504 ≤ 197568), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 197440 ≤ 197504) (by norm_num : 197504 ≤ 197568), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 197440 ≤ 197504) (by norm_num : 197504 ≤ 197568), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_197376_197568 :
    (∑ n ∈ Ico 197376 197568, mobiusTreeValue 16 mobiusTable1200001 n) = (14 : ℤ) ∧
    (∑ n ∈ Ico 197376 197568, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (118 : ℕ) ∧
    (∑ n ∈ Ico 197376 197568, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (354415 : ℤ) ∧
    (∑ n ∈ Ico 197376 197568, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (7088461933407126134014568716 : ℤ) := by
  rcases cdemPrefixStats_197376_197440 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_197440_197568 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 197376 ≤ 197440) (by norm_num : 197440 ≤ 197568), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 197376 ≤ 197440) (by norm_num : 197440 ≤ 197568), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 197376 ≤ 197440) (by norm_num : 197440 ≤ 197568), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 197376 ≤ 197440) (by norm_num : 197440 ≤ 197568), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_197248_197568 :
    (∑ n ∈ Ico 197248 197568, mobiusTreeValue 16 mobiusTable1200001 n) = (7 : ℤ) ∧
    (∑ n ∈ Ico 197248 197568, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (195 : ℕ) ∧
    (∑ n ∈ Ico 197248 197568, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (177061 : ℤ) ∧
    (∑ n ∈ Ico 197248 197568, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (3541304851829150199845600058 : ℤ) := by
  rcases cdemPrefixStats_197248_197376 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_197376_197568 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 197248 ≤ 197376) (by norm_num : 197376 ≤ 197568), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 197248 ≤ 197376) (by norm_num : 197376 ≤ 197568), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 197248 ≤ 197376) (by norm_num : 197376 ≤ 197568), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 197248 ≤ 197376) (by norm_num : 197376 ≤ 197568), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_197568_197632 :
    (∑ n ∈ Ico 197568 197632, mobiusTreeValue 16 mobiusTable1200001 n) = (-7 : ℤ) ∧
    (∑ n ∈ Ico 197568 197632, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 197568 197632, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-177142 : ℤ) ∧
    (∑ n ∈ Ico 197568 197632, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-3542973704240760667235266324 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_197632_197696 :
    (∑ n ∈ Ico 197632 197696, mobiusTreeValue 16 mobiusTable1200001 n) = (-11 : ℤ) ∧
    (∑ n ∈ Ico 197632 197696, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 197632 197696, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-278241 : ℤ) ∧
    (∑ n ∈ Ico 197632 197696, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-5564945484877722007661556163 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_197696_197760 :
    (∑ n ∈ Ico 197696 197760, mobiusTreeValue 16 mobiusTable1200001 n) = (3 : ℤ) ∧
    (∑ n ∈ Ico 197696 197760, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 197696 197760, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (75856 : ℤ) ∧
    (∑ n ∈ Ico 197696 197760, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1517184664646501368966953588 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_197632_197760 :
    (∑ n ∈ Ico 197632 197760, mobiusTreeValue 16 mobiusTable1200001 n) = (-8 : ℤ) ∧
    (∑ n ∈ Ico 197632 197760, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 197632 197760, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-202385 : ℤ) ∧
    (∑ n ∈ Ico 197632 197760, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-4047760820231220638694602575 : ℤ) := by
  rcases cdemPrefixStats_197632_197696 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_197696_197760 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 197632 ≤ 197696) (by norm_num : 197696 ≤ 197760), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 197632 ≤ 197696) (by norm_num : 197696 ≤ 197760), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 197632 ≤ 197696) (by norm_num : 197696 ≤ 197760), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 197632 ≤ 197696) (by norm_num : 197696 ≤ 197760), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_197568_197760 :
    (∑ n ∈ Ico 197568 197760, mobiusTreeValue 16 mobiusTable1200001 n) = (-15 : ℤ) ∧
    (∑ n ∈ Ico 197568 197760, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (115 : ℕ) ∧
    (∑ n ∈ Ico 197568 197760, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-379527 : ℤ) ∧
    (∑ n ∈ Ico 197568 197760, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-7590734524471981305929868899 : ℤ) := by
  rcases cdemPrefixStats_197568_197632 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_197632_197760 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 197568 ≤ 197632) (by norm_num : 197632 ≤ 197760), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 197568 ≤ 197632) (by norm_num : 197632 ≤ 197760), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 197568 ≤ 197632) (by norm_num : 197632 ≤ 197760), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 197568 ≤ 197632) (by norm_num : 197632 ≤ 197760), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_197760_197824 :
    (∑ n ∈ Ico 197760 197824, mobiusTreeValue 16 mobiusTable1200001 n) = (6 : ℤ) ∧
    (∑ n ∈ Ico 197760 197824, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (42 : ℕ) ∧
    (∑ n ∈ Ico 197760 197824, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (151654 : ℤ) ∧
    (∑ n ∈ Ico 197760 197824, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (3033101226739345932616873452 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_197824_197888 :
    (∑ n ∈ Ico 197824 197888, mobiusTreeValue 16 mobiusTable1200001 n) = (3 : ℤ) ∧
    (∑ n ∈ Ico 197824 197888, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (35 : ℕ) ∧
    (∑ n ∈ Ico 197824 197888, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (75814 : ℤ) ∧
    (∑ n ∈ Ico 197824 197888, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1516335950116797099556129339 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_197888_197952 :
    (∑ n ∈ Ico 197888 197952, mobiusTreeValue 16 mobiusTable1200001 n) = (-3 : ℤ) ∧
    (∑ n ∈ Ico 197888 197952, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 197888 197952, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-75807 : ℤ) ∧
    (∑ n ∈ Ico 197888 197952, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-1516126429307908781278329399 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_197824_197952 :
    (∑ n ∈ Ico 197824 197952, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 197824 197952, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (74 : ℕ) ∧
    (∑ n ∈ Ico 197824 197952, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (7 : ℤ) ∧
    (∑ n ∈ Ico 197824 197952, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (209520808888318277799940 : ℤ) := by
  rcases cdemPrefixStats_197824_197888 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_197888_197952 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 197824 ≤ 197888) (by norm_num : 197888 ≤ 197952), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 197824 ≤ 197888) (by norm_num : 197888 ≤ 197952), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 197824 ≤ 197888) (by norm_num : 197888 ≤ 197952), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 197824 ≤ 197888) (by norm_num : 197888 ≤ 197952), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_197760_197952 :
    (∑ n ∈ Ico 197760 197952, mobiusTreeValue 16 mobiusTable1200001 n) = (6 : ℤ) ∧
    (∑ n ∈ Ico 197760 197952, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (116 : ℕ) ∧
    (∑ n ∈ Ico 197760 197952, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (151661 : ℤ) ∧
    (∑ n ∈ Ico 197760 197952, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (3033310747548234250894673392 : ℤ) := by
  rcases cdemPrefixStats_197760_197824 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_197824_197952 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 197760 ≤ 197824) (by norm_num : 197824 ≤ 197952), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 197760 ≤ 197824) (by norm_num : 197824 ≤ 197952), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 197760 ≤ 197824) (by norm_num : 197824 ≤ 197952), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 197760 ≤ 197824) (by norm_num : 197824 ≤ 197952), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_197568_197952 :
    (∑ n ∈ Ico 197568 197952, mobiusTreeValue 16 mobiusTable1200001 n) = (-9 : ℤ) ∧
    (∑ n ∈ Ico 197568 197952, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (231 : ℕ) ∧
    (∑ n ∈ Ico 197568 197952, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-227866 : ℤ) ∧
    (∑ n ∈ Ico 197568 197952, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-4557423776923747055035195507 : ℤ) := by
  rcases cdemPrefixStats_197568_197760 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_197760_197952 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 197568 ≤ 197760) (by norm_num : 197760 ≤ 197952), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 197568 ≤ 197760) (by norm_num : 197760 ≤ 197952), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 197568 ≤ 197760) (by norm_num : 197760 ≤ 197952), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 197568 ≤ 197760) (by norm_num : 197760 ≤ 197952), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_197248_197952 :
    (∑ n ∈ Ico 197248 197952, mobiusTreeValue 16 mobiusTable1200001 n) = (-2 : ℤ) ∧
    (∑ n ∈ Ico 197248 197952, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (426 : ℕ) ∧
    (∑ n ∈ Ico 197248 197952, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-50805 : ℤ) ∧
    (∑ n ∈ Ico 197248 197952, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-1016118925094596855189595449 : ℤ) := by
  rcases cdemPrefixStats_197248_197568 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_197568_197952 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 197248 ≤ 197568) (by norm_num : 197568 ≤ 197952), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 197248 ≤ 197568) (by norm_num : 197568 ≤ 197952), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 197248 ≤ 197568) (by norm_num : 197568 ≤ 197952), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 197248 ≤ 197568) (by norm_num : 197568 ≤ 197952), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_196608_197952 :
    (∑ n ∈ Ico 196608 197952, mobiusTreeValue 16 mobiusTable1200001 n) = (3 : ℤ) ∧
    (∑ n ∈ Ico 196608 197952, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (815 : ℕ) ∧
    (∑ n ∈ Ico 196608 197952, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (76077 : ℤ) ∧
    (∑ n ∈ Ico 196608 197952, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1521581109659363319357932238 : ℤ) := by
  rcases cdemPrefixStats_196608_197248 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_197248_197952 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 196608 ≤ 197248) (by norm_num : 197248 ≤ 197952), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 196608 ≤ 197248) (by norm_num : 197248 ≤ 197952), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 196608 ≤ 197248) (by norm_num : 197248 ≤ 197952), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 196608 ≤ 197248) (by norm_num : 197248 ≤ 197952), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_197952_198016 :
    (∑ n ∈ Ico 197952 198016, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 197952 198016, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 197952 198016, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-25252 : ℤ) ∧
    (∑ n ∈ Ico 197952 198016, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-505012274587382829485535582 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_198016_198080 :
    (∑ n ∈ Ico 198016 198080, mobiusTreeValue 16 mobiusTable1200001 n) = (-2 : ℤ) ∧
    (∑ n ∈ Ico 198016 198080, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 198016 198080, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-50476 : ℤ) ∧
    (∑ n ∈ Ico 198016 198080, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-1009596157556791953604464838 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_197952_198080 :
    (∑ n ∈ Ico 197952 198080, mobiusTreeValue 16 mobiusTable1200001 n) = (-3 : ℤ) ∧
    (∑ n ∈ Ico 197952 198080, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 197952 198080, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-75728 : ℤ) ∧
    (∑ n ∈ Ico 197952 198080, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-1514608432144174783090000420 : ℤ) := by
  rcases cdemPrefixStats_197952_198016 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_198016_198080 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 197952 ≤ 198016) (by norm_num : 198016 ≤ 198080), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 197952 ≤ 198016) (by norm_num : 198016 ≤ 198080), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 197952 ≤ 198016) (by norm_num : 198016 ≤ 198080), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 197952 ≤ 198016) (by norm_num : 198016 ≤ 198080), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_198080_198144 :
    (∑ n ∈ Ico 198080 198144, mobiusTreeValue 16 mobiusTable1200001 n) = (4 : ℤ) ∧
    (∑ n ∈ Ico 198080 198144, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 198080 198144, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (100952 : ℤ) ∧
    (∑ n ∈ Ico 198080 198144, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (2019008958668899864446101635 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_198144_198208 :
    (∑ n ∈ Ico 198144 198208, mobiusTreeValue 16 mobiusTable1200001 n) = (-4 : ℤ) ∧
    (∑ n ∈ Ico 198144 198208, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 198144 198208, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-100898 : ℤ) ∧
    (∑ n ∈ Ico 198144 198208, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-2018038680038565272242127726 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_198208_198272 :
    (∑ n ∈ Ico 198208 198272, mobiusTreeValue 16 mobiusTable1200001 n) = (-6 : ℤ) ∧
    (∑ n ∈ Ico 198208 198272, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 198208 198272, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-151327 : ℤ) ∧
    (∑ n ∈ Ico 198208 198272, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-3026563142352558385615004522 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_198144_198272 :
    (∑ n ∈ Ico 198144 198272, mobiusTreeValue 16 mobiusTable1200001 n) = (-10 : ℤ) ∧
    (∑ n ∈ Ico 198144 198272, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 198144 198272, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-252225 : ℤ) ∧
    (∑ n ∈ Ico 198144 198272, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-5044601822391123657857132248 : ℤ) := by
  rcases cdemPrefixStats_198144_198208 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_198208_198272 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 198144 ≤ 198208) (by norm_num : 198208 ≤ 198272), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 198144 ≤ 198208) (by norm_num : 198208 ≤ 198272), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 198144 ≤ 198208) (by norm_num : 198208 ≤ 198272), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 198144 ≤ 198208) (by norm_num : 198208 ≤ 198272), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_198080_198272 :
    (∑ n ∈ Ico 198080 198272, mobiusTreeValue 16 mobiusTable1200001 n) = (-6 : ℤ) ∧
    (∑ n ∈ Ico 198080 198272, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (118 : ℕ) ∧
    (∑ n ∈ Ico 198080 198272, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-151273 : ℤ) ∧
    (∑ n ∈ Ico 198080 198272, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-3025592863722223793411030613 : ℤ) := by
  rcases cdemPrefixStats_198080_198144 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_198144_198272 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 198080 ≤ 198144) (by norm_num : 198144 ≤ 198272), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 198080 ≤ 198144) (by norm_num : 198144 ≤ 198272), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 198080 ≤ 198144) (by norm_num : 198144 ≤ 198272), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 198080 ≤ 198144) (by norm_num : 198144 ≤ 198272), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_197952_198272 :
    (∑ n ∈ Ico 197952 198272, mobiusTreeValue 16 mobiusTable1200001 n) = (-9 : ℤ) ∧
    (∑ n ∈ Ico 197952 198272, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (195 : ℕ) ∧
    (∑ n ∈ Ico 197952 198272, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-227001 : ℤ) ∧
    (∑ n ∈ Ico 197952 198272, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-4540201295866398576501031033 : ℤ) := by
  rcases cdemPrefixStats_197952_198080 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_198080_198272 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 197952 ≤ 198080) (by norm_num : 198080 ≤ 198272), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 197952 ≤ 198080) (by norm_num : 198080 ≤ 198272), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 197952 ≤ 198080) (by norm_num : 198080 ≤ 198272), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 197952 ≤ 198080) (by norm_num : 198080 ≤ 198272), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_198272_198336 :
    (∑ n ∈ Ico 198272 198336, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 198272 198336, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 198272 198336, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (25218 : ℤ) ∧
    (∑ n ∈ Ico 198272 198336, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (504428839902382309385097338 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_198336_198400 :
    (∑ n ∈ Ico 198336 198400, mobiusTreeValue 16 mobiusTable1200001 n) = (2 : ℤ) ∧
    (∑ n ∈ Ico 198336 198400, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 198336 198400, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (50423 : ℤ) ∧
    (∑ n ∈ Ico 198336 198400, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1008521923163844555095881424 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_198272_198400 :
    (∑ n ∈ Ico 198272 198400, mobiusTreeValue 16 mobiusTable1200001 n) = (3 : ℤ) ∧
    (∑ n ∈ Ico 198272 198400, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (79 : ℕ) ∧
    (∑ n ∈ Ico 198272 198400, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (75641 : ℤ) ∧
    (∑ n ∈ Ico 198272 198400, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1512950763066226864480978762 : ℤ) := by
  rcases cdemPrefixStats_198272_198336 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_198336_198400 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 198272 ≤ 198336) (by norm_num : 198336 ≤ 198400), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 198272 ≤ 198336) (by norm_num : 198336 ≤ 198400), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 198272 ≤ 198336) (by norm_num : 198336 ≤ 198400), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 198272 ≤ 198336) (by norm_num : 198336 ≤ 198400), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_198400_198464 :
    (∑ n ∈ Ico 198400 198464, mobiusTreeValue 16 mobiusTable1200001 n) = (-8 : ℤ) ∧
    (∑ n ∈ Ico 198400 198464, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 198400 198464, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-201564 : ℤ) ∧
    (∑ n ∈ Ico 198400 198464, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-4031432593110966435536959914 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_198464_198528 :
    (∑ n ∈ Ico 198464 198528, mobiusTreeValue 16 mobiusTable1200001 n) = (11 : ℤ) ∧
    (∑ n ∈ Ico 198464 198528, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 198464 198528, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (277084 : ℤ) ∧
    (∑ n ∈ Ico 198464 198528, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (5541731834903598328785959249 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_198528_198592 :
    (∑ n ∈ Ico 198528 198592, mobiusTreeValue 16 mobiusTable1200001 n) = (-7 : ℤ) ∧
    (∑ n ∈ Ico 198528 198592, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 198528 198592, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-176280 : ℤ) ∧
    (∑ n ∈ Ico 198528 198592, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-3525684640686597614882766418 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_198464_198592 :
    (∑ n ∈ Ico 198464 198592, mobiusTreeValue 16 mobiusTable1200001 n) = (4 : ℤ) ∧
    (∑ n ∈ Ico 198464 198592, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 198464 198592, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (100804 : ℤ) ∧
    (∑ n ∈ Ico 198464 198592, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (2016047194217000713903192831 : ℤ) := by
  rcases cdemPrefixStats_198464_198528 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_198528_198592 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 198464 ≤ 198528) (by norm_num : 198528 ≤ 198592), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 198464 ≤ 198528) (by norm_num : 198528 ≤ 198592), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 198464 ≤ 198528) (by norm_num : 198528 ≤ 198592), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 198464 ≤ 198528) (by norm_num : 198528 ≤ 198592), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_198400_198592 :
    (∑ n ∈ Ico 198400 198592, mobiusTreeValue 16 mobiusTable1200001 n) = (-4 : ℤ) ∧
    (∑ n ∈ Ico 198400 198592, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (116 : ℕ) ∧
    (∑ n ∈ Ico 198400 198592, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-100760 : ℤ) ∧
    (∑ n ∈ Ico 198400 198592, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-2015385398893965721633767083 : ℤ) := by
  rcases cdemPrefixStats_198400_198464 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_198464_198592 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 198400 ≤ 198464) (by norm_num : 198464 ≤ 198592), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 198400 ≤ 198464) (by norm_num : 198464 ≤ 198592), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 198400 ≤ 198464) (by norm_num : 198464 ≤ 198592), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 198400 ≤ 198464) (by norm_num : 198464 ≤ 198592), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_198272_198592 :
    (∑ n ∈ Ico 198272 198592, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 198272 198592, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (195 : ℕ) ∧
    (∑ n ∈ Ico 198272 198592, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-25119 : ℤ) ∧
    (∑ n ∈ Ico 198272 198592, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-502434635827738857152788321 : ℤ) := by
  rcases cdemPrefixStats_198272_198400 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_198400_198592 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 198272 ≤ 198400) (by norm_num : 198400 ≤ 198592), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 198272 ≤ 198400) (by norm_num : 198400 ≤ 198592), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 198272 ≤ 198400) (by norm_num : 198400 ≤ 198592), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 198272 ≤ 198400) (by norm_num : 198400 ≤ 198592), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_197952_198592 :
    (∑ n ∈ Ico 197952 198592, mobiusTreeValue 16 mobiusTable1200001 n) = (-10 : ℤ) ∧
    (∑ n ∈ Ico 197952 198592, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (390 : ℕ) ∧
    (∑ n ∈ Ico 197952 198592, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-252120 : ℤ) ∧
    (∑ n ∈ Ico 197952 198592, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-5042635931694137433653819354 : ℤ) := by
  rcases cdemPrefixStats_197952_198272 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_198272_198592 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 197952 ≤ 198272) (by norm_num : 198272 ≤ 198592), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 197952 ≤ 198272) (by norm_num : 198272 ≤ 198592), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 197952 ≤ 198272) (by norm_num : 198272 ≤ 198592), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 197952 ≤ 198272) (by norm_num : 198272 ≤ 198592), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_198592_198656 :
    (∑ n ∈ Ico 198592 198656, mobiusTreeValue 16 mobiusTable1200001 n) = (-7 : ℤ) ∧
    (∑ n ∈ Ico 198592 198656, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 198592 198656, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-176215 : ℤ) ∧
    (∑ n ∈ Ico 198592 198656, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-3524330490388740825384322989 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_198656_198720 :
    (∑ n ∈ Ico 198656 198720, mobiusTreeValue 16 mobiusTable1200001 n) = (-4 : ℤ) ∧
    (∑ n ∈ Ico 198656 198720, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 198656 198720, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-100663 : ℤ) ∧
    (∑ n ∈ Ico 198656 198720, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-2013330782792921504871280317 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_198592_198720 :
    (∑ n ∈ Ico 198592 198720, mobiusTreeValue 16 mobiusTable1200001 n) = (-11 : ℤ) ∧
    (∑ n ∈ Ico 198592 198720, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (79 : ℕ) ∧
    (∑ n ∈ Ico 198592 198720, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-276878 : ℤ) ∧
    (∑ n ∈ Ico 198592 198720, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-5537661273181662330255603306 : ℤ) := by
  rcases cdemPrefixStats_198592_198656 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_198656_198720 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 198592 ≤ 198656) (by norm_num : 198656 ≤ 198720), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 198592 ≤ 198656) (by norm_num : 198656 ≤ 198720), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 198592 ≤ 198656) (by norm_num : 198656 ≤ 198720), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 198592 ≤ 198656) (by norm_num : 198656 ≤ 198720), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_198720_198784 :
    (∑ n ∈ Ico 198720 198784, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 198720 198784, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 198720 198784, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (25167 : ℤ) ∧
    (∑ n ∈ Ico 198720 198784, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (503291448468938585058655444 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_198784_198848 :
    (∑ n ∈ Ico 198784 198848, mobiusTreeValue 16 mobiusTable1200001 n) = (3 : ℤ) ∧
    (∑ n ∈ Ico 198784 198848, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 198784 198848, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (75485 : ℤ) ∧
    (∑ n ∈ Ico 198784 198848, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1509656468429556051972973448 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_198848_198912 :
    (∑ n ∈ Ico 198848 198912, mobiusTreeValue 16 mobiusTable1200001 n) = (-6 : ℤ) ∧
    (∑ n ∈ Ico 198848 198912, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 198848 198912, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-150838 : ℤ) ∧
    (∑ n ∈ Ico 198848 198912, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-3016742958662742988361748048 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_198784_198912 :
    (∑ n ∈ Ico 198784 198912, mobiusTreeValue 16 mobiusTable1200001 n) = (-3 : ℤ) ∧
    (∑ n ∈ Ico 198784 198912, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (79 : ℕ) ∧
    (∑ n ∈ Ico 198784 198912, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-75353 : ℤ) ∧
    (∑ n ∈ Ico 198784 198912, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-1507086490233186936388774600 : ℤ) := by
  rcases cdemPrefixStats_198784_198848 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_198848_198912 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 198784 ≤ 198848) (by norm_num : 198848 ≤ 198912), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 198784 ≤ 198848) (by norm_num : 198848 ≤ 198912), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 198784 ≤ 198848) (by norm_num : 198848 ≤ 198912), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 198784 ≤ 198848) (by norm_num : 198848 ≤ 198912), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_198720_198912 :
    (∑ n ∈ Ico 198720 198912, mobiusTreeValue 16 mobiusTable1200001 n) = (-2 : ℤ) ∧
    (∑ n ∈ Ico 198720 198912, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (118 : ℕ) ∧
    (∑ n ∈ Ico 198720 198912, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-50186 : ℤ) ∧
    (∑ n ∈ Ico 198720 198912, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-1003795041764248351330119156 : ℤ) := by
  rcases cdemPrefixStats_198720_198784 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_198784_198912 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 198720 ≤ 198784) (by norm_num : 198784 ≤ 198912), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 198720 ≤ 198784) (by norm_num : 198784 ≤ 198912), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 198720 ≤ 198784) (by norm_num : 198784 ≤ 198912), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 198720 ≤ 198784) (by norm_num : 198784 ≤ 198912), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_198592_198912 :
    (∑ n ∈ Ico 198592 198912, mobiusTreeValue 16 mobiusTable1200001 n) = (-13 : ℤ) ∧
    (∑ n ∈ Ico 198592 198912, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (197 : ℕ) ∧
    (∑ n ∈ Ico 198592 198912, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-327064 : ℤ) ∧
    (∑ n ∈ Ico 198592 198912, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-6541456314945910681585722462 : ℤ) := by
  rcases cdemPrefixStats_198592_198720 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_198720_198912 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 198592 ≤ 198720) (by norm_num : 198720 ≤ 198912), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 198592 ≤ 198720) (by norm_num : 198720 ≤ 198912), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 198592 ≤ 198720) (by norm_num : 198720 ≤ 198912), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 198592 ≤ 198720) (by norm_num : 198720 ≤ 198912), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_198912_198976 :
    (∑ n ∈ Ico 198912 198976, mobiusTreeValue 16 mobiusTable1200001 n) = (-17 : ℤ) ∧
    (∑ n ∈ Ico 198912 198976, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 198912 198976, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-427234 : ℤ) ∧
    (∑ n ∈ Ico 198912 198976, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-8544840348188554082187145262 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_198976_199040 :
    (∑ n ∈ Ico 198976 199040, mobiusTreeValue 16 mobiusTable1200001 n) = (5 : ℤ) ∧
    (∑ n ∈ Ico 198976 199040, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 198976 199040, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (125625 : ℤ) ∧
    (∑ n ∈ Ico 198976 199040, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (2512557769735051157952012422 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_199040_199104 :
    (∑ n ∈ Ico 199040 199104, mobiusTreeValue 16 mobiusTable1200001 n) = (12 : ℤ) ∧
    (∑ n ∈ Ico 199040 199104, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 199040 199104, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (301381 : ℤ) ∧
    (∑ n ∈ Ico 199040 199104, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (6027747759492917424311533069 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_198976_199104 :
    (∑ n ∈ Ico 198976 199104, mobiusTreeValue 16 mobiusTable1200001 n) = (17 : ℤ) ∧
    (∑ n ∈ Ico 198976 199104, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 198976 199104, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (427006 : ℤ) ∧
    (∑ n ∈ Ico 198976 199104, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (8540305529227968582263545491 : ℤ) := by
  rcases cdemPrefixStats_198976_199040 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_199040_199104 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 198976 ≤ 199040) (by norm_num : 199040 ≤ 199104), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 198976 ≤ 199040) (by norm_num : 199040 ≤ 199104), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 198976 ≤ 199040) (by norm_num : 199040 ≤ 199104), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 198976 ≤ 199040) (by norm_num : 199040 ≤ 199104), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_198912_199104 :
    (∑ n ∈ Ico 198912 199104, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 198912 199104, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (116 : ℕ) ∧
    (∑ n ∈ Ico 198912 199104, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-228 : ℤ) ∧
    (∑ n ∈ Ico 198912 199104, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-4534818960585499923599771 : ℤ) := by
  rcases cdemPrefixStats_198912_198976 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_198976_199104 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 198912 ≤ 198976) (by norm_num : 198976 ≤ 199104), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 198912 ≤ 198976) (by norm_num : 198976 ≤ 199104), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 198912 ≤ 198976) (by norm_num : 198976 ≤ 199104), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 198912 ≤ 198976) (by norm_num : 198976 ≤ 199104), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_199104_199168 :
    (∑ n ∈ Ico 199104 199168, mobiusTreeValue 16 mobiusTable1200001 n) = (2 : ℤ) ∧
    (∑ n ∈ Ico 199104 199168, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 199104 199168, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (50211 : ℤ) ∧
    (∑ n ∈ Ico 199104 199168, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1004270644072970067895471614 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_199168_199232 :
    (∑ n ∈ Ico 199168 199232, mobiusTreeValue 16 mobiusTable1200001 n) = (2 : ℤ) ∧
    (∑ n ∈ Ico 199168 199232, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 199168 199232, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (50185 : ℤ) ∧
    (∑ n ∈ Ico 199168 199232, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1003723751738051032540746132 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_199232_199296 :
    (∑ n ∈ Ico 199232 199296, mobiusTreeValue 16 mobiusTable1200001 n) = (2 : ℤ) ∧
    (∑ n ∈ Ico 199232 199296, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 199232 199296, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (50203 : ℤ) ∧
    (∑ n ∈ Ico 199232 199296, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1004131845180472235720921969 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_199296_199331 :
    (∑ n ∈ Ico 199296 199331, mobiusTreeValue 16 mobiusTable1200001 n) = (7 : ℤ) ∧
    (∑ n ∈ Ico 199296 199331, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (21 : ℕ) ∧
    (∑ n ∈ Ico 199296 199331, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (175588 : ℤ) ∧
    (∑ n ∈ Ico 199296 199331, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (3511857532680659252099213354 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_199232_199331 :
    (∑ n ∈ Ico 199232 199331, mobiusTreeValue 16 mobiusTable1200001 n) = (9 : ℤ) ∧
    (∑ n ∈ Ico 199232 199331, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (59 : ℕ) ∧
    (∑ n ∈ Ico 199232 199331, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (225791 : ℤ) ∧
    (∑ n ∈ Ico 199232 199331, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (4515989377861131487820135323 : ℤ) := by
  rcases cdemPrefixStats_199232_199296 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_199296_199331 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 199232 ≤ 199296) (by norm_num : 199296 ≤ 199331), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 199232 ≤ 199296) (by norm_num : 199296 ≤ 199331), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 199232 ≤ 199296) (by norm_num : 199296 ≤ 199331), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 199232 ≤ 199296) (by norm_num : 199296 ≤ 199331), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_199168_199331 :
    (∑ n ∈ Ico 199168 199331, mobiusTreeValue 16 mobiusTable1200001 n) = (11 : ℤ) ∧
    (∑ n ∈ Ico 199168 199331, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (99 : ℕ) ∧
    (∑ n ∈ Ico 199168 199331, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (275976 : ℤ) ∧
    (∑ n ∈ Ico 199168 199331, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (5519713129599182520360881455 : ℤ) := by
  rcases cdemPrefixStats_199168_199232 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_199232_199331 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 199168 ≤ 199232) (by norm_num : 199232 ≤ 199331), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 199168 ≤ 199232) (by norm_num : 199232 ≤ 199331), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 199168 ≤ 199232) (by norm_num : 199232 ≤ 199331), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 199168 ≤ 199232) (by norm_num : 199232 ≤ 199331), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_199104_199331 :
    (∑ n ∈ Ico 199104 199331, mobiusTreeValue 16 mobiusTable1200001 n) = (13 : ℤ) ∧
    (∑ n ∈ Ico 199104 199331, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (139 : ℕ) ∧
    (∑ n ∈ Ico 199104 199331, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (326187 : ℤ) ∧
    (∑ n ∈ Ico 199104 199331, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (6523983773672152588256353069 : ℤ) := by
  rcases cdemPrefixStats_199104_199168 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_199168_199331 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 199104 ≤ 199168) (by norm_num : 199168 ≤ 199331), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 199104 ≤ 199168) (by norm_num : 199168 ≤ 199331), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 199104 ≤ 199168) (by norm_num : 199168 ≤ 199331), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 199104 ≤ 199168) (by norm_num : 199168 ≤ 199331), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_198912_199331 :
    (∑ n ∈ Ico 198912 199331, mobiusTreeValue 16 mobiusTable1200001 n) = (13 : ℤ) ∧
    (∑ n ∈ Ico 198912 199331, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (255 : ℕ) ∧
    (∑ n ∈ Ico 198912 199331, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (325959 : ℤ) ∧
    (∑ n ∈ Ico 198912 199331, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (6519448954711567088332753298 : ℤ) := by
  rcases cdemPrefixStats_198912_199104 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_199104_199331 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 198912 ≤ 199104) (by norm_num : 199104 ≤ 199331), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 198912 ≤ 199104) (by norm_num : 199104 ≤ 199331), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 198912 ≤ 199104) (by norm_num : 199104 ≤ 199331), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 198912 ≤ 199104) (by norm_num : 199104 ≤ 199331), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_198592_199331 :
    (∑ n ∈ Ico 198592 199331, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 198592 199331, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (452 : ℕ) ∧
    (∑ n ∈ Ico 198592 199331, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-1105 : ℤ) ∧
    (∑ n ∈ Ico 198592 199331, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-22007360234343593252969164 : ℤ) := by
  rcases cdemPrefixStats_198592_198912 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_198912_199331 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 198592 ≤ 198912) (by norm_num : 198912 ≤ 199331), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 198592 ≤ 198912) (by norm_num : 198912 ≤ 199331), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 198592 ≤ 198912) (by norm_num : 198912 ≤ 199331), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 198592 ≤ 198912) (by norm_num : 198912 ≤ 199331), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_197952_199331 :
    (∑ n ∈ Ico 197952 199331, mobiusTreeValue 16 mobiusTable1200001 n) = (-10 : ℤ) ∧
    (∑ n ∈ Ico 197952 199331, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (842 : ℕ) ∧
    (∑ n ∈ Ico 197952 199331, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-253225 : ℤ) ∧
    (∑ n ∈ Ico 197952 199331, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-5064643291928481026906788518 : ℤ) := by
  rcases cdemPrefixStats_197952_198592 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_198592_199331 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 197952 ≤ 198592) (by norm_num : 198592 ≤ 199331), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 197952 ≤ 198592) (by norm_num : 198592 ≤ 199331), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 197952 ≤ 198592) (by norm_num : 198592 ≤ 199331), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 197952 ≤ 198592) (by norm_num : 198592 ≤ 199331), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_196608_199331 :
    (∑ n ∈ Ico 196608 199331, mobiusTreeValue 16 mobiusTable1200001 n) = (-7 : ℤ) ∧
    (∑ n ∈ Ico 196608 199331, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (1657 : ℕ) ∧
    (∑ n ∈ Ico 196608 199331, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-177148 : ℤ) ∧
    (∑ n ∈ Ico 196608 199331, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-3543062182269117707548856280 : ℤ) := by
  rcases cdemPrefixStats_196608_197952 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_197952_199331 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 196608 ≤ 197952) (by norm_num : 197952 ≤ 199331), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 196608 ≤ 197952) (by norm_num : 197952 ≤ 199331), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 196608 ≤ 197952) (by norm_num : 197952 ≤ 199331), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 196608 ≤ 197952) (by norm_num : 197952 ≤ 199331), hR1, hR2] <;> norm_num

theorem cdemPrefixGroup048_checked_complete :
    (∑ n ∈ Ico 196608 199331, mobiusTreeValue 16 mobiusTable1200001 n) = (-7 : ℤ) ∧
    (∑ n ∈ Ico 196608 199331, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (1657 : ℕ) ∧
    (∑ n ∈ Ico 196608 199331, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-177148 : ℤ) ∧
    (∑ n ∈ Ico 196608 199331, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-3543062182269117707548856280 : ℤ) := cdemPrefixStats_196608_199331
end Helfgott
#print axioms Helfgott.cdemPrefixGroup048_checked_complete

open Helfgott Finset
open scoped BigOperators

theorem solution :
    (∑ n ∈ Ico 196608 199331, mobiusTreeValue 16 mobiusTable1200001 n) = (-7 : ℤ) ∧
    (∑ n ∈ Ico 196608 199331, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (1657 : ℕ) ∧
    (∑ n ∈ Ico 196608 199331, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-177148 : ℤ) ∧
    (∑ n ∈ Ico 196608 199331, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-3543062182269117707548856280 : ℤ) := Helfgott.cdemPrefixGroup048_checked_complete
#print axioms solution
