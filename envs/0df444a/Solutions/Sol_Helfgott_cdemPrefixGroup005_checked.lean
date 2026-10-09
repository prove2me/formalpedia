-- Prove2me | solution 1 for Helfgott.cdemPrefixGroup005_checked
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-09T01:23:08.294935+00:00
-- url     : https://prove2.me/submissions/f503733d-e4d4-40cc-a3bc-e2499eaa6815

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
private theorem cdemPrefixStats_20480_20544 :
    (∑ n ∈ Ico 20480 20544, mobiusTreeValue 16 mobiusTable1200001 n) = (4 : ℤ) ∧
    (∑ n ∈ Ico 20480 20544, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 20480 20544, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (976714 : ℤ) ∧
    (∑ n ∈ Ico 20480 20544, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (19534313071159522506542786991 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_20544_20608 :
    (∑ n ∈ Ico 20544 20608, mobiusTreeValue 16 mobiusTable1200001 n) = (9 : ℤ) ∧
    (∑ n ∈ Ico 20544 20608, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 20544 20608, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (2186937 : ℤ) ∧
    (∑ n ∈ Ico 20544 20608, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (43738877426200619629277226853 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_20480_20608 :
    (∑ n ∈ Ico 20480 20608, mobiusTreeValue 16 mobiusTable1200001 n) = (13 : ℤ) ∧
    (∑ n ∈ Ico 20480 20608, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 20480 20608, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (3163651 : ℤ) ∧
    (∑ n ∈ Ico 20480 20608, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (63273190497360142135820013844 : ℤ) := by
  rcases cdemPrefixStats_20480_20544 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_20544_20608 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 20480 ≤ 20544) (by norm_num : 20544 ≤ 20608), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 20480 ≤ 20544) (by norm_num : 20544 ≤ 20608), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 20480 ≤ 20544) (by norm_num : 20544 ≤ 20608), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 20480 ≤ 20544) (by norm_num : 20544 ≤ 20608), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_20608_20672 :
    (∑ n ∈ Ico 20608 20672, mobiusTreeValue 16 mobiusTable1200001 n) = (11 : ℤ) ∧
    (∑ n ∈ Ico 20608 20672, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 20608 20672, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (2664763 : ℤ) ∧
    (∑ n ∈ Ico 20608 20672, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (53295331177038192015589463750 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_20672_20736 :
    (∑ n ∈ Ico 20672 20736, mobiusTreeValue 16 mobiusTable1200001 n) = (-5 : ℤ) ∧
    (∑ n ∈ Ico 20672 20736, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 20672 20736, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-1207467 : ℤ) ∧
    (∑ n ∈ Ico 20672 20736, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-24149460104716293510525487885 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_20608_20736 :
    (∑ n ∈ Ico 20608 20736, mobiusTreeValue 16 mobiusTable1200001 n) = (6 : ℤ) ∧
    (∑ n ∈ Ico 20608 20736, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (76 : ℕ) ∧
    (∑ n ∈ Ico 20608 20736, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (1457296 : ℤ) ∧
    (∑ n ∈ Ico 20608 20736, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (29145871072321898505063975865 : ℤ) := by
  rcases cdemPrefixStats_20608_20672 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_20672_20736 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 20608 ≤ 20672) (by norm_num : 20672 ≤ 20736), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 20608 ≤ 20672) (by norm_num : 20672 ≤ 20736), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 20608 ≤ 20672) (by norm_num : 20672 ≤ 20736), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 20608 ≤ 20672) (by norm_num : 20672 ≤ 20736), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_20480_20736 :
    (∑ n ∈ Ico 20480 20736, mobiusTreeValue 16 mobiusTable1200001 n) = (19 : ℤ) ∧
    (∑ n ∈ Ico 20480 20736, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (153 : ℕ) ∧
    (∑ n ∈ Ico 20480 20736, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (4620947 : ℤ) ∧
    (∑ n ∈ Ico 20480 20736, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (92419061569682040640883989709 : ℤ) := by
  rcases cdemPrefixStats_20480_20608 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_20608_20736 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 20480 ≤ 20608) (by norm_num : 20608 ≤ 20736), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 20480 ≤ 20608) (by norm_num : 20608 ≤ 20736), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 20480 ≤ 20608) (by norm_num : 20608 ≤ 20736), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 20480 ≤ 20608) (by norm_num : 20608 ≤ 20736), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_20736_20800 :
    (∑ n ∈ Ico 20736 20800, mobiusTreeValue 16 mobiusTable1200001 n) = (3 : ℤ) ∧
    (∑ n ∈ Ico 20736 20800, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 20736 20800, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (721082 : ℤ) ∧
    (∑ n ∈ Ico 20736 20800, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (14421670930945762746321860218 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_20800_20864 :
    (∑ n ∈ Ico 20800 20864, mobiusTreeValue 16 mobiusTable1200001 n) = (-5 : ℤ) ∧
    (∑ n ∈ Ico 20800 20864, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 20800 20864, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-1202174 : ℤ) ∧
    (∑ n ∈ Ico 20800 20864, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-24043499217464050839048922628 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_20736_20864 :
    (∑ n ∈ Ico 20736 20864, mobiusTreeValue 16 mobiusTable1200001 n) = (-2 : ℤ) ∧
    (∑ n ∈ Ico 20736 20864, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (80 : ℕ) ∧
    (∑ n ∈ Ico 20736 20864, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-481092 : ℤ) ∧
    (∑ n ∈ Ico 20736 20864, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-9621828286518288092727062410 : ℤ) := by
  rcases cdemPrefixStats_20736_20800 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_20800_20864 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 20736 ≤ 20800) (by norm_num : 20800 ≤ 20864), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 20736 ≤ 20800) (by norm_num : 20800 ≤ 20864), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 20736 ≤ 20800) (by norm_num : 20800 ≤ 20864), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 20736 ≤ 20800) (by norm_num : 20800 ≤ 20864), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_20864_20928 :
    (∑ n ∈ Ico 20864 20928, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 20864 20928, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 20864 20928, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (238617 : ℤ) ∧
    (∑ n ∈ Ico 20864 20928, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (4772355598608903180580795901 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_20928_20992 :
    (∑ n ∈ Ico 20928 20992, mobiusTreeValue 16 mobiusTable1200001 n) = (-5 : ℤ) ∧
    (∑ n ∈ Ico 20928 20992, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 20928 20992, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-1194168 : ℤ) ∧
    (∑ n ∈ Ico 20928 20992, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-23883444732981304370648438629 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_20864_20992 :
    (∑ n ∈ Ico 20864 20992, mobiusTreeValue 16 mobiusTable1200001 n) = (-4 : ℤ) ∧
    (∑ n ∈ Ico 20864 20992, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 20864 20992, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-955551 : ℤ) ∧
    (∑ n ∈ Ico 20864 20992, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-19111089134372401190067642728 : ℤ) := by
  rcases cdemPrefixStats_20864_20928 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_20928_20992 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 20864 ≤ 20928) (by norm_num : 20928 ≤ 20992), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 20864 ≤ 20928) (by norm_num : 20928 ≤ 20992), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 20864 ≤ 20928) (by norm_num : 20928 ≤ 20992), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 20864 ≤ 20928) (by norm_num : 20928 ≤ 20992), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_20736_20992 :
    (∑ n ∈ Ico 20736 20992, mobiusTreeValue 16 mobiusTable1200001 n) = (-6 : ℤ) ∧
    (∑ n ∈ Ico 20736 20992, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (158 : ℕ) ∧
    (∑ n ∈ Ico 20736 20992, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-1436643 : ℤ) ∧
    (∑ n ∈ Ico 20736 20992, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-28732917420890689282794705138 : ℤ) := by
  rcases cdemPrefixStats_20736_20864 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_20864_20992 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 20736 ≤ 20864) (by norm_num : 20864 ≤ 20992), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 20736 ≤ 20864) (by norm_num : 20864 ≤ 20992), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 20736 ≤ 20864) (by norm_num : 20864 ≤ 20992), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 20736 ≤ 20864) (by norm_num : 20864 ≤ 20992), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_20480_20992 :
    (∑ n ∈ Ico 20480 20992, mobiusTreeValue 16 mobiusTable1200001 n) = (13 : ℤ) ∧
    (∑ n ∈ Ico 20480 20992, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (311 : ℕ) ∧
    (∑ n ∈ Ico 20480 20992, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (3184304 : ℤ) ∧
    (∑ n ∈ Ico 20480 20992, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (63686144148791351358089284571 : ℤ) := by
  rcases cdemPrefixStats_20480_20736 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_20736_20992 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 20480 ≤ 20736) (by norm_num : 20736 ≤ 20992), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 20480 ≤ 20736) (by norm_num : 20736 ≤ 20992), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 20480 ≤ 20736) (by norm_num : 20736 ≤ 20992), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 20480 ≤ 20736) (by norm_num : 20736 ≤ 20992), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_20992_21056 :
    (∑ n ∈ Ico 20992 21056, mobiusTreeValue 16 mobiusTable1200001 n) = (4 : ℤ) ∧
    (∑ n ∈ Ico 20992 21056, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 20992 21056, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (950997 : ℤ) ∧
    (∑ n ∈ Ico 20992 21056, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (19020036353153538221802181614 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_21056_21120 :
    (∑ n ∈ Ico 21056 21120, mobiusTreeValue 16 mobiusTable1200001 n) = (-5 : ℤ) ∧
    (∑ n ∈ Ico 21056 21120, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 21056 21120, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-1184340 : ℤ) ∧
    (∑ n ∈ Ico 21056 21120, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-23686780425085863306007674388 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_20992_21120 :
    (∑ n ∈ Ico 20992 21120, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 20992 21120, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 20992 21120, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-233343 : ℤ) ∧
    (∑ n ∈ Ico 20992 21120, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-4666744071932325084205492774 : ℤ) := by
  rcases cdemPrefixStats_20992_21056 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_21056_21120 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 20992 ≤ 21056) (by norm_num : 21056 ≤ 21120), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 20992 ≤ 21056) (by norm_num : 21056 ≤ 21120), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 20992 ≤ 21056) (by norm_num : 21056 ≤ 21120), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 20992 ≤ 21056) (by norm_num : 21056 ≤ 21120), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_21120_21184 :
    (∑ n ∈ Ico 21120 21184, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 21120 21184, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 21120 21184, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-402 : ℤ) ∧
    (∑ n ∈ Ico 21120 21184, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-8038757248173437407324871 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_21184_21248 :
    (∑ n ∈ Ico 21184 21248, mobiusTreeValue 16 mobiusTable1200001 n) = (-6 : ℤ) ∧
    (∑ n ∈ Ico 21184 21248, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 21184 21248, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-1415415 : ℤ) ∧
    (∑ n ∈ Ico 21184 21248, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-28308362190335500361936157700 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_21120_21248 :
    (∑ n ∈ Ico 21120 21248, mobiusTreeValue 16 mobiusTable1200001 n) = (-6 : ℤ) ∧
    (∑ n ∈ Ico 21120 21248, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (80 : ℕ) ∧
    (∑ n ∈ Ico 21120 21248, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-1415817 : ℤ) ∧
    (∑ n ∈ Ico 21120 21248, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-28316400947583673799343482571 : ℤ) := by
  rcases cdemPrefixStats_21120_21184 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_21184_21248 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 21120 ≤ 21184) (by norm_num : 21184 ≤ 21248), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 21120 ≤ 21184) (by norm_num : 21184 ≤ 21248), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 21120 ≤ 21184) (by norm_num : 21184 ≤ 21248), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 21120 ≤ 21184) (by norm_num : 21184 ≤ 21248), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_20992_21248 :
    (∑ n ∈ Ico 20992 21248, mobiusTreeValue 16 mobiusTable1200001 n) = (-7 : ℤ) ∧
    (∑ n ∈ Ico 20992 21248, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (157 : ℕ) ∧
    (∑ n ∈ Ico 20992 21248, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-1649160 : ℤ) ∧
    (∑ n ∈ Ico 20992 21248, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-32983145019515998883548975345 : ℤ) := by
  rcases cdemPrefixStats_20992_21120 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_21120_21248 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 20992 ≤ 21120) (by norm_num : 21120 ≤ 21248), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 20992 ≤ 21120) (by norm_num : 21120 ≤ 21248), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 20992 ≤ 21120) (by norm_num : 21120 ≤ 21248), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 20992 ≤ 21120) (by norm_num : 21120 ≤ 21248), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_21248_21312 :
    (∑ n ∈ Ico 21248 21312, mobiusTreeValue 16 mobiusTable1200001 n) = (6 : ℤ) ∧
    (∑ n ∈ Ico 21248 21312, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 21248 21312, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (1411341 : ℤ) ∧
    (∑ n ∈ Ico 21248 21312, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (28226903035796855078479580936 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_21312_21376 :
    (∑ n ∈ Ico 21312 21376, mobiusTreeValue 16 mobiusTable1200001 n) = (-9 : ℤ) ∧
    (∑ n ∈ Ico 21312 21376, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 21312 21376, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-2108974 : ℤ) ∧
    (∑ n ∈ Ico 21312 21376, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-42179624171398341964767459106 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_21248_21376 :
    (∑ n ∈ Ico 21248 21376, mobiusTreeValue 16 mobiusTable1200001 n) = (-3 : ℤ) ∧
    (∑ n ∈ Ico 21248 21376, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 21248 21376, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-697633 : ℤ) ∧
    (∑ n ∈ Ico 21248 21376, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-13952721135601486886287878170 : ℤ) := by
  rcases cdemPrefixStats_21248_21312 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_21312_21376 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 21248 ≤ 21312) (by norm_num : 21312 ≤ 21376), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 21248 ≤ 21312) (by norm_num : 21312 ≤ 21376), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 21248 ≤ 21312) (by norm_num : 21312 ≤ 21376), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 21248 ≤ 21312) (by norm_num : 21312 ≤ 21376), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_21376_21440 :
    (∑ n ∈ Ico 21376 21440, mobiusTreeValue 16 mobiusTable1200001 n) = (-5 : ℤ) ∧
    (∑ n ∈ Ico 21376 21440, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 21376 21440, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-1167613 : ℤ) ∧
    (∑ n ∈ Ico 21376 21440, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-23352281303737794484429403146 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_21440_21504 :
    (∑ n ∈ Ico 21440 21504, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 21440 21504, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 21440 21504, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-229759 : ℤ) ∧
    (∑ n ∈ Ico 21440 21504, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-4595234744625258470482218426 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_21376_21504 :
    (∑ n ∈ Ico 21376 21504, mobiusTreeValue 16 mobiusTable1200001 n) = (-6 : ℤ) ∧
    (∑ n ∈ Ico 21376 21504, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 21376 21504, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-1397372 : ℤ) ∧
    (∑ n ∈ Ico 21376 21504, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-27947516048363052954911621572 : ℤ) := by
  rcases cdemPrefixStats_21376_21440 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_21440_21504 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 21376 ≤ 21440) (by norm_num : 21440 ≤ 21504), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 21376 ≤ 21440) (by norm_num : 21440 ≤ 21504), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 21376 ≤ 21440) (by norm_num : 21440 ≤ 21504), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 21376 ≤ 21440) (by norm_num : 21440 ≤ 21504), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_21248_21504 :
    (∑ n ∈ Ico 21248 21504, mobiusTreeValue 16 mobiusTable1200001 n) = (-9 : ℤ) ∧
    (∑ n ∈ Ico 21248 21504, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (155 : ℕ) ∧
    (∑ n ∈ Ico 21248 21504, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-2095005 : ℤ) ∧
    (∑ n ∈ Ico 21248 21504, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-41900237183964539841199499742 : ℤ) := by
  rcases cdemPrefixStats_21248_21376 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_21376_21504 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 21248 ≤ 21376) (by norm_num : 21376 ≤ 21504), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 21248 ≤ 21376) (by norm_num : 21376 ≤ 21504), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 21248 ≤ 21376) (by norm_num : 21376 ≤ 21504), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 21248 ≤ 21376) (by norm_num : 21376 ≤ 21504), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_20992_21504 :
    (∑ n ∈ Ico 20992 21504, mobiusTreeValue 16 mobiusTable1200001 n) = (-16 : ℤ) ∧
    (∑ n ∈ Ico 20992 21504, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (312 : ℕ) ∧
    (∑ n ∈ Ico 20992 21504, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-3744165 : ℤ) ∧
    (∑ n ∈ Ico 20992 21504, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-74883382203480538724748475087 : ℤ) := by
  rcases cdemPrefixStats_20992_21248 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_21248_21504 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 20992 ≤ 21248) (by norm_num : 21248 ≤ 21504), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 20992 ≤ 21248) (by norm_num : 21248 ≤ 21504), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 20992 ≤ 21248) (by norm_num : 21248 ≤ 21504), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 20992 ≤ 21248) (by norm_num : 21248 ≤ 21504), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_20480_21504 :
    (∑ n ∈ Ico 20480 21504, mobiusTreeValue 16 mobiusTable1200001 n) = (-3 : ℤ) ∧
    (∑ n ∈ Ico 20480 21504, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (623 : ℕ) ∧
    (∑ n ∈ Ico 20480 21504, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-559861 : ℤ) ∧
    (∑ n ∈ Ico 20480 21504, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-11197238054689187366659190516 : ℤ) := by
  rcases cdemPrefixStats_20480_20992 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_20992_21504 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 20480 ≤ 20992) (by norm_num : 20992 ≤ 21504), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 20480 ≤ 20992) (by norm_num : 20992 ≤ 21504), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 20480 ≤ 20992) (by norm_num : 20992 ≤ 21504), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 20480 ≤ 20992) (by norm_num : 20992 ≤ 21504), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_21504_21568 :
    (∑ n ∈ Ico 21504 21568, mobiusTreeValue 16 mobiusTable1200001 n) = (-7 : ℤ) ∧
    (∑ n ∈ Ico 21504 21568, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 21504 21568, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-1624959 : ℤ) ∧
    (∑ n ∈ Ico 21504 21568, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-32499204555424312015153128055 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_21568_21632 :
    (∑ n ∈ Ico 21568 21632, mobiusTreeValue 16 mobiusTable1200001 n) = (-8 : ℤ) ∧
    (∑ n ∈ Ico 21568 21632, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 21568 21632, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-1851656 : ℤ) ∧
    (∑ n ∈ Ico 21568 21632, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-37033173701539862415894173168 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_21504_21632 :
    (∑ n ∈ Ico 21504 21632, mobiusTreeValue 16 mobiusTable1200001 n) = (-15 : ℤ) ∧
    (∑ n ∈ Ico 21504 21632, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (79 : ℕ) ∧
    (∑ n ∈ Ico 21504 21632, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-3476615 : ℤ) ∧
    (∑ n ∈ Ico 21504 21632, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-69532378256964174431047301223 : ℤ) := by
  rcases cdemPrefixStats_21504_21568 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_21568_21632 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 21504 ≤ 21568) (by norm_num : 21568 ≤ 21632), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 21504 ≤ 21568) (by norm_num : 21568 ≤ 21632), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 21504 ≤ 21568) (by norm_num : 21568 ≤ 21632), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 21504 ≤ 21568) (by norm_num : 21568 ≤ 21632), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_21632_21696 :
    (∑ n ∈ Ico 21632 21696, mobiusTreeValue 16 mobiusTable1200001 n) = (-2 : ℤ) ∧
    (∑ n ∈ Ico 21632 21696, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 21632 21696, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-462849 : ℤ) ∧
    (∑ n ∈ Ico 21632 21696, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-9257047623020069614668408351 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_21696_21760 :
    (∑ n ∈ Ico 21696 21760, mobiusTreeValue 16 mobiusTable1200001 n) = (-2 : ℤ) ∧
    (∑ n ∈ Ico 21696 21760, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 21696 21760, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-459386 : ℤ) ∧
    (∑ n ∈ Ico 21696 21760, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-9187787127079763217374728158 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_21632_21760 :
    (∑ n ∈ Ico 21632 21760, mobiusTreeValue 16 mobiusTable1200001 n) = (-4 : ℤ) ∧
    (∑ n ∈ Ico 21632 21760, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 21632 21760, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-922235 : ℤ) ∧
    (∑ n ∈ Ico 21632 21760, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-18444834750099832832043136509 : ℤ) := by
  rcases cdemPrefixStats_21632_21696 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_21696_21760 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 21632 ≤ 21696) (by norm_num : 21696 ≤ 21760), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 21632 ≤ 21696) (by norm_num : 21696 ≤ 21760), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 21632 ≤ 21696) (by norm_num : 21696 ≤ 21760), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 21632 ≤ 21696) (by norm_num : 21696 ≤ 21760), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_21504_21760 :
    (∑ n ∈ Ico 21504 21760, mobiusTreeValue 16 mobiusTable1200001 n) = (-19 : ℤ) ∧
    (∑ n ∈ Ico 21504 21760, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (157 : ℕ) ∧
    (∑ n ∈ Ico 21504 21760, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-4398850 : ℤ) ∧
    (∑ n ∈ Ico 21504 21760, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-87977213007064007263090437732 : ℤ) := by
  rcases cdemPrefixStats_21504_21632 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_21632_21760 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 21504 ≤ 21632) (by norm_num : 21632 ≤ 21760), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 21504 ≤ 21632) (by norm_num : 21632 ≤ 21760), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 21504 ≤ 21632) (by norm_num : 21632 ≤ 21760), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 21504 ≤ 21632) (by norm_num : 21632 ≤ 21760), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_21760_21824 :
    (∑ n ∈ Ico 21760 21824, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 21760 21824, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 21760 21824, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (1684 : ℤ) ∧
    (∑ n ∈ Ico 21760 21824, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (33710036117450493124384056 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_21824_21888 :
    (∑ n ∈ Ico 21824 21888, mobiusTreeValue 16 mobiusTable1200001 n) = (-5 : ℤ) ∧
    (∑ n ∈ Ico 21824 21888, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 21824 21888, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-1145148 : ℤ) ∧
    (∑ n ∈ Ico 21824 21888, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-22902985313532569806558511639 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_21760_21888 :
    (∑ n ∈ Ico 21760 21888, mobiusTreeValue 16 mobiusTable1200001 n) = (-5 : ℤ) ∧
    (∑ n ∈ Ico 21760 21888, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 21760 21888, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-1143464 : ℤ) ∧
    (∑ n ∈ Ico 21760 21888, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-22869275277415119313434127583 : ℤ) := by
  rcases cdemPrefixStats_21760_21824 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_21824_21888 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 21760 ≤ 21824) (by norm_num : 21824 ≤ 21888), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 21760 ≤ 21824) (by norm_num : 21824 ≤ 21888), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 21760 ≤ 21824) (by norm_num : 21824 ≤ 21888), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 21760 ≤ 21824) (by norm_num : 21824 ≤ 21888), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_21888_21952 :
    (∑ n ∈ Ico 21888 21952, mobiusTreeValue 16 mobiusTable1200001 n) = (-2 : ℤ) ∧
    (∑ n ∈ Ico 21888 21952, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 21888 21952, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-455341 : ℤ) ∧
    (∑ n ∈ Ico 21888 21952, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-9106808862216313987090083639 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_21952_22016 :
    (∑ n ∈ Ico 21952 22016, mobiusTreeValue 16 mobiusTable1200001 n) = (6 : ℤ) ∧
    (∑ n ∈ Ico 21952 22016, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 21952 22016, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (1364042 : ℤ) ∧
    (∑ n ∈ Ico 21952 22016, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (27280821235270061037545406537 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_21888_22016 :
    (∑ n ∈ Ico 21888 22016, mobiusTreeValue 16 mobiusTable1200001 n) = (4 : ℤ) ∧
    (∑ n ∈ Ico 21888 22016, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 21888 22016, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (908701 : ℤ) ∧
    (∑ n ∈ Ico 21888 22016, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (18174012373053747050455322898 : ℤ) := by
  rcases cdemPrefixStats_21888_21952 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_21952_22016 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 21888 ≤ 21952) (by norm_num : 21952 ≤ 22016), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 21888 ≤ 21952) (by norm_num : 21952 ≤ 22016), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 21888 ≤ 21952) (by norm_num : 21952 ≤ 22016), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 21888 ≤ 21952) (by norm_num : 21952 ≤ 22016), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_21760_22016 :
    (∑ n ∈ Ico 21760 22016, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 21760 22016, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (155 : ℕ) ∧
    (∑ n ∈ Ico 21760 22016, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-234763 : ℤ) ∧
    (∑ n ∈ Ico 21760 22016, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-4695262904361372262978804685 : ℤ) := by
  rcases cdemPrefixStats_21760_21888 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_21888_22016 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 21760 ≤ 21888) (by norm_num : 21888 ≤ 22016), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 21760 ≤ 21888) (by norm_num : 21888 ≤ 22016), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 21760 ≤ 21888) (by norm_num : 21888 ≤ 22016), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 21760 ≤ 21888) (by norm_num : 21888 ≤ 22016), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_21504_22016 :
    (∑ n ∈ Ico 21504 22016, mobiusTreeValue 16 mobiusTable1200001 n) = (-20 : ℤ) ∧
    (∑ n ∈ Ico 21504 22016, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (312 : ℕ) ∧
    (∑ n ∈ Ico 21504 22016, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-4633613 : ℤ) ∧
    (∑ n ∈ Ico 21504 22016, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-92672475911425379526069242417 : ℤ) := by
  rcases cdemPrefixStats_21504_21760 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_21760_22016 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 21504 ≤ 21760) (by norm_num : 21760 ≤ 22016), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 21504 ≤ 21760) (by norm_num : 21760 ≤ 22016), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 21504 ≤ 21760) (by norm_num : 21760 ≤ 22016), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 21504 ≤ 21760) (by norm_num : 21760 ≤ 22016), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_22016_22080 :
    (∑ n ∈ Ico 22016 22080, mobiusTreeValue 16 mobiusTable1200001 n) = (-13 : ℤ) ∧
    (∑ n ∈ Ico 22016 22080, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 22016 22080, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-2948923 : ℤ) ∧
    (∑ n ∈ Ico 22016 22080, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-58978556684599514327790552616 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_22080_22144 :
    (∑ n ∈ Ico 22080 22144, mobiusTreeValue 16 mobiusTable1200001 n) = (-5 : ℤ) ∧
    (∑ n ∈ Ico 22080 22144, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 22080 22144, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-1130935 : ℤ) ∧
    (∑ n ∈ Ico 22080 22144, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-22618719450027940581776093710 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_22016_22144 :
    (∑ n ∈ Ico 22016 22144, mobiusTreeValue 16 mobiusTable1200001 n) = (-18 : ℤ) ∧
    (∑ n ∈ Ico 22016 22144, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (76 : ℕ) ∧
    (∑ n ∈ Ico 22016 22144, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-4079858 : ℤ) ∧
    (∑ n ∈ Ico 22016 22144, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-81597276134627454909566646326 : ℤ) := by
  rcases cdemPrefixStats_22016_22080 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_22080_22144 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 22016 ≤ 22080) (by norm_num : 22080 ≤ 22144), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 22016 ≤ 22080) (by norm_num : 22080 ≤ 22144), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 22016 ≤ 22080) (by norm_num : 22080 ≤ 22144), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 22016 ≤ 22080) (by norm_num : 22080 ≤ 22144), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_22144_22208 :
    (∑ n ∈ Ico 22144 22208, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 22144 22208, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 22144 22208, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-539 : ℤ) ∧
    (∑ n ∈ Ico 22144 22208, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-10801331001793015672071450 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_22208_22272 :
    (∑ n ∈ Ico 22208 22272, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 22208 22272, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 22208 22272, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-315 : ℤ) ∧
    (∑ n ∈ Ico 22208 22272, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-6297714633661008207744988 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_22144_22272 :
    (∑ n ∈ Ico 22144 22272, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 22144 22272, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (76 : ℕ) ∧
    (∑ n ∈ Ico 22144 22272, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-854 : ℤ) ∧
    (∑ n ∈ Ico 22144 22272, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-17099045635454023879816438 : ℤ) := by
  rcases cdemPrefixStats_22144_22208 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_22208_22272 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 22144 ≤ 22208) (by norm_num : 22208 ≤ 22272), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 22144 ≤ 22208) (by norm_num : 22208 ≤ 22272), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 22144 ≤ 22208) (by norm_num : 22208 ≤ 22272), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 22144 ≤ 22208) (by norm_num : 22208 ≤ 22272), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_22016_22272 :
    (∑ n ∈ Ico 22016 22272, mobiusTreeValue 16 mobiusTable1200001 n) = (-18 : ℤ) ∧
    (∑ n ∈ Ico 22016 22272, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (152 : ℕ) ∧
    (∑ n ∈ Ico 22016 22272, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-4080712 : ℤ) ∧
    (∑ n ∈ Ico 22016 22272, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-81614375180262908933446462764 : ℤ) := by
  rcases cdemPrefixStats_22016_22144 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_22144_22272 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 22016 ≤ 22144) (by norm_num : 22144 ≤ 22272), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 22016 ≤ 22144) (by norm_num : 22144 ≤ 22272), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 22016 ≤ 22144) (by norm_num : 22144 ≤ 22272), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 22016 ≤ 22144) (by norm_num : 22144 ≤ 22272), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_22272_22336 :
    (∑ n ∈ Ico 22272 22336, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 22272 22336, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 22272 22336, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-544 : ℤ) ∧
    (∑ n ∈ Ico 22272 22336, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-10872635081590893200773024 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_22336_22400 :
    (∑ n ∈ Ico 22336 22400, mobiusTreeValue 16 mobiusTable1200001 n) = (-10 : ℤ) ∧
    (∑ n ∈ Ico 22336 22400, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 22336 22400, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-2234212 : ℤ) ∧
    (∑ n ∈ Ico 22336 22400, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-44684355726047892734072602561 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_22272_22400 :
    (∑ n ∈ Ico 22272 22400, mobiusTreeValue 16 mobiusTable1200001 n) = (-10 : ℤ) ∧
    (∑ n ∈ Ico 22272 22400, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 22272 22400, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-2234756 : ℤ) ∧
    (∑ n ∈ Ico 22272 22400, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-44695228361129483627273375585 : ℤ) := by
  rcases cdemPrefixStats_22272_22336 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_22336_22400 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 22272 ≤ 22336) (by norm_num : 22336 ≤ 22400), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 22272 ≤ 22336) (by norm_num : 22336 ≤ 22400), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 22272 ≤ 22336) (by norm_num : 22336 ≤ 22400), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 22272 ≤ 22336) (by norm_num : 22336 ≤ 22400), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_22400_22464 :
    (∑ n ∈ Ico 22400 22464, mobiusTreeValue 16 mobiusTable1200001 n) = (2 : ℤ) ∧
    (∑ n ∈ Ico 22400 22464, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 22400 22464, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (446149 : ℤ) ∧
    (∑ n ∈ Ico 22400 22464, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (8923003893043946840109669421 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_22464_22528 :
    (∑ n ∈ Ico 22464 22528, mobiusTreeValue 16 mobiusTable1200001 n) = (4 : ℤ) ∧
    (∑ n ∈ Ico 22464 22528, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 22464 22528, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (888110 : ℤ) ∧
    (∑ n ∈ Ico 22464 22528, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (17762177380617938118163810430 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_22400_22528 :
    (∑ n ∈ Ico 22400 22528, mobiusTreeValue 16 mobiusTable1200001 n) = (6 : ℤ) ∧
    (∑ n ∈ Ico 22400 22528, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (76 : ℕ) ∧
    (∑ n ∈ Ico 22400 22528, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (1334259 : ℤ) ∧
    (∑ n ∈ Ico 22400 22528, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (26685181273661884958273479851 : ℤ) := by
  rcases cdemPrefixStats_22400_22464 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_22464_22528 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 22400 ≤ 22464) (by norm_num : 22464 ≤ 22528), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 22400 ≤ 22464) (by norm_num : 22464 ≤ 22528), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 22400 ≤ 22464) (by norm_num : 22464 ≤ 22528), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 22400 ≤ 22464) (by norm_num : 22464 ≤ 22528), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_22272_22528 :
    (∑ n ∈ Ico 22272 22528, mobiusTreeValue 16 mobiusTable1200001 n) = (-4 : ℤ) ∧
    (∑ n ∈ Ico 22272 22528, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (154 : ℕ) ∧
    (∑ n ∈ Ico 22272 22528, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-900497 : ℤ) ∧
    (∑ n ∈ Ico 22272 22528, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-18010047087467598668999895734 : ℤ) := by
  rcases cdemPrefixStats_22272_22400 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_22400_22528 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 22272 ≤ 22400) (by norm_num : 22400 ≤ 22528), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 22272 ≤ 22400) (by norm_num : 22400 ≤ 22528), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 22272 ≤ 22400) (by norm_num : 22400 ≤ 22528), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 22272 ≤ 22400) (by norm_num : 22400 ≤ 22528), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_22016_22528 :
    (∑ n ∈ Ico 22016 22528, mobiusTreeValue 16 mobiusTable1200001 n) = (-22 : ℤ) ∧
    (∑ n ∈ Ico 22016 22528, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (306 : ℕ) ∧
    (∑ n ∈ Ico 22016 22528, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-4981209 : ℤ) ∧
    (∑ n ∈ Ico 22016 22528, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-99624422267730507602446358498 : ℤ) := by
  rcases cdemPrefixStats_22016_22272 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_22272_22528 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 22016 ≤ 22272) (by norm_num : 22272 ≤ 22528), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 22016 ≤ 22272) (by norm_num : 22272 ≤ 22528), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 22016 ≤ 22272) (by norm_num : 22272 ≤ 22528), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 22016 ≤ 22272) (by norm_num : 22272 ≤ 22528), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_21504_22528 :
    (∑ n ∈ Ico 21504 22528, mobiusTreeValue 16 mobiusTable1200001 n) = (-42 : ℤ) ∧
    (∑ n ∈ Ico 21504 22528, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (618 : ℕ) ∧
    (∑ n ∈ Ico 21504 22528, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-9614822 : ℤ) ∧
    (∑ n ∈ Ico 21504 22528, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-192296898179155887128515600915 : ℤ) := by
  rcases cdemPrefixStats_21504_22016 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_22016_22528 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 21504 ≤ 22016) (by norm_num : 22016 ≤ 22528), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 21504 ≤ 22016) (by norm_num : 22016 ≤ 22528), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 21504 ≤ 22016) (by norm_num : 22016 ≤ 22528), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 21504 ≤ 22016) (by norm_num : 22016 ≤ 22528), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_20480_22528 :
    (∑ n ∈ Ico 20480 22528, mobiusTreeValue 16 mobiusTable1200001 n) = (-45 : ℤ) ∧
    (∑ n ∈ Ico 20480 22528, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (1241 : ℕ) ∧
    (∑ n ∈ Ico 20480 22528, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-10174683 : ℤ) ∧
    (∑ n ∈ Ico 20480 22528, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-203494136233845074495174791431 : ℤ) := by
  rcases cdemPrefixStats_20480_21504 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_21504_22528 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 20480 ≤ 21504) (by norm_num : 21504 ≤ 22528), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 20480 ≤ 21504) (by norm_num : 21504 ≤ 22528), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 20480 ≤ 21504) (by norm_num : 21504 ≤ 22528), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 20480 ≤ 21504) (by norm_num : 21504 ≤ 22528), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_22528_22592 :
    (∑ n ∈ Ico 22528 22592, mobiusTreeValue 16 mobiusTable1200001 n) = (3 : ℤ) ∧
    (∑ n ∈ Ico 22528 22592, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 22528 22592, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (664704 : ℤ) ∧
    (∑ n ∈ Ico 22528 22592, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (13294154486158398990560372250 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_22592_22656 :
    (∑ n ∈ Ico 22592 22656, mobiusTreeValue 16 mobiusTable1200001 n) = (-2 : ℤ) ∧
    (∑ n ∈ Ico 22592 22656, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 22592 22656, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-440170 : ℤ) ∧
    (∑ n ∈ Ico 22592 22656, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-8803445995115372294153421830 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_22528_22656 :
    (∑ n ∈ Ico 22528 22656, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 22528 22656, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 22528 22656, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (224534 : ℤ) ∧
    (∑ n ∈ Ico 22528 22656, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (4490708491043026696406950420 : ℤ) := by
  rcases cdemPrefixStats_22528_22592 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_22592_22656 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 22528 ≤ 22592) (by norm_num : 22592 ≤ 22656), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 22528 ≤ 22592) (by norm_num : 22592 ≤ 22656), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 22528 ≤ 22592) (by norm_num : 22592 ≤ 22656), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 22528 ≤ 22592) (by norm_num : 22592 ≤ 22656), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_22656_22720 :
    (∑ n ∈ Ico 22656 22720, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 22656 22720, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 22656 22720, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-220197 : ℤ) ∧
    (∑ n ∈ Ico 22656 22720, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-4403918676317599174612009990 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_22720_22784 :
    (∑ n ∈ Ico 22720 22784, mobiusTreeValue 16 mobiusTable1200001 n) = (-3 : ℤ) ∧
    (∑ n ∈ Ico 22720 22784, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 22720 22784, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-657969 : ℤ) ∧
    (∑ n ∈ Ico 22720 22784, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-13159417384329994726137637122 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_22656_22784 :
    (∑ n ∈ Ico 22656 22784, mobiusTreeValue 16 mobiusTable1200001 n) = (-4 : ℤ) ∧
    (∑ n ∈ Ico 22656 22784, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (80 : ℕ) ∧
    (∑ n ∈ Ico 22656 22784, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-878166 : ℤ) ∧
    (∑ n ∈ Ico 22656 22784, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-17563336060647593900749647112 : ℤ) := by
  rcases cdemPrefixStats_22656_22720 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_22720_22784 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 22656 ≤ 22720) (by norm_num : 22720 ≤ 22784), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 22656 ≤ 22720) (by norm_num : 22720 ≤ 22784), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 22656 ≤ 22720) (by norm_num : 22720 ≤ 22784), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 22656 ≤ 22720) (by norm_num : 22720 ≤ 22784), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_22528_22784 :
    (∑ n ∈ Ico 22528 22784, mobiusTreeValue 16 mobiusTable1200001 n) = (-3 : ℤ) ∧
    (∑ n ∈ Ico 22528 22784, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (157 : ℕ) ∧
    (∑ n ∈ Ico 22528 22784, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-653632 : ℤ) ∧
    (∑ n ∈ Ico 22528 22784, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-13072627569604567204342696692 : ℤ) := by
  rcases cdemPrefixStats_22528_22656 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_22656_22784 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 22528 ≤ 22656) (by norm_num : 22656 ≤ 22784), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 22528 ≤ 22656) (by norm_num : 22656 ≤ 22784), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 22528 ≤ 22656) (by norm_num : 22656 ≤ 22784), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 22528 ≤ 22656) (by norm_num : 22656 ≤ 22784), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_22784_22848 :
    (∑ n ∈ Ico 22784 22848, mobiusTreeValue 16 mobiusTable1200001 n) = (4 : ℤ) ∧
    (∑ n ∈ Ico 22784 22848, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 22784 22848, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (877276 : ℤ) ∧
    (∑ n ∈ Ico 22784 22848, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (17545587912326083697939138918 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_22848_22912 :
    (∑ n ∈ Ico 22848 22912, mobiusTreeValue 16 mobiusTable1200001 n) = (-3 : ℤ) ∧
    (∑ n ∈ Ico 22848 22912, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 22848 22912, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-655899 : ℤ) ∧
    (∑ n ∈ Ico 22848 22912, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-13118010051049872700775004369 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_22784_22912 :
    (∑ n ∈ Ico 22784 22912, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 22784 22912, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 22784 22912, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (221377 : ℤ) ∧
    (∑ n ∈ Ico 22784 22912, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (4427577861276210997164134549 : ℤ) := by
  rcases cdemPrefixStats_22784_22848 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_22848_22912 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 22784 ≤ 22848) (by norm_num : 22848 ≤ 22912), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 22784 ≤ 22848) (by norm_num : 22848 ≤ 22912), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 22784 ≤ 22848) (by norm_num : 22848 ≤ 22912), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 22784 ≤ 22848) (by norm_num : 22848 ≤ 22912), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_22912_22976 :
    (∑ n ∈ Ico 22912 22976, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 22912 22976, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 22912 22976, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-217912 : ℤ) ∧
    (∑ n ∈ Ico 22912 22976, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-4358245842359385765037459282 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_22976_23040 :
    (∑ n ∈ Ico 22976 23040, mobiusTreeValue 16 mobiusTable1200001 n) = (-2 : ℤ) ∧
    (∑ n ∈ Ico 22976 23040, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 22976 23040, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-433006 : ℤ) ∧
    (∑ n ∈ Ico 22976 23040, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-8660127879433471873486590862 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_22912_23040 :
    (∑ n ∈ Ico 22912 23040, mobiusTreeValue 16 mobiusTable1200001 n) = (-3 : ℤ) ∧
    (∑ n ∈ Ico 22912 23040, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (79 : ℕ) ∧
    (∑ n ∈ Ico 22912 23040, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-650918 : ℤ) ∧
    (∑ n ∈ Ico 22912 23040, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-13018373721792857638524050144 : ℤ) := by
  rcases cdemPrefixStats_22912_22976 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_22976_23040 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 22912 ≤ 22976) (by norm_num : 22976 ≤ 23040), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 22912 ≤ 22976) (by norm_num : 22976 ≤ 23040), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 22912 ≤ 22976) (by norm_num : 22976 ≤ 23040), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 22912 ≤ 22976) (by norm_num : 22976 ≤ 23040), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_22784_23040 :
    (∑ n ∈ Ico 22784 23040, mobiusTreeValue 16 mobiusTable1200001 n) = (-2 : ℤ) ∧
    (∑ n ∈ Ico 22784 23040, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (156 : ℕ) ∧
    (∑ n ∈ Ico 22784 23040, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-429541 : ℤ) ∧
    (∑ n ∈ Ico 22784 23040, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-8590795860516646641359915595 : ℤ) := by
  rcases cdemPrefixStats_22784_22912 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_22912_23040 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 22784 ≤ 22912) (by norm_num : 22912 ≤ 23040), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 22784 ≤ 22912) (by norm_num : 22912 ≤ 23040), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 22784 ≤ 22912) (by norm_num : 22912 ≤ 23040), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 22784 ≤ 22912) (by norm_num : 22912 ≤ 23040), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_22528_23040 :
    (∑ n ∈ Ico 22528 23040, mobiusTreeValue 16 mobiusTable1200001 n) = (-5 : ℤ) ∧
    (∑ n ∈ Ico 22528 23040, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (313 : ℕ) ∧
    (∑ n ∈ Ico 22528 23040, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-1083173 : ℤ) ∧
    (∑ n ∈ Ico 22528 23040, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-21663423430121213845702612287 : ℤ) := by
  rcases cdemPrefixStats_22528_22784 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_22784_23040 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 22528 ≤ 22784) (by norm_num : 22784 ≤ 23040), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 22528 ≤ 22784) (by norm_num : 22784 ≤ 23040), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 22528 ≤ 22784) (by norm_num : 22784 ≤ 23040), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 22528 ≤ 22784) (by norm_num : 22784 ≤ 23040), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_23040_23104 :
    (∑ n ∈ Ico 23040 23104, mobiusTreeValue 16 mobiusTable1200001 n) = (-5 : ℤ) ∧
    (∑ n ∈ Ico 23040 23104, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 23040 23104, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-1084636 : ℤ) ∧
    (∑ n ∈ Ico 23040 23104, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-21692701278492683669051188848 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_23104_23168 :
    (∑ n ∈ Ico 23104 23168, mobiusTreeValue 16 mobiusTable1200001 n) = (-7 : ℤ) ∧
    (∑ n ∈ Ico 23104 23168, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 23104 23168, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-1511093 : ℤ) ∧
    (∑ n ∈ Ico 23104 23168, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-30221891744878750956208439686 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_23040_23168 :
    (∑ n ∈ Ico 23040 23168, mobiusTreeValue 16 mobiusTable1200001 n) = (-12 : ℤ) ∧
    (∑ n ∈ Ico 23040 23168, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 23040 23168, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-2595729 : ℤ) ∧
    (∑ n ∈ Ico 23040 23168, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-51914593023371434625259628534 : ℤ) := by
  rcases cdemPrefixStats_23040_23104 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_23104_23168 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 23040 ≤ 23104) (by norm_num : 23104 ≤ 23168), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 23040 ≤ 23104) (by norm_num : 23104 ≤ 23168), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 23040 ≤ 23104) (by norm_num : 23104 ≤ 23168), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 23040 ≤ 23104) (by norm_num : 23104 ≤ 23168), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_23168_23232 :
    (∑ n ∈ Ico 23168 23232, mobiusTreeValue 16 mobiusTable1200001 n) = (6 : ℤ) ∧
    (∑ n ∈ Ico 23168 23232, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 23168 23232, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (1293158 : ℤ) ∧
    (∑ n ∈ Ico 23168 23232, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (25863211654789255205085898977 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_23232_23296 :
    (∑ n ∈ Ico 23232 23296, mobiusTreeValue 16 mobiusTable1200001 n) = (4 : ℤ) ∧
    (∑ n ∈ Ico 23232 23296, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 23232 23296, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (862161 : ℤ) ∧
    (∑ n ∈ Ico 23232 23296, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (17243271837240528996794224392 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_23168_23296 :
    (∑ n ∈ Ico 23168 23296, mobiusTreeValue 16 mobiusTable1200001 n) = (10 : ℤ) ∧
    (∑ n ∈ Ico 23168 23296, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (80 : ℕ) ∧
    (∑ n ∈ Ico 23168 23296, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (2155319 : ℤ) ∧
    (∑ n ∈ Ico 23168 23296, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (43106483492029784201880123369 : ℤ) := by
  rcases cdemPrefixStats_23168_23232 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_23232_23296 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 23168 ≤ 23232) (by norm_num : 23232 ≤ 23296), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 23168 ≤ 23232) (by norm_num : 23232 ≤ 23296), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 23168 ≤ 23232) (by norm_num : 23232 ≤ 23296), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 23168 ≤ 23232) (by norm_num : 23232 ≤ 23296), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_23040_23296 :
    (∑ n ∈ Ico 23040 23296, mobiusTreeValue 16 mobiusTable1200001 n) = (-2 : ℤ) ∧
    (∑ n ∈ Ico 23040 23296, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (158 : ℕ) ∧
    (∑ n ∈ Ico 23040 23296, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-440410 : ℤ) ∧
    (∑ n ∈ Ico 23040 23296, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-8808109531341650423379505165 : ℤ) := by
  rcases cdemPrefixStats_23040_23168 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_23168_23296 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 23040 ≤ 23168) (by norm_num : 23168 ≤ 23296), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 23040 ≤ 23168) (by norm_num : 23168 ≤ 23296), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 23040 ≤ 23168) (by norm_num : 23168 ≤ 23296), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 23040 ≤ 23168) (by norm_num : 23168 ≤ 23296), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_23296_23360 :
    (∑ n ∈ Ico 23296 23360, mobiusTreeValue 16 mobiusTable1200001 n) = (-8 : ℤ) ∧
    (∑ n ∈ Ico 23296 23360, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 23296 23360, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-1715114 : ℤ) ∧
    (∑ n ∈ Ico 23296 23360, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-34302383480571631552278054482 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_23360_23424 :
    (∑ n ∈ Ico 23360 23424, mobiusTreeValue 16 mobiusTable1200001 n) = (7 : ℤ) ∧
    (∑ n ∈ Ico 23360 23424, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 23360 23424, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (1496235 : ℤ) ∧
    (∑ n ∈ Ico 23360 23424, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (29924776616990148732902940895 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_23296_23424 :
    (∑ n ∈ Ico 23296 23424, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 23296 23424, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (79 : ℕ) ∧
    (∑ n ∈ Ico 23296 23424, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-218879 : ℤ) ∧
    (∑ n ∈ Ico 23296 23424, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-4377606863581482819375113587 : ℤ) := by
  rcases cdemPrefixStats_23296_23360 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_23360_23424 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 23296 ≤ 23360) (by norm_num : 23360 ≤ 23424), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 23296 ≤ 23360) (by norm_num : 23360 ≤ 23424), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 23296 ≤ 23360) (by norm_num : 23360 ≤ 23424), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 23296 ≤ 23360) (by norm_num : 23360 ≤ 23424), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_23424_23488 :
    (∑ n ∈ Ico 23424 23488, mobiusTreeValue 16 mobiusTable1200001 n) = (3 : ℤ) ∧
    (∑ n ∈ Ico 23424 23488, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 23424 23488, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (638477 : ℤ) ∧
    (∑ n ∈ Ico 23424 23488, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (12769570846800884216555023469 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_23488_23552 :
    (∑ n ∈ Ico 23488 23552, mobiusTreeValue 16 mobiusTable1200001 n) = (-5 : ℤ) ∧
    (∑ n ∈ Ico 23488 23552, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 23488 23552, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-1063009 : ℤ) ∧
    (∑ n ∈ Ico 23488 23552, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-21260161044429267814180618016 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_23424_23552 :
    (∑ n ∈ Ico 23424 23552, mobiusTreeValue 16 mobiusTable1200001 n) = (-2 : ℤ) ∧
    (∑ n ∈ Ico 23424 23552, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (76 : ℕ) ∧
    (∑ n ∈ Ico 23424 23552, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-424532 : ℤ) ∧
    (∑ n ∈ Ico 23424 23552, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-8490590197628383597625594547 : ℤ) := by
  rcases cdemPrefixStats_23424_23488 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_23488_23552 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 23424 ≤ 23488) (by norm_num : 23488 ≤ 23552), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 23424 ≤ 23488) (by norm_num : 23488 ≤ 23552), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 23424 ≤ 23488) (by norm_num : 23488 ≤ 23552), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 23424 ≤ 23488) (by norm_num : 23488 ≤ 23552), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_23296_23552 :
    (∑ n ∈ Ico 23296 23552, mobiusTreeValue 16 mobiusTable1200001 n) = (-3 : ℤ) ∧
    (∑ n ∈ Ico 23296 23552, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (155 : ℕ) ∧
    (∑ n ∈ Ico 23296 23552, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-643411 : ℤ) ∧
    (∑ n ∈ Ico 23296 23552, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-12868197061209866417000708134 : ℤ) := by
  rcases cdemPrefixStats_23296_23424 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_23424_23552 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 23296 ≤ 23424) (by norm_num : 23424 ≤ 23552), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 23296 ≤ 23424) (by norm_num : 23424 ≤ 23552), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 23296 ≤ 23424) (by norm_num : 23424 ≤ 23552), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 23296 ≤ 23424) (by norm_num : 23424 ≤ 23552), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_23040_23552 :
    (∑ n ∈ Ico 23040 23552, mobiusTreeValue 16 mobiusTable1200001 n) = (-5 : ℤ) ∧
    (∑ n ∈ Ico 23040 23552, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (313 : ℕ) ∧
    (∑ n ∈ Ico 23040 23552, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-1083821 : ℤ) ∧
    (∑ n ∈ Ico 23040 23552, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-21676306592551516840380213299 : ℤ) := by
  rcases cdemPrefixStats_23040_23296 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_23296_23552 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 23040 ≤ 23296) (by norm_num : 23296 ≤ 23552), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 23040 ≤ 23296) (by norm_num : 23296 ≤ 23552), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 23040 ≤ 23296) (by norm_num : 23296 ≤ 23552), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 23040 ≤ 23296) (by norm_num : 23296 ≤ 23552), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_22528_23552 :
    (∑ n ∈ Ico 22528 23552, mobiusTreeValue 16 mobiusTable1200001 n) = (-10 : ℤ) ∧
    (∑ n ∈ Ico 22528 23552, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (626 : ℕ) ∧
    (∑ n ∈ Ico 22528 23552, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-2166994 : ℤ) ∧
    (∑ n ∈ Ico 22528 23552, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-43339730022672730686082825586 : ℤ) := by
  rcases cdemPrefixStats_22528_23040 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_23040_23552 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 22528 ≤ 23040) (by norm_num : 23040 ≤ 23552), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 22528 ≤ 23040) (by norm_num : 23040 ≤ 23552), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 22528 ≤ 23040) (by norm_num : 23040 ≤ 23552), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 22528 ≤ 23040) (by norm_num : 23040 ≤ 23552), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_23552_23616 :
    (∑ n ∈ Ico 23552 23616, mobiusTreeValue 16 mobiusTable1200001 n) = (-3 : ℤ) ∧
    (∑ n ∈ Ico 23552 23616, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 23552 23616, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-637581 : ℤ) ∧
    (∑ n ∈ Ico 23552 23616, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-12751577365867940286351779707 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_23616_23680 :
    (∑ n ∈ Ico 23616 23680, mobiusTreeValue 16 mobiusTable1200001 n) = (4 : ℤ) ∧
    (∑ n ∈ Ico 23616 23680, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 23616 23680, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (845343 : ℤ) ∧
    (∑ n ∈ Ico 23616 23680, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (16906874375709458719848060214 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_23552_23680 :
    (∑ n ∈ Ico 23552 23680, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 23552 23680, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 23552 23680, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (207762 : ℤ) ∧
    (∑ n ∈ Ico 23552 23680, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (4155297009841518433496280507 : ℤ) := by
  rcases cdemPrefixStats_23552_23616 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_23616_23680 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 23552 ≤ 23616) (by norm_num : 23616 ≤ 23680), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 23552 ≤ 23616) (by norm_num : 23616 ≤ 23680), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 23552 ≤ 23616) (by norm_num : 23616 ≤ 23680), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 23552 ≤ 23616) (by norm_num : 23616 ≤ 23680), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_23680_23744 :
    (∑ n ∈ Ico 23680 23744, mobiusTreeValue 16 mobiusTable1200001 n) = (-3 : ℤ) ∧
    (∑ n ∈ Ico 23680 23744, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 23680 23744, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-633712 : ℤ) ∧
    (∑ n ∈ Ico 23680 23744, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-12674265193539984545625480025 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_23744_23808 :
    (∑ n ∈ Ico 23744 23808, mobiusTreeValue 16 mobiusTable1200001 n) = (-2 : ℤ) ∧
    (∑ n ∈ Ico 23744 23808, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 23744 23808, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-421732 : ℤ) ∧
    (∑ n ∈ Ico 23744 23808, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-8434681021238993866350955298 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_23680_23808 :
    (∑ n ∈ Ico 23680 23808, mobiusTreeValue 16 mobiusTable1200001 n) = (-5 : ℤ) ∧
    (∑ n ∈ Ico 23680 23808, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (79 : ℕ) ∧
    (∑ n ∈ Ico 23680 23808, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-1055444 : ℤ) ∧
    (∑ n ∈ Ico 23680 23808, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-21108946214778978411976435323 : ℤ) := by
  rcases cdemPrefixStats_23680_23744 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_23744_23808 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 23680 ≤ 23744) (by norm_num : 23744 ≤ 23808), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 23680 ≤ 23744) (by norm_num : 23744 ≤ 23808), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 23680 ≤ 23744) (by norm_num : 23744 ≤ 23808), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 23680 ≤ 23744) (by norm_num : 23744 ≤ 23808), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_23552_23808 :
    (∑ n ∈ Ico 23552 23808, mobiusTreeValue 16 mobiusTable1200001 n) = (-4 : ℤ) ∧
    (∑ n ∈ Ico 23552 23808, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (156 : ℕ) ∧
    (∑ n ∈ Ico 23552 23808, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-847682 : ℤ) ∧
    (∑ n ∈ Ico 23552 23808, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-16953649204937459978480154816 : ℤ) := by
  rcases cdemPrefixStats_23552_23680 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_23680_23808 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 23552 ≤ 23680) (by norm_num : 23680 ≤ 23808), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 23552 ≤ 23680) (by norm_num : 23680 ≤ 23808), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 23552 ≤ 23680) (by norm_num : 23680 ≤ 23808), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 23552 ≤ 23680) (by norm_num : 23680 ≤ 23808), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_23808_23872 :
    (∑ n ∈ Ico 23808 23872, mobiusTreeValue 16 mobiusTable1200001 n) = (-2 : ℤ) ∧
    (∑ n ∈ Ico 23808 23872, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 23808 23872, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-420668 : ℤ) ∧
    (∑ n ∈ Ico 23808 23872, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-8413383149846178401131220567 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_23872_23936 :
    (∑ n ∈ Ico 23872 23936, mobiusTreeValue 16 mobiusTable1200001 n) = (-6 : ℤ) ∧
    (∑ n ∈ Ico 23872 23936, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 23872 23936, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-1255246 : ℤ) ∧
    (∑ n ∈ Ico 23872 23936, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-25104968453661715846272850061 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_23808_23936 :
    (∑ n ∈ Ico 23808 23936, mobiusTreeValue 16 mobiusTable1200001 n) = (-8 : ℤ) ∧
    (∑ n ∈ Ico 23808 23936, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 23808 23936, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-1675914 : ℤ) ∧
    (∑ n ∈ Ico 23808 23936, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-33518351603507894247404070628 : ℤ) := by
  rcases cdemPrefixStats_23808_23872 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_23872_23936 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 23808 ≤ 23872) (by norm_num : 23872 ≤ 23936), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 23808 ≤ 23872) (by norm_num : 23872 ≤ 23936), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 23808 ≤ 23872) (by norm_num : 23872 ≤ 23936), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 23808 ≤ 23872) (by norm_num : 23872 ≤ 23936), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_23936_24000 :
    (∑ n ∈ Ico 23936 24000, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 23936 24000, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 23936 24000, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (1568 : ℤ) ∧
    (∑ n ∈ Ico 23936 24000, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (31342053754655922679230907 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_24000_24064 :
    (∑ n ∈ Ico 24000 24064, mobiusTreeValue 16 mobiusTable1200001 n) = (-8 : ℤ) ∧
    (∑ n ∈ Ico 24000 24064, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 24000 24064, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-1665007 : ℤ) ∧
    (∑ n ∈ Ico 24000 24064, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-33300247768173507243959940872 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_23936_24064 :
    (∑ n ∈ Ico 23936 24064, mobiusTreeValue 16 mobiusTable1200001 n) = (-8 : ℤ) ∧
    (∑ n ∈ Ico 23936 24064, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (76 : ℕ) ∧
    (∑ n ∈ Ico 23936 24064, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-1663439 : ℤ) ∧
    (∑ n ∈ Ico 23936 24064, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-33268905714418851321280709965 : ℤ) := by
  rcases cdemPrefixStats_23936_24000 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_24000_24064 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 23936 ≤ 24000) (by norm_num : 24000 ≤ 24064), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 23936 ≤ 24000) (by norm_num : 24000 ≤ 24064), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 23936 ≤ 24000) (by norm_num : 24000 ≤ 24064), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 23936 ≤ 24000) (by norm_num : 24000 ≤ 24064), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_23808_24064 :
    (∑ n ∈ Ico 23808 24064, mobiusTreeValue 16 mobiusTable1200001 n) = (-16 : ℤ) ∧
    (∑ n ∈ Ico 23808 24064, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (154 : ℕ) ∧
    (∑ n ∈ Ico 23808 24064, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-3339353 : ℤ) ∧
    (∑ n ∈ Ico 23808 24064, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-66787257317926745568684780593 : ℤ) := by
  rcases cdemPrefixStats_23808_23936 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_23936_24064 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 23808 ≤ 23936) (by norm_num : 23936 ≤ 24064), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 23808 ≤ 23936) (by norm_num : 23936 ≤ 24064), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 23808 ≤ 23936) (by norm_num : 23936 ≤ 24064), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 23808 ≤ 23936) (by norm_num : 23936 ≤ 24064), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_23552_24064 :
    (∑ n ∈ Ico 23552 24064, mobiusTreeValue 16 mobiusTable1200001 n) = (-20 : ℤ) ∧
    (∑ n ∈ Ico 23552 24064, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (310 : ℕ) ∧
    (∑ n ∈ Ico 23552 24064, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-4187035 : ℤ) ∧
    (∑ n ∈ Ico 23552 24064, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-83740906522864205547164935409 : ℤ) := by
  rcases cdemPrefixStats_23552_23808 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_23808_24064 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 23552 ≤ 23808) (by norm_num : 23808 ≤ 24064), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 23552 ≤ 23808) (by norm_num : 23808 ≤ 24064), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 23552 ≤ 23808) (by norm_num : 23808 ≤ 24064), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 23552 ≤ 23808) (by norm_num : 23808 ≤ 24064), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_24064_24128 :
    (∑ n ∈ Ico 24064 24128, mobiusTreeValue 16 mobiusTable1200001 n) = (-13 : ℤ) ∧
    (∑ n ∈ Ico 24064 24128, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 24064 24128, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-2696859 : ℤ) ∧
    (∑ n ∈ Ico 24064 24128, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-53937261574955284915332514128 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_24128_24192 :
    (∑ n ∈ Ico 24128 24192, mobiusTreeValue 16 mobiusTable1200001 n) = (-5 : ℤ) ∧
    (∑ n ∈ Ico 24128 24192, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 24128 24192, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-1034938 : ℤ) ∧
    (∑ n ∈ Ico 24128 24192, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-20698791934097333199796084826 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_24064_24192 :
    (∑ n ∈ Ico 24064 24192, mobiusTreeValue 16 mobiusTable1200001 n) = (-18 : ℤ) ∧
    (∑ n ∈ Ico 24064 24192, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 24064 24192, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-3731797 : ℤ) ∧
    (∑ n ∈ Ico 24064 24192, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-74636053509052618115128598954 : ℤ) := by
  rcases cdemPrefixStats_24064_24128 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_24128_24192 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 24064 ≤ 24128) (by norm_num : 24128 ≤ 24192), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 24064 ≤ 24128) (by norm_num : 24128 ≤ 24192), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 24064 ≤ 24128) (by norm_num : 24128 ≤ 24192), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 24064 ≤ 24128) (by norm_num : 24128 ≤ 24192), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_24192_24256 :
    (∑ n ∈ Ico 24192 24256, mobiusTreeValue 16 mobiusTable1200001 n) = (3 : ℤ) ∧
    (∑ n ∈ Ico 24192 24256, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 24192 24256, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (620181 : ℤ) ∧
    (∑ n ∈ Ico 24192 24256, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (12403670072497354004778715379 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_24256_24320 :
    (∑ n ∈ Ico 24256 24320, mobiusTreeValue 16 mobiusTable1200001 n) = (11 : ℤ) ∧
    (∑ n ∈ Ico 24256 24320, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 24256 24320, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (2265448 : ℤ) ∧
    (∑ n ∈ Ico 24256 24320, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (45309038504640936932809000411 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_24192_24320 :
    (∑ n ∈ Ico 24192 24320, mobiusTreeValue 16 mobiusTable1200001 n) = (14 : ℤ) ∧
    (∑ n ∈ Ico 24192 24320, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (80 : ℕ) ∧
    (∑ n ∈ Ico 24192 24320, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (2885629 : ℤ) ∧
    (∑ n ∈ Ico 24192 24320, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (57712708577138290937587715790 : ℤ) := by
  rcases cdemPrefixStats_24192_24256 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_24256_24320 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 24192 ≤ 24256) (by norm_num : 24256 ≤ 24320), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 24192 ≤ 24256) (by norm_num : 24256 ≤ 24320), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 24192 ≤ 24256) (by norm_num : 24256 ≤ 24320), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 24192 ≤ 24256) (by norm_num : 24256 ≤ 24320), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_24064_24320 :
    (∑ n ∈ Ico 24064 24320, mobiusTreeValue 16 mobiusTable1200001 n) = (-4 : ℤ) ∧
    (∑ n ∈ Ico 24064 24320, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (158 : ℕ) ∧
    (∑ n ∈ Ico 24064 24320, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-846168 : ℤ) ∧
    (∑ n ∈ Ico 24064 24320, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-16923344931914327177540883164 : ℤ) := by
  rcases cdemPrefixStats_24064_24192 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_24192_24320 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 24064 ≤ 24192) (by norm_num : 24192 ≤ 24320), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 24064 ≤ 24192) (by norm_num : 24192 ≤ 24320), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 24064 ≤ 24192) (by norm_num : 24192 ≤ 24320), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 24064 ≤ 24192) (by norm_num : 24192 ≤ 24320), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_24320_24384 :
    (∑ n ∈ Ico 24320 24384, mobiusTreeValue 16 mobiusTable1200001 n) = (4 : ℤ) ∧
    (∑ n ∈ Ico 24320 24384, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (36 : ℕ) ∧
    (∑ n ∈ Ico 24320 24384, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (822710 : ℤ) ∧
    (∑ n ∈ Ico 24320 24384, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (16454267832430278654356625383 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_24384_24448 :
    (∑ n ∈ Ico 24384 24448, mobiusTreeValue 16 mobiusTable1200001 n) = (-7 : ℤ) ∧
    (∑ n ∈ Ico 24384 24448, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 24384 24448, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-1433407 : ℤ) ∧
    (∑ n ∈ Ico 24384 24448, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-28668230203896207950462814908 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_24320_24448 :
    (∑ n ∈ Ico 24320 24448, mobiusTreeValue 16 mobiusTable1200001 n) = (-3 : ℤ) ∧
    (∑ n ∈ Ico 24320 24448, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (75 : ℕ) ∧
    (∑ n ∈ Ico 24320 24448, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-610697 : ℤ) ∧
    (∑ n ∈ Ico 24320 24448, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-12213962371465929296106189525 : ℤ) := by
  rcases cdemPrefixStats_24320_24384 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_24384_24448 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 24320 ≤ 24384) (by norm_num : 24384 ≤ 24448), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 24320 ≤ 24384) (by norm_num : 24384 ≤ 24448), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 24320 ≤ 24384) (by norm_num : 24384 ≤ 24448), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 24320 ≤ 24384) (by norm_num : 24384 ≤ 24448), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_24448_24512 :
    (∑ n ∈ Ico 24448 24512, mobiusTreeValue 16 mobiusTable1200001 n) = (2 : ℤ) ∧
    (∑ n ∈ Ico 24448 24512, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 24448 24512, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (408187 : ℤ) ∧
    (∑ n ∈ Ico 24448 24512, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (8163775950460214018660997503 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_24512_24576 :
    (∑ n ∈ Ico 24512 24576, mobiusTreeValue 16 mobiusTable1200001 n) = (4 : ℤ) ∧
    (∑ n ∈ Ico 24512 24576, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 24512 24576, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (816016 : ℤ) ∧
    (∑ n ∈ Ico 24512 24576, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (16320351607040742060084418761 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_24448_24576 :
    (∑ n ∈ Ico 24448 24576, mobiusTreeValue 16 mobiusTable1200001 n) = (6 : ℤ) ∧
    (∑ n ∈ Ico 24448 24576, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (76 : ℕ) ∧
    (∑ n ∈ Ico 24448 24576, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (1224203 : ℤ) ∧
    (∑ n ∈ Ico 24448 24576, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (24484127557500956078745416264 : ℤ) := by
  rcases cdemPrefixStats_24448_24512 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_24512_24576 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 24448 ≤ 24512) (by norm_num : 24512 ≤ 24576), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 24448 ≤ 24512) (by norm_num : 24512 ≤ 24576), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 24448 ≤ 24512) (by norm_num : 24512 ≤ 24576), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 24448 ≤ 24512) (by norm_num : 24512 ≤ 24576), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_24320_24576 :
    (∑ n ∈ Ico 24320 24576, mobiusTreeValue 16 mobiusTable1200001 n) = (3 : ℤ) ∧
    (∑ n ∈ Ico 24320 24576, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (151 : ℕ) ∧
    (∑ n ∈ Ico 24320 24576, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (613506 : ℤ) ∧
    (∑ n ∈ Ico 24320 24576, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (12270165186035026782639226739 : ℤ) := by
  rcases cdemPrefixStats_24320_24448 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_24448_24576 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 24320 ≤ 24448) (by norm_num : 24448 ≤ 24576), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 24320 ≤ 24448) (by norm_num : 24448 ≤ 24576), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 24320 ≤ 24448) (by norm_num : 24448 ≤ 24576), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 24320 ≤ 24448) (by norm_num : 24448 ≤ 24576), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_24064_24576 :
    (∑ n ∈ Ico 24064 24576, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 24064 24576, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (309 : ℕ) ∧
    (∑ n ∈ Ico 24064 24576, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-232662 : ℤ) ∧
    (∑ n ∈ Ico 24064 24576, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-4653179745879300394901656425 : ℤ) := by
  rcases cdemPrefixStats_24064_24320 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_24320_24576 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 24064 ≤ 24320) (by norm_num : 24320 ≤ 24576), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 24064 ≤ 24320) (by norm_num : 24320 ≤ 24576), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 24064 ≤ 24320) (by norm_num : 24320 ≤ 24576), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 24064 ≤ 24320) (by norm_num : 24320 ≤ 24576), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_23552_24576 :
    (∑ n ∈ Ico 23552 24576, mobiusTreeValue 16 mobiusTable1200001 n) = (-21 : ℤ) ∧
    (∑ n ∈ Ico 23552 24576, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (619 : ℕ) ∧
    (∑ n ∈ Ico 23552 24576, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-4419697 : ℤ) ∧
    (∑ n ∈ Ico 23552 24576, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-88394086268743505942066591834 : ℤ) := by
  rcases cdemPrefixStats_23552_24064 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_24064_24576 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 23552 ≤ 24064) (by norm_num : 24064 ≤ 24576), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 23552 ≤ 24064) (by norm_num : 24064 ≤ 24576), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 23552 ≤ 24064) (by norm_num : 24064 ≤ 24576), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 23552 ≤ 24064) (by norm_num : 24064 ≤ 24576), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_22528_24576 :
    (∑ n ∈ Ico 22528 24576, mobiusTreeValue 16 mobiusTable1200001 n) = (-31 : ℤ) ∧
    (∑ n ∈ Ico 22528 24576, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (1245 : ℕ) ∧
    (∑ n ∈ Ico 22528 24576, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-6586691 : ℤ) ∧
    (∑ n ∈ Ico 22528 24576, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-131733816291416236628149417420 : ℤ) := by
  rcases cdemPrefixStats_22528_23552 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_23552_24576 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 22528 ≤ 23552) (by norm_num : 23552 ≤ 24576), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 22528 ≤ 23552) (by norm_num : 23552 ≤ 24576), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 22528 ≤ 23552) (by norm_num : 23552 ≤ 24576), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 22528 ≤ 23552) (by norm_num : 23552 ≤ 24576), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_20480_24576 :
    (∑ n ∈ Ico 20480 24576, mobiusTreeValue 16 mobiusTable1200001 n) = (-76 : ℤ) ∧
    (∑ n ∈ Ico 20480 24576, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (2486 : ℕ) ∧
    (∑ n ∈ Ico 20480 24576, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-16761374 : ℤ) ∧
    (∑ n ∈ Ico 20480 24576, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-335227952525261311123324208851 : ℤ) := by
  rcases cdemPrefixStats_20480_22528 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_22528_24576 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 20480 ≤ 22528) (by norm_num : 22528 ≤ 24576), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 20480 ≤ 22528) (by norm_num : 22528 ≤ 24576), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 20480 ≤ 22528) (by norm_num : 22528 ≤ 24576), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 20480 ≤ 22528) (by norm_num : 22528 ≤ 24576), hR1, hR2] <;> norm_num

theorem cdemPrefixGroup005_checked_complete :
    (∑ n ∈ Ico 20480 24576, mobiusTreeValue 16 mobiusTable1200001 n) = (-76 : ℤ) ∧
    (∑ n ∈ Ico 20480 24576, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (2486 : ℕ) ∧
    (∑ n ∈ Ico 20480 24576, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-16761374 : ℤ) ∧
    (∑ n ∈ Ico 20480 24576, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-335227952525261311123324208851 : ℤ) := cdemPrefixStats_20480_24576
end Helfgott
#print axioms Helfgott.cdemPrefixGroup005_checked_complete

open Helfgott Finset
open scoped BigOperators

theorem solution :
    (∑ n ∈ Ico 20480 24576, mobiusTreeValue 16 mobiusTable1200001 n) = (-76 : ℤ) ∧
    (∑ n ∈ Ico 20480 24576, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (2486 : ℕ) ∧
    (∑ n ∈ Ico 20480 24576, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-16761374 : ℤ) ∧
    (∑ n ∈ Ico 20480 24576, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-335227952525261311123324208851 : ℤ) := Helfgott.cdemPrefixGroup005_checked_complete
#print axioms solution
