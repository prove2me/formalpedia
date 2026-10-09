-- Prove2me | solution 1 for Helfgott.cdemPrefixGroup004_checked
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-09T01:22:44.204988+00:00
-- url     : https://prove2.me/submissions/002ab952-4f3d-42ef-a5fe-b82983c3d358

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
private theorem cdemPrefixStats_16384_16448 :
    (∑ n ∈ Ico 16384 16448, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 16384 16448, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 16384 16448, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (303337 : ℤ) ∧
    (∑ n ∈ Ico 16384 16448, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (6066782661386886495580793017 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_16448_16512 :
    (∑ n ∈ Ico 16448 16512, mobiusTreeValue 16 mobiusTable1200001 n) = (8 : ℤ) ∧
    (∑ n ∈ Ico 16448 16512, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 16448 16512, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (2425546 : ℤ) ∧
    (∑ n ∈ Ico 16448 16512, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (48510978066578765078642576777 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_16384_16512 :
    (∑ n ∈ Ico 16384 16512, mobiusTreeValue 16 mobiusTable1200001 n) = (9 : ℤ) ∧
    (∑ n ∈ Ico 16384 16512, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (79 : ℕ) ∧
    (∑ n ∈ Ico 16384 16512, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (2728883 : ℤ) ∧
    (∑ n ∈ Ico 16384 16512, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (54577760727965651574223369794 : ℤ) := by
  rcases cdemPrefixStats_16384_16448 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_16448_16512 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 16384 ≤ 16448) (by norm_num : 16448 ≤ 16512), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 16384 ≤ 16448) (by norm_num : 16448 ≤ 16512), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 16384 ≤ 16448) (by norm_num : 16448 ≤ 16512), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 16384 ≤ 16448) (by norm_num : 16448 ≤ 16512), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_16512_16576 :
    (∑ n ∈ Ico 16512 16576, mobiusTreeValue 16 mobiusTable1200001 n) = (-2 : ℤ) ∧
    (∑ n ∈ Ico 16512 16576, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 16512 16576, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-606770 : ℤ) ∧
    (∑ n ∈ Ico 16512 16576, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-12135401177992721235807054412 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_16576_16640 :
    (∑ n ∈ Ico 16576 16640, mobiusTreeValue 16 mobiusTable1200001 n) = (7 : ℤ) ∧
    (∑ n ∈ Ico 16576 16640, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 16576 16640, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (2108432 : ℤ) ∧
    (∑ n ∈ Ico 16576 16640, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (42168748232485705953137053074 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_16512_16640 :
    (∑ n ∈ Ico 16512 16640, mobiusTreeValue 16 mobiusTable1200001 n) = (5 : ℤ) ∧
    (∑ n ∈ Ico 16512 16640, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 16512 16640, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (1501662 : ℤ) ∧
    (∑ n ∈ Ico 16512 16640, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (30033347054492984717329998662 : ℤ) := by
  rcases cdemPrefixStats_16512_16576 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_16576_16640 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 16512 ≤ 16576) (by norm_num : 16576 ≤ 16640), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 16512 ≤ 16576) (by norm_num : 16576 ≤ 16640), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 16512 ≤ 16576) (by norm_num : 16576 ≤ 16640), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 16512 ≤ 16576) (by norm_num : 16576 ≤ 16640), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_16384_16640 :
    (∑ n ∈ Ico 16384 16640, mobiusTreeValue 16 mobiusTable1200001 n) = (14 : ℤ) ∧
    (∑ n ∈ Ico 16384 16640, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (156 : ℕ) ∧
    (∑ n ∈ Ico 16384 16640, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (4230545 : ℤ) ∧
    (∑ n ∈ Ico 16384 16640, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (84611107782458636291553368456 : ℤ) := by
  rcases cdemPrefixStats_16384_16512 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_16512_16640 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 16384 ≤ 16512) (by norm_num : 16512 ≤ 16640), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 16384 ≤ 16512) (by norm_num : 16512 ≤ 16640), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 16384 ≤ 16512) (by norm_num : 16512 ≤ 16640), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 16384 ≤ 16512) (by norm_num : 16512 ≤ 16640), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_16640_16704 :
    (∑ n ∈ Ico 16640 16704, mobiusTreeValue 16 mobiusTable1200001 n) = (-10 : ℤ) ∧
    (∑ n ∈ Ico 16640 16704, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 16640 16704, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-2996686 : ℤ) ∧
    (∑ n ∈ Ico 16640 16704, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-59933813784022759554281303185 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_16704_16768 :
    (∑ n ∈ Ico 16704 16768, mobiusTreeValue 16 mobiusTable1200001 n) = (4 : ℤ) ∧
    (∑ n ∈ Ico 16704 16768, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 16704 16768, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (1199598 : ℤ) ∧
    (∑ n ∈ Ico 16704 16768, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (23991970173107464674477035864 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_16640_16768 :
    (∑ n ∈ Ico 16640 16768, mobiusTreeValue 16 mobiusTable1200001 n) = (-6 : ℤ) ∧
    (∑ n ∈ Ico 16640 16768, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 16640 16768, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-1797088 : ℤ) ∧
    (∑ n ∈ Ico 16640 16768, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-35941843610915294879804267321 : ℤ) := by
  rcases cdemPrefixStats_16640_16704 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_16704_16768 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 16640 ≤ 16704) (by norm_num : 16704 ≤ 16768), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 16640 ≤ 16704) (by norm_num : 16704 ≤ 16768), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 16640 ≤ 16704) (by norm_num : 16704 ≤ 16768), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 16640 ≤ 16704) (by norm_num : 16704 ≤ 16768), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_16768_16832 :
    (∑ n ∈ Ico 16768 16832, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 16768 16832, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 16768 16832, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (6752 : ℤ) ∧
    (∑ n ∈ Ico 16768 16832, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (134985556188251556768896835 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_16832_16896 :
    (∑ n ∈ Ico 16832 16896, mobiusTreeValue 16 mobiusTable1200001 n) = (9 : ℤ) ∧
    (∑ n ∈ Ico 16832 16896, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 16832 16896, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (2670760 : ℤ) ∧
    (∑ n ∈ Ico 16832 16896, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (53415223241132461536629256057 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_16768_16896 :
    (∑ n ∈ Ico 16768 16896, mobiusTreeValue 16 mobiusTable1200001 n) = (9 : ℤ) ∧
    (∑ n ∈ Ico 16768 16896, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (79 : ℕ) ∧
    (∑ n ∈ Ico 16768 16896, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (2677512 : ℤ) ∧
    (∑ n ∈ Ico 16768 16896, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (53550208797320713093398152892 : ℤ) := by
  rcases cdemPrefixStats_16768_16832 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_16832_16896 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 16768 ≤ 16832) (by norm_num : 16832 ≤ 16896), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 16768 ≤ 16832) (by norm_num : 16832 ≤ 16896), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 16768 ≤ 16832) (by norm_num : 16832 ≤ 16896), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 16768 ≤ 16832) (by norm_num : 16832 ≤ 16896), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_16640_16896 :
    (∑ n ∈ Ico 16640 16896, mobiusTreeValue 16 mobiusTable1200001 n) = (3 : ℤ) ∧
    (∑ n ∈ Ico 16640 16896, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (157 : ℕ) ∧
    (∑ n ∈ Ico 16640 16896, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (880424 : ℤ) ∧
    (∑ n ∈ Ico 16640 16896, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (17608365186405418213593885571 : ℤ) := by
  rcases cdemPrefixStats_16640_16768 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_16768_16896 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 16640 ≤ 16768) (by norm_num : 16768 ≤ 16896), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 16640 ≤ 16768) (by norm_num : 16768 ≤ 16896), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 16640 ≤ 16768) (by norm_num : 16768 ≤ 16896), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 16640 ≤ 16768) (by norm_num : 16768 ≤ 16896), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_16384_16896 :
    (∑ n ∈ Ico 16384 16896, mobiusTreeValue 16 mobiusTable1200001 n) = (17 : ℤ) ∧
    (∑ n ∈ Ico 16384 16896, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (313 : ℕ) ∧
    (∑ n ∈ Ico 16384 16896, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (5110969 : ℤ) ∧
    (∑ n ∈ Ico 16384 16896, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (102219472968864054505147254027 : ℤ) := by
  rcases cdemPrefixStats_16384_16640 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_16640_16896 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 16384 ≤ 16640) (by norm_num : 16640 ≤ 16896), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 16384 ≤ 16640) (by norm_num : 16640 ≤ 16896), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 16384 ≤ 16640) (by norm_num : 16640 ≤ 16896), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 16384 ≤ 16640) (by norm_num : 16640 ≤ 16896), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_16896_16960 :
    (∑ n ∈ Ico 16896 16960, mobiusTreeValue 16 mobiusTable1200001 n) = (-3 : ℤ) ∧
    (∑ n ∈ Ico 16896 16960, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 16896 16960, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-887517 : ℤ) ∧
    (∑ n ∈ Ico 16896 16960, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-17750357813641919856512448727 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_16960_17024 :
    (∑ n ∈ Ico 16960 17024, mobiusTreeValue 16 mobiusTable1200001 n) = (-7 : ℤ) ∧
    (∑ n ∈ Ico 16960 17024, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 16960 17024, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-2058110 : ℤ) ∧
    (∑ n ∈ Ico 16960 17024, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-41162293247811779856124514169 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_16896_17024 :
    (∑ n ∈ Ico 16896 17024, mobiusTreeValue 16 mobiusTable1200001 n) = (-10 : ℤ) ∧
    (∑ n ∈ Ico 16896 17024, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 16896 17024, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-2945627 : ℤ) ∧
    (∑ n ∈ Ico 16896 17024, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-58912651061453699712636962896 : ℤ) := by
  rcases cdemPrefixStats_16896_16960 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_16960_17024 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 16896 ≤ 16960) (by norm_num : 16960 ≤ 17024), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 16896 ≤ 16960) (by norm_num : 16960 ≤ 17024), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 16896 ≤ 16960) (by norm_num : 16960 ≤ 17024), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 16896 ≤ 16960) (by norm_num : 16960 ≤ 17024), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_17024_17088 :
    (∑ n ∈ Ico 17024 17088, mobiusTreeValue 16 mobiusTable1200001 n) = (11 : ℤ) ∧
    (∑ n ∈ Ico 17024 17088, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 17024 17088, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (3221166 : ℤ) ∧
    (∑ n ∈ Ico 17024 17088, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (64423391783434575700952980453 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_17088_17152 :
    (∑ n ∈ Ico 17088 17152, mobiusTreeValue 16 mobiusTable1200001 n) = (-6 : ℤ) ∧
    (∑ n ∈ Ico 17088 17152, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 17088 17152, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-1756601 : ℤ) ∧
    (∑ n ∈ Ico 17088 17152, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-35132054966548156959536004033 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_17024_17152 :
    (∑ n ∈ Ico 17024 17152, mobiusTreeValue 16 mobiusTable1200001 n) = (5 : ℤ) ∧
    (∑ n ∈ Ico 17024 17152, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 17024 17152, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (1464565 : ℤ) ∧
    (∑ n ∈ Ico 17024 17152, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (29291336816886418741416976420 : ℤ) := by
  rcases cdemPrefixStats_17024_17088 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_17088_17152 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 17024 ≤ 17088) (by norm_num : 17088 ≤ 17152), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 17024 ≤ 17088) (by norm_num : 17088 ≤ 17152), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 17024 ≤ 17088) (by norm_num : 17088 ≤ 17152), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 17024 ≤ 17088) (by norm_num : 17088 ≤ 17152), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_16896_17152 :
    (∑ n ∈ Ico 16896 17152, mobiusTreeValue 16 mobiusTable1200001 n) = (-5 : ℤ) ∧
    (∑ n ∈ Ico 16896 17152, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (155 : ℕ) ∧
    (∑ n ∈ Ico 16896 17152, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-1481062 : ℤ) ∧
    (∑ n ∈ Ico 16896 17152, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-29621314244567280971219986476 : ℤ) := by
  rcases cdemPrefixStats_16896_17024 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_17024_17152 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 16896 ≤ 17024) (by norm_num : 17024 ≤ 17152), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 16896 ≤ 17024) (by norm_num : 17024 ≤ 17152), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 16896 ≤ 17024) (by norm_num : 17024 ≤ 17152), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 16896 ≤ 17024) (by norm_num : 17024 ≤ 17152), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_17152_17216 :
    (∑ n ∈ Ico 17152 17216, mobiusTreeValue 16 mobiusTable1200001 n) = (-4 : ℤ) ∧
    (∑ n ∈ Ico 17152 17216, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 17152 17216, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-1163990 : ℤ) ∧
    (∑ n ∈ Ico 17152 17216, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-23279842403506063565472108248 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_17216_17280 :
    (∑ n ∈ Ico 17216 17280, mobiusTreeValue 16 mobiusTable1200001 n) = (8 : ℤ) ∧
    (∑ n ∈ Ico 17216 17280, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 17216 17280, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (2319375 : ℤ) ∧
    (∑ n ∈ Ico 17216 17280, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (46387606123789032512064035688 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_17152_17280 :
    (∑ n ∈ Ico 17152 17280, mobiusTreeValue 16 mobiusTable1200001 n) = (4 : ℤ) ∧
    (∑ n ∈ Ico 17152 17280, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 17152 17280, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (1155385 : ℤ) ∧
    (∑ n ∈ Ico 17152 17280, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (23107763720282968946591927440 : ℤ) := by
  rcases cdemPrefixStats_17152_17216 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_17216_17280 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 17152 ≤ 17216) (by norm_num : 17216 ≤ 17280), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 17152 ≤ 17216) (by norm_num : 17216 ≤ 17280), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 17152 ≤ 17216) (by norm_num : 17216 ≤ 17280), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 17152 ≤ 17216) (by norm_num : 17216 ≤ 17280), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_17280_17344 :
    (∑ n ∈ Ico 17280 17344, mobiusTreeValue 16 mobiusTable1200001 n) = (-4 : ℤ) ∧
    (∑ n ∈ Ico 17280 17344, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 17280 17344, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-1154897 : ℤ) ∧
    (∑ n ∈ Ico 17280 17344, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-23097972778348190045658677898 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_17344_17408 :
    (∑ n ∈ Ico 17344 17408, mobiusTreeValue 16 mobiusTable1200001 n) = (7 : ℤ) ∧
    (∑ n ∈ Ico 17344 17408, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 17344 17408, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (2013894 : ℤ) ∧
    (∑ n ∈ Ico 17344 17408, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (40277894373865157098815845794 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_17280_17408 :
    (∑ n ∈ Ico 17280 17408, mobiusTreeValue 16 mobiusTable1200001 n) = (3 : ℤ) ∧
    (∑ n ∈ Ico 17280 17408, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 17280 17408, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (858997 : ℤ) ∧
    (∑ n ∈ Ico 17280 17408, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (17179921595516967053157167896 : ℤ) := by
  rcases cdemPrefixStats_17280_17344 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_17344_17408 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 17280 ≤ 17344) (by norm_num : 17344 ≤ 17408), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 17280 ≤ 17344) (by norm_num : 17344 ≤ 17408), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 17280 ≤ 17344) (by norm_num : 17344 ≤ 17408), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 17280 ≤ 17344) (by norm_num : 17344 ≤ 17408), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_17152_17408 :
    (∑ n ∈ Ico 17152 17408, mobiusTreeValue 16 mobiusTable1200001 n) = (7 : ℤ) ∧
    (∑ n ∈ Ico 17152 17408, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (155 : ℕ) ∧
    (∑ n ∈ Ico 17152 17408, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (2014382 : ℤ) ∧
    (∑ n ∈ Ico 17152 17408, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (40287685315799935999749095336 : ℤ) := by
  rcases cdemPrefixStats_17152_17280 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_17280_17408 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 17152 ≤ 17280) (by norm_num : 17280 ≤ 17408), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 17152 ≤ 17280) (by norm_num : 17280 ≤ 17408), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 17152 ≤ 17280) (by norm_num : 17280 ≤ 17408), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 17152 ≤ 17280) (by norm_num : 17280 ≤ 17408), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_16896_17408 :
    (∑ n ∈ Ico 16896 17408, mobiusTreeValue 16 mobiusTable1200001 n) = (2 : ℤ) ∧
    (∑ n ∈ Ico 16896 17408, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (310 : ℕ) ∧
    (∑ n ∈ Ico 16896 17408, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (533320 : ℤ) ∧
    (∑ n ∈ Ico 16896 17408, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (10666371071232655028529108860 : ℤ) := by
  rcases cdemPrefixStats_16896_17152 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_17152_17408 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 16896 ≤ 17152) (by norm_num : 17152 ≤ 17408), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 16896 ≤ 17152) (by norm_num : 17152 ≤ 17408), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 16896 ≤ 17152) (by norm_num : 17152 ≤ 17408), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 16896 ≤ 17152) (by norm_num : 17152 ≤ 17408), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_16384_17408 :
    (∑ n ∈ Ico 16384 17408, mobiusTreeValue 16 mobiusTable1200001 n) = (19 : ℤ) ∧
    (∑ n ∈ Ico 16384 17408, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (623 : ℕ) ∧
    (∑ n ∈ Ico 16384 17408, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (5644289 : ℤ) ∧
    (∑ n ∈ Ico 16384 17408, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (112885844040096709533676362887 : ℤ) := by
  rcases cdemPrefixStats_16384_16896 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_16896_17408 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 16384 ≤ 16896) (by norm_num : 16896 ≤ 17408), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 16384 ≤ 16896) (by norm_num : 16896 ≤ 17408), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 16384 ≤ 16896) (by norm_num : 16896 ≤ 17408), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 16384 ≤ 16896) (by norm_num : 16896 ≤ 17408), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_17408_17472 :
    (∑ n ∈ Ico 17408 17472, mobiusTreeValue 16 mobiusTable1200001 n) = (-4 : ℤ) ∧
    (∑ n ∈ Ico 17408 17472, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 17408 17472, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-1147907 : ℤ) ∧
    (∑ n ∈ Ico 17408 17472, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-22958181648308381637956357032 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_17472_17536 :
    (∑ n ∈ Ico 17472 17536, mobiusTreeValue 16 mobiusTable1200001 n) = (-2 : ℤ) ∧
    (∑ n ∈ Ico 17472 17536, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 17472 17536, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-573905 : ℤ) ∧
    (∑ n ∈ Ico 17472 17536, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-11478129887235617197910165170 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_17408_17536 :
    (∑ n ∈ Ico 17408 17536, mobiusTreeValue 16 mobiusTable1200001 n) = (-6 : ℤ) ∧
    (∑ n ∈ Ico 17408 17536, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (80 : ℕ) ∧
    (∑ n ∈ Ico 17408 17536, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-1721812 : ℤ) ∧
    (∑ n ∈ Ico 17408 17536, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-34436311535543998835866522202 : ℤ) := by
  rcases cdemPrefixStats_17408_17472 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_17472_17536 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 17408 ≤ 17472) (by norm_num : 17472 ≤ 17536), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 17408 ≤ 17472) (by norm_num : 17472 ≤ 17536), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 17408 ≤ 17472) (by norm_num : 17472 ≤ 17536), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 17408 ≤ 17472) (by norm_num : 17472 ≤ 17536), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_17536_17600 :
    (∑ n ∈ Ico 17536 17600, mobiusTreeValue 16 mobiusTable1200001 n) = (2 : ℤ) ∧
    (∑ n ∈ Ico 17536 17600, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 17536 17600, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (569099 : ℤ) ∧
    (∑ n ∈ Ico 17536 17600, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (11382047718060936201702066078 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_17600_17664 :
    (∑ n ∈ Ico 17600 17664, mobiusTreeValue 16 mobiusTable1200001 n) = (11 : ℤ) ∧
    (∑ n ∈ Ico 17600 17664, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 17600 17664, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (3117558 : ℤ) ∧
    (∑ n ∈ Ico 17600 17664, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (62351276912533039466250644724 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_17536_17664 :
    (∑ n ∈ Ico 17536 17664, mobiusTreeValue 16 mobiusTable1200001 n) = (13 : ℤ) ∧
    (∑ n ∈ Ico 17536 17664, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 17536 17664, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (3686657 : ℤ) ∧
    (∑ n ∈ Ico 17536 17664, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (73733324630593975667952710802 : ℤ) := by
  rcases cdemPrefixStats_17536_17600 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_17600_17664 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 17536 ≤ 17600) (by norm_num : 17600 ≤ 17664), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 17536 ≤ 17600) (by norm_num : 17600 ≤ 17664), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 17536 ≤ 17600) (by norm_num : 17600 ≤ 17664), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 17536 ≤ 17600) (by norm_num : 17600 ≤ 17664), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_17408_17664 :
    (∑ n ∈ Ico 17408 17664, mobiusTreeValue 16 mobiusTable1200001 n) = (7 : ℤ) ∧
    (∑ n ∈ Ico 17408 17664, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (157 : ℕ) ∧
    (∑ n ∈ Ico 17408 17664, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (1964845 : ℤ) ∧
    (∑ n ∈ Ico 17408 17664, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (39297013095049976832086188600 : ℤ) := by
  rcases cdemPrefixStats_17408_17536 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_17536_17664 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 17408 ≤ 17536) (by norm_num : 17536 ≤ 17664), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 17408 ≤ 17536) (by norm_num : 17536 ≤ 17664), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 17408 ≤ 17536) (by norm_num : 17536 ≤ 17664), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 17408 ≤ 17536) (by norm_num : 17536 ≤ 17664), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_17664_17728 :
    (∑ n ∈ Ico 17664 17728, mobiusTreeValue 16 mobiusTable1200001 n) = (5 : ℤ) ∧
    (∑ n ∈ Ico 17664 17728, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 17664 17728, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (1413115 : ℤ) ∧
    (∑ n ∈ Ico 17664 17728, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (28262325634964893147087771305 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_17728_17792 :
    (∑ n ∈ Ico 17728 17792, mobiusTreeValue 16 mobiusTable1200001 n) = (-3 : ℤ) ∧
    (∑ n ∈ Ico 17728 17792, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 17728 17792, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-846829 : ℤ) ∧
    (∑ n ∈ Ico 17728 17792, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-16936617174383044891943346817 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_17664_17792 :
    (∑ n ∈ Ico 17664 17792, mobiusTreeValue 16 mobiusTable1200001 n) = (2 : ℤ) ∧
    (∑ n ∈ Ico 17664 17792, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 17664 17792, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (566286 : ℤ) ∧
    (∑ n ∈ Ico 17664 17792, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (11325708460581848255144424488 : ℤ) := by
  rcases cdemPrefixStats_17664_17728 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_17728_17792 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 17664 ≤ 17728) (by norm_num : 17728 ≤ 17792), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 17664 ≤ 17728) (by norm_num : 17728 ≤ 17792), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 17664 ≤ 17728) (by norm_num : 17728 ≤ 17792), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 17664 ≤ 17728) (by norm_num : 17728 ≤ 17792), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_17792_17856 :
    (∑ n ∈ Ico 17792 17856, mobiusTreeValue 16 mobiusTable1200001 n) = (-3 : ℤ) ∧
    (∑ n ∈ Ico 17792 17856, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 17792 17856, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-840053 : ℤ) ∧
    (∑ n ∈ Ico 17792 17856, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-16801030556200640792730672319 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_17856_17920 :
    (∑ n ∈ Ico 17856 17920, mobiusTreeValue 16 mobiusTable1200001 n) = (4 : ℤ) ∧
    (∑ n ∈ Ico 17856 17920, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 17856 17920, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (1122129 : ℤ) ∧
    (∑ n ∈ Ico 17856 17920, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (22442665455204071991260359689 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_17792_17920 :
    (∑ n ∈ Ico 17792 17920, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 17792 17920, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 17792 17920, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (282076 : ℤ) ∧
    (∑ n ∈ Ico 17792 17920, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (5641634899003431198529687370 : ℤ) := by
  rcases cdemPrefixStats_17792_17856 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_17856_17920 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 17792 ≤ 17856) (by norm_num : 17856 ≤ 17920), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 17792 ≤ 17856) (by norm_num : 17856 ≤ 17920), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 17792 ≤ 17856) (by norm_num : 17856 ≤ 17920), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 17792 ≤ 17856) (by norm_num : 17856 ≤ 17920), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_17664_17920 :
    (∑ n ∈ Ico 17664 17920, mobiusTreeValue 16 mobiusTable1200001 n) = (3 : ℤ) ∧
    (∑ n ∈ Ico 17664 17920, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (155 : ℕ) ∧
    (∑ n ∈ Ico 17664 17920, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (848362 : ℤ) ∧
    (∑ n ∈ Ico 17664 17920, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (16967343359585279453674111858 : ℤ) := by
  rcases cdemPrefixStats_17664_17792 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_17792_17920 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 17664 ≤ 17792) (by norm_num : 17792 ≤ 17920), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 17664 ≤ 17792) (by norm_num : 17792 ≤ 17920), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 17664 ≤ 17792) (by norm_num : 17792 ≤ 17920), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 17664 ≤ 17792) (by norm_num : 17792 ≤ 17920), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_17408_17920 :
    (∑ n ∈ Ico 17408 17920, mobiusTreeValue 16 mobiusTable1200001 n) = (10 : ℤ) ∧
    (∑ n ∈ Ico 17408 17920, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (312 : ℕ) ∧
    (∑ n ∈ Ico 17408 17920, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (2813207 : ℤ) ∧
    (∑ n ∈ Ico 17408 17920, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (56264356454635256285760300458 : ℤ) := by
  rcases cdemPrefixStats_17408_17664 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_17664_17920 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 17408 ≤ 17664) (by norm_num : 17664 ≤ 17920), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 17408 ≤ 17664) (by norm_num : 17664 ≤ 17920), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 17408 ≤ 17664) (by norm_num : 17664 ≤ 17920), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 17408 ≤ 17664) (by norm_num : 17664 ≤ 17920), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_17920_17984 :
    (∑ n ∈ Ico 17920 17984, mobiusTreeValue 16 mobiusTable1200001 n) = (-8 : ℤ) ∧
    (∑ n ∈ Ico 17920 17984, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 17920 17984, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-2226706 : ℤ) ∧
    (∑ n ∈ Ico 17920 17984, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-44534187407006024888127300995 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_17984_18048 :
    (∑ n ∈ Ico 17984 18048, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 17984 18048, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 17984 18048, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (766 : ℤ) ∧
    (∑ n ∈ Ico 17984 18048, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (15359871029965818554463274 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_17920_18048 :
    (∑ n ∈ Ico 17920 18048, mobiusTreeValue 16 mobiusTable1200001 n) = (-8 : ℤ) ∧
    (∑ n ∈ Ico 17920 18048, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 17920 18048, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-2225940 : ℤ) ∧
    (∑ n ∈ Ico 17920 18048, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-44518827535976059069572837721 : ℤ) := by
  rcases cdemPrefixStats_17920_17984 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_17984_18048 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 17920 ≤ 17984) (by norm_num : 17984 ≤ 18048), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 17920 ≤ 17984) (by norm_num : 17984 ≤ 18048), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 17920 ≤ 17984) (by norm_num : 17984 ≤ 18048), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 17920 ≤ 17984) (by norm_num : 17984 ≤ 18048), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_18048_18112 :
    (∑ n ∈ Ico 18048 18112, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 18048 18112, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 18048 18112, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-3196 : ℤ) ∧
    (∑ n ∈ Ico 18048 18112, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-63964380598407542219562146 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_18112_18176 :
    (∑ n ∈ Ico 18112 18176, mobiusTreeValue 16 mobiusTable1200001 n) = (-2 : ℤ) ∧
    (∑ n ∈ Ico 18112 18176, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 18112 18176, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-552755 : ℤ) ∧
    (∑ n ∈ Ico 18112 18176, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-11055079939010232072968158215 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_18048_18176 :
    (∑ n ∈ Ico 18048 18176, mobiusTreeValue 16 mobiusTable1200001 n) = (-2 : ℤ) ∧
    (∑ n ∈ Ico 18048 18176, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 18048 18176, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-555951 : ℤ) ∧
    (∑ n ∈ Ico 18048 18176, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-11119044319608639615187720361 : ℤ) := by
  rcases cdemPrefixStats_18048_18112 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_18112_18176 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 18048 ≤ 18112) (by norm_num : 18112 ≤ 18176), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 18048 ≤ 18112) (by norm_num : 18112 ≤ 18176), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 18048 ≤ 18112) (by norm_num : 18112 ≤ 18176), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 18048 ≤ 18112) (by norm_num : 18112 ≤ 18176), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_17920_18176 :
    (∑ n ∈ Ico 17920 18176, mobiusTreeValue 16 mobiusTable1200001 n) = (-10 : ℤ) ∧
    (∑ n ∈ Ico 17920 18176, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (156 : ℕ) ∧
    (∑ n ∈ Ico 17920 18176, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-2781891 : ℤ) ∧
    (∑ n ∈ Ico 17920 18176, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-55637871855584698684760558082 : ℤ) := by
  rcases cdemPrefixStats_17920_18048 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_18048_18176 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 17920 ≤ 18048) (by norm_num : 18048 ≤ 18176), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 17920 ≤ 18048) (by norm_num : 18048 ≤ 18176), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 17920 ≤ 18048) (by norm_num : 18048 ≤ 18176), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 17920 ≤ 18048) (by norm_num : 18048 ≤ 18176), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_18176_18240 :
    (∑ n ∈ Ico 18176 18240, mobiusTreeValue 16 mobiusTable1200001 n) = (-8 : ℤ) ∧
    (∑ n ∈ Ico 18176 18240, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (42 : ℕ) ∧
    (∑ n ∈ Ico 18176 18240, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-2194152 : ℤ) ∧
    (∑ n ∈ Ico 18176 18240, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-43883116538964848169896420969 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_18240_18304 :
    (∑ n ∈ Ico 18240 18304, mobiusTreeValue 16 mobiusTable1200001 n) = (4 : ℤ) ∧
    (∑ n ∈ Ico 18240 18304, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 18240 18304, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (1091514 : ℤ) ∧
    (∑ n ∈ Ico 18240 18304, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (21830301689066933014929608776 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_18176_18304 :
    (∑ n ∈ Ico 18176 18304, mobiusTreeValue 16 mobiusTable1200001 n) = (-4 : ℤ) ∧
    (∑ n ∈ Ico 18176 18304, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (80 : ℕ) ∧
    (∑ n ∈ Ico 18176 18304, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-1102638 : ℤ) ∧
    (∑ n ∈ Ico 18176 18304, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-22052814849897915154966812193 : ℤ) := by
  rcases cdemPrefixStats_18176_18240 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_18240_18304 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 18176 ≤ 18240) (by norm_num : 18240 ≤ 18304), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 18176 ≤ 18240) (by norm_num : 18240 ≤ 18304), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 18176 ≤ 18240) (by norm_num : 18240 ≤ 18304), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 18176 ≤ 18240) (by norm_num : 18240 ≤ 18304), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_18304_18368 :
    (∑ n ∈ Ico 18304 18368, mobiusTreeValue 16 mobiusTable1200001 n) = (-6 : ℤ) ∧
    (∑ n ∈ Ico 18304 18368, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 18304 18368, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-1637136 : ℤ) ∧
    (∑ n ∈ Ico 18304 18368, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-32742796356212813270163844300 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_18368_18432 :
    (∑ n ∈ Ico 18368 18432, mobiusTreeValue 16 mobiusTable1200001 n) = (4 : ℤ) ∧
    (∑ n ∈ Ico 18368 18432, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 18368 18432, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (1086158 : ℤ) ∧
    (∑ n ∈ Ico 18368 18432, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (21723232464672958864783238956 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_18304_18432 :
    (∑ n ∈ Ico 18304 18432, mobiusTreeValue 16 mobiusTable1200001 n) = (-2 : ℤ) ∧
    (∑ n ∈ Ico 18304 18432, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 18304 18432, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-550978 : ℤ) ∧
    (∑ n ∈ Ico 18304 18432, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-11019563891539854405380605344 : ℤ) := by
  rcases cdemPrefixStats_18304_18368 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_18368_18432 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 18304 ≤ 18368) (by norm_num : 18368 ≤ 18432), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 18304 ≤ 18368) (by norm_num : 18368 ≤ 18432), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 18304 ≤ 18368) (by norm_num : 18368 ≤ 18432), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 18304 ≤ 18368) (by norm_num : 18368 ≤ 18432), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_18176_18432 :
    (∑ n ∈ Ico 18176 18432, mobiusTreeValue 16 mobiusTable1200001 n) = (-6 : ℤ) ∧
    (∑ n ∈ Ico 18176 18432, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (158 : ℕ) ∧
    (∑ n ∈ Ico 18176 18432, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-1653616 : ℤ) ∧
    (∑ n ∈ Ico 18176 18432, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-33072378741437769560347417537 : ℤ) := by
  rcases cdemPrefixStats_18176_18304 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_18304_18432 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 18176 ≤ 18304) (by norm_num : 18304 ≤ 18432), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 18176 ≤ 18304) (by norm_num : 18304 ≤ 18432), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 18176 ≤ 18304) (by norm_num : 18304 ≤ 18432), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 18176 ≤ 18304) (by norm_num : 18304 ≤ 18432), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_17920_18432 :
    (∑ n ∈ Ico 17920 18432, mobiusTreeValue 16 mobiusTable1200001 n) = (-16 : ℤ) ∧
    (∑ n ∈ Ico 17920 18432, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (314 : ℕ) ∧
    (∑ n ∈ Ico 17920 18432, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-4435507 : ℤ) ∧
    (∑ n ∈ Ico 17920 18432, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-88710250597022468245107975619 : ℤ) := by
  rcases cdemPrefixStats_17920_18176 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_18176_18432 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 17920 ≤ 18176) (by norm_num : 18176 ≤ 18432), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 17920 ≤ 18176) (by norm_num : 18176 ≤ 18432), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 17920 ≤ 18176) (by norm_num : 18176 ≤ 18432), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 17920 ≤ 18176) (by norm_num : 18176 ≤ 18432), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_17408_18432 :
    (∑ n ∈ Ico 17408 18432, mobiusTreeValue 16 mobiusTable1200001 n) = (-6 : ℤ) ∧
    (∑ n ∈ Ico 17408 18432, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (626 : ℕ) ∧
    (∑ n ∈ Ico 17408 18432, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-1622300 : ℤ) ∧
    (∑ n ∈ Ico 17408 18432, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-32445894142387211959347675161 : ℤ) := by
  rcases cdemPrefixStats_17408_17920 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_17920_18432 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 17408 ≤ 17920) (by norm_num : 17920 ≤ 18432), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 17408 ≤ 17920) (by norm_num : 17920 ≤ 18432), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 17408 ≤ 17920) (by norm_num : 17920 ≤ 18432), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 17408 ≤ 17920) (by norm_num : 17920 ≤ 18432), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_16384_18432 :
    (∑ n ∈ Ico 16384 18432, mobiusTreeValue 16 mobiusTable1200001 n) = (13 : ℤ) ∧
    (∑ n ∈ Ico 16384 18432, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (1249 : ℕ) ∧
    (∑ n ∈ Ico 16384 18432, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (4021989 : ℤ) ∧
    (∑ n ∈ Ico 16384 18432, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (80439949897709497574328687726 : ℤ) := by
  rcases cdemPrefixStats_16384_17408 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_17408_18432 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 16384 ≤ 17408) (by norm_num : 17408 ≤ 18432), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 16384 ≤ 17408) (by norm_num : 17408 ≤ 18432), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 16384 ≤ 17408) (by norm_num : 17408 ≤ 18432), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 16384 ≤ 17408) (by norm_num : 17408 ≤ 18432), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_18432_18496 :
    (∑ n ∈ Ico 18432 18496, mobiusTreeValue 16 mobiusTable1200001 n) = (-4 : ℤ) ∧
    (∑ n ∈ Ico 18432 18496, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 18432 18496, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-1082762 : ℤ) ∧
    (∑ n ∈ Ico 18432 18496, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-21655313046727694266999597404 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_18496_18560 :
    (∑ n ∈ Ico 18496 18560, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 18496 18560, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 18496 18560, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-269788 : ℤ) ∧
    (∑ n ∈ Ico 18496 18560, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-5395775347292888552820336317 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_18432_18560 :
    (∑ n ∈ Ico 18432 18560, mobiusTreeValue 16 mobiusTable1200001 n) = (-5 : ℤ) ∧
    (∑ n ∈ Ico 18432 18560, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 18432 18560, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-1352550 : ℤ) ∧
    (∑ n ∈ Ico 18432 18560, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-27051088394020582819819933721 : ℤ) := by
  rcases cdemPrefixStats_18432_18496 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_18496_18560 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 18432 ≤ 18496) (by norm_num : 18496 ≤ 18560), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 18432 ≤ 18496) (by norm_num : 18496 ≤ 18560), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 18432 ≤ 18496) (by norm_num : 18496 ≤ 18560), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 18432 ≤ 18496) (by norm_num : 18496 ≤ 18560), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_18560_18624 :
    (∑ n ∈ Ico 18560 18624, mobiusTreeValue 16 mobiusTable1200001 n) = (9 : ℤ) ∧
    (∑ n ∈ Ico 18560 18624, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 18560 18624, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (2418848 : ℤ) ∧
    (∑ n ∈ Ico 18560 18624, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (48377037195533219825899775187 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_18624_18688 :
    (∑ n ∈ Ico 18624 18688, mobiusTreeValue 16 mobiusTable1200001 n) = (15 : ℤ) ∧
    (∑ n ∈ Ico 18624 18688, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 18624 18688, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (4021027 : ℤ) ∧
    (∑ n ∈ Ico 18624 18688, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (80420655682843200447647444908 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_18560_18688 :
    (∑ n ∈ Ico 18560 18688, mobiusTreeValue 16 mobiusTable1200001 n) = (24 : ℤ) ∧
    (∑ n ∈ Ico 18560 18688, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 18560 18688, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (6439875 : ℤ) ∧
    (∑ n ∈ Ico 18560 18688, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (128797692878376420273547220095 : ℤ) := by
  rcases cdemPrefixStats_18560_18624 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_18624_18688 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 18560 ≤ 18624) (by norm_num : 18624 ≤ 18688), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 18560 ≤ 18624) (by norm_num : 18624 ≤ 18688), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 18560 ≤ 18624) (by norm_num : 18624 ≤ 18688), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 18560 ≤ 18624) (by norm_num : 18624 ≤ 18688), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_18432_18688 :
    (∑ n ∈ Ico 18432 18688, mobiusTreeValue 16 mobiusTable1200001 n) = (19 : ℤ) ∧
    (∑ n ∈ Ico 18432 18688, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (155 : ℕ) ∧
    (∑ n ∈ Ico 18432 18688, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (5087325 : ℤ) ∧
    (∑ n ∈ Ico 18432 18688, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (101746604484355837453727286374 : ℤ) := by
  rcases cdemPrefixStats_18432_18560 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_18560_18688 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 18432 ≤ 18560) (by norm_num : 18560 ≤ 18688), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 18432 ≤ 18560) (by norm_num : 18560 ≤ 18688), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 18432 ≤ 18560) (by norm_num : 18560 ≤ 18688), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 18432 ≤ 18560) (by norm_num : 18560 ≤ 18688), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_18688_18752 :
    (∑ n ∈ Ico 18688 18752, mobiusTreeValue 16 mobiusTable1200001 n) = (-2 : ℤ) ∧
    (∑ n ∈ Ico 18688 18752, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 18688 18752, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-534783 : ℤ) ∧
    (∑ n ∈ Ico 18688 18752, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-10695736795056812548707792862 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_18752_18816 :
    (∑ n ∈ Ico 18752 18816, mobiusTreeValue 16 mobiusTable1200001 n) = (7 : ℤ) ∧
    (∑ n ∈ Ico 18752 18816, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 18752 18816, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (1862395 : ℤ) ∧
    (∑ n ∈ Ico 18752 18816, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (37247955249955743329653837827 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_18688_18816 :
    (∑ n ∈ Ico 18688 18816, mobiusTreeValue 16 mobiusTable1200001 n) = (5 : ℤ) ∧
    (∑ n ∈ Ico 18688 18816, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (75 : ℕ) ∧
    (∑ n ∈ Ico 18688 18816, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (1327612 : ℤ) ∧
    (∑ n ∈ Ico 18688 18816, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (26552218454898930780946044965 : ℤ) := by
  rcases cdemPrefixStats_18688_18752 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_18752_18816 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 18688 ≤ 18752) (by norm_num : 18752 ≤ 18816), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 18688 ≤ 18752) (by norm_num : 18752 ≤ 18816), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 18688 ≤ 18752) (by norm_num : 18752 ≤ 18816), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 18688 ≤ 18752) (by norm_num : 18752 ≤ 18816), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_18816_18880 :
    (∑ n ∈ Ico 18816 18880, mobiusTreeValue 16 mobiusTable1200001 n) = (18 : ℤ) ∧
    (∑ n ∈ Ico 18816 18880, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 18816 18880, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (4775167 : ℤ) ∧
    (∑ n ∈ Ico 18816 18880, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (95503477161578112972475859922 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_18880_18944 :
    (∑ n ∈ Ico 18880 18944, mobiusTreeValue 16 mobiusTable1200001 n) = (7 : ℤ) ∧
    (∑ n ∈ Ico 18880 18944, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 18880 18944, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (1851095 : ℤ) ∧
    (∑ n ∈ Ico 18880 18944, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (37021958378549032326023082616 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_18816_18944 :
    (∑ n ∈ Ico 18816 18944, mobiusTreeValue 16 mobiusTable1200001 n) = (25 : ℤ) ∧
    (∑ n ∈ Ico 18816 18944, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (79 : ℕ) ∧
    (∑ n ∈ Ico 18816 18944, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (6626262 : ℤ) ∧
    (∑ n ∈ Ico 18816 18944, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (132525435540127145298498942538 : ℤ) := by
  rcases cdemPrefixStats_18816_18880 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_18880_18944 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 18816 ≤ 18880) (by norm_num : 18880 ≤ 18944), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 18816 ≤ 18880) (by norm_num : 18880 ≤ 18944), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 18816 ≤ 18880) (by norm_num : 18880 ≤ 18944), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 18816 ≤ 18880) (by norm_num : 18880 ≤ 18944), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_18688_18944 :
    (∑ n ∈ Ico 18688 18944, mobiusTreeValue 16 mobiusTable1200001 n) = (30 : ℤ) ∧
    (∑ n ∈ Ico 18688 18944, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (154 : ℕ) ∧
    (∑ n ∈ Ico 18688 18944, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (7953874 : ℤ) ∧
    (∑ n ∈ Ico 18688 18944, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (159077653995026076079444987503 : ℤ) := by
  rcases cdemPrefixStats_18688_18816 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_18816_18944 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 18688 ≤ 18816) (by norm_num : 18816 ≤ 18944), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 18688 ≤ 18816) (by norm_num : 18816 ≤ 18944), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 18688 ≤ 18816) (by norm_num : 18816 ≤ 18944), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 18688 ≤ 18816) (by norm_num : 18816 ≤ 18944), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_18432_18944 :
    (∑ n ∈ Ico 18432 18944, mobiusTreeValue 16 mobiusTable1200001 n) = (49 : ℤ) ∧
    (∑ n ∈ Ico 18432 18944, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (309 : ℕ) ∧
    (∑ n ∈ Ico 18432 18944, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (13041199 : ℤ) ∧
    (∑ n ∈ Ico 18432 18944, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (260824258479381913533172273877 : ℤ) := by
  rcases cdemPrefixStats_18432_18688 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_18688_18944 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 18432 ≤ 18688) (by norm_num : 18688 ≤ 18944), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 18432 ≤ 18688) (by norm_num : 18688 ≤ 18944), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 18432 ≤ 18688) (by norm_num : 18688 ≤ 18944), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 18432 ≤ 18688) (by norm_num : 18688 ≤ 18944), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_18944_19008 :
    (∑ n ∈ Ico 18944 19008, mobiusTreeValue 16 mobiusTable1200001 n) = (11 : ℤ) ∧
    (∑ n ∈ Ico 18944 19008, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 18944 19008, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (2897895 : ℤ) ∧
    (∑ n ∈ Ico 18944 19008, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (57958027227806465714487926332 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_19008_19072 :
    (∑ n ∈ Ico 19008 19072, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 19008 19072, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 19008 19072, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-262552 : ℤ) ∧
    (∑ n ∈ Ico 19008 19072, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-5251013748164850200435117316 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_18944_19072 :
    (∑ n ∈ Ico 18944 19072, mobiusTreeValue 16 mobiusTable1200001 n) = (10 : ℤ) ∧
    (∑ n ∈ Ico 18944 19072, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 18944 19072, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (2635343 : ℤ) ∧
    (∑ n ∈ Ico 18944 19072, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (52707013479641615514052809016 : ℤ) := by
  rcases cdemPrefixStats_18944_19008 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_19008_19072 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 18944 ≤ 19008) (by norm_num : 19008 ≤ 19072), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 18944 ≤ 19008) (by norm_num : 19008 ≤ 19072), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 18944 ≤ 19008) (by norm_num : 19008 ≤ 19072), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 18944 ≤ 19008) (by norm_num : 19008 ≤ 19072), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_19072_19136 :
    (∑ n ∈ Ico 19072 19136, mobiusTreeValue 16 mobiusTable1200001 n) = (5 : ℤ) ∧
    (∑ n ∈ Ico 19072 19136, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 19072 19136, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (1310320 : ℤ) ∧
    (∑ n ∈ Ico 19072 19136, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (26206464610398400982705273326 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_19136_19200 :
    (∑ n ∈ Ico 19136 19200, mobiusTreeValue 16 mobiusTable1200001 n) = (3 : ℤ) ∧
    (∑ n ∈ Ico 19136 19200, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 19136 19200, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (779965 : ℤ) ∧
    (∑ n ∈ Ico 19136 19200, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (15599353847573702230484451762 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_19072_19200 :
    (∑ n ∈ Ico 19072 19200, mobiusTreeValue 16 mobiusTable1200001 n) = (8 : ℤ) ∧
    (∑ n ∈ Ico 19072 19200, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (76 : ℕ) ∧
    (∑ n ∈ Ico 19072 19200, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (2090285 : ℤ) ∧
    (∑ n ∈ Ico 19072 19200, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (41805818457972103213189725088 : ℤ) := by
  rcases cdemPrefixStats_19072_19136 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_19136_19200 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 19072 ≤ 19136) (by norm_num : 19136 ≤ 19200), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 19072 ≤ 19136) (by norm_num : 19136 ≤ 19200), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 19072 ≤ 19136) (by norm_num : 19136 ≤ 19200), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 19072 ≤ 19136) (by norm_num : 19136 ≤ 19200), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_18944_19200 :
    (∑ n ∈ Ico 18944 19200, mobiusTreeValue 16 mobiusTable1200001 n) = (18 : ℤ) ∧
    (∑ n ∈ Ico 18944 19200, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (154 : ℕ) ∧
    (∑ n ∈ Ico 18944 19200, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (4725628 : ℤ) ∧
    (∑ n ∈ Ico 18944 19200, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (94512831937613718727242534104 : ℤ) := by
  rcases cdemPrefixStats_18944_19072 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_19072_19200 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 18944 ≤ 19072) (by norm_num : 19072 ≤ 19200), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 18944 ≤ 19072) (by norm_num : 19072 ≤ 19200), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 18944 ≤ 19072) (by norm_num : 19072 ≤ 19200), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 18944 ≤ 19072) (by norm_num : 19072 ≤ 19200), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_19200_19264 :
    (∑ n ∈ Ico 19200 19264, mobiusTreeValue 16 mobiusTable1200001 n) = (-3 : ℤ) ∧
    (∑ n ∈ Ico 19200 19264, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 19200 19264, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-783057 : ℤ) ∧
    (∑ n ∈ Ico 19200 19264, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-15661214169170805968323997652 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_19264_19328 :
    (∑ n ∈ Ico 19264 19328, mobiusTreeValue 16 mobiusTable1200001 n) = (-3 : ℤ) ∧
    (∑ n ∈ Ico 19264 19328, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 19264 19328, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-774527 : ℤ) ∧
    (∑ n ∈ Ico 19264 19328, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-15490616249328073609324883070 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_19200_19328 :
    (∑ n ∈ Ico 19200 19328, mobiusTreeValue 16 mobiusTable1200001 n) = (-6 : ℤ) ∧
    (∑ n ∈ Ico 19200 19328, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (76 : ℕ) ∧
    (∑ n ∈ Ico 19200 19328, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-1557584 : ℤ) ∧
    (∑ n ∈ Ico 19200 19328, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-31151830418498879577648880722 : ℤ) := by
  rcases cdemPrefixStats_19200_19264 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_19264_19328 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 19200 ≤ 19264) (by norm_num : 19264 ≤ 19328), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 19200 ≤ 19264) (by norm_num : 19264 ≤ 19328), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 19200 ≤ 19264) (by norm_num : 19264 ≤ 19328), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 19200 ≤ 19264) (by norm_num : 19264 ≤ 19328), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_19328_19392 :
    (∑ n ∈ Ico 19328 19392, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 19328 19392, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 19328 19392, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (258703 : ℤ) ∧
    (∑ n ∈ Ico 19328 19392, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (5174043786251503901706337231 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_19392_19456 :
    (∑ n ∈ Ico 19392 19456, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 19392 19456, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 19392 19456, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-258380 : ℤ) ∧
    (∑ n ∈ Ico 19392 19456, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-5167622381904427132362480523 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_19328_19456 :
    (∑ n ∈ Ico 19328 19456, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 19328 19456, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 19328 19456, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (323 : ℤ) ∧
    (∑ n ∈ Ico 19328 19456, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (6421404347076769343856708 : ℤ) := by
  rcases cdemPrefixStats_19328_19392 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_19392_19456 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 19328 ≤ 19392) (by norm_num : 19392 ≤ 19456), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 19328 ≤ 19392) (by norm_num : 19392 ≤ 19456), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 19328 ≤ 19392) (by norm_num : 19392 ≤ 19456), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 19328 ≤ 19392) (by norm_num : 19392 ≤ 19456), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_19200_19456 :
    (∑ n ∈ Ico 19200 19456, mobiusTreeValue 16 mobiusTable1200001 n) = (-6 : ℤ) ∧
    (∑ n ∈ Ico 19200 19456, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (154 : ℕ) ∧
    (∑ n ∈ Ico 19200 19456, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-1557261 : ℤ) ∧
    (∑ n ∈ Ico 19200 19456, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-31145409014151802808305024014 : ℤ) := by
  rcases cdemPrefixStats_19200_19328 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_19328_19456 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 19200 ≤ 19328) (by norm_num : 19328 ≤ 19456), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 19200 ≤ 19328) (by norm_num : 19328 ≤ 19456), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 19200 ≤ 19328) (by norm_num : 19328 ≤ 19456), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 19200 ≤ 19328) (by norm_num : 19328 ≤ 19456), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_18944_19456 :
    (∑ n ∈ Ico 18944 19456, mobiusTreeValue 16 mobiusTable1200001 n) = (12 : ℤ) ∧
    (∑ n ∈ Ico 18944 19456, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (308 : ℕ) ∧
    (∑ n ∈ Ico 18944 19456, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (3168367 : ℤ) ∧
    (∑ n ∈ Ico 18944 19456, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (63367422923461915918937510090 : ℤ) := by
  rcases cdemPrefixStats_18944_19200 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_19200_19456 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 18944 ≤ 19200) (by norm_num : 19200 ≤ 19456), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 18944 ≤ 19200) (by norm_num : 19200 ≤ 19456), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 18944 ≤ 19200) (by norm_num : 19200 ≤ 19456), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 18944 ≤ 19200) (by norm_num : 19200 ≤ 19456), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_18432_19456 :
    (∑ n ∈ Ico 18432 19456, mobiusTreeValue 16 mobiusTable1200001 n) = (61 : ℤ) ∧
    (∑ n ∈ Ico 18432 19456, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (617 : ℕ) ∧
    (∑ n ∈ Ico 18432 19456, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (16209566 : ℤ) ∧
    (∑ n ∈ Ico 18432 19456, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (324191681402843829452109783967 : ℤ) := by
  rcases cdemPrefixStats_18432_18944 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_18944_19456 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 18432 ≤ 18944) (by norm_num : 18944 ≤ 19456), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 18432 ≤ 18944) (by norm_num : 18944 ≤ 19456), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 18432 ≤ 18944) (by norm_num : 18944 ≤ 19456), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 18432 ≤ 18944) (by norm_num : 18944 ≤ 19456), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_19456_19520 :
    (∑ n ∈ Ico 19456 19520, mobiusTreeValue 16 mobiusTable1200001 n) = (-16 : ℤ) ∧
    (∑ n ∈ Ico 19456 19520, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 19456 19520, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-4105311 : ℤ) ∧
    (∑ n ∈ Ico 19456 19520, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-82106381479932864020548852771 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_19520_19584 :
    (∑ n ∈ Ico 19520 19584, mobiusTreeValue 16 mobiusTable1200001 n) = (2 : ℤ) ∧
    (∑ n ∈ Ico 19520 19584, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 19520 19584, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (510158 : ℤ) ∧
    (∑ n ∈ Ico 19520 19584, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (10203232282021101656203964622 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_19456_19584 :
    (∑ n ∈ Ico 19456 19584, mobiusTreeValue 16 mobiusTable1200001 n) = (-14 : ℤ) ∧
    (∑ n ∈ Ico 19456 19584, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 19456 19584, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-3595153 : ℤ) ∧
    (∑ n ∈ Ico 19456 19584, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-71903149197911762364344888149 : ℤ) := by
  rcases cdemPrefixStats_19456_19520 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_19520_19584 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 19456 ≤ 19520) (by norm_num : 19520 ≤ 19584), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 19456 ≤ 19520) (by norm_num : 19520 ≤ 19584), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 19456 ≤ 19520) (by norm_num : 19520 ≤ 19584), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 19456 ≤ 19520) (by norm_num : 19520 ≤ 19584), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_19584_19648 :
    (∑ n ∈ Ico 19584 19648, mobiusTreeValue 16 mobiusTable1200001 n) = (13 : ℤ) ∧
    (∑ n ∈ Ico 19584 19648, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 19584 19648, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (3310850 : ℤ) ∧
    (∑ n ∈ Ico 19584 19648, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (66217157941658616719581630525 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_19648_19712 :
    (∑ n ∈ Ico 19648 19712, mobiusTreeValue 16 mobiusTable1200001 n) = (4 : ℤ) ∧
    (∑ n ∈ Ico 19648 19712, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 19648 19712, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (1018711 : ℤ) ∧
    (∑ n ∈ Ico 19648 19712, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (20374290922876507469337751682 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_19584_19712 :
    (∑ n ∈ Ico 19584 19712, mobiusTreeValue 16 mobiusTable1200001 n) = (17 : ℤ) ∧
    (∑ n ∈ Ico 19584 19712, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (79 : ℕ) ∧
    (∑ n ∈ Ico 19584 19712, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (4329561 : ℤ) ∧
    (∑ n ∈ Ico 19584 19712, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (86591448864535124188919382207 : ℤ) := by
  rcases cdemPrefixStats_19584_19648 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_19648_19712 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 19584 ≤ 19648) (by norm_num : 19648 ≤ 19712), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 19584 ≤ 19648) (by norm_num : 19648 ≤ 19712), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 19584 ≤ 19648) (by norm_num : 19648 ≤ 19712), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 19584 ≤ 19648) (by norm_num : 19648 ≤ 19712), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_19456_19712 :
    (∑ n ∈ Ico 19456 19712, mobiusTreeValue 16 mobiusTable1200001 n) = (3 : ℤ) ∧
    (∑ n ∈ Ico 19456 19712, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (157 : ℕ) ∧
    (∑ n ∈ Ico 19456 19712, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (734408 : ℤ) ∧
    (∑ n ∈ Ico 19456 19712, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (14688299666623361824574494058 : ℤ) := by
  rcases cdemPrefixStats_19456_19584 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_19584_19712 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 19456 ≤ 19584) (by norm_num : 19584 ≤ 19712), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 19456 ≤ 19584) (by norm_num : 19584 ≤ 19712), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 19456 ≤ 19584) (by norm_num : 19584 ≤ 19712), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 19456 ≤ 19584) (by norm_num : 19584 ≤ 19712), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_19712_19776 :
    (∑ n ∈ Ico 19712 19776, mobiusTreeValue 16 mobiusTable1200001 n) = (2 : ℤ) ∧
    (∑ n ∈ Ico 19712 19776, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 19712 19776, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (506997 : ℤ) ∧
    (∑ n ∈ Ico 19712 19776, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (10139970001269418431818075545 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_19776_19840 :
    (∑ n ∈ Ico 19776 19840, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 19776 19840, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (42 : ℕ) ∧
    (∑ n ∈ Ico 19776 19840, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-1834 : ℤ) ∧
    (∑ n ∈ Ico 19776 19840, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-36696075193838089810248567 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_19712_19840 :
    (∑ n ∈ Ico 19712 19840, mobiusTreeValue 16 mobiusTable1200001 n) = (2 : ℤ) ∧
    (∑ n ∈ Ico 19712 19840, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (80 : ℕ) ∧
    (∑ n ∈ Ico 19712 19840, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (505163 : ℤ) ∧
    (∑ n ∈ Ico 19712 19840, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (10103273926075580342007826978 : ℤ) := by
  rcases cdemPrefixStats_19712_19776 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_19776_19840 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 19712 ≤ 19776) (by norm_num : 19776 ≤ 19840), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 19712 ≤ 19776) (by norm_num : 19776 ≤ 19840), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 19712 ≤ 19776) (by norm_num : 19776 ≤ 19840), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 19712 ≤ 19776) (by norm_num : 19776 ≤ 19840), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_19840_19904 :
    (∑ n ∈ Ico 19840 19904, mobiusTreeValue 16 mobiusTable1200001 n) = (-6 : ℤ) ∧
    (∑ n ∈ Ico 19840 19904, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 19840 19904, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-1510545 : ℤ) ∧
    (∑ n ∈ Ico 19840 19904, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-30210953148509086895141288653 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_19904_19968 :
    (∑ n ∈ Ico 19904 19968, mobiusTreeValue 16 mobiusTable1200001 n) = (-5 : ℤ) ∧
    (∑ n ∈ Ico 19904 19968, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 19904 19968, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-1254127 : ℤ) ∧
    (∑ n ∈ Ico 19904 19968, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-25082554087302571537801766142 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_19840_19968 :
    (∑ n ∈ Ico 19840 19968, mobiusTreeValue 16 mobiusTable1200001 n) = (-11 : ℤ) ∧
    (∑ n ∈ Ico 19840 19968, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (75 : ℕ) ∧
    (∑ n ∈ Ico 19840 19968, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-2764672 : ℤ) ∧
    (∑ n ∈ Ico 19840 19968, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-55293507235811658432943054795 : ℤ) := by
  rcases cdemPrefixStats_19840_19904 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_19904_19968 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 19840 ≤ 19904) (by norm_num : 19904 ≤ 19968), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 19840 ≤ 19904) (by norm_num : 19904 ≤ 19968), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 19840 ≤ 19904) (by norm_num : 19904 ≤ 19968), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 19840 ≤ 19904) (by norm_num : 19904 ≤ 19968), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_19712_19968 :
    (∑ n ∈ Ico 19712 19968, mobiusTreeValue 16 mobiusTable1200001 n) = (-9 : ℤ) ∧
    (∑ n ∈ Ico 19712 19968, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (155 : ℕ) ∧
    (∑ n ∈ Ico 19712 19968, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-2259509 : ℤ) ∧
    (∑ n ∈ Ico 19712 19968, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-45190233309736078090935227817 : ℤ) := by
  rcases cdemPrefixStats_19712_19840 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_19840_19968 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 19712 ≤ 19840) (by norm_num : 19840 ≤ 19968), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 19712 ≤ 19840) (by norm_num : 19840 ≤ 19968), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 19712 ≤ 19840) (by norm_num : 19840 ≤ 19968), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 19712 ≤ 19840) (by norm_num : 19840 ≤ 19968), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_19456_19968 :
    (∑ n ∈ Ico 19456 19968, mobiusTreeValue 16 mobiusTable1200001 n) = (-6 : ℤ) ∧
    (∑ n ∈ Ico 19456 19968, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (312 : ℕ) ∧
    (∑ n ∈ Ico 19456 19968, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-1525101 : ℤ) ∧
    (∑ n ∈ Ico 19456 19968, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-30501933643112716266360733759 : ℤ) := by
  rcases cdemPrefixStats_19456_19712 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_19712_19968 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 19456 ≤ 19712) (by norm_num : 19712 ≤ 19968), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 19456 ≤ 19712) (by norm_num : 19712 ≤ 19968), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 19456 ≤ 19712) (by norm_num : 19712 ≤ 19968), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 19456 ≤ 19712) (by norm_num : 19712 ≤ 19968), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_19968_20032 :
    (∑ n ∈ Ico 19968 20032, mobiusTreeValue 16 mobiusTable1200001 n) = (-12 : ℤ) ∧
    (∑ n ∈ Ico 19968 20032, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (42 : ℕ) ∧
    (∑ n ∈ Ico 19968 20032, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-3001786 : ℤ) ∧
    (∑ n ∈ Ico 19968 20032, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-60035798027698656745448020651 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_20032_20096 :
    (∑ n ∈ Ico 20032 20096, mobiusTreeValue 16 mobiusTable1200001 n) = (2 : ℤ) ∧
    (∑ n ∈ Ico 20032 20096, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 20032 20096, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (496805 : ℤ) ∧
    (∑ n ∈ Ico 20032 20096, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (9936080828342655186157667395 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_19968_20096 :
    (∑ n ∈ Ico 19968 20096, mobiusTreeValue 16 mobiusTable1200001 n) = (-10 : ℤ) ∧
    (∑ n ∈ Ico 19968 20096, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (80 : ℕ) ∧
    (∑ n ∈ Ico 19968 20096, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-2504981 : ℤ) ∧
    (∑ n ∈ Ico 19968 20096, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-50099717199356001559290353256 : ℤ) := by
  rcases cdemPrefixStats_19968_20032 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_20032_20096 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 19968 ≤ 20032) (by norm_num : 20032 ≤ 20096), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 19968 ≤ 20032) (by norm_num : 20032 ≤ 20096), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 19968 ≤ 20032) (by norm_num : 20032 ≤ 20096), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 19968 ≤ 20032) (by norm_num : 20032 ≤ 20096), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_20096_20160 :
    (∑ n ∈ Ico 20096 20160, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 20096 20160, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 20096 20160, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-249605 : ℤ) ∧
    (∑ n ∈ Ico 20096 20160, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-4992137537635827417363990028 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_20160_20224 :
    (∑ n ∈ Ico 20160 20224, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 20160 20224, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 20160 20224, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-249060 : ℤ) ∧
    (∑ n ∈ Ico 20160 20224, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-4981191955728795241588709562 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_20096_20224 :
    (∑ n ∈ Ico 20096 20224, mobiusTreeValue 16 mobiusTable1200001 n) = (-2 : ℤ) ∧
    (∑ n ∈ Ico 20096 20224, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (76 : ℕ) ∧
    (∑ n ∈ Ico 20096 20224, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-498665 : ℤ) ∧
    (∑ n ∈ Ico 20096 20224, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-9973329493364622658952699590 : ℤ) := by
  rcases cdemPrefixStats_20096_20160 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_20160_20224 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 20096 ≤ 20160) (by norm_num : 20160 ≤ 20224), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 20096 ≤ 20160) (by norm_num : 20160 ≤ 20224), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 20096 ≤ 20160) (by norm_num : 20160 ≤ 20224), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 20096 ≤ 20160) (by norm_num : 20160 ≤ 20224), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_19968_20224 :
    (∑ n ∈ Ico 19968 20224, mobiusTreeValue 16 mobiusTable1200001 n) = (-12 : ℤ) ∧
    (∑ n ∈ Ico 19968 20224, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (156 : ℕ) ∧
    (∑ n ∈ Ico 19968 20224, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-3003646 : ℤ) ∧
    (∑ n ∈ Ico 19968 20224, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-60073046692720624218243052846 : ℤ) := by
  rcases cdemPrefixStats_19968_20096 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_20096_20224 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 19968 ≤ 20096) (by norm_num : 20096 ≤ 20224), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 19968 ≤ 20096) (by norm_num : 20096 ≤ 20224), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 19968 ≤ 20096) (by norm_num : 20096 ≤ 20224), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 19968 ≤ 20096) (by norm_num : 20096 ≤ 20224), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_20224_20288 :
    (∑ n ∈ Ico 20224 20288, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 20224 20288, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 20224 20288, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (244207 : ℤ) ∧
    (∑ n ∈ Ico 20224 20288, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (4884171600491128378143533492 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_20288_20352 :
    (∑ n ∈ Ico 20288 20352, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 20288 20352, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 20288 20352, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (246852 : ℤ) ∧
    (∑ n ∈ Ico 20288 20352, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (4936991861787645427696222489 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_20224_20352 :
    (∑ n ∈ Ico 20224 20352, mobiusTreeValue 16 mobiusTable1200001 n) = (2 : ℤ) ∧
    (∑ n ∈ Ico 20224 20352, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 20224 20352, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (491059 : ℤ) ∧
    (∑ n ∈ Ico 20224 20352, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (9821163462278773805839755981 : ℤ) := by
  rcases cdemPrefixStats_20224_20288 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_20288_20352 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 20224 ≤ 20288) (by norm_num : 20288 ≤ 20352), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 20224 ≤ 20288) (by norm_num : 20288 ≤ 20352), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 20224 ≤ 20288) (by norm_num : 20288 ≤ 20352), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 20224 ≤ 20288) (by norm_num : 20288 ≤ 20352), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_20352_20416 :
    (∑ n ∈ Ico 20352 20416, mobiusTreeValue 16 mobiusTable1200001 n) = (-3 : ℤ) ∧
    (∑ n ∈ Ico 20352 20416, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 20352 20416, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-736114 : ℤ) ∧
    (∑ n ∈ Ico 20352 20416, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-14722244206859325093505056584 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_20416_20480 :
    (∑ n ∈ Ico 20416 20480, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 20416 20480, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 20416 20480, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (894 : ℤ) ∧
    (∑ n ∈ Ico 20416 20480, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (17956091634050356390975073 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_20352_20480 :
    (∑ n ∈ Ico 20352 20480, mobiusTreeValue 16 mobiusTable1200001 n) = (-3 : ℤ) ∧
    (∑ n ∈ Ico 20352 20480, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (79 : ℕ) ∧
    (∑ n ∈ Ico 20352 20480, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-735220 : ℤ) ∧
    (∑ n ∈ Ico 20352 20480, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-14704288115225274737114081511 : ℤ) := by
  rcases cdemPrefixStats_20352_20416 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_20416_20480 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 20352 ≤ 20416) (by norm_num : 20416 ≤ 20480), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 20352 ≤ 20416) (by norm_num : 20416 ≤ 20480), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 20352 ≤ 20416) (by norm_num : 20416 ≤ 20480), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 20352 ≤ 20416) (by norm_num : 20416 ≤ 20480), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_20224_20480 :
    (∑ n ∈ Ico 20224 20480, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 20224 20480, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (157 : ℕ) ∧
    (∑ n ∈ Ico 20224 20480, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-244161 : ℤ) ∧
    (∑ n ∈ Ico 20224 20480, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-4883124652946500931274325530 : ℤ) := by
  rcases cdemPrefixStats_20224_20352 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_20352_20480 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 20224 ≤ 20352) (by norm_num : 20352 ≤ 20480), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 20224 ≤ 20352) (by norm_num : 20352 ≤ 20480), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 20224 ≤ 20352) (by norm_num : 20352 ≤ 20480), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 20224 ≤ 20352) (by norm_num : 20352 ≤ 20480), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_19968_20480 :
    (∑ n ∈ Ico 19968 20480, mobiusTreeValue 16 mobiusTable1200001 n) = (-13 : ℤ) ∧
    (∑ n ∈ Ico 19968 20480, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (313 : ℕ) ∧
    (∑ n ∈ Ico 19968 20480, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-3247807 : ℤ) ∧
    (∑ n ∈ Ico 19968 20480, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-64956171345667125149517378376 : ℤ) := by
  rcases cdemPrefixStats_19968_20224 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_20224_20480 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 19968 ≤ 20224) (by norm_num : 20224 ≤ 20480), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 19968 ≤ 20224) (by norm_num : 20224 ≤ 20480), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 19968 ≤ 20224) (by norm_num : 20224 ≤ 20480), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 19968 ≤ 20224) (by norm_num : 20224 ≤ 20480), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_19456_20480 :
    (∑ n ∈ Ico 19456 20480, mobiusTreeValue 16 mobiusTable1200001 n) = (-19 : ℤ) ∧
    (∑ n ∈ Ico 19456 20480, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (625 : ℕ) ∧
    (∑ n ∈ Ico 19456 20480, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-4772908 : ℤ) ∧
    (∑ n ∈ Ico 19456 20480, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-95458104988779841415878112135 : ℤ) := by
  rcases cdemPrefixStats_19456_19968 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_19968_20480 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 19456 ≤ 19968) (by norm_num : 19968 ≤ 20480), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 19456 ≤ 19968) (by norm_num : 19968 ≤ 20480), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 19456 ≤ 19968) (by norm_num : 19968 ≤ 20480), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 19456 ≤ 19968) (by norm_num : 19968 ≤ 20480), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_18432_20480 :
    (∑ n ∈ Ico 18432 20480, mobiusTreeValue 16 mobiusTable1200001 n) = (42 : ℤ) ∧
    (∑ n ∈ Ico 18432 20480, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (1242 : ℕ) ∧
    (∑ n ∈ Ico 18432 20480, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (11436658 : ℤ) ∧
    (∑ n ∈ Ico 18432 20480, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (228733576414063988036231671832 : ℤ) := by
  rcases cdemPrefixStats_18432_19456 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_19456_20480 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 18432 ≤ 19456) (by norm_num : 19456 ≤ 20480), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 18432 ≤ 19456) (by norm_num : 19456 ≤ 20480), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 18432 ≤ 19456) (by norm_num : 19456 ≤ 20480), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 18432 ≤ 19456) (by norm_num : 19456 ≤ 20480), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_16384_20480 :
    (∑ n ∈ Ico 16384 20480, mobiusTreeValue 16 mobiusTable1200001 n) = (55 : ℤ) ∧
    (∑ n ∈ Ico 16384 20480, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (2491 : ℕ) ∧
    (∑ n ∈ Ico 16384 20480, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (15458647 : ℤ) ∧
    (∑ n ∈ Ico 16384 20480, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (309173526311773485610560359558 : ℤ) := by
  rcases cdemPrefixStats_16384_18432 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_18432_20480 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 16384 ≤ 18432) (by norm_num : 18432 ≤ 20480), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 16384 ≤ 18432) (by norm_num : 18432 ≤ 20480), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 16384 ≤ 18432) (by norm_num : 18432 ≤ 20480), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 16384 ≤ 18432) (by norm_num : 18432 ≤ 20480), hR1, hR2] <;> norm_num

theorem cdemPrefixGroup004_checked_complete :
    (∑ n ∈ Ico 16384 20480, mobiusTreeValue 16 mobiusTable1200001 n) = (55 : ℤ) ∧
    (∑ n ∈ Ico 16384 20480, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (2491 : ℕ) ∧
    (∑ n ∈ Ico 16384 20480, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (15458647 : ℤ) ∧
    (∑ n ∈ Ico 16384 20480, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (309173526311773485610560359558 : ℤ) := cdemPrefixStats_16384_20480
end Helfgott
#print axioms Helfgott.cdemPrefixGroup004_checked_complete

open Helfgott Finset
open scoped BigOperators

theorem solution :
    (∑ n ∈ Ico 16384 20480, mobiusTreeValue 16 mobiusTable1200001 n) = (55 : ℤ) ∧
    (∑ n ∈ Ico 16384 20480, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (2491 : ℕ) ∧
    (∑ n ∈ Ico 16384 20480, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (15458647 : ℤ) ∧
    (∑ n ∈ Ico 16384 20480, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (309173526311773485610560359558 : ℤ) := Helfgott.cdemPrefixGroup004_checked_complete
#print axioms solution
