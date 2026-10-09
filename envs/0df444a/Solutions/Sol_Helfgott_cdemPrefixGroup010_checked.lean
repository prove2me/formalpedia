-- Prove2me | solution 1 for Helfgott.cdemPrefixGroup010_checked
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-09T01:35:02.531797+00:00
-- url     : https://prove2.me/submissions/0132723b-fe2d-47a8-9b30-eee6a1fb49fc

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
private theorem cdemPrefixStats_40960_41024 :
    (∑ n ∈ Ico 40960 41024, mobiusTreeValue 16 mobiusTable1200001 n) = (-5 : ℤ) ∧
    (∑ n ∈ Ico 40960 41024, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 40960 41024, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-610113 : ℤ) ∧
    (∑ n ∈ Ico 40960 41024, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-12202327453269931322016262990 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_41024_41088 :
    (∑ n ∈ Ico 41024 41088, mobiusTreeValue 16 mobiusTable1200001 n) = (11 : ℤ) ∧
    (∑ n ∈ Ico 41024 41088, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 41024 41088, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (1339488 : ℤ) ∧
    (∑ n ∈ Ico 41024 41088, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (26789834679964143517911689338 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_40960_41088 :
    (∑ n ∈ Ico 40960 41088, mobiusTreeValue 16 mobiusTable1200001 n) = (6 : ℤ) ∧
    (∑ n ∈ Ico 40960 41088, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 40960 41088, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (729375 : ℤ) ∧
    (∑ n ∈ Ico 40960 41088, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (14587507226694212195895426348 : ℤ) := by
  rcases cdemPrefixStats_40960_41024 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_41024_41088 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 40960 ≤ 41024) (by norm_num : 41024 ≤ 41088), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 40960 ≤ 41024) (by norm_num : 41024 ≤ 41088), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 40960 ≤ 41024) (by norm_num : 41024 ≤ 41088), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 40960 ≤ 41024) (by norm_num : 41024 ≤ 41088), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_41088_41152 :
    (∑ n ∈ Ico 41088 41152, mobiusTreeValue 16 mobiusTable1200001 n) = (-2 : ℤ) ∧
    (∑ n ∈ Ico 41088 41152, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 41088 41152, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-242642 : ℤ) ∧
    (∑ n ∈ Ico 41088 41152, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-4852867202744482601153005793 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_41152_41216 :
    (∑ n ∈ Ico 41152 41216, mobiusTreeValue 16 mobiusTable1200001 n) = (6 : ℤ) ∧
    (∑ n ∈ Ico 41152 41216, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 41152 41216, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (728678 : ℤ) ∧
    (∑ n ∈ Ico 41152 41216, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (14573661321126100320095102830 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_41088_41216 :
    (∑ n ∈ Ico 41088 41216, mobiusTreeValue 16 mobiusTable1200001 n) = (4 : ℤ) ∧
    (∑ n ∈ Ico 41088 41216, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (80 : ℕ) ∧
    (∑ n ∈ Ico 41088 41216, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (486036 : ℤ) ∧
    (∑ n ∈ Ico 41088 41216, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (9720794118381617718942097037 : ℤ) := by
  rcases cdemPrefixStats_41088_41152 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_41152_41216 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 41088 ≤ 41152) (by norm_num : 41152 ≤ 41216), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 41088 ≤ 41152) (by norm_num : 41152 ≤ 41216), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 41088 ≤ 41152) (by norm_num : 41152 ≤ 41216), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 41088 ≤ 41152) (by norm_num : 41152 ≤ 41216), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_40960_41216 :
    (∑ n ∈ Ico 40960 41216, mobiusTreeValue 16 mobiusTable1200001 n) = (10 : ℤ) ∧
    (∑ n ∈ Ico 40960 41216, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (158 : ℕ) ∧
    (∑ n ∈ Ico 40960 41216, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (1215411 : ℤ) ∧
    (∑ n ∈ Ico 40960 41216, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (24308301345075829914837523385 : ℤ) := by
  rcases cdemPrefixStats_40960_41088 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_41088_41216 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 40960 ≤ 41088) (by norm_num : 41088 ≤ 41216), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 40960 ≤ 41088) (by norm_num : 41088 ≤ 41216), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 40960 ≤ 41088) (by norm_num : 41088 ≤ 41216), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 40960 ≤ 41088) (by norm_num : 41088 ≤ 41216), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_41216_41280 :
    (∑ n ∈ Ico 41216 41280, mobiusTreeValue 16 mobiusTable1200001 n) = (-15 : ℤ) ∧
    (∑ n ∈ Ico 41216 41280, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 41216 41280, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-1818945 : ℤ) ∧
    (∑ n ∈ Ico 41216 41280, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-36379035898983417626817835314 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_41280_41344 :
    (∑ n ∈ Ico 41280 41344, mobiusTreeValue 16 mobiusTable1200001 n) = (-4 : ℤ) ∧
    (∑ n ∈ Ico 41280 41344, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 41280 41344, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-484195 : ℤ) ∧
    (∑ n ∈ Ico 41280 41344, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-9683944659670415868072001384 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_41216_41344 :
    (∑ n ∈ Ico 41216 41344, mobiusTreeValue 16 mobiusTable1200001 n) = (-19 : ℤ) ∧
    (∑ n ∈ Ico 41216 41344, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (75 : ℕ) ∧
    (∑ n ∈ Ico 41216 41344, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-2303140 : ℤ) ∧
    (∑ n ∈ Ico 41216 41344, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-46062980558653833494889836698 : ℤ) := by
  rcases cdemPrefixStats_41216_41280 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_41280_41344 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 41216 ≤ 41280) (by norm_num : 41280 ≤ 41344), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 41216 ≤ 41280) (by norm_num : 41280 ≤ 41344), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 41216 ≤ 41280) (by norm_num : 41280 ≤ 41344), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 41216 ≤ 41280) (by norm_num : 41280 ≤ 41344), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_41344_41408 :
    (∑ n ∈ Ico 41344 41408, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 41344 41408, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 41344 41408, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (615 : ℤ) ∧
    (∑ n ∈ Ico 41344 41408, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (12328559477847903979469868 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_41408_41472 :
    (∑ n ∈ Ico 41408 41472, mobiusTreeValue 16 mobiusTable1200001 n) = (6 : ℤ) ∧
    (∑ n ∈ Ico 41408 41472, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 41408 41472, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (724320 : ℤ) ∧
    (∑ n ∈ Ico 41408 41472, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (14486393794537319966885219528 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_41344_41472 :
    (∑ n ∈ Ico 41344 41472, mobiusTreeValue 16 mobiusTable1200001 n) = (6 : ℤ) ∧
    (∑ n ∈ Ico 41344 41472, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (80 : ℕ) ∧
    (∑ n ∈ Ico 41344 41472, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (724935 : ℤ) ∧
    (∑ n ∈ Ico 41344 41472, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (14498722354015167870864689396 : ℤ) := by
  rcases cdemPrefixStats_41344_41408 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_41408_41472 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 41344 ≤ 41408) (by norm_num : 41408 ≤ 41472), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 41344 ≤ 41408) (by norm_num : 41408 ≤ 41472), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 41344 ≤ 41408) (by norm_num : 41408 ≤ 41472), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 41344 ≤ 41408) (by norm_num : 41408 ≤ 41472), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_41216_41472 :
    (∑ n ∈ Ico 41216 41472, mobiusTreeValue 16 mobiusTable1200001 n) = (-13 : ℤ) ∧
    (∑ n ∈ Ico 41216 41472, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (155 : ℕ) ∧
    (∑ n ∈ Ico 41216 41472, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-1578205 : ℤ) ∧
    (∑ n ∈ Ico 41216 41472, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-31564258204638665624025147302 : ℤ) := by
  rcases cdemPrefixStats_41216_41344 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_41344_41472 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 41216 ≤ 41344) (by norm_num : 41344 ≤ 41472), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 41216 ≤ 41344) (by norm_num : 41344 ≤ 41472), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 41216 ≤ 41344) (by norm_num : 41344 ≤ 41472), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 41216 ≤ 41344) (by norm_num : 41344 ≤ 41472), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_40960_41472 :
    (∑ n ∈ Ico 40960 41472, mobiusTreeValue 16 mobiusTable1200001 n) = (-3 : ℤ) ∧
    (∑ n ∈ Ico 40960 41472, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (313 : ℕ) ∧
    (∑ n ∈ Ico 40960 41472, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-362794 : ℤ) ∧
    (∑ n ∈ Ico 40960 41472, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-7255956859562835709187623917 : ℤ) := by
  rcases cdemPrefixStats_40960_41216 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_41216_41472 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 40960 ≤ 41216) (by norm_num : 41216 ≤ 41472), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 40960 ≤ 41216) (by norm_num : 41216 ≤ 41472), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 40960 ≤ 41216) (by norm_num : 41216 ≤ 41472), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 40960 ≤ 41216) (by norm_num : 41216 ≤ 41472), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_41472_41536 :
    (∑ n ∈ Ico 41472 41536, mobiusTreeValue 16 mobiusTable1200001 n) = (-2 : ℤ) ∧
    (∑ n ∈ Ico 41472 41536, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 41472 41536, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-240487 : ℤ) ∧
    (∑ n ∈ Ico 41472 41536, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-4809758520681559570560670888 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_41536_41600 :
    (∑ n ∈ Ico 41536 41600, mobiusTreeValue 16 mobiusTable1200001 n) = (-4 : ℤ) ∧
    (∑ n ∈ Ico 41536 41600, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 41536 41600, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-481231 : ℤ) ∧
    (∑ n ∈ Ico 41536 41600, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-9624643598813619453644293263 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_41472_41600 :
    (∑ n ∈ Ico 41472 41600, mobiusTreeValue 16 mobiusTable1200001 n) = (-6 : ℤ) ∧
    (∑ n ∈ Ico 41472 41600, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 41472 41600, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-721718 : ℤ) ∧
    (∑ n ∈ Ico 41472 41600, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-14434402119495179024204964151 : ℤ) := by
  rcases cdemPrefixStats_41472_41536 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_41536_41600 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 41472 ≤ 41536) (by norm_num : 41536 ≤ 41600), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 41472 ≤ 41536) (by norm_num : 41536 ≤ 41600), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 41472 ≤ 41536) (by norm_num : 41536 ≤ 41600), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 41472 ≤ 41536) (by norm_num : 41536 ≤ 41600), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_41600_41664 :
    (∑ n ∈ Ico 41600 41664, mobiusTreeValue 16 mobiusTable1200001 n) = (-5 : ℤ) ∧
    (∑ n ∈ Ico 41600 41664, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 41600 41664, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-600498 : ℤ) ∧
    (∑ n ∈ Ico 41600 41664, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-12009938727274436450224078450 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_41664_41728 :
    (∑ n ∈ Ico 41664 41728, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 41664 41728, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 41664 41728, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-246 : ℤ) ∧
    (∑ n ∈ Ico 41664 41728, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-4949158106951968794316561 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_41600_41728 :
    (∑ n ∈ Ico 41600 41728, mobiusTreeValue 16 mobiusTable1200001 n) = (-5 : ℤ) ∧
    (∑ n ∈ Ico 41600 41728, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (81 : ℕ) ∧
    (∑ n ∈ Ico 41600 41728, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-600744 : ℤ) ∧
    (∑ n ∈ Ico 41600 41728, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-12014887885381388419018395011 : ℤ) := by
  rcases cdemPrefixStats_41600_41664 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_41664_41728 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 41600 ≤ 41664) (by norm_num : 41664 ≤ 41728), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 41600 ≤ 41664) (by norm_num : 41664 ≤ 41728), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 41600 ≤ 41664) (by norm_num : 41664 ≤ 41728), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 41600 ≤ 41664) (by norm_num : 41664 ≤ 41728), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_41472_41728 :
    (∑ n ∈ Ico 41472 41728, mobiusTreeValue 16 mobiusTable1200001 n) = (-11 : ℤ) ∧
    (∑ n ∈ Ico 41472 41728, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (159 : ℕ) ∧
    (∑ n ∈ Ico 41472 41728, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-1322462 : ℤ) ∧
    (∑ n ∈ Ico 41472 41728, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-26449290004876567443223359162 : ℤ) := by
  rcases cdemPrefixStats_41472_41600 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_41600_41728 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 41472 ≤ 41600) (by norm_num : 41600 ≤ 41728), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 41472 ≤ 41600) (by norm_num : 41600 ≤ 41728), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 41472 ≤ 41600) (by norm_num : 41600 ≤ 41728), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 41472 ≤ 41600) (by norm_num : 41600 ≤ 41728), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_41728_41792 :
    (∑ n ∈ Ico 41728 41792, mobiusTreeValue 16 mobiusTable1200001 n) = (-7 : ℤ) ∧
    (∑ n ∈ Ico 41728 41792, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 41728 41792, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-837785 : ℤ) ∧
    (∑ n ∈ Ico 41728 41792, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-16755808115895146636898459461 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_41792_41856 :
    (∑ n ∈ Ico 41792 41856, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 41792 41856, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 41792 41856, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (614 : ℤ) ∧
    (∑ n ∈ Ico 41792 41856, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (12289686691262563101094790 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_41728_41856 :
    (∑ n ∈ Ico 41728 41856, mobiusTreeValue 16 mobiusTable1200001 n) = (-7 : ℤ) ∧
    (∑ n ∈ Ico 41728 41856, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 41728 41856, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-837171 : ℤ) ∧
    (∑ n ∈ Ico 41728 41856, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-16743518429203884073797364671 : ℤ) := by
  rcases cdemPrefixStats_41728_41792 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_41792_41856 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 41728 ≤ 41792) (by norm_num : 41792 ≤ 41856), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 41728 ≤ 41792) (by norm_num : 41792 ≤ 41856), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 41728 ≤ 41792) (by norm_num : 41792 ≤ 41856), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 41728 ≤ 41792) (by norm_num : 41792 ≤ 41856), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_41856_41920 :
    (∑ n ∈ Ico 41856 41920, mobiusTreeValue 16 mobiusTable1200001 n) = (-2 : ℤ) ∧
    (∑ n ∈ Ico 41856 41920, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 41856 41920, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-238258 : ℤ) ∧
    (∑ n ∈ Ico 41856 41920, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-4765176417437266817361146883 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_41920_41984 :
    (∑ n ∈ Ico 41920 41984, mobiusTreeValue 16 mobiusTable1200001 n) = (-9 : ℤ) ∧
    (∑ n ∈ Ico 41920 41984, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 41920 41984, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-1072237 : ℤ) ∧
    (∑ n ∈ Ico 41920 41984, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-21444799232643789039610427324 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_41856_41984 :
    (∑ n ∈ Ico 41856 41984, mobiusTreeValue 16 mobiusTable1200001 n) = (-11 : ℤ) ∧
    (∑ n ∈ Ico 41856 41984, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (79 : ℕ) ∧
    (∑ n ∈ Ico 41856 41984, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-1310495 : ℤ) ∧
    (∑ n ∈ Ico 41856 41984, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-26209975650081055856971574207 : ℤ) := by
  rcases cdemPrefixStats_41856_41920 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_41920_41984 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 41856 ≤ 41920) (by norm_num : 41920 ≤ 41984), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 41856 ≤ 41920) (by norm_num : 41920 ≤ 41984), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 41856 ≤ 41920) (by norm_num : 41920 ≤ 41984), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 41856 ≤ 41920) (by norm_num : 41920 ≤ 41984), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_41728_41984 :
    (∑ n ∈ Ico 41728 41984, mobiusTreeValue 16 mobiusTable1200001 n) = (-18 : ℤ) ∧
    (∑ n ∈ Ico 41728 41984, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (156 : ℕ) ∧
    (∑ n ∈ Ico 41728 41984, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-2147666 : ℤ) ∧
    (∑ n ∈ Ico 41728 41984, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-42953494079284939930768938878 : ℤ) := by
  rcases cdemPrefixStats_41728_41856 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_41856_41984 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 41728 ≤ 41856) (by norm_num : 41856 ≤ 41984), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 41728 ≤ 41856) (by norm_num : 41856 ≤ 41984), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 41728 ≤ 41856) (by norm_num : 41856 ≤ 41984), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 41728 ≤ 41856) (by norm_num : 41856 ≤ 41984), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_41472_41984 :
    (∑ n ∈ Ico 41472 41984, mobiusTreeValue 16 mobiusTable1200001 n) = (-29 : ℤ) ∧
    (∑ n ∈ Ico 41472 41984, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (315 : ℕ) ∧
    (∑ n ∈ Ico 41472 41984, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-3470128 : ℤ) ∧
    (∑ n ∈ Ico 41472 41984, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-69402784084161507373992298040 : ℤ) := by
  rcases cdemPrefixStats_41472_41728 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_41728_41984 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 41472 ≤ 41728) (by norm_num : 41728 ≤ 41984), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 41472 ≤ 41728) (by norm_num : 41728 ≤ 41984), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 41472 ≤ 41728) (by norm_num : 41728 ≤ 41984), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 41472 ≤ 41728) (by norm_num : 41728 ≤ 41984), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_40960_41984 :
    (∑ n ∈ Ico 40960 41984, mobiusTreeValue 16 mobiusTable1200001 n) = (-32 : ℤ) ∧
    (∑ n ∈ Ico 40960 41984, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (628 : ℕ) ∧
    (∑ n ∈ Ico 40960 41984, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-3832922 : ℤ) ∧
    (∑ n ∈ Ico 40960 41984, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-76658740943724343083179921957 : ℤ) := by
  rcases cdemPrefixStats_40960_41472 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_41472_41984 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 40960 ≤ 41472) (by norm_num : 41472 ≤ 41984), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 40960 ≤ 41472) (by norm_num : 41472 ≤ 41984), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 40960 ≤ 41472) (by norm_num : 41472 ≤ 41984), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 40960 ≤ 41472) (by norm_num : 41472 ≤ 41984), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_41984_42048 :
    (∑ n ∈ Ico 41984 42048, mobiusTreeValue 16 mobiusTable1200001 n) = (2 : ℤ) ∧
    (∑ n ∈ Ico 41984 42048, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 41984 42048, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (237680 : ℤ) ∧
    (∑ n ∈ Ico 41984 42048, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (4753580084039896362147736917 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_42048_42112 :
    (∑ n ∈ Ico 42048 42112, mobiusTreeValue 16 mobiusTable1200001 n) = (-9 : ℤ) ∧
    (∑ n ∈ Ico 42048 42112, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 42048 42112, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-1069400 : ℤ) ∧
    (∑ n ∈ Ico 42048 42112, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-21388059367773228582966515461 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_41984_42112 :
    (∑ n ∈ Ico 41984 42112, mobiusTreeValue 16 mobiusTable1200001 n) = (-7 : ℤ) ∧
    (∑ n ∈ Ico 41984 42112, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 41984 42112, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-831720 : ℤ) ∧
    (∑ n ∈ Ico 41984 42112, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-16634479283733332220818778544 : ℤ) := by
  rcases cdemPrefixStats_41984_42048 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_42048_42112 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 41984 ≤ 42048) (by norm_num : 42048 ≤ 42112), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 41984 ≤ 42048) (by norm_num : 42048 ≤ 42112), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 41984 ≤ 42048) (by norm_num : 42048 ≤ 42112), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 41984 ≤ 42048) (by norm_num : 42048 ≤ 42112), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_42112_42176 :
    (∑ n ∈ Ico 42112 42176, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 42112 42176, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 42112 42176, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-118571 : ℤ) ∧
    (∑ n ∈ Ico 42112 42176, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-2371464580418608132878378868 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_42176_42240 :
    (∑ n ∈ Ico 42176 42240, mobiusTreeValue 16 mobiusTable1200001 n) = (-2 : ℤ) ∧
    (∑ n ∈ Ico 42176 42240, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 42176 42240, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-236796 : ℤ) ∧
    (∑ n ∈ Ico 42176 42240, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-4735914211101957065420069996 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_42112_42240 :
    (∑ n ∈ Ico 42112 42240, mobiusTreeValue 16 mobiusTable1200001 n) = (-3 : ℤ) ∧
    (∑ n ∈ Ico 42112 42240, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 42112 42240, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-355367 : ℤ) ∧
    (∑ n ∈ Ico 42112 42240, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-7107378791520565198298448864 : ℤ) := by
  rcases cdemPrefixStats_42112_42176 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_42176_42240 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 42112 ≤ 42176) (by norm_num : 42176 ≤ 42240), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 42112 ≤ 42176) (by norm_num : 42176 ≤ 42240), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 42112 ≤ 42176) (by norm_num : 42176 ≤ 42240), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 42112 ≤ 42176) (by norm_num : 42176 ≤ 42240), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_41984_42240 :
    (∑ n ∈ Ico 41984 42240, mobiusTreeValue 16 mobiusTable1200001 n) = (-10 : ℤ) ∧
    (∑ n ∈ Ico 41984 42240, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (154 : ℕ) ∧
    (∑ n ∈ Ico 41984 42240, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-1187087 : ℤ) ∧
    (∑ n ∈ Ico 41984 42240, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-23741858075253897419117227408 : ℤ) := by
  rcases cdemPrefixStats_41984_42112 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_42112_42240 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 41984 ≤ 42112) (by norm_num : 42112 ≤ 42240), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 41984 ≤ 42112) (by norm_num : 42112 ≤ 42240), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 41984 ≤ 42112) (by norm_num : 42112 ≤ 42240), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 41984 ≤ 42112) (by norm_num : 42112 ≤ 42240), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_42240_42304 :
    (∑ n ∈ Ico 42240 42304, mobiusTreeValue 16 mobiusTable1200001 n) = (-2 : ℤ) ∧
    (∑ n ∈ Ico 42240 42304, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 42240 42304, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-235862 : ℤ) ∧
    (∑ n ∈ Ico 42240 42304, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-4717217609541880233721180196 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_42304_42368 :
    (∑ n ∈ Ico 42304 42368, mobiusTreeValue 16 mobiusTable1200001 n) = (-6 : ℤ) ∧
    (∑ n ∈ Ico 42304 42368, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 42304 42368, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-708370 : ℤ) ∧
    (∑ n ∈ Ico 42304 42368, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-14167480549101563745865017080 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_42240_42368 :
    (∑ n ∈ Ico 42240 42368, mobiusTreeValue 16 mobiusTable1200001 n) = (-8 : ℤ) ∧
    (∑ n ∈ Ico 42240 42368, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (80 : ℕ) ∧
    (∑ n ∈ Ico 42240 42368, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-944232 : ℤ) ∧
    (∑ n ∈ Ico 42240 42368, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-18884698158643443979586197276 : ℤ) := by
  rcases cdemPrefixStats_42240_42304 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_42304_42368 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 42240 ≤ 42304) (by norm_num : 42304 ≤ 42368), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 42240 ≤ 42304) (by norm_num : 42304 ≤ 42368), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 42240 ≤ 42304) (by norm_num : 42304 ≤ 42368), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 42240 ≤ 42304) (by norm_num : 42304 ≤ 42368), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_42368_42432 :
    (∑ n ∈ Ico 42368 42432, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 42368 42432, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 42368 42432, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-117732 : ℤ) ∧
    (∑ n ∈ Ico 42368 42432, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-2354649159427707007171834613 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_42432_42496 :
    (∑ n ∈ Ico 42432 42496, mobiusTreeValue 16 mobiusTable1200001 n) = (-4 : ℤ) ∧
    (∑ n ∈ Ico 42432 42496, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 42432 42496, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-471155 : ℤ) ∧
    (∑ n ∈ Ico 42432 42496, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-9423127901755388301505780901 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_42368_42496 :
    (∑ n ∈ Ico 42368 42496, mobiusTreeValue 16 mobiusTable1200001 n) = (-5 : ℤ) ∧
    (∑ n ∈ Ico 42368 42496, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 42368 42496, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-588887 : ℤ) ∧
    (∑ n ∈ Ico 42368 42496, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-11777777061183095308677615514 : ℤ) := by
  rcases cdemPrefixStats_42368_42432 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_42432_42496 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 42368 ≤ 42432) (by norm_num : 42432 ≤ 42496), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 42368 ≤ 42432) (by norm_num : 42432 ≤ 42496), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 42368 ≤ 42432) (by norm_num : 42432 ≤ 42496), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 42368 ≤ 42432) (by norm_num : 42432 ≤ 42496), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_42240_42496 :
    (∑ n ∈ Ico 42240 42496, mobiusTreeValue 16 mobiusTable1200001 n) = (-13 : ℤ) ∧
    (∑ n ∈ Ico 42240 42496, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (157 : ℕ) ∧
    (∑ n ∈ Ico 42240 42496, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-1533119 : ℤ) ∧
    (∑ n ∈ Ico 42240 42496, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-30662475219826539288263812790 : ℤ) := by
  rcases cdemPrefixStats_42240_42368 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_42368_42496 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 42240 ≤ 42368) (by norm_num : 42368 ≤ 42496), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 42240 ≤ 42368) (by norm_num : 42368 ≤ 42496), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 42240 ≤ 42368) (by norm_num : 42368 ≤ 42496), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 42240 ≤ 42368) (by norm_num : 42368 ≤ 42496), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_41984_42496 :
    (∑ n ∈ Ico 41984 42496, mobiusTreeValue 16 mobiusTable1200001 n) = (-23 : ℤ) ∧
    (∑ n ∈ Ico 41984 42496, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (311 : ℕ) ∧
    (∑ n ∈ Ico 41984 42496, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-2720206 : ℤ) ∧
    (∑ n ∈ Ico 41984 42496, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-54404333295080436707381040198 : ℤ) := by
  rcases cdemPrefixStats_41984_42240 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_42240_42496 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 41984 ≤ 42240) (by norm_num : 42240 ≤ 42496), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 41984 ≤ 42240) (by norm_num : 42240 ≤ 42496), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 41984 ≤ 42240) (by norm_num : 42240 ≤ 42496), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 41984 ≤ 42240) (by norm_num : 42240 ≤ 42496), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_42496_42560 :
    (∑ n ∈ Ico 42496 42560, mobiusTreeValue 16 mobiusTable1200001 n) = (-7 : ℤ) ∧
    (∑ n ∈ Ico 42496 42560, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 42496 42560, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-823374 : ℤ) ∧
    (∑ n ∈ Ico 42496 42560, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-16467489513761059480638031933 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_42560_42624 :
    (∑ n ∈ Ico 42560 42624, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 42560 42624, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 42560 42624, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-117607 : ℤ) ∧
    (∑ n ∈ Ico 42560 42624, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-2352159412703971712867245035 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_42496_42624 :
    (∑ n ∈ Ico 42496 42624, mobiusTreeValue 16 mobiusTable1200001 n) = (-8 : ℤ) ∧
    (∑ n ∈ Ico 42496 42624, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (80 : ℕ) ∧
    (∑ n ∈ Ico 42496 42624, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-940981 : ℤ) ∧
    (∑ n ∈ Ico 42496 42624, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-18819648926465031193505276968 : ℤ) := by
  rcases cdemPrefixStats_42496_42560 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_42560_42624 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 42496 ≤ 42560) (by norm_num : 42560 ≤ 42624), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 42496 ≤ 42560) (by norm_num : 42560 ≤ 42624), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 42496 ≤ 42560) (by norm_num : 42560 ≤ 42624), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 42496 ≤ 42560) (by norm_num : 42560 ≤ 42624), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_42624_42688 :
    (∑ n ∈ Ico 42624 42688, mobiusTreeValue 16 mobiusTable1200001 n) = (3 : ℤ) ∧
    (∑ n ∈ Ico 42624 42688, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 42624 42688, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (351883 : ℤ) ∧
    (∑ n ∈ Ico 42624 42688, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (7037681911863292361099695544 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_42688_42752 :
    (∑ n ∈ Ico 42688 42752, mobiusTreeValue 16 mobiusTable1200001 n) = (-9 : ℤ) ∧
    (∑ n ∈ Ico 42688 42752, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 42688 42752, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-1053227 : ℤ) ∧
    (∑ n ∈ Ico 42688 42752, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-21064621760762201151863946177 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_42624_42752 :
    (∑ n ∈ Ico 42624 42752, mobiusTreeValue 16 mobiusTable1200001 n) = (-6 : ℤ) ∧
    (∑ n ∈ Ico 42624 42752, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 42624 42752, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-701344 : ℤ) ∧
    (∑ n ∈ Ico 42624 42752, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-14026939848898908790764250633 : ℤ) := by
  rcases cdemPrefixStats_42624_42688 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_42688_42752 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 42624 ≤ 42688) (by norm_num : 42688 ≤ 42752), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 42624 ≤ 42688) (by norm_num : 42688 ≤ 42752), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 42624 ≤ 42688) (by norm_num : 42688 ≤ 42752), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 42624 ≤ 42688) (by norm_num : 42688 ≤ 42752), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_42496_42752 :
    (∑ n ∈ Ico 42496 42752, mobiusTreeValue 16 mobiusTable1200001 n) = (-14 : ℤ) ∧
    (∑ n ∈ Ico 42496 42752, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (158 : ℕ) ∧
    (∑ n ∈ Ico 42496 42752, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-1642325 : ℤ) ∧
    (∑ n ∈ Ico 42496 42752, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-32846588775363939984269527601 : ℤ) := by
  rcases cdemPrefixStats_42496_42624 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_42624_42752 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 42496 ≤ 42624) (by norm_num : 42624 ≤ 42752), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 42496 ≤ 42624) (by norm_num : 42624 ≤ 42752), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 42496 ≤ 42624) (by norm_num : 42624 ≤ 42752), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 42496 ≤ 42624) (by norm_num : 42624 ≤ 42752), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_42752_42816 :
    (∑ n ∈ Ico 42752 42816, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 42752 42816, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 42752 42816, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-117067 : ℤ) ∧
    (∑ n ∈ Ico 42752 42816, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-2341361825174106577792351476 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_42816_42880 :
    (∑ n ∈ Ico 42816 42880, mobiusTreeValue 16 mobiusTable1200001 n) = (-2 : ℤ) ∧
    (∑ n ∈ Ico 42816 42880, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 42816 42880, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-234020 : ℤ) ∧
    (∑ n ∈ Ico 42816 42880, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-4680462716243777788784239334 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_42752_42880 :
    (∑ n ∈ Ico 42752 42880, mobiusTreeValue 16 mobiusTable1200001 n) = (-3 : ℤ) ∧
    (∑ n ∈ Ico 42752 42880, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (79 : ℕ) ∧
    (∑ n ∈ Ico 42752 42880, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-351087 : ℤ) ∧
    (∑ n ∈ Ico 42752 42880, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-7021824541417884366576590810 : ℤ) := by
  rcases cdemPrefixStats_42752_42816 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_42816_42880 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 42752 ≤ 42816) (by norm_num : 42816 ≤ 42880), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 42752 ≤ 42816) (by norm_num : 42816 ≤ 42880), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 42752 ≤ 42816) (by norm_num : 42816 ≤ 42880), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 42752 ≤ 42816) (by norm_num : 42816 ≤ 42880), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_42880_42944 :
    (∑ n ∈ Ico 42880 42944, mobiusTreeValue 16 mobiusTable1200001 n) = (-7 : ℤ) ∧
    (∑ n ∈ Ico 42880 42944, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 42880 42944, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-815621 : ℤ) ∧
    (∑ n ∈ Ico 42880 42944, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-16312455943518879733307315772 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_42944_43008 :
    (∑ n ∈ Ico 42944 43008, mobiusTreeValue 16 mobiusTable1200001 n) = (9 : ℤ) ∧
    (∑ n ∈ Ico 42944 43008, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 42944 43008, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (1046568 : ℤ) ∧
    (∑ n ∈ Ico 42944 43008, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (20931421092888302665968889108 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_42880_43008 :
    (∑ n ∈ Ico 42880 43008, mobiusTreeValue 16 mobiusTable1200001 n) = (2 : ℤ) ∧
    (∑ n ∈ Ico 42880 43008, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 42880 43008, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (230947 : ℤ) ∧
    (∑ n ∈ Ico 42880 43008, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (4618965149369422932661573336 : ℤ) := by
  rcases cdemPrefixStats_42880_42944 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_42944_43008 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 42880 ≤ 42944) (by norm_num : 42944 ≤ 43008), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 42880 ≤ 42944) (by norm_num : 42944 ≤ 43008), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 42880 ≤ 42944) (by norm_num : 42944 ≤ 43008), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 42880 ≤ 42944) (by norm_num : 42944 ≤ 43008), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_42752_43008 :
    (∑ n ∈ Ico 42752 43008, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 42752 43008, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (157 : ℕ) ∧
    (∑ n ∈ Ico 42752 43008, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-120140 : ℤ) ∧
    (∑ n ∈ Ico 42752 43008, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-2402859392048461433915017474 : ℤ) := by
  rcases cdemPrefixStats_42752_42880 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_42880_43008 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 42752 ≤ 42880) (by norm_num : 42880 ≤ 43008), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 42752 ≤ 42880) (by norm_num : 42880 ≤ 43008), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 42752 ≤ 42880) (by norm_num : 42880 ≤ 43008), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 42752 ≤ 42880) (by norm_num : 42880 ≤ 43008), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_42496_43008 :
    (∑ n ∈ Ico 42496 43008, mobiusTreeValue 16 mobiusTable1200001 n) = (-15 : ℤ) ∧
    (∑ n ∈ Ico 42496 43008, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (315 : ℕ) ∧
    (∑ n ∈ Ico 42496 43008, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-1762465 : ℤ) ∧
    (∑ n ∈ Ico 42496 43008, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-35249448167412401418184545075 : ℤ) := by
  rcases cdemPrefixStats_42496_42752 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_42752_43008 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 42496 ≤ 42752) (by norm_num : 42752 ≤ 43008), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 42496 ≤ 42752) (by norm_num : 42752 ≤ 43008), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 42496 ≤ 42752) (by norm_num : 42752 ≤ 43008), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 42496 ≤ 42752) (by norm_num : 42752 ≤ 43008), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_41984_43008 :
    (∑ n ∈ Ico 41984 43008, mobiusTreeValue 16 mobiusTable1200001 n) = (-38 : ℤ) ∧
    (∑ n ∈ Ico 41984 43008, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (626 : ℕ) ∧
    (∑ n ∈ Ico 41984 43008, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-4482671 : ℤ) ∧
    (∑ n ∈ Ico 41984 43008, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-89653781462492838125565585273 : ℤ) := by
  rcases cdemPrefixStats_41984_42496 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_42496_43008 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 41984 ≤ 42496) (by norm_num : 42496 ≤ 43008), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 41984 ≤ 42496) (by norm_num : 42496 ≤ 43008), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 41984 ≤ 42496) (by norm_num : 42496 ≤ 43008), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 41984 ≤ 42496) (by norm_num : 42496 ≤ 43008), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_40960_43008 :
    (∑ n ∈ Ico 40960 43008, mobiusTreeValue 16 mobiusTable1200001 n) = (-70 : ℤ) ∧
    (∑ n ∈ Ico 40960 43008, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (1254 : ℕ) ∧
    (∑ n ∈ Ico 40960 43008, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-8315593 : ℤ) ∧
    (∑ n ∈ Ico 40960 43008, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-166312522406217181208745507230 : ℤ) := by
  rcases cdemPrefixStats_40960_41984 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_41984_43008 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 40960 ≤ 41984) (by norm_num : 41984 ≤ 43008), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 40960 ≤ 41984) (by norm_num : 41984 ≤ 43008), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 40960 ≤ 41984) (by norm_num : 41984 ≤ 43008), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 40960 ≤ 41984) (by norm_num : 41984 ≤ 43008), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_43008_43072 :
    (∑ n ∈ Ico 43008 43072, mobiusTreeValue 16 mobiusTable1200001 n) = (6 : ℤ) ∧
    (∑ n ∈ Ico 43008 43072, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 43008 43072, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (697151 : ℤ) ∧
    (∑ n ∈ Ico 43008 43072, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (13943055727330801045434081195 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_43072_43136 :
    (∑ n ∈ Ico 43072 43136, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 43072 43136, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 43072 43136, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (308 : ℤ) ∧
    (∑ n ∈ Ico 43072 43136, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (6136148652754630732336993 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_43008_43136 :
    (∑ n ∈ Ico 43008 43136, mobiusTreeValue 16 mobiusTable1200001 n) = (6 : ℤ) ∧
    (∑ n ∈ Ico 43008 43136, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 43008 43136, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (697459 : ℤ) ∧
    (∑ n ∈ Ico 43008 43136, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (13949191875983555676166418188 : ℤ) := by
  rcases cdemPrefixStats_43008_43072 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_43072_43136 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 43008 ≤ 43072) (by norm_num : 43072 ≤ 43136), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 43008 ≤ 43072) (by norm_num : 43072 ≤ 43136), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 43008 ≤ 43072) (by norm_num : 43072 ≤ 43136), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 43008 ≤ 43072) (by norm_num : 43072 ≤ 43136), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_43136_43200 :
    (∑ n ∈ Ico 43136 43200, mobiusTreeValue 16 mobiusTable1200001 n) = (10 : ℤ) ∧
    (∑ n ∈ Ico 43136 43200, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 43136 43200, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (1158297 : ℤ) ∧
    (∑ n ∈ Ico 43136 43200, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (23166012704082098823692437405 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_43200_43264 :
    (∑ n ∈ Ico 43200 43264, mobiusTreeValue 16 mobiusTable1200001 n) = (12 : ℤ) ∧
    (∑ n ∈ Ico 43200 43264, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 43200 43264, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (1388568 : ℤ) ∧
    (∑ n ∈ Ico 43200 43264, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (27771505103455678937631197147 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_43136_43264 :
    (∑ n ∈ Ico 43136 43264, mobiusTreeValue 16 mobiusTable1200001 n) = (22 : ℤ) ∧
    (∑ n ∈ Ico 43136 43264, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 43136 43264, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (2546865 : ℤ) ∧
    (∑ n ∈ Ico 43136 43264, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (50937517807537777761323634552 : ℤ) := by
  rcases cdemPrefixStats_43136_43200 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_43200_43264 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 43136 ≤ 43200) (by norm_num : 43200 ≤ 43264), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 43136 ≤ 43200) (by norm_num : 43200 ≤ 43264), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 43136 ≤ 43200) (by norm_num : 43200 ≤ 43264), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 43136 ≤ 43200) (by norm_num : 43200 ≤ 43264), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_43008_43264 :
    (∑ n ∈ Ico 43008 43264, mobiusTreeValue 16 mobiusTable1200001 n) = (28 : ℤ) ∧
    (∑ n ∈ Ico 43008 43264, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (156 : ℕ) ∧
    (∑ n ∈ Ico 43008 43264, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (3244324 : ℤ) ∧
    (∑ n ∈ Ico 43008 43264, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (64886709683521333437490052740 : ℤ) := by
  rcases cdemPrefixStats_43008_43136 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_43136_43264 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 43008 ≤ 43136) (by norm_num : 43136 ≤ 43264), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 43008 ≤ 43136) (by norm_num : 43136 ≤ 43264), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 43008 ≤ 43136) (by norm_num : 43136 ≤ 43264), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 43008 ≤ 43136) (by norm_num : 43136 ≤ 43264), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_43264_43328 :
    (∑ n ∈ Ico 43264 43328, mobiusTreeValue 16 mobiusTable1200001 n) = (-3 : ℤ) ∧
    (∑ n ∈ Ico 43264 43328, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 43264 43328, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-346472 : ℤ) ∧
    (∑ n ∈ Ico 43264 43328, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-6929475572457615655961751008 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_43328_43392 :
    (∑ n ∈ Ico 43328 43392, mobiusTreeValue 16 mobiusTable1200001 n) = (11 : ℤ) ∧
    (∑ n ∈ Ico 43328 43392, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 43328 43392, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (1268721 : ℤ) ∧
    (∑ n ∈ Ico 43328 43392, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (25374538189093578663002440074 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_43264_43392 :
    (∑ n ∈ Ico 43264 43392, mobiusTreeValue 16 mobiusTable1200001 n) = (8 : ℤ) ∧
    (∑ n ∈ Ico 43264 43392, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 43264 43392, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (922249 : ℤ) ∧
    (∑ n ∈ Ico 43264 43392, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (18445062616635963007040689066 : ℤ) := by
  rcases cdemPrefixStats_43264_43328 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_43328_43392 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 43264 ≤ 43328) (by norm_num : 43328 ≤ 43392), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 43264 ≤ 43328) (by norm_num : 43328 ≤ 43392), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 43264 ≤ 43328) (by norm_num : 43328 ≤ 43392), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 43264 ≤ 43328) (by norm_num : 43328 ≤ 43392), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_43392_43456 :
    (∑ n ∈ Ico 43392 43456, mobiusTreeValue 16 mobiusTable1200001 n) = (3 : ℤ) ∧
    (∑ n ∈ Ico 43392 43456, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 43392 43456, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (345272 : ℤ) ∧
    (∑ n ∈ Ico 43392 43456, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (6905494541285735850212523826 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_43456_43520 :
    (∑ n ∈ Ico 43456 43520, mobiusTreeValue 16 mobiusTable1200001 n) = (8 : ℤ) ∧
    (∑ n ∈ Ico 43456 43520, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 43456 43520, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (919411 : ℤ) ∧
    (∑ n ∈ Ico 43456 43520, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (18388267972536844449915620361 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_43392_43520 :
    (∑ n ∈ Ico 43392 43520, mobiusTreeValue 16 mobiusTable1200001 n) = (11 : ℤ) ∧
    (∑ n ∈ Ico 43392 43520, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (79 : ℕ) ∧
    (∑ n ∈ Ico 43392 43520, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (1264683 : ℤ) ∧
    (∑ n ∈ Ico 43392 43520, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (25293762513822580300128144187 : ℤ) := by
  rcases cdemPrefixStats_43392_43456 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_43456_43520 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 43392 ≤ 43456) (by norm_num : 43456 ≤ 43520), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 43392 ≤ 43456) (by norm_num : 43456 ≤ 43520), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 43392 ≤ 43456) (by norm_num : 43456 ≤ 43520), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 43392 ≤ 43456) (by norm_num : 43456 ≤ 43520), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_43264_43520 :
    (∑ n ∈ Ico 43264 43520, mobiusTreeValue 16 mobiusTable1200001 n) = (19 : ℤ) ∧
    (∑ n ∈ Ico 43264 43520, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (157 : ℕ) ∧
    (∑ n ∈ Ico 43264 43520, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (2186932 : ℤ) ∧
    (∑ n ∈ Ico 43264 43520, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (43738825130458543307168833253 : ℤ) := by
  rcases cdemPrefixStats_43264_43392 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_43392_43520 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 43264 ≤ 43392) (by norm_num : 43392 ≤ 43520), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 43264 ≤ 43392) (by norm_num : 43392 ≤ 43520), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 43264 ≤ 43392) (by norm_num : 43392 ≤ 43520), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 43264 ≤ 43392) (by norm_num : 43392 ≤ 43520), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_43008_43520 :
    (∑ n ∈ Ico 43008 43520, mobiusTreeValue 16 mobiusTable1200001 n) = (47 : ℤ) ∧
    (∑ n ∈ Ico 43008 43520, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (313 : ℕ) ∧
    (∑ n ∈ Ico 43008 43520, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (5431256 : ℤ) ∧
    (∑ n ∈ Ico 43008 43520, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (108625534813979876744658885993 : ℤ) := by
  rcases cdemPrefixStats_43008_43264 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_43264_43520 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 43008 ≤ 43264) (by norm_num : 43264 ≤ 43520), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 43008 ≤ 43264) (by norm_num : 43264 ≤ 43520), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 43008 ≤ 43264) (by norm_num : 43264 ≤ 43520), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 43008 ≤ 43264) (by norm_num : 43264 ≤ 43520), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_43520_43584 :
    (∑ n ∈ Ico 43520 43584, mobiusTreeValue 16 mobiusTable1200001 n) = (-7 : ℤ) ∧
    (∑ n ∈ Ico 43520 43584, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 43520 43584, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-803781 : ℤ) ∧
    (∑ n ∈ Ico 43520 43584, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-16075696256952880939862177026 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_43584_43648 :
    (∑ n ∈ Ico 43584 43648, mobiusTreeValue 16 mobiusTable1200001 n) = (5 : ℤ) ∧
    (∑ n ∈ Ico 43584 43648, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 43584 43648, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (572914 : ℤ) ∧
    (∑ n ∈ Ico 43584 43648, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (11458323625535372385494960654 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_43520_43648 :
    (∑ n ∈ Ico 43520 43648, mobiusTreeValue 16 mobiusTable1200001 n) = (-2 : ℤ) ∧
    (∑ n ∈ Ico 43520 43648, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 43520 43648, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-230867 : ℤ) ∧
    (∑ n ∈ Ico 43520 43648, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-4617372631417508554367216372 : ℤ) := by
  rcases cdemPrefixStats_43520_43584 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_43584_43648 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 43520 ≤ 43584) (by norm_num : 43584 ≤ 43648), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 43520 ≤ 43584) (by norm_num : 43584 ≤ 43648), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 43520 ≤ 43584) (by norm_num : 43584 ≤ 43648), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 43520 ≤ 43584) (by norm_num : 43584 ≤ 43648), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_43648_43712 :
    (∑ n ∈ Ico 43648 43712, mobiusTreeValue 16 mobiusTable1200001 n) = (9 : ℤ) ∧
    (∑ n ∈ Ico 43648 43712, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 43648 43712, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (1030427 : ℤ) ∧
    (∑ n ∈ Ico 43648 43712, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (20608588078860962410763160011 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_43712_43776 :
    (∑ n ∈ Ico 43712 43776, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 43712 43776, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 43712 43776, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-114196 : ℤ) ∧
    (∑ n ∈ Ico 43712 43776, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-2283938048416753878594430027 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_43648_43776 :
    (∑ n ∈ Ico 43648 43776, mobiusTreeValue 16 mobiusTable1200001 n) = (8 : ℤ) ∧
    (∑ n ∈ Ico 43648 43776, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (76 : ℕ) ∧
    (∑ n ∈ Ico 43648 43776, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (916231 : ℤ) ∧
    (∑ n ∈ Ico 43648 43776, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (18324650030444208532168729984 : ℤ) := by
  rcases cdemPrefixStats_43648_43712 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_43712_43776 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 43648 ≤ 43712) (by norm_num : 43712 ≤ 43776), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 43648 ≤ 43712) (by norm_num : 43712 ≤ 43776), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 43648 ≤ 43712) (by norm_num : 43712 ≤ 43776), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 43648 ≤ 43712) (by norm_num : 43712 ≤ 43776), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_43520_43776 :
    (∑ n ∈ Ico 43520 43776, mobiusTreeValue 16 mobiusTable1200001 n) = (6 : ℤ) ∧
    (∑ n ∈ Ico 43520 43776, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (154 : ℕ) ∧
    (∑ n ∈ Ico 43520 43776, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (685364 : ℤ) ∧
    (∑ n ∈ Ico 43520 43776, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (13707277399026699977801513612 : ℤ) := by
  rcases cdemPrefixStats_43520_43648 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_43648_43776 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 43520 ≤ 43648) (by norm_num : 43648 ≤ 43776), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 43520 ≤ 43648) (by norm_num : 43648 ≤ 43776), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 43520 ≤ 43648) (by norm_num : 43648 ≤ 43776), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 43520 ≤ 43648) (by norm_num : 43648 ≤ 43776), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_43776_43840 :
    (∑ n ∈ Ico 43776 43840, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 43776 43840, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 43776 43840, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-114523 : ℤ) ∧
    (∑ n ∈ Ico 43776 43840, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-2290454167968320578277206965 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_43840_43904 :
    (∑ n ∈ Ico 43840 43904, mobiusTreeValue 16 mobiusTable1200001 n) = (9 : ℤ) ∧
    (∑ n ∈ Ico 43840 43904, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 43840 43904, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (1025756 : ℤ) ∧
    (∑ n ∈ Ico 43840 43904, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (20515161350538608336647873091 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_43776_43904 :
    (∑ n ∈ Ico 43776 43904, mobiusTreeValue 16 mobiusTable1200001 n) = (8 : ℤ) ∧
    (∑ n ∈ Ico 43776 43904, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (80 : ℕ) ∧
    (∑ n ∈ Ico 43776 43904, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (911233 : ℤ) ∧
    (∑ n ∈ Ico 43776 43904, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (18224707182570287758370666126 : ℤ) := by
  rcases cdemPrefixStats_43776_43840 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_43840_43904 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 43776 ≤ 43840) (by norm_num : 43840 ≤ 43904), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 43776 ≤ 43840) (by norm_num : 43840 ≤ 43904), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 43776 ≤ 43840) (by norm_num : 43840 ≤ 43904), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 43776 ≤ 43840) (by norm_num : 43840 ≤ 43904), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_43904_43968 :
    (∑ n ∈ Ico 43904 43968, mobiusTreeValue 16 mobiusTable1200001 n) = (2 : ℤ) ∧
    (∑ n ∈ Ico 43904 43968, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 43904 43968, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (227597 : ℤ) ∧
    (∑ n ∈ Ico 43904 43968, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (4551970886719867903259297593 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_43968_44032 :
    (∑ n ∈ Ico 43968 44032, mobiusTreeValue 16 mobiusTable1200001 n) = (-12 : ℤ) ∧
    (∑ n ∈ Ico 43968 44032, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 43968 44032, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-1363587 : ℤ) ∧
    (∑ n ∈ Ico 43968 44032, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-27271859011373153532002087883 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_43904_44032 :
    (∑ n ∈ Ico 43904 44032, mobiusTreeValue 16 mobiusTable1200001 n) = (-10 : ℤ) ∧
    (∑ n ∈ Ico 43904 44032, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 43904 44032, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-1135990 : ℤ) ∧
    (∑ n ∈ Ico 43904 44032, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-22719888124653285628742790290 : ℤ) := by
  rcases cdemPrefixStats_43904_43968 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_43968_44032 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 43904 ≤ 43968) (by norm_num : 43968 ≤ 44032), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 43904 ≤ 43968) (by norm_num : 43968 ≤ 44032), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 43904 ≤ 43968) (by norm_num : 43968 ≤ 44032), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 43904 ≤ 43968) (by norm_num : 43968 ≤ 44032), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_43776_44032 :
    (∑ n ∈ Ico 43776 44032, mobiusTreeValue 16 mobiusTable1200001 n) = (-2 : ℤ) ∧
    (∑ n ∈ Ico 43776 44032, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (158 : ℕ) ∧
    (∑ n ∈ Ico 43776 44032, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-224757 : ℤ) ∧
    (∑ n ∈ Ico 43776 44032, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-4495180942082997870372124164 : ℤ) := by
  rcases cdemPrefixStats_43776_43904 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_43904_44032 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 43776 ≤ 43904) (by norm_num : 43904 ≤ 44032), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 43776 ≤ 43904) (by norm_num : 43904 ≤ 44032), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 43776 ≤ 43904) (by norm_num : 43904 ≤ 44032), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 43776 ≤ 43904) (by norm_num : 43904 ≤ 44032), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_43520_44032 :
    (∑ n ∈ Ico 43520 44032, mobiusTreeValue 16 mobiusTable1200001 n) = (4 : ℤ) ∧
    (∑ n ∈ Ico 43520 44032, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (312 : ℕ) ∧
    (∑ n ∈ Ico 43520 44032, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (460607 : ℤ) ∧
    (∑ n ∈ Ico 43520 44032, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (9212096456943702107429389448 : ℤ) := by
  rcases cdemPrefixStats_43520_43776 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_43776_44032 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 43520 ≤ 43776) (by norm_num : 43776 ≤ 44032), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 43520 ≤ 43776) (by norm_num : 43776 ≤ 44032), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 43520 ≤ 43776) (by norm_num : 43776 ≤ 44032), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 43520 ≤ 43776) (by norm_num : 43776 ≤ 44032), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_43008_44032 :
    (∑ n ∈ Ico 43008 44032, mobiusTreeValue 16 mobiusTable1200001 n) = (51 : ℤ) ∧
    (∑ n ∈ Ico 43008 44032, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (625 : ℕ) ∧
    (∑ n ∈ Ico 43008 44032, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (5891863 : ℤ) ∧
    (∑ n ∈ Ico 43008 44032, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (117837631270923578852088275441 : ℤ) := by
  rcases cdemPrefixStats_43008_43520 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_43520_44032 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 43008 ≤ 43520) (by norm_num : 43520 ≤ 44032), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 43008 ≤ 43520) (by norm_num : 43520 ≤ 44032), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 43008 ≤ 43520) (by norm_num : 43520 ≤ 44032), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 43008 ≤ 43520) (by norm_num : 43520 ≤ 44032), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_44032_44096 :
    (∑ n ∈ Ico 44032 44096, mobiusTreeValue 16 mobiusTable1200001 n) = (2 : ℤ) ∧
    (∑ n ∈ Ico 44032 44096, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 44032 44096, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (227105 : ℤ) ∧
    (∑ n ∈ Ico 44032 44096, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (4542150872835579209251350258 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_44096_44160 :
    (∑ n ∈ Ico 44096 44160, mobiusTreeValue 16 mobiusTable1200001 n) = (8 : ℤ) ∧
    (∑ n ∈ Ico 44096 44160, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 44096 44160, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (906161 : ℤ) ∧
    (∑ n ∈ Ico 44096 44160, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (18123381035346971490990744413 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_44032_44160 :
    (∑ n ∈ Ico 44032 44160, mobiusTreeValue 16 mobiusTable1200001 n) = (10 : ℤ) ∧
    (∑ n ∈ Ico 44032 44160, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 44032 44160, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (1133266 : ℤ) ∧
    (∑ n ∈ Ico 44032 44160, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (22665531908182550700242094671 : ℤ) := by
  rcases cdemPrefixStats_44032_44096 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_44096_44160 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 44032 ≤ 44096) (by norm_num : 44096 ≤ 44160), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 44032 ≤ 44096) (by norm_num : 44096 ≤ 44160), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 44032 ≤ 44096) (by norm_num : 44096 ≤ 44160), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 44032 ≤ 44096) (by norm_num : 44096 ≤ 44160), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_44160_44224 :
    (∑ n ∈ Ico 44160 44224, mobiusTreeValue 16 mobiusTable1200001 n) = (5 : ℤ) ∧
    (∑ n ∈ Ico 44160 44224, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 44160 44224, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (565750 : ℤ) ∧
    (∑ n ∈ Ico 44160 44224, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (11314983736994857683127819020 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_44224_44288 :
    (∑ n ∈ Ico 44224 44288, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 44224 44288, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 44224 44288, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-112808 : ℤ) ∧
    (∑ n ∈ Ico 44224 44288, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-2256213273841283633053079462 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_44160_44288 :
    (∑ n ∈ Ico 44160 44288, mobiusTreeValue 16 mobiusTable1200001 n) = (4 : ℤ) ∧
    (∑ n ∈ Ico 44160 44288, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (76 : ℕ) ∧
    (∑ n ∈ Ico 44160 44288, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (452942 : ℤ) ∧
    (∑ n ∈ Ico 44160 44288, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (9058770463153574050074739558 : ℤ) := by
  rcases cdemPrefixStats_44160_44224 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_44224_44288 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 44160 ≤ 44224) (by norm_num : 44224 ≤ 44288), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 44160 ≤ 44224) (by norm_num : 44224 ≤ 44288), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 44160 ≤ 44224) (by norm_num : 44224 ≤ 44288), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 44160 ≤ 44224) (by norm_num : 44224 ≤ 44288), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_44032_44288 :
    (∑ n ∈ Ico 44032 44288, mobiusTreeValue 16 mobiusTable1200001 n) = (14 : ℤ) ∧
    (∑ n ∈ Ico 44032 44288, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (154 : ℕ) ∧
    (∑ n ∈ Ico 44032 44288, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (1586208 : ℤ) ∧
    (∑ n ∈ Ico 44032 44288, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (31724302371336124750316834229 : ℤ) := by
  rcases cdemPrefixStats_44032_44160 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_44160_44288 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 44032 ≤ 44160) (by norm_num : 44160 ≤ 44288), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 44032 ≤ 44160) (by norm_num : 44160 ≤ 44288), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 44032 ≤ 44160) (by norm_num : 44160 ≤ 44288), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 44032 ≤ 44160) (by norm_num : 44160 ≤ 44288), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_44288_44352 :
    (∑ n ∈ Ico 44288 44352, mobiusTreeValue 16 mobiusTable1200001 n) = (16 : ℤ) ∧
    (∑ n ∈ Ico 44288 44352, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 44288 44352, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (1805201 : ℤ) ∧
    (∑ n ∈ Ico 44288 44352, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (36104194177235931384680644361 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_44352_44416 :
    (∑ n ∈ Ico 44352 44416, mobiusTreeValue 16 mobiusTable1200001 n) = (-7 : ℤ) ∧
    (∑ n ∈ Ico 44352 44416, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 44352 44416, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-788922 : ℤ) ∧
    (∑ n ∈ Ico 44352 44416, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-15778510125434933703724159655 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_44288_44416 :
    (∑ n ∈ Ico 44288 44416, mobiusTreeValue 16 mobiusTable1200001 n) = (9 : ℤ) ∧
    (∑ n ∈ Ico 44288 44416, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 44288 44416, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (1016279 : ℤ) ∧
    (∑ n ∈ Ico 44288 44416, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (20325684051800997680956484706 : ℤ) := by
  rcases cdemPrefixStats_44288_44352 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_44352_44416 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 44288 ≤ 44352) (by norm_num : 44352 ≤ 44416), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 44288 ≤ 44352) (by norm_num : 44352 ≤ 44416), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 44288 ≤ 44352) (by norm_num : 44352 ≤ 44416), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 44288 ≤ 44352) (by norm_num : 44352 ≤ 44416), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_44416_44480 :
    (∑ n ∈ Ico 44416 44480, mobiusTreeValue 16 mobiusTable1200001 n) = (8 : ℤ) ∧
    (∑ n ∈ Ico 44416 44480, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 44416 44480, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (899913 : ℤ) ∧
    (∑ n ∈ Ico 44416 44480, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (17998412789404002211292286227 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_44480_44544 :
    (∑ n ∈ Ico 44480 44544, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 44480 44544, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 44480 44544, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (92 : ℤ) ∧
    (∑ n ∈ Ico 44480 44544, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1919074844221608612427807 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_44416_44544 :
    (∑ n ∈ Ico 44416 44544, mobiusTreeValue 16 mobiusTable1200001 n) = (8 : ℤ) ∧
    (∑ n ∈ Ico 44416 44544, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 44416 44544, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (900005 : ℤ) ∧
    (∑ n ∈ Ico 44416 44544, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (18000331864248223819904714034 : ℤ) := by
  rcases cdemPrefixStats_44416_44480 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_44480_44544 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 44416 ≤ 44480) (by norm_num : 44480 ≤ 44544), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 44416 ≤ 44480) (by norm_num : 44480 ≤ 44544), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 44416 ≤ 44480) (by norm_num : 44480 ≤ 44544), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 44416 ≤ 44480) (by norm_num : 44480 ≤ 44544), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_44288_44544 :
    (∑ n ∈ Ico 44288 44544, mobiusTreeValue 16 mobiusTable1200001 n) = (17 : ℤ) ∧
    (∑ n ∈ Ico 44288 44544, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (155 : ℕ) ∧
    (∑ n ∈ Ico 44288 44544, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (1916284 : ℤ) ∧
    (∑ n ∈ Ico 44288 44544, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (38326015916049221500861198740 : ℤ) := by
  rcases cdemPrefixStats_44288_44416 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_44416_44544 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 44288 ≤ 44416) (by norm_num : 44416 ≤ 44544), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 44288 ≤ 44416) (by norm_num : 44416 ≤ 44544), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 44288 ≤ 44416) (by norm_num : 44416 ≤ 44544), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 44288 ≤ 44416) (by norm_num : 44416 ≤ 44544), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_44032_44544 :
    (∑ n ∈ Ico 44032 44544, mobiusTreeValue 16 mobiusTable1200001 n) = (31 : ℤ) ∧
    (∑ n ∈ Ico 44032 44544, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (309 : ℕ) ∧
    (∑ n ∈ Ico 44032 44544, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (3502492 : ℤ) ∧
    (∑ n ∈ Ico 44032 44544, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (70050318287385346251178032969 : ℤ) := by
  rcases cdemPrefixStats_44032_44288 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_44288_44544 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 44032 ≤ 44288) (by norm_num : 44288 ≤ 44544), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 44032 ≤ 44288) (by norm_num : 44288 ≤ 44544), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 44032 ≤ 44288) (by norm_num : 44288 ≤ 44544), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 44032 ≤ 44288) (by norm_num : 44288 ≤ 44544), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_44544_44608 :
    (∑ n ∈ Ico 44544 44608, mobiusTreeValue 16 mobiusTable1200001 n) = (-2 : ℤ) ∧
    (∑ n ∈ Ico 44544 44608, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 44544 44608, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-224107 : ℤ) ∧
    (∑ n ∈ Ico 44544 44608, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-4482140165064350938921474854 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_44608_44672 :
    (∑ n ∈ Ico 44608 44672, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 44608 44672, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 44608 44672, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-111965 : ℤ) ∧
    (∑ n ∈ Ico 44608 44672, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-2239337629756848448887848928 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_44544_44672 :
    (∑ n ∈ Ico 44544 44672, mobiusTreeValue 16 mobiusTable1200001 n) = (-3 : ℤ) ∧
    (∑ n ∈ Ico 44544 44672, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (79 : ℕ) ∧
    (∑ n ∈ Ico 44544 44672, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-336072 : ℤ) ∧
    (∑ n ∈ Ico 44544 44672, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-6721477794821199387809323782 : ℤ) := by
  rcases cdemPrefixStats_44544_44608 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_44608_44672 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 44544 ≤ 44608) (by norm_num : 44608 ≤ 44672), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 44544 ≤ 44608) (by norm_num : 44608 ≤ 44672), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 44544 ≤ 44608) (by norm_num : 44608 ≤ 44672), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 44544 ≤ 44608) (by norm_num : 44608 ≤ 44672), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_44672_44736 :
    (∑ n ∈ Ico 44672 44736, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 44672 44736, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 44672 44736, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-112176 : ℤ) ∧
    (∑ n ∈ Ico 44672 44736, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-2243490876632405077692621040 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_44736_44800 :
    (∑ n ∈ Ico 44736 44800, mobiusTreeValue 16 mobiusTable1200001 n) = (3 : ℤ) ∧
    (∑ n ∈ Ico 44736 44800, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 44736 44800, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (335053 : ℤ) ∧
    (∑ n ∈ Ico 44736 44800, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (6701065539718042389421554366 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_44672_44800 :
    (∑ n ∈ Ico 44672 44800, mobiusTreeValue 16 mobiusTable1200001 n) = (2 : ℤ) ∧
    (∑ n ∈ Ico 44672 44800, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 44672 44800, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (222877 : ℤ) ∧
    (∑ n ∈ Ico 44672 44800, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (4457574663085637311728933326 : ℤ) := by
  rcases cdemPrefixStats_44672_44736 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_44736_44800 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 44672 ≤ 44736) (by norm_num : 44736 ≤ 44800), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 44672 ≤ 44736) (by norm_num : 44736 ≤ 44800), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 44672 ≤ 44736) (by norm_num : 44736 ≤ 44800), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 44672 ≤ 44736) (by norm_num : 44736 ≤ 44800), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_44544_44800 :
    (∑ n ∈ Ico 44544 44800, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 44544 44800, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (157 : ℕ) ∧
    (∑ n ∈ Ico 44544 44800, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-113195 : ℤ) ∧
    (∑ n ∈ Ico 44544 44800, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-2263903131735562076080390456 : ℤ) := by
  rcases cdemPrefixStats_44544_44672 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_44672_44800 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 44544 ≤ 44672) (by norm_num : 44672 ≤ 44800), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 44544 ≤ 44672) (by norm_num : 44672 ≤ 44800), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 44544 ≤ 44672) (by norm_num : 44672 ≤ 44800), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 44544 ≤ 44672) (by norm_num : 44672 ≤ 44800), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_44800_44864 :
    (∑ n ∈ Ico 44800 44864, mobiusTreeValue 16 mobiusTable1200001 n) = (-2 : ℤ) ∧
    (∑ n ∈ Ico 44800 44864, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 44800 44864, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-222972 : ℤ) ∧
    (∑ n ∈ Ico 44800 44864, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-4459456998689834810929366652 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_44864_44928 :
    (∑ n ∈ Ico 44864 44928, mobiusTreeValue 16 mobiusTable1200001 n) = (-2 : ℤ) ∧
    (∑ n ∈ Ico 44864 44928, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 44864 44928, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-222386 : ℤ) ∧
    (∑ n ∈ Ico 44864 44928, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-4447745773186448826597723627 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_44800_44928 :
    (∑ n ∈ Ico 44800 44928, mobiusTreeValue 16 mobiusTable1200001 n) = (-4 : ℤ) ∧
    (∑ n ∈ Ico 44800 44928, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 44800 44928, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-445358 : ℤ) ∧
    (∑ n ∈ Ico 44800 44928, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-8907202771876283637527090279 : ℤ) := by
  rcases cdemPrefixStats_44800_44864 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_44864_44928 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 44800 ≤ 44864) (by norm_num : 44864 ≤ 44928), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 44800 ≤ 44864) (by norm_num : 44864 ≤ 44928), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 44800 ≤ 44864) (by norm_num : 44864 ≤ 44928), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 44800 ≤ 44864) (by norm_num : 44864 ≤ 44928), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_44928_44992 :
    (∑ n ∈ Ico 44928 44992, mobiusTreeValue 16 mobiusTable1200001 n) = (-3 : ℤ) ∧
    (∑ n ∈ Ico 44928 44992, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 44928 44992, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-333687 : ℤ) ∧
    (∑ n ∈ Ico 44928 44992, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-6673736960615116214461548722 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_44992_45056 :
    (∑ n ∈ Ico 44992 45056, mobiusTreeValue 16 mobiusTable1200001 n) = (4 : ℤ) ∧
    (∑ n ∈ Ico 44992 45056, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 44992 45056, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (444006 : ℤ) ∧
    (∑ n ∈ Ico 44992 45056, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (8880158175377312887883849970 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_44928_45056 :
    (∑ n ∈ Ico 44928 45056, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 44928 45056, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 44928 45056, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (110319 : ℤ) ∧
    (∑ n ∈ Ico 44928 45056, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (2206421214762196673422301248 : ℤ) := by
  rcases cdemPrefixStats_44928_44992 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_44992_45056 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 44928 ≤ 44992) (by norm_num : 44992 ≤ 45056), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 44928 ≤ 44992) (by norm_num : 44992 ≤ 45056), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 44928 ≤ 44992) (by norm_num : 44992 ≤ 45056), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 44928 ≤ 44992) (by norm_num : 44992 ≤ 45056), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_44800_45056 :
    (∑ n ∈ Ico 44800 45056, mobiusTreeValue 16 mobiusTable1200001 n) = (-3 : ℤ) ∧
    (∑ n ∈ Ico 44800 45056, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (155 : ℕ) ∧
    (∑ n ∈ Ico 44800 45056, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-335039 : ℤ) ∧
    (∑ n ∈ Ico 44800 45056, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-6700781557114086964104789031 : ℤ) := by
  rcases cdemPrefixStats_44800_44928 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_44928_45056 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 44800 ≤ 44928) (by norm_num : 44928 ≤ 45056), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 44800 ≤ 44928) (by norm_num : 44928 ≤ 45056), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 44800 ≤ 44928) (by norm_num : 44928 ≤ 45056), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 44800 ≤ 44928) (by norm_num : 44928 ≤ 45056), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_44544_45056 :
    (∑ n ∈ Ico 44544 45056, mobiusTreeValue 16 mobiusTable1200001 n) = (-4 : ℤ) ∧
    (∑ n ∈ Ico 44544 45056, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (312 : ℕ) ∧
    (∑ n ∈ Ico 44544 45056, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-448234 : ℤ) ∧
    (∑ n ∈ Ico 44544 45056, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-8964684688849649040185179487 : ℤ) := by
  rcases cdemPrefixStats_44544_44800 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_44800_45056 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 44544 ≤ 44800) (by norm_num : 44800 ≤ 45056), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 44544 ≤ 44800) (by norm_num : 44800 ≤ 45056), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 44544 ≤ 44800) (by norm_num : 44800 ≤ 45056), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 44544 ≤ 44800) (by norm_num : 44800 ≤ 45056), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_44032_45056 :
    (∑ n ∈ Ico 44032 45056, mobiusTreeValue 16 mobiusTable1200001 n) = (27 : ℤ) ∧
    (∑ n ∈ Ico 44032 45056, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (621 : ℕ) ∧
    (∑ n ∈ Ico 44032 45056, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (3054258 : ℤ) ∧
    (∑ n ∈ Ico 44032 45056, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (61085633598535697210992853482 : ℤ) := by
  rcases cdemPrefixStats_44032_44544 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_44544_45056 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 44032 ≤ 44544) (by norm_num : 44544 ≤ 45056), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 44032 ≤ 44544) (by norm_num : 44544 ≤ 45056), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 44032 ≤ 44544) (by norm_num : 44544 ≤ 45056), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 44032 ≤ 44544) (by norm_num : 44544 ≤ 45056), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_43008_45056 :
    (∑ n ∈ Ico 43008 45056, mobiusTreeValue 16 mobiusTable1200001 n) = (78 : ℤ) ∧
    (∑ n ∈ Ico 43008 45056, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (1246 : ℕ) ∧
    (∑ n ∈ Ico 43008 45056, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (8946121 : ℤ) ∧
    (∑ n ∈ Ico 43008 45056, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (178923264869459276063081128923 : ℤ) := by
  rcases cdemPrefixStats_43008_44032 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_44032_45056 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 43008 ≤ 44032) (by norm_num : 44032 ≤ 45056), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 43008 ≤ 44032) (by norm_num : 44032 ≤ 45056), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 43008 ≤ 44032) (by norm_num : 44032 ≤ 45056), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 43008 ≤ 44032) (by norm_num : 44032 ≤ 45056), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_40960_45056 :
    (∑ n ∈ Ico 40960 45056, mobiusTreeValue 16 mobiusTable1200001 n) = (8 : ℤ) ∧
    (∑ n ∈ Ico 40960 45056, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (2500 : ℕ) ∧
    (∑ n ∈ Ico 40960 45056, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (630528 : ℤ) ∧
    (∑ n ∈ Ico 40960 45056, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (12610742463242094854335621693 : ℤ) := by
  rcases cdemPrefixStats_40960_43008 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_43008_45056 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 40960 ≤ 43008) (by norm_num : 43008 ≤ 45056), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 40960 ≤ 43008) (by norm_num : 43008 ≤ 45056), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 40960 ≤ 43008) (by norm_num : 43008 ≤ 45056), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 40960 ≤ 43008) (by norm_num : 43008 ≤ 45056), hR1, hR2] <;> norm_num

theorem cdemPrefixGroup010_checked_complete :
    (∑ n ∈ Ico 40960 45056, mobiusTreeValue 16 mobiusTable1200001 n) = (8 : ℤ) ∧
    (∑ n ∈ Ico 40960 45056, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (2500 : ℕ) ∧
    (∑ n ∈ Ico 40960 45056, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (630528 : ℤ) ∧
    (∑ n ∈ Ico 40960 45056, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (12610742463242094854335621693 : ℤ) := cdemPrefixStats_40960_45056
end Helfgott
#print axioms Helfgott.cdemPrefixGroup010_checked_complete

open Helfgott Finset
open scoped BigOperators

theorem solution :
    (∑ n ∈ Ico 40960 45056, mobiusTreeValue 16 mobiusTable1200001 n) = (8 : ℤ) ∧
    (∑ n ∈ Ico 40960 45056, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (2500 : ℕ) ∧
    (∑ n ∈ Ico 40960 45056, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (630528 : ℤ) ∧
    (∑ n ∈ Ico 40960 45056, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (12610742463242094854335621693 : ℤ) := Helfgott.cdemPrefixGroup010_checked_complete
#print axioms solution
