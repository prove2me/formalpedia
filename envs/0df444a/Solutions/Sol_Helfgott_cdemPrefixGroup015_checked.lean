-- Prove2me | solution 1 for Helfgott.cdemPrefixGroup015_checked
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-09T01:44:45.321579+00:00
-- url     : https://prove2.me/submissions/e6bdd8b6-f255-4ed9-bf19-fa2818b71397

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
private theorem cdemPrefixStats_61440_61504 :
    (∑ n ∈ Ico 61440 61504, mobiusTreeValue 16 mobiusTable1200001 n) = (-9 : ℤ) ∧
    (∑ n ∈ Ico 61440 61504, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 61440 61504, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-732069 : ℤ) ∧
    (∑ n ∈ Ico 61440 61504, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-14641446484923070487951621161 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_61504_61568 :
    (∑ n ∈ Ico 61504 61568, mobiusTreeValue 16 mobiusTable1200001 n) = (-6 : ℤ) ∧
    (∑ n ∈ Ico 61504 61568, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 61504 61568, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-487329 : ℤ) ∧
    (∑ n ∈ Ico 61504 61568, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-9746666971209321817053443562 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_61440_61568 :
    (∑ n ∈ Ico 61440 61568, mobiusTreeValue 16 mobiusTable1200001 n) = (-15 : ℤ) ∧
    (∑ n ∈ Ico 61440 61568, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (79 : ℕ) ∧
    (∑ n ∈ Ico 61440 61568, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-1219398 : ℤ) ∧
    (∑ n ∈ Ico 61440 61568, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-24388113456132392305005064723 : ℤ) := by
  rcases cdemPrefixStats_61440_61504 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_61504_61568 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 61440 ≤ 61504) (by norm_num : 61504 ≤ 61568), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 61440 ≤ 61504) (by norm_num : 61504 ≤ 61568), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 61440 ≤ 61504) (by norm_num : 61504 ≤ 61568), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 61440 ≤ 61504) (by norm_num : 61504 ≤ 61568), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_61568_61632 :
    (∑ n ∈ Ico 61568 61632, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 61568 61632, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 61568 61632, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (99 : ℤ) ∧
    (∑ n ∈ Ico 61568 61632, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1949952104051335379870008 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_61632_61696 :
    (∑ n ∈ Ico 61632 61696, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 61632 61696, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 61632 61696, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (44 : ℤ) ∧
    (∑ n ∈ Ico 61632 61696, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (867514374710018036479418 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_61568_61696 :
    (∑ n ∈ Ico 61568 61696, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 61568 61696, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (76 : ℕ) ∧
    (∑ n ∈ Ico 61568 61696, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (143 : ℤ) ∧
    (∑ n ∈ Ico 61568 61696, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (2817466478761353416349426 : ℤ) := by
  rcases cdemPrefixStats_61568_61632 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_61632_61696 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 61568 ≤ 61632) (by norm_num : 61632 ≤ 61696), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 61568 ≤ 61632) (by norm_num : 61632 ≤ 61696), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 61568 ≤ 61632) (by norm_num : 61632 ≤ 61696), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 61568 ≤ 61632) (by norm_num : 61632 ≤ 61696), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_61440_61696 :
    (∑ n ∈ Ico 61440 61696, mobiusTreeValue 16 mobiusTable1200001 n) = (-15 : ℤ) ∧
    (∑ n ∈ Ico 61440 61696, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (155 : ℕ) ∧
    (∑ n ∈ Ico 61440 61696, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-1219255 : ℤ) ∧
    (∑ n ∈ Ico 61440 61696, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-24385295989653630951588715297 : ℤ) := by
  rcases cdemPrefixStats_61440_61568 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_61568_61696 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 61440 ≤ 61568) (by norm_num : 61568 ≤ 61696), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 61440 ≤ 61568) (by norm_num : 61568 ≤ 61696), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 61440 ≤ 61568) (by norm_num : 61568 ≤ 61696), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 61440 ≤ 61568) (by norm_num : 61568 ≤ 61696), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_61696_61760 :
    (∑ n ∈ Ico 61696 61760, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 61696 61760, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 61696 61760, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-204 : ℤ) ∧
    (∑ n ∈ Ico 61696 61760, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-4093560016763391259624087 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_61760_61824 :
    (∑ n ∈ Ico 61760 61824, mobiusTreeValue 16 mobiusTable1200001 n) = (6 : ℤ) ∧
    (∑ n ∈ Ico 61760 61824, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 61760 61824, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (485554 : ℤ) ∧
    (∑ n ∈ Ico 61760 61824, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (9711148347009699507088587760 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_61696_61824 :
    (∑ n ∈ Ico 61696 61824, mobiusTreeValue 16 mobiusTable1200001 n) = (6 : ℤ) ∧
    (∑ n ∈ Ico 61696 61824, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (80 : ℕ) ∧
    (∑ n ∈ Ico 61696 61824, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (485350 : ℤ) ∧
    (∑ n ∈ Ico 61696 61824, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (9707054786992936115828963673 : ℤ) := by
  rcases cdemPrefixStats_61696_61760 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_61760_61824 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 61696 ≤ 61760) (by norm_num : 61760 ≤ 61824), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 61696 ≤ 61760) (by norm_num : 61760 ≤ 61824), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 61696 ≤ 61760) (by norm_num : 61760 ≤ 61824), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 61696 ≤ 61760) (by norm_num : 61760 ≤ 61824), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_61824_61888 :
    (∑ n ∈ Ico 61824 61888, mobiusTreeValue 16 mobiusTable1200001 n) = (2 : ℤ) ∧
    (∑ n ∈ Ico 61824 61888, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (36 : ℕ) ∧
    (∑ n ∈ Ico 61824 61888, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (161362 : ℤ) ∧
    (∑ n ∈ Ico 61824 61888, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (3227253338785443194691863002 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_61888_61952 :
    (∑ n ∈ Ico 61888 61952, mobiusTreeValue 16 mobiusTable1200001 n) = (2 : ℤ) ∧
    (∑ n ∈ Ico 61888 61952, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 61888 61952, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (161614 : ℤ) ∧
    (∑ n ∈ Ico 61888 61952, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (3232243923340539581658555698 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_61824_61952 :
    (∑ n ∈ Ico 61824 61952, mobiusTreeValue 16 mobiusTable1200001 n) = (4 : ℤ) ∧
    (∑ n ∈ Ico 61824 61952, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (76 : ℕ) ∧
    (∑ n ∈ Ico 61824 61952, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (322976 : ℤ) ∧
    (∑ n ∈ Ico 61824 61952, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (6459497262125982776350418700 : ℤ) := by
  rcases cdemPrefixStats_61824_61888 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_61888_61952 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 61824 ≤ 61888) (by norm_num : 61888 ≤ 61952), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 61824 ≤ 61888) (by norm_num : 61888 ≤ 61952), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 61824 ≤ 61888) (by norm_num : 61888 ≤ 61952), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 61824 ≤ 61888) (by norm_num : 61888 ≤ 61952), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_61696_61952 :
    (∑ n ∈ Ico 61696 61952, mobiusTreeValue 16 mobiusTable1200001 n) = (10 : ℤ) ∧
    (∑ n ∈ Ico 61696 61952, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (156 : ℕ) ∧
    (∑ n ∈ Ico 61696 61952, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (808326 : ℤ) ∧
    (∑ n ∈ Ico 61696 61952, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (16166552049118918892179382373 : ℤ) := by
  rcases cdemPrefixStats_61696_61824 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_61824_61952 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 61696 ≤ 61824) (by norm_num : 61824 ≤ 61952), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 61696 ≤ 61824) (by norm_num : 61824 ≤ 61952), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 61696 ≤ 61824) (by norm_num : 61824 ≤ 61952), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 61696 ≤ 61824) (by norm_num : 61824 ≤ 61952), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_61440_61952 :
    (∑ n ∈ Ico 61440 61952, mobiusTreeValue 16 mobiusTable1200001 n) = (-5 : ℤ) ∧
    (∑ n ∈ Ico 61440 61952, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (311 : ℕ) ∧
    (∑ n ∈ Ico 61440 61952, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-410929 : ℤ) ∧
    (∑ n ∈ Ico 61440 61952, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-8218743940534712059409332924 : ℤ) := by
  rcases cdemPrefixStats_61440_61696 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_61696_61952 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 61440 ≤ 61696) (by norm_num : 61696 ≤ 61952), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 61440 ≤ 61696) (by norm_num : 61696 ≤ 61952), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 61440 ≤ 61696) (by norm_num : 61696 ≤ 61952), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 61440 ≤ 61696) (by norm_num : 61696 ≤ 61952), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_61952_62016 :
    (∑ n ∈ Ico 61952 62016, mobiusTreeValue 16 mobiusTable1200001 n) = (-15 : ℤ) ∧
    (∑ n ∈ Ico 61952 62016, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 61952 62016, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-1209828 : ℤ) ∧
    (∑ n ∈ Ico 61952 62016, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-24196698401205473472146964231 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_62016_62080 :
    (∑ n ∈ Ico 62016 62080, mobiusTreeValue 16 mobiusTable1200001 n) = (4 : ℤ) ∧
    (∑ n ∈ Ico 62016 62080, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 62016 62080, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (322193 : ℤ) ∧
    (∑ n ∈ Ico 62016 62080, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (6443947286489268076617988397 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_61952_62080 :
    (∑ n ∈ Ico 61952 62080, mobiusTreeValue 16 mobiusTable1200001 n) = (-11 : ℤ) ∧
    (∑ n ∈ Ico 61952 62080, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (79 : ℕ) ∧
    (∑ n ∈ Ico 61952 62080, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-887635 : ℤ) ∧
    (∑ n ∈ Ico 61952 62080, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-17752751114716205395528975834 : ℤ) := by
  rcases cdemPrefixStats_61952_62016 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_62016_62080 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 61952 ≤ 62016) (by norm_num : 62016 ≤ 62080), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 61952 ≤ 62016) (by norm_num : 62016 ≤ 62080), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 61952 ≤ 62016) (by norm_num : 62016 ≤ 62080), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 61952 ≤ 62016) (by norm_num : 62016 ≤ 62080), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_62080_62144 :
    (∑ n ∈ Ico 62080 62144, mobiusTreeValue 16 mobiusTable1200001 n) = (-8 : ℤ) ∧
    (∑ n ∈ Ico 62080 62144, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 62080 62144, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-643830 : ℤ) ∧
    (∑ n ∈ Ico 62080 62144, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-12876694720845399900804189142 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_62144_62208 :
    (∑ n ∈ Ico 62144 62208, mobiusTreeValue 16 mobiusTable1200001 n) = (8 : ℤ) ∧
    (∑ n ∈ Ico 62144 62208, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 62144 62208, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (643647 : ℤ) ∧
    (∑ n ∈ Ico 62144 62208, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (12873064774834936425312036515 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_62080_62208 :
    (∑ n ∈ Ico 62080 62208, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 62080 62208, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 62080 62208, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-183 : ℤ) ∧
    (∑ n ∈ Ico 62080 62208, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-3629946010463475492152627 : ℤ) := by
  rcases cdemPrefixStats_62080_62144 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_62144_62208 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 62080 ≤ 62144) (by norm_num : 62144 ≤ 62208), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 62080 ≤ 62144) (by norm_num : 62144 ≤ 62208), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 62080 ≤ 62144) (by norm_num : 62144 ≤ 62208), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 62080 ≤ 62144) (by norm_num : 62144 ≤ 62208), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_61952_62208 :
    (∑ n ∈ Ico 61952 62208, mobiusTreeValue 16 mobiusTable1200001 n) = (-11 : ℤ) ∧
    (∑ n ∈ Ico 61952 62208, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (157 : ℕ) ∧
    (∑ n ∈ Ico 61952 62208, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-887818 : ℤ) ∧
    (∑ n ∈ Ico 61952 62208, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-17756381060726668871021128461 : ℤ) := by
  rcases cdemPrefixStats_61952_62080 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_62080_62208 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 61952 ≤ 62080) (by norm_num : 62080 ≤ 62208), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 61952 ≤ 62080) (by norm_num : 62080 ≤ 62208), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 61952 ≤ 62080) (by norm_num : 62080 ≤ 62208), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 61952 ≤ 62080) (by norm_num : 62080 ≤ 62208), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_62208_62272 :
    (∑ n ∈ Ico 62208 62272, mobiusTreeValue 16 mobiusTable1200001 n) = (4 : ℤ) ∧
    (∑ n ∈ Ico 62208 62272, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 62208 62272, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (320973 : ℤ) ∧
    (∑ n ∈ Ico 62208 62272, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (6419532723182397208047125555 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_62272_62336 :
    (∑ n ∈ Ico 62272 62336, mobiusTreeValue 16 mobiusTable1200001 n) = (2 : ℤ) ∧
    (∑ n ∈ Ico 62272 62336, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 62272 62336, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (160617 : ℤ) ∧
    (∑ n ∈ Ico 62272 62336, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (3212283724319392666889187400 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_62208_62336 :
    (∑ n ∈ Ico 62208 62336, mobiusTreeValue 16 mobiusTable1200001 n) = (6 : ℤ) ∧
    (∑ n ∈ Ico 62208 62336, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 62208 62336, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (481590 : ℤ) ∧
    (∑ n ∈ Ico 62208 62336, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (9631816447501789874936312955 : ℤ) := by
  rcases cdemPrefixStats_62208_62272 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_62272_62336 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 62208 ≤ 62272) (by norm_num : 62272 ≤ 62336), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 62208 ≤ 62272) (by norm_num : 62272 ≤ 62336), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 62208 ≤ 62272) (by norm_num : 62272 ≤ 62336), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 62208 ≤ 62272) (by norm_num : 62272 ≤ 62336), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_62336_62400 :
    (∑ n ∈ Ico 62336 62400, mobiusTreeValue 16 mobiusTable1200001 n) = (4 : ℤ) ∧
    (∑ n ∈ Ico 62336 62400, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 62336 62400, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (320496 : ℤ) ∧
    (∑ n ∈ Ico 62336 62400, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (6409894209700144306737726599 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_62400_62464 :
    (∑ n ∈ Ico 62400 62464, mobiusTreeValue 16 mobiusTable1200001 n) = (11 : ℤ) ∧
    (∑ n ∈ Ico 62400 62464, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 62400 62464, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (880773 : ℤ) ∧
    (∑ n ∈ Ico 62400 62464, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (17615552384779884334020365865 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_62336_62464 :
    (∑ n ∈ Ico 62336 62464, mobiusTreeValue 16 mobiusTable1200001 n) = (15 : ℤ) ∧
    (∑ n ∈ Ico 62336 62464, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 62336 62464, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (1201269 : ℤ) ∧
    (∑ n ∈ Ico 62336 62464, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (24025446594480028640758092464 : ℤ) := by
  rcases cdemPrefixStats_62336_62400 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_62400_62464 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 62336 ≤ 62400) (by norm_num : 62400 ≤ 62464), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 62336 ≤ 62400) (by norm_num : 62400 ≤ 62464), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 62336 ≤ 62400) (by norm_num : 62400 ≤ 62464), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 62336 ≤ 62400) (by norm_num : 62400 ≤ 62464), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_62208_62464 :
    (∑ n ∈ Ico 62208 62464, mobiusTreeValue 16 mobiusTable1200001 n) = (21 : ℤ) ∧
    (∑ n ∈ Ico 62208 62464, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (155 : ℕ) ∧
    (∑ n ∈ Ico 62208 62464, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (1682859 : ℤ) ∧
    (∑ n ∈ Ico 62208 62464, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (33657263041981818515694405419 : ℤ) := by
  rcases cdemPrefixStats_62208_62336 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_62336_62464 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 62208 ≤ 62336) (by norm_num : 62336 ≤ 62464), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 62208 ≤ 62336) (by norm_num : 62336 ≤ 62464), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 62208 ≤ 62336) (by norm_num : 62336 ≤ 62464), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 62208 ≤ 62336) (by norm_num : 62336 ≤ 62464), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_61952_62464 :
    (∑ n ∈ Ico 61952 62464, mobiusTreeValue 16 mobiusTable1200001 n) = (10 : ℤ) ∧
    (∑ n ∈ Ico 61952 62464, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (312 : ℕ) ∧
    (∑ n ∈ Ico 61952 62464, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (795041 : ℤ) ∧
    (∑ n ∈ Ico 61952 62464, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (15900881981255149644673276958 : ℤ) := by
  rcases cdemPrefixStats_61952_62208 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_62208_62464 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 61952 ≤ 62208) (by norm_num : 62208 ≤ 62464), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 61952 ≤ 62208) (by norm_num : 62208 ≤ 62464), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 61952 ≤ 62208) (by norm_num : 62208 ≤ 62464), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 61952 ≤ 62208) (by norm_num : 62208 ≤ 62464), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_61440_62464 :
    (∑ n ∈ Ico 61440 62464, mobiusTreeValue 16 mobiusTable1200001 n) = (5 : ℤ) ∧
    (∑ n ∈ Ico 61440 62464, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (623 : ℕ) ∧
    (∑ n ∈ Ico 61440 62464, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (384112 : ℤ) ∧
    (∑ n ∈ Ico 61440 62464, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (7682138040720437585263944034 : ℤ) := by
  rcases cdemPrefixStats_61440_61952 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_61952_62464 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 61440 ≤ 61952) (by norm_num : 61952 ≤ 62464), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 61440 ≤ 61952) (by norm_num : 61952 ≤ 62464), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 61440 ≤ 61952) (by norm_num : 61952 ≤ 62464), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 61440 ≤ 61952) (by norm_num : 61952 ≤ 62464), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_62464_62528 :
    (∑ n ∈ Ico 62464 62528, mobiusTreeValue 16 mobiusTable1200001 n) = (3 : ℤ) ∧
    (∑ n ∈ Ico 62464 62528, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 62464 62528, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (239767 : ℤ) ∧
    (∑ n ∈ Ico 62464 62528, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (4795367024945119447704677055 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_62528_62592 :
    (∑ n ∈ Ico 62528 62592, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 62528 62592, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 62528 62592, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (79965 : ℤ) ∧
    (∑ n ∈ Ico 62528 62592, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1599334483881986742471702147 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_62464_62592 :
    (∑ n ∈ Ico 62464 62592, mobiusTreeValue 16 mobiusTable1200001 n) = (4 : ℤ) ∧
    (∑ n ∈ Ico 62464 62592, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 62464 62592, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (319732 : ℤ) ∧
    (∑ n ∈ Ico 62464 62592, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (6394701508827106190176379202 : ℤ) := by
  rcases cdemPrefixStats_62464_62528 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_62528_62592 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 62464 ≤ 62528) (by norm_num : 62528 ≤ 62592), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 62464 ≤ 62528) (by norm_num : 62528 ≤ 62592), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 62464 ≤ 62528) (by norm_num : 62528 ≤ 62592), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 62464 ≤ 62528) (by norm_num : 62528 ≤ 62592), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_62592_62656 :
    (∑ n ∈ Ico 62592 62656, mobiusTreeValue 16 mobiusTable1200001 n) = (-3 : ℤ) ∧
    (∑ n ∈ Ico 62592 62656, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 62592 62656, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-239569 : ℤ) ∧
    (∑ n ∈ Ico 62592 62656, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-4791337245693905669287709704 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_62656_62720 :
    (∑ n ∈ Ico 62656 62720, mobiusTreeValue 16 mobiusTable1200001 n) = (12 : ℤ) ∧
    (∑ n ∈ Ico 62656 62720, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 62656 62720, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (957063 : ℤ) ∧
    (∑ n ∈ Ico 62656 62720, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (19141378933142968723712582236 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_62592_62720 :
    (∑ n ∈ Ico 62592 62720, mobiusTreeValue 16 mobiusTable1200001 n) = (9 : ℤ) ∧
    (∑ n ∈ Ico 62592 62720, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (79 : ℕ) ∧
    (∑ n ∈ Ico 62592 62720, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (717494 : ℤ) ∧
    (∑ n ∈ Ico 62592 62720, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (14350041687449063054424872532 : ℤ) := by
  rcases cdemPrefixStats_62592_62656 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_62656_62720 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 62592 ≤ 62656) (by norm_num : 62656 ≤ 62720), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 62592 ≤ 62656) (by norm_num : 62656 ≤ 62720), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 62592 ≤ 62656) (by norm_num : 62656 ≤ 62720), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 62592 ≤ 62656) (by norm_num : 62656 ≤ 62720), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_62464_62720 :
    (∑ n ∈ Ico 62464 62720, mobiusTreeValue 16 mobiusTable1200001 n) = (13 : ℤ) ∧
    (∑ n ∈ Ico 62464 62720, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (157 : ℕ) ∧
    (∑ n ∈ Ico 62464 62720, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (1037226 : ℤ) ∧
    (∑ n ∈ Ico 62464 62720, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (20744743196276169244601251734 : ℤ) := by
  rcases cdemPrefixStats_62464_62592 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_62592_62720 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 62464 ≤ 62592) (by norm_num : 62592 ≤ 62720), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 62464 ≤ 62592) (by norm_num : 62592 ≤ 62720), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 62464 ≤ 62592) (by norm_num : 62592 ≤ 62720), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 62464 ≤ 62592) (by norm_num : 62592 ≤ 62720), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_62720_62784 :
    (∑ n ∈ Ico 62720 62784, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 62720 62784, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 62720 62784, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (79559 : ℤ) ∧
    (∑ n ∈ Ico 62720 62784, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1591238084076223158518536954 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_62784_62848 :
    (∑ n ∈ Ico 62784 62848, mobiusTreeValue 16 mobiusTable1200001 n) = (7 : ℤ) ∧
    (∑ n ∈ Ico 62784 62848, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 62784 62848, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (557238 : ℤ) ∧
    (∑ n ∈ Ico 62784 62848, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (11144824421187919847727162431 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_62720_62848 :
    (∑ n ∈ Ico 62720 62848, mobiusTreeValue 16 mobiusTable1200001 n) = (8 : ℤ) ∧
    (∑ n ∈ Ico 62720 62848, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (76 : ℕ) ∧
    (∑ n ∈ Ico 62720 62848, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (636797 : ℤ) ∧
    (∑ n ∈ Ico 62720 62848, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (12736062505264143006245699385 : ℤ) := by
  rcases cdemPrefixStats_62720_62784 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_62784_62848 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 62720 ≤ 62784) (by norm_num : 62784 ≤ 62848), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 62720 ≤ 62784) (by norm_num : 62784 ≤ 62848), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 62720 ≤ 62784) (by norm_num : 62784 ≤ 62848), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 62720 ≤ 62784) (by norm_num : 62784 ≤ 62848), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_62848_62912 :
    (∑ n ∈ Ico 62848 62912, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 62848 62912, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 62848 62912, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-79698 : ℤ) ∧
    (∑ n ∈ Ico 62848 62912, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-1593897471299716553535831447 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_62912_62976 :
    (∑ n ∈ Ico 62912 62976, mobiusTreeValue 16 mobiusTable1200001 n) = (-7 : ℤ) ∧
    (∑ n ∈ Ico 62912 62976, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 62912 62976, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-556239 : ℤ) ∧
    (∑ n ∈ Ico 62912 62976, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-11124834867816072198764106540 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_62848_62976 :
    (∑ n ∈ Ico 62848 62976, mobiusTreeValue 16 mobiusTable1200001 n) = (-8 : ℤ) ∧
    (∑ n ∈ Ico 62848 62976, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (76 : ℕ) ∧
    (∑ n ∈ Ico 62848 62976, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-635937 : ℤ) ∧
    (∑ n ∈ Ico 62848 62976, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-12718732339115788752299937987 : ℤ) := by
  rcases cdemPrefixStats_62848_62912 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_62912_62976 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 62848 ≤ 62912) (by norm_num : 62912 ≤ 62976), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 62848 ≤ 62912) (by norm_num : 62912 ≤ 62976), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 62848 ≤ 62912) (by norm_num : 62912 ≤ 62976), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 62848 ≤ 62912) (by norm_num : 62912 ≤ 62976), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_62720_62976 :
    (∑ n ∈ Ico 62720 62976, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 62720 62976, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (152 : ℕ) ∧
    (∑ n ∈ Ico 62720 62976, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (860 : ℤ) ∧
    (∑ n ∈ Ico 62720 62976, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (17330166148354253945761398 : ℤ) := by
  rcases cdemPrefixStats_62720_62848 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_62848_62976 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 62720 ≤ 62848) (by norm_num : 62848 ≤ 62976), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 62720 ≤ 62848) (by norm_num : 62848 ≤ 62976), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 62720 ≤ 62848) (by norm_num : 62848 ≤ 62976), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 62720 ≤ 62848) (by norm_num : 62848 ≤ 62976), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_62464_62976 :
    (∑ n ∈ Ico 62464 62976, mobiusTreeValue 16 mobiusTable1200001 n) = (13 : ℤ) ∧
    (∑ n ∈ Ico 62464 62976, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (309 : ℕ) ∧
    (∑ n ∈ Ico 62464 62976, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (1038086 : ℤ) ∧
    (∑ n ∈ Ico 62464 62976, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (20762073362424523498547013132 : ℤ) := by
  rcases cdemPrefixStats_62464_62720 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_62720_62976 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 62464 ≤ 62720) (by norm_num : 62720 ≤ 62976), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 62464 ≤ 62720) (by norm_num : 62720 ≤ 62976), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 62464 ≤ 62720) (by norm_num : 62720 ≤ 62976), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 62464 ≤ 62720) (by norm_num : 62720 ≤ 62976), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_62976_63040 :
    (∑ n ∈ Ico 62976 63040, mobiusTreeValue 16 mobiusTable1200001 n) = (-8 : ℤ) ∧
    (∑ n ∈ Ico 62976 63040, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 62976 63040, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-634851 : ℤ) ∧
    (∑ n ∈ Ico 62976 63040, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-12697053272872324824012977239 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_63040_63104 :
    (∑ n ∈ Ico 63040 63104, mobiusTreeValue 16 mobiusTable1200001 n) = (11 : ℤ) ∧
    (∑ n ∈ Ico 63040 63104, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 63040 63104, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (872046 : ℤ) ∧
    (∑ n ∈ Ico 63040 63104, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (17441040355305062956942946606 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_62976_63104 :
    (∑ n ∈ Ico 62976 63104, mobiusTreeValue 16 mobiusTable1200001 n) = (3 : ℤ) ∧
    (∑ n ∈ Ico 62976 63104, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 62976 63104, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (237195 : ℤ) ∧
    (∑ n ∈ Ico 62976 63104, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (4743987082432738132929969367 : ℤ) := by
  rcases cdemPrefixStats_62976_63040 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_63040_63104 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 62976 ≤ 63040) (by norm_num : 63040 ≤ 63104), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 62976 ≤ 63040) (by norm_num : 63040 ≤ 63104), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 62976 ≤ 63040) (by norm_num : 63040 ≤ 63104), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 62976 ≤ 63040) (by norm_num : 63040 ≤ 63104), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_63104_63168 :
    (∑ n ∈ Ico 63104 63168, mobiusTreeValue 16 mobiusTable1200001 n) = (-4 : ℤ) ∧
    (∑ n ∈ Ico 63104 63168, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 63104 63168, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-316848 : ℤ) ∧
    (∑ n ∈ Ico 63104 63168, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-6337060510959306522605896178 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_63168_63232 :
    (∑ n ∈ Ico 63168 63232, mobiusTreeValue 16 mobiusTable1200001 n) = (2 : ℤ) ∧
    (∑ n ∈ Ico 63168 63232, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 63168 63232, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (158252 : ℤ) ∧
    (∑ n ∈ Ico 63168 63232, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (3165082340092479059599955756 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_63104_63232 :
    (∑ n ∈ Ico 63104 63232, mobiusTreeValue 16 mobiusTable1200001 n) = (-2 : ℤ) ∧
    (∑ n ∈ Ico 63104 63232, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (80 : ℕ) ∧
    (∑ n ∈ Ico 63104 63232, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-158596 : ℤ) ∧
    (∑ n ∈ Ico 63104 63232, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-3171978170866827463005940422 : ℤ) := by
  rcases cdemPrefixStats_63104_63168 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_63168_63232 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 63104 ≤ 63168) (by norm_num : 63168 ≤ 63232), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 63104 ≤ 63168) (by norm_num : 63168 ≤ 63232), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 63104 ≤ 63168) (by norm_num : 63168 ≤ 63232), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 63104 ≤ 63168) (by norm_num : 63168 ≤ 63232), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_62976_63232 :
    (∑ n ∈ Ico 62976 63232, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 62976 63232, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (157 : ℕ) ∧
    (∑ n ∈ Ico 62976 63232, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (78599 : ℤ) ∧
    (∑ n ∈ Ico 62976 63232, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1572008911565910669924028945 : ℤ) := by
  rcases cdemPrefixStats_62976_63104 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_63104_63232 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 62976 ≤ 63104) (by norm_num : 63104 ≤ 63232), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 62976 ≤ 63104) (by norm_num : 63104 ≤ 63232), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 62976 ≤ 63104) (by norm_num : 63104 ≤ 63232), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 62976 ≤ 63104) (by norm_num : 63104 ≤ 63232), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_63232_63296 :
    (∑ n ∈ Ico 63232 63296, mobiusTreeValue 16 mobiusTable1200001 n) = (3 : ℤ) ∧
    (∑ n ∈ Ico 63232 63296, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 63232 63296, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (237096 : ℤ) ∧
    (∑ n ∈ Ico 63232 63296, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (4741934065336543421390656591 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_63296_63360 :
    (∑ n ∈ Ico 63296 63360, mobiusTreeValue 16 mobiusTable1200001 n) = (-3 : ℤ) ∧
    (∑ n ∈ Ico 63296 63360, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 63296 63360, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-236797 : ℤ) ∧
    (∑ n ∈ Ico 63296 63360, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-4735994976330907453912965972 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_63232_63360 :
    (∑ n ∈ Ico 63232 63360, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 63232 63360, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (76 : ℕ) ∧
    (∑ n ∈ Ico 63232 63360, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (299 : ℤ) ∧
    (∑ n ∈ Ico 63232 63360, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (5939089005635967477690619 : ℤ) := by
  rcases cdemPrefixStats_63232_63296 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_63296_63360 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 63232 ≤ 63296) (by norm_num : 63296 ≤ 63360), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 63232 ≤ 63296) (by norm_num : 63296 ≤ 63360), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 63232 ≤ 63296) (by norm_num : 63296 ≤ 63360), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 63232 ≤ 63296) (by norm_num : 63296 ≤ 63360), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_63360_63424 :
    (∑ n ∈ Ico 63360 63424, mobiusTreeValue 16 mobiusTable1200001 n) = (-8 : ℤ) ∧
    (∑ n ∈ Ico 63360 63424, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 63360 63424, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-630871 : ℤ) ∧
    (∑ n ∈ Ico 63360 63424, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-12617526266245418581033000628 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_63424_63488 :
    (∑ n ∈ Ico 63424 63488, mobiusTreeValue 16 mobiusTable1200001 n) = (5 : ℤ) ∧
    (∑ n ∈ Ico 63424 63488, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 63424 63488, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (394168 : ℤ) ∧
    (∑ n ∈ Ico 63424 63488, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (7883399656447333939569881524 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_63360_63488 :
    (∑ n ∈ Ico 63360 63488, mobiusTreeValue 16 mobiusTable1200001 n) = (-3 : ℤ) ∧
    (∑ n ∈ Ico 63360 63488, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (79 : ℕ) ∧
    (∑ n ∈ Ico 63360 63488, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-236703 : ℤ) ∧
    (∑ n ∈ Ico 63360 63488, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-4734126609798084641463119104 : ℤ) := by
  rcases cdemPrefixStats_63360_63424 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_63424_63488 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 63360 ≤ 63424) (by norm_num : 63424 ≤ 63488), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 63360 ≤ 63424) (by norm_num : 63424 ≤ 63488), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 63360 ≤ 63424) (by norm_num : 63424 ≤ 63488), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 63360 ≤ 63424) (by norm_num : 63424 ≤ 63488), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_63232_63488 :
    (∑ n ∈ Ico 63232 63488, mobiusTreeValue 16 mobiusTable1200001 n) = (-3 : ℤ) ∧
    (∑ n ∈ Ico 63232 63488, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (155 : ℕ) ∧
    (∑ n ∈ Ico 63232 63488, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-236404 : ℤ) ∧
    (∑ n ∈ Ico 63232 63488, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-4728187520792448673985428485 : ℤ) := by
  rcases cdemPrefixStats_63232_63360 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_63360_63488 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 63232 ≤ 63360) (by norm_num : 63360 ≤ 63488), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 63232 ≤ 63360) (by norm_num : 63360 ≤ 63488), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 63232 ≤ 63360) (by norm_num : 63360 ≤ 63488), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 63232 ≤ 63360) (by norm_num : 63360 ≤ 63488), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_62976_63488 :
    (∑ n ∈ Ico 62976 63488, mobiusTreeValue 16 mobiusTable1200001 n) = (-2 : ℤ) ∧
    (∑ n ∈ Ico 62976 63488, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (312 : ℕ) ∧
    (∑ n ∈ Ico 62976 63488, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-157805 : ℤ) ∧
    (∑ n ∈ Ico 62976 63488, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-3156178609226538004061399540 : ℤ) := by
  rcases cdemPrefixStats_62976_63232 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_63232_63488 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 62976 ≤ 63232) (by norm_num : 63232 ≤ 63488), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 62976 ≤ 63232) (by norm_num : 63232 ≤ 63488), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 62976 ≤ 63232) (by norm_num : 63232 ≤ 63488), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 62976 ≤ 63232) (by norm_num : 63232 ≤ 63488), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_62464_63488 :
    (∑ n ∈ Ico 62464 63488, mobiusTreeValue 16 mobiusTable1200001 n) = (11 : ℤ) ∧
    (∑ n ∈ Ico 62464 63488, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (621 : ℕ) ∧
    (∑ n ∈ Ico 62464 63488, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (880281 : ℤ) ∧
    (∑ n ∈ Ico 62464 63488, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (17605894753197985494485613592 : ℤ) := by
  rcases cdemPrefixStats_62464_62976 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_62976_63488 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 62464 ≤ 62976) (by norm_num : 62976 ≤ 63488), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 62464 ≤ 62976) (by norm_num : 62976 ≤ 63488), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 62464 ≤ 62976) (by norm_num : 62976 ≤ 63488), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 62464 ≤ 62976) (by norm_num : 62976 ≤ 63488), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_61440_63488 :
    (∑ n ∈ Ico 61440 63488, mobiusTreeValue 16 mobiusTable1200001 n) = (16 : ℤ) ∧
    (∑ n ∈ Ico 61440 63488, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (1244 : ℕ) ∧
    (∑ n ∈ Ico 61440 63488, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (1264393 : ℤ) ∧
    (∑ n ∈ Ico 61440 63488, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (25288032793918423079749557626 : ℤ) := by
  rcases cdemPrefixStats_61440_62464 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_62464_63488 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 61440 ≤ 62464) (by norm_num : 62464 ≤ 63488), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 61440 ≤ 62464) (by norm_num : 62464 ≤ 63488), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 61440 ≤ 62464) (by norm_num : 62464 ≤ 63488), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 61440 ≤ 62464) (by norm_num : 62464 ≤ 63488), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_63488_63552 :
    (∑ n ∈ Ico 63488 63552, mobiusTreeValue 16 mobiusTable1200001 n) = (-11 : ℤ) ∧
    (∑ n ∈ Ico 63488 63552, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 63488 63552, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-865736 : ℤ) ∧
    (∑ n ∈ Ico 63488 63552, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-17314877895722756052900991724 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_63552_63616 :
    (∑ n ∈ Ico 63552 63616, mobiusTreeValue 16 mobiusTable1200001 n) = (-2 : ℤ) ∧
    (∑ n ∈ Ico 63552 63616, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 63552 63616, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-157121 : ℤ) ∧
    (∑ n ∈ Ico 63552 63616, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-3142502534639403947819819653 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_63488_63616 :
    (∑ n ∈ Ico 63488 63616, mobiusTreeValue 16 mobiusTable1200001 n) = (-13 : ℤ) ∧
    (∑ n ∈ Ico 63488 63616, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (81 : ℕ) ∧
    (∑ n ∈ Ico 63488 63616, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-1022857 : ℤ) ∧
    (∑ n ∈ Ico 63488 63616, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-20457380430362160000720811377 : ℤ) := by
  rcases cdemPrefixStats_63488_63552 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_63552_63616 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 63488 ≤ 63552) (by norm_num : 63552 ≤ 63616), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 63488 ≤ 63552) (by norm_num : 63552 ≤ 63616), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 63488 ≤ 63552) (by norm_num : 63552 ≤ 63616), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 63488 ≤ 63552) (by norm_num : 63552 ≤ 63616), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_63616_63680 :
    (∑ n ∈ Ico 63616 63680, mobiusTreeValue 16 mobiusTable1200001 n) = (-9 : ℤ) ∧
    (∑ n ∈ Ico 63616 63680, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 63616 63680, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-706974 : ℤ) ∧
    (∑ n ∈ Ico 63616 63680, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-14139581515050485304595170709 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_63680_63744 :
    (∑ n ∈ Ico 63680 63744, mobiusTreeValue 16 mobiusTable1200001 n) = (-7 : ℤ) ∧
    (∑ n ∈ Ico 63680 63744, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 63680 63744, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-549358 : ℤ) ∧
    (∑ n ∈ Ico 63680 63744, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-10987212596188535960869086015 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_63616_63744 :
    (∑ n ∈ Ico 63616 63744, mobiusTreeValue 16 mobiusTable1200001 n) = (-16 : ℤ) ∧
    (∑ n ∈ Ico 63616 63744, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 63616 63744, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-1256332 : ℤ) ∧
    (∑ n ∈ Ico 63616 63744, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-25126794111239021265464256724 : ℤ) := by
  rcases cdemPrefixStats_63616_63680 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_63680_63744 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 63616 ≤ 63680) (by norm_num : 63680 ≤ 63744), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 63616 ≤ 63680) (by norm_num : 63680 ≤ 63744), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 63616 ≤ 63680) (by norm_num : 63680 ≤ 63744), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 63616 ≤ 63680) (by norm_num : 63680 ≤ 63744), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_63488_63744 :
    (∑ n ∈ Ico 63488 63744, mobiusTreeValue 16 mobiusTable1200001 n) = (-29 : ℤ) ∧
    (∑ n ∈ Ico 63488 63744, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (159 : ℕ) ∧
    (∑ n ∈ Ico 63488 63744, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-2279189 : ℤ) ∧
    (∑ n ∈ Ico 63488 63744, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-45584174541601181266185068101 : ℤ) := by
  rcases cdemPrefixStats_63488_63616 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_63616_63744 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 63488 ≤ 63616) (by norm_num : 63616 ≤ 63744), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 63488 ≤ 63616) (by norm_num : 63616 ≤ 63744), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 63488 ≤ 63616) (by norm_num : 63616 ≤ 63744), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 63488 ≤ 63616) (by norm_num : 63616 ≤ 63744), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_63744_63808 :
    (∑ n ∈ Ico 63744 63808, mobiusTreeValue 16 mobiusTable1200001 n) = (-8 : ℤ) ∧
    (∑ n ∈ Ico 63744 63808, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 63744 63808, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-627044 : ℤ) ∧
    (∑ n ∈ Ico 63744 63808, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-12540929427928699262678475950 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_63808_63872 :
    (∑ n ∈ Ico 63808 63872, mobiusTreeValue 16 mobiusTable1200001 n) = (-6 : ℤ) ∧
    (∑ n ∈ Ico 63808 63872, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 63808 63872, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-469758 : ℤ) ∧
    (∑ n ∈ Ico 63808 63872, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-9395232950831522729919898993 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_63744_63872 :
    (∑ n ∈ Ico 63744 63872, mobiusTreeValue 16 mobiusTable1200001 n) = (-14 : ℤ) ∧
    (∑ n ∈ Ico 63744 63872, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (76 : ℕ) ∧
    (∑ n ∈ Ico 63744 63872, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-1096802 : ℤ) ∧
    (∑ n ∈ Ico 63744 63872, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-21936162378760221992598374943 : ℤ) := by
  rcases cdemPrefixStats_63744_63808 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_63808_63872 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 63744 ≤ 63808) (by norm_num : 63808 ≤ 63872), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 63744 ≤ 63808) (by norm_num : 63808 ≤ 63872), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 63744 ≤ 63808) (by norm_num : 63808 ≤ 63872), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 63744 ≤ 63808) (by norm_num : 63808 ≤ 63872), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_63872_63936 :
    (∑ n ∈ Ico 63872 63936, mobiusTreeValue 16 mobiusTable1200001 n) = (-4 : ℤ) ∧
    (∑ n ∈ Ico 63872 63936, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 63872 63936, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-312932 : ℤ) ∧
    (∑ n ∈ Ico 63872 63936, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-6258728413363615494034114813 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_63936_64000 :
    (∑ n ∈ Ico 63936 64000, mobiusTreeValue 16 mobiusTable1200001 n) = (11 : ℤ) ∧
    (∑ n ∈ Ico 63936 64000, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 63936 64000, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (859950 : ℤ) ∧
    (∑ n ∈ Ico 63936 64000, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (17199154036923239752832917632 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_63872_64000 :
    (∑ n ∈ Ico 63872 64000, mobiusTreeValue 16 mobiusTable1200001 n) = (7 : ℤ) ∧
    (∑ n ∈ Ico 63872 64000, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 63872 64000, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (547018 : ℤ) ∧
    (∑ n ∈ Ico 63872 64000, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (10940425623559624258798802819 : ℤ) := by
  rcases cdemPrefixStats_63872_63936 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_63936_64000 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 63872 ≤ 63936) (by norm_num : 63936 ≤ 64000), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 63872 ≤ 63936) (by norm_num : 63936 ≤ 64000), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 63872 ≤ 63936) (by norm_num : 63936 ≤ 64000), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 63872 ≤ 63936) (by norm_num : 63936 ≤ 64000), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_63744_64000 :
    (∑ n ∈ Ico 63744 64000, mobiusTreeValue 16 mobiusTable1200001 n) = (-7 : ℤ) ∧
    (∑ n ∈ Ico 63744 64000, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (153 : ℕ) ∧
    (∑ n ∈ Ico 63744 64000, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-549784 : ℤ) ∧
    (∑ n ∈ Ico 63744 64000, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-10995736755200597733799572124 : ℤ) := by
  rcases cdemPrefixStats_63744_63872 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_63872_64000 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 63744 ≤ 63872) (by norm_num : 63872 ≤ 64000), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 63744 ≤ 63872) (by norm_num : 63872 ≤ 64000), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 63744 ≤ 63872) (by norm_num : 63872 ≤ 64000), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 63744 ≤ 63872) (by norm_num : 63872 ≤ 64000), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_63488_64000 :
    (∑ n ∈ Ico 63488 64000, mobiusTreeValue 16 mobiusTable1200001 n) = (-36 : ℤ) ∧
    (∑ n ∈ Ico 63488 64000, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (312 : ℕ) ∧
    (∑ n ∈ Ico 63488 64000, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-2828973 : ℤ) ∧
    (∑ n ∈ Ico 63488 64000, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-56579911296801778999984640225 : ℤ) := by
  rcases cdemPrefixStats_63488_63744 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_63744_64000 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 63488 ≤ 63744) (by norm_num : 63744 ≤ 64000), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 63488 ≤ 63744) (by norm_num : 63744 ≤ 64000), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 63488 ≤ 63744) (by norm_num : 63744 ≤ 64000), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 63488 ≤ 63744) (by norm_num : 63744 ≤ 64000), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_64000_64064 :
    (∑ n ∈ Ico 64000 64064, mobiusTreeValue 16 mobiusTable1200001 n) = (7 : ℤ) ∧
    (∑ n ∈ Ico 64000 64064, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 64000 64064, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (546639 : ℤ) ∧
    (∑ n ∈ Ico 64000 64064, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (10932814545359628366549441096 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_64064_64128 :
    (∑ n ∈ Ico 64064 64128, mobiusTreeValue 16 mobiusTable1200001 n) = (13 : ℤ) ∧
    (∑ n ∈ Ico 64064 64128, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 64064 64128, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (1013889 : ℤ) ∧
    (∑ n ∈ Ico 64064 64128, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (20277964894791208774996541295 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_64000_64128 :
    (∑ n ∈ Ico 64000 64128, mobiusTreeValue 16 mobiusTable1200001 n) = (20 : ℤ) ∧
    (∑ n ∈ Ico 64000 64128, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 64000 64128, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (1560528 : ℤ) ∧
    (∑ n ∈ Ico 64000 64128, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (31210779440150837141545982391 : ℤ) := by
  rcases cdemPrefixStats_64000_64064 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_64064_64128 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 64000 ≤ 64064) (by norm_num : 64064 ≤ 64128), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 64000 ≤ 64064) (by norm_num : 64064 ≤ 64128), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 64000 ≤ 64064) (by norm_num : 64064 ≤ 64128), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 64000 ≤ 64064) (by norm_num : 64064 ≤ 64128), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_64128_64192 :
    (∑ n ∈ Ico 64128 64192, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 64128 64192, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 64128 64192, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (78074 : ℤ) ∧
    (∑ n ∈ Ico 64128 64192, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1561544126372855266993061620 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_64192_64256 :
    (∑ n ∈ Ico 64192 64256, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 64192 64256, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 64192 64256, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-77800 : ℤ) ∧
    (∑ n ∈ Ico 64192 64256, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-1555983326619736950476559300 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_64128_64256 :
    (∑ n ∈ Ico 64128 64256, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 64128 64256, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (76 : ℕ) ∧
    (∑ n ∈ Ico 64128 64256, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (274 : ℤ) ∧
    (∑ n ∈ Ico 64128 64256, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (5560799753118316516502320 : ℤ) := by
  rcases cdemPrefixStats_64128_64192 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_64192_64256 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 64128 ≤ 64192) (by norm_num : 64192 ≤ 64256), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 64128 ≤ 64192) (by norm_num : 64192 ≤ 64256), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 64128 ≤ 64192) (by norm_num : 64192 ≤ 64256), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 64128 ≤ 64192) (by norm_num : 64192 ≤ 64256), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_64000_64256 :
    (∑ n ∈ Ico 64000 64256, mobiusTreeValue 16 mobiusTable1200001 n) = (20 : ℤ) ∧
    (∑ n ∈ Ico 64000 64256, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (154 : ℕ) ∧
    (∑ n ∈ Ico 64000 64256, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (1560802 : ℤ) ∧
    (∑ n ∈ Ico 64000 64256, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (31216340239903955458062484711 : ℤ) := by
  rcases cdemPrefixStats_64000_64128 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_64128_64256 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 64000 ≤ 64128) (by norm_num : 64128 ≤ 64256), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 64000 ≤ 64128) (by norm_num : 64128 ≤ 64256), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 64000 ≤ 64128) (by norm_num : 64128 ≤ 64256), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 64000 ≤ 64128) (by norm_num : 64128 ≤ 64256), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_64256_64320 :
    (∑ n ∈ Ico 64256 64320, mobiusTreeValue 16 mobiusTable1200001 n) = (9 : ℤ) ∧
    (∑ n ∈ Ico 64256 64320, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 64256 64320, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (699942 : ℤ) ∧
    (∑ n ∈ Ico 64256 64320, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (13998874416817371802499044301 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_64320_64384 :
    (∑ n ∈ Ico 64320 64384, mobiusTreeValue 16 mobiusTable1200001 n) = (-3 : ℤ) ∧
    (∑ n ∈ Ico 64320 64384, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 64320 64384, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-233157 : ℤ) ∧
    (∑ n ∈ Ico 64320 64384, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-4663164266629186864332561924 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_64256_64384 :
    (∑ n ∈ Ico 64256 64384, mobiusTreeValue 16 mobiusTable1200001 n) = (6 : ℤ) ∧
    (∑ n ∈ Ico 64256 64384, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (80 : ℕ) ∧
    (∑ n ∈ Ico 64256 64384, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (466785 : ℤ) ∧
    (∑ n ∈ Ico 64256 64384, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (9335710150188184938166482377 : ℤ) := by
  rcases cdemPrefixStats_64256_64320 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_64320_64384 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 64256 ≤ 64320) (by norm_num : 64320 ≤ 64384), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 64256 ≤ 64320) (by norm_num : 64320 ≤ 64384), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 64256 ≤ 64320) (by norm_num : 64320 ≤ 64384), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 64256 ≤ 64320) (by norm_num : 64320 ≤ 64384), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_64384_64448 :
    (∑ n ∈ Ico 64384 64448, mobiusTreeValue 16 mobiusTable1200001 n) = (4 : ℤ) ∧
    (∑ n ∈ Ico 64384 64448, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 64384 64448, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (310367 : ℤ) ∧
    (∑ n ∈ Ico 64384 64448, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (6207372691419061895915133328 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_64448_64512 :
    (∑ n ∈ Ico 64448 64512, mobiusTreeValue 16 mobiusTable1200001 n) = (13 : ℤ) ∧
    (∑ n ∈ Ico 64448 64512, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 64448 64512, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (1007914 : ℤ) ∧
    (∑ n ∈ Ico 64448 64512, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (20158405826999354222411942354 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_64384_64512 :
    (∑ n ∈ Ico 64384 64512, mobiusTreeValue 16 mobiusTable1200001 n) = (17 : ℤ) ∧
    (∑ n ∈ Ico 64384 64512, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 64384 64512, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (1318281 : ℤ) ∧
    (∑ n ∈ Ico 64384 64512, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (26365778518418416118327075682 : ℤ) := by
  rcases cdemPrefixStats_64384_64448 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_64448_64512 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 64384 ≤ 64448) (by norm_num : 64448 ≤ 64512), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 64384 ≤ 64448) (by norm_num : 64448 ≤ 64512), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 64384 ≤ 64448) (by norm_num : 64448 ≤ 64512), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 64384 ≤ 64448) (by norm_num : 64448 ≤ 64512), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_64256_64512 :
    (∑ n ∈ Ico 64256 64512, mobiusTreeValue 16 mobiusTable1200001 n) = (23 : ℤ) ∧
    (∑ n ∈ Ico 64256 64512, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (157 : ℕ) ∧
    (∑ n ∈ Ico 64256 64512, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (1785066 : ℤ) ∧
    (∑ n ∈ Ico 64256 64512, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (35701488668606601056493558059 : ℤ) := by
  rcases cdemPrefixStats_64256_64384 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_64384_64512 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 64256 ≤ 64384) (by norm_num : 64384 ≤ 64512), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 64256 ≤ 64384) (by norm_num : 64384 ≤ 64512), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 64256 ≤ 64384) (by norm_num : 64384 ≤ 64512), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 64256 ≤ 64384) (by norm_num : 64384 ≤ 64512), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_64000_64512 :
    (∑ n ∈ Ico 64000 64512, mobiusTreeValue 16 mobiusTable1200001 n) = (43 : ℤ) ∧
    (∑ n ∈ Ico 64000 64512, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (311 : ℕ) ∧
    (∑ n ∈ Ico 64000 64512, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (3345868 : ℤ) ∧
    (∑ n ∈ Ico 64000 64512, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (66917828908510556514556042770 : ℤ) := by
  rcases cdemPrefixStats_64000_64256 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_64256_64512 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 64000 ≤ 64256) (by norm_num : 64256 ≤ 64512), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 64000 ≤ 64256) (by norm_num : 64256 ≤ 64512), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 64000 ≤ 64256) (by norm_num : 64256 ≤ 64512), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 64000 ≤ 64256) (by norm_num : 64256 ≤ 64512), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_63488_64512 :
    (∑ n ∈ Ico 63488 64512, mobiusTreeValue 16 mobiusTable1200001 n) = (7 : ℤ) ∧
    (∑ n ∈ Ico 63488 64512, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (623 : ℕ) ∧
    (∑ n ∈ Ico 63488 64512, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (516895 : ℤ) ∧
    (∑ n ∈ Ico 63488 64512, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (10337917611708777514571402545 : ℤ) := by
  rcases cdemPrefixStats_63488_64000 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_64000_64512 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 63488 ≤ 64000) (by norm_num : 64000 ≤ 64512), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 63488 ≤ 64000) (by norm_num : 64000 ≤ 64512), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 63488 ≤ 64000) (by norm_num : 64000 ≤ 64512), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 63488 ≤ 64000) (by norm_num : 64000 ≤ 64512), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_64512_64576 :
    (∑ n ∈ Ico 64512 64576, mobiusTreeValue 16 mobiusTable1200001 n) = (7 : ℤ) ∧
    (∑ n ∈ Ico 64512 64576, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 64512 64576, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (542251 : ℤ) ∧
    (∑ n ∈ Ico 64512 64576, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (10845075121857320390713875025 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_64576_64640 :
    (∑ n ∈ Ico 64576 64640, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 64576 64640, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 64576 64640, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (77448 : ℤ) ∧
    (∑ n ∈ Ico 64576 64640, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1548970250543431016535185893 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_64512_64640 :
    (∑ n ∈ Ico 64512 64640, mobiusTreeValue 16 mobiusTable1200001 n) = (8 : ℤ) ∧
    (∑ n ∈ Ico 64512 64640, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (74 : ℕ) ∧
    (∑ n ∈ Ico 64512 64640, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (619699 : ℤ) ∧
    (∑ n ∈ Ico 64512 64640, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (12394045372400751407249060918 : ℤ) := by
  rcases cdemPrefixStats_64512_64576 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_64576_64640 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 64512 ≤ 64576) (by norm_num : 64576 ≤ 64640), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 64512 ≤ 64576) (by norm_num : 64576 ≤ 64640), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 64512 ≤ 64576) (by norm_num : 64576 ≤ 64640), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 64512 ≤ 64576) (by norm_num : 64576 ≤ 64640), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_64640_64704 :
    (∑ n ∈ Ico 64640 64704, mobiusTreeValue 16 mobiusTable1200001 n) = (5 : ℤ) ∧
    (∑ n ∈ Ico 64640 64704, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 64640 64704, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (386477 : ℤ) ∧
    (∑ n ∈ Ico 64640 64704, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (7729529055339674686116730391 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_64704_64768 :
    (∑ n ∈ Ico 64704 64768, mobiusTreeValue 16 mobiusTable1200001 n) = (14 : ℤ) ∧
    (∑ n ∈ Ico 64704 64768, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (36 : ℕ) ∧
    (∑ n ∈ Ico 64704 64768, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (1081313 : ℤ) ∧
    (∑ n ∈ Ico 64704 64768, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (21626419861709612594322925656 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_64640_64768 :
    (∑ n ∈ Ico 64640 64768, mobiusTreeValue 16 mobiusTable1200001 n) = (19 : ℤ) ∧
    (∑ n ∈ Ico 64640 64768, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 64640 64768, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (1467790 : ℤ) ∧
    (∑ n ∈ Ico 64640 64768, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (29355948917049287280439656047 : ℤ) := by
  rcases cdemPrefixStats_64640_64704 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_64704_64768 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 64640 ≤ 64704) (by norm_num : 64704 ≤ 64768), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 64640 ≤ 64704) (by norm_num : 64704 ≤ 64768), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 64640 ≤ 64704) (by norm_num : 64704 ≤ 64768), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 64640 ≤ 64704) (by norm_num : 64704 ≤ 64768), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_64512_64768 :
    (∑ n ∈ Ico 64512 64768, mobiusTreeValue 16 mobiusTable1200001 n) = (27 : ℤ) ∧
    (∑ n ∈ Ico 64512 64768, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (151 : ℕ) ∧
    (∑ n ∈ Ico 64512 64768, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (2087489 : ℤ) ∧
    (∑ n ∈ Ico 64512 64768, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (41749994289450038687688716965 : ℤ) := by
  rcases cdemPrefixStats_64512_64640 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_64640_64768 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 64512 ≤ 64640) (by norm_num : 64640 ≤ 64768), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 64512 ≤ 64640) (by norm_num : 64640 ≤ 64768), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 64512 ≤ 64640) (by norm_num : 64640 ≤ 64768), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 64512 ≤ 64640) (by norm_num : 64640 ≤ 64768), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_64768_64832 :
    (∑ n ∈ Ico 64768 64832, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 64768 64832, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 64768 64832, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (76944 : ℤ) ∧
    (∑ n ∈ Ico 64768 64832, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1538924007843092500463593952 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_64832_64896 :
    (∑ n ∈ Ico 64832 64896, mobiusTreeValue 16 mobiusTable1200001 n) = (9 : ℤ) ∧
    (∑ n ∈ Ico 64832 64896, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 64832 64896, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (694058 : ℤ) ∧
    (∑ n ∈ Ico 64832 64896, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (13881270395038203869502601773 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_64768_64896 :
    (∑ n ∈ Ico 64768 64896, mobiusTreeValue 16 mobiusTable1200001 n) = (10 : ℤ) ∧
    (∑ n ∈ Ico 64768 64896, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (80 : ℕ) ∧
    (∑ n ∈ Ico 64768 64896, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (771002 : ℤ) ∧
    (∑ n ∈ Ico 64768 64896, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (15420194402881296369966195725 : ℤ) := by
  rcases cdemPrefixStats_64768_64832 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_64832_64896 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 64768 ≤ 64832) (by norm_num : 64832 ≤ 64896), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 64768 ≤ 64832) (by norm_num : 64832 ≤ 64896), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 64768 ≤ 64832) (by norm_num : 64832 ≤ 64896), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 64768 ≤ 64832) (by norm_num : 64832 ≤ 64896), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_64896_64960 :
    (∑ n ∈ Ico 64896 64960, mobiusTreeValue 16 mobiusTable1200001 n) = (5 : ℤ) ∧
    (∑ n ∈ Ico 64896 64960, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 64896 64960, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (385072 : ℤ) ∧
    (∑ n ∈ Ico 64896 64960, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (7701525508702501398118253828 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_64960_65024 :
    (∑ n ∈ Ico 64960 65024, mobiusTreeValue 16 mobiusTable1200001 n) = (5 : ℤ) ∧
    (∑ n ∈ Ico 64960 65024, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 64960 65024, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (384760 : ℤ) ∧
    (∑ n ∈ Ico 64960 65024, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (7695290917060746745672127707 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_64896_65024 :
    (∑ n ∈ Ico 64896 65024, mobiusTreeValue 16 mobiusTable1200001 n) = (10 : ℤ) ∧
    (∑ n ∈ Ico 64896 65024, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (80 : ℕ) ∧
    (∑ n ∈ Ico 64896 65024, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (769832 : ℤ) ∧
    (∑ n ∈ Ico 64896 65024, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (15396816425763248143790381535 : ℤ) := by
  rcases cdemPrefixStats_64896_64960 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_64960_65024 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 64896 ≤ 64960) (by norm_num : 64960 ≤ 65024), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 64896 ≤ 64960) (by norm_num : 64960 ≤ 65024), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 64896 ≤ 64960) (by norm_num : 64960 ≤ 65024), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 64896 ≤ 64960) (by norm_num : 64960 ≤ 65024), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_64768_65024 :
    (∑ n ∈ Ico 64768 65024, mobiusTreeValue 16 mobiusTable1200001 n) = (20 : ℤ) ∧
    (∑ n ∈ Ico 64768 65024, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (160 : ℕ) ∧
    (∑ n ∈ Ico 64768 65024, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (1540834 : ℤ) ∧
    (∑ n ∈ Ico 64768 65024, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (30817010828644544513756577260 : ℤ) := by
  rcases cdemPrefixStats_64768_64896 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_64896_65024 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 64768 ≤ 64896) (by norm_num : 64896 ≤ 65024), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 64768 ≤ 64896) (by norm_num : 64896 ≤ 65024), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 64768 ≤ 64896) (by norm_num : 64896 ≤ 65024), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 64768 ≤ 64896) (by norm_num : 64896 ≤ 65024), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_64512_65024 :
    (∑ n ∈ Ico 64512 65024, mobiusTreeValue 16 mobiusTable1200001 n) = (47 : ℤ) ∧
    (∑ n ∈ Ico 64512 65024, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (311 : ℕ) ∧
    (∑ n ∈ Ico 64512 65024, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (3628323 : ℤ) ∧
    (∑ n ∈ Ico 64512 65024, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (72567005118094583201445294225 : ℤ) := by
  rcases cdemPrefixStats_64512_64768 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_64768_65024 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 64512 ≤ 64768) (by norm_num : 64768 ≤ 65024), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 64512 ≤ 64768) (by norm_num : 64768 ≤ 65024), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 64512 ≤ 64768) (by norm_num : 64768 ≤ 65024), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 64512 ≤ 64768) (by norm_num : 64768 ≤ 65024), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_65024_65088 :
    (∑ n ∈ Ico 65024 65088, mobiusTreeValue 16 mobiusTable1200001 n) = (2 : ℤ) ∧
    (∑ n ∈ Ico 65024 65088, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 65024 65088, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (153810 : ℤ) ∧
    (∑ n ∈ Ico 65024 65088, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (3076282119216903108755051586 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_65088_65152 :
    (∑ n ∈ Ico 65088 65152, mobiusTreeValue 16 mobiusTable1200001 n) = (-12 : ℤ) ∧
    (∑ n ∈ Ico 65088 65152, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 65088 65152, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-921533 : ℤ) ∧
    (∑ n ∈ Ico 65088 65152, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-18430773738694889060626183449 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_65024_65152 :
    (∑ n ∈ Ico 65024 65152, mobiusTreeValue 16 mobiusTable1200001 n) = (-10 : ℤ) ∧
    (∑ n ∈ Ico 65024 65152, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (76 : ℕ) ∧
    (∑ n ∈ Ico 65024 65152, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-767723 : ℤ) ∧
    (∑ n ∈ Ico 65024 65152, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-15354491619477985951871131863 : ℤ) := by
  rcases cdemPrefixStats_65024_65088 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_65088_65152 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 65024 ≤ 65088) (by norm_num : 65088 ≤ 65152), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 65024 ≤ 65088) (by norm_num : 65088 ≤ 65152), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 65024 ≤ 65088) (by norm_num : 65088 ≤ 65152), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 65024 ≤ 65088) (by norm_num : 65088 ≤ 65152), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_65152_65216 :
    (∑ n ∈ Ico 65152 65216, mobiusTreeValue 16 mobiusTable1200001 n) = (-3 : ℤ) ∧
    (∑ n ∈ Ico 65152 65216, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 65152 65216, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-230135 : ℤ) ∧
    (∑ n ∈ Ico 65152 65216, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-4602732658730759382275278233 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_65216_65280 :
    (∑ n ∈ Ico 65216 65280, mobiusTreeValue 16 mobiusTable1200001 n) = (13 : ℤ) ∧
    (∑ n ∈ Ico 65216 65280, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 65216 65280, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (996279 : ℤ) ∧
    (∑ n ∈ Ico 65216 65280, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (19925745281366443332298431757 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_65152_65280 :
    (∑ n ∈ Ico 65152 65280, mobiusTreeValue 16 mobiusTable1200001 n) = (10 : ℤ) ∧
    (∑ n ∈ Ico 65152 65280, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (80 : ℕ) ∧
    (∑ n ∈ Ico 65152 65280, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (766144 : ℤ) ∧
    (∑ n ∈ Ico 65152 65280, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (15323012622635683950023153524 : ℤ) := by
  rcases cdemPrefixStats_65152_65216 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_65216_65280 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 65152 ≤ 65216) (by norm_num : 65216 ≤ 65280), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 65152 ≤ 65216) (by norm_num : 65216 ≤ 65280), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 65152 ≤ 65216) (by norm_num : 65216 ≤ 65280), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 65152 ≤ 65216) (by norm_num : 65216 ≤ 65280), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_65024_65280 :
    (∑ n ∈ Ico 65024 65280, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 65024 65280, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (156 : ℕ) ∧
    (∑ n ∈ Ico 65024 65280, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-1579 : ℤ) ∧
    (∑ n ∈ Ico 65024 65280, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-31478996842302001847978339 : ℤ) := by
  rcases cdemPrefixStats_65024_65152 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_65152_65280 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 65024 ≤ 65152) (by norm_num : 65152 ≤ 65280), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 65024 ≤ 65152) (by norm_num : 65152 ≤ 65280), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 65024 ≤ 65152) (by norm_num : 65152 ≤ 65280), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 65024 ≤ 65152) (by norm_num : 65152 ≤ 65280), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_65280_65344 :
    (∑ n ∈ Ico 65280 65344, mobiusTreeValue 16 mobiusTable1200001 n) = (-9 : ℤ) ∧
    (∑ n ∈ Ico 65280 65344, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 65280 65344, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-689102 : ℤ) ∧
    (∑ n ∈ Ico 65280 65344, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-13782121318781522605155414349 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_65344_65408 :
    (∑ n ∈ Ico 65344 65408, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 65344 65408, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 65344 65408, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (76314 : ℤ) ∧
    (∑ n ∈ Ico 65344 65408, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1526266447791854275113556277 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_65280_65408 :
    (∑ n ∈ Ico 65280 65408, mobiusTreeValue 16 mobiusTable1200001 n) = (-8 : ℤ) ∧
    (∑ n ∈ Ico 65280 65408, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 65280 65408, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-612788 : ℤ) ∧
    (∑ n ∈ Ico 65280 65408, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-12255854870989668330041858072 : ℤ) := by
  rcases cdemPrefixStats_65280_65344 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_65344_65408 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 65280 ≤ 65344) (by norm_num : 65344 ≤ 65408), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 65280 ≤ 65344) (by norm_num : 65344 ≤ 65408), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 65280 ≤ 65344) (by norm_num : 65344 ≤ 65408), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 65280 ≤ 65344) (by norm_num : 65344 ≤ 65408), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_65408_65472 :
    (∑ n ∈ Ico 65408 65472, mobiusTreeValue 16 mobiusTable1200001 n) = (-5 : ℤ) ∧
    (∑ n ∈ Ico 65408 65472, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 65408 65472, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-381981 : ℤ) ∧
    (∑ n ∈ Ico 65408 65472, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-7639699776412321117266103038 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_65472_65536 :
    (∑ n ∈ Ico 65472 65536, mobiusTreeValue 16 mobiusTable1200001 n) = (11 : ℤ) ∧
    (∑ n ∈ Ico 65472 65536, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 65472 65536, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (839504 : ℤ) ∧
    (∑ n ∈ Ico 65472 65536, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (16790188885827710443408059065 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_65408_65536 :
    (∑ n ∈ Ico 65408 65536, mobiusTreeValue 16 mobiusTable1200001 n) = (6 : ℤ) ∧
    (∑ n ∈ Ico 65408 65536, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 65408 65536, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (457523 : ℤ) ∧
    (∑ n ∈ Ico 65408 65536, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (9150489109415389326141956027 : ℤ) := by
  rcases cdemPrefixStats_65408_65472 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_65472_65536 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 65408 ≤ 65472) (by norm_num : 65472 ≤ 65536), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 65408 ≤ 65472) (by norm_num : 65472 ≤ 65536), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 65408 ≤ 65472) (by norm_num : 65472 ≤ 65536), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 65408 ≤ 65472) (by norm_num : 65472 ≤ 65536), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_65280_65536 :
    (∑ n ∈ Ico 65280 65536, mobiusTreeValue 16 mobiusTable1200001 n) = (-2 : ℤ) ∧
    (∑ n ∈ Ico 65280 65536, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (156 : ℕ) ∧
    (∑ n ∈ Ico 65280 65536, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-155265 : ℤ) ∧
    (∑ n ∈ Ico 65280 65536, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-3105365761574279003899902045 : ℤ) := by
  rcases cdemPrefixStats_65280_65408 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_65408_65536 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 65280 ≤ 65408) (by norm_num : 65408 ≤ 65536), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 65280 ≤ 65408) (by norm_num : 65408 ≤ 65536), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 65280 ≤ 65408) (by norm_num : 65408 ≤ 65536), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 65280 ≤ 65408) (by norm_num : 65408 ≤ 65536), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_65024_65536 :
    (∑ n ∈ Ico 65024 65536, mobiusTreeValue 16 mobiusTable1200001 n) = (-2 : ℤ) ∧
    (∑ n ∈ Ico 65024 65536, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (312 : ℕ) ∧
    (∑ n ∈ Ico 65024 65536, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-156844 : ℤ) ∧
    (∑ n ∈ Ico 65024 65536, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-3136844758416581005747880384 : ℤ) := by
  rcases cdemPrefixStats_65024_65280 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_65280_65536 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 65024 ≤ 65280) (by norm_num : 65280 ≤ 65536), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 65024 ≤ 65280) (by norm_num : 65280 ≤ 65536), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 65024 ≤ 65280) (by norm_num : 65280 ≤ 65536), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 65024 ≤ 65280) (by norm_num : 65280 ≤ 65536), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_64512_65536 :
    (∑ n ∈ Ico 64512 65536, mobiusTreeValue 16 mobiusTable1200001 n) = (45 : ℤ) ∧
    (∑ n ∈ Ico 64512 65536, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (623 : ℕ) ∧
    (∑ n ∈ Ico 64512 65536, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (3471479 : ℤ) ∧
    (∑ n ∈ Ico 64512 65536, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (69430160359678002195697413841 : ℤ) := by
  rcases cdemPrefixStats_64512_65024 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_65024_65536 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 64512 ≤ 65024) (by norm_num : 65024 ≤ 65536), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 64512 ≤ 65024) (by norm_num : 65024 ≤ 65536), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 64512 ≤ 65024) (by norm_num : 65024 ≤ 65536), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 64512 ≤ 65024) (by norm_num : 65024 ≤ 65536), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_63488_65536 :
    (∑ n ∈ Ico 63488 65536, mobiusTreeValue 16 mobiusTable1200001 n) = (52 : ℤ) ∧
    (∑ n ∈ Ico 63488 65536, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (1246 : ℕ) ∧
    (∑ n ∈ Ico 63488 65536, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (3988374 : ℤ) ∧
    (∑ n ∈ Ico 63488 65536, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (79768077971386779710268816386 : ℤ) := by
  rcases cdemPrefixStats_63488_64512 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_64512_65536 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 63488 ≤ 64512) (by norm_num : 64512 ≤ 65536), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 63488 ≤ 64512) (by norm_num : 64512 ≤ 65536), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 63488 ≤ 64512) (by norm_num : 64512 ≤ 65536), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 63488 ≤ 64512) (by norm_num : 64512 ≤ 65536), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_61440_65536 :
    (∑ n ∈ Ico 61440 65536, mobiusTreeValue 16 mobiusTable1200001 n) = (68 : ℤ) ∧
    (∑ n ∈ Ico 61440 65536, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (2490 : ℕ) ∧
    (∑ n ∈ Ico 61440 65536, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (5252767 : ℤ) ∧
    (∑ n ∈ Ico 61440 65536, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (105056110765305202790018374012 : ℤ) := by
  rcases cdemPrefixStats_61440_63488 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_63488_65536 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 61440 ≤ 63488) (by norm_num : 63488 ≤ 65536), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 61440 ≤ 63488) (by norm_num : 63488 ≤ 65536), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 61440 ≤ 63488) (by norm_num : 63488 ≤ 65536), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 61440 ≤ 63488) (by norm_num : 63488 ≤ 65536), hR1, hR2] <;> norm_num

theorem cdemPrefixGroup015_checked_complete :
    (∑ n ∈ Ico 61440 65536, mobiusTreeValue 16 mobiusTable1200001 n) = (68 : ℤ) ∧
    (∑ n ∈ Ico 61440 65536, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (2490 : ℕ) ∧
    (∑ n ∈ Ico 61440 65536, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (5252767 : ℤ) ∧
    (∑ n ∈ Ico 61440 65536, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (105056110765305202790018374012 : ℤ) := cdemPrefixStats_61440_65536
end Helfgott
#print axioms Helfgott.cdemPrefixGroup015_checked_complete

open Helfgott Finset
open scoped BigOperators

theorem solution :
    (∑ n ∈ Ico 61440 65536, mobiusTreeValue 16 mobiusTable1200001 n) = (68 : ℤ) ∧
    (∑ n ∈ Ico 61440 65536, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (2490 : ℕ) ∧
    (∑ n ∈ Ico 61440 65536, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (5252767 : ℤ) ∧
    (∑ n ∈ Ico 61440 65536, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (105056110765305202790018374012 : ℤ) := Helfgott.cdemPrefixGroup015_checked_complete
#print axioms solution
