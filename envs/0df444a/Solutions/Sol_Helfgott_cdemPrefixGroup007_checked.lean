-- Prove2me | solution 1 for Helfgott.cdemPrefixGroup007_checked
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-09T01:28:50.401504+00:00
-- url     : https://prove2.me/submissions/819babfc-a54d-4a85-bf04-e7a99fbef4dd

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
private theorem cdemPrefixStats_28672_28736 :
    (∑ n ∈ Ico 28672 28736, mobiusTreeValue 16 mobiusTable1200001 n) = (-9 : ℤ) ∧
    (∑ n ∈ Ico 28672 28736, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 28672 28736, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-1566706 : ℤ) ∧
    (∑ n ∈ Ico 28672 28736, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-31334259891595877554432495622 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_28736_28800 :
    (∑ n ∈ Ico 28736 28800, mobiusTreeValue 16 mobiusTable1200001 n) = (-5 : ℤ) ∧
    (∑ n ∈ Ico 28736 28800, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 28736 28800, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-868471 : ℤ) ∧
    (∑ n ∈ Ico 28736 28800, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-17369428235021497640380490251 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_28672_28800 :
    (∑ n ∈ Ico 28672 28800, mobiusTreeValue 16 mobiusTable1200001 n) = (-14 : ℤ) ∧
    (∑ n ∈ Ico 28672 28800, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (74 : ℕ) ∧
    (∑ n ∈ Ico 28672 28800, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-2435177 : ℤ) ∧
    (∑ n ∈ Ico 28672 28800, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-48703688126617375194812985873 : ℤ) := by
  rcases cdemPrefixStats_28672_28736 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_28736_28800 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 28672 ≤ 28736) (by norm_num : 28736 ≤ 28800), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 28672 ≤ 28736) (by norm_num : 28736 ≤ 28800), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 28672 ≤ 28736) (by norm_num : 28736 ≤ 28800), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 28672 ≤ 28736) (by norm_num : 28736 ≤ 28800), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_28800_28864 :
    (∑ n ∈ Ico 28800 28864, mobiusTreeValue 16 mobiusTable1200001 n) = (-2 : ℤ) ∧
    (∑ n ∈ Ico 28800 28864, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 28800 28864, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-346245 : ℤ) ∧
    (∑ n ∈ Ico 28800 28864, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-6924946484137722806736284072 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_28864_28928 :
    (∑ n ∈ Ico 28864 28928, mobiusTreeValue 16 mobiusTable1200001 n) = (3 : ℤ) ∧
    (∑ n ∈ Ico 28864 28928, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 28864 28928, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (519378 : ℤ) ∧
    (∑ n ∈ Ico 28864 28928, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (10387560462495091363512887774 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_28800_28928 :
    (∑ n ∈ Ico 28800 28928, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 28800 28928, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 28800 28928, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (173133 : ℤ) ∧
    (∑ n ∈ Ico 28800 28928, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (3462613978357368556776603702 : ℤ) := by
  rcases cdemPrefixStats_28800_28864 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_28864_28928 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 28800 ≤ 28864) (by norm_num : 28864 ≤ 28928), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 28800 ≤ 28864) (by norm_num : 28864 ≤ 28928), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 28800 ≤ 28864) (by norm_num : 28864 ≤ 28928), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 28800 ≤ 28864) (by norm_num : 28864 ≤ 28928), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_28672_28928 :
    (∑ n ∈ Ico 28672 28928, mobiusTreeValue 16 mobiusTable1200001 n) = (-13 : ℤ) ∧
    (∑ n ∈ Ico 28672 28928, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (151 : ℕ) ∧
    (∑ n ∈ Ico 28672 28928, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-2262044 : ℤ) ∧
    (∑ n ∈ Ico 28672 28928, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-45241074148260006638036382171 : ℤ) := by
  rcases cdemPrefixStats_28672_28800 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_28800_28928 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 28672 ≤ 28800) (by norm_num : 28800 ≤ 28928), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 28672 ≤ 28800) (by norm_num : 28800 ≤ 28928), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 28672 ≤ 28800) (by norm_num : 28800 ≤ 28928), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 28672 ≤ 28800) (by norm_num : 28800 ≤ 28928), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_28928_28992 :
    (∑ n ∈ Ico 28928 28992, mobiusTreeValue 16 mobiusTable1200001 n) = (4 : ℤ) ∧
    (∑ n ∈ Ico 28928 28992, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 28928 28992, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (690593 : ℤ) ∧
    (∑ n ∈ Ico 28928 28992, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (13811932164735671555652387652 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_28992_29056 :
    (∑ n ∈ Ico 28992 29056, mobiusTreeValue 16 mobiusTable1200001 n) = (-2 : ℤ) ∧
    (∑ n ∈ Ico 28992 29056, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (42 : ℕ) ∧
    (∑ n ∈ Ico 28992 29056, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-344710 : ℤ) ∧
    (∑ n ∈ Ico 28992 29056, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-6894283069327576981575594417 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_28928_29056 :
    (∑ n ∈ Ico 28928 29056, mobiusTreeValue 16 mobiusTable1200001 n) = (2 : ℤ) ∧
    (∑ n ∈ Ico 28928 29056, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (82 : ℕ) ∧
    (∑ n ∈ Ico 28928 29056, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (345883 : ℤ) ∧
    (∑ n ∈ Ico 28928 29056, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (6917649095408094574076793235 : ℤ) := by
  rcases cdemPrefixStats_28928_28992 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_28992_29056 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 28928 ≤ 28992) (by norm_num : 28992 ≤ 29056), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 28928 ≤ 28992) (by norm_num : 28992 ≤ 29056), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 28928 ≤ 28992) (by norm_num : 28992 ≤ 29056), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 28928 ≤ 28992) (by norm_num : 28992 ≤ 29056), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_29056_29120 :
    (∑ n ∈ Ico 29056 29120, mobiusTreeValue 16 mobiusTable1200001 n) = (19 : ℤ) ∧
    (∑ n ∈ Ico 29056 29120, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 29056 29120, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (3265062 : ℤ) ∧
    (∑ n ∈ Ico 29056 29120, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (65301447308766412044211852924 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_29120_29184 :
    (∑ n ∈ Ico 29120 29184, mobiusTreeValue 16 mobiusTable1200001 n) = (-6 : ℤ) ∧
    (∑ n ∈ Ico 29120 29184, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 29120 29184, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-1028657 : ℤ) ∧
    (∑ n ∈ Ico 29120 29184, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-20573200931377952864566601823 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_29056_29184 :
    (∑ n ∈ Ico 29056 29184, mobiusTreeValue 16 mobiusTable1200001 n) = (13 : ℤ) ∧
    (∑ n ∈ Ico 29056 29184, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 29056 29184, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (2236405 : ℤ) ∧
    (∑ n ∈ Ico 29056 29184, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (44728246377388459179645251101 : ℤ) := by
  rcases cdemPrefixStats_29056_29120 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_29120_29184 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 29056 ≤ 29120) (by norm_num : 29120 ≤ 29184), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 29056 ≤ 29120) (by norm_num : 29120 ≤ 29184), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 29056 ≤ 29120) (by norm_num : 29120 ≤ 29184), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 29056 ≤ 29120) (by norm_num : 29120 ≤ 29184), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_28928_29184 :
    (∑ n ∈ Ico 28928 29184, mobiusTreeValue 16 mobiusTable1200001 n) = (15 : ℤ) ∧
    (∑ n ∈ Ico 28928 29184, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (159 : ℕ) ∧
    (∑ n ∈ Ico 28928 29184, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (2582288 : ℤ) ∧
    (∑ n ∈ Ico 28928 29184, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (51645895472796553753722044336 : ℤ) := by
  rcases cdemPrefixStats_28928_29056 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_29056_29184 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 28928 ≤ 29056) (by norm_num : 29056 ≤ 29184), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 28928 ≤ 29056) (by norm_num : 29056 ≤ 29184), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 28928 ≤ 29056) (by norm_num : 29056 ≤ 29184), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 28928 ≤ 29056) (by norm_num : 29056 ≤ 29184), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_28672_29184 :
    (∑ n ∈ Ico 28672 29184, mobiusTreeValue 16 mobiusTable1200001 n) = (2 : ℤ) ∧
    (∑ n ∈ Ico 28672 29184, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (310 : ℕ) ∧
    (∑ n ∈ Ico 28672 29184, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (320244 : ℤ) ∧
    (∑ n ∈ Ico 28672 29184, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (6404821324536547115685662165 : ℤ) := by
  rcases cdemPrefixStats_28672_28928 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_28928_29184 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 28672 ≤ 28928) (by norm_num : 28928 ≤ 29184), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 28672 ≤ 28928) (by norm_num : 28928 ≤ 29184), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 28672 ≤ 28928) (by norm_num : 28928 ≤ 29184), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 28672 ≤ 28928) (by norm_num : 28928 ≤ 29184), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_29184_29248 :
    (∑ n ∈ Ico 29184 29248, mobiusTreeValue 16 mobiusTable1200001 n) = (-4 : ℤ) ∧
    (∑ n ∈ Ico 29184 29248, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 29184 29248, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-685403 : ℤ) ∧
    (∑ n ∈ Ico 29184 29248, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-13708122334118649056486004629 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_29248_29312 :
    (∑ n ∈ Ico 29248 29312, mobiusTreeValue 16 mobiusTable1200001 n) = (3 : ℤ) ∧
    (∑ n ∈ Ico 29248 29312, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 29248 29312, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (512310 : ℤ) ∧
    (∑ n ∈ Ico 29248 29312, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (10246266674013009820688917108 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_29184_29312 :
    (∑ n ∈ Ico 29184 29312, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 29184 29312, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (79 : ℕ) ∧
    (∑ n ∈ Ico 29184 29312, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-173093 : ℤ) ∧
    (∑ n ∈ Ico 29184 29312, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-3461855660105639235797087521 : ℤ) := by
  rcases cdemPrefixStats_29184_29248 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_29248_29312 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 29184 ≤ 29248) (by norm_num : 29248 ≤ 29312), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 29184 ≤ 29248) (by norm_num : 29248 ≤ 29312), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 29184 ≤ 29248) (by norm_num : 29248 ≤ 29312), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 29184 ≤ 29248) (by norm_num : 29248 ≤ 29312), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_29312_29376 :
    (∑ n ∈ Ico 29312 29376, mobiusTreeValue 16 mobiusTable1200001 n) = (4 : ℤ) ∧
    (∑ n ∈ Ico 29312 29376, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 29312 29376, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (681828 : ℤ) ∧
    (∑ n ∈ Ico 29312 29376, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (13636640454616300648082757348 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_29376_29440 :
    (∑ n ∈ Ico 29376 29440, mobiusTreeValue 16 mobiusTable1200001 n) = (-3 : ℤ) ∧
    (∑ n ∈ Ico 29376 29440, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 29376 29440, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-510400 : ℤ) ∧
    (∑ n ∈ Ico 29376 29440, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-10208022217261400477230840248 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_29312_29440 :
    (∑ n ∈ Ico 29312 29440, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 29312 29440, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 29312 29440, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (171428 : ℤ) ∧
    (∑ n ∈ Ico 29312 29440, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (3428618237354900170851917100 : ℤ) := by
  rcases cdemPrefixStats_29312_29376 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_29376_29440 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 29312 ≤ 29376) (by norm_num : 29376 ≤ 29440), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 29312 ≤ 29376) (by norm_num : 29376 ≤ 29440), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 29312 ≤ 29376) (by norm_num : 29376 ≤ 29440), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 29312 ≤ 29376) (by norm_num : 29376 ≤ 29440), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_29184_29440 :
    (∑ n ∈ Ico 29184 29440, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 29184 29440, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (156 : ℕ) ∧
    (∑ n ∈ Ico 29184 29440, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-1665 : ℤ) ∧
    (∑ n ∈ Ico 29184 29440, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-33237422750739064945170421 : ℤ) := by
  rcases cdemPrefixStats_29184_29312 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_29312_29440 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 29184 ≤ 29312) (by norm_num : 29312 ≤ 29440), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 29184 ≤ 29312) (by norm_num : 29312 ≤ 29440), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 29184 ≤ 29312) (by norm_num : 29312 ≤ 29440), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 29184 ≤ 29312) (by norm_num : 29312 ≤ 29440), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_29440_29504 :
    (∑ n ∈ Ico 29440 29504, mobiusTreeValue 16 mobiusTable1200001 n) = (15 : ℤ) ∧
    (∑ n ∈ Ico 29440 29504, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 29440 29504, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (2545084 : ℤ) ∧
    (∑ n ∈ Ico 29440 29504, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (50901771772242520323769356241 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_29504_29568 :
    (∑ n ∈ Ico 29504 29568, mobiusTreeValue 16 mobiusTable1200001 n) = (9 : ℤ) ∧
    (∑ n ∈ Ico 29504 29568, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 29504 29568, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (1524539 : ℤ) ∧
    (∑ n ∈ Ico 29504 29568, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (30490910126371799950091654525 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_29440_29568 :
    (∑ n ∈ Ico 29440 29568, mobiusTreeValue 16 mobiusTable1200001 n) = (24 : ℤ) ∧
    (∑ n ∈ Ico 29440 29568, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (80 : ℕ) ∧
    (∑ n ∈ Ico 29440 29568, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (4069623 : ℤ) ∧
    (∑ n ∈ Ico 29440 29568, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (81392681898614320273861010766 : ℤ) := by
  rcases cdemPrefixStats_29440_29504 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_29504_29568 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 29440 ≤ 29504) (by norm_num : 29504 ≤ 29568), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 29440 ≤ 29504) (by norm_num : 29504 ≤ 29568), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 29440 ≤ 29504) (by norm_num : 29504 ≤ 29568), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 29440 ≤ 29504) (by norm_num : 29504 ≤ 29568), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_29568_29632 :
    (∑ n ∈ Ico 29568 29632, mobiusTreeValue 16 mobiusTable1200001 n) = (-4 : ℤ) ∧
    (∑ n ∈ Ico 29568 29632, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 29568 29632, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-676341 : ℤ) ∧
    (∑ n ∈ Ico 29568 29632, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-13526876295770300812812291668 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_29632_29696 :
    (∑ n ∈ Ico 29632 29696, mobiusTreeValue 16 mobiusTable1200001 n) = (8 : ℤ) ∧
    (∑ n ∈ Ico 29632 29696, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 29632 29696, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (1348740 : ℤ) ∧
    (∑ n ∈ Ico 29632 29696, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (26974870955345299160629727558 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_29568_29696 :
    (∑ n ∈ Ico 29568 29696, mobiusTreeValue 16 mobiusTable1200001 n) = (4 : ℤ) ∧
    (∑ n ∈ Ico 29568 29696, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 29568 29696, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (672399 : ℤ) ∧
    (∑ n ∈ Ico 29568 29696, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (13447994659574998347817435890 : ℤ) := by
  rcases cdemPrefixStats_29568_29632 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_29632_29696 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 29568 ≤ 29632) (by norm_num : 29632 ≤ 29696), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 29568 ≤ 29632) (by norm_num : 29632 ≤ 29696), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 29568 ≤ 29632) (by norm_num : 29632 ≤ 29696), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 29568 ≤ 29632) (by norm_num : 29632 ≤ 29696), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_29440_29696 :
    (∑ n ∈ Ico 29440 29696, mobiusTreeValue 16 mobiusTable1200001 n) = (28 : ℤ) ∧
    (∑ n ∈ Ico 29440 29696, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (158 : ℕ) ∧
    (∑ n ∈ Ico 29440 29696, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (4742022 : ℤ) ∧
    (∑ n ∈ Ico 29440 29696, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (94840676558189318621678446656 : ℤ) := by
  rcases cdemPrefixStats_29440_29568 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_29568_29696 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 29440 ≤ 29568) (by norm_num : 29568 ≤ 29696), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 29440 ≤ 29568) (by norm_num : 29568 ≤ 29696), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 29440 ≤ 29568) (by norm_num : 29568 ≤ 29696), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 29440 ≤ 29568) (by norm_num : 29568 ≤ 29696), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_29184_29696 :
    (∑ n ∈ Ico 29184 29696, mobiusTreeValue 16 mobiusTable1200001 n) = (28 : ℤ) ∧
    (∑ n ∈ Ico 29184 29696, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (314 : ℕ) ∧
    (∑ n ∈ Ico 29184 29696, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (4740357 : ℤ) ∧
    (∑ n ∈ Ico 29184 29696, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (94807439135438579556733276235 : ℤ) := by
  rcases cdemPrefixStats_29184_29440 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_29440_29696 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 29184 ≤ 29440) (by norm_num : 29440 ≤ 29696), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 29184 ≤ 29440) (by norm_num : 29440 ≤ 29696), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 29184 ≤ 29440) (by norm_num : 29440 ≤ 29696), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 29184 ≤ 29440) (by norm_num : 29440 ≤ 29696), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_28672_29696 :
    (∑ n ∈ Ico 28672 29696, mobiusTreeValue 16 mobiusTable1200001 n) = (30 : ℤ) ∧
    (∑ n ∈ Ico 28672 29696, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (624 : ℕ) ∧
    (∑ n ∈ Ico 28672 29696, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (5060601 : ℤ) ∧
    (∑ n ∈ Ico 28672 29696, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (101212260459975126672418938400 : ℤ) := by
  rcases cdemPrefixStats_28672_29184 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_29184_29696 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 28672 ≤ 29184) (by norm_num : 29184 ≤ 29696), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 28672 ≤ 29184) (by norm_num : 29184 ≤ 29696), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 28672 ≤ 29184) (by norm_num : 29184 ≤ 29696), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 28672 ≤ 29184) (by norm_num : 29184 ≤ 29696), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_29696_29760 :
    (∑ n ∈ Ico 29696 29760, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 29696 29760, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 29696 29760, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (234 : ℤ) ∧
    (∑ n ∈ Ico 29696 29760, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (4636002521230665588487036 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_29760_29824 :
    (∑ n ∈ Ico 29760 29824, mobiusTreeValue 16 mobiusTable1200001 n) = (7 : ℤ) ∧
    (∑ n ∈ Ico 29760 29824, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 29760 29824, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (1175432 : ℤ) ∧
    (∑ n ∈ Ico 29760 29824, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (23508755550738182215768620475 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_29696_29824 :
    (∑ n ∈ Ico 29696 29824, mobiusTreeValue 16 mobiusTable1200001 n) = (7 : ℤ) ∧
    (∑ n ∈ Ico 29696 29824, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (79 : ℕ) ∧
    (∑ n ∈ Ico 29696 29824, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (1175666 : ℤ) ∧
    (∑ n ∈ Ico 29696 29824, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (23513391553259412881357107511 : ℤ) := by
  rcases cdemPrefixStats_29696_29760 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_29760_29824 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 29696 ≤ 29760) (by norm_num : 29760 ≤ 29824), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 29696 ≤ 29760) (by norm_num : 29760 ≤ 29824), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 29696 ≤ 29760) (by norm_num : 29760 ≤ 29824), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 29696 ≤ 29760) (by norm_num : 29760 ≤ 29824), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_29824_29888 :
    (∑ n ∈ Ico 29824 29888, mobiusTreeValue 16 mobiusTable1200001 n) = (-4 : ℤ) ∧
    (∑ n ∈ Ico 29824 29888, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 29824 29888, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-669271 : ℤ) ∧
    (∑ n ∈ Ico 29824 29888, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-13385423176187118642378706304 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_29888_29952 :
    (∑ n ∈ Ico 29888 29952, mobiusTreeValue 16 mobiusTable1200001 n) = (5 : ℤ) ∧
    (∑ n ∈ Ico 29888 29952, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 29888 29952, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (836926 : ℤ) ∧
    (∑ n ∈ Ico 29888 29952, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (16738606424519681846212602629 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_29824_29952 :
    (∑ n ∈ Ico 29824 29952, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 29824 29952, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (75 : ℕ) ∧
    (∑ n ∈ Ico 29824 29952, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (167655 : ℤ) ∧
    (∑ n ∈ Ico 29824 29952, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (3353183248332563203833896325 : ℤ) := by
  rcases cdemPrefixStats_29824_29888 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_29888_29952 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 29824 ≤ 29888) (by norm_num : 29888 ≤ 29952), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 29824 ≤ 29888) (by norm_num : 29888 ≤ 29952), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 29824 ≤ 29888) (by norm_num : 29888 ≤ 29952), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 29824 ≤ 29888) (by norm_num : 29888 ≤ 29952), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_29696_29952 :
    (∑ n ∈ Ico 29696 29952, mobiusTreeValue 16 mobiusTable1200001 n) = (8 : ℤ) ∧
    (∑ n ∈ Ico 29696 29952, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (154 : ℕ) ∧
    (∑ n ∈ Ico 29696 29952, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (1343321 : ℤ) ∧
    (∑ n ∈ Ico 29696 29952, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (26866574801591976085191003836 : ℤ) := by
  rcases cdemPrefixStats_29696_29824 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_29824_29952 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 29696 ≤ 29824) (by norm_num : 29824 ≤ 29952), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 29696 ≤ 29824) (by norm_num : 29824 ≤ 29952), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 29696 ≤ 29824) (by norm_num : 29824 ≤ 29952), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 29696 ≤ 29824) (by norm_num : 29824 ≤ 29952), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_29952_30016 :
    (∑ n ∈ Ico 29952 30016, mobiusTreeValue 16 mobiusTable1200001 n) = (-16 : ℤ) ∧
    (∑ n ∈ Ico 29952 30016, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 29952 30016, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-2668018 : ℤ) ∧
    (∑ n ∈ Ico 29952 30016, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-53360489776182576520311172669 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_30016_30080 :
    (∑ n ∈ Ico 30016 30080, mobiusTreeValue 16 mobiusTable1200001 n) = (7 : ℤ) ∧
    (∑ n ∈ Ico 30016 30080, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 30016 30080, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (1165608 : ℤ) ∧
    (∑ n ∈ Ico 30016 30080, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (23312242774930373623880599087 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_29952_30080 :
    (∑ n ∈ Ico 29952 30080, mobiusTreeValue 16 mobiusTable1200001 n) = (-9 : ℤ) ∧
    (∑ n ∈ Ico 29952 30080, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (79 : ℕ) ∧
    (∑ n ∈ Ico 29952 30080, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-1502410 : ℤ) ∧
    (∑ n ∈ Ico 29952 30080, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-30048247001252202896430573582 : ℤ) := by
  rcases cdemPrefixStats_29952_30016 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_30016_30080 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 29952 ≤ 30016) (by norm_num : 30016 ≤ 30080), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 29952 ≤ 30016) (by norm_num : 30016 ≤ 30080), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 29952 ≤ 30016) (by norm_num : 30016 ≤ 30080), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 29952 ≤ 30016) (by norm_num : 30016 ≤ 30080), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_30080_30144 :
    (∑ n ∈ Ico 30080 30144, mobiusTreeValue 16 mobiusTable1200001 n) = (-11 : ℤ) ∧
    (∑ n ∈ Ico 30080 30144, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 30080 30144, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-1827223 : ℤ) ∧
    (∑ n ∈ Ico 30080 30144, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-36544531806558837784788755204 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_30144_30208 :
    (∑ n ∈ Ico 30144 30208, mobiusTreeValue 16 mobiusTable1200001 n) = (-3 : ℤ) ∧
    (∑ n ∈ Ico 30144 30208, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 30144 30208, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-496640 : ℤ) ∧
    (∑ n ∈ Ico 30144 30208, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-9932781918069844953275400537 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_30080_30208 :
    (∑ n ∈ Ico 30080 30208, mobiusTreeValue 16 mobiusTable1200001 n) = (-14 : ℤ) ∧
    (∑ n ∈ Ico 30080 30208, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 30080 30208, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-2323863 : ℤ) ∧
    (∑ n ∈ Ico 30080 30208, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-46477313724628682738064155741 : ℤ) := by
  rcases cdemPrefixStats_30080_30144 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_30144_30208 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 30080 ≤ 30144) (by norm_num : 30144 ≤ 30208), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 30080 ≤ 30144) (by norm_num : 30144 ≤ 30208), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 30080 ≤ 30144) (by norm_num : 30144 ≤ 30208), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 30080 ≤ 30144) (by norm_num : 30144 ≤ 30208), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_29952_30208 :
    (∑ n ∈ Ico 29952 30208, mobiusTreeValue 16 mobiusTable1200001 n) = (-23 : ℤ) ∧
    (∑ n ∈ Ico 29952 30208, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (157 : ℕ) ∧
    (∑ n ∈ Ico 29952 30208, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-3826273 : ℤ) ∧
    (∑ n ∈ Ico 29952 30208, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-76525560725880885634494729323 : ℤ) := by
  rcases cdemPrefixStats_29952_30080 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_30080_30208 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 29952 ≤ 30080) (by norm_num : 30080 ≤ 30208), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 29952 ≤ 30080) (by norm_num : 30080 ≤ 30208), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 29952 ≤ 30080) (by norm_num : 30080 ≤ 30208), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 29952 ≤ 30080) (by norm_num : 30080 ≤ 30208), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_29696_30208 :
    (∑ n ∈ Ico 29696 30208, mobiusTreeValue 16 mobiusTable1200001 n) = (-15 : ℤ) ∧
    (∑ n ∈ Ico 29696 30208, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (311 : ℕ) ∧
    (∑ n ∈ Ico 29696 30208, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-2482952 : ℤ) ∧
    (∑ n ∈ Ico 29696 30208, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-49658985924288909549303725487 : ℤ) := by
  rcases cdemPrefixStats_29696_29952 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_29952_30208 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 29696 ≤ 29952) (by norm_num : 29952 ≤ 30208), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 29696 ≤ 29952) (by norm_num : 29952 ≤ 30208), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 29696 ≤ 29952) (by norm_num : 29952 ≤ 30208), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 29696 ≤ 29952) (by norm_num : 29952 ≤ 30208), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_30208_30272 :
    (∑ n ∈ Ico 30208 30272, mobiusTreeValue 16 mobiusTable1200001 n) = (-5 : ℤ) ∧
    (∑ n ∈ Ico 30208 30272, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 30208 30272, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-826774 : ℤ) ∧
    (∑ n ∈ Ico 30208 30272, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-16535597916646143027730055955 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_30272_30336 :
    (∑ n ∈ Ico 30272 30336, mobiusTreeValue 16 mobiusTable1200001 n) = (7 : ℤ) ∧
    (∑ n ∈ Ico 30272 30336, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 30272 30336, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (1155734 : ℤ) ∧
    (∑ n ∈ Ico 30272 30336, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (23114737477577196355153989576 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_30208_30336 :
    (∑ n ∈ Ico 30208 30336, mobiusTreeValue 16 mobiusTable1200001 n) = (2 : ℤ) ∧
    (∑ n ∈ Ico 30208 30336, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (76 : ℕ) ∧
    (∑ n ∈ Ico 30208 30336, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (328960 : ℤ) ∧
    (∑ n ∈ Ico 30208 30336, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (6579139560931053327423933621 : ℤ) := by
  rcases cdemPrefixStats_30208_30272 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_30272_30336 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 30208 ≤ 30272) (by norm_num : 30272 ≤ 30336), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 30208 ≤ 30272) (by norm_num : 30272 ≤ 30336), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 30208 ≤ 30272) (by norm_num : 30272 ≤ 30336), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 30208 ≤ 30272) (by norm_num : 30272 ≤ 30336), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_30336_30400 :
    (∑ n ∈ Ico 30336 30400, mobiusTreeValue 16 mobiusTable1200001 n) = (8 : ℤ) ∧
    (∑ n ∈ Ico 30336 30400, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 30336 30400, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (1316585 : ℤ) ∧
    (∑ n ∈ Ico 30336 30400, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (26331828504556202726567164524 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_30400_30464 :
    (∑ n ∈ Ico 30400 30464, mobiusTreeValue 16 mobiusTable1200001 n) = (9 : ℤ) ∧
    (∑ n ∈ Ico 30400 30464, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 30400 30464, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (1478356 : ℤ) ∧
    (∑ n ∈ Ico 30400 30464, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (29567224632419012747240619543 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_30336_30464 :
    (∑ n ∈ Ico 30336 30464, mobiusTreeValue 16 mobiusTable1200001 n) = (17 : ℤ) ∧
    (∑ n ∈ Ico 30336 30464, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (81 : ℕ) ∧
    (∑ n ∈ Ico 30336 30464, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (2794941 : ℤ) ∧
    (∑ n ∈ Ico 30336 30464, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (55899053136975215473807784067 : ℤ) := by
  rcases cdemPrefixStats_30336_30400 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_30400_30464 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 30336 ≤ 30400) (by norm_num : 30400 ≤ 30464), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 30336 ≤ 30400) (by norm_num : 30400 ≤ 30464), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 30336 ≤ 30400) (by norm_num : 30400 ≤ 30464), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 30336 ≤ 30400) (by norm_num : 30400 ≤ 30464), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_30208_30464 :
    (∑ n ∈ Ico 30208 30464, mobiusTreeValue 16 mobiusTable1200001 n) = (19 : ℤ) ∧
    (∑ n ∈ Ico 30208 30464, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (157 : ℕ) ∧
    (∑ n ∈ Ico 30208 30464, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (3123901 : ℤ) ∧
    (∑ n ∈ Ico 30208 30464, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (62478192697906268801231717688 : ℤ) := by
  rcases cdemPrefixStats_30208_30336 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_30336_30464 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 30208 ≤ 30336) (by norm_num : 30336 ≤ 30464), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 30208 ≤ 30336) (by norm_num : 30336 ≤ 30464), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 30208 ≤ 30336) (by norm_num : 30336 ≤ 30464), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 30208 ≤ 30336) (by norm_num : 30336 ≤ 30464), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_30464_30528 :
    (∑ n ∈ Ico 30464 30528, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 30464 30528, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 30464 30528, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-17 : ℤ) ∧
    (∑ n ∈ Ico 30464 30528, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-315597499539433291123368 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_30528_30592 :
    (∑ n ∈ Ico 30528 30592, mobiusTreeValue 16 mobiusTable1200001 n) = (7 : ℤ) ∧
    (∑ n ∈ Ico 30528 30592, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 30528 30592, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (1145851 : ℤ) ∧
    (∑ n ∈ Ico 30528 30592, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (22917115068459026970799165067 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_30464_30592 :
    (∑ n ∈ Ico 30464 30592, mobiusTreeValue 16 mobiusTable1200001 n) = (7 : ℤ) ∧
    (∑ n ∈ Ico 30464 30592, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 30464 30592, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (1145834 : ℤ) ∧
    (∑ n ∈ Ico 30464 30592, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (22916799470959487537508041699 : ℤ) := by
  rcases cdemPrefixStats_30464_30528 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_30528_30592 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 30464 ≤ 30528) (by norm_num : 30528 ≤ 30592), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 30464 ≤ 30528) (by norm_num : 30528 ≤ 30592), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 30464 ≤ 30528) (by norm_num : 30528 ≤ 30592), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 30464 ≤ 30528) (by norm_num : 30528 ≤ 30592), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_30592_30656 :
    (∑ n ∈ Ico 30592 30656, mobiusTreeValue 16 mobiusTable1200001 n) = (6 : ℤ) ∧
    (∑ n ∈ Ico 30592 30656, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 30592 30656, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (980216 : ℤ) ∧
    (∑ n ∈ Ico 30592 30656, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (19604419115409667773651831268 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_30656_30720 :
    (∑ n ∈ Ico 30656 30720, mobiusTreeValue 16 mobiusTable1200001 n) = (-9 : ℤ) ∧
    (∑ n ∈ Ico 30656 30720, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 30656 30720, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-1465940 : ℤ) ∧
    (∑ n ∈ Ico 30656 30720, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-29318937839845189667686972647 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_30592_30720 :
    (∑ n ∈ Ico 30592 30720, mobiusTreeValue 16 mobiusTable1200001 n) = (-3 : ℤ) ∧
    (∑ n ∈ Ico 30592 30720, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 30592 30720, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-485724 : ℤ) ∧
    (∑ n ∈ Ico 30592 30720, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-9714518724435521894035141379 : ℤ) := by
  rcases cdemPrefixStats_30592_30656 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_30656_30720 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 30592 ≤ 30656) (by norm_num : 30656 ≤ 30720), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 30592 ≤ 30656) (by norm_num : 30656 ≤ 30720), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 30592 ≤ 30656) (by norm_num : 30656 ≤ 30720), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 30592 ≤ 30656) (by norm_num : 30656 ≤ 30720), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_30464_30720 :
    (∑ n ∈ Ico 30464 30720, mobiusTreeValue 16 mobiusTable1200001 n) = (4 : ℤ) ∧
    (∑ n ∈ Ico 30464 30720, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (154 : ℕ) ∧
    (∑ n ∈ Ico 30464 30720, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (660110 : ℤ) ∧
    (∑ n ∈ Ico 30464 30720, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (13202280746523965643472900320 : ℤ) := by
  rcases cdemPrefixStats_30464_30592 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_30592_30720 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 30464 ≤ 30592) (by norm_num : 30592 ≤ 30720), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 30464 ≤ 30592) (by norm_num : 30592 ≤ 30720), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 30464 ≤ 30592) (by norm_num : 30592 ≤ 30720), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 30464 ≤ 30592) (by norm_num : 30592 ≤ 30720), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_30208_30720 :
    (∑ n ∈ Ico 30208 30720, mobiusTreeValue 16 mobiusTable1200001 n) = (23 : ℤ) ∧
    (∑ n ∈ Ico 30208 30720, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (311 : ℕ) ∧
    (∑ n ∈ Ico 30208 30720, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (3784011 : ℤ) ∧
    (∑ n ∈ Ico 30208 30720, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (75680473444430234444704618008 : ℤ) := by
  rcases cdemPrefixStats_30208_30464 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_30464_30720 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 30208 ≤ 30464) (by norm_num : 30464 ≤ 30720), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 30208 ≤ 30464) (by norm_num : 30464 ≤ 30720), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 30208 ≤ 30464) (by norm_num : 30464 ≤ 30720), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 30208 ≤ 30464) (by norm_num : 30464 ≤ 30720), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_29696_30720 :
    (∑ n ∈ Ico 29696 30720, mobiusTreeValue 16 mobiusTable1200001 n) = (8 : ℤ) ∧
    (∑ n ∈ Ico 29696 30720, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (622 : ℕ) ∧
    (∑ n ∈ Ico 29696 30720, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (1301059 : ℤ) ∧
    (∑ n ∈ Ico 29696 30720, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (26021487520141324895400892521 : ℤ) := by
  rcases cdemPrefixStats_29696_30208 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_30208_30720 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 29696 ≤ 30208) (by norm_num : 30208 ≤ 30720), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 29696 ≤ 30208) (by norm_num : 30208 ≤ 30720), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 29696 ≤ 30208) (by norm_num : 30208 ≤ 30720), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 29696 ≤ 30208) (by norm_num : 30208 ≤ 30720), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_28672_30720 :
    (∑ n ∈ Ico 28672 30720, mobiusTreeValue 16 mobiusTable1200001 n) = (38 : ℤ) ∧
    (∑ n ∈ Ico 28672 30720, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (1246 : ℕ) ∧
    (∑ n ∈ Ico 28672 30720, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (6361660 : ℤ) ∧
    (∑ n ∈ Ico 28672 30720, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (127233747980116451567819830921 : ℤ) := by
  rcases cdemPrefixStats_28672_29696 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_29696_30720 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 28672 ≤ 29696) (by norm_num : 29696 ≤ 30720), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 28672 ≤ 29696) (by norm_num : 29696 ≤ 30720), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 28672 ≤ 29696) (by norm_num : 29696 ≤ 30720), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 28672 ≤ 29696) (by norm_num : 29696 ≤ 30720), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_30720_30784 :
    (∑ n ∈ Ico 30720 30784, mobiusTreeValue 16 mobiusTable1200001 n) = (17 : ℤ) ∧
    (∑ n ∈ Ico 30720 30784, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 30720 30784, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (2764591 : ℤ) ∧
    (∑ n ∈ Ico 30720 30784, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (55291971266895305323043805342 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_30784_30848 :
    (∑ n ∈ Ico 30784 30848, mobiusTreeValue 16 mobiusTable1200001 n) = (-5 : ℤ) ∧
    (∑ n ∈ Ico 30784 30848, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 30784 30848, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-811017 : ℤ) ∧
    (∑ n ∈ Ico 30784 30848, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-16220398072865280534898177505 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_30720_30848 :
    (∑ n ∈ Ico 30720 30848, mobiusTreeValue 16 mobiusTable1200001 n) = (12 : ℤ) ∧
    (∑ n ∈ Ico 30720 30848, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 30720 30848, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (1953574 : ℤ) ∧
    (∑ n ∈ Ico 30720 30848, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (39071573194030024788145627837 : ℤ) := by
  rcases cdemPrefixStats_30720_30784 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_30784_30848 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 30720 ≤ 30784) (by norm_num : 30784 ≤ 30848), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 30720 ≤ 30784) (by norm_num : 30784 ≤ 30848), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 30720 ≤ 30784) (by norm_num : 30784 ≤ 30848), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 30720 ≤ 30784) (by norm_num : 30784 ≤ 30848), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_30848_30912 :
    (∑ n ∈ Ico 30848 30912, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 30848 30912, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 30848 30912, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (161813 : ℤ) ∧
    (∑ n ∈ Ico 30848 30912, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (3236253186304573625378086378 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_30912_30976 :
    (∑ n ∈ Ico 30912 30976, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 30912 30976, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (36 : ℕ) ∧
    (∑ n ∈ Ico 30912 30976, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (267 : ℤ) ∧
    (∑ n ∈ Ico 30912 30976, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (5334853038539786059613050 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_30848_30976 :
    (∑ n ∈ Ico 30848 30976, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 30848 30976, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (75 : ℕ) ∧
    (∑ n ∈ Ico 30848 30976, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (162080 : ℤ) ∧
    (∑ n ∈ Ico 30848 30976, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (3241588039343113411437699428 : ℤ) := by
  rcases cdemPrefixStats_30848_30912 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_30912_30976 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 30848 ≤ 30912) (by norm_num : 30912 ≤ 30976), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 30848 ≤ 30912) (by norm_num : 30912 ≤ 30976), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 30848 ≤ 30912) (by norm_num : 30912 ≤ 30976), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 30848 ≤ 30912) (by norm_num : 30912 ≤ 30976), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_30720_30976 :
    (∑ n ∈ Ico 30720 30976, mobiusTreeValue 16 mobiusTable1200001 n) = (13 : ℤ) ∧
    (∑ n ∈ Ico 30720 30976, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (153 : ℕ) ∧
    (∑ n ∈ Ico 30720 30976, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (2115654 : ℤ) ∧
    (∑ n ∈ Ico 30720 30976, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (42313161233373138199583327265 : ℤ) := by
  rcases cdemPrefixStats_30720_30848 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_30848_30976 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 30720 ≤ 30848) (by norm_num : 30848 ≤ 30976), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 30720 ≤ 30848) (by norm_num : 30848 ≤ 30976), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 30720 ≤ 30848) (by norm_num : 30848 ≤ 30976), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 30720 ≤ 30848) (by norm_num : 30848 ≤ 30976), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_30976_31040 :
    (∑ n ∈ Ico 30976 31040, mobiusTreeValue 16 mobiusTable1200001 n) = (5 : ℤ) ∧
    (∑ n ∈ Ico 30976 31040, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 30976 31040, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (806425 : ℤ) ∧
    (∑ n ∈ Ico 30976 31040, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (16128509459570407312251933795 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_31040_31104 :
    (∑ n ∈ Ico 31040 31104, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 31040 31104, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 31040 31104, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (308 : ℤ) ∧
    (∑ n ∈ Ico 31040 31104, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (6220240758596206787422294 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_30976_31104 :
    (∑ n ∈ Ico 30976 31104, mobiusTreeValue 16 mobiusTable1200001 n) = (5 : ℤ) ∧
    (∑ n ∈ Ico 30976 31104, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (79 : ℕ) ∧
    (∑ n ∈ Ico 30976 31104, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (806733 : ℤ) ∧
    (∑ n ∈ Ico 30976 31104, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (16134729700329003519039356089 : ℤ) := by
  rcases cdemPrefixStats_30976_31040 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_31040_31104 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 30976 ≤ 31040) (by norm_num : 31040 ≤ 31104), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 30976 ≤ 31040) (by norm_num : 31040 ≤ 31104), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 30976 ≤ 31040) (by norm_num : 31040 ≤ 31104), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 30976 ≤ 31040) (by norm_num : 31040 ≤ 31104), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_31104_31168 :
    (∑ n ∈ Ico 31104 31168, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 31104 31168, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 31104 31168, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (95 : ℤ) ∧
    (∑ n ∈ Ico 31104 31168, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1969324373104206530492758 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_31168_31232 :
    (∑ n ∈ Ico 31168 31232, mobiusTreeValue 16 mobiusTable1200001 n) = (-11 : ℤ) ∧
    (∑ n ∈ Ico 31168 31232, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 31168 31232, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-1761962 : ℤ) ∧
    (∑ n ∈ Ico 31168 31232, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-35239371873078009000455137075 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_31104_31232 :
    (∑ n ∈ Ico 31104 31232, mobiusTreeValue 16 mobiusTable1200001 n) = (-11 : ℤ) ∧
    (∑ n ∈ Ico 31104 31232, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (75 : ℕ) ∧
    (∑ n ∈ Ico 31104 31232, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-1761867 : ℤ) ∧
    (∑ n ∈ Ico 31104 31232, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-35237402548704904793924644317 : ℤ) := by
  rcases cdemPrefixStats_31104_31168 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_31168_31232 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 31104 ≤ 31168) (by norm_num : 31168 ≤ 31232), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 31104 ≤ 31168) (by norm_num : 31168 ≤ 31232), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 31104 ≤ 31168) (by norm_num : 31168 ≤ 31232), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 31104 ≤ 31168) (by norm_num : 31168 ≤ 31232), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_30976_31232 :
    (∑ n ∈ Ico 30976 31232, mobiusTreeValue 16 mobiusTable1200001 n) = (-6 : ℤ) ∧
    (∑ n ∈ Ico 30976 31232, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (154 : ℕ) ∧
    (∑ n ∈ Ico 30976 31232, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-955134 : ℤ) ∧
    (∑ n ∈ Ico 30976 31232, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-19102672848375901274885288228 : ℤ) := by
  rcases cdemPrefixStats_30976_31104 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_31104_31232 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 30976 ≤ 31104) (by norm_num : 31104 ≤ 31232), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 30976 ≤ 31104) (by norm_num : 31104 ≤ 31232), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 30976 ≤ 31104) (by norm_num : 31104 ≤ 31232), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 30976 ≤ 31104) (by norm_num : 31104 ≤ 31232), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_30720_31232 :
    (∑ n ∈ Ico 30720 31232, mobiusTreeValue 16 mobiusTable1200001 n) = (7 : ℤ) ∧
    (∑ n ∈ Ico 30720 31232, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (307 : ℕ) ∧
    (∑ n ∈ Ico 30720 31232, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (1160520 : ℤ) ∧
    (∑ n ∈ Ico 30720 31232, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (23210488384997236924698039037 : ℤ) := by
  rcases cdemPrefixStats_30720_30976 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_30976_31232 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 30720 ≤ 30976) (by norm_num : 30976 ≤ 31232), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 30720 ≤ 30976) (by norm_num : 30976 ≤ 31232), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 30720 ≤ 30976) (by norm_num : 30976 ≤ 31232), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 30720 ≤ 30976) (by norm_num : 30976 ≤ 31232), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_31232_31296 :
    (∑ n ∈ Ico 31232 31296, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 31232 31296, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 31232 31296, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-292 : ℤ) ∧
    (∑ n ∈ Ico 31232 31296, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-5825868687623481350673175 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_31296_31360 :
    (∑ n ∈ Ico 31296 31360, mobiusTreeValue 16 mobiusTable1200001 n) = (2 : ℤ) ∧
    (∑ n ∈ Ico 31296 31360, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 31296 31360, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (319566 : ℤ) ∧
    (∑ n ∈ Ico 31296 31360, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (6391307711841303831228544197 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_31232_31360 :
    (∑ n ∈ Ico 31232 31360, mobiusTreeValue 16 mobiusTable1200001 n) = (2 : ℤ) ∧
    (∑ n ∈ Ico 31232 31360, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (80 : ℕ) ∧
    (∑ n ∈ Ico 31232 31360, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (319274 : ℤ) ∧
    (∑ n ∈ Ico 31232 31360, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (6385481843153680349877871022 : ℤ) := by
  rcases cdemPrefixStats_31232_31296 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_31296_31360 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 31232 ≤ 31296) (by norm_num : 31296 ≤ 31360), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 31232 ≤ 31296) (by norm_num : 31296 ≤ 31360), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 31232 ≤ 31296) (by norm_num : 31296 ≤ 31360), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 31232 ≤ 31296) (by norm_num : 31296 ≤ 31360), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_31360_31424 :
    (∑ n ∈ Ico 31360 31424, mobiusTreeValue 16 mobiusTable1200001 n) = (-4 : ℤ) ∧
    (∑ n ∈ Ico 31360 31424, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 31360 31424, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-636241 : ℤ) ∧
    (∑ n ∈ Ico 31360 31424, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-12724847404721293627730002695 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_31424_31488 :
    (∑ n ∈ Ico 31424 31488, mobiusTreeValue 16 mobiusTable1200001 n) = (10 : ℤ) ∧
    (∑ n ∈ Ico 31424 31488, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (36 : ℕ) ∧
    (∑ n ∈ Ico 31424 31488, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (1589635 : ℤ) ∧
    (∑ n ∈ Ico 31424 31488, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (31792769788686209612731213725 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_31360_31488 :
    (∑ n ∈ Ico 31360 31488, mobiusTreeValue 16 mobiusTable1200001 n) = (6 : ℤ) ∧
    (∑ n ∈ Ico 31360 31488, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (74 : ℕ) ∧
    (∑ n ∈ Ico 31360 31488, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (953394 : ℤ) ∧
    (∑ n ∈ Ico 31360 31488, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (19067922383964915985001211030 : ℤ) := by
  rcases cdemPrefixStats_31360_31424 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_31424_31488 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 31360 ≤ 31424) (by norm_num : 31424 ≤ 31488), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 31360 ≤ 31424) (by norm_num : 31424 ≤ 31488), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 31360 ≤ 31424) (by norm_num : 31424 ≤ 31488), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 31360 ≤ 31424) (by norm_num : 31424 ≤ 31488), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_31232_31488 :
    (∑ n ∈ Ico 31232 31488, mobiusTreeValue 16 mobiusTable1200001 n) = (8 : ℤ) ∧
    (∑ n ∈ Ico 31232 31488, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (154 : ℕ) ∧
    (∑ n ∈ Ico 31232 31488, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (1272668 : ℤ) ∧
    (∑ n ∈ Ico 31232 31488, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (25453404227118596334879082052 : ℤ) := by
  rcases cdemPrefixStats_31232_31360 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_31360_31488 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 31232 ≤ 31360) (by norm_num : 31360 ≤ 31488), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 31232 ≤ 31360) (by norm_num : 31360 ≤ 31488), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 31232 ≤ 31360) (by norm_num : 31360 ≤ 31488), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 31232 ≤ 31360) (by norm_num : 31360 ≤ 31488), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_31488_31552 :
    (∑ n ∈ Ico 31488 31552, mobiusTreeValue 16 mobiusTable1200001 n) = (7 : ℤ) ∧
    (∑ n ∈ Ico 31488 31552, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 31488 31552, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (1111033 : ℤ) ∧
    (∑ n ∈ Ico 31488 31552, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (22220708851916582634114923856 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_31552_31616 :
    (∑ n ∈ Ico 31552 31616, mobiusTreeValue 16 mobiusTable1200001 n) = (6 : ℤ) ∧
    (∑ n ∈ Ico 31552 31616, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 31552 31616, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (948608 : ℤ) ∧
    (∑ n ∈ Ico 31552 31616, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (18972307504468252343093918020 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_31488_31616 :
    (∑ n ∈ Ico 31488 31616, mobiusTreeValue 16 mobiusTable1200001 n) = (13 : ℤ) ∧
    (∑ n ∈ Ico 31488 31616, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (79 : ℕ) ∧
    (∑ n ∈ Ico 31488 31616, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (2059641 : ℤ) ∧
    (∑ n ∈ Ico 31488 31616, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (41193016356384834977208841876 : ℤ) := by
  rcases cdemPrefixStats_31488_31552 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_31552_31616 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 31488 ≤ 31552) (by norm_num : 31552 ≤ 31616), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 31488 ≤ 31552) (by norm_num : 31552 ≤ 31616), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 31488 ≤ 31552) (by norm_num : 31552 ≤ 31616), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 31488 ≤ 31552) (by norm_num : 31552 ≤ 31616), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_31616_31680 :
    (∑ n ∈ Ico 31616 31680, mobiusTreeValue 16 mobiusTable1200001 n) = (-4 : ℤ) ∧
    (∑ n ∈ Ico 31616 31680, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 31616 31680, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-631531 : ℤ) ∧
    (∑ n ∈ Ico 31616 31680, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-12630642092201581829292640067 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_31680_31744 :
    (∑ n ∈ Ico 31680 31744, mobiusTreeValue 16 mobiusTable1200001 n) = (-9 : ℤ) ∧
    (∑ n ∈ Ico 31680 31744, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 31680 31744, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-1418351 : ℤ) ∧
    (∑ n ∈ Ico 31680 31744, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-28367109343664457517257441134 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_31616_31744 :
    (∑ n ∈ Ico 31616 31744, mobiusTreeValue 16 mobiusTable1200001 n) = (-13 : ℤ) ∧
    (∑ n ∈ Ico 31616 31744, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 31616 31744, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-2049882 : ℤ) ∧
    (∑ n ∈ Ico 31616 31744, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-40997751435866039346550081201 : ℤ) := by
  rcases cdemPrefixStats_31616_31680 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_31680_31744 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 31616 ≤ 31680) (by norm_num : 31680 ≤ 31744), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 31616 ≤ 31680) (by norm_num : 31680 ≤ 31744), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 31616 ≤ 31680) (by norm_num : 31680 ≤ 31744), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 31616 ≤ 31680) (by norm_num : 31680 ≤ 31744), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_31488_31744 :
    (∑ n ∈ Ico 31488 31744, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 31488 31744, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (156 : ℕ) ∧
    (∑ n ∈ Ico 31488 31744, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (9759 : ℤ) ∧
    (∑ n ∈ Ico 31488 31744, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (195264920518795630658760675 : ℤ) := by
  rcases cdemPrefixStats_31488_31616 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_31616_31744 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 31488 ≤ 31616) (by norm_num : 31616 ≤ 31744), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 31488 ≤ 31616) (by norm_num : 31616 ≤ 31744), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 31488 ≤ 31616) (by norm_num : 31616 ≤ 31744), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 31488 ≤ 31616) (by norm_num : 31616 ≤ 31744), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_31232_31744 :
    (∑ n ∈ Ico 31232 31744, mobiusTreeValue 16 mobiusTable1200001 n) = (8 : ℤ) ∧
    (∑ n ∈ Ico 31232 31744, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (310 : ℕ) ∧
    (∑ n ∈ Ico 31232 31744, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (1282427 : ℤ) ∧
    (∑ n ∈ Ico 31232 31744, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (25648669147637391965537842727 : ℤ) := by
  rcases cdemPrefixStats_31232_31488 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_31488_31744 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 31232 ≤ 31488) (by norm_num : 31488 ≤ 31744), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 31232 ≤ 31488) (by norm_num : 31488 ≤ 31744), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 31232 ≤ 31488) (by norm_num : 31488 ≤ 31744), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 31232 ≤ 31488) (by norm_num : 31488 ≤ 31744), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_30720_31744 :
    (∑ n ∈ Ico 30720 31744, mobiusTreeValue 16 mobiusTable1200001 n) = (15 : ℤ) ∧
    (∑ n ∈ Ico 30720 31744, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (617 : ℕ) ∧
    (∑ n ∈ Ico 30720 31744, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (2442947 : ℤ) ∧
    (∑ n ∈ Ico 30720 31744, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (48859157532634628890235881764 : ℤ) := by
  rcases cdemPrefixStats_30720_31232 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_31232_31744 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 30720 ≤ 31232) (by norm_num : 31232 ≤ 31744), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 30720 ≤ 31232) (by norm_num : 31232 ≤ 31744), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 30720 ≤ 31232) (by norm_num : 31232 ≤ 31744), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 30720 ≤ 31232) (by norm_num : 31232 ≤ 31744), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_31744_31808 :
    (∑ n ∈ Ico 31744 31808, mobiusTreeValue 16 mobiusTable1200001 n) = (11 : ℤ) ∧
    (∑ n ∈ Ico 31744 31808, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 31744 31808, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (1730458 : ℤ) ∧
    (∑ n ∈ Ico 31744 31808, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (34609307796758959202377420568 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_31808_31872 :
    (∑ n ∈ Ico 31808 31872, mobiusTreeValue 16 mobiusTable1200001 n) = (7 : ℤ) ∧
    (∑ n ∈ Ico 31808 31872, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 31808 31872, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (1099436 : ℤ) ∧
    (∑ n ∈ Ico 31808 31872, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (21988772461244769713586657221 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_31744_31872 :
    (∑ n ∈ Ico 31744 31872, mobiusTreeValue 16 mobiusTable1200001 n) = (18 : ℤ) ∧
    (∑ n ∈ Ico 31744 31872, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 31744 31872, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (2829894 : ℤ) ∧
    (∑ n ∈ Ico 31744 31872, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (56598080258003728915964077789 : ℤ) := by
  rcases cdemPrefixStats_31744_31808 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_31808_31872 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 31744 ≤ 31808) (by norm_num : 31808 ≤ 31872), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 31744 ≤ 31808) (by norm_num : 31808 ≤ 31872), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 31744 ≤ 31808) (by norm_num : 31808 ≤ 31872), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 31744 ≤ 31808) (by norm_num : 31808 ≤ 31872), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_31872_31936 :
    (∑ n ∈ Ico 31872 31936, mobiusTreeValue 16 mobiusTable1200001 n) = (2 : ℤ) ∧
    (∑ n ∈ Ico 31872 31936, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 31872 31936, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (313136 : ℤ) ∧
    (∑ n ∈ Ico 31872 31936, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (6262718891029213633436290903 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_31936_32000 :
    (∑ n ∈ Ico 31936 32000, mobiusTreeValue 16 mobiusTable1200001 n) = (7 : ℤ) ∧
    (∑ n ∈ Ico 31936 32000, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 31936 32000, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (1095452 : ℤ) ∧
    (∑ n ∈ Ico 31936 32000, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (21909135509013883672315644293 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_31872_32000 :
    (∑ n ∈ Ico 31872 32000, mobiusTreeValue 16 mobiusTable1200001 n) = (9 : ℤ) ∧
    (∑ n ∈ Ico 31872 32000, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 31872 32000, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (1408588 : ℤ) ∧
    (∑ n ∈ Ico 31872 32000, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (28171854400043097305751935196 : ℤ) := by
  rcases cdemPrefixStats_31872_31936 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_31936_32000 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 31872 ≤ 31936) (by norm_num : 31936 ≤ 32000), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 31872 ≤ 31936) (by norm_num : 31936 ≤ 32000), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 31872 ≤ 31936) (by norm_num : 31936 ≤ 32000), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 31872 ≤ 31936) (by norm_num : 31936 ≤ 32000), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_31744_32000 :
    (∑ n ∈ Ico 31744 32000, mobiusTreeValue 16 mobiusTable1200001 n) = (27 : ℤ) ∧
    (∑ n ∈ Ico 31744 32000, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (155 : ℕ) ∧
    (∑ n ∈ Ico 31744 32000, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (4238482 : ℤ) ∧
    (∑ n ∈ Ico 31744 32000, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (84769934658046826221716012985 : ℤ) := by
  rcases cdemPrefixStats_31744_31872 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_31872_32000 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 31744 ≤ 31872) (by norm_num : 31872 ≤ 32000), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 31744 ≤ 31872) (by norm_num : 31872 ≤ 32000), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 31744 ≤ 31872) (by norm_num : 31872 ≤ 32000), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 31744 ≤ 31872) (by norm_num : 31872 ≤ 32000), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_32000_32064 :
    (∑ n ∈ Ico 32000 32064, mobiusTreeValue 16 mobiusTable1200001 n) = (-15 : ℤ) ∧
    (∑ n ∈ Ico 32000 32064, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 32000 32064, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-2341719 : ℤ) ∧
    (∑ n ∈ Ico 32000 32064, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-46834519117943340101017496508 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_32064_32128 :
    (∑ n ∈ Ico 32064 32128, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 32064 32128, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 32064 32128, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (155537 : ℤ) ∧
    (∑ n ∈ Ico 32064 32128, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (3110713163107145625931626252 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_32000_32128 :
    (∑ n ∈ Ico 32000 32128, mobiusTreeValue 16 mobiusTable1200001 n) = (-14 : ℤ) ∧
    (∑ n ∈ Ico 32000 32128, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (76 : ℕ) ∧
    (∑ n ∈ Ico 32000 32128, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-2186182 : ℤ) ∧
    (∑ n ∈ Ico 32000 32128, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-43723805954836194475085870256 : ℤ) := by
  rcases cdemPrefixStats_32000_32064 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_32064_32128 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 32000 ≤ 32064) (by norm_num : 32064 ≤ 32128), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 32000 ≤ 32064) (by norm_num : 32064 ≤ 32128), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 32000 ≤ 32064) (by norm_num : 32064 ≤ 32128), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 32000 ≤ 32064) (by norm_num : 32064 ≤ 32128), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_32128_32192 :
    (∑ n ∈ Ico 32128 32192, mobiusTreeValue 16 mobiusTable1200001 n) = (-2 : ℤ) ∧
    (∑ n ∈ Ico 32128 32192, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 32128 32192, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-310451 : ℤ) ∧
    (∑ n ∈ Ico 32128 32192, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-6209044275873247887717956507 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_32192_32256 :
    (∑ n ∈ Ico 32192 32256, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 32192 32256, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 32192 32256, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-155005 : ℤ) ∧
    (∑ n ∈ Ico 32192 32256, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-3100096900639581103185797054 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_32128_32256 :
    (∑ n ∈ Ico 32128 32256, mobiusTreeValue 16 mobiusTable1200001 n) = (-3 : ℤ) ∧
    (∑ n ∈ Ico 32128 32256, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (79 : ℕ) ∧
    (∑ n ∈ Ico 32128 32256, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-465456 : ℤ) ∧
    (∑ n ∈ Ico 32128 32256, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-9309141176512828990903753561 : ℤ) := by
  rcases cdemPrefixStats_32128_32192 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_32192_32256 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 32128 ≤ 32192) (by norm_num : 32192 ≤ 32256), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 32128 ≤ 32192) (by norm_num : 32192 ≤ 32256), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 32128 ≤ 32192) (by norm_num : 32192 ≤ 32256), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 32128 ≤ 32192) (by norm_num : 32192 ≤ 32256), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_32000_32256 :
    (∑ n ∈ Ico 32000 32256, mobiusTreeValue 16 mobiusTable1200001 n) = (-17 : ℤ) ∧
    (∑ n ∈ Ico 32000 32256, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (155 : ℕ) ∧
    (∑ n ∈ Ico 32000 32256, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-2651638 : ℤ) ∧
    (∑ n ∈ Ico 32000 32256, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-53032947131349023465989623817 : ℤ) := by
  rcases cdemPrefixStats_32000_32128 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_32128_32256 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 32000 ≤ 32128) (by norm_num : 32128 ≤ 32256), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 32000 ≤ 32128) (by norm_num : 32128 ≤ 32256), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 32000 ≤ 32128) (by norm_num : 32128 ≤ 32256), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 32000 ≤ 32128) (by norm_num : 32128 ≤ 32256), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_31744_32256 :
    (∑ n ∈ Ico 31744 32256, mobiusTreeValue 16 mobiusTable1200001 n) = (10 : ℤ) ∧
    (∑ n ∈ Ico 31744 32256, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (310 : ℕ) ∧
    (∑ n ∈ Ico 31744 32256, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (1586844 : ℤ) ∧
    (∑ n ∈ Ico 31744 32256, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (31736987526697802755726389168 : ℤ) := by
  rcases cdemPrefixStats_31744_32000 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_32000_32256 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 31744 ≤ 32000) (by norm_num : 32000 ≤ 32256), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 31744 ≤ 32000) (by norm_num : 32000 ≤ 32256), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 31744 ≤ 32000) (by norm_num : 32000 ≤ 32256), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 31744 ≤ 32000) (by norm_num : 32000 ≤ 32256), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_32256_32320 :
    (∑ n ∈ Ico 32256 32320, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 32256 32320, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (36 : ℕ) ∧
    (∑ n ∈ Ico 32256 32320, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (382 : ℤ) ∧
    (∑ n ∈ Ico 32256 32320, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (7581115866815906565585581 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_32320_32384 :
    (∑ n ∈ Ico 32320 32384, mobiusTreeValue 16 mobiusTable1200001 n) = (-12 : ℤ) ∧
    (∑ n ∈ Ico 32320 32384, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 32320 32384, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-1854614 : ℤ) ∧
    (∑ n ∈ Ico 32320 32384, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-37092292785110926594380429575 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_32256_32384 :
    (∑ n ∈ Ico 32256 32384, mobiusTreeValue 16 mobiusTable1200001 n) = (-12 : ℤ) ∧
    (∑ n ∈ Ico 32256 32384, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (76 : ℕ) ∧
    (∑ n ∈ Ico 32256 32384, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-1854232 : ℤ) ∧
    (∑ n ∈ Ico 32256 32384, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-37084711669244110687814843994 : ℤ) := by
  rcases cdemPrefixStats_32256_32320 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_32320_32384 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 32256 ≤ 32320) (by norm_num : 32320 ≤ 32384), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 32256 ≤ 32320) (by norm_num : 32320 ≤ 32384), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 32256 ≤ 32320) (by norm_num : 32320 ≤ 32384), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 32256 ≤ 32320) (by norm_num : 32320 ≤ 32384), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_32384_32448 :
    (∑ n ∈ Ico 32384 32448, mobiusTreeValue 16 mobiusTable1200001 n) = (-4 : ℤ) ∧
    (∑ n ∈ Ico 32384 32448, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 32384 32448, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-615874 : ℤ) ∧
    (∑ n ∈ Ico 32384 32448, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-12317499279068395700344365124 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_32448_32512 :
    (∑ n ∈ Ico 32448 32512, mobiusTreeValue 16 mobiusTable1200001 n) = (-2 : ℤ) ∧
    (∑ n ∈ Ico 32448 32512, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 32448 32512, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-307684 : ℤ) ∧
    (∑ n ∈ Ico 32448 32512, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-6153750331563122099454967995 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_32384_32512 :
    (∑ n ∈ Ico 32384 32512, mobiusTreeValue 16 mobiusTable1200001 n) = (-6 : ℤ) ∧
    (∑ n ∈ Ico 32384 32512, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (80 : ℕ) ∧
    (∑ n ∈ Ico 32384 32512, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-923558 : ℤ) ∧
    (∑ n ∈ Ico 32384 32512, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-18471249610631517799799333119 : ℤ) := by
  rcases cdemPrefixStats_32384_32448 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_32448_32512 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 32384 ≤ 32448) (by norm_num : 32448 ≤ 32512), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 32384 ≤ 32448) (by norm_num : 32448 ≤ 32512), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 32384 ≤ 32448) (by norm_num : 32448 ≤ 32512), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 32384 ≤ 32448) (by norm_num : 32448 ≤ 32512), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_32256_32512 :
    (∑ n ∈ Ico 32256 32512, mobiusTreeValue 16 mobiusTable1200001 n) = (-18 : ℤ) ∧
    (∑ n ∈ Ico 32256 32512, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (156 : ℕ) ∧
    (∑ n ∈ Ico 32256 32512, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-2777790 : ℤ) ∧
    (∑ n ∈ Ico 32256 32512, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-55555961279875628487614177113 : ℤ) := by
  rcases cdemPrefixStats_32256_32384 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_32384_32512 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 32256 ≤ 32384) (by norm_num : 32384 ≤ 32512), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 32256 ≤ 32384) (by norm_num : 32384 ≤ 32512), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 32256 ≤ 32384) (by norm_num : 32384 ≤ 32512), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 32256 ≤ 32384) (by norm_num : 32384 ≤ 32512), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_32512_32576 :
    (∑ n ∈ Ico 32512 32576, mobiusTreeValue 16 mobiusTable1200001 n) = (-8 : ℤ) ∧
    (∑ n ∈ Ico 32512 32576, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 32512 32576, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-1229257 : ℤ) ∧
    (∑ n ∈ Ico 32512 32576, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-24585231489610591056047187368 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_32576_32640 :
    (∑ n ∈ Ico 32576 32640, mobiusTreeValue 16 mobiusTable1200001 n) = (-5 : ℤ) ∧
    (∑ n ∈ Ico 32576 32640, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 32576 32640, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-766264 : ℤ) ∧
    (∑ n ∈ Ico 32576 32640, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-15325287932726783390867788962 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_32512_32640 :
    (∑ n ∈ Ico 32512 32640, mobiusTreeValue 16 mobiusTable1200001 n) = (-13 : ℤ) ∧
    (∑ n ∈ Ico 32512 32640, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (79 : ℕ) ∧
    (∑ n ∈ Ico 32512 32640, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-1995521 : ℤ) ∧
    (∑ n ∈ Ico 32512 32640, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-39910519422337374446914976330 : ℤ) := by
  rcases cdemPrefixStats_32512_32576 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_32576_32640 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 32512 ≤ 32576) (by norm_num : 32576 ≤ 32640), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 32512 ≤ 32576) (by norm_num : 32576 ≤ 32640), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 32512 ≤ 32576) (by norm_num : 32576 ≤ 32640), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 32512 ≤ 32576) (by norm_num : 32576 ≤ 32640), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_32640_32704 :
    (∑ n ∈ Ico 32640 32704, mobiusTreeValue 16 mobiusTable1200001 n) = (2 : ℤ) ∧
    (∑ n ∈ Ico 32640 32704, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 32640 32704, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (306261 : ℤ) ∧
    (∑ n ∈ Ico 32640 32704, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (6125287179542600494182819289 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_32704_32768 :
    (∑ n ∈ Ico 32704 32768, mobiusTreeValue 16 mobiusTable1200001 n) = (2 : ℤ) ∧
    (∑ n ∈ Ico 32704 32768, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 32704 32768, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (305066 : ℤ) ∧
    (∑ n ∈ Ico 32704 32768, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (6101355929492387195167824883 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_32640_32768 :
    (∑ n ∈ Ico 32640 32768, mobiusTreeValue 16 mobiusTable1200001 n) = (4 : ℤ) ∧
    (∑ n ∈ Ico 32640 32768, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 32640 32768, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (611327 : ℤ) ∧
    (∑ n ∈ Ico 32640 32768, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (12226643109034987689350644172 : ℤ) := by
  rcases cdemPrefixStats_32640_32704 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_32704_32768 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 32640 ≤ 32704) (by norm_num : 32704 ≤ 32768), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 32640 ≤ 32704) (by norm_num : 32704 ≤ 32768), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 32640 ≤ 32704) (by norm_num : 32704 ≤ 32768), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 32640 ≤ 32704) (by norm_num : 32704 ≤ 32768), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_32512_32768 :
    (∑ n ∈ Ico 32512 32768, mobiusTreeValue 16 mobiusTable1200001 n) = (-9 : ℤ) ∧
    (∑ n ∈ Ico 32512 32768, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (157 : ℕ) ∧
    (∑ n ∈ Ico 32512 32768, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-1384194 : ℤ) ∧
    (∑ n ∈ Ico 32512 32768, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-27683876313302386757564332158 : ℤ) := by
  rcases cdemPrefixStats_32512_32640 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_32640_32768 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 32512 ≤ 32640) (by norm_num : 32640 ≤ 32768), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 32512 ≤ 32640) (by norm_num : 32640 ≤ 32768), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 32512 ≤ 32640) (by norm_num : 32640 ≤ 32768), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 32512 ≤ 32640) (by norm_num : 32640 ≤ 32768), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_32256_32768 :
    (∑ n ∈ Ico 32256 32768, mobiusTreeValue 16 mobiusTable1200001 n) = (-27 : ℤ) ∧
    (∑ n ∈ Ico 32256 32768, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (313 : ℕ) ∧
    (∑ n ∈ Ico 32256 32768, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-4161984 : ℤ) ∧
    (∑ n ∈ Ico 32256 32768, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-83239837593178015245178509271 : ℤ) := by
  rcases cdemPrefixStats_32256_32512 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_32512_32768 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 32256 ≤ 32512) (by norm_num : 32512 ≤ 32768), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 32256 ≤ 32512) (by norm_num : 32512 ≤ 32768), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 32256 ≤ 32512) (by norm_num : 32512 ≤ 32768), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 32256 ≤ 32512) (by norm_num : 32512 ≤ 32768), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_31744_32768 :
    (∑ n ∈ Ico 31744 32768, mobiusTreeValue 16 mobiusTable1200001 n) = (-17 : ℤ) ∧
    (∑ n ∈ Ico 31744 32768, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (623 : ℕ) ∧
    (∑ n ∈ Ico 31744 32768, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-2575140 : ℤ) ∧
    (∑ n ∈ Ico 31744 32768, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-51502850066480212489452120103 : ℤ) := by
  rcases cdemPrefixStats_31744_32256 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_32256_32768 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 31744 ≤ 32256) (by norm_num : 32256 ≤ 32768), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 31744 ≤ 32256) (by norm_num : 32256 ≤ 32768), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 31744 ≤ 32256) (by norm_num : 32256 ≤ 32768), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 31744 ≤ 32256) (by norm_num : 32256 ≤ 32768), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_30720_32768 :
    (∑ n ∈ Ico 30720 32768, mobiusTreeValue 16 mobiusTable1200001 n) = (-2 : ℤ) ∧
    (∑ n ∈ Ico 30720 32768, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (1240 : ℕ) ∧
    (∑ n ∈ Ico 30720 32768, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-132193 : ℤ) ∧
    (∑ n ∈ Ico 30720 32768, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-2643692533845583599216238339 : ℤ) := by
  rcases cdemPrefixStats_30720_31744 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_31744_32768 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 30720 ≤ 31744) (by norm_num : 31744 ≤ 32768), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 30720 ≤ 31744) (by norm_num : 31744 ≤ 32768), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 30720 ≤ 31744) (by norm_num : 31744 ≤ 32768), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 30720 ≤ 31744) (by norm_num : 31744 ≤ 32768), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_28672_32768 :
    (∑ n ∈ Ico 28672 32768, mobiusTreeValue 16 mobiusTable1200001 n) = (36 : ℤ) ∧
    (∑ n ∈ Ico 28672 32768, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (2486 : ℕ) ∧
    (∑ n ∈ Ico 28672 32768, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (6229467 : ℤ) ∧
    (∑ n ∈ Ico 28672 32768, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (124590055446270867968603592582 : ℤ) := by
  rcases cdemPrefixStats_28672_30720 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_30720_32768 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 28672 ≤ 30720) (by norm_num : 30720 ≤ 32768), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 28672 ≤ 30720) (by norm_num : 30720 ≤ 32768), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 28672 ≤ 30720) (by norm_num : 30720 ≤ 32768), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 28672 ≤ 30720) (by norm_num : 30720 ≤ 32768), hR1, hR2] <;> norm_num

theorem cdemPrefixGroup007_checked_complete :
    (∑ n ∈ Ico 28672 32768, mobiusTreeValue 16 mobiusTable1200001 n) = (36 : ℤ) ∧
    (∑ n ∈ Ico 28672 32768, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (2486 : ℕ) ∧
    (∑ n ∈ Ico 28672 32768, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (6229467 : ℤ) ∧
    (∑ n ∈ Ico 28672 32768, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (124590055446270867968603592582 : ℤ) := cdemPrefixStats_28672_32768
end Helfgott
#print axioms Helfgott.cdemPrefixGroup007_checked_complete

open Helfgott Finset
open scoped BigOperators

theorem solution :
    (∑ n ∈ Ico 28672 32768, mobiusTreeValue 16 mobiusTable1200001 n) = (36 : ℤ) ∧
    (∑ n ∈ Ico 28672 32768, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (2486 : ℕ) ∧
    (∑ n ∈ Ico 28672 32768, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (6229467 : ℤ) ∧
    (∑ n ∈ Ico 28672 32768, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (124590055446270867968603592582 : ℤ) := Helfgott.cdemPrefixGroup007_checked_complete
#print axioms solution
