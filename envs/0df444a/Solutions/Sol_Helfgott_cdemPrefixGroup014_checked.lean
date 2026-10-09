-- Prove2me | solution 1 for Helfgott.cdemPrefixGroup014_checked
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-09T01:43:48.402296+00:00
-- url     : https://prove2.me/submissions/ea75df8a-184b-4ed7-8aeb-ac96824b0ff5

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
private theorem cdemPrefixStats_57344_57408 :
    (∑ n ∈ Ico 57344 57408, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 57344 57408, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 57344 57408, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (87057 : ℤ) ∧
    (∑ n ∈ Ico 57344 57408, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1741157200765458013886074505 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_57408_57472 :
    (∑ n ∈ Ico 57408 57472, mobiusTreeValue 16 mobiusTable1200001 n) = (6 : ℤ) ∧
    (∑ n ∈ Ico 57408 57472, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 57408 57472, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (522153 : ℤ) ∧
    (∑ n ∈ Ico 57408 57472, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (10443107116295350750243040218 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_57344_57472 :
    (∑ n ∈ Ico 57344 57472, mobiusTreeValue 16 mobiusTable1200001 n) = (7 : ℤ) ∧
    (∑ n ∈ Ico 57344 57472, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (79 : ℕ) ∧
    (∑ n ∈ Ico 57344 57472, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (609210 : ℤ) ∧
    (∑ n ∈ Ico 57344 57472, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (12184264317060808764129114723 : ℤ) := by
  rcases cdemPrefixStats_57344_57408 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_57408_57472 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 57344 ≤ 57408) (by norm_num : 57408 ≤ 57472), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 57344 ≤ 57408) (by norm_num : 57408 ≤ 57472), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 57344 ≤ 57408) (by norm_num : 57408 ≤ 57472), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 57344 ≤ 57408) (by norm_num : 57408 ≤ 57472), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_57472_57536 :
    (∑ n ∈ Ico 57472 57536, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 57472 57536, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 57472 57536, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (86987 : ℤ) ∧
    (∑ n ∈ Ico 57472 57536, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1739705037489026174232981092 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_57536_57600 :
    (∑ n ∈ Ico 57536 57600, mobiusTreeValue 16 mobiusTable1200001 n) = (-2 : ℤ) ∧
    (∑ n ∈ Ico 57536 57600, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 57536 57600, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-173663 : ℤ) ∧
    (∑ n ∈ Ico 57536 57600, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-3473276020567203122390435681 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_57472_57600 :
    (∑ n ∈ Ico 57472 57600, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 57472 57600, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 57472 57600, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-86676 : ℤ) ∧
    (∑ n ∈ Ico 57472 57600, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-1733570983078176948157454589 : ℤ) := by
  rcases cdemPrefixStats_57472_57536 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_57536_57600 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 57472 ≤ 57536) (by norm_num : 57536 ≤ 57600), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 57472 ≤ 57536) (by norm_num : 57536 ≤ 57600), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 57472 ≤ 57536) (by norm_num : 57536 ≤ 57600), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 57472 ≤ 57536) (by norm_num : 57536 ≤ 57600), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_57344_57600 :
    (∑ n ∈ Ico 57344 57600, mobiusTreeValue 16 mobiusTable1200001 n) = (6 : ℤ) ∧
    (∑ n ∈ Ico 57344 57600, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (156 : ℕ) ∧
    (∑ n ∈ Ico 57344 57600, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (522534 : ℤ) ∧
    (∑ n ∈ Ico 57344 57600, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (10450693333982631815971660134 : ℤ) := by
  rcases cdemPrefixStats_57344_57472 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_57472_57600 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 57344 ≤ 57472) (by norm_num : 57472 ≤ 57600), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 57344 ≤ 57472) (by norm_num : 57472 ≤ 57600), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 57344 ≤ 57472) (by norm_num : 57472 ≤ 57600), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 57344 ≤ 57472) (by norm_num : 57472 ≤ 57600), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_57600_57664 :
    (∑ n ∈ Ico 57600 57664, mobiusTreeValue 16 mobiusTable1200001 n) = (10 : ℤ) ∧
    (∑ n ∈ Ico 57600 57664, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 57600 57664, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (867729 : ℤ) ∧
    (∑ n ∈ Ico 57600 57664, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (17354752804327214892330230728 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_57664_57728 :
    (∑ n ∈ Ico 57664 57728, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 57664 57728, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 57664 57728, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (86720 : ℤ) ∧
    (∑ n ∈ Ico 57664 57728, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1734363333649093145777761222 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_57600_57728 :
    (∑ n ∈ Ico 57600 57728, mobiusTreeValue 16 mobiusTable1200001 n) = (11 : ℤ) ∧
    (∑ n ∈ Ico 57600 57728, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 57600 57728, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (954449 : ℤ) ∧
    (∑ n ∈ Ico 57600 57728, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (19089116137976308038107991950 : ℤ) := by
  rcases cdemPrefixStats_57600_57664 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_57664_57728 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 57600 ≤ 57664) (by norm_num : 57664 ≤ 57728), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 57600 ≤ 57664) (by norm_num : 57664 ≤ 57728), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 57600 ≤ 57664) (by norm_num : 57664 ≤ 57728), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 57600 ≤ 57664) (by norm_num : 57664 ≤ 57728), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_57728_57792 :
    (∑ n ∈ Ico 57728 57792, mobiusTreeValue 16 mobiusTable1200001 n) = (-9 : ℤ) ∧
    (∑ n ∈ Ico 57728 57792, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 57728 57792, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-779036 : ℤ) ∧
    (∑ n ∈ Ico 57728 57792, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-15580790433032110212600818828 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_57792_57856 :
    (∑ n ∈ Ico 57792 57856, mobiusTreeValue 16 mobiusTable1200001 n) = (-11 : ℤ) ∧
    (∑ n ∈ Ico 57792 57856, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 57792 57856, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-951085 : ℤ) ∧
    (∑ n ∈ Ico 57792 57856, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-19021899228541699855067354913 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_57728_57856 :
    (∑ n ∈ Ico 57728 57856, mobiusTreeValue 16 mobiusTable1200001 n) = (-20 : ℤ) ∧
    (∑ n ∈ Ico 57728 57856, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (82 : ℕ) ∧
    (∑ n ∈ Ico 57728 57856, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-1730121 : ℤ) ∧
    (∑ n ∈ Ico 57728 57856, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-34602689661573810067668173741 : ℤ) := by
  rcases cdemPrefixStats_57728_57792 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_57792_57856 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 57728 ≤ 57792) (by norm_num : 57792 ≤ 57856), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 57728 ≤ 57792) (by norm_num : 57792 ≤ 57856), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 57728 ≤ 57792) (by norm_num : 57792 ≤ 57856), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 57728 ≤ 57792) (by norm_num : 57792 ≤ 57856), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_57600_57856 :
    (∑ n ∈ Ico 57600 57856, mobiusTreeValue 16 mobiusTable1200001 n) = (-9 : ℤ) ∧
    (∑ n ∈ Ico 57600 57856, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (159 : ℕ) ∧
    (∑ n ∈ Ico 57600 57856, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-775672 : ℤ) ∧
    (∑ n ∈ Ico 57600 57856, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-15513573523597502029560181791 : ℤ) := by
  rcases cdemPrefixStats_57600_57728 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_57728_57856 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 57600 ≤ 57728) (by norm_num : 57728 ≤ 57856), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 57600 ≤ 57728) (by norm_num : 57728 ≤ 57856), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 57600 ≤ 57728) (by norm_num : 57728 ≤ 57856), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 57600 ≤ 57728) (by norm_num : 57728 ≤ 57856), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_57344_57856 :
    (∑ n ∈ Ico 57344 57856, mobiusTreeValue 16 mobiusTable1200001 n) = (-3 : ℤ) ∧
    (∑ n ∈ Ico 57344 57856, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (315 : ℕ) ∧
    (∑ n ∈ Ico 57344 57856, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-253138 : ℤ) ∧
    (∑ n ∈ Ico 57344 57856, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-5062880189614870213588521657 : ℤ) := by
  rcases cdemPrefixStats_57344_57600 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_57600_57856 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 57344 ≤ 57600) (by norm_num : 57600 ≤ 57856), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 57344 ≤ 57600) (by norm_num : 57600 ≤ 57856), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 57344 ≤ 57600) (by norm_num : 57600 ≤ 57856), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 57344 ≤ 57600) (by norm_num : 57600 ≤ 57856), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_57856_57920 :
    (∑ n ∈ Ico 57856 57920, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 57856 57920, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 57856 57920, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-86381 : ℤ) ∧
    (∑ n ∈ Ico 57856 57920, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-1727653086329204793821488363 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_57920_57984 :
    (∑ n ∈ Ico 57920 57984, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 57920 57984, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 57920 57984, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (86223 : ℤ) ∧
    (∑ n ∈ Ico 57920 57984, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1724494698485973706435504816 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_57856_57984 :
    (∑ n ∈ Ico 57856 57984, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 57856 57984, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (76 : ℕ) ∧
    (∑ n ∈ Ico 57856 57984, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-158 : ℤ) ∧
    (∑ n ∈ Ico 57856 57984, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-3158387843231087385983547 : ℤ) := by
  rcases cdemPrefixStats_57856_57920 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_57920_57984 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 57856 ≤ 57920) (by norm_num : 57920 ≤ 57984), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 57856 ≤ 57920) (by norm_num : 57920 ≤ 57984), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 57856 ≤ 57920) (by norm_num : 57920 ≤ 57984), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 57856 ≤ 57920) (by norm_num : 57920 ≤ 57984), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_57984_58048 :
    (∑ n ∈ Ico 57984 58048, mobiusTreeValue 16 mobiusTable1200001 n) = (7 : ℤ) ∧
    (∑ n ∈ Ico 57984 58048, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 57984 58048, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (603081 : ℤ) ∧
    (∑ n ∈ Ico 57984 58048, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (12061717073212373096552370028 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_58048_58112 :
    (∑ n ∈ Ico 58048 58112, mobiusTreeValue 16 mobiusTable1200001 n) = (-11 : ℤ) ∧
    (∑ n ∈ Ico 58048 58112, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 58048 58112, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-946971 : ℤ) ∧
    (∑ n ∈ Ico 58048 58112, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-18939485755350231529385736438 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_57984_58112 :
    (∑ n ∈ Ico 57984 58112, mobiusTreeValue 16 mobiusTable1200001 n) = (-4 : ℤ) ∧
    (∑ n ∈ Ico 57984 58112, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (80 : ℕ) ∧
    (∑ n ∈ Ico 57984 58112, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-343890 : ℤ) ∧
    (∑ n ∈ Ico 57984 58112, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-6877768682137858432833366410 : ℤ) := by
  rcases cdemPrefixStats_57984_58048 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_58048_58112 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 57984 ≤ 58048) (by norm_num : 58048 ≤ 58112), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 57984 ≤ 58048) (by norm_num : 58048 ≤ 58112), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 57984 ≤ 58048) (by norm_num : 58048 ≤ 58112), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 57984 ≤ 58048) (by norm_num : 58048 ≤ 58112), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_57856_58112 :
    (∑ n ∈ Ico 57856 58112, mobiusTreeValue 16 mobiusTable1200001 n) = (-4 : ℤ) ∧
    (∑ n ∈ Ico 57856 58112, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (156 : ℕ) ∧
    (∑ n ∈ Ico 57856 58112, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-344048 : ℤ) ∧
    (∑ n ∈ Ico 57856 58112, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-6880927069981089520219349957 : ℤ) := by
  rcases cdemPrefixStats_57856_57984 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_57984_58112 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 57856 ≤ 57984) (by norm_num : 57984 ≤ 58112), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 57856 ≤ 57984) (by norm_num : 57984 ≤ 58112), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 57856 ≤ 57984) (by norm_num : 57984 ≤ 58112), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 57856 ≤ 57984) (by norm_num : 57984 ≤ 58112), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_58112_58176 :
    (∑ n ∈ Ico 58112 58176, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 58112 58176, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (36 : ℕ) ∧
    (∑ n ∈ Ico 58112 58176, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (132 : ℤ) ∧
    (∑ n ∈ Ico 58112 58176, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (2662465727454777917270269 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_58176_58240 :
    (∑ n ∈ Ico 58176 58240, mobiusTreeValue 16 mobiusTable1200001 n) = (-13 : ℤ) ∧
    (∑ n ∈ Ico 58176 58240, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 58176 58240, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-1116392 : ℤ) ∧
    (∑ n ∈ Ico 58176 58240, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-22327916893567995331207797646 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_58112_58240 :
    (∑ n ∈ Ico 58112 58240, mobiusTreeValue 16 mobiusTable1200001 n) = (-13 : ℤ) ∧
    (∑ n ∈ Ico 58112 58240, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (75 : ℕ) ∧
    (∑ n ∈ Ico 58112 58240, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-1116260 : ℤ) ∧
    (∑ n ∈ Ico 58112 58240, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-22325254427840540553290527377 : ℤ) := by
  rcases cdemPrefixStats_58112_58176 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_58176_58240 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 58112 ≤ 58176) (by norm_num : 58176 ≤ 58240), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 58112 ≤ 58176) (by norm_num : 58176 ≤ 58240), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 58112 ≤ 58176) (by norm_num : 58176 ≤ 58240), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 58112 ≤ 58176) (by norm_num : 58176 ≤ 58240), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_58240_58304 :
    (∑ n ∈ Ico 58240 58304, mobiusTreeValue 16 mobiusTable1200001 n) = (15 : ℤ) ∧
    (∑ n ∈ Ico 58240 58304, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 58240 58304, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (1287019 : ℤ) ∧
    (∑ n ∈ Ico 58240 58304, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (25740529097499817541140281793 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_58304_58368 :
    (∑ n ∈ Ico 58304 58368, mobiusTreeValue 16 mobiusTable1200001 n) = (-6 : ℤ) ∧
    (∑ n ∈ Ico 58304 58368, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (36 : ℕ) ∧
    (∑ n ∈ Ico 58304 58368, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-514320 : ℤ) ∧
    (∑ n ∈ Ico 58304 58368, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-10286478961143869848432365960 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_58240_58368 :
    (∑ n ∈ Ico 58240 58368, mobiusTreeValue 16 mobiusTable1200001 n) = (9 : ℤ) ∧
    (∑ n ∈ Ico 58240 58368, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 58240 58368, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (772699 : ℤ) ∧
    (∑ n ∈ Ico 58240 58368, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (15454050136355947692707915833 : ℤ) := by
  rcases cdemPrefixStats_58240_58304 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_58304_58368 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 58240 ≤ 58304) (by norm_num : 58304 ≤ 58368), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 58240 ≤ 58304) (by norm_num : 58304 ≤ 58368), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 58240 ≤ 58304) (by norm_num : 58304 ≤ 58368), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 58240 ≤ 58304) (by norm_num : 58304 ≤ 58368), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_58112_58368 :
    (∑ n ∈ Ico 58112 58368, mobiusTreeValue 16 mobiusTable1200001 n) = (-4 : ℤ) ∧
    (∑ n ∈ Ico 58112 58368, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (152 : ℕ) ∧
    (∑ n ∈ Ico 58112 58368, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-343561 : ℤ) ∧
    (∑ n ∈ Ico 58112 58368, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-6871204291484592860582611544 : ℤ) := by
  rcases cdemPrefixStats_58112_58240 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_58240_58368 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 58112 ≤ 58240) (by norm_num : 58240 ≤ 58368), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 58112 ≤ 58240) (by norm_num : 58240 ≤ 58368), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 58112 ≤ 58240) (by norm_num : 58240 ≤ 58368), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 58112 ≤ 58240) (by norm_num : 58240 ≤ 58368), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_57856_58368 :
    (∑ n ∈ Ico 57856 58368, mobiusTreeValue 16 mobiusTable1200001 n) = (-8 : ℤ) ∧
    (∑ n ∈ Ico 57856 58368, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (308 : ℕ) ∧
    (∑ n ∈ Ico 57856 58368, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-687609 : ℤ) ∧
    (∑ n ∈ Ico 57856 58368, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-13752131361465682380801961501 : ℤ) := by
  rcases cdemPrefixStats_57856_58112 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_58112_58368 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 57856 ≤ 58112) (by norm_num : 58112 ≤ 58368), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 57856 ≤ 58112) (by norm_num : 58112 ≤ 58368), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 57856 ≤ 58112) (by norm_num : 58112 ≤ 58368), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 57856 ≤ 58112) (by norm_num : 58112 ≤ 58368), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_57344_58368 :
    (∑ n ∈ Ico 57344 58368, mobiusTreeValue 16 mobiusTable1200001 n) = (-11 : ℤ) ∧
    (∑ n ∈ Ico 57344 58368, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (623 : ℕ) ∧
    (∑ n ∈ Ico 57344 58368, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-940747 : ℤ) ∧
    (∑ n ∈ Ico 57344 58368, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-18815011551080552594390483158 : ℤ) := by
  rcases cdemPrefixStats_57344_57856 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_57856_58368 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 57344 ≤ 57856) (by norm_num : 57856 ≤ 58368), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 57344 ≤ 57856) (by norm_num : 57856 ≤ 58368), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 57344 ≤ 57856) (by norm_num : 57856 ≤ 58368), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 57344 ≤ 57856) (by norm_num : 57856 ≤ 58368), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_58368_58432 :
    (∑ n ∈ Ico 58368 58432, mobiusTreeValue 16 mobiusTable1200001 n) = (4 : ℤ) ∧
    (∑ n ∈ Ico 58368 58432, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 58368 58432, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (342649 : ℤ) ∧
    (∑ n ∈ Ico 58368 58432, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (6853038141677908984131959568 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_58432_58496 :
    (∑ n ∈ Ico 58432 58496, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 58432 58496, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 58432 58496, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (85466 : ℤ) ∧
    (∑ n ∈ Ico 58432 58496, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1709313729298790190767540242 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_58368_58496 :
    (∑ n ∈ Ico 58368 58496, mobiusTreeValue 16 mobiusTable1200001 n) = (5 : ℤ) ∧
    (∑ n ∈ Ico 58368 58496, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 58368 58496, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (428115 : ℤ) ∧
    (∑ n ∈ Ico 58368 58496, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (8562351870976699174899499810 : ℤ) := by
  rcases cdemPrefixStats_58368_58432 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_58432_58496 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 58368 ≤ 58432) (by norm_num : 58432 ≤ 58496), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 58368 ≤ 58432) (by norm_num : 58432 ≤ 58496), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 58368 ≤ 58432) (by norm_num : 58432 ≤ 58496), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 58368 ≤ 58432) (by norm_num : 58432 ≤ 58496), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_58496_58560 :
    (∑ n ∈ Ico 58496 58560, mobiusTreeValue 16 mobiusTable1200001 n) = (5 : ℤ) ∧
    (∑ n ∈ Ico 58496 58560, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 58496 58560, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (427195 : ℤ) ∧
    (∑ n ∈ Ico 58496 58560, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (8543942636356757542738538328 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_58560_58624 :
    (∑ n ∈ Ico 58560 58624, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 58560 58624, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 58560 58624, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (193 : ℤ) ∧
    (∑ n ∈ Ico 58560 58624, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (3817010856541128649237140 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_58496_58624 :
    (∑ n ∈ Ico 58496 58624, mobiusTreeValue 16 mobiusTable1200001 n) = (5 : ℤ) ∧
    (∑ n ∈ Ico 58496 58624, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (79 : ℕ) ∧
    (∑ n ∈ Ico 58496 58624, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (427388 : ℤ) ∧
    (∑ n ∈ Ico 58496 58624, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (8547759647213298671387775468 : ℤ) := by
  rcases cdemPrefixStats_58496_58560 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_58560_58624 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 58496 ≤ 58560) (by norm_num : 58560 ≤ 58624), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 58496 ≤ 58560) (by norm_num : 58560 ≤ 58624), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 58496 ≤ 58560) (by norm_num : 58560 ≤ 58624), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 58496 ≤ 58560) (by norm_num : 58560 ≤ 58624), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_58368_58624 :
    (∑ n ∈ Ico 58368 58624, mobiusTreeValue 16 mobiusTable1200001 n) = (10 : ℤ) ∧
    (∑ n ∈ Ico 58368 58624, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (156 : ℕ) ∧
    (∑ n ∈ Ico 58368 58624, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (855503 : ℤ) ∧
    (∑ n ∈ Ico 58368 58624, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (17110111518189997846287275278 : ℤ) := by
  rcases cdemPrefixStats_58368_58496 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_58496_58624 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 58368 ≤ 58496) (by norm_num : 58496 ≤ 58624), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 58368 ≤ 58496) (by norm_num : 58496 ≤ 58624), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 58368 ≤ 58496) (by norm_num : 58496 ≤ 58624), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 58368 ≤ 58496) (by norm_num : 58496 ≤ 58624), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_58624_58688 :
    (∑ n ∈ Ico 58624 58688, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 58624 58688, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 58624 58688, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (85392 : ℤ) ∧
    (∑ n ∈ Ico 58624 58688, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1707819440584901203093117464 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_58688_58752 :
    (∑ n ∈ Ico 58688 58752, mobiusTreeValue 16 mobiusTable1200001 n) = (-4 : ℤ) ∧
    (∑ n ∈ Ico 58688 58752, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 58688 58752, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-340575 : ℤ) ∧
    (∑ n ∈ Ico 58688 58752, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-6811526214790365227406520797 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_58624_58752 :
    (∑ n ∈ Ico 58624 58752, mobiusTreeValue 16 mobiusTable1200001 n) = (-3 : ℤ) ∧
    (∑ n ∈ Ico 58624 58752, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (75 : ℕ) ∧
    (∑ n ∈ Ico 58624 58752, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-255183 : ℤ) ∧
    (∑ n ∈ Ico 58624 58752, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-5103706774205464024313403333 : ℤ) := by
  rcases cdemPrefixStats_58624_58688 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_58688_58752 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 58624 ≤ 58688) (by norm_num : 58688 ≤ 58752), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 58624 ≤ 58688) (by norm_num : 58688 ≤ 58752), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 58624 ≤ 58688) (by norm_num : 58688 ≤ 58752), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 58624 ≤ 58688) (by norm_num : 58688 ≤ 58752), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_58752_58816 :
    (∑ n ∈ Ico 58752 58816, mobiusTreeValue 16 mobiusTable1200001 n) = (3 : ℤ) ∧
    (∑ n ∈ Ico 58752 58816, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 58752 58816, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (255186 : ℤ) ∧
    (∑ n ∈ Ico 58752 58816, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (5103689872184701609980417911 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_58816_58880 :
    (∑ n ∈ Ico 58816 58880, mobiusTreeValue 16 mobiusTable1200001 n) = (5 : ℤ) ∧
    (∑ n ∈ Ico 58816 58880, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (35 : ℕ) ∧
    (∑ n ∈ Ico 58816 58880, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (424823 : ℤ) ∧
    (∑ n ∈ Ico 58816 58880, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (8496495526412138113727881515 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_58752_58880 :
    (∑ n ∈ Ico 58752 58880, mobiusTreeValue 16 mobiusTable1200001 n) = (8 : ℤ) ∧
    (∑ n ∈ Ico 58752 58880, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (76 : ℕ) ∧
    (∑ n ∈ Ico 58752 58880, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (680009 : ℤ) ∧
    (∑ n ∈ Ico 58752 58880, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (13600185398596839723708299426 : ℤ) := by
  rcases cdemPrefixStats_58752_58816 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_58816_58880 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 58752 ≤ 58816) (by norm_num : 58816 ≤ 58880), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 58752 ≤ 58816) (by norm_num : 58816 ≤ 58880), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 58752 ≤ 58816) (by norm_num : 58816 ≤ 58880), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 58752 ≤ 58816) (by norm_num : 58816 ≤ 58880), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_58624_58880 :
    (∑ n ∈ Ico 58624 58880, mobiusTreeValue 16 mobiusTable1200001 n) = (5 : ℤ) ∧
    (∑ n ∈ Ico 58624 58880, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (151 : ℕ) ∧
    (∑ n ∈ Ico 58624 58880, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (424826 : ℤ) ∧
    (∑ n ∈ Ico 58624 58880, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (8496478624391375699394896093 : ℤ) := by
  rcases cdemPrefixStats_58624_58752 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_58752_58880 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 58624 ≤ 58752) (by norm_num : 58752 ≤ 58880), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 58624 ≤ 58752) (by norm_num : 58752 ≤ 58880), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 58624 ≤ 58752) (by norm_num : 58752 ≤ 58880), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 58624 ≤ 58752) (by norm_num : 58752 ≤ 58880), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_58368_58880 :
    (∑ n ∈ Ico 58368 58880, mobiusTreeValue 16 mobiusTable1200001 n) = (15 : ℤ) ∧
    (∑ n ∈ Ico 58368 58880, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (307 : ℕ) ∧
    (∑ n ∈ Ico 58368 58880, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (1280329 : ℤ) ∧
    (∑ n ∈ Ico 58368 58880, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (25606590142581373545682171371 : ℤ) := by
  rcases cdemPrefixStats_58368_58624 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_58624_58880 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 58368 ≤ 58624) (by norm_num : 58624 ≤ 58880), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 58368 ≤ 58624) (by norm_num : 58624 ≤ 58880), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 58368 ≤ 58624) (by norm_num : 58624 ≤ 58880), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 58368 ≤ 58624) (by norm_num : 58624 ≤ 58880), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_58880_58944 :
    (∑ n ∈ Ico 58880 58944, mobiusTreeValue 16 mobiusTable1200001 n) = (-20 : ℤ) ∧
    (∑ n ∈ Ico 58880 58944, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 58880 58944, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-1697501 : ℤ) ∧
    (∑ n ∈ Ico 58880 58944, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-33950211964215991519066585001 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_58944_59008 :
    (∑ n ∈ Ico 58944 59008, mobiusTreeValue 16 mobiusTable1200001 n) = (-5 : ℤ) ∧
    (∑ n ∈ Ico 58944 59008, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 58944 59008, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-423976 : ℤ) ∧
    (∑ n ∈ Ico 58944 59008, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-8479548497866019138061223617 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_58880_59008 :
    (∑ n ∈ Ico 58880 59008, mobiusTreeValue 16 mobiusTable1200001 n) = (-25 : ℤ) ∧
    (∑ n ∈ Ico 58880 59008, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (79 : ℕ) ∧
    (∑ n ∈ Ico 58880 59008, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-2121477 : ℤ) ∧
    (∑ n ∈ Ico 58880 59008, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-42429760462082010657127808618 : ℤ) := by
  rcases cdemPrefixStats_58880_58944 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_58944_59008 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 58880 ≤ 58944) (by norm_num : 58944 ≤ 59008), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 58880 ≤ 58944) (by norm_num : 58944 ≤ 59008), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 58880 ≤ 58944) (by norm_num : 58944 ≤ 59008), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 58880 ≤ 58944) (by norm_num : 58944 ≤ 59008), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_59008_59072 :
    (∑ n ∈ Ico 59008 59072, mobiusTreeValue 16 mobiusTable1200001 n) = (-7 : ℤ) ∧
    (∑ n ∈ Ico 59008 59072, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 59008 59072, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-593138 : ℤ) ∧
    (∑ n ∈ Ico 59008 59072, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-11862853947617267632686609153 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_59072_59136 :
    (∑ n ∈ Ico 59072 59136, mobiusTreeValue 16 mobiusTable1200001 n) = (5 : ℤ) ∧
    (∑ n ∈ Ico 59072 59136, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 59072 59136, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (422708 : ℤ) ∧
    (∑ n ∈ Ico 59072 59136, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (8454197986717201834696014185 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_59008_59136 :
    (∑ n ∈ Ico 59008 59136, mobiusTreeValue 16 mobiusTable1200001 n) = (-2 : ℤ) ∧
    (∑ n ∈ Ico 59008 59136, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (80 : ℕ) ∧
    (∑ n ∈ Ico 59008 59136, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-170430 : ℤ) ∧
    (∑ n ∈ Ico 59008 59136, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-3408655960900065797990594968 : ℤ) := by
  rcases cdemPrefixStats_59008_59072 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_59072_59136 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 59008 ≤ 59072) (by norm_num : 59072 ≤ 59136), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 59008 ≤ 59072) (by norm_num : 59072 ≤ 59136), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 59008 ≤ 59072) (by norm_num : 59072 ≤ 59136), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 59008 ≤ 59072) (by norm_num : 59072 ≤ 59136), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_58880_59136 :
    (∑ n ∈ Ico 58880 59136, mobiusTreeValue 16 mobiusTable1200001 n) = (-27 : ℤ) ∧
    (∑ n ∈ Ico 58880 59136, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (159 : ℕ) ∧
    (∑ n ∈ Ico 58880 59136, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-2291907 : ℤ) ∧
    (∑ n ∈ Ico 58880 59136, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-45838416422982076455118403586 : ℤ) := by
  rcases cdemPrefixStats_58880_59008 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_59008_59136 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 58880 ≤ 59008) (by norm_num : 59008 ≤ 59136), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 58880 ≤ 59008) (by norm_num : 59008 ≤ 59136), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 58880 ≤ 59008) (by norm_num : 59008 ≤ 59136), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 58880 ≤ 59008) (by norm_num : 59008 ≤ 59136), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_59136_59200 :
    (∑ n ∈ Ico 59136 59200, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 59136 59200, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 59136 59200, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (84548 : ℤ) ∧
    (∑ n ∈ Ico 59136 59200, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1690987843447870206776661346 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_59200_59264 :
    (∑ n ∈ Ico 59200 59264, mobiusTreeValue 16 mobiusTable1200001 n) = (-3 : ℤ) ∧
    (∑ n ∈ Ico 59200 59264, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 59200 59264, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-253418 : ℤ) ∧
    (∑ n ∈ Ico 59200 59264, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-5068420804588188013511467926 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_59136_59264 :
    (∑ n ∈ Ico 59136 59264, mobiusTreeValue 16 mobiusTable1200001 n) = (-2 : ℤ) ∧
    (∑ n ∈ Ico 59136 59264, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 59136 59264, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-168870 : ℤ) ∧
    (∑ n ∈ Ico 59136 59264, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-3377432961140317806734806580 : ℤ) := by
  rcases cdemPrefixStats_59136_59200 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_59200_59264 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 59136 ≤ 59200) (by norm_num : 59200 ≤ 59264), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 59136 ≤ 59200) (by norm_num : 59200 ≤ 59264), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 59136 ≤ 59200) (by norm_num : 59200 ≤ 59264), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 59136 ≤ 59200) (by norm_num : 59200 ≤ 59264), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_59264_59328 :
    (∑ n ∈ Ico 59264 59328, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 59264 59328, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 59264 59328, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (84145 : ℤ) ∧
    (∑ n ∈ Ico 59264 59328, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1682928487743555034440050034 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_59328_59392 :
    (∑ n ∈ Ico 59328 59392, mobiusTreeValue 16 mobiusTable1200001 n) = (-5 : ℤ) ∧
    (∑ n ∈ Ico 59328 59392, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 59328 59392, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-421011 : ℤ) ∧
    (∑ n ∈ Ico 59328 59392, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-8420285274992045039661565571 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_59264_59392 :
    (∑ n ∈ Ico 59264 59392, mobiusTreeValue 16 mobiusTable1200001 n) = (-4 : ℤ) ∧
    (∑ n ∈ Ico 59264 59392, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 59264 59392, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-336866 : ℤ) ∧
    (∑ n ∈ Ico 59264 59392, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-6737356787248490005221515537 : ℤ) := by
  rcases cdemPrefixStats_59264_59328 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_59328_59392 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 59264 ≤ 59328) (by norm_num : 59328 ≤ 59392), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 59264 ≤ 59328) (by norm_num : 59328 ≤ 59392), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 59264 ≤ 59328) (by norm_num : 59328 ≤ 59392), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 59264 ≤ 59328) (by norm_num : 59328 ≤ 59392), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_59136_59392 :
    (∑ n ∈ Ico 59136 59392, mobiusTreeValue 16 mobiusTable1200001 n) = (-6 : ℤ) ∧
    (∑ n ∈ Ico 59136 59392, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (156 : ℕ) ∧
    (∑ n ∈ Ico 59136 59392, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-505736 : ℤ) ∧
    (∑ n ∈ Ico 59136 59392, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-10114789748388807811956322117 : ℤ) := by
  rcases cdemPrefixStats_59136_59264 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_59264_59392 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 59136 ≤ 59264) (by norm_num : 59264 ≤ 59392), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 59136 ≤ 59264) (by norm_num : 59264 ≤ 59392), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 59136 ≤ 59264) (by norm_num : 59264 ≤ 59392), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 59136 ≤ 59264) (by norm_num : 59264 ≤ 59392), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_58880_59392 :
    (∑ n ∈ Ico 58880 59392, mobiusTreeValue 16 mobiusTable1200001 n) = (-33 : ℤ) ∧
    (∑ n ∈ Ico 58880 59392, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (315 : ℕ) ∧
    (∑ n ∈ Ico 58880 59392, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-2797643 : ℤ) ∧
    (∑ n ∈ Ico 58880 59392, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-55953206171370884267074725703 : ℤ) := by
  rcases cdemPrefixStats_58880_59136 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_59136_59392 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 58880 ≤ 59136) (by norm_num : 59136 ≤ 59392), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 58880 ≤ 59136) (by norm_num : 59136 ≤ 59392), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 58880 ≤ 59136) (by norm_num : 59136 ≤ 59392), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 58880 ≤ 59136) (by norm_num : 59136 ≤ 59392), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_58368_59392 :
    (∑ n ∈ Ico 58368 59392, mobiusTreeValue 16 mobiusTable1200001 n) = (-18 : ℤ) ∧
    (∑ n ∈ Ico 58368 59392, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (622 : ℕ) ∧
    (∑ n ∈ Ico 58368 59392, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-1517314 : ℤ) ∧
    (∑ n ∈ Ico 58368 59392, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-30346616028789510721392554332 : ℤ) := by
  rcases cdemPrefixStats_58368_58880 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_58880_59392 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 58368 ≤ 58880) (by norm_num : 58880 ≤ 59392), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 58368 ≤ 58880) (by norm_num : 58880 ≤ 59392), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 58368 ≤ 58880) (by norm_num : 58880 ≤ 59392), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 58368 ≤ 58880) (by norm_num : 58880 ≤ 59392), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_57344_59392 :
    (∑ n ∈ Ico 57344 59392, mobiusTreeValue 16 mobiusTable1200001 n) = (-29 : ℤ) ∧
    (∑ n ∈ Ico 57344 59392, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (1245 : ℕ) ∧
    (∑ n ∈ Ico 57344 59392, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-2458061 : ℤ) ∧
    (∑ n ∈ Ico 57344 59392, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-49161627579870063315783037490 : ℤ) := by
  rcases cdemPrefixStats_57344_58368 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_58368_59392 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 57344 ≤ 58368) (by norm_num : 58368 ≤ 59392), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 57344 ≤ 58368) (by norm_num : 58368 ≤ 59392), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 57344 ≤ 58368) (by norm_num : 58368 ≤ 59392), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 57344 ≤ 58368) (by norm_num : 58368 ≤ 59392), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_59392_59456 :
    (∑ n ∈ Ico 59392 59456, mobiusTreeValue 16 mobiusTable1200001 n) = (-10 : ℤ) ∧
    (∑ n ∈ Ico 59392 59456, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 59392 59456, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-841552 : ℤ) ∧
    (∑ n ∈ Ico 59392 59456, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-16831022877290967737519717592 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_59456_59520 :
    (∑ n ∈ Ico 59456 59520, mobiusTreeValue 16 mobiusTable1200001 n) = (-3 : ℤ) ∧
    (∑ n ∈ Ico 59456 59520, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 59456 59520, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-252169 : ℤ) ∧
    (∑ n ∈ Ico 59456 59520, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-5043400325796401298748896833 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_59392_59520 :
    (∑ n ∈ Ico 59392 59520, mobiusTreeValue 16 mobiusTable1200001 n) = (-13 : ℤ) ∧
    (∑ n ∈ Ico 59392 59520, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (79 : ℕ) ∧
    (∑ n ∈ Ico 59392 59520, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-1093721 : ℤ) ∧
    (∑ n ∈ Ico 59392 59520, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-21874423203087369036268614425 : ℤ) := by
  rcases cdemPrefixStats_59392_59456 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_59456_59520 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 59392 ≤ 59456) (by norm_num : 59456 ≤ 59520), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 59392 ≤ 59456) (by norm_num : 59456 ≤ 59520), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 59392 ≤ 59456) (by norm_num : 59456 ≤ 59520), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 59392 ≤ 59456) (by norm_num : 59456 ≤ 59520), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_59520_59584 :
    (∑ n ∈ Ico 59520 59584, mobiusTreeValue 16 mobiusTable1200001 n) = (-7 : ℤ) ∧
    (∑ n ∈ Ico 59520 59584, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 59520 59584, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-587698 : ℤ) ∧
    (∑ n ∈ Ico 59520 59584, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-11754037739064646899239900233 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_59584_59648 :
    (∑ n ∈ Ico 59584 59648, mobiusTreeValue 16 mobiusTable1200001 n) = (5 : ℤ) ∧
    (∑ n ∈ Ico 59584 59648, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 59584 59648, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (419558 : ℤ) ∧
    (∑ n ∈ Ico 59584 59648, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (8391202970921964917789497744 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_59520_59648 :
    (∑ n ∈ Ico 59520 59648, mobiusTreeValue 16 mobiusTable1200001 n) = (-2 : ℤ) ∧
    (∑ n ∈ Ico 59520 59648, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 59520 59648, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-168140 : ℤ) ∧
    (∑ n ∈ Ico 59520 59648, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-3362834768142681981450402489 : ℤ) := by
  rcases cdemPrefixStats_59520_59584 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_59584_59648 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 59520 ≤ 59584) (by norm_num : 59584 ≤ 59648), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 59520 ≤ 59584) (by norm_num : 59584 ≤ 59648), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 59520 ≤ 59584) (by norm_num : 59584 ≤ 59648), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 59520 ≤ 59584) (by norm_num : 59584 ≤ 59648), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_59392_59648 :
    (∑ n ∈ Ico 59392 59648, mobiusTreeValue 16 mobiusTable1200001 n) = (-15 : ℤ) ∧
    (∑ n ∈ Ico 59392 59648, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (157 : ℕ) ∧
    (∑ n ∈ Ico 59392 59648, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-1261861 : ℤ) ∧
    (∑ n ∈ Ico 59392 59648, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-25237257971230051017719016914 : ℤ) := by
  rcases cdemPrefixStats_59392_59520 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_59520_59648 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 59392 ≤ 59520) (by norm_num : 59520 ≤ 59648), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 59392 ≤ 59520) (by norm_num : 59520 ≤ 59648), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 59392 ≤ 59520) (by norm_num : 59520 ≤ 59648), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 59392 ≤ 59520) (by norm_num : 59520 ≤ 59648), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_59648_59712 :
    (∑ n ∈ Ico 59648 59712, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 59648 59712, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 59648 59712, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (83718 : ℤ) ∧
    (∑ n ∈ Ico 59648 59712, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1674282535856382352314697315 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_59712_59776 :
    (∑ n ∈ Ico 59712 59776, mobiusTreeValue 16 mobiusTable1200001 n) = (6 : ℤ) ∧
    (∑ n ∈ Ico 59712 59776, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 59712 59776, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (501746 : ℤ) ∧
    (∑ n ∈ Ico 59712 59776, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (10034977286343706304694400804 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_59648_59776 :
    (∑ n ∈ Ico 59648 59776, mobiusTreeValue 16 mobiusTable1200001 n) = (7 : ℤ) ∧
    (∑ n ∈ Ico 59648 59776, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (75 : ℕ) ∧
    (∑ n ∈ Ico 59648 59776, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (585464 : ℤ) ∧
    (∑ n ∈ Ico 59648 59776, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (11709259822200088657009098119 : ℤ) := by
  rcases cdemPrefixStats_59648_59712 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_59712_59776 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 59648 ≤ 59712) (by norm_num : 59712 ≤ 59776), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 59648 ≤ 59712) (by norm_num : 59712 ≤ 59776), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 59648 ≤ 59712) (by norm_num : 59712 ≤ 59776), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 59648 ≤ 59712) (by norm_num : 59712 ≤ 59776), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_59776_59840 :
    (∑ n ∈ Ico 59776 59840, mobiusTreeValue 16 mobiusTable1200001 n) = (-7 : ℤ) ∧
    (∑ n ∈ Ico 59776 59840, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 59776 59840, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-585300 : ℤ) ∧
    (∑ n ∈ Ico 59776 59840, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-11706077227563668932392026695 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_59840_59904 :
    (∑ n ∈ Ico 59840 59904, mobiusTreeValue 16 mobiusTable1200001 n) = (7 : ℤ) ∧
    (∑ n ∈ Ico 59840 59904, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 59840 59904, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (584614 : ℤ) ∧
    (∑ n ∈ Ico 59840 59904, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (11692307519284506760041120670 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_59776_59904 :
    (∑ n ∈ Ico 59776 59904, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 59776 59904, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 59776 59904, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-686 : ℤ) ∧
    (∑ n ∈ Ico 59776 59904, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-13769708279162172350906025 : ℤ) := by
  rcases cdemPrefixStats_59776_59840 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_59840_59904 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 59776 ≤ 59840) (by norm_num : 59840 ≤ 59904), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 59776 ≤ 59840) (by norm_num : 59840 ≤ 59904), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 59776 ≤ 59840) (by norm_num : 59840 ≤ 59904), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 59776 ≤ 59840) (by norm_num : 59840 ≤ 59904), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_59648_59904 :
    (∑ n ∈ Ico 59648 59904, mobiusTreeValue 16 mobiusTable1200001 n) = (7 : ℤ) ∧
    (∑ n ∈ Ico 59648 59904, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (153 : ℕ) ∧
    (∑ n ∈ Ico 59648 59904, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (584778 : ℤ) ∧
    (∑ n ∈ Ico 59648 59904, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (11695490113920926484658192094 : ℤ) := by
  rcases cdemPrefixStats_59648_59776 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_59776_59904 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 59648 ≤ 59776) (by norm_num : 59776 ≤ 59904), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 59648 ≤ 59776) (by norm_num : 59776 ≤ 59904), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 59648 ≤ 59776) (by norm_num : 59776 ≤ 59904), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 59648 ≤ 59776) (by norm_num : 59776 ≤ 59904), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_59392_59904 :
    (∑ n ∈ Ico 59392 59904, mobiusTreeValue 16 mobiusTable1200001 n) = (-8 : ℤ) ∧
    (∑ n ∈ Ico 59392 59904, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (310 : ℕ) ∧
    (∑ n ∈ Ico 59392 59904, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-677083 : ℤ) ∧
    (∑ n ∈ Ico 59392 59904, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-13541767857309124533060824820 : ℤ) := by
  rcases cdemPrefixStats_59392_59648 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_59648_59904 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 59392 ≤ 59648) (by norm_num : 59648 ≤ 59904), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 59392 ≤ 59648) (by norm_num : 59648 ≤ 59904), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 59392 ≤ 59648) (by norm_num : 59648 ≤ 59904), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 59392 ≤ 59648) (by norm_num : 59648 ≤ 59904), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_59904_59968 :
    (∑ n ∈ Ico 59904 59968, mobiusTreeValue 16 mobiusTable1200001 n) = (12 : ℤ) ∧
    (∑ n ∈ Ico 59904 59968, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 59904 59968, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (1001092 : ℤ) ∧
    (∑ n ∈ Ico 59904 59968, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (20021970157824879705368983521 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_59968_60032 :
    (∑ n ∈ Ico 59968 60032, mobiusTreeValue 16 mobiusTable1200001 n) = (8 : ℤ) ∧
    (∑ n ∈ Ico 59968 60032, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 59968 60032, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (666644 : ℤ) ∧
    (∑ n ∈ Ico 59968 60032, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (13332946160700403452507463638 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_59904_60032 :
    (∑ n ∈ Ico 59904 60032, mobiusTreeValue 16 mobiusTable1200001 n) = (20 : ℤ) ∧
    (∑ n ∈ Ico 59904 60032, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 59904 60032, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (1667736 : ℤ) ∧
    (∑ n ∈ Ico 59904 60032, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (33354916318525283157876447159 : ℤ) := by
  rcases cdemPrefixStats_59904_59968 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_59968_60032 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 59904 ≤ 59968) (by norm_num : 59968 ≤ 60032), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 59904 ≤ 59968) (by norm_num : 59968 ≤ 60032), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 59904 ≤ 59968) (by norm_num : 59968 ≤ 60032), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 59904 ≤ 59968) (by norm_num : 59968 ≤ 60032), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_60032_60096 :
    (∑ n ∈ Ico 60032 60096, mobiusTreeValue 16 mobiusTable1200001 n) = (-11 : ℤ) ∧
    (∑ n ∈ Ico 60032 60096, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 60032 60096, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-915812 : ℤ) ∧
    (∑ n ∈ Ico 60032 60096, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-18316294612157655209929514881 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_60096_60160 :
    (∑ n ∈ Ico 60096 60160, mobiusTreeValue 16 mobiusTable1200001 n) = (-5 : ℤ) ∧
    (∑ n ∈ Ico 60096 60160, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 60096 60160, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-415816 : ℤ) ∧
    (∑ n ∈ Ico 60096 60160, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-8316369953384898124805750036 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_60032_60160 :
    (∑ n ∈ Ico 60032 60160, mobiusTreeValue 16 mobiusTable1200001 n) = (-16 : ℤ) ∧
    (∑ n ∈ Ico 60032 60160, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (80 : ℕ) ∧
    (∑ n ∈ Ico 60032 60160, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-1331628 : ℤ) ∧
    (∑ n ∈ Ico 60032 60160, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-26632664565542553334735264917 : ℤ) := by
  rcases cdemPrefixStats_60032_60096 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_60096_60160 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 60032 ≤ 60096) (by norm_num : 60096 ≤ 60160), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 60032 ≤ 60096) (by norm_num : 60096 ≤ 60160), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 60032 ≤ 60096) (by norm_num : 60096 ≤ 60160), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 60032 ≤ 60096) (by norm_num : 60096 ≤ 60160), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_59904_60160 :
    (∑ n ∈ Ico 59904 60160, mobiusTreeValue 16 mobiusTable1200001 n) = (4 : ℤ) ∧
    (∑ n ∈ Ico 59904 60160, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (158 : ℕ) ∧
    (∑ n ∈ Ico 59904 60160, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (336108 : ℤ) ∧
    (∑ n ∈ Ico 59904 60160, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (6722251752982729823141182242 : ℤ) := by
  rcases cdemPrefixStats_59904_60032 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_60032_60160 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 59904 ≤ 60032) (by norm_num : 60032 ≤ 60160), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 59904 ≤ 60032) (by norm_num : 60032 ≤ 60160), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 59904 ≤ 60032) (by norm_num : 60032 ≤ 60160), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 59904 ≤ 60032) (by norm_num : 60032 ≤ 60160), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_60160_60224 :
    (∑ n ∈ Ico 60160 60224, mobiusTreeValue 16 mobiusTable1200001 n) = (12 : ℤ) ∧
    (∑ n ∈ Ico 60160 60224, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 60160 60224, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (996838 : ℤ) ∧
    (∑ n ∈ Ico 60160 60224, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (19936976540592214260095103721 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_60224_60288 :
    (∑ n ∈ Ico 60224 60288, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 60224 60288, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 60224 60288, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (83048 : ℤ) ∧
    (∑ n ∈ Ico 60224 60288, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1660962979794309376305909435 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_60160_60288 :
    (∑ n ∈ Ico 60160 60288, mobiusTreeValue 16 mobiusTable1200001 n) = (13 : ℤ) ∧
    (∑ n ∈ Ico 60160 60288, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 60160 60288, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (1079886 : ℤ) ∧
    (∑ n ∈ Ico 60160 60288, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (21597939520386523636401013156 : ℤ) := by
  rcases cdemPrefixStats_60160_60224 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_60224_60288 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 60160 ≤ 60224) (by norm_num : 60224 ≤ 60288), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 60160 ≤ 60224) (by norm_num : 60224 ≤ 60288), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 60160 ≤ 60224) (by norm_num : 60224 ≤ 60288), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 60160 ≤ 60224) (by norm_num : 60224 ≤ 60288), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_60288_60352 :
    (∑ n ∈ Ico 60288 60352, mobiusTreeValue 16 mobiusTable1200001 n) = (4 : ℤ) ∧
    (∑ n ∈ Ico 60288 60352, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 60288 60352, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (331412 : ℤ) ∧
    (∑ n ∈ Ico 60288 60352, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (6628249189887230305508593376 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_60352_60416 :
    (∑ n ∈ Ico 60352 60416, mobiusTreeValue 16 mobiusTable1200001 n) = (4 : ℤ) ∧
    (∑ n ∈ Ico 60352 60416, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 60352 60416, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (331373 : ℤ) ∧
    (∑ n ∈ Ico 60352 60416, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (6627507582373333148116482395 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_60288_60416 :
    (∑ n ∈ Ico 60288 60416, mobiusTreeValue 16 mobiusTable1200001 n) = (8 : ℤ) ∧
    (∑ n ∈ Ico 60288 60416, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 60288 60416, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (662785 : ℤ) ∧
    (∑ n ∈ Ico 60288 60416, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (13255756772260563453625075771 : ℤ) := by
  rcases cdemPrefixStats_60288_60352 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_60352_60416 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 60288 ≤ 60352) (by norm_num : 60352 ≤ 60416), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 60288 ≤ 60352) (by norm_num : 60352 ≤ 60416), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 60288 ≤ 60352) (by norm_num : 60352 ≤ 60416), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 60288 ≤ 60352) (by norm_num : 60352 ≤ 60416), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_60160_60416 :
    (∑ n ∈ Ico 60160 60416, mobiusTreeValue 16 mobiusTable1200001 n) = (21 : ℤ) ∧
    (∑ n ∈ Ico 60160 60416, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (155 : ℕ) ∧
    (∑ n ∈ Ico 60160 60416, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (1742671 : ℤ) ∧
    (∑ n ∈ Ico 60160 60416, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (34853696292647087090026088927 : ℤ) := by
  rcases cdemPrefixStats_60160_60288 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_60288_60416 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 60160 ≤ 60288) (by norm_num : 60288 ≤ 60416), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 60160 ≤ 60288) (by norm_num : 60288 ≤ 60416), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 60160 ≤ 60288) (by norm_num : 60288 ≤ 60416), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 60160 ≤ 60288) (by norm_num : 60288 ≤ 60416), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_59904_60416 :
    (∑ n ∈ Ico 59904 60416, mobiusTreeValue 16 mobiusTable1200001 n) = (25 : ℤ) ∧
    (∑ n ∈ Ico 59904 60416, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (313 : ℕ) ∧
    (∑ n ∈ Ico 59904 60416, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (2078779 : ℤ) ∧
    (∑ n ∈ Ico 59904 60416, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (41575948045629816913167271169 : ℤ) := by
  rcases cdemPrefixStats_59904_60160 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_60160_60416 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 59904 ≤ 60160) (by norm_num : 60160 ≤ 60416), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 59904 ≤ 60160) (by norm_num : 60160 ≤ 60416), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 59904 ≤ 60160) (by norm_num : 60160 ≤ 60416), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 59904 ≤ 60160) (by norm_num : 60160 ≤ 60416), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_59392_60416 :
    (∑ n ∈ Ico 59392 60416, mobiusTreeValue 16 mobiusTable1200001 n) = (17 : ℤ) ∧
    (∑ n ∈ Ico 59392 60416, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (623 : ℕ) ∧
    (∑ n ∈ Ico 59392 60416, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (1401696 : ℤ) ∧
    (∑ n ∈ Ico 59392 60416, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (28034180188320692380106446349 : ℤ) := by
  rcases cdemPrefixStats_59392_59904 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_59904_60416 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 59392 ≤ 59904) (by norm_num : 59904 ≤ 60416), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 59392 ≤ 59904) (by norm_num : 59904 ≤ 60416), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 59392 ≤ 59904) (by norm_num : 59904 ≤ 60416), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 59392 ≤ 59904) (by norm_num : 59904 ≤ 60416), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_60416_60480 :
    (∑ n ∈ Ico 60416 60480, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 60416 60480, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 60416 60480, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (100 : ℤ) ∧
    (∑ n ∈ Ico 60416 60480, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1969248689584492386888987 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_60480_60544 :
    (∑ n ∈ Ico 60480 60544, mobiusTreeValue 16 mobiusTable1200001 n) = (16 : ℤ) ∧
    (∑ n ∈ Ico 60480 60544, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 60480 60544, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (1322296 : ℤ) ∧
    (∑ n ∈ Ico 60480 60544, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (26446092448752437489996262576 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_60416_60544 :
    (∑ n ∈ Ico 60416 60544, mobiusTreeValue 16 mobiusTable1200001 n) = (16 : ℤ) ∧
    (∑ n ∈ Ico 60416 60544, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 60416 60544, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (1322396 : ℤ) ∧
    (∑ n ∈ Ico 60416 60544, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (26448061697442021982383151563 : ℤ) := by
  rcases cdemPrefixStats_60416_60480 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_60480_60544 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 60416 ≤ 60480) (by norm_num : 60480 ≤ 60544), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 60416 ≤ 60480) (by norm_num : 60480 ≤ 60544), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 60416 ≤ 60480) (by norm_num : 60480 ≤ 60544), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 60416 ≤ 60480) (by norm_num : 60480 ≤ 60544), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_60544_60608 :
    (∑ n ∈ Ico 60544 60608, mobiusTreeValue 16 mobiusTable1200001 n) = (3 : ℤ) ∧
    (∑ n ∈ Ico 60544 60608, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 60544 60608, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (247854 : ℤ) ∧
    (∑ n ∈ Ico 60544 60608, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (4957089935220070091661590360 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_60608_60672 :
    (∑ n ∈ Ico 60608 60672, mobiusTreeValue 16 mobiusTable1200001 n) = (-11 : ℤ) ∧
    (∑ n ∈ Ico 60608 60672, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 60608 60672, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-906935 : ℤ) ∧
    (∑ n ∈ Ico 60608 60672, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-18138811646212320272991212545 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_60544_60672 :
    (∑ n ∈ Ico 60544 60672, mobiusTreeValue 16 mobiusTable1200001 n) = (-8 : ℤ) ∧
    (∑ n ∈ Ico 60544 60672, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 60544 60672, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-659081 : ℤ) ∧
    (∑ n ∈ Ico 60544 60672, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-13181721710992250181329622185 : ℤ) := by
  rcases cdemPrefixStats_60544_60608 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_60608_60672 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 60544 ≤ 60608) (by norm_num : 60608 ≤ 60672), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 60544 ≤ 60608) (by norm_num : 60608 ≤ 60672), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 60544 ≤ 60608) (by norm_num : 60608 ≤ 60672), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 60544 ≤ 60608) (by norm_num : 60608 ≤ 60672), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_60416_60672 :
    (∑ n ∈ Ico 60416 60672, mobiusTreeValue 16 mobiusTable1200001 n) = (8 : ℤ) ∧
    (∑ n ∈ Ico 60416 60672, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (156 : ℕ) ∧
    (∑ n ∈ Ico 60416 60672, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (663315 : ℤ) ∧
    (∑ n ∈ Ico 60416 60672, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (13266339986449771801053529378 : ℤ) := by
  rcases cdemPrefixStats_60416_60544 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_60544_60672 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 60416 ≤ 60544) (by norm_num : 60544 ≤ 60672), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 60416 ≤ 60544) (by norm_num : 60544 ≤ 60672), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 60416 ≤ 60544) (by norm_num : 60544 ≤ 60672), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 60416 ≤ 60544) (by norm_num : 60544 ≤ 60672), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_60672_60736 :
    (∑ n ∈ Ico 60672 60736, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 60672 60736, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 60672 60736, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (82396 : ℤ) ∧
    (∑ n ∈ Ico 60672 60736, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1647933259563603880486704335 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_60736_60800 :
    (∑ n ∈ Ico 60736 60800, mobiusTreeValue 16 mobiusTable1200001 n) = (-4 : ℤ) ∧
    (∑ n ∈ Ico 60736 60800, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 60736 60800, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-329064 : ℤ) ∧
    (∑ n ∈ Ico 60736 60800, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-6581301581587578082888554138 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_60672_60800 :
    (∑ n ∈ Ico 60672 60800, mobiusTreeValue 16 mobiusTable1200001 n) = (-3 : ℤ) ∧
    (∑ n ∈ Ico 60672 60800, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (79 : ℕ) ∧
    (∑ n ∈ Ico 60672 60800, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-246668 : ℤ) ∧
    (∑ n ∈ Ico 60672 60800, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-4933368322023974202401849803 : ℤ) := by
  rcases cdemPrefixStats_60672_60736 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_60736_60800 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 60672 ≤ 60736) (by norm_num : 60736 ≤ 60800), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 60672 ≤ 60736) (by norm_num : 60736 ≤ 60800), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 60672 ≤ 60736) (by norm_num : 60736 ≤ 60800), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 60672 ≤ 60736) (by norm_num : 60736 ≤ 60800), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_60800_60864 :
    (∑ n ∈ Ico 60800 60864, mobiusTreeValue 16 mobiusTable1200001 n) = (4 : ℤ) ∧
    (∑ n ∈ Ico 60800 60864, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 60800 60864, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (328899 : ℤ) ∧
    (∑ n ∈ Ico 60800 60864, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (6578001598260989093302504995 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_60864_60928 :
    (∑ n ∈ Ico 60864 60928, mobiusTreeValue 16 mobiusTable1200001 n) = (-12 : ℤ) ∧
    (∑ n ∈ Ico 60864 60928, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 60864 60928, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-984986 : ℤ) ∧
    (∑ n ∈ Ico 60864 60928, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-19699824114981490118167829404 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_60800_60928 :
    (∑ n ∈ Ico 60800 60928, mobiusTreeValue 16 mobiusTable1200001 n) = (-8 : ℤ) ∧
    (∑ n ∈ Ico 60800 60928, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 60800 60928, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-656087 : ℤ) ∧
    (∑ n ∈ Ico 60800 60928, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-13121822516720501024865324409 : ℤ) := by
  rcases cdemPrefixStats_60800_60864 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_60864_60928 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 60800 ≤ 60864) (by norm_num : 60864 ≤ 60928), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 60800 ≤ 60864) (by norm_num : 60864 ≤ 60928), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 60800 ≤ 60864) (by norm_num : 60864 ≤ 60928), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 60800 ≤ 60864) (by norm_num : 60864 ≤ 60928), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_60672_60928 :
    (∑ n ∈ Ico 60672 60928, mobiusTreeValue 16 mobiusTable1200001 n) = (-11 : ℤ) ∧
    (∑ n ∈ Ico 60672 60928, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (157 : ℕ) ∧
    (∑ n ∈ Ico 60672 60928, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-902755 : ℤ) ∧
    (∑ n ∈ Ico 60672 60928, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-18055190838744475227267174212 : ℤ) := by
  rcases cdemPrefixStats_60672_60800 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_60800_60928 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 60672 ≤ 60800) (by norm_num : 60800 ≤ 60928), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 60672 ≤ 60800) (by norm_num : 60800 ≤ 60928), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 60672 ≤ 60800) (by norm_num : 60800 ≤ 60928), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 60672 ≤ 60800) (by norm_num : 60800 ≤ 60928), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_60416_60928 :
    (∑ n ∈ Ico 60416 60928, mobiusTreeValue 16 mobiusTable1200001 n) = (-3 : ℤ) ∧
    (∑ n ∈ Ico 60416 60928, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (313 : ℕ) ∧
    (∑ n ∈ Ico 60416 60928, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-239440 : ℤ) ∧
    (∑ n ∈ Ico 60416 60928, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-4788850852294703426213644834 : ℤ) := by
  rcases cdemPrefixStats_60416_60672 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_60672_60928 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 60416 ≤ 60672) (by norm_num : 60672 ≤ 60928), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 60416 ≤ 60672) (by norm_num : 60672 ≤ 60928), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 60416 ≤ 60672) (by norm_num : 60672 ≤ 60928), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 60416 ≤ 60672) (by norm_num : 60672 ≤ 60928), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_60928_60992 :
    (∑ n ∈ Ico 60928 60992, mobiusTreeValue 16 mobiusTable1200001 n) = (-3 : ℤ) ∧
    (∑ n ∈ Ico 60928 60992, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 60928 60992, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-246246 : ℤ) ∧
    (∑ n ∈ Ico 60928 60992, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-4924973363356978069437320817 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_60992_61056 :
    (∑ n ∈ Ico 60992 61056, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 60992 61056, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (36 : ℕ) ∧
    (∑ n ∈ Ico 60992 61056, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (60 : ℤ) ∧
    (∑ n ∈ Ico 60992 61056, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1073821423875669589709171 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_60928_61056 :
    (∑ n ∈ Ico 60928 61056, mobiusTreeValue 16 mobiusTable1200001 n) = (-3 : ℤ) ∧
    (∑ n ∈ Ico 60928 61056, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 60928 61056, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-246186 : ℤ) ∧
    (∑ n ∈ Ico 60928 61056, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-4923899541933102399847611646 : ℤ) := by
  rcases cdemPrefixStats_60928_60992 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_60992_61056 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 60928 ≤ 60992) (by norm_num : 60992 ≤ 61056), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 60928 ≤ 60992) (by norm_num : 60992 ≤ 61056), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 60928 ≤ 60992) (by norm_num : 60992 ≤ 61056), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 60928 ≤ 60992) (by norm_num : 60992 ≤ 61056), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_61056_61120 :
    (∑ n ∈ Ico 61056 61120, mobiusTreeValue 16 mobiusTable1200001 n) = (9 : ℤ) ∧
    (∑ n ∈ Ico 61056 61120, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 61056 61120, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (736706 : ℤ) ∧
    (∑ n ∈ Ico 61056 61120, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (14734159862606231343755993058 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_61120_61184 :
    (∑ n ∈ Ico 61120 61184, mobiusTreeValue 16 mobiusTable1200001 n) = (5 : ℤ) ∧
    (∑ n ∈ Ico 61120 61184, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 61120 61184, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (408828 : ℤ) ∧
    (∑ n ∈ Ico 61120 61184, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (8176642487070121982078833459 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_61056_61184 :
    (∑ n ∈ Ico 61056 61184, mobiusTreeValue 16 mobiusTable1200001 n) = (14 : ℤ) ∧
    (∑ n ∈ Ico 61056 61184, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 61056 61184, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (1145534 : ℤ) ∧
    (∑ n ∈ Ico 61056 61184, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (22910802349676353325834826517 : ℤ) := by
  rcases cdemPrefixStats_61056_61120 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_61120_61184 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 61056 ≤ 61120) (by norm_num : 61120 ≤ 61184), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 61056 ≤ 61120) (by norm_num : 61120 ≤ 61184), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 61056 ≤ 61120) (by norm_num : 61120 ≤ 61184), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 61056 ≤ 61120) (by norm_num : 61120 ≤ 61184), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_60928_61184 :
    (∑ n ∈ Ico 60928 61184, mobiusTreeValue 16 mobiusTable1200001 n) = (11 : ℤ) ∧
    (∑ n ∈ Ico 60928 61184, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (155 : ℕ) ∧
    (∑ n ∈ Ico 60928 61184, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (899348 : ℤ) ∧
    (∑ n ∈ Ico 60928 61184, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (17986902807743250925987214871 : ℤ) := by
  rcases cdemPrefixStats_60928_61056 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_61056_61184 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 60928 ≤ 61056) (by norm_num : 61056 ≤ 61184), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 60928 ≤ 61056) (by norm_num : 61056 ≤ 61184), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 60928 ≤ 61056) (by norm_num : 61056 ≤ 61184), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 60928 ≤ 61056) (by norm_num : 61056 ≤ 61184), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_61184_61248 :
    (∑ n ∈ Ico 61184 61248, mobiusTreeValue 16 mobiusTable1200001 n) = (-3 : ℤ) ∧
    (∑ n ∈ Ico 61184 61248, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 61184 61248, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-244781 : ℤ) ∧
    (∑ n ∈ Ico 61184 61248, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-4895715569572185403440719460 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_61248_61312 :
    (∑ n ∈ Ico 61248 61312, mobiusTreeValue 16 mobiusTable1200001 n) = (11 : ℤ) ∧
    (∑ n ∈ Ico 61248 61312, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 61248 61312, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (897370 : ℤ) ∧
    (∑ n ∈ Ico 61248 61312, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (17947516713546988192072015378 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_61184_61312 :
    (∑ n ∈ Ico 61184 61312, mobiusTreeValue 16 mobiusTable1200001 n) = (8 : ℤ) ∧
    (∑ n ∈ Ico 61184 61312, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (80 : ℕ) ∧
    (∑ n ∈ Ico 61184 61312, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (652589 : ℤ) ∧
    (∑ n ∈ Ico 61184 61312, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (13051801143974802788631295918 : ℤ) := by
  rcases cdemPrefixStats_61184_61248 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_61248_61312 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 61184 ≤ 61248) (by norm_num : 61248 ≤ 61312), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 61184 ≤ 61248) (by norm_num : 61248 ≤ 61312), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 61184 ≤ 61248) (by norm_num : 61248 ≤ 61312), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 61184 ≤ 61248) (by norm_num : 61248 ≤ 61312), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_61312_61376 :
    (∑ n ∈ Ico 61312 61376, mobiusTreeValue 16 mobiusTable1200001 n) = (3 : ℤ) ∧
    (∑ n ∈ Ico 61312 61376, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 61312 61376, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (244686 : ℤ) ∧
    (∑ n ∈ Ico 61312 61376, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (4893723603334606443727979656 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_61376_61440 :
    (∑ n ∈ Ico 61376 61440, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 61376 61440, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 61376 61440, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (81332 : ℤ) ∧
    (∑ n ∈ Ico 61376 61440, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1626623001438655670768933697 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_61312_61440 :
    (∑ n ∈ Ico 61312 61440, mobiusTreeValue 16 mobiusTable1200001 n) = (4 : ℤ) ∧
    (∑ n ∈ Ico 61312 61440, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 61312 61440, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (326018 : ℤ) ∧
    (∑ n ∈ Ico 61312 61440, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (6520346604773262114496913353 : ℤ) := by
  rcases cdemPrefixStats_61312_61376 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_61376_61440 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 61312 ≤ 61376) (by norm_num : 61376 ≤ 61440), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 61312 ≤ 61376) (by norm_num : 61376 ≤ 61440), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 61312 ≤ 61376) (by norm_num : 61376 ≤ 61440), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 61312 ≤ 61376) (by norm_num : 61376 ≤ 61440), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_61184_61440 :
    (∑ n ∈ Ico 61184 61440, mobiusTreeValue 16 mobiusTable1200001 n) = (12 : ℤ) ∧
    (∑ n ∈ Ico 61184 61440, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (158 : ℕ) ∧
    (∑ n ∈ Ico 61184 61440, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (978607 : ℤ) ∧
    (∑ n ∈ Ico 61184 61440, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (19572147748748064903128209271 : ℤ) := by
  rcases cdemPrefixStats_61184_61312 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_61312_61440 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 61184 ≤ 61312) (by norm_num : 61312 ≤ 61440), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 61184 ≤ 61312) (by norm_num : 61312 ≤ 61440), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 61184 ≤ 61312) (by norm_num : 61312 ≤ 61440), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 61184 ≤ 61312) (by norm_num : 61312 ≤ 61440), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_60928_61440 :
    (∑ n ∈ Ico 60928 61440, mobiusTreeValue 16 mobiusTable1200001 n) = (23 : ℤ) ∧
    (∑ n ∈ Ico 60928 61440, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (313 : ℕ) ∧
    (∑ n ∈ Ico 60928 61440, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (1877955 : ℤ) ∧
    (∑ n ∈ Ico 60928 61440, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (37559050556491315829115424142 : ℤ) := by
  rcases cdemPrefixStats_60928_61184 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_61184_61440 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 60928 ≤ 61184) (by norm_num : 61184 ≤ 61440), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 60928 ≤ 61184) (by norm_num : 61184 ≤ 61440), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 60928 ≤ 61184) (by norm_num : 61184 ≤ 61440), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 60928 ≤ 61184) (by norm_num : 61184 ≤ 61440), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_60416_61440 :
    (∑ n ∈ Ico 60416 61440, mobiusTreeValue 16 mobiusTable1200001 n) = (20 : ℤ) ∧
    (∑ n ∈ Ico 60416 61440, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (626 : ℕ) ∧
    (∑ n ∈ Ico 60416 61440, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (1638515 : ℤ) ∧
    (∑ n ∈ Ico 60416 61440, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (32770199704196612402901779308 : ℤ) := by
  rcases cdemPrefixStats_60416_60928 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_60928_61440 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 60416 ≤ 60928) (by norm_num : 60928 ≤ 61440), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 60416 ≤ 60928) (by norm_num : 60928 ≤ 61440), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 60416 ≤ 60928) (by norm_num : 60928 ≤ 61440), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 60416 ≤ 60928) (by norm_num : 60928 ≤ 61440), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_59392_61440 :
    (∑ n ∈ Ico 59392 61440, mobiusTreeValue 16 mobiusTable1200001 n) = (37 : ℤ) ∧
    (∑ n ∈ Ico 59392 61440, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (1249 : ℕ) ∧
    (∑ n ∈ Ico 59392 61440, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (3040211 : ℤ) ∧
    (∑ n ∈ Ico 59392 61440, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (60804379892517304783008225657 : ℤ) := by
  rcases cdemPrefixStats_59392_60416 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_60416_61440 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 59392 ≤ 60416) (by norm_num : 60416 ≤ 61440), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 59392 ≤ 60416) (by norm_num : 60416 ≤ 61440), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 59392 ≤ 60416) (by norm_num : 60416 ≤ 61440), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 59392 ≤ 60416) (by norm_num : 60416 ≤ 61440), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_57344_61440 :
    (∑ n ∈ Ico 57344 61440, mobiusTreeValue 16 mobiusTable1200001 n) = (8 : ℤ) ∧
    (∑ n ∈ Ico 57344 61440, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (2494 : ℕ) ∧
    (∑ n ∈ Ico 57344 61440, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (582150 : ℤ) ∧
    (∑ n ∈ Ico 57344 61440, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (11642752312647241467225188167 : ℤ) := by
  rcases cdemPrefixStats_57344_59392 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_59392_61440 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 57344 ≤ 59392) (by norm_num : 59392 ≤ 61440), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 57344 ≤ 59392) (by norm_num : 59392 ≤ 61440), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 57344 ≤ 59392) (by norm_num : 59392 ≤ 61440), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 57344 ≤ 59392) (by norm_num : 59392 ≤ 61440), hR1, hR2] <;> norm_num

theorem cdemPrefixGroup014_checked_complete :
    (∑ n ∈ Ico 57344 61440, mobiusTreeValue 16 mobiusTable1200001 n) = (8 : ℤ) ∧
    (∑ n ∈ Ico 57344 61440, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (2494 : ℕ) ∧
    (∑ n ∈ Ico 57344 61440, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (582150 : ℤ) ∧
    (∑ n ∈ Ico 57344 61440, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (11642752312647241467225188167 : ℤ) := cdemPrefixStats_57344_61440
end Helfgott
#print axioms Helfgott.cdemPrefixGroup014_checked_complete

open Helfgott Finset
open scoped BigOperators

theorem solution :
    (∑ n ∈ Ico 57344 61440, mobiusTreeValue 16 mobiusTable1200001 n) = (8 : ℤ) ∧
    (∑ n ∈ Ico 57344 61440, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (2494 : ℕ) ∧
    (∑ n ∈ Ico 57344 61440, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (582150 : ℤ) ∧
    (∑ n ∈ Ico 57344 61440, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (11642752312647241467225188167 : ℤ) := Helfgott.cdemPrefixGroup014_checked_complete
#print axioms solution
