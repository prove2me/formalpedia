-- Prove2me | solution 1 for Helfgott.cdemPrefixGroup024_checked
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-09T02:01:53.039227+00:00
-- url     : https://prove2.me/submissions/e83a6ec2-983a-41ea-907e-0d086cea08b9

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
private theorem cdemPrefixStats_98304_98368 :
    (∑ n ∈ Ico 98304 98368, mobiusTreeValue 16 mobiusTable1200001 n) = (10 : ℤ) ∧
    (∑ n ∈ Ico 98304 98368, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 98304 98368, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (508429 : ℤ) ∧
    (∑ n ∈ Ico 98304 98368, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (10168626757480368871081333458 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_98368_98432 :
    (∑ n ∈ Ico 98368 98432, mobiusTreeValue 16 mobiusTable1200001 n) = (3 : ℤ) ∧
    (∑ n ∈ Ico 98368 98432, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 98368 98432, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (152457 : ℤ) ∧
    (∑ n ∈ Ico 98368 98432, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (3049234686802270031022396620 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_98304_98432 :
    (∑ n ∈ Ico 98304 98432, mobiusTreeValue 16 mobiusTable1200001 n) = (13 : ℤ) ∧
    (∑ n ∈ Ico 98304 98432, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (79 : ℕ) ∧
    (∑ n ∈ Ico 98304 98432, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (660886 : ℤ) ∧
    (∑ n ∈ Ico 98304 98432, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (13217861444282638902103730078 : ℤ) := by
  rcases cdemPrefixStats_98304_98368 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_98368_98432 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 98304 ≤ 98368) (by norm_num : 98368 ≤ 98432), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 98304 ≤ 98368) (by norm_num : 98368 ≤ 98432), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 98304 ≤ 98368) (by norm_num : 98368 ≤ 98432), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 98304 ≤ 98368) (by norm_num : 98368 ≤ 98432), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_98432_98496 :
    (∑ n ∈ Ico 98432 98496, mobiusTreeValue 16 mobiusTable1200001 n) = (-3 : ℤ) ∧
    (∑ n ∈ Ico 98432 98496, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 98432 98496, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-152274 : ℤ) ∧
    (∑ n ∈ Ico 98432 98496, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-3045498940618517938992148042 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_98496_98560 :
    (∑ n ∈ Ico 98496 98560, mobiusTreeValue 16 mobiusTable1200001 n) = (5 : ℤ) ∧
    (∑ n ∈ Ico 98496 98560, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 98496 98560, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (253743 : ℤ) ∧
    (∑ n ∈ Ico 98496 98560, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (5074936817320203217233799767 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_98432_98560 :
    (∑ n ∈ Ico 98432 98560, mobiusTreeValue 16 mobiusTable1200001 n) = (2 : ℤ) ∧
    (∑ n ∈ Ico 98432 98560, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (74 : ℕ) ∧
    (∑ n ∈ Ico 98432 98560, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (101469 : ℤ) ∧
    (∑ n ∈ Ico 98432 98560, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (2029437876701685278241651725 : ℤ) := by
  rcases cdemPrefixStats_98432_98496 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_98496_98560 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 98432 ≤ 98496) (by norm_num : 98496 ≤ 98560), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 98432 ≤ 98496) (by norm_num : 98496 ≤ 98560), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 98432 ≤ 98496) (by norm_num : 98496 ≤ 98560), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 98432 ≤ 98496) (by norm_num : 98496 ≤ 98560), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_98304_98560 :
    (∑ n ∈ Ico 98304 98560, mobiusTreeValue 16 mobiusTable1200001 n) = (15 : ℤ) ∧
    (∑ n ∈ Ico 98304 98560, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (153 : ℕ) ∧
    (∑ n ∈ Ico 98304 98560, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (762355 : ℤ) ∧
    (∑ n ∈ Ico 98304 98560, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (15247299320984324180345381803 : ℤ) := by
  rcases cdemPrefixStats_98304_98432 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_98432_98560 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 98304 ≤ 98432) (by norm_num : 98432 ≤ 98560), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 98304 ≤ 98432) (by norm_num : 98432 ≤ 98560), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 98304 ≤ 98432) (by norm_num : 98432 ≤ 98560), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 98304 ≤ 98432) (by norm_num : 98432 ≤ 98560), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_98560_98624 :
    (∑ n ∈ Ico 98560 98624, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 98560 98624, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 98560 98624, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-50715 : ℤ) ∧
    (∑ n ∈ Ico 98560 98624, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-1014312289802507488504952519 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_98624_98688 :
    (∑ n ∈ Ico 98624 98688, mobiusTreeValue 16 mobiusTable1200001 n) = (2 : ℤ) ∧
    (∑ n ∈ Ico 98624 98688, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 98624 98688, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (101315 : ℤ) ∧
    (∑ n ∈ Ico 98624 98688, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (2026311198627490491632115759 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_98560_98688 :
    (∑ n ∈ Ico 98560 98688, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 98560 98688, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (79 : ℕ) ∧
    (∑ n ∈ Ico 98560 98688, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (50600 : ℤ) ∧
    (∑ n ∈ Ico 98560 98688, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1011998908824983003127163240 : ℤ) := by
  rcases cdemPrefixStats_98560_98624 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_98624_98688 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 98560 ≤ 98624) (by norm_num : 98624 ≤ 98688), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 98560 ≤ 98624) (by norm_num : 98624 ≤ 98688), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 98560 ≤ 98624) (by norm_num : 98624 ≤ 98688), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 98560 ≤ 98624) (by norm_num : 98624 ≤ 98688), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_98688_98752 :
    (∑ n ∈ Ico 98688 98752, mobiusTreeValue 16 mobiusTable1200001 n) = (-4 : ℤ) ∧
    (∑ n ∈ Ico 98688 98752, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 98688 98752, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-202719 : ℤ) ∧
    (∑ n ∈ Ico 98688 98752, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-4054500905413571204191283626 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_98752_98816 :
    (∑ n ∈ Ico 98752 98816, mobiusTreeValue 16 mobiusTable1200001 n) = (5 : ℤ) ∧
    (∑ n ∈ Ico 98752 98816, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 98752 98816, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (253099 : ℤ) ∧
    (∑ n ∈ Ico 98752 98816, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (5062081563523529297057444538 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_98688_98816 :
    (∑ n ∈ Ico 98688 98816, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 98688 98816, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (81 : ℕ) ∧
    (∑ n ∈ Ico 98688 98816, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (50380 : ℤ) ∧
    (∑ n ∈ Ico 98688 98816, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1007580658109958092866160912 : ℤ) := by
  rcases cdemPrefixStats_98688_98752 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_98752_98816 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 98688 ≤ 98752) (by norm_num : 98752 ≤ 98816), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 98688 ≤ 98752) (by norm_num : 98752 ≤ 98816), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 98688 ≤ 98752) (by norm_num : 98752 ≤ 98816), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 98688 ≤ 98752) (by norm_num : 98752 ≤ 98816), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_98560_98816 :
    (∑ n ∈ Ico 98560 98816, mobiusTreeValue 16 mobiusTable1200001 n) = (2 : ℤ) ∧
    (∑ n ∈ Ico 98560 98816, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (160 : ℕ) ∧
    (∑ n ∈ Ico 98560 98816, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (100980 : ℤ) ∧
    (∑ n ∈ Ico 98560 98816, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (2019579566934941095993324152 : ℤ) := by
  rcases cdemPrefixStats_98560_98688 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_98688_98816 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 98560 ≤ 98688) (by norm_num : 98688 ≤ 98816), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 98560 ≤ 98688) (by norm_num : 98688 ≤ 98816), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 98560 ≤ 98688) (by norm_num : 98688 ≤ 98816), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 98560 ≤ 98688) (by norm_num : 98688 ≤ 98816), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_98304_98816 :
    (∑ n ∈ Ico 98304 98816, mobiusTreeValue 16 mobiusTable1200001 n) = (17 : ℤ) ∧
    (∑ n ∈ Ico 98304 98816, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (313 : ℕ) ∧
    (∑ n ∈ Ico 98304 98816, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (863335 : ℤ) ∧
    (∑ n ∈ Ico 98304 98816, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (17266878887919265276338705955 : ℤ) := by
  rcases cdemPrefixStats_98304_98560 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_98560_98816 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 98304 ≤ 98560) (by norm_num : 98560 ≤ 98816), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 98304 ≤ 98560) (by norm_num : 98560 ≤ 98816), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 98304 ≤ 98560) (by norm_num : 98560 ≤ 98816), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 98304 ≤ 98560) (by norm_num : 98560 ≤ 98816), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_98816_98880 :
    (∑ n ∈ Ico 98816 98880, mobiusTreeValue 16 mobiusTable1200001 n) = (-4 : ℤ) ∧
    (∑ n ∈ Ico 98816 98880, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 98816 98880, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-202187 : ℤ) ∧
    (∑ n ∈ Ico 98816 98880, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-4043823100195511348220918745 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_98880_98944 :
    (∑ n ∈ Ico 98880 98944, mobiusTreeValue 16 mobiusTable1200001 n) = (-4 : ℤ) ∧
    (∑ n ∈ Ico 98880 98944, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 98880 98944, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-202211 : ℤ) ∧
    (∑ n ∈ Ico 98880 98944, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-4044213290945980974307199752 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_98816_98944 :
    (∑ n ∈ Ico 98816 98944, mobiusTreeValue 16 mobiusTable1200001 n) = (-8 : ℤ) ∧
    (∑ n ∈ Ico 98816 98944, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (76 : ℕ) ∧
    (∑ n ∈ Ico 98816 98944, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-404398 : ℤ) ∧
    (∑ n ∈ Ico 98816 98944, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-8088036391141492322528118497 : ℤ) := by
  rcases cdemPrefixStats_98816_98880 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_98880_98944 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 98816 ≤ 98880) (by norm_num : 98880 ≤ 98944), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 98816 ≤ 98880) (by norm_num : 98880 ≤ 98944), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 98816 ≤ 98880) (by norm_num : 98880 ≤ 98944), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 98816 ≤ 98880) (by norm_num : 98880 ≤ 98944), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_98944_99008 :
    (∑ n ∈ Ico 98944 99008, mobiusTreeValue 16 mobiusTable1200001 n) = (5 : ℤ) ∧
    (∑ n ∈ Ico 98944 99008, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 98944 99008, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (252580 : ℤ) ∧
    (∑ n ∈ Ico 98944 99008, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (5051638193565897922383003745 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_99008_99072 :
    (∑ n ∈ Ico 99008 99072, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 99008 99072, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 99008 99072, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-99 : ℤ) ∧
    (∑ n ∈ Ico 99008 99072, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-1916666289627166255231004 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_98944_99072 :
    (∑ n ∈ Ico 98944 99072, mobiusTreeValue 16 mobiusTable1200001 n) = (5 : ℤ) ∧
    (∑ n ∈ Ico 98944 99072, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 98944 99072, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (252481 : ℤ) ∧
    (∑ n ∈ Ico 98944 99072, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (5049721527276270756127772741 : ℤ) := by
  rcases cdemPrefixStats_98944_99008 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_99008_99072 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 98944 ≤ 99008) (by norm_num : 99008 ≤ 99072), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 98944 ≤ 99008) (by norm_num : 99008 ≤ 99072), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 98944 ≤ 99008) (by norm_num : 99008 ≤ 99072), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 98944 ≤ 99008) (by norm_num : 99008 ≤ 99072), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_98816_99072 :
    (∑ n ∈ Ico 98816 99072, mobiusTreeValue 16 mobiusTable1200001 n) = (-3 : ℤ) ∧
    (∑ n ∈ Ico 98816 99072, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (153 : ℕ) ∧
    (∑ n ∈ Ico 98816 99072, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-151917 : ℤ) ∧
    (∑ n ∈ Ico 98816 99072, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-3038314863865221566400345756 : ℤ) := by
  rcases cdemPrefixStats_98816_98944 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_98944_99072 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 98816 ≤ 98944) (by norm_num : 98944 ≤ 99072), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 98816 ≤ 98944) (by norm_num : 98944 ≤ 99072), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 98816 ≤ 98944) (by norm_num : 98944 ≤ 99072), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 98816 ≤ 98944) (by norm_num : 98944 ≤ 99072), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_99072_99136 :
    (∑ n ∈ Ico 99072 99136, mobiusTreeValue 16 mobiusTable1200001 n) = (4 : ℤ) ∧
    (∑ n ∈ Ico 99072 99136, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 99072 99136, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (201882 : ℤ) ∧
    (∑ n ∈ Ico 99072 99136, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (4037681285791024717596930173 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_99136_99200 :
    (∑ n ∈ Ico 99136 99200, mobiusTreeValue 16 mobiusTable1200001 n) = (-16 : ℤ) ∧
    (∑ n ∈ Ico 99136 99200, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 99136 99200, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-806741 : ℤ) ∧
    (∑ n ∈ Ico 99136 99200, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-16135040872264527414930583852 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_99072_99200 :
    (∑ n ∈ Ico 99072 99200, mobiusTreeValue 16 mobiusTable1200001 n) = (-12 : ℤ) ∧
    (∑ n ∈ Ico 99072 99200, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 99072 99200, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-604859 : ℤ) ∧
    (∑ n ∈ Ico 99072 99200, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-12097359586473502697333653679 : ℤ) := by
  rcases cdemPrefixStats_99072_99136 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_99136_99200 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 99072 ≤ 99136) (by norm_num : 99136 ≤ 99200), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 99072 ≤ 99136) (by norm_num : 99136 ≤ 99200), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 99072 ≤ 99136) (by norm_num : 99136 ≤ 99200), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 99072 ≤ 99136) (by norm_num : 99136 ≤ 99200), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_99200_99264 :
    (∑ n ∈ Ico 99200 99264, mobiusTreeValue 16 mobiusTable1200001 n) = (4 : ℤ) ∧
    (∑ n ∈ Ico 99200 99264, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 99200 99264, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (201601 : ℤ) ∧
    (∑ n ∈ Ico 99200 99264, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (4032044466083885508523353197 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_99264_99328 :
    (∑ n ∈ Ico 99264 99328, mobiusTreeValue 16 mobiusTable1200001 n) = (3 : ℤ) ∧
    (∑ n ∈ Ico 99264 99328, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 99264 99328, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (151107 : ℤ) ∧
    (∑ n ∈ Ico 99264 99328, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (3022203263243532804923833897 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_99200_99328 :
    (∑ n ∈ Ico 99200 99328, mobiusTreeValue 16 mobiusTable1200001 n) = (7 : ℤ) ∧
    (∑ n ∈ Ico 99200 99328, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (79 : ℕ) ∧
    (∑ n ∈ Ico 99200 99328, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (352708 : ℤ) ∧
    (∑ n ∈ Ico 99200 99328, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (7054247729327418313447187094 : ℤ) := by
  rcases cdemPrefixStats_99200_99264 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_99264_99328 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 99200 ≤ 99264) (by norm_num : 99264 ≤ 99328), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 99200 ≤ 99264) (by norm_num : 99264 ≤ 99328), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 99200 ≤ 99264) (by norm_num : 99264 ≤ 99328), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 99200 ≤ 99264) (by norm_num : 99264 ≤ 99328), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_99072_99328 :
    (∑ n ∈ Ico 99072 99328, mobiusTreeValue 16 mobiusTable1200001 n) = (-5 : ℤ) ∧
    (∑ n ∈ Ico 99072 99328, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (157 : ℕ) ∧
    (∑ n ∈ Ico 99072 99328, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-252151 : ℤ) ∧
    (∑ n ∈ Ico 99072 99328, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-5043111857146084383886466585 : ℤ) := by
  rcases cdemPrefixStats_99072_99200 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_99200_99328 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 99072 ≤ 99200) (by norm_num : 99200 ≤ 99328), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 99072 ≤ 99200) (by norm_num : 99200 ≤ 99328), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 99072 ≤ 99200) (by norm_num : 99200 ≤ 99328), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 99072 ≤ 99200) (by norm_num : 99200 ≤ 99328), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_98816_99328 :
    (∑ n ∈ Ico 98816 99328, mobiusTreeValue 16 mobiusTable1200001 n) = (-8 : ℤ) ∧
    (∑ n ∈ Ico 98816 99328, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (310 : ℕ) ∧
    (∑ n ∈ Ico 98816 99328, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-404068 : ℤ) ∧
    (∑ n ∈ Ico 98816 99328, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-8081426721011305950286812341 : ℤ) := by
  rcases cdemPrefixStats_98816_99072 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_99072_99328 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 98816 ≤ 99072) (by norm_num : 99072 ≤ 99328), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 98816 ≤ 99072) (by norm_num : 99072 ≤ 99328), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 98816 ≤ 99072) (by norm_num : 99072 ≤ 99328), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 98816 ≤ 99072) (by norm_num : 99072 ≤ 99328), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_98304_99328 :
    (∑ n ∈ Ico 98304 99328, mobiusTreeValue 16 mobiusTable1200001 n) = (9 : ℤ) ∧
    (∑ n ∈ Ico 98304 99328, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (623 : ℕ) ∧
    (∑ n ∈ Ico 98304 99328, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (459267 : ℤ) ∧
    (∑ n ∈ Ico 98304 99328, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (9185452166907959326051893614 : ℤ) := by
  rcases cdemPrefixStats_98304_98816 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_98816_99328 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 98304 ≤ 98816) (by norm_num : 98816 ≤ 99328), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 98304 ≤ 98816) (by norm_num : 98816 ≤ 99328), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 98304 ≤ 98816) (by norm_num : 98816 ≤ 99328), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 98304 ≤ 98816) (by norm_num : 98816 ≤ 99328), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_99328_99392 :
    (∑ n ∈ Ico 99328 99392, mobiusTreeValue 16 mobiusTable1200001 n) = (11 : ℤ) ∧
    (∑ n ∈ Ico 99328 99392, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 99328 99392, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (553597 : ℤ) ∧
    (∑ n ∈ Ico 99328 99392, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (11072069588342303880814172492 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_99392_99456 :
    (∑ n ∈ Ico 99392 99456, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 99392 99456, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 99392 99456, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-50479 : ℤ) ∧
    (∑ n ∈ Ico 99392 99456, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-1009647670777361445233317139 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_99328_99456 :
    (∑ n ∈ Ico 99328 99456, mobiusTreeValue 16 mobiusTable1200001 n) = (10 : ℤ) ∧
    (∑ n ∈ Ico 99328 99456, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (80 : ℕ) ∧
    (∑ n ∈ Ico 99328 99456, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (503118 : ℤ) ∧
    (∑ n ∈ Ico 99328 99456, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (10062421917564942435580855353 : ℤ) := by
  rcases cdemPrefixStats_99328_99392 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_99392_99456 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 99328 ≤ 99392) (by norm_num : 99392 ≤ 99456), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 99328 ≤ 99392) (by norm_num : 99392 ≤ 99456), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 99328 ≤ 99392) (by norm_num : 99392 ≤ 99456), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 99328 ≤ 99392) (by norm_num : 99392 ≤ 99456), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_99456_99520 :
    (∑ n ∈ Ico 99456 99520, mobiusTreeValue 16 mobiusTable1200001 n) = (-2 : ℤ) ∧
    (∑ n ∈ Ico 99456 99520, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 99456 99520, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-100422 : ℤ) ∧
    (∑ n ∈ Ico 99456 99520, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-2008453986858673963354467093 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_99520_99584 :
    (∑ n ∈ Ico 99520 99584, mobiusTreeValue 16 mobiusTable1200001 n) = (2 : ℤ) ∧
    (∑ n ∈ Ico 99520 99584, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 99520 99584, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (100397 : ℤ) ∧
    (∑ n ∈ Ico 99520 99584, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (2008001329504428136801850380 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_99456_99584 :
    (∑ n ∈ Ico 99456 99584, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 99456 99584, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (76 : ℕ) ∧
    (∑ n ∈ Ico 99456 99584, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-25 : ℤ) ∧
    (∑ n ∈ Ico 99456 99584, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-452657354245826552616713 : ℤ) := by
  rcases cdemPrefixStats_99456_99520 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_99520_99584 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 99456 ≤ 99520) (by norm_num : 99520 ≤ 99584), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 99456 ≤ 99520) (by norm_num : 99520 ≤ 99584), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 99456 ≤ 99520) (by norm_num : 99520 ≤ 99584), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 99456 ≤ 99520) (by norm_num : 99520 ≤ 99584), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_99328_99584 :
    (∑ n ∈ Ico 99328 99584, mobiusTreeValue 16 mobiusTable1200001 n) = (10 : ℤ) ∧
    (∑ n ∈ Ico 99328 99584, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (156 : ℕ) ∧
    (∑ n ∈ Ico 99328 99584, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (503093 : ℤ) ∧
    (∑ n ∈ Ico 99328 99584, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (10061969260210696609028238640 : ℤ) := by
  rcases cdemPrefixStats_99328_99456 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_99456_99584 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 99328 ≤ 99456) (by norm_num : 99456 ≤ 99584), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 99328 ≤ 99456) (by norm_num : 99456 ≤ 99584), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 99328 ≤ 99456) (by norm_num : 99456 ≤ 99584), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 99328 ≤ 99456) (by norm_num : 99456 ≤ 99584), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_99584_99648 :
    (∑ n ∈ Ico 99584 99648, mobiusTreeValue 16 mobiusTable1200001 n) = (4 : ℤ) ∧
    (∑ n ∈ Ico 99584 99648, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 99584 99648, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (200788 : ℤ) ∧
    (∑ n ∈ Ico 99584 99648, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (4015822589285467449427253725 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_99648_99712 :
    (∑ n ∈ Ico 99648 99712, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 99648 99712, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 99648 99712, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (50135 : ℤ) ∧
    (∑ n ∈ Ico 99648 99712, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1002757265618352731858388002 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_99584_99712 :
    (∑ n ∈ Ico 99584 99712, mobiusTreeValue 16 mobiusTable1200001 n) = (5 : ℤ) ∧
    (∑ n ∈ Ico 99584 99712, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (79 : ℕ) ∧
    (∑ n ∈ Ico 99584 99712, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (250923 : ℤ) ∧
    (∑ n ∈ Ico 99584 99712, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (5018579854903820181285641727 : ℤ) := by
  rcases cdemPrefixStats_99584_99648 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_99648_99712 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 99584 ≤ 99648) (by norm_num : 99648 ≤ 99712), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 99584 ≤ 99648) (by norm_num : 99648 ≤ 99712), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 99584 ≤ 99648) (by norm_num : 99648 ≤ 99712), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 99584 ≤ 99648) (by norm_num : 99648 ≤ 99712), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_99712_99776 :
    (∑ n ∈ Ico 99712 99776, mobiusTreeValue 16 mobiusTable1200001 n) = (-3 : ℤ) ∧
    (∑ n ∈ Ico 99712 99776, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 99712 99776, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-150438 : ℤ) ∧
    (∑ n ∈ Ico 99712 99776, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-3008805860662152350983520479 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_99776_99840 :
    (∑ n ∈ Ico 99776 99840, mobiusTreeValue 16 mobiusTable1200001 n) = (-7 : ℤ) ∧
    (∑ n ∈ Ico 99776 99840, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 99776 99840, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-350699 : ℤ) ∧
    (∑ n ∈ Ico 99776 99840, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-7014088590946422712543483176 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_99712_99840 :
    (∑ n ∈ Ico 99712 99840, mobiusTreeValue 16 mobiusTable1200001 n) = (-10 : ℤ) ∧
    (∑ n ∈ Ico 99712 99840, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (80 : ℕ) ∧
    (∑ n ∈ Ico 99712 99840, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-501137 : ℤ) ∧
    (∑ n ∈ Ico 99712 99840, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-10022894451608575063527003655 : ℤ) := by
  rcases cdemPrefixStats_99712_99776 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_99776_99840 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 99712 ≤ 99776) (by norm_num : 99776 ≤ 99840), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 99712 ≤ 99776) (by norm_num : 99776 ≤ 99840), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 99712 ≤ 99776) (by norm_num : 99776 ≤ 99840), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 99712 ≤ 99776) (by norm_num : 99776 ≤ 99840), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_99584_99840 :
    (∑ n ∈ Ico 99584 99840, mobiusTreeValue 16 mobiusTable1200001 n) = (-5 : ℤ) ∧
    (∑ n ∈ Ico 99584 99840, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (159 : ℕ) ∧
    (∑ n ∈ Ico 99584 99840, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-250214 : ℤ) ∧
    (∑ n ∈ Ico 99584 99840, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-5004314596704754882241361928 : ℤ) := by
  rcases cdemPrefixStats_99584_99712 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_99712_99840 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 99584 ≤ 99712) (by norm_num : 99712 ≤ 99840), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 99584 ≤ 99712) (by norm_num : 99712 ≤ 99840), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 99584 ≤ 99712) (by norm_num : 99712 ≤ 99840), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 99584 ≤ 99712) (by norm_num : 99712 ≤ 99840), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_99328_99840 :
    (∑ n ∈ Ico 99328 99840, mobiusTreeValue 16 mobiusTable1200001 n) = (5 : ℤ) ∧
    (∑ n ∈ Ico 99328 99840, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (315 : ℕ) ∧
    (∑ n ∈ Ico 99328 99840, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (252879 : ℤ) ∧
    (∑ n ∈ Ico 99328 99840, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (5057654663505941726786876712 : ℤ) := by
  rcases cdemPrefixStats_99328_99584 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_99584_99840 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 99328 ≤ 99584) (by norm_num : 99584 ≤ 99840), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 99328 ≤ 99584) (by norm_num : 99584 ≤ 99840), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 99328 ≤ 99584) (by norm_num : 99584 ≤ 99840), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 99328 ≤ 99584) (by norm_num : 99584 ≤ 99840), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_99840_99904 :
    (∑ n ∈ Ico 99840 99904, mobiusTreeValue 16 mobiusTable1200001 n) = (5 : ℤ) ∧
    (∑ n ∈ Ico 99840 99904, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 99840 99904, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (250269 : ℤ) ∧
    (∑ n ∈ Ico 99840 99904, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (5005375639916482772648029193 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_99904_99968 :
    (∑ n ∈ Ico 99904 99968, mobiusTreeValue 16 mobiusTable1200001 n) = (3 : ℤ) ∧
    (∑ n ∈ Ico 99904 99968, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 99904 99968, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (150032 : ℤ) ∧
    (∑ n ∈ Ico 99904 99968, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (3000709784954072079985960060 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_99840_99968 :
    (∑ n ∈ Ico 99840 99968, mobiusTreeValue 16 mobiusTable1200001 n) = (8 : ℤ) ∧
    (∑ n ∈ Ico 99840 99968, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (76 : ℕ) ∧
    (∑ n ∈ Ico 99840 99968, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (400301 : ℤ) ∧
    (∑ n ∈ Ico 99840 99968, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (8006085424870554852633989253 : ℤ) := by
  rcases cdemPrefixStats_99840_99904 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_99904_99968 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 99840 ≤ 99904) (by norm_num : 99904 ≤ 99968), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 99840 ≤ 99904) (by norm_num : 99904 ≤ 99968), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 99840 ≤ 99904) (by norm_num : 99904 ≤ 99968), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 99840 ≤ 99904) (by norm_num : 99904 ≤ 99968), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_99968_100032 :
    (∑ n ∈ Ico 99968 100032, mobiusTreeValue 16 mobiusTable1200001 n) = (14 : ℤ) ∧
    (∑ n ∈ Ico 99968 100032, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 99968 100032, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (699980 : ℤ) ∧
    (∑ n ∈ Ico 99968 100032, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (13999670573037814928358269212 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_100032_100096 :
    (∑ n ∈ Ico 100032 100096, mobiusTreeValue 16 mobiusTable1200001 n) = (2 : ℤ) ∧
    (∑ n ∈ Ico 100032 100096, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 100032 100096, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (99973 : ℤ) ∧
    (∑ n ∈ Ico 100032 100096, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1999489832355120790327676782 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_99968_100096 :
    (∑ n ∈ Ico 99968 100096, mobiusTreeValue 16 mobiusTable1200001 n) = (16 : ℤ) ∧
    (∑ n ∈ Ico 99968 100096, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (76 : ℕ) ∧
    (∑ n ∈ Ico 99968 100096, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (799953 : ℤ) ∧
    (∑ n ∈ Ico 99968 100096, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (15999160405392935718685945994 : ℤ) := by
  rcases cdemPrefixStats_99968_100032 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_100032_100096 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 99968 ≤ 100032) (by norm_num : 100032 ≤ 100096), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 99968 ≤ 100032) (by norm_num : 100032 ≤ 100096), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 99968 ≤ 100032) (by norm_num : 100032 ≤ 100096), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 99968 ≤ 100032) (by norm_num : 100032 ≤ 100096), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_99840_100096 :
    (∑ n ∈ Ico 99840 100096, mobiusTreeValue 16 mobiusTable1200001 n) = (24 : ℤ) ∧
    (∑ n ∈ Ico 99840 100096, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (152 : ℕ) ∧
    (∑ n ∈ Ico 99840 100096, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (1200254 : ℤ) ∧
    (∑ n ∈ Ico 99840 100096, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (24005245830263490571319935247 : ℤ) := by
  rcases cdemPrefixStats_99840_99968 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_99968_100096 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 99840 ≤ 99968) (by norm_num : 99968 ≤ 100096), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 99840 ≤ 99968) (by norm_num : 99968 ≤ 100096), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 99840 ≤ 99968) (by norm_num : 99968 ≤ 100096), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 99840 ≤ 99968) (by norm_num : 99968 ≤ 100096), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_100096_100160 :
    (∑ n ∈ Ico 100096 100160, mobiusTreeValue 16 mobiusTable1200001 n) = (4 : ℤ) ∧
    (∑ n ∈ Ico 100096 100160, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (42 : ℕ) ∧
    (∑ n ∈ Ico 100096 100160, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (199722 : ℤ) ∧
    (∑ n ∈ Ico 100096 100160, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (3994517791350144200651218020 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_100160_100224 :
    (∑ n ∈ Ico 100160 100224, mobiusTreeValue 16 mobiusTable1200001 n) = (-3 : ℤ) ∧
    (∑ n ∈ Ico 100160 100224, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 100160 100224, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-149688 : ℤ) ∧
    (∑ n ∈ Ico 100160 100224, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-2993842929088722414813572587 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_100096_100224 :
    (∑ n ∈ Ico 100096 100224, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 100096 100224, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (81 : ℕ) ∧
    (∑ n ∈ Ico 100096 100224, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (50034 : ℤ) ∧
    (∑ n ∈ Ico 100096 100224, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1000674862261421785837645433 : ℤ) := by
  rcases cdemPrefixStats_100096_100160 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_100160_100224 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 100096 ≤ 100160) (by norm_num : 100160 ≤ 100224), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 100096 ≤ 100160) (by norm_num : 100160 ≤ 100224), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 100096 ≤ 100160) (by norm_num : 100160 ≤ 100224), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 100096 ≤ 100160) (by norm_num : 100160 ≤ 100224), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_100224_100288 :
    (∑ n ∈ Ico 100224 100288, mobiusTreeValue 16 mobiusTable1200001 n) = (7 : ℤ) ∧
    (∑ n ∈ Ico 100224 100288, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 100224 100288, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (349175 : ℤ) ∧
    (∑ n ∈ Ico 100224 100288, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (6983608081428196196234807749 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_100288_100352 :
    (∑ n ∈ Ico 100288 100352, mobiusTreeValue 16 mobiusTable1200001 n) = (10 : ℤ) ∧
    (∑ n ∈ Ico 100288 100352, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 100288 100352, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (498389 : ℤ) ∧
    (∑ n ∈ Ico 100288 100352, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (9967804294953894293880662219 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_100224_100352 :
    (∑ n ∈ Ico 100224 100352, mobiusTreeValue 16 mobiusTable1200001 n) = (17 : ℤ) ∧
    (∑ n ∈ Ico 100224 100352, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 100224 100352, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (847564 : ℤ) ∧
    (∑ n ∈ Ico 100224 100352, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (16951412376382090490115469968 : ℤ) := by
  rcases cdemPrefixStats_100224_100288 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_100288_100352 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 100224 ≤ 100288) (by norm_num : 100288 ≤ 100352), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 100224 ≤ 100288) (by norm_num : 100288 ≤ 100352), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 100224 ≤ 100288) (by norm_num : 100288 ≤ 100352), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 100224 ≤ 100288) (by norm_num : 100288 ≤ 100352), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_100096_100352 :
    (∑ n ∈ Ico 100096 100352, mobiusTreeValue 16 mobiusTable1200001 n) = (18 : ℤ) ∧
    (∑ n ∈ Ico 100096 100352, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (158 : ℕ) ∧
    (∑ n ∈ Ico 100096 100352, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (897598 : ℤ) ∧
    (∑ n ∈ Ico 100096 100352, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (17952087238643512275953115401 : ℤ) := by
  rcases cdemPrefixStats_100096_100224 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_100224_100352 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 100096 ≤ 100224) (by norm_num : 100224 ≤ 100352), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 100096 ≤ 100224) (by norm_num : 100224 ≤ 100352), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 100096 ≤ 100224) (by norm_num : 100224 ≤ 100352), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 100096 ≤ 100224) (by norm_num : 100224 ≤ 100352), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_99840_100352 :
    (∑ n ∈ Ico 99840 100352, mobiusTreeValue 16 mobiusTable1200001 n) = (42 : ℤ) ∧
    (∑ n ∈ Ico 99840 100352, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (310 : ℕ) ∧
    (∑ n ∈ Ico 99840 100352, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (2097852 : ℤ) ∧
    (∑ n ∈ Ico 99840 100352, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (41957333068907002847273050648 : ℤ) := by
  rcases cdemPrefixStats_99840_100096 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_100096_100352 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 99840 ≤ 100096) (by norm_num : 100096 ≤ 100352), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 99840 ≤ 100096) (by norm_num : 100096 ≤ 100352), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 99840 ≤ 100096) (by norm_num : 100096 ≤ 100352), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 99840 ≤ 100096) (by norm_num : 100096 ≤ 100352), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_99328_100352 :
    (∑ n ∈ Ico 99328 100352, mobiusTreeValue 16 mobiusTable1200001 n) = (47 : ℤ) ∧
    (∑ n ∈ Ico 99328 100352, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (625 : ℕ) ∧
    (∑ n ∈ Ico 99328 100352, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (2350731 : ℤ) ∧
    (∑ n ∈ Ico 99328 100352, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (47014987732412944574059927360 : ℤ) := by
  rcases cdemPrefixStats_99328_99840 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_99840_100352 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 99328 ≤ 99840) (by norm_num : 99840 ≤ 100352), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 99328 ≤ 99840) (by norm_num : 99840 ≤ 100352), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 99328 ≤ 99840) (by norm_num : 99840 ≤ 100352), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 99328 ≤ 99840) (by norm_num : 99840 ≤ 100352), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_98304_100352 :
    (∑ n ∈ Ico 98304 100352, mobiusTreeValue 16 mobiusTable1200001 n) = (56 : ℤ) ∧
    (∑ n ∈ Ico 98304 100352, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (1248 : ℕ) ∧
    (∑ n ∈ Ico 98304 100352, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (2809998 : ℤ) ∧
    (∑ n ∈ Ico 98304 100352, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (56200439899320903900111820974 : ℤ) := by
  rcases cdemPrefixStats_98304_99328 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_99328_100352 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 98304 ≤ 99328) (by norm_num : 99328 ≤ 100352), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 98304 ≤ 99328) (by norm_num : 99328 ≤ 100352), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 98304 ≤ 99328) (by norm_num : 99328 ≤ 100352), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 98304 ≤ 99328) (by norm_num : 99328 ≤ 100352), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_100352_100416 :
    (∑ n ∈ Ico 100352 100416, mobiusTreeValue 16 mobiusTable1200001 n) = (-4 : ℤ) ∧
    (∑ n ∈ Ico 100352 100416, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 100352 100416, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-199247 : ℤ) ∧
    (∑ n ∈ Ico 100352 100416, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-3984956737045658080920716638 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_100416_100480 :
    (∑ n ∈ Ico 100416 100480, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 100416 100480, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 100416 100480, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-49645 : ℤ) ∧
    (∑ n ∈ Ico 100416 100480, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-992913656794372362880911021 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_100352_100480 :
    (∑ n ∈ Ico 100352 100480, mobiusTreeValue 16 mobiusTable1200001 n) = (-5 : ℤ) ∧
    (∑ n ∈ Ico 100352 100480, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (79 : ℕ) ∧
    (∑ n ∈ Ico 100352 100480, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-248892 : ℤ) ∧
    (∑ n ∈ Ico 100352 100480, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-4977870393840030443801627659 : ℤ) := by
  rcases cdemPrefixStats_100352_100416 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_100416_100480 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 100352 ≤ 100416) (by norm_num : 100416 ≤ 100480), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 100352 ≤ 100416) (by norm_num : 100416 ≤ 100480), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 100352 ≤ 100416) (by norm_num : 100416 ≤ 100480), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 100352 ≤ 100416) (by norm_num : 100416 ≤ 100480), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_100480_100544 :
    (∑ n ∈ Ico 100480 100544, mobiusTreeValue 16 mobiusTable1200001 n) = (-4 : ℤ) ∧
    (∑ n ∈ Ico 100480 100544, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 100480 100544, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-199063 : ℤ) ∧
    (∑ n ∈ Ico 100480 100544, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-3981317006699859250621217441 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_100544_100608 :
    (∑ n ∈ Ico 100544 100608, mobiusTreeValue 16 mobiusTable1200001 n) = (5 : ℤ) ∧
    (∑ n ∈ Ico 100544 100608, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 100544 100608, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (248500 : ℤ) ∧
    (∑ n ∈ Ico 100544 100608, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (4969981014061710574498166824 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_100480_100608 :
    (∑ n ∈ Ico 100480 100608, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 100480 100608, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 100480 100608, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (49437 : ℤ) ∧
    (∑ n ∈ Ico 100480 100608, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (988664007361851323876949383 : ℤ) := by
  rcases cdemPrefixStats_100480_100544 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_100544_100608 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 100480 ≤ 100544) (by norm_num : 100544 ≤ 100608), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 100480 ≤ 100544) (by norm_num : 100544 ≤ 100608), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 100480 ≤ 100544) (by norm_num : 100544 ≤ 100608), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 100480 ≤ 100544) (by norm_num : 100544 ≤ 100608), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_100352_100608 :
    (∑ n ∈ Ico 100352 100608, mobiusTreeValue 16 mobiusTable1200001 n) = (-4 : ℤ) ∧
    (∑ n ∈ Ico 100352 100608, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (156 : ℕ) ∧
    (∑ n ∈ Ico 100352 100608, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-199455 : ℤ) ∧
    (∑ n ∈ Ico 100352 100608, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-3989206386478179119924678276 : ℤ) := by
  rcases cdemPrefixStats_100352_100480 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_100480_100608 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 100352 ≤ 100480) (by norm_num : 100480 ≤ 100608), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 100352 ≤ 100480) (by norm_num : 100480 ≤ 100608), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 100352 ≤ 100480) (by norm_num : 100480 ≤ 100608), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 100352 ≤ 100480) (by norm_num : 100480 ≤ 100608), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_100608_100672 :
    (∑ n ∈ Ico 100608 100672, mobiusTreeValue 16 mobiusTable1200001 n) = (2 : ℤ) ∧
    (∑ n ∈ Ico 100608 100672, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 100608 100672, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (99363 : ℤ) ∧
    (∑ n ∈ Ico 100608 100672, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1987271225525406015659186688 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_100672_100736 :
    (∑ n ∈ Ico 100672 100736, mobiusTreeValue 16 mobiusTable1200001 n) = (4 : ℤ) ∧
    (∑ n ∈ Ico 100672 100736, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 100672 100736, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (198507 : ℤ) ∧
    (∑ n ∈ Ico 100672 100736, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (3970163629555235881424290951 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_100608_100736 :
    (∑ n ∈ Ico 100608 100736, mobiusTreeValue 16 mobiusTable1200001 n) = (6 : ℤ) ∧
    (∑ n ∈ Ico 100608 100736, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (80 : ℕ) ∧
    (∑ n ∈ Ico 100608 100736, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (297870 : ℤ) ∧
    (∑ n ∈ Ico 100608 100736, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (5957434855080641897083477639 : ℤ) := by
  rcases cdemPrefixStats_100608_100672 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_100672_100736 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 100608 ≤ 100672) (by norm_num : 100672 ≤ 100736), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 100608 ≤ 100672) (by norm_num : 100672 ≤ 100736), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 100608 ≤ 100672) (by norm_num : 100672 ≤ 100736), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 100608 ≤ 100672) (by norm_num : 100672 ≤ 100736), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_100736_100800 :
    (∑ n ∈ Ico 100736 100800, mobiusTreeValue 16 mobiusTable1200001 n) = (7 : ℤ) ∧
    (∑ n ∈ Ico 100736 100800, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 100736 100800, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (347385 : ℤ) ∧
    (∑ n ∈ Ico 100736 100800, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (6947792182967755687307406929 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_100800_100864 :
    (∑ n ∈ Ico 100800 100864, mobiusTreeValue 16 mobiusTable1200001 n) = (8 : ℤ) ∧
    (∑ n ∈ Ico 100800 100864, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 100800 100864, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (396727 : ℤ) ∧
    (∑ n ∈ Ico 100800 100864, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (7934618855143399148344914846 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_100736_100864 :
    (∑ n ∈ Ico 100736 100864, mobiusTreeValue 16 mobiusTable1200001 n) = (15 : ℤ) ∧
    (∑ n ∈ Ico 100736 100864, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 100736 100864, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (744112 : ℤ) ∧
    (∑ n ∈ Ico 100736 100864, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (14882411038111154835652321775 : ℤ) := by
  rcases cdemPrefixStats_100736_100800 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_100800_100864 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 100736 ≤ 100800) (by norm_num : 100800 ≤ 100864), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 100736 ≤ 100800) (by norm_num : 100800 ≤ 100864), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 100736 ≤ 100800) (by norm_num : 100800 ≤ 100864), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 100736 ≤ 100800) (by norm_num : 100800 ≤ 100864), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_100608_100864 :
    (∑ n ∈ Ico 100608 100864, mobiusTreeValue 16 mobiusTable1200001 n) = (21 : ℤ) ∧
    (∑ n ∈ Ico 100608 100864, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (157 : ℕ) ∧
    (∑ n ∈ Ico 100608 100864, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (1041982 : ℤ) ∧
    (∑ n ∈ Ico 100608 100864, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (20839845893191796732735799414 : ℤ) := by
  rcases cdemPrefixStats_100608_100736 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_100736_100864 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 100608 ≤ 100736) (by norm_num : 100736 ≤ 100864), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 100608 ≤ 100736) (by norm_num : 100736 ≤ 100864), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 100608 ≤ 100736) (by norm_num : 100736 ≤ 100864), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 100608 ≤ 100736) (by norm_num : 100736 ≤ 100864), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_100352_100864 :
    (∑ n ∈ Ico 100352 100864, mobiusTreeValue 16 mobiusTable1200001 n) = (17 : ℤ) ∧
    (∑ n ∈ Ico 100352 100864, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (313 : ℕ) ∧
    (∑ n ∈ Ico 100352 100864, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (842527 : ℤ) ∧
    (∑ n ∈ Ico 100352 100864, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (16850639506713617612811121138 : ℤ) := by
  rcases cdemPrefixStats_100352_100608 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_100608_100864 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 100352 ≤ 100608) (by norm_num : 100608 ≤ 100864), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 100352 ≤ 100608) (by norm_num : 100608 ≤ 100864), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 100352 ≤ 100608) (by norm_num : 100608 ≤ 100864), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 100352 ≤ 100608) (by norm_num : 100608 ≤ 100864), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_100864_100928 :
    (∑ n ∈ Ico 100864 100928, mobiusTreeValue 16 mobiusTable1200001 n) = (5 : ℤ) ∧
    (∑ n ∈ Ico 100864 100928, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 100864 100928, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (247828 : ℤ) ∧
    (∑ n ∈ Ico 100864 100928, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (4956521539088245195546992967 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_100928_100992 :
    (∑ n ∈ Ico 100928 100992, mobiusTreeValue 16 mobiusTable1200001 n) = (-14 : ℤ) ∧
    (∑ n ∈ Ico 100928 100992, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 100928 100992, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-693349 : ℤ) ∧
    (∑ n ∈ Ico 100928 100992, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-13867133797155480418347500318 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_100864_100992 :
    (∑ n ∈ Ico 100864 100992, mobiusTreeValue 16 mobiusTable1200001 n) = (-9 : ℤ) ∧
    (∑ n ∈ Ico 100864 100992, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 100864 100992, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-445521 : ℤ) ∧
    (∑ n ∈ Ico 100864 100992, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-8910612258067235222800507351 : ℤ) := by
  rcases cdemPrefixStats_100864_100928 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_100928_100992 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 100864 ≤ 100928) (by norm_num : 100928 ≤ 100992), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 100864 ≤ 100928) (by norm_num : 100928 ≤ 100992), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 100864 ≤ 100928) (by norm_num : 100928 ≤ 100992), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 100864 ≤ 100928) (by norm_num : 100928 ≤ 100992), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_100992_101056 :
    (∑ n ∈ Ico 100992 101056, mobiusTreeValue 16 mobiusTable1200001 n) = (-3 : ℤ) ∧
    (∑ n ∈ Ico 100992 101056, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 100992 101056, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-148527 : ℤ) ∧
    (∑ n ∈ Ico 100992 101056, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-2970561516857688520691733613 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_101056_101120 :
    (∑ n ∈ Ico 101056 101120, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 101056 101120, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 101056 101120, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-49388 : ℤ) ∧
    (∑ n ∈ Ico 101056 101120, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-987789069475184060888307404 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_100992_101120 :
    (∑ n ∈ Ico 100992 101120, mobiusTreeValue 16 mobiusTable1200001 n) = (-4 : ℤ) ∧
    (∑ n ∈ Ico 100992 101120, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 100992 101120, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-197915 : ℤ) ∧
    (∑ n ∈ Ico 100992 101120, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-3958350586332872581580041017 : ℤ) := by
  rcases cdemPrefixStats_100992_101056 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_101056_101120 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 100992 ≤ 101056) (by norm_num : 101056 ≤ 101120), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 100992 ≤ 101056) (by norm_num : 101056 ≤ 101120), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 100992 ≤ 101056) (by norm_num : 101056 ≤ 101120), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 100992 ≤ 101056) (by norm_num : 101056 ≤ 101120), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_100864_101120 :
    (∑ n ∈ Ico 100864 101120, mobiusTreeValue 16 mobiusTable1200001 n) = (-13 : ℤ) ∧
    (∑ n ∈ Ico 100864 101120, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (155 : ℕ) ∧
    (∑ n ∈ Ico 100864 101120, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-643436 : ℤ) ∧
    (∑ n ∈ Ico 100864 101120, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-12868962844400107804380548368 : ℤ) := by
  rcases cdemPrefixStats_100864_100992 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_100992_101120 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 100864 ≤ 100992) (by norm_num : 100992 ≤ 101120), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 100864 ≤ 100992) (by norm_num : 100992 ≤ 101120), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 100864 ≤ 100992) (by norm_num : 100992 ≤ 101120), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 100864 ≤ 100992) (by norm_num : 100992 ≤ 101120), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_101120_101184 :
    (∑ n ∈ Ico 101120 101184, mobiusTreeValue 16 mobiusTable1200001 n) = (-4 : ℤ) ∧
    (∑ n ∈ Ico 101120 101184, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 101120 101184, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-197706 : ℤ) ∧
    (∑ n ∈ Ico 101120 101184, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-3954083488996218202200354433 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_101184_101248 :
    (∑ n ∈ Ico 101184 101248, mobiusTreeValue 16 mobiusTable1200001 n) = (9 : ℤ) ∧
    (∑ n ∈ Ico 101184 101248, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 101184 101248, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (444516 : ℤ) ∧
    (∑ n ∈ Ico 101184 101248, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (8890342943908927064546485809 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_101120_101248 :
    (∑ n ∈ Ico 101120 101248, mobiusTreeValue 16 mobiusTable1200001 n) = (5 : ℤ) ∧
    (∑ n ∈ Ico 101120 101248, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (79 : ℕ) ∧
    (∑ n ∈ Ico 101120 101248, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (246810 : ℤ) ∧
    (∑ n ∈ Ico 101120 101248, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (4936259454912708862346131376 : ℤ) := by
  rcases cdemPrefixStats_101120_101184 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_101184_101248 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 101120 ≤ 101184) (by norm_num : 101184 ≤ 101248), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 101120 ≤ 101184) (by norm_num : 101184 ≤ 101248), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 101120 ≤ 101184) (by norm_num : 101184 ≤ 101248), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 101120 ≤ 101184) (by norm_num : 101184 ≤ 101248), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_101248_101312 :
    (∑ n ∈ Ico 101248 101312, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 101248 101312, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 101248 101312, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (49429 : ℤ) ∧
    (∑ n ∈ Ico 101248 101312, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (988571052834649238233647625 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_101312_101376 :
    (∑ n ∈ Ico 101312 101376, mobiusTreeValue 16 mobiusTable1200001 n) = (-3 : ℤ) ∧
    (∑ n ∈ Ico 101312 101376, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 101312 101376, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-148111 : ℤ) ∧
    (∑ n ∈ Ico 101312 101376, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-2962259449796951055819143541 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_101248_101376 :
    (∑ n ∈ Ico 101248 101376, mobiusTreeValue 16 mobiusTable1200001 n) = (-2 : ℤ) ∧
    (∑ n ∈ Ico 101248 101376, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 101248 101376, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-98682 : ℤ) ∧
    (∑ n ∈ Ico 101248 101376, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-1973688396962301817585495916 : ℤ) := by
  rcases cdemPrefixStats_101248_101312 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_101312_101376 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 101248 ≤ 101312) (by norm_num : 101312 ≤ 101376), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 101248 ≤ 101312) (by norm_num : 101312 ≤ 101376), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 101248 ≤ 101312) (by norm_num : 101312 ≤ 101376), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 101248 ≤ 101312) (by norm_num : 101312 ≤ 101376), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_101120_101376 :
    (∑ n ∈ Ico 101120 101376, mobiusTreeValue 16 mobiusTable1200001 n) = (3 : ℤ) ∧
    (∑ n ∈ Ico 101120 101376, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (157 : ℕ) ∧
    (∑ n ∈ Ico 101120 101376, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (148128 : ℤ) ∧
    (∑ n ∈ Ico 101120 101376, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (2962571057950407044760635460 : ℤ) := by
  rcases cdemPrefixStats_101120_101248 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_101248_101376 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 101120 ≤ 101248) (by norm_num : 101248 ≤ 101376), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 101120 ≤ 101248) (by norm_num : 101248 ≤ 101376), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 101120 ≤ 101248) (by norm_num : 101248 ≤ 101376), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 101120 ≤ 101248) (by norm_num : 101248 ≤ 101376), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_100864_101376 :
    (∑ n ∈ Ico 100864 101376, mobiusTreeValue 16 mobiusTable1200001 n) = (-10 : ℤ) ∧
    (∑ n ∈ Ico 100864 101376, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (312 : ℕ) ∧
    (∑ n ∈ Ico 100864 101376, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-495308 : ℤ) ∧
    (∑ n ∈ Ico 100864 101376, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-9906391786449700759619912908 : ℤ) := by
  rcases cdemPrefixStats_100864_101120 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_101120_101376 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 100864 ≤ 101120) (by norm_num : 101120 ≤ 101376), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 100864 ≤ 101120) (by norm_num : 101120 ≤ 101376), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 100864 ≤ 101120) (by norm_num : 101120 ≤ 101376), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 100864 ≤ 101120) (by norm_num : 101120 ≤ 101376), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_100352_101376 :
    (∑ n ∈ Ico 100352 101376, mobiusTreeValue 16 mobiusTable1200001 n) = (7 : ℤ) ∧
    (∑ n ∈ Ico 100352 101376, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (625 : ℕ) ∧
    (∑ n ∈ Ico 100352 101376, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (347219 : ℤ) ∧
    (∑ n ∈ Ico 100352 101376, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (6944247720263916853191208230 : ℤ) := by
  rcases cdemPrefixStats_100352_100864 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_100864_101376 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 100352 ≤ 100864) (by norm_num : 100864 ≤ 101376), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 100352 ≤ 100864) (by norm_num : 100864 ≤ 101376), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 100352 ≤ 100864) (by norm_num : 100864 ≤ 101376), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 100352 ≤ 100864) (by norm_num : 100864 ≤ 101376), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_101376_101440 :
    (∑ n ∈ Ico 101376 101440, mobiusTreeValue 16 mobiusTable1200001 n) = (-7 : ℤ) ∧
    (∑ n ∈ Ico 101376 101440, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 101376 101440, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-345207 : ℤ) ∧
    (∑ n ∈ Ico 101376 101440, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-6904247975389475414656319620 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_101440_101504 :
    (∑ n ∈ Ico 101440 101504, mobiusTreeValue 16 mobiusTable1200001 n) = (-8 : ℤ) ∧
    (∑ n ∈ Ico 101440 101504, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 101440 101504, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-394148 : ℤ) ∧
    (∑ n ∈ Ico 101440 101504, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-7883045523402852388741393648 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_101376_101504 :
    (∑ n ∈ Ico 101376 101504, mobiusTreeValue 16 mobiusTable1200001 n) = (-15 : ℤ) ∧
    (∑ n ∈ Ico 101376 101504, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (79 : ℕ) ∧
    (∑ n ∈ Ico 101376 101504, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-739355 : ℤ) ∧
    (∑ n ∈ Ico 101376 101504, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-14787293498792327803397713268 : ℤ) := by
  rcases cdemPrefixStats_101376_101440 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_101440_101504 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 101376 ≤ 101440) (by norm_num : 101440 ≤ 101504), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 101376 ≤ 101440) (by norm_num : 101440 ≤ 101504), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 101376 ≤ 101440) (by norm_num : 101440 ≤ 101504), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 101376 ≤ 101440) (by norm_num : 101440 ≤ 101504), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_101504_101568 :
    (∑ n ∈ Ico 101504 101568, mobiusTreeValue 16 mobiusTable1200001 n) = (-6 : ℤ) ∧
    (∑ n ∈ Ico 101504 101568, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 101504 101568, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-295454 : ℤ) ∧
    (∑ n ∈ Ico 101504 101568, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-5909098468159878271670748650 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_101568_101632 :
    (∑ n ∈ Ico 101568 101632, mobiusTreeValue 16 mobiusTable1200001 n) = (-7 : ℤ) ∧
    (∑ n ∈ Ico 101568 101632, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 101568 101632, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-344479 : ℤ) ∧
    (∑ n ∈ Ico 101568 101632, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-6889657210752745279434394207 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_101504_101632 :
    (∑ n ∈ Ico 101504 101632, mobiusTreeValue 16 mobiusTable1200001 n) = (-13 : ℤ) ∧
    (∑ n ∈ Ico 101504 101632, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 101504 101632, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-639933 : ℤ) ∧
    (∑ n ∈ Ico 101504 101632, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-12798755678912623551105142857 : ℤ) := by
  rcases cdemPrefixStats_101504_101568 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_101568_101632 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 101504 ≤ 101568) (by norm_num : 101568 ≤ 101632), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 101504 ≤ 101568) (by norm_num : 101568 ≤ 101632), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 101504 ≤ 101568) (by norm_num : 101568 ≤ 101632), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 101504 ≤ 101568) (by norm_num : 101568 ≤ 101632), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_101376_101632 :
    (∑ n ∈ Ico 101376 101632, mobiusTreeValue 16 mobiusTable1200001 n) = (-28 : ℤ) ∧
    (∑ n ∈ Ico 101376 101632, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (156 : ℕ) ∧
    (∑ n ∈ Ico 101376 101632, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-1379288 : ℤ) ∧
    (∑ n ∈ Ico 101376 101632, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-27586049177704951354502856125 : ℤ) := by
  rcases cdemPrefixStats_101376_101504 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_101504_101632 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 101376 ≤ 101504) (by norm_num : 101504 ≤ 101632), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 101376 ≤ 101504) (by norm_num : 101504 ≤ 101632), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 101376 ≤ 101504) (by norm_num : 101504 ≤ 101632), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 101376 ≤ 101504) (by norm_num : 101504 ≤ 101632), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_101632_101696 :
    (∑ n ∈ Ico 101632 101696, mobiusTreeValue 16 mobiusTable1200001 n) = (3 : ℤ) ∧
    (∑ n ∈ Ico 101632 101696, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 101632 101696, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (147546 : ℤ) ∧
    (∑ n ∈ Ico 101632 101696, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (2950858302742215718450153750 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_101696_101760 :
    (∑ n ∈ Ico 101696 101760, mobiusTreeValue 16 mobiusTable1200001 n) = (-4 : ℤ) ∧
    (∑ n ∈ Ico 101696 101760, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 101696 101760, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-196596 : ℤ) ∧
    (∑ n ∈ Ico 101696 101760, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-3931938350625015724109381333 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_101632_101760 :
    (∑ n ∈ Ico 101632 101760, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 101632 101760, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (79 : ℕ) ∧
    (∑ n ∈ Ico 101632 101760, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-49050 : ℤ) ∧
    (∑ n ∈ Ico 101632 101760, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-981080047882800005659227583 : ℤ) := by
  rcases cdemPrefixStats_101632_101696 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_101696_101760 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 101632 ≤ 101696) (by norm_num : 101696 ≤ 101760), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 101632 ≤ 101696) (by norm_num : 101696 ≤ 101760), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 101632 ≤ 101696) (by norm_num : 101696 ≤ 101760), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 101632 ≤ 101696) (by norm_num : 101696 ≤ 101760), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_101760_101824 :
    (∑ n ∈ Ico 101760 101824, mobiusTreeValue 16 mobiusTable1200001 n) = (8 : ℤ) ∧
    (∑ n ∈ Ico 101760 101824, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 101760 101824, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (392990 : ℤ) ∧
    (∑ n ∈ Ico 101760 101824, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (7859868645693095294422694808 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_101824_101888 :
    (∑ n ∈ Ico 101824 101888, mobiusTreeValue 16 mobiusTable1200001 n) = (-4 : ℤ) ∧
    (∑ n ∈ Ico 101824 101888, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 101824 101888, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-196316 : ℤ) ∧
    (∑ n ∈ Ico 101824 101888, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-3926331933395116312182285978 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_101760_101888 :
    (∑ n ∈ Ico 101760 101888, mobiusTreeValue 16 mobiusTable1200001 n) = (4 : ℤ) ∧
    (∑ n ∈ Ico 101760 101888, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (76 : ℕ) ∧
    (∑ n ∈ Ico 101760 101888, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (196674 : ℤ) ∧
    (∑ n ∈ Ico 101760 101888, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (3933536712297978982240408830 : ℤ) := by
  rcases cdemPrefixStats_101760_101824 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_101824_101888 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 101760 ≤ 101824) (by norm_num : 101824 ≤ 101888), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 101760 ≤ 101824) (by norm_num : 101824 ≤ 101888), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 101760 ≤ 101824) (by norm_num : 101824 ≤ 101888), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 101760 ≤ 101824) (by norm_num : 101824 ≤ 101888), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_101632_101888 :
    (∑ n ∈ Ico 101632 101888, mobiusTreeValue 16 mobiusTable1200001 n) = (3 : ℤ) ∧
    (∑ n ∈ Ico 101632 101888, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (155 : ℕ) ∧
    (∑ n ∈ Ico 101632 101888, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (147624 : ℤ) ∧
    (∑ n ∈ Ico 101632 101888, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (2952456664415178976581181247 : ℤ) := by
  rcases cdemPrefixStats_101632_101760 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_101760_101888 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 101632 ≤ 101760) (by norm_num : 101760 ≤ 101888), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 101632 ≤ 101760) (by norm_num : 101760 ≤ 101888), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 101632 ≤ 101760) (by norm_num : 101760 ≤ 101888), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 101632 ≤ 101760) (by norm_num : 101760 ≤ 101888), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_101376_101888 :
    (∑ n ∈ Ico 101376 101888, mobiusTreeValue 16 mobiusTable1200001 n) = (-25 : ℤ) ∧
    (∑ n ∈ Ico 101376 101888, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (311 : ℕ) ∧
    (∑ n ∈ Ico 101376 101888, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-1231664 : ℤ) ∧
    (∑ n ∈ Ico 101376 101888, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-24633592513289772377921674878 : ℤ) := by
  rcases cdemPrefixStats_101376_101632 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_101632_101888 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 101376 ≤ 101632) (by norm_num : 101632 ≤ 101888), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 101376 ≤ 101632) (by norm_num : 101632 ≤ 101888), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 101376 ≤ 101632) (by norm_num : 101632 ≤ 101888), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 101376 ≤ 101632) (by norm_num : 101632 ≤ 101888), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_101888_101952 :
    (∑ n ∈ Ico 101888 101952, mobiusTreeValue 16 mobiusTable1200001 n) = (5 : ℤ) ∧
    (∑ n ∈ Ico 101888 101952, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 101888 101952, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (245229 : ℤ) ∧
    (∑ n ∈ Ico 101888 101952, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (4904653453439094683349906103 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_101952_102016 :
    (∑ n ∈ Ico 101952 102016, mobiusTreeValue 16 mobiusTable1200001 n) = (-4 : ℤ) ∧
    (∑ n ∈ Ico 101952 102016, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 101952 102016, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-196116 : ℤ) ∧
    (∑ n ∈ Ico 101952 102016, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-3922386037640969672378448742 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_101888_102016 :
    (∑ n ∈ Ico 101888 102016, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 101888 102016, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (79 : ℕ) ∧
    (∑ n ∈ Ico 101888 102016, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (49113 : ℤ) ∧
    (∑ n ∈ Ico 101888 102016, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (982267415798125010971457361 : ℤ) := by
  rcases cdemPrefixStats_101888_101952 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_101952_102016 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 101888 ≤ 101952) (by norm_num : 101952 ≤ 102016), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 101888 ≤ 101952) (by norm_num : 101952 ≤ 102016), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 101888 ≤ 101952) (by norm_num : 101952 ≤ 102016), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 101888 ≤ 101952) (by norm_num : 101952 ≤ 102016), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_102016_102080 :
    (∑ n ∈ Ico 102016 102080, mobiusTreeValue 16 mobiusTable1200001 n) = (-11 : ℤ) ∧
    (∑ n ∈ Ico 102016 102080, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 102016 102080, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-539012 : ℤ) ∧
    (∑ n ∈ Ico 102016 102080, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-10780326770758480155769083113 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_102080_102144 :
    (∑ n ∈ Ico 102080 102144, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 102080 102144, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 102080 102144, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-49055 : ℤ) ∧
    (∑ n ∈ Ico 102080 102144, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-981081439229277976557668302 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_102016_102144 :
    (∑ n ∈ Ico 102016 102144, mobiusTreeValue 16 mobiusTable1200001 n) = (-12 : ℤ) ∧
    (∑ n ∈ Ico 102016 102144, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 102016 102144, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-588067 : ℤ) ∧
    (∑ n ∈ Ico 102016 102144, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-11761408209987758132326751415 : ℤ) := by
  rcases cdemPrefixStats_102016_102080 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_102080_102144 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 102016 ≤ 102080) (by norm_num : 102080 ≤ 102144), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 102016 ≤ 102080) (by norm_num : 102080 ≤ 102144), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 102016 ≤ 102080) (by norm_num : 102080 ≤ 102144), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 102016 ≤ 102080) (by norm_num : 102080 ≤ 102144), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_101888_102144 :
    (∑ n ∈ Ico 101888 102144, mobiusTreeValue 16 mobiusTable1200001 n) = (-11 : ℤ) ∧
    (∑ n ∈ Ico 101888 102144, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (157 : ℕ) ∧
    (∑ n ∈ Ico 101888 102144, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-538954 : ℤ) ∧
    (∑ n ∈ Ico 101888 102144, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-10779140794189633121355294054 : ℤ) := by
  rcases cdemPrefixStats_101888_102016 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_102016_102144 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 101888 ≤ 102016) (by norm_num : 102016 ≤ 102144), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 101888 ≤ 102016) (by norm_num : 102016 ≤ 102144), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 101888 ≤ 102016) (by norm_num : 102016 ≤ 102144), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 101888 ≤ 102016) (by norm_num : 102016 ≤ 102144), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_102144_102208 :
    (∑ n ∈ Ico 102144 102208, mobiusTreeValue 16 mobiusTable1200001 n) = (-16 : ℤ) ∧
    (∑ n ∈ Ico 102144 102208, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 102144 102208, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-782984 : ℤ) ∧
    (∑ n ∈ Ico 102144 102208, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-15659849119019970484877541884 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_102208_102272 :
    (∑ n ∈ Ico 102208 102272, mobiusTreeValue 16 mobiusTable1200001 n) = (3 : ℤ) ∧
    (∑ n ∈ Ico 102208 102272, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 102208 102272, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (146731 : ℤ) ∧
    (∑ n ∈ Ico 102208 102272, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (2934645734529495540908513139 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_102144_102272 :
    (∑ n ∈ Ico 102144 102272, mobiusTreeValue 16 mobiusTable1200001 n) = (-13 : ℤ) ∧
    (∑ n ∈ Ico 102144 102272, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 102144 102272, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-636253 : ℤ) ∧
    (∑ n ∈ Ico 102144 102272, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-12725203384490474943969028745 : ℤ) := by
  rcases cdemPrefixStats_102144_102208 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_102208_102272 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 102144 ≤ 102208) (by norm_num : 102208 ≤ 102272), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 102144 ≤ 102208) (by norm_num : 102208 ≤ 102272), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 102144 ≤ 102208) (by norm_num : 102208 ≤ 102272), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 102144 ≤ 102208) (by norm_num : 102208 ≤ 102272), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_102272_102336 :
    (∑ n ∈ Ico 102272 102336, mobiusTreeValue 16 mobiusTable1200001 n) = (-10 : ℤ) ∧
    (∑ n ∈ Ico 102272 102336, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 102272 102336, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-488720 : ℤ) ∧
    (∑ n ∈ Ico 102272 102336, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-9774512245460545284491840685 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_102336_102400 :
    (∑ n ∈ Ico 102336 102400, mobiusTreeValue 16 mobiusTable1200001 n) = (13 : ℤ) ∧
    (∑ n ∈ Ico 102336 102400, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 102336 102400, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (634878 : ℤ) ∧
    (∑ n ∈ Ico 102336 102400, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (12697668873626341887733613588 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_102272_102400 :
    (∑ n ∈ Ico 102272 102400, mobiusTreeValue 16 mobiusTable1200001 n) = (3 : ℤ) ∧
    (∑ n ∈ Ico 102272 102400, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (81 : ℕ) ∧
    (∑ n ∈ Ico 102272 102400, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (146158 : ℤ) ∧
    (∑ n ∈ Ico 102272 102400, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (2923156628165796603241772903 : ℤ) := by
  rcases cdemPrefixStats_102272_102336 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_102336_102400 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 102272 ≤ 102336) (by norm_num : 102336 ≤ 102400), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 102272 ≤ 102336) (by norm_num : 102336 ≤ 102400), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 102272 ≤ 102336) (by norm_num : 102336 ≤ 102400), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 102272 ≤ 102336) (by norm_num : 102336 ≤ 102400), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_102144_102400 :
    (∑ n ∈ Ico 102144 102400, mobiusTreeValue 16 mobiusTable1200001 n) = (-10 : ℤ) ∧
    (∑ n ∈ Ico 102144 102400, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (158 : ℕ) ∧
    (∑ n ∈ Ico 102144 102400, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-490095 : ℤ) ∧
    (∑ n ∈ Ico 102144 102400, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-9802046756324678340727255842 : ℤ) := by
  rcases cdemPrefixStats_102144_102272 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_102272_102400 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 102144 ≤ 102272) (by norm_num : 102272 ≤ 102400), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 102144 ≤ 102272) (by norm_num : 102272 ≤ 102400), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 102144 ≤ 102272) (by norm_num : 102272 ≤ 102400), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 102144 ≤ 102272) (by norm_num : 102272 ≤ 102400), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_101888_102400 :
    (∑ n ∈ Ico 101888 102400, mobiusTreeValue 16 mobiusTable1200001 n) = (-21 : ℤ) ∧
    (∑ n ∈ Ico 101888 102400, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (315 : ℕ) ∧
    (∑ n ∈ Ico 101888 102400, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-1029049 : ℤ) ∧
    (∑ n ∈ Ico 101888 102400, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-20581187550514311462082549896 : ℤ) := by
  rcases cdemPrefixStats_101888_102144 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_102144_102400 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 101888 ≤ 102144) (by norm_num : 102144 ≤ 102400), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 101888 ≤ 102144) (by norm_num : 102144 ≤ 102400), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 101888 ≤ 102144) (by norm_num : 102144 ≤ 102400), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 101888 ≤ 102144) (by norm_num : 102144 ≤ 102400), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_101376_102400 :
    (∑ n ∈ Ico 101376 102400, mobiusTreeValue 16 mobiusTable1200001 n) = (-46 : ℤ) ∧
    (∑ n ∈ Ico 101376 102400, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (626 : ℕ) ∧
    (∑ n ∈ Ico 101376 102400, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-2260713 : ℤ) ∧
    (∑ n ∈ Ico 101376 102400, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-45214780063804083840004224774 : ℤ) := by
  rcases cdemPrefixStats_101376_101888 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_101888_102400 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 101376 ≤ 101888) (by norm_num : 101888 ≤ 102400), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 101376 ≤ 101888) (by norm_num : 101888 ≤ 102400), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 101376 ≤ 101888) (by norm_num : 101888 ≤ 102400), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 101376 ≤ 101888) (by norm_num : 101888 ≤ 102400), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_100352_102400 :
    (∑ n ∈ Ico 100352 102400, mobiusTreeValue 16 mobiusTable1200001 n) = (-39 : ℤ) ∧
    (∑ n ∈ Ico 100352 102400, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (1251 : ℕ) ∧
    (∑ n ∈ Ico 100352 102400, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-1913494 : ℤ) ∧
    (∑ n ∈ Ico 100352 102400, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-38270532343540166986813016544 : ℤ) := by
  rcases cdemPrefixStats_100352_101376 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_101376_102400 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 100352 ≤ 101376) (by norm_num : 101376 ≤ 102400), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 100352 ≤ 101376) (by norm_num : 101376 ≤ 102400), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 100352 ≤ 101376) (by norm_num : 101376 ≤ 102400), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 100352 ≤ 101376) (by norm_num : 101376 ≤ 102400), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_98304_102400 :
    (∑ n ∈ Ico 98304 102400, mobiusTreeValue 16 mobiusTable1200001 n) = (17 : ℤ) ∧
    (∑ n ∈ Ico 98304 102400, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (2499 : ℕ) ∧
    (∑ n ∈ Ico 98304 102400, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (896504 : ℤ) ∧
    (∑ n ∈ Ico 98304 102400, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (17929907555780736913298804430 : ℤ) := by
  rcases cdemPrefixStats_98304_100352 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_100352_102400 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 98304 ≤ 100352) (by norm_num : 100352 ≤ 102400), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 98304 ≤ 100352) (by norm_num : 100352 ≤ 102400), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 98304 ≤ 100352) (by norm_num : 100352 ≤ 102400), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 98304 ≤ 100352) (by norm_num : 100352 ≤ 102400), hR1, hR2] <;> norm_num

theorem cdemPrefixGroup024_checked_complete :
    (∑ n ∈ Ico 98304 102400, mobiusTreeValue 16 mobiusTable1200001 n) = (17 : ℤ) ∧
    (∑ n ∈ Ico 98304 102400, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (2499 : ℕ) ∧
    (∑ n ∈ Ico 98304 102400, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (896504 : ℤ) ∧
    (∑ n ∈ Ico 98304 102400, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (17929907555780736913298804430 : ℤ) := cdemPrefixStats_98304_102400
end Helfgott
#print axioms Helfgott.cdemPrefixGroup024_checked_complete

open Helfgott Finset
open scoped BigOperators

theorem solution :
    (∑ n ∈ Ico 98304 102400, mobiusTreeValue 16 mobiusTable1200001 n) = (17 : ℤ) ∧
    (∑ n ∈ Ico 98304 102400, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (2499 : ℕ) ∧
    (∑ n ∈ Ico 98304 102400, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (896504 : ℤ) ∧
    (∑ n ∈ Ico 98304 102400, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (17929907555780736913298804430 : ℤ) := Helfgott.cdemPrefixGroup024_checked_complete
#print axioms solution
