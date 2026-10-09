-- Prove2me | solution 1 for Helfgott.cdemPrefixGroup026_checked
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-09T02:06:56.756765+00:00
-- url     : https://prove2.me/submissions/6381e780-c649-48d3-8f27-f8ade21fa266

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
private theorem cdemPrefixStats_106496_106560 :
    (∑ n ∈ Ico 106496 106560, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 106496 106560, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 106496 106560, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (46978 : ℤ) ∧
    (∑ n ∈ Ico 106496 106560, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (939610165541964584032161135 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_106560_106624 :
    (∑ n ∈ Ico 106560 106624, mobiusTreeValue 16 mobiusTable1200001 n) = (6 : ℤ) ∧
    (∑ n ∈ Ico 106560 106624, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 106560 106624, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (281501 : ℤ) ∧
    (∑ n ∈ Ico 106560 106624, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (5630066787838028657309579505 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_106496_106624 :
    (∑ n ∈ Ico 106496 106624, mobiusTreeValue 16 mobiusTable1200001 n) = (7 : ℤ) ∧
    (∑ n ∈ Ico 106496 106624, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (79 : ℕ) ∧
    (∑ n ∈ Ico 106496 106624, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (328479 : ℤ) ∧
    (∑ n ∈ Ico 106496 106624, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (6569676953379993241341740640 : ℤ) := by
  rcases cdemPrefixStats_106496_106560 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_106560_106624 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 106496 ≤ 106560) (by norm_num : 106560 ≤ 106624), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 106496 ≤ 106560) (by norm_num : 106560 ≤ 106624), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 106496 ≤ 106560) (by norm_num : 106560 ≤ 106624), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 106496 ≤ 106560) (by norm_num : 106560 ≤ 106624), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_106624_106688 :
    (∑ n ∈ Ico 106624 106688, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 106624 106688, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 106624 106688, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (34 : ℤ) ∧
    (∑ n ∈ Ico 106624 106688, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (668158123434493406705196 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_106688_106752 :
    (∑ n ∈ Ico 106688 106752, mobiusTreeValue 16 mobiusTable1200001 n) = (-10 : ℤ) ∧
    (∑ n ∈ Ico 106688 106752, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 106688 106752, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-468452 : ℤ) ∧
    (∑ n ∈ Ico 106688 106752, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-9369129938212221201036742620 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_106624_106752 :
    (∑ n ∈ Ico 106624 106752, mobiusTreeValue 16 mobiusTable1200001 n) = (-10 : ℤ) ∧
    (∑ n ∈ Ico 106624 106752, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 106624 106752, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-468418 : ℤ) ∧
    (∑ n ∈ Ico 106624 106752, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-9368461780088786707630037424 : ℤ) := by
  rcases cdemPrefixStats_106624_106688 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_106688_106752 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 106624 ≤ 106688) (by norm_num : 106688 ≤ 106752), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 106624 ≤ 106688) (by norm_num : 106688 ≤ 106752), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 106624 ≤ 106688) (by norm_num : 106688 ≤ 106752), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 106624 ≤ 106688) (by norm_num : 106688 ≤ 106752), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_106496_106752 :
    (∑ n ∈ Ico 106496 106752, mobiusTreeValue 16 mobiusTable1200001 n) = (-3 : ℤ) ∧
    (∑ n ∈ Ico 106496 106752, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (157 : ℕ) ∧
    (∑ n ∈ Ico 106496 106752, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-139939 : ℤ) ∧
    (∑ n ∈ Ico 106496 106752, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-2798784826708793466288296784 : ℤ) := by
  rcases cdemPrefixStats_106496_106624 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_106624_106752 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 106496 ≤ 106624) (by norm_num : 106624 ≤ 106752), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 106496 ≤ 106624) (by norm_num : 106624 ≤ 106752), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 106496 ≤ 106624) (by norm_num : 106624 ≤ 106752), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 106496 ≤ 106624) (by norm_num : 106624 ≤ 106752), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_106752_106816 :
    (∑ n ∈ Ico 106752 106816, mobiusTreeValue 16 mobiusTable1200001 n) = (3 : ℤ) ∧
    (∑ n ∈ Ico 106752 106816, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 106752 106816, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (140434 : ℤ) ∧
    (∑ n ∈ Ico 106752 106816, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (2808708181025350755118248872 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_106816_106880 :
    (∑ n ∈ Ico 106816 106880, mobiusTreeValue 16 mobiusTable1200001 n) = (7 : ℤ) ∧
    (∑ n ∈ Ico 106816 106880, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 106816 106880, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (327595 : ℤ) ∧
    (∑ n ∈ Ico 106816 106880, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (6551984878121965670706987738 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_106752_106880 :
    (∑ n ∈ Ico 106752 106880, mobiusTreeValue 16 mobiusTable1200001 n) = (10 : ℤ) ∧
    (∑ n ∈ Ico 106752 106880, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (76 : ℕ) ∧
    (∑ n ∈ Ico 106752 106880, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (468029 : ℤ) ∧
    (∑ n ∈ Ico 106752 106880, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (9360693059147316425825236610 : ℤ) := by
  rcases cdemPrefixStats_106752_106816 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_106816_106880 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 106752 ≤ 106816) (by norm_num : 106816 ≤ 106880), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 106752 ≤ 106816) (by norm_num : 106816 ≤ 106880), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 106752 ≤ 106816) (by norm_num : 106816 ≤ 106880), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 106752 ≤ 106816) (by norm_num : 106816 ≤ 106880), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_106880_106944 :
    (∑ n ∈ Ico 106880 106944, mobiusTreeValue 16 mobiusTable1200001 n) = (4 : ℤ) ∧
    (∑ n ∈ Ico 106880 106944, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 106880 106944, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (187134 : ℤ) ∧
    (∑ n ∈ Ico 106880 106944, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (3742707278361491217581097017 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_106944_107008 :
    (∑ n ∈ Ico 106944 107008, mobiusTreeValue 16 mobiusTable1200001 n) = (-3 : ℤ) ∧
    (∑ n ∈ Ico 106944 107008, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 106944 107008, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-140317 : ℤ) ∧
    (∑ n ∈ Ico 106944 107008, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-2806351093281780497517849134 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_106880_107008 :
    (∑ n ∈ Ico 106880 107008, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 106880 107008, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (79 : ℕ) ∧
    (∑ n ∈ Ico 106880 107008, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (46817 : ℤ) ∧
    (∑ n ∈ Ico 106880 107008, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (936356185079710720063247883 : ℤ) := by
  rcases cdemPrefixStats_106880_106944 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_106944_107008 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 106880 ≤ 106944) (by norm_num : 106944 ≤ 107008), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 106880 ≤ 106944) (by norm_num : 106944 ≤ 107008), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 106880 ≤ 106944) (by norm_num : 106944 ≤ 107008), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 106880 ≤ 106944) (by norm_num : 106944 ≤ 107008), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_106752_107008 :
    (∑ n ∈ Ico 106752 107008, mobiusTreeValue 16 mobiusTable1200001 n) = (11 : ℤ) ∧
    (∑ n ∈ Ico 106752 107008, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (155 : ℕ) ∧
    (∑ n ∈ Ico 106752 107008, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (514846 : ℤ) ∧
    (∑ n ∈ Ico 106752 107008, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (10297049244227027145888484493 : ℤ) := by
  rcases cdemPrefixStats_106752_106880 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_106880_107008 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 106752 ≤ 106880) (by norm_num : 106880 ≤ 107008), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 106752 ≤ 106880) (by norm_num : 106880 ≤ 107008), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 106752 ≤ 106880) (by norm_num : 106880 ≤ 107008), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 106752 ≤ 106880) (by norm_num : 106880 ≤ 107008), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_106496_107008 :
    (∑ n ∈ Ico 106496 107008, mobiusTreeValue 16 mobiusTable1200001 n) = (8 : ℤ) ∧
    (∑ n ∈ Ico 106496 107008, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (312 : ℕ) ∧
    (∑ n ∈ Ico 106496 107008, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (374907 : ℤ) ∧
    (∑ n ∈ Ico 106496 107008, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (7498264417518233679600187709 : ℤ) := by
  rcases cdemPrefixStats_106496_106752 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_106752_107008 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 106496 ≤ 106752) (by norm_num : 106752 ≤ 107008), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 106496 ≤ 106752) (by norm_num : 106752 ≤ 107008), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 106496 ≤ 106752) (by norm_num : 106752 ≤ 107008), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 106496 ≤ 106752) (by norm_num : 106752 ≤ 107008), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_107008_107072 :
    (∑ n ∈ Ico 107008 107072, mobiusTreeValue 16 mobiusTable1200001 n) = (-6 : ℤ) ∧
    (∑ n ∈ Ico 107008 107072, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 107008 107072, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-280199 : ℤ) ∧
    (∑ n ∈ Ico 107008 107072, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-5604045885248604569947967570 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_107072_107136 :
    (∑ n ∈ Ico 107072 107136, mobiusTreeValue 16 mobiusTable1200001 n) = (-2 : ℤ) ∧
    (∑ n ∈ Ico 107072 107136, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 107072 107136, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-93387 : ℤ) ∧
    (∑ n ∈ Ico 107072 107136, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-1867718658726336979381273093 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_107008_107136 :
    (∑ n ∈ Ico 107008 107136, mobiusTreeValue 16 mobiusTable1200001 n) = (-8 : ℤ) ∧
    (∑ n ∈ Ico 107008 107136, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 107008 107136, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-373586 : ℤ) ∧
    (∑ n ∈ Ico 107008 107136, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-7471764543974941549329240663 : ℤ) := by
  rcases cdemPrefixStats_107008_107072 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_107072_107136 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 107008 ≤ 107072) (by norm_num : 107072 ≤ 107136), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 107008 ≤ 107072) (by norm_num : 107072 ≤ 107136), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 107008 ≤ 107072) (by norm_num : 107072 ≤ 107136), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 107008 ≤ 107072) (by norm_num : 107072 ≤ 107136), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_107136_107200 :
    (∑ n ∈ Ico 107136 107200, mobiusTreeValue 16 mobiusTable1200001 n) = (9 : ℤ) ∧
    (∑ n ∈ Ico 107136 107200, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 107136 107200, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (419916 : ℤ) ∧
    (∑ n ∈ Ico 107136 107200, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (8398473550741334707975778383 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_107200_107264 :
    (∑ n ∈ Ico 107200 107264, mobiusTreeValue 16 mobiusTable1200001 n) = (5 : ℤ) ∧
    (∑ n ∈ Ico 107200 107264, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 107200 107264, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (233135 : ℤ) ∧
    (∑ n ∈ Ico 107200 107264, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (4662769951205495660694545802 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_107136_107264 :
    (∑ n ∈ Ico 107136 107264, mobiusTreeValue 16 mobiusTable1200001 n) = (14 : ℤ) ∧
    (∑ n ∈ Ico 107136 107264, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (76 : ℕ) ∧
    (∑ n ∈ Ico 107136 107264, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (653051 : ℤ) ∧
    (∑ n ∈ Ico 107136 107264, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (13061243501946830368670324185 : ℤ) := by
  rcases cdemPrefixStats_107136_107200 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_107200_107264 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 107136 ≤ 107200) (by norm_num : 107200 ≤ 107264), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 107136 ≤ 107200) (by norm_num : 107200 ≤ 107264), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 107136 ≤ 107200) (by norm_num : 107200 ≤ 107264), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 107136 ≤ 107200) (by norm_num : 107200 ≤ 107264), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_107008_107264 :
    (∑ n ∈ Ico 107008 107264, mobiusTreeValue 16 mobiusTable1200001 n) = (6 : ℤ) ∧
    (∑ n ∈ Ico 107008 107264, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (154 : ℕ) ∧
    (∑ n ∈ Ico 107008 107264, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (279465 : ℤ) ∧
    (∑ n ∈ Ico 107008 107264, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (5589478957971888819341083522 : ℤ) := by
  rcases cdemPrefixStats_107008_107136 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_107136_107264 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 107008 ≤ 107136) (by norm_num : 107136 ≤ 107264), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 107008 ≤ 107136) (by norm_num : 107136 ≤ 107264), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 107008 ≤ 107136) (by norm_num : 107136 ≤ 107264), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 107008 ≤ 107136) (by norm_num : 107136 ≤ 107264), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_107264_107328 :
    (∑ n ∈ Ico 107264 107328, mobiusTreeValue 16 mobiusTable1200001 n) = (3 : ℤ) ∧
    (∑ n ∈ Ico 107264 107328, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 107264 107328, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (139838 : ℤ) ∧
    (∑ n ∈ Ico 107264 107328, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (2796811378741736950110905230 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_107328_107392 :
    (∑ n ∈ Ico 107328 107392, mobiusTreeValue 16 mobiusTable1200001 n) = (-7 : ℤ) ∧
    (∑ n ∈ Ico 107328 107392, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 107328 107392, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-326046 : ℤ) ∧
    (∑ n ∈ Ico 107328 107392, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-6520969411631643294767227723 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_107264_107392 :
    (∑ n ∈ Ico 107264 107392, mobiusTreeValue 16 mobiusTable1200001 n) = (-4 : ℤ) ∧
    (∑ n ∈ Ico 107264 107392, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 107264 107392, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-186208 : ℤ) ∧
    (∑ n ∈ Ico 107264 107392, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-3724158032889906344656322493 : ℤ) := by
  rcases cdemPrefixStats_107264_107328 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_107328_107392 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 107264 ≤ 107328) (by norm_num : 107328 ≤ 107392), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 107264 ≤ 107328) (by norm_num : 107328 ≤ 107392), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 107264 ≤ 107328) (by norm_num : 107328 ≤ 107392), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 107264 ≤ 107328) (by norm_num : 107328 ≤ 107392), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_107392_107456 :
    (∑ n ∈ Ico 107392 107456, mobiusTreeValue 16 mobiusTable1200001 n) = (6 : ℤ) ∧
    (∑ n ∈ Ico 107392 107456, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 107392 107456, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (279307 : ℤ) ∧
    (∑ n ∈ Ico 107392 107456, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (5586219265496259079647458862 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_107456_107520 :
    (∑ n ∈ Ico 107456 107520, mobiusTreeValue 16 mobiusTable1200001 n) = (8 : ℤ) ∧
    (∑ n ∈ Ico 107456 107520, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 107456 107520, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (372082 : ℤ) ∧
    (∑ n ∈ Ico 107456 107520, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (7441730898114318122022748263 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_107392_107520 :
    (∑ n ∈ Ico 107392 107520, mobiusTreeValue 16 mobiusTable1200001 n) = (14 : ℤ) ∧
    (∑ n ∈ Ico 107392 107520, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (80 : ℕ) ∧
    (∑ n ∈ Ico 107392 107520, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (651389 : ℤ) ∧
    (∑ n ∈ Ico 107392 107520, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (13027950163610577201670207125 : ℤ) := by
  rcases cdemPrefixStats_107392_107456 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_107456_107520 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 107392 ≤ 107456) (by norm_num : 107456 ≤ 107520), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 107392 ≤ 107456) (by norm_num : 107456 ≤ 107520), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 107392 ≤ 107456) (by norm_num : 107456 ≤ 107520), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 107392 ≤ 107456) (by norm_num : 107456 ≤ 107520), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_107264_107520 :
    (∑ n ∈ Ico 107264 107520, mobiusTreeValue 16 mobiusTable1200001 n) = (10 : ℤ) ∧
    (∑ n ∈ Ico 107264 107520, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (158 : ℕ) ∧
    (∑ n ∈ Ico 107264 107520, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (465181 : ℤ) ∧
    (∑ n ∈ Ico 107264 107520, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (9303792130720670857013884632 : ℤ) := by
  rcases cdemPrefixStats_107264_107392 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_107392_107520 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 107264 ≤ 107392) (by norm_num : 107392 ≤ 107520), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 107264 ≤ 107392) (by norm_num : 107392 ≤ 107520), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 107264 ≤ 107392) (by norm_num : 107392 ≤ 107520), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 107264 ≤ 107392) (by norm_num : 107392 ≤ 107520), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_107008_107520 :
    (∑ n ∈ Ico 107008 107520, mobiusTreeValue 16 mobiusTable1200001 n) = (16 : ℤ) ∧
    (∑ n ∈ Ico 107008 107520, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (312 : ℕ) ∧
    (∑ n ∈ Ico 107008 107520, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (744646 : ℤ) ∧
    (∑ n ∈ Ico 107008 107520, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (14893271088692559676354968154 : ℤ) := by
  rcases cdemPrefixStats_107008_107264 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_107264_107520 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 107008 ≤ 107264) (by norm_num : 107264 ≤ 107520), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 107008 ≤ 107264) (by norm_num : 107264 ≤ 107520), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 107008 ≤ 107264) (by norm_num : 107264 ≤ 107520), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 107008 ≤ 107264) (by norm_num : 107264 ≤ 107520), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_106496_107520 :
    (∑ n ∈ Ico 106496 107520, mobiusTreeValue 16 mobiusTable1200001 n) = (24 : ℤ) ∧
    (∑ n ∈ Ico 106496 107520, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (624 : ℕ) ∧
    (∑ n ∈ Ico 106496 107520, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (1119553 : ℤ) ∧
    (∑ n ∈ Ico 106496 107520, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (22391535506210793355955155863 : ℤ) := by
  rcases cdemPrefixStats_106496_107008 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_107008_107520 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 106496 ≤ 107008) (by norm_num : 107008 ≤ 107520), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 106496 ≤ 107008) (by norm_num : 107008 ≤ 107520), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 106496 ≤ 107008) (by norm_num : 107008 ≤ 107520), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 106496 ≤ 107008) (by norm_num : 107008 ≤ 107520), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_107520_107584 :
    (∑ n ∈ Ico 107520 107584, mobiusTreeValue 16 mobiusTable1200001 n) = (6 : ℤ) ∧
    (∑ n ∈ Ico 107520 107584, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 107520 107584, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (278887 : ℤ) ∧
    (∑ n ∈ Ico 107520 107584, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (5577815180383615449339086180 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_107584_107648 :
    (∑ n ∈ Ico 107584 107648, mobiusTreeValue 16 mobiusTable1200001 n) = (4 : ℤ) ∧
    (∑ n ∈ Ico 107584 107648, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (42 : ℕ) ∧
    (∑ n ∈ Ico 107584 107648, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (185883 : ℤ) ∧
    (∑ n ∈ Ico 107584 107648, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (3717679395671868667940990781 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_107520_107648 :
    (∑ n ∈ Ico 107520 107648, mobiusTreeValue 16 mobiusTable1200001 n) = (10 : ℤ) ∧
    (∑ n ∈ Ico 107520 107648, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (80 : ℕ) ∧
    (∑ n ∈ Ico 107520 107648, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (464770 : ℤ) ∧
    (∑ n ∈ Ico 107520 107648, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (9295494576055484117280076961 : ℤ) := by
  rcases cdemPrefixStats_107520_107584 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_107584_107648 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 107520 ≤ 107584) (by norm_num : 107584 ≤ 107648), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 107520 ≤ 107584) (by norm_num : 107584 ≤ 107648), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 107520 ≤ 107584) (by norm_num : 107584 ≤ 107648), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 107520 ≤ 107584) (by norm_num : 107584 ≤ 107648), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_107648_107712 :
    (∑ n ∈ Ico 107648 107712, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 107648 107712, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 107648 107712, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (46398 : ℤ) ∧
    (∑ n ∈ Ico 107648 107712, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (928004946624847557163008925 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_107712_107776 :
    (∑ n ∈ Ico 107712 107776, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 107712 107776, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 107712 107776, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-46416 : ℤ) ∧
    (∑ n ∈ Ico 107712 107776, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-928298123431144067486260273 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_107648_107776 :
    (∑ n ∈ Ico 107648 107776, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 107648 107776, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (76 : ℕ) ∧
    (∑ n ∈ Ico 107648 107776, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-18 : ℤ) ∧
    (∑ n ∈ Ico 107648 107776, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-293176806296510323251348 : ℤ) := by
  rcases cdemPrefixStats_107648_107712 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_107712_107776 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 107648 ≤ 107712) (by norm_num : 107712 ≤ 107776), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 107648 ≤ 107712) (by norm_num : 107712 ≤ 107776), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 107648 ≤ 107712) (by norm_num : 107712 ≤ 107776), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 107648 ≤ 107712) (by norm_num : 107712 ≤ 107776), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_107520_107776 :
    (∑ n ∈ Ico 107520 107776, mobiusTreeValue 16 mobiusTable1200001 n) = (10 : ℤ) ∧
    (∑ n ∈ Ico 107520 107776, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (156 : ℕ) ∧
    (∑ n ∈ Ico 107520 107776, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (464752 : ℤ) ∧
    (∑ n ∈ Ico 107520 107776, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (9295201399249187606956825613 : ℤ) := by
  rcases cdemPrefixStats_107520_107648 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_107648_107776 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 107520 ≤ 107648) (by norm_num : 107648 ≤ 107776), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 107520 ≤ 107648) (by norm_num : 107648 ≤ 107776), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 107520 ≤ 107648) (by norm_num : 107648 ≤ 107776), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 107520 ≤ 107648) (by norm_num : 107648 ≤ 107776), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_107776_107840 :
    (∑ n ∈ Ico 107776 107840, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 107776 107840, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 107776 107840, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (4 : ℤ) ∧
    (∑ n ∈ Ico 107776 107840, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (146061197178356738023395 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_107840_107904 :
    (∑ n ∈ Ico 107840 107904, mobiusTreeValue 16 mobiusTable1200001 n) = (-5 : ℤ) ∧
    (∑ n ∈ Ico 107840 107904, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 107840 107904, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-231739 : ℤ) ∧
    (∑ n ∈ Ico 107840 107904, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-4634831110599748826473799000 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_107776_107904 :
    (∑ n ∈ Ico 107776 107904, mobiusTreeValue 16 mobiusTable1200001 n) = (-5 : ℤ) ∧
    (∑ n ∈ Ico 107776 107904, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (79 : ℕ) ∧
    (∑ n ∈ Ico 107776 107904, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-231735 : ℤ) ∧
    (∑ n ∈ Ico 107776 107904, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-4634685049402570469735775605 : ℤ) := by
  rcases cdemPrefixStats_107776_107840 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_107840_107904 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 107776 ≤ 107840) (by norm_num : 107840 ≤ 107904), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 107776 ≤ 107840) (by norm_num : 107840 ≤ 107904), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 107776 ≤ 107840) (by norm_num : 107840 ≤ 107904), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 107776 ≤ 107840) (by norm_num : 107840 ≤ 107904), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_107904_107968 :
    (∑ n ∈ Ico 107904 107968, mobiusTreeValue 16 mobiusTable1200001 n) = (3 : ℤ) ∧
    (∑ n ∈ Ico 107904 107968, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 107904 107968, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (138885 : ℤ) ∧
    (∑ n ∈ Ico 107904 107968, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (2777691104324022873313065558 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_107968_108032 :
    (∑ n ∈ Ico 107968 108032, mobiusTreeValue 16 mobiusTable1200001 n) = (12 : ℤ) ∧
    (∑ n ∈ Ico 107968 108032, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 107968 108032, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (555552 : ℤ) ∧
    (∑ n ∈ Ico 107968 108032, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (11111145638498672666572237049 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_107904_108032 :
    (∑ n ∈ Ico 107904 108032, mobiusTreeValue 16 mobiusTable1200001 n) = (15 : ℤ) ∧
    (∑ n ∈ Ico 107904 108032, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 107904 108032, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (694437 : ℤ) ∧
    (∑ n ∈ Ico 107904 108032, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (13888836742822695539885302607 : ℤ) := by
  rcases cdemPrefixStats_107904_107968 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_107968_108032 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 107904 ≤ 107968) (by norm_num : 107968 ≤ 108032), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 107904 ≤ 107968) (by norm_num : 107968 ≤ 108032), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 107904 ≤ 107968) (by norm_num : 107968 ≤ 108032), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 107904 ≤ 107968) (by norm_num : 107968 ≤ 108032), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_107776_108032 :
    (∑ n ∈ Ico 107776 108032, mobiusTreeValue 16 mobiusTable1200001 n) = (10 : ℤ) ∧
    (∑ n ∈ Ico 107776 108032, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (156 : ℕ) ∧
    (∑ n ∈ Ico 107776 108032, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (462702 : ℤ) ∧
    (∑ n ∈ Ico 107776 108032, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (9254151693420125070149527002 : ℤ) := by
  rcases cdemPrefixStats_107776_107904 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_107904_108032 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 107776 ≤ 107904) (by norm_num : 107904 ≤ 108032), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 107776 ≤ 107904) (by norm_num : 107904 ≤ 108032), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 107776 ≤ 107904) (by norm_num : 107904 ≤ 108032), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 107776 ≤ 107904) (by norm_num : 107904 ≤ 108032), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_107520_108032 :
    (∑ n ∈ Ico 107520 108032, mobiusTreeValue 16 mobiusTable1200001 n) = (20 : ℤ) ∧
    (∑ n ∈ Ico 107520 108032, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (312 : ℕ) ∧
    (∑ n ∈ Ico 107520 108032, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (927454 : ℤ) ∧
    (∑ n ∈ Ico 107520 108032, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (18549353092669312677106352615 : ℤ) := by
  rcases cdemPrefixStats_107520_107776 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_107776_108032 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 107520 ≤ 107776) (by norm_num : 107776 ≤ 108032), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 107520 ≤ 107776) (by norm_num : 107776 ≤ 108032), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 107520 ≤ 107776) (by norm_num : 107776 ≤ 108032), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 107520 ≤ 107776) (by norm_num : 107776 ≤ 108032), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_108032_108096 :
    (∑ n ∈ Ico 108032 108096, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 108032 108096, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 108032 108096, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (40 : ℤ) ∧
    (∑ n ∈ Ico 108032 108096, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (830538319185501127288950 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_108096_108160 :
    (∑ n ∈ Ico 108096 108160, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 108096 108160, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 108096 108160, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (46299 : ℤ) ∧
    (∑ n ∈ Ico 108096 108160, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (925950206208731491677394151 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_108032_108160 :
    (∑ n ∈ Ico 108032 108160, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 108032 108160, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 108032 108160, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (46339 : ℤ) ∧
    (∑ n ∈ Ico 108032 108160, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (926780744527916992804683101 : ℤ) := by
  rcases cdemPrefixStats_108032_108096 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_108096_108160 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 108032 ≤ 108096) (by norm_num : 108096 ≤ 108160), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 108032 ≤ 108096) (by norm_num : 108096 ≤ 108160), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 108032 ≤ 108096) (by norm_num : 108096 ≤ 108160), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 108032 ≤ 108096) (by norm_num : 108096 ≤ 108160), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_108160_108224 :
    (∑ n ∈ Ico 108160 108224, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 108160 108224, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 108160 108224, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (46228 : ℤ) ∧
    (∑ n ∈ Ico 108160 108224, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (924607413608942332846456663 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_108224_108288 :
    (∑ n ∈ Ico 108224 108288, mobiusTreeValue 16 mobiusTable1200001 n) = (-3 : ℤ) ∧
    (∑ n ∈ Ico 108224 108288, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 108224 108288, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-138473 : ℤ) ∧
    (∑ n ∈ Ico 108224 108288, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-2769502647066002545600628527 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_108160_108288 :
    (∑ n ∈ Ico 108160 108288, mobiusTreeValue 16 mobiusTable1200001 n) = (-2 : ℤ) ∧
    (∑ n ∈ Ico 108160 108288, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (80 : ℕ) ∧
    (∑ n ∈ Ico 108160 108288, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-92245 : ℤ) ∧
    (∑ n ∈ Ico 108160 108288, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-1844895233457060212754171864 : ℤ) := by
  rcases cdemPrefixStats_108160_108224 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_108224_108288 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 108160 ≤ 108224) (by norm_num : 108224 ≤ 108288), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 108160 ≤ 108224) (by norm_num : 108224 ≤ 108288), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 108160 ≤ 108224) (by norm_num : 108224 ≤ 108288), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 108160 ≤ 108224) (by norm_num : 108224 ≤ 108288), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_108032_108288 :
    (∑ n ∈ Ico 108032 108288, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 108032 108288, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (157 : ℕ) ∧
    (∑ n ∈ Ico 108032 108288, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-45906 : ℤ) ∧
    (∑ n ∈ Ico 108032 108288, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-918114488929143219949488763 : ℤ) := by
  rcases cdemPrefixStats_108032_108160 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_108160_108288 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 108032 ≤ 108160) (by norm_num : 108160 ≤ 108288), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 108032 ≤ 108160) (by norm_num : 108160 ≤ 108288), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 108032 ≤ 108160) (by norm_num : 108160 ≤ 108288), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 108032 ≤ 108160) (by norm_num : 108160 ≤ 108288), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_108288_108352 :
    (∑ n ∈ Ico 108288 108352, mobiusTreeValue 16 mobiusTable1200001 n) = (2 : ℤ) ∧
    (∑ n ∈ Ico 108288 108352, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (36 : ℕ) ∧
    (∑ n ∈ Ico 108288 108352, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (92254 : ℤ) ∧
    (∑ n ∈ Ico 108288 108352, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1845119670539682684070331046 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_108352_108416 :
    (∑ n ∈ Ico 108352 108416, mobiusTreeValue 16 mobiusTable1200001 n) = (-8 : ℤ) ∧
    (∑ n ∈ Ico 108352 108416, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (42 : ℕ) ∧
    (∑ n ∈ Ico 108352 108416, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-369135 : ℤ) ∧
    (∑ n ∈ Ico 108352 108416, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-7382832156914817183388823010 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_108288_108416 :
    (∑ n ∈ Ico 108288 108416, mobiusTreeValue 16 mobiusTable1200001 n) = (-6 : ℤ) ∧
    (∑ n ∈ Ico 108288 108416, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 108288 108416, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-276881 : ℤ) ∧
    (∑ n ∈ Ico 108288 108416, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-5537712486375134499318491964 : ℤ) := by
  rcases cdemPrefixStats_108288_108352 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_108352_108416 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 108288 ≤ 108352) (by norm_num : 108352 ≤ 108416), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 108288 ≤ 108352) (by norm_num : 108352 ≤ 108416), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 108288 ≤ 108352) (by norm_num : 108352 ≤ 108416), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 108288 ≤ 108352) (by norm_num : 108352 ≤ 108416), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_108416_108480 :
    (∑ n ∈ Ico 108416 108480, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 108416 108480, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 108416 108480, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-46154 : ℤ) ∧
    (∑ n ∈ Ico 108416 108480, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-923002207524460208840769942 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_108480_108544 :
    (∑ n ∈ Ico 108480 108544, mobiusTreeValue 16 mobiusTable1200001 n) = (-12 : ℤ) ∧
    (∑ n ∈ Ico 108480 108544, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 108480 108544, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-552889 : ℤ) ∧
    (∑ n ∈ Ico 108480 108544, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-11057963128486820287202241474 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_108416_108544 :
    (∑ n ∈ Ico 108416 108544, mobiusTreeValue 16 mobiusTable1200001 n) = (-13 : ℤ) ∧
    (∑ n ∈ Ico 108416 108544, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 108416 108544, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-599043 : ℤ) ∧
    (∑ n ∈ Ico 108416 108544, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-11980965336011280496043011416 : ℤ) := by
  rcases cdemPrefixStats_108416_108480 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_108480_108544 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 108416 ≤ 108480) (by norm_num : 108480 ≤ 108544), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 108416 ≤ 108480) (by norm_num : 108480 ≤ 108544), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 108416 ≤ 108480) (by norm_num : 108480 ≤ 108544), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 108416 ≤ 108480) (by norm_num : 108480 ≤ 108544), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_108288_108544 :
    (∑ n ∈ Ico 108288 108544, mobiusTreeValue 16 mobiusTable1200001 n) = (-19 : ℤ) ∧
    (∑ n ∈ Ico 108288 108544, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (155 : ℕ) ∧
    (∑ n ∈ Ico 108288 108544, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-875924 : ℤ) ∧
    (∑ n ∈ Ico 108288 108544, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-17518677822386414995361503380 : ℤ) := by
  rcases cdemPrefixStats_108288_108416 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_108416_108544 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 108288 ≤ 108416) (by norm_num : 108416 ≤ 108544), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 108288 ≤ 108416) (by norm_num : 108416 ≤ 108544), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 108288 ≤ 108416) (by norm_num : 108416 ≤ 108544), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 108288 ≤ 108416) (by norm_num : 108416 ≤ 108544), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_108032_108544 :
    (∑ n ∈ Ico 108032 108544, mobiusTreeValue 16 mobiusTable1200001 n) = (-20 : ℤ) ∧
    (∑ n ∈ Ico 108032 108544, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (312 : ℕ) ∧
    (∑ n ∈ Ico 108032 108544, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-921830 : ℤ) ∧
    (∑ n ∈ Ico 108032 108544, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-18436792311315558215310992143 : ℤ) := by
  rcases cdemPrefixStats_108032_108288 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_108288_108544 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 108032 ≤ 108288) (by norm_num : 108288 ≤ 108544), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 108032 ≤ 108288) (by norm_num : 108288 ≤ 108544), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 108032 ≤ 108288) (by norm_num : 108288 ≤ 108544), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 108032 ≤ 108288) (by norm_num : 108288 ≤ 108544), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_107520_108544 :
    (∑ n ∈ Ico 107520 108544, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 107520 108544, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (624 : ℕ) ∧
    (∑ n ∈ Ico 107520 108544, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (5624 : ℤ) ∧
    (∑ n ∈ Ico 107520 108544, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (112560781353754461795360472 : ℤ) := by
  rcases cdemPrefixStats_107520_108032 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_108032_108544 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 107520 ≤ 108032) (by norm_num : 108032 ≤ 108544), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 107520 ≤ 108032) (by norm_num : 108032 ≤ 108544), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 107520 ≤ 108032) (by norm_num : 108032 ≤ 108544), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 107520 ≤ 108032) (by norm_num : 108032 ≤ 108544), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_106496_108544 :
    (∑ n ∈ Ico 106496 108544, mobiusTreeValue 16 mobiusTable1200001 n) = (24 : ℤ) ∧
    (∑ n ∈ Ico 106496 108544, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (1248 : ℕ) ∧
    (∑ n ∈ Ico 106496 108544, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (1125177 : ℤ) ∧
    (∑ n ∈ Ico 106496 108544, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (22504096287564547817750516335 : ℤ) := by
  rcases cdemPrefixStats_106496_107520 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_107520_108544 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 106496 ≤ 107520) (by norm_num : 107520 ≤ 108544), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 106496 ≤ 107520) (by norm_num : 107520 ≤ 108544), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 106496 ≤ 107520) (by norm_num : 107520 ≤ 108544), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 106496 ≤ 107520) (by norm_num : 107520 ≤ 108544), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_108544_108608 :
    (∑ n ∈ Ico 108544 108608, mobiusTreeValue 16 mobiusTable1200001 n) = (2 : ℤ) ∧
    (∑ n ∈ Ico 108544 108608, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 108544 108608, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (92073 : ℤ) ∧
    (∑ n ∈ Ico 108544 108608, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1841433963096850586583501024 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_108608_108672 :
    (∑ n ∈ Ico 108608 108672, mobiusTreeValue 16 mobiusTable1200001 n) = (3 : ℤ) ∧
    (∑ n ∈ Ico 108608 108672, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 108608 108672, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (138087 : ℤ) ∧
    (∑ n ∈ Ico 108608 108672, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (2761727432250764163393814470 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_108544_108672 :
    (∑ n ∈ Ico 108544 108672, mobiusTreeValue 16 mobiusTable1200001 n) = (5 : ℤ) ∧
    (∑ n ∈ Ico 108544 108672, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (75 : ℕ) ∧
    (∑ n ∈ Ico 108544 108672, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (230160 : ℤ) ∧
    (∑ n ∈ Ico 108544 108672, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (4603161395347614749977315494 : ℤ) := by
  rcases cdemPrefixStats_108544_108608 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_108608_108672 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 108544 ≤ 108608) (by norm_num : 108608 ≤ 108672), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 108544 ≤ 108608) (by norm_num : 108608 ≤ 108672), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 108544 ≤ 108608) (by norm_num : 108608 ≤ 108672), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 108544 ≤ 108608) (by norm_num : 108608 ≤ 108672), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_108672_108736 :
    (∑ n ∈ Ico 108672 108736, mobiusTreeValue 16 mobiusTable1200001 n) = (8 : ℤ) ∧
    (∑ n ∈ Ico 108672 108736, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 108672 108736, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (367964 : ℤ) ∧
    (∑ n ∈ Ico 108672 108736, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (7359384345826816292182260007 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_108736_108800 :
    (∑ n ∈ Ico 108736 108800, mobiusTreeValue 16 mobiusTable1200001 n) = (-2 : ℤ) ∧
    (∑ n ∈ Ico 108736 108800, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 108736 108800, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-91891 : ℤ) ∧
    (∑ n ∈ Ico 108736 108800, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-1837871870680740281722312433 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_108672_108800 :
    (∑ n ∈ Ico 108672 108800, mobiusTreeValue 16 mobiusTable1200001 n) = (6 : ℤ) ∧
    (∑ n ∈ Ico 108672 108800, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (80 : ℕ) ∧
    (∑ n ∈ Ico 108672 108800, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (276073 : ℤ) ∧
    (∑ n ∈ Ico 108672 108800, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (5521512475146076010459947574 : ℤ) := by
  rcases cdemPrefixStats_108672_108736 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_108736_108800 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 108672 ≤ 108736) (by norm_num : 108736 ≤ 108800), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 108672 ≤ 108736) (by norm_num : 108736 ≤ 108800), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 108672 ≤ 108736) (by norm_num : 108736 ≤ 108800), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 108672 ≤ 108736) (by norm_num : 108736 ≤ 108800), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_108544_108800 :
    (∑ n ∈ Ico 108544 108800, mobiusTreeValue 16 mobiusTable1200001 n) = (11 : ℤ) ∧
    (∑ n ∈ Ico 108544 108800, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (155 : ℕ) ∧
    (∑ n ∈ Ico 108544 108800, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (506233 : ℤ) ∧
    (∑ n ∈ Ico 108544 108800, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (10124673870493690760437263068 : ℤ) := by
  rcases cdemPrefixStats_108544_108672 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_108672_108800 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 108544 ≤ 108672) (by norm_num : 108672 ≤ 108800), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 108544 ≤ 108672) (by norm_num : 108672 ≤ 108800), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 108544 ≤ 108672) (by norm_num : 108672 ≤ 108800), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 108544 ≤ 108672) (by norm_num : 108672 ≤ 108800), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_108800_108864 :
    (∑ n ∈ Ico 108800 108864, mobiusTreeValue 16 mobiusTable1200001 n) = (5 : ℤ) ∧
    (∑ n ∈ Ico 108800 108864, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 108800 108864, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (229723 : ℤ) ∧
    (∑ n ∈ Ico 108800 108864, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (4594540988953946001827088642 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_108864_108928 :
    (∑ n ∈ Ico 108864 108928, mobiusTreeValue 16 mobiusTable1200001 n) = (-13 : ℤ) ∧
    (∑ n ∈ Ico 108864 108928, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 108864 108928, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-596925 : ℤ) ∧
    (∑ n ∈ Ico 108864 108928, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-11938654023153134121022354811 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_108800_108928 :
    (∑ n ∈ Ico 108800 108928, mobiusTreeValue 16 mobiusTable1200001 n) = (-8 : ℤ) ∧
    (∑ n ∈ Ico 108800 108928, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 108800 108928, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-367202 : ℤ) ∧
    (∑ n ∈ Ico 108800 108928, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-7344113034199188119195266169 : ℤ) := by
  rcases cdemPrefixStats_108800_108864 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_108864_108928 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 108800 ≤ 108864) (by norm_num : 108864 ≤ 108928), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 108800 ≤ 108864) (by norm_num : 108864 ≤ 108928), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 108800 ≤ 108864) (by norm_num : 108864 ≤ 108928), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 108800 ≤ 108864) (by norm_num : 108864 ≤ 108928), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_108928_108992 :
    (∑ n ∈ Ico 108928 108992, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 108928 108992, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 108928 108992, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (45931 : ℤ) ∧
    (∑ n ∈ Ico 108928 108992, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (918618851838404032518582848 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_108992_109056 :
    (∑ n ∈ Ico 108992 109056, mobiusTreeValue 16 mobiusTable1200001 n) = (6 : ℤ) ∧
    (∑ n ∈ Ico 108992 109056, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 108992 109056, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (275273 : ℤ) ∧
    (∑ n ∈ Ico 108992 109056, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (5505503819476797585701562559 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_108928_109056 :
    (∑ n ∈ Ico 108928 109056, mobiusTreeValue 16 mobiusTable1200001 n) = (7 : ℤ) ∧
    (∑ n ∈ Ico 108928 109056, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 108928 109056, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (321204 : ℤ) ∧
    (∑ n ∈ Ico 108928 109056, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (6424122671315201618220145407 : ℤ) := by
  rcases cdemPrefixStats_108928_108992 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_108992_109056 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 108928 ≤ 108992) (by norm_num : 108992 ≤ 109056), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 108928 ≤ 108992) (by norm_num : 108992 ≤ 109056), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 108928 ≤ 108992) (by norm_num : 108992 ≤ 109056), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 108928 ≤ 108992) (by norm_num : 108992 ≤ 109056), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_108800_109056 :
    (∑ n ∈ Ico 108800 109056, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 108800 109056, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (155 : ℕ) ∧
    (∑ n ∈ Ico 108800 109056, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-45998 : ℤ) ∧
    (∑ n ∈ Ico 108800 109056, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-919990362883986500975120762 : ℤ) := by
  rcases cdemPrefixStats_108800_108928 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_108928_109056 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 108800 ≤ 108928) (by norm_num : 108928 ≤ 109056), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 108800 ≤ 108928) (by norm_num : 108928 ≤ 109056), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 108800 ≤ 108928) (by norm_num : 108928 ≤ 109056), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 108800 ≤ 108928) (by norm_num : 108928 ≤ 109056), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_108544_109056 :
    (∑ n ∈ Ico 108544 109056, mobiusTreeValue 16 mobiusTable1200001 n) = (10 : ℤ) ∧
    (∑ n ∈ Ico 108544 109056, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (310 : ℕ) ∧
    (∑ n ∈ Ico 108544 109056, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (460235 : ℤ) ∧
    (∑ n ∈ Ico 108544 109056, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (9204683507609704259462142306 : ℤ) := by
  rcases cdemPrefixStats_108544_108800 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_108800_109056 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 108544 ≤ 108800) (by norm_num : 108800 ≤ 109056), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 108544 ≤ 108800) (by norm_num : 108800 ≤ 109056), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 108544 ≤ 108800) (by norm_num : 108800 ≤ 109056), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 108544 ≤ 108800) (by norm_num : 108800 ≤ 109056), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_109056_109120 :
    (∑ n ∈ Ico 109056 109120, mobiusTreeValue 16 mobiusTable1200001 n) = (4 : ℤ) ∧
    (∑ n ∈ Ico 109056 109120, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 109056 109120, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (183372 : ℤ) ∧
    (∑ n ∈ Ico 109056 109120, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (3667478926563466512768098053 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_109120_109184 :
    (∑ n ∈ Ico 109120 109184, mobiusTreeValue 16 mobiusTable1200001 n) = (-3 : ℤ) ∧
    (∑ n ∈ Ico 109120 109184, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 109120 109184, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-137445 : ℤ) ∧
    (∑ n ∈ Ico 109120 109184, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-2748930892287588463400295520 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_109056_109184 :
    (∑ n ∈ Ico 109056 109184, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 109056 109184, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 109056 109184, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (45927 : ℤ) ∧
    (∑ n ∈ Ico 109056 109184, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (918548034275878049367802533 : ℤ) := by
  rcases cdemPrefixStats_109056_109120 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_109120_109184 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 109056 ≤ 109120) (by norm_num : 109120 ≤ 109184), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 109056 ≤ 109120) (by norm_num : 109120 ≤ 109184), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 109056 ≤ 109120) (by norm_num : 109120 ≤ 109184), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 109056 ≤ 109120) (by norm_num : 109120 ≤ 109184), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_109184_109248 :
    (∑ n ∈ Ico 109184 109248, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 109184 109248, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 109184 109248, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (45766 : ℤ) ∧
    (∑ n ∈ Ico 109184 109248, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (915340256657606105161593089 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_109248_109312 :
    (∑ n ∈ Ico 109248 109312, mobiusTreeValue 16 mobiusTable1200001 n) = (2 : ℤ) ∧
    (∑ n ∈ Ico 109248 109312, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 109248 109312, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (91530 : ℤ) ∧
    (∑ n ∈ Ico 109248 109312, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1830621849536253749905224464 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_109184_109312 :
    (∑ n ∈ Ico 109184 109312, mobiusTreeValue 16 mobiusTable1200001 n) = (3 : ℤ) ∧
    (∑ n ∈ Ico 109184 109312, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (79 : ℕ) ∧
    (∑ n ∈ Ico 109184 109312, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (137296 : ℤ) ∧
    (∑ n ∈ Ico 109184 109312, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (2745962106193859855066817553 : ℤ) := by
  rcases cdemPrefixStats_109184_109248 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_109248_109312 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 109184 ≤ 109248) (by norm_num : 109248 ≤ 109312), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 109184 ≤ 109248) (by norm_num : 109248 ≤ 109312), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 109184 ≤ 109248) (by norm_num : 109248 ≤ 109312), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 109184 ≤ 109248) (by norm_num : 109248 ≤ 109312), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_109056_109312 :
    (∑ n ∈ Ico 109056 109312, mobiusTreeValue 16 mobiusTable1200001 n) = (4 : ℤ) ∧
    (∑ n ∈ Ico 109056 109312, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (156 : ℕ) ∧
    (∑ n ∈ Ico 109056 109312, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (183223 : ℤ) ∧
    (∑ n ∈ Ico 109056 109312, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (3664510140469737904434620086 : ℤ) := by
  rcases cdemPrefixStats_109056_109184 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_109184_109312 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 109056 ≤ 109184) (by norm_num : 109184 ≤ 109312), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 109056 ≤ 109184) (by norm_num : 109184 ≤ 109312), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 109056 ≤ 109184) (by norm_num : 109184 ≤ 109312), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 109056 ≤ 109184) (by norm_num : 109184 ≤ 109312), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_109312_109376 :
    (∑ n ∈ Ico 109312 109376, mobiusTreeValue 16 mobiusTable1200001 n) = (-4 : ℤ) ∧
    (∑ n ∈ Ico 109312 109376, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 109312 109376, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-182928 : ℤ) ∧
    (∑ n ∈ Ico 109312 109376, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-3658606709250386947629898380 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_109376_109440 :
    (∑ n ∈ Ico 109376 109440, mobiusTreeValue 16 mobiusTable1200001 n) = (-7 : ℤ) ∧
    (∑ n ∈ Ico 109376 109440, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 109376 109440, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-319934 : ℤ) ∧
    (∑ n ∈ Ico 109376 109440, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-6398679693745634684495871610 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_109312_109440 :
    (∑ n ∈ Ico 109312 109440, mobiusTreeValue 16 mobiusTable1200001 n) = (-11 : ℤ) ∧
    (∑ n ∈ Ico 109312 109440, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 109312 109440, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-502862 : ℤ) ∧
    (∑ n ∈ Ico 109312 109440, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-10057286402996021632125769990 : ℤ) := by
  rcases cdemPrefixStats_109312_109376 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_109376_109440 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 109312 ≤ 109376) (by norm_num : 109376 ≤ 109440), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 109312 ≤ 109376) (by norm_num : 109376 ≤ 109440), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 109312 ≤ 109376) (by norm_num : 109376 ≤ 109440), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 109312 ≤ 109376) (by norm_num : 109376 ≤ 109440), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_109440_109504 :
    (∑ n ∈ Ico 109440 109504, mobiusTreeValue 16 mobiusTable1200001 n) = (2 : ℤ) ∧
    (∑ n ∈ Ico 109440 109504, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 109440 109504, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (91295 : ℤ) ∧
    (∑ n ∈ Ico 109440 109504, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1825883299661236401970598379 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_109504_109568 :
    (∑ n ∈ Ico 109504 109568, mobiusTreeValue 16 mobiusTable1200001 n) = (-7 : ℤ) ∧
    (∑ n ∈ Ico 109504 109568, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (35 : ℕ) ∧
    (∑ n ∈ Ico 109504 109568, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-319554 : ℤ) ∧
    (∑ n ∈ Ico 109504 109568, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-6391118427280843443213759266 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_109440_109568 :
    (∑ n ∈ Ico 109440 109568, mobiusTreeValue 16 mobiusTable1200001 n) = (-5 : ℤ) ∧
    (∑ n ∈ Ico 109440 109568, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (73 : ℕ) ∧
    (∑ n ∈ Ico 109440 109568, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-228259 : ℤ) ∧
    (∑ n ∈ Ico 109440 109568, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-4565235127619607041243160887 : ℤ) := by
  rcases cdemPrefixStats_109440_109504 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_109504_109568 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 109440 ≤ 109504) (by norm_num : 109504 ≤ 109568), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 109440 ≤ 109504) (by norm_num : 109504 ≤ 109568), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 109440 ≤ 109504) (by norm_num : 109504 ≤ 109568), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 109440 ≤ 109504) (by norm_num : 109504 ≤ 109568), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_109312_109568 :
    (∑ n ∈ Ico 109312 109568, mobiusTreeValue 16 mobiusTable1200001 n) = (-16 : ℤ) ∧
    (∑ n ∈ Ico 109312 109568, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (150 : ℕ) ∧
    (∑ n ∈ Ico 109312 109568, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-731121 : ℤ) ∧
    (∑ n ∈ Ico 109312 109568, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-14622521530615628673368930877 : ℤ) := by
  rcases cdemPrefixStats_109312_109440 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_109440_109568 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 109312 ≤ 109440) (by norm_num : 109440 ≤ 109568), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 109312 ≤ 109440) (by norm_num : 109440 ≤ 109568), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 109312 ≤ 109440) (by norm_num : 109440 ≤ 109568), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 109312 ≤ 109440) (by norm_num : 109440 ≤ 109568), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_109056_109568 :
    (∑ n ∈ Ico 109056 109568, mobiusTreeValue 16 mobiusTable1200001 n) = (-12 : ℤ) ∧
    (∑ n ∈ Ico 109056 109568, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (306 : ℕ) ∧
    (∑ n ∈ Ico 109056 109568, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-547898 : ℤ) ∧
    (∑ n ∈ Ico 109056 109568, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-10958011390145890768934310791 : ℤ) := by
  rcases cdemPrefixStats_109056_109312 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_109312_109568 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 109056 ≤ 109312) (by norm_num : 109312 ≤ 109568), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 109056 ≤ 109312) (by norm_num : 109312 ≤ 109568), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 109056 ≤ 109312) (by norm_num : 109312 ≤ 109568), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 109056 ≤ 109312) (by norm_num : 109312 ≤ 109568), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_108544_109568 :
    (∑ n ∈ Ico 108544 109568, mobiusTreeValue 16 mobiusTable1200001 n) = (-2 : ℤ) ∧
    (∑ n ∈ Ico 108544 109568, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (616 : ℕ) ∧
    (∑ n ∈ Ico 108544 109568, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-87663 : ℤ) ∧
    (∑ n ∈ Ico 108544 109568, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-1753327882536186509472168485 : ℤ) := by
  rcases cdemPrefixStats_108544_109056 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_109056_109568 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 108544 ≤ 109056) (by norm_num : 109056 ≤ 109568), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 108544 ≤ 109056) (by norm_num : 109056 ≤ 109568), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 108544 ≤ 109056) (by norm_num : 109056 ≤ 109568), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 108544 ≤ 109056) (by norm_num : 109056 ≤ 109568), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_109568_109632 :
    (∑ n ∈ Ico 109568 109632, mobiusTreeValue 16 mobiusTable1200001 n) = (-2 : ℤ) ∧
    (∑ n ∈ Ico 109568 109632, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 109568 109632, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-91230 : ℤ) ∧
    (∑ n ∈ Ico 109568 109632, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-1824650948628369348587559805 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_109632_109696 :
    (∑ n ∈ Ico 109632 109696, mobiusTreeValue 16 mobiusTable1200001 n) = (11 : ℤ) ∧
    (∑ n ∈ Ico 109632 109696, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 109632 109696, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (501491 : ℤ) ∧
    (∑ n ∈ Ico 109632 109696, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (10029949283068414253676616541 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_109568_109696 :
    (∑ n ∈ Ico 109568 109696, mobiusTreeValue 16 mobiusTable1200001 n) = (9 : ℤ) ∧
    (∑ n ∈ Ico 109568 109696, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (79 : ℕ) ∧
    (∑ n ∈ Ico 109568 109696, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (410261 : ℤ) ∧
    (∑ n ∈ Ico 109568 109696, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (8205298334440044905089056736 : ℤ) := by
  rcases cdemPrefixStats_109568_109632 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_109632_109696 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 109568 ≤ 109632) (by norm_num : 109632 ≤ 109696), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 109568 ≤ 109632) (by norm_num : 109632 ≤ 109696), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 109568 ≤ 109632) (by norm_num : 109632 ≤ 109696), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 109568 ≤ 109632) (by norm_num : 109632 ≤ 109696), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_109696_109760 :
    (∑ n ∈ Ico 109696 109760, mobiusTreeValue 16 mobiusTable1200001 n) = (2 : ℤ) ∧
    (∑ n ∈ Ico 109696 109760, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 109696 109760, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (91169 : ℤ) ∧
    (∑ n ∈ Ico 109696 109760, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1823378700572546567399436738 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_109760_109824 :
    (∑ n ∈ Ico 109760 109824, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 109760 109824, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (42 : ℕ) ∧
    (∑ n ∈ Ico 109760 109824, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (8 : ℤ) ∧
    (∑ n ∈ Ico 109760 109824, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (182377342842473468681680 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_109696_109824 :
    (∑ n ∈ Ico 109696 109824, mobiusTreeValue 16 mobiusTable1200001 n) = (2 : ℤ) ∧
    (∑ n ∈ Ico 109696 109824, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (80 : ℕ) ∧
    (∑ n ∈ Ico 109696 109824, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (91177 : ℤ) ∧
    (∑ n ∈ Ico 109696 109824, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1823561077915389040868118418 : ℤ) := by
  rcases cdemPrefixStats_109696_109760 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_109760_109824 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 109696 ≤ 109760) (by norm_num : 109760 ≤ 109824), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 109696 ≤ 109760) (by norm_num : 109760 ≤ 109824), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 109696 ≤ 109760) (by norm_num : 109760 ≤ 109824), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 109696 ≤ 109760) (by norm_num : 109760 ≤ 109824), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_109568_109824 :
    (∑ n ∈ Ico 109568 109824, mobiusTreeValue 16 mobiusTable1200001 n) = (11 : ℤ) ∧
    (∑ n ∈ Ico 109568 109824, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (159 : ℕ) ∧
    (∑ n ∈ Ico 109568 109824, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (501438 : ℤ) ∧
    (∑ n ∈ Ico 109568 109824, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (10028859412355433945957175154 : ℤ) := by
  rcases cdemPrefixStats_109568_109696 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_109696_109824 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 109568 ≤ 109696) (by norm_num : 109696 ≤ 109824), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 109568 ≤ 109696) (by norm_num : 109696 ≤ 109824), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 109568 ≤ 109696) (by norm_num : 109696 ≤ 109824), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 109568 ≤ 109696) (by norm_num : 109696 ≤ 109824), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_109824_109888 :
    (∑ n ∈ Ico 109824 109888, mobiusTreeValue 16 mobiusTable1200001 n) = (-13 : ℤ) ∧
    (∑ n ∈ Ico 109824 109888, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 109824 109888, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-591731 : ℤ) ∧
    (∑ n ∈ Ico 109824 109888, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-11834833407589141257747945304 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_109888_109952 :
    (∑ n ∈ Ico 109888 109952, mobiusTreeValue 16 mobiusTable1200001 n) = (-4 : ℤ) ∧
    (∑ n ∈ Ico 109888 109952, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 109888 109952, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-181972 : ℤ) ∧
    (∑ n ∈ Ico 109888 109952, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-3639465824663574643232869955 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_109824_109952 :
    (∑ n ∈ Ico 109824 109952, mobiusTreeValue 16 mobiusTable1200001 n) = (-17 : ℤ) ∧
    (∑ n ∈ Ico 109824 109952, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (79 : ℕ) ∧
    (∑ n ∈ Ico 109824 109952, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-773703 : ℤ) ∧
    (∑ n ∈ Ico 109824 109952, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-15474299232252715900980815259 : ℤ) := by
  rcases cdemPrefixStats_109824_109888 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_109888_109952 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 109824 ≤ 109888) (by norm_num : 109888 ≤ 109952), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 109824 ≤ 109888) (by norm_num : 109888 ≤ 109952), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 109824 ≤ 109888) (by norm_num : 109888 ≤ 109952), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 109824 ≤ 109888) (by norm_num : 109888 ≤ 109952), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_109952_110016 :
    (∑ n ∈ Ico 109952 110016, mobiusTreeValue 16 mobiusTable1200001 n) = (2 : ℤ) ∧
    (∑ n ∈ Ico 109952 110016, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 109952 110016, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (90928 : ℤ) ∧
    (∑ n ∈ Ico 109952 110016, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1818628290684725830488608421 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_110016_110080 :
    (∑ n ∈ Ico 110016 110080, mobiusTreeValue 16 mobiusTable1200001 n) = (-6 : ℤ) ∧
    (∑ n ∈ Ico 110016 110080, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 110016 110080, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-272563 : ℤ) ∧
    (∑ n ∈ Ico 110016 110080, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-5451324062322439992780612503 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_109952_110080 :
    (∑ n ∈ Ico 109952 110080, mobiusTreeValue 16 mobiusTable1200001 n) = (-4 : ℤ) ∧
    (∑ n ∈ Ico 109952 110080, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 109952 110080, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-181635 : ℤ) ∧
    (∑ n ∈ Ico 109952 110080, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-3632695771637714162292004082 : ℤ) := by
  rcases cdemPrefixStats_109952_110016 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_110016_110080 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 109952 ≤ 110016) (by norm_num : 110016 ≤ 110080), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 109952 ≤ 110016) (by norm_num : 110016 ≤ 110080), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 109952 ≤ 110016) (by norm_num : 110016 ≤ 110080), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 109952 ≤ 110016) (by norm_num : 110016 ≤ 110080), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_109824_110080 :
    (∑ n ∈ Ico 109824 110080, mobiusTreeValue 16 mobiusTable1200001 n) = (-21 : ℤ) ∧
    (∑ n ∈ Ico 109824 110080, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (157 : ℕ) ∧
    (∑ n ∈ Ico 109824 110080, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-955338 : ℤ) ∧
    (∑ n ∈ Ico 109824 110080, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-19106995003890430063272819341 : ℤ) := by
  rcases cdemPrefixStats_109824_109952 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_109952_110080 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 109824 ≤ 109952) (by norm_num : 109952 ≤ 110080), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 109824 ≤ 109952) (by norm_num : 109952 ≤ 110080), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 109824 ≤ 109952) (by norm_num : 109952 ≤ 110080), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 109824 ≤ 109952) (by norm_num : 109952 ≤ 110080), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_109568_110080 :
    (∑ n ∈ Ico 109568 110080, mobiusTreeValue 16 mobiusTable1200001 n) = (-10 : ℤ) ∧
    (∑ n ∈ Ico 109568 110080, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (316 : ℕ) ∧
    (∑ n ∈ Ico 109568 110080, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-453900 : ℤ) ∧
    (∑ n ∈ Ico 109568 110080, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-9078135591534996117315644187 : ℤ) := by
  rcases cdemPrefixStats_109568_109824 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_109824_110080 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 109568 ≤ 109824) (by norm_num : 109824 ≤ 110080), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 109568 ≤ 109824) (by norm_num : 109824 ≤ 110080), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 109568 ≤ 109824) (by norm_num : 109824 ≤ 110080), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 109568 ≤ 109824) (by norm_num : 109824 ≤ 110080), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_110080_110144 :
    (∑ n ∈ Ico 110080 110144, mobiusTreeValue 16 mobiusTable1200001 n) = (18 : ℤ) ∧
    (∑ n ∈ Ico 110080 110144, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 110080 110144, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (817338 : ℤ) ∧
    (∑ n ∈ Ico 110080 110144, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (16346967828763241082510423408 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_110144_110208 :
    (∑ n ∈ Ico 110144 110208, mobiusTreeValue 16 mobiusTable1200001 n) = (11 : ℤ) ∧
    (∑ n ∈ Ico 110144 110208, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 110144 110208, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (499223 : ℤ) ∧
    (∑ n ∈ Ico 110144 110208, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (9984577953804802334670489901 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_110080_110208 :
    (∑ n ∈ Ico 110080 110208, mobiusTreeValue 16 mobiusTable1200001 n) = (29 : ℤ) ∧
    (∑ n ∈ Ico 110080 110208, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 110080 110208, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (1316561 : ℤ) ∧
    (∑ n ∈ Ico 110080 110208, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (26331545782568043417180913309 : ℤ) := by
  rcases cdemPrefixStats_110080_110144 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_110144_110208 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 110080 ≤ 110144) (by norm_num : 110144 ≤ 110208), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 110080 ≤ 110144) (by norm_num : 110144 ≤ 110208), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 110080 ≤ 110144) (by norm_num : 110144 ≤ 110208), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 110080 ≤ 110144) (by norm_num : 110144 ≤ 110208), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_110208_110272 :
    (∑ n ∈ Ico 110208 110272, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 110208 110272, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 110208 110272, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-45310 : ℤ) ∧
    (∑ n ∈ Ico 110208 110272, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-906214906170580954161299749 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_110272_110336 :
    (∑ n ∈ Ico 110272 110336, mobiusTreeValue 16 mobiusTable1200001 n) = (-3 : ℤ) ∧
    (∑ n ∈ Ico 110272 110336, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 110272 110336, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-136034 : ℤ) ∧
    (∑ n ∈ Ico 110272 110336, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-2720685209209524801372253928 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_110208_110336 :
    (∑ n ∈ Ico 110208 110336, mobiusTreeValue 16 mobiusTable1200001 n) = (-4 : ℤ) ∧
    (∑ n ∈ Ico 110208 110336, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (80 : ℕ) ∧
    (∑ n ∈ Ico 110208 110336, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-181344 : ℤ) ∧
    (∑ n ∈ Ico 110208 110336, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-3626900115380105755533553677 : ℤ) := by
  rcases cdemPrefixStats_110208_110272 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_110272_110336 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 110208 ≤ 110272) (by norm_num : 110272 ≤ 110336), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 110208 ≤ 110272) (by norm_num : 110272 ≤ 110336), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 110208 ≤ 110272) (by norm_num : 110272 ≤ 110336), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 110208 ≤ 110272) (by norm_num : 110272 ≤ 110336), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_110080_110336 :
    (∑ n ∈ Ico 110080 110336, mobiusTreeValue 16 mobiusTable1200001 n) = (25 : ℤ) ∧
    (∑ n ∈ Ico 110080 110336, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (157 : ℕ) ∧
    (∑ n ∈ Ico 110080 110336, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (1135217 : ℤ) ∧
    (∑ n ∈ Ico 110080 110336, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (22704645667187937661647359632 : ℤ) := by
  rcases cdemPrefixStats_110080_110208 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_110208_110336 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 110080 ≤ 110208) (by norm_num : 110208 ≤ 110336), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 110080 ≤ 110208) (by norm_num : 110208 ≤ 110336), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 110080 ≤ 110208) (by norm_num : 110208 ≤ 110336), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 110080 ≤ 110208) (by norm_num : 110208 ≤ 110336), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_110336_110400 :
    (∑ n ∈ Ico 110336 110400, mobiusTreeValue 16 mobiusTable1200001 n) = (2 : ℤ) ∧
    (∑ n ∈ Ico 110336 110400, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 110336 110400, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (90606 : ℤ) ∧
    (∑ n ∈ Ico 110336 110400, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1812119598297605797623671601 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_110400_110464 :
    (∑ n ∈ Ico 110400 110464, mobiusTreeValue 16 mobiusTable1200001 n) = (10 : ℤ) ∧
    (∑ n ∈ Ico 110400 110464, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 110400 110464, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (452834 : ℤ) ∧
    (∑ n ∈ Ico 110400 110464, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (9056781505292297572146662177 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_110336_110464 :
    (∑ n ∈ Ico 110336 110464, mobiusTreeValue 16 mobiusTable1200001 n) = (12 : ℤ) ∧
    (∑ n ∈ Ico 110336 110464, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 110336 110464, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (543440 : ℤ) ∧
    (∑ n ∈ Ico 110336 110464, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (10868901103589903369770333778 : ℤ) := by
  rcases cdemPrefixStats_110336_110400 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_110400_110464 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 110336 ≤ 110400) (by norm_num : 110400 ≤ 110464), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 110336 ≤ 110400) (by norm_num : 110400 ≤ 110464), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 110336 ≤ 110400) (by norm_num : 110400 ≤ 110464), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 110336 ≤ 110400) (by norm_num : 110400 ≤ 110464), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_110464_110528 :
    (∑ n ∈ Ico 110464 110528, mobiusTreeValue 16 mobiusTable1200001 n) = (-2 : ℤ) ∧
    (∑ n ∈ Ico 110464 110528, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 110464 110528, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-90580 : ℤ) ∧
    (∑ n ∈ Ico 110464 110528, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-1811633841389575652550573976 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_110528_110592 :
    (∑ n ∈ Ico 110528 110592, mobiusTreeValue 16 mobiusTable1200001 n) = (-13 : ℤ) ∧
    (∑ n ∈ Ico 110528 110592, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 110528 110592, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-587869 : ℤ) ∧
    (∑ n ∈ Ico 110528 110592, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-11757536182185181846828717104 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_110464_110592 :
    (∑ n ∈ Ico 110464 110592, mobiusTreeValue 16 mobiusTable1200001 n) = (-15 : ℤ) ∧
    (∑ n ∈ Ico 110464 110592, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 110464 110592, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-678449 : ℤ) ∧
    (∑ n ∈ Ico 110464 110592, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-13569170023574757499379291080 : ℤ) := by
  rcases cdemPrefixStats_110464_110528 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_110528_110592 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 110464 ≤ 110528) (by norm_num : 110528 ≤ 110592), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 110464 ≤ 110528) (by norm_num : 110528 ≤ 110592), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 110464 ≤ 110528) (by norm_num : 110528 ≤ 110592), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 110464 ≤ 110528) (by norm_num : 110528 ≤ 110592), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_110336_110592 :
    (∑ n ∈ Ico 110336 110592, mobiusTreeValue 16 mobiusTable1200001 n) = (-3 : ℤ) ∧
    (∑ n ∈ Ico 110336 110592, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (155 : ℕ) ∧
    (∑ n ∈ Ico 110336 110592, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-135009 : ℤ) ∧
    (∑ n ∈ Ico 110336 110592, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-2700268919984854129608957302 : ℤ) := by
  rcases cdemPrefixStats_110336_110464 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_110464_110592 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 110336 ≤ 110464) (by norm_num : 110464 ≤ 110592), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 110336 ≤ 110464) (by norm_num : 110464 ≤ 110592), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 110336 ≤ 110464) (by norm_num : 110464 ≤ 110592), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 110336 ≤ 110464) (by norm_num : 110464 ≤ 110592), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_110080_110592 :
    (∑ n ∈ Ico 110080 110592, mobiusTreeValue 16 mobiusTable1200001 n) = (22 : ℤ) ∧
    (∑ n ∈ Ico 110080 110592, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (312 : ℕ) ∧
    (∑ n ∈ Ico 110080 110592, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (1000208 : ℤ) ∧
    (∑ n ∈ Ico 110080 110592, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (20004376747203083532038402330 : ℤ) := by
  rcases cdemPrefixStats_110080_110336 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_110336_110592 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 110080 ≤ 110336) (by norm_num : 110336 ≤ 110592), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 110080 ≤ 110336) (by norm_num : 110336 ≤ 110592), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 110080 ≤ 110336) (by norm_num : 110336 ≤ 110592), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 110080 ≤ 110336) (by norm_num : 110336 ≤ 110592), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_109568_110592 :
    (∑ n ∈ Ico 109568 110592, mobiusTreeValue 16 mobiusTable1200001 n) = (12 : ℤ) ∧
    (∑ n ∈ Ico 109568 110592, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (628 : ℕ) ∧
    (∑ n ∈ Ico 109568 110592, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (546308 : ℤ) ∧
    (∑ n ∈ Ico 109568 110592, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (10926241155668087414722758143 : ℤ) := by
  rcases cdemPrefixStats_109568_110080 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_110080_110592 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 109568 ≤ 110080) (by norm_num : 110080 ≤ 110592), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 109568 ≤ 110080) (by norm_num : 110080 ≤ 110592), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 109568 ≤ 110080) (by norm_num : 110080 ≤ 110592), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 109568 ≤ 110080) (by norm_num : 110080 ≤ 110592), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_108544_110592 :
    (∑ n ∈ Ico 108544 110592, mobiusTreeValue 16 mobiusTable1200001 n) = (10 : ℤ) ∧
    (∑ n ∈ Ico 108544 110592, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (1244 : ℕ) ∧
    (∑ n ∈ Ico 108544 110592, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (458645 : ℤ) ∧
    (∑ n ∈ Ico 108544 110592, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (9172913273131900905250589658 : ℤ) := by
  rcases cdemPrefixStats_108544_109568 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_109568_110592 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 108544 ≤ 109568) (by norm_num : 109568 ≤ 110592), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 108544 ≤ 109568) (by norm_num : 109568 ≤ 110592), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 108544 ≤ 109568) (by norm_num : 109568 ≤ 110592), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 108544 ≤ 109568) (by norm_num : 109568 ≤ 110592), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_106496_110592 :
    (∑ n ∈ Ico 106496 110592, mobiusTreeValue 16 mobiusTable1200001 n) = (34 : ℤ) ∧
    (∑ n ∈ Ico 106496 110592, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (2492 : ℕ) ∧
    (∑ n ∈ Ico 106496 110592, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (1583822 : ℤ) ∧
    (∑ n ∈ Ico 106496 110592, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (31677009560696448723001105993 : ℤ) := by
  rcases cdemPrefixStats_106496_108544 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_108544_110592 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 106496 ≤ 108544) (by norm_num : 108544 ≤ 110592), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 106496 ≤ 108544) (by norm_num : 108544 ≤ 110592), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 106496 ≤ 108544) (by norm_num : 108544 ≤ 110592), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 106496 ≤ 108544) (by norm_num : 108544 ≤ 110592), hR1, hR2] <;> norm_num

theorem cdemPrefixGroup026_checked_complete :
    (∑ n ∈ Ico 106496 110592, mobiusTreeValue 16 mobiusTable1200001 n) = (34 : ℤ) ∧
    (∑ n ∈ Ico 106496 110592, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (2492 : ℕ) ∧
    (∑ n ∈ Ico 106496 110592, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (1583822 : ℤ) ∧
    (∑ n ∈ Ico 106496 110592, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (31677009560696448723001105993 : ℤ) := cdemPrefixStats_106496_110592
end Helfgott
#print axioms Helfgott.cdemPrefixGroup026_checked_complete

open Helfgott Finset
open scoped BigOperators

theorem solution :
    (∑ n ∈ Ico 106496 110592, mobiusTreeValue 16 mobiusTable1200001 n) = (34 : ℤ) ∧
    (∑ n ∈ Ico 106496 110592, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (2492 : ℕ) ∧
    (∑ n ∈ Ico 106496 110592, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (1583822 : ℤ) ∧
    (∑ n ∈ Ico 106496 110592, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (31677009560696448723001105993 : ℤ) := Helfgott.cdemPrefixGroup026_checked_complete
#print axioms solution
