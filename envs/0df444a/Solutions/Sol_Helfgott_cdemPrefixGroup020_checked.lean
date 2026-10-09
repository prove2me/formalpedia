-- Prove2me | solution 1 for Helfgott.cdemPrefixGroup020_checked
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-09T01:55:26.895437+00:00
-- url     : https://prove2.me/submissions/d6ba8aaa-7010-42a2-829b-a152e62d6e2e

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
private theorem cdemPrefixStats_81920_81984 :
    (∑ n ∈ Ico 81920 81984, mobiusTreeValue 16 mobiusTable1200001 n) = (-9 : ℤ) ∧
    (∑ n ∈ Ico 81920 81984, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 81920 81984, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-549053 : ℤ) ∧
    (∑ n ∈ Ico 81920 81984, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-10981160079697174591225375337 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_81984_82048 :
    (∑ n ∈ Ico 81984 82048, mobiusTreeValue 16 mobiusTable1200001 n) = (-2 : ℤ) ∧
    (∑ n ∈ Ico 81984 82048, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 81984 82048, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-121933 : ℤ) ∧
    (∑ n ∈ Ico 81984 82048, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-2438711784826258165316491277 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_81920_82048 :
    (∑ n ∈ Ico 81920 82048, mobiusTreeValue 16 mobiusTable1200001 n) = (-11 : ℤ) ∧
    (∑ n ∈ Ico 81920 82048, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 81920 82048, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-670986 : ℤ) ∧
    (∑ n ∈ Ico 81920 82048, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-13419871864523432756541866614 : ℤ) := by
  rcases cdemPrefixStats_81920_81984 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_81984_82048 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 81920 ≤ 81984) (by norm_num : 81984 ≤ 82048), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 81920 ≤ 81984) (by norm_num : 81984 ≤ 82048), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 81920 ≤ 81984) (by norm_num : 81984 ≤ 82048), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 81920 ≤ 81984) (by norm_num : 81984 ≤ 82048), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_82048_82112 :
    (∑ n ∈ Ico 82048 82112, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 82048 82112, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 82048 82112, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-145 : ℤ) ∧
    (∑ n ∈ Ico 82048 82112, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-2894030481625933121856095 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_82112_82176 :
    (∑ n ∈ Ico 82112 82176, mobiusTreeValue 16 mobiusTable1200001 n) = (-9 : ℤ) ∧
    (∑ n ∈ Ico 82112 82176, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 82112 82176, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-547788 : ℤ) ∧
    (∑ n ∈ Ico 82112 82176, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-10955836283360206621531419314 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_82048_82176 :
    (∑ n ∈ Ico 82048 82176, mobiusTreeValue 16 mobiusTable1200001 n) = (-9 : ℤ) ∧
    (∑ n ∈ Ico 82048 82176, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (79 : ℕ) ∧
    (∑ n ∈ Ico 82048 82176, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-547933 : ℤ) ∧
    (∑ n ∈ Ico 82048 82176, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-10958730313841832554653275409 : ℤ) := by
  rcases cdemPrefixStats_82048_82112 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_82112_82176 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 82048 ≤ 82112) (by norm_num : 82112 ≤ 82176), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 82048 ≤ 82112) (by norm_num : 82112 ≤ 82176), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 82048 ≤ 82112) (by norm_num : 82112 ≤ 82176), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 82048 ≤ 82112) (by norm_num : 82112 ≤ 82176), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_81920_82176 :
    (∑ n ∈ Ico 81920 82176, mobiusTreeValue 16 mobiusTable1200001 n) = (-20 : ℤ) ∧
    (∑ n ∈ Ico 81920 82176, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (156 : ℕ) ∧
    (∑ n ∈ Ico 81920 82176, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-1218919 : ℤ) ∧
    (∑ n ∈ Ico 81920 82176, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-24378602178365265311195142023 : ℤ) := by
  rcases cdemPrefixStats_81920_82048 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_82048_82176 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 81920 ≤ 82048) (by norm_num : 82048 ≤ 82176), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 81920 ≤ 82048) (by norm_num : 82048 ≤ 82176), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 81920 ≤ 82048) (by norm_num : 82048 ≤ 82176), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 81920 ≤ 82048) (by norm_num : 82048 ≤ 82176), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_82176_82240 :
    (∑ n ∈ Ico 82176 82240, mobiusTreeValue 16 mobiusTable1200001 n) = (-9 : ℤ) ∧
    (∑ n ∈ Ico 82176 82240, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 82176 82240, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-547487 : ℤ) ∧
    (∑ n ∈ Ico 82176 82240, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-10949867638914166310935592542 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_82240_82304 :
    (∑ n ∈ Ico 82240 82304, mobiusTreeValue 16 mobiusTable1200001 n) = (-3 : ℤ) ∧
    (∑ n ∈ Ico 82240 82304, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 82240 82304, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-182265 : ℤ) ∧
    (∑ n ∈ Ico 82240 82304, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-3645348463414403103919570827 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_82176_82304 :
    (∑ n ∈ Ico 82176 82304, mobiusTreeValue 16 mobiusTable1200001 n) = (-12 : ℤ) ∧
    (∑ n ∈ Ico 82176 82304, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (80 : ℕ) ∧
    (∑ n ∈ Ico 82176 82304, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-729752 : ℤ) ∧
    (∑ n ∈ Ico 82176 82304, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-14595216102328569414855163369 : ℤ) := by
  rcases cdemPrefixStats_82176_82240 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_82240_82304 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 82176 ≤ 82240) (by norm_num : 82240 ≤ 82304), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 82176 ≤ 82240) (by norm_num : 82240 ≤ 82304), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 82176 ≤ 82240) (by norm_num : 82240 ≤ 82304), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 82176 ≤ 82240) (by norm_num : 82240 ≤ 82304), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_82304_82368 :
    (∑ n ∈ Ico 82304 82368, mobiusTreeValue 16 mobiusTable1200001 n) = (-4 : ℤ) ∧
    (∑ n ∈ Ico 82304 82368, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 82304 82368, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-243043 : ℤ) ∧
    (∑ n ∈ Ico 82304 82368, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-4860856413013567715547372734 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_82368_82432 :
    (∑ n ∈ Ico 82368 82432, mobiusTreeValue 16 mobiusTable1200001 n) = (-5 : ℤ) ∧
    (∑ n ∈ Ico 82368 82432, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 82368 82432, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-303414 : ℤ) ∧
    (∑ n ∈ Ico 82368 82432, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-6068344308827172854966152183 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_82304_82432 :
    (∑ n ∈ Ico 82304 82432, mobiusTreeValue 16 mobiusTable1200001 n) = (-9 : ℤ) ∧
    (∑ n ∈ Ico 82304 82432, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 82304 82432, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-546457 : ℤ) ∧
    (∑ n ∈ Ico 82304 82432, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-10929200721840740570513524917 : ℤ) := by
  rcases cdemPrefixStats_82304_82368 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_82368_82432 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 82304 ≤ 82368) (by norm_num : 82368 ≤ 82432), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 82304 ≤ 82368) (by norm_num : 82368 ≤ 82432), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 82304 ≤ 82368) (by norm_num : 82368 ≤ 82432), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 82304 ≤ 82368) (by norm_num : 82368 ≤ 82432), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_82176_82432 :
    (∑ n ∈ Ico 82176 82432, mobiusTreeValue 16 mobiusTable1200001 n) = (-21 : ℤ) ∧
    (∑ n ∈ Ico 82176 82432, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (157 : ℕ) ∧
    (∑ n ∈ Ico 82176 82432, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-1276209 : ℤ) ∧
    (∑ n ∈ Ico 82176 82432, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-25524416824169309985368688286 : ℤ) := by
  rcases cdemPrefixStats_82176_82304 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_82304_82432 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 82176 ≤ 82304) (by norm_num : 82304 ≤ 82432), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 82176 ≤ 82304) (by norm_num : 82304 ≤ 82432), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 82176 ≤ 82304) (by norm_num : 82304 ≤ 82432), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 82176 ≤ 82304) (by norm_num : 82304 ≤ 82432), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_81920_82432 :
    (∑ n ∈ Ico 81920 82432, mobiusTreeValue 16 mobiusTable1200001 n) = (-41 : ℤ) ∧
    (∑ n ∈ Ico 81920 82432, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (313 : ℕ) ∧
    (∑ n ∈ Ico 81920 82432, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-2495128 : ℤ) ∧
    (∑ n ∈ Ico 81920 82432, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-49903019002534575296563830309 : ℤ) := by
  rcases cdemPrefixStats_81920_82176 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_82176_82432 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 81920 ≤ 82176) (by norm_num : 82176 ≤ 82432), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 81920 ≤ 82176) (by norm_num : 82176 ≤ 82432), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 81920 ≤ 82176) (by norm_num : 82176 ≤ 82432), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 81920 ≤ 82176) (by norm_num : 82176 ≤ 82432), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_82432_82496 :
    (∑ n ∈ Ico 82432 82496, mobiusTreeValue 16 mobiusTable1200001 n) = (11 : ℤ) ∧
    (∑ n ∈ Ico 82432 82496, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 82432 82496, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (667069 : ℤ) ∧
    (∑ n ∈ Ico 82432 82496, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (13341448438515349722486519478 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_82496_82560 :
    (∑ n ∈ Ico 82496 82560, mobiusTreeValue 16 mobiusTable1200001 n) = (-8 : ℤ) ∧
    (∑ n ∈ Ico 82496 82560, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 82496 82560, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-484647 : ℤ) ∧
    (∑ n ∈ Ico 82496 82560, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-9692990603407287258802365988 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_82432_82560 :
    (∑ n ∈ Ico 82432 82560, mobiusTreeValue 16 mobiusTable1200001 n) = (3 : ℤ) ∧
    (∑ n ∈ Ico 82432 82560, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (81 : ℕ) ∧
    (∑ n ∈ Ico 82432 82560, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (182422 : ℤ) ∧
    (∑ n ∈ Ico 82432 82560, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (3648457835108062463684153490 : ℤ) := by
  rcases cdemPrefixStats_82432_82496 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_82496_82560 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 82432 ≤ 82496) (by norm_num : 82496 ≤ 82560), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 82432 ≤ 82496) (by norm_num : 82496 ≤ 82560), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 82432 ≤ 82496) (by norm_num : 82496 ≤ 82560), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 82432 ≤ 82496) (by norm_num : 82496 ≤ 82560), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_82560_82624 :
    (∑ n ∈ Ico 82560 82624, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 82560 82624, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 82560 82624, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (60571 : ℤ) ∧
    (∑ n ∈ Ico 82560 82624, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1211445409708926472159902688 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_82624_82688 :
    (∑ n ∈ Ico 82624 82688, mobiusTreeValue 16 mobiusTable1200001 n) = (7 : ℤ) ∧
    (∑ n ∈ Ico 82624 82688, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (33 : ℕ) ∧
    (∑ n ∈ Ico 82624 82688, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (423427 : ℤ) ∧
    (∑ n ∈ Ico 82624 82688, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (8468601074128247828465619570 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_82560_82688 :
    (∑ n ∈ Ico 82560 82688, mobiusTreeValue 16 mobiusTable1200001 n) = (8 : ℤ) ∧
    (∑ n ∈ Ico 82560 82688, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (74 : ℕ) ∧
    (∑ n ∈ Ico 82560 82688, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (483998 : ℤ) ∧
    (∑ n ∈ Ico 82560 82688, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (9680046483837174300625522258 : ℤ) := by
  rcases cdemPrefixStats_82560_82624 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_82624_82688 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 82560 ≤ 82624) (by norm_num : 82624 ≤ 82688), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 82560 ≤ 82624) (by norm_num : 82624 ≤ 82688), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 82560 ≤ 82624) (by norm_num : 82624 ≤ 82688), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 82560 ≤ 82624) (by norm_num : 82624 ≤ 82688), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_82432_82688 :
    (∑ n ∈ Ico 82432 82688, mobiusTreeValue 16 mobiusTable1200001 n) = (11 : ℤ) ∧
    (∑ n ∈ Ico 82432 82688, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (155 : ℕ) ∧
    (∑ n ∈ Ico 82432 82688, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (666420 : ℤ) ∧
    (∑ n ∈ Ico 82432 82688, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (13328504318945236764309675748 : ℤ) := by
  rcases cdemPrefixStats_82432_82560 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_82560_82688 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 82432 ≤ 82560) (by norm_num : 82560 ≤ 82688), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 82432 ≤ 82560) (by norm_num : 82560 ≤ 82688), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 82432 ≤ 82560) (by norm_num : 82560 ≤ 82688), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 82432 ≤ 82560) (by norm_num : 82560 ≤ 82688), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_82688_82752 :
    (∑ n ∈ Ico 82688 82752, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 82688 82752, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 82688 82752, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-60502 : ℤ) ∧
    (∑ n ∈ Ico 82688 82752, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-1210124665521844186331528334 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_82752_82816 :
    (∑ n ∈ Ico 82752 82816, mobiusTreeValue 16 mobiusTable1200001 n) = (-2 : ℤ) ∧
    (∑ n ∈ Ico 82752 82816, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 82752 82816, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-120711 : ℤ) ∧
    (∑ n ∈ Ico 82752 82816, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-2414233361300207906652467489 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_82688_82816 :
    (∑ n ∈ Ico 82688 82816, mobiusTreeValue 16 mobiusTable1200001 n) = (-3 : ℤ) ∧
    (∑ n ∈ Ico 82688 82816, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (81 : ℕ) ∧
    (∑ n ∈ Ico 82688 82816, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-181213 : ℤ) ∧
    (∑ n ∈ Ico 82688 82816, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-3624358026822052092983995823 : ℤ) := by
  rcases cdemPrefixStats_82688_82752 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_82752_82816 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 82688 ≤ 82752) (by norm_num : 82752 ≤ 82816), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 82688 ≤ 82752) (by norm_num : 82752 ≤ 82816), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 82688 ≤ 82752) (by norm_num : 82752 ≤ 82816), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 82688 ≤ 82752) (by norm_num : 82752 ≤ 82816), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_82816_82880 :
    (∑ n ∈ Ico 82816 82880, mobiusTreeValue 16 mobiusTable1200001 n) = (3 : ℤ) ∧
    (∑ n ∈ Ico 82816 82880, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 82816 82880, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (181043 : ℤ) ∧
    (∑ n ∈ Ico 82816 82880, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (3620915207994430148800411132 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_82880_82944 :
    (∑ n ∈ Ico 82880 82944, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 82880 82944, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 82880 82944, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (60171 : ℤ) ∧
    (∑ n ∈ Ico 82880 82944, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1203494089299713266729415713 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_82816_82944 :
    (∑ n ∈ Ico 82816 82944, mobiusTreeValue 16 mobiusTable1200001 n) = (4 : ℤ) ∧
    (∑ n ∈ Ico 82816 82944, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 82816 82944, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (241214 : ℤ) ∧
    (∑ n ∈ Ico 82816 82944, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (4824409297294143415529826845 : ℤ) := by
  rcases cdemPrefixStats_82816_82880 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_82880_82944 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 82816 ≤ 82880) (by norm_num : 82880 ≤ 82944), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 82816 ≤ 82880) (by norm_num : 82880 ≤ 82944), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 82816 ≤ 82880) (by norm_num : 82880 ≤ 82944), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 82816 ≤ 82880) (by norm_num : 82880 ≤ 82944), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_82688_82944 :
    (∑ n ∈ Ico 82688 82944, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 82688 82944, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (159 : ℕ) ∧
    (∑ n ∈ Ico 82688 82944, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (60001 : ℤ) ∧
    (∑ n ∈ Ico 82688 82944, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1200051270472091322545831022 : ℤ) := by
  rcases cdemPrefixStats_82688_82816 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_82816_82944 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 82688 ≤ 82816) (by norm_num : 82816 ≤ 82944), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 82688 ≤ 82816) (by norm_num : 82816 ≤ 82944), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 82688 ≤ 82816) (by norm_num : 82816 ≤ 82944), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 82688 ≤ 82816) (by norm_num : 82816 ≤ 82944), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_82432_82944 :
    (∑ n ∈ Ico 82432 82944, mobiusTreeValue 16 mobiusTable1200001 n) = (12 : ℤ) ∧
    (∑ n ∈ Ico 82432 82944, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (314 : ℕ) ∧
    (∑ n ∈ Ico 82432 82944, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (726421 : ℤ) ∧
    (∑ n ∈ Ico 82432 82944, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (14528555589417328086855506770 : ℤ) := by
  rcases cdemPrefixStats_82432_82688 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_82688_82944 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 82432 ≤ 82688) (by norm_num : 82688 ≤ 82944), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 82432 ≤ 82688) (by norm_num : 82688 ≤ 82944), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 82432 ≤ 82688) (by norm_num : 82688 ≤ 82944), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 82432 ≤ 82688) (by norm_num : 82688 ≤ 82944), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_81920_82944 :
    (∑ n ∈ Ico 81920 82944, mobiusTreeValue 16 mobiusTable1200001 n) = (-29 : ℤ) ∧
    (∑ n ∈ Ico 81920 82944, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (627 : ℕ) ∧
    (∑ n ∈ Ico 81920 82944, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-1768707 : ℤ) ∧
    (∑ n ∈ Ico 81920 82944, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-35374463413117247209708323539 : ℤ) := by
  rcases cdemPrefixStats_81920_82432 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_82432_82944 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 81920 ≤ 82432) (by norm_num : 82432 ≤ 82944), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 81920 ≤ 82432) (by norm_num : 82432 ≤ 82944), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 81920 ≤ 82432) (by norm_num : 82432 ≤ 82944), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 81920 ≤ 82432) (by norm_num : 82432 ≤ 82944), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_82944_83008 :
    (∑ n ∈ Ico 82944 83008, mobiusTreeValue 16 mobiusTable1200001 n) = (-9 : ℤ) ∧
    (∑ n ∈ Ico 82944 83008, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 82944 83008, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-542242 : ℤ) ∧
    (∑ n ∈ Ico 82944 83008, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-10844985478704391937118114444 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_83008_83072 :
    (∑ n ∈ Ico 83008 83072, mobiusTreeValue 16 mobiusTable1200001 n) = (9 : ℤ) ∧
    (∑ n ∈ Ico 83008 83072, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 83008 83072, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (542024 : ℤ) ∧
    (∑ n ∈ Ico 83008 83072, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (10840601554634528759497610255 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_82944_83072 :
    (∑ n ∈ Ico 82944 83072, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 82944 83072, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (76 : ℕ) ∧
    (∑ n ∈ Ico 82944 83072, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-218 : ℤ) ∧
    (∑ n ∈ Ico 82944 83072, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-4383924069863177620504189 : ℤ) := by
  rcases cdemPrefixStats_82944_83008 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_83008_83072 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 82944 ≤ 83008) (by norm_num : 83008 ≤ 83072), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 82944 ≤ 83008) (by norm_num : 83008 ≤ 83072), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 82944 ≤ 83008) (by norm_num : 83008 ≤ 83072), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 82944 ≤ 83008) (by norm_num : 83008 ≤ 83072), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_83072_83136 :
    (∑ n ∈ Ico 83072 83136, mobiusTreeValue 16 mobiusTable1200001 n) = (6 : ℤ) ∧
    (∑ n ∈ Ico 83072 83136, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 83072 83136, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (361124 : ℤ) ∧
    (∑ n ∈ Ico 83072 83136, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (7222548072497982893503609804 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_83136_83200 :
    (∑ n ∈ Ico 83136 83200, mobiusTreeValue 16 mobiusTable1200001 n) = (7 : ℤ) ∧
    (∑ n ∈ Ico 83136 83200, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 83136 83200, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (420756 : ℤ) ∧
    (∑ n ∈ Ico 83136 83200, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (8415166346416336695025233158 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_83072_83200 :
    (∑ n ∈ Ico 83072 83200, mobiusTreeValue 16 mobiusTable1200001 n) = (13 : ℤ) ∧
    (∑ n ∈ Ico 83072 83200, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (79 : ℕ) ∧
    (∑ n ∈ Ico 83072 83200, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (781880 : ℤ) ∧
    (∑ n ∈ Ico 83072 83200, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (15637714418914319588528842962 : ℤ) := by
  rcases cdemPrefixStats_83072_83136 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_83136_83200 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 83072 ≤ 83136) (by norm_num : 83136 ≤ 83200), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 83072 ≤ 83136) (by norm_num : 83136 ≤ 83200), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 83072 ≤ 83136) (by norm_num : 83136 ≤ 83200), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 83072 ≤ 83136) (by norm_num : 83136 ≤ 83200), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_82944_83200 :
    (∑ n ∈ Ico 82944 83200, mobiusTreeValue 16 mobiusTable1200001 n) = (13 : ℤ) ∧
    (∑ n ∈ Ico 82944 83200, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (155 : ℕ) ∧
    (∑ n ∈ Ico 82944 83200, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (781662 : ℤ) ∧
    (∑ n ∈ Ico 82944 83200, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (15633330494844456410908338773 : ℤ) := by
  rcases cdemPrefixStats_82944_83072 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_83072_83200 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 82944 ≤ 83072) (by norm_num : 83072 ≤ 83200), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 82944 ≤ 83072) (by norm_num : 83072 ≤ 83200), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 82944 ≤ 83072) (by norm_num : 83072 ≤ 83200), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 82944 ≤ 83072) (by norm_num : 83072 ≤ 83200), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_83200_83264 :
    (∑ n ∈ Ico 83200 83264, mobiusTreeValue 16 mobiusTable1200001 n) = (3 : ℤ) ∧
    (∑ n ∈ Ico 83200 83264, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 83200 83264, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (180161 : ℤ) ∧
    (∑ n ∈ Ico 83200 83264, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (3603228478581301233536931482 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_83264_83328 :
    (∑ n ∈ Ico 83264 83328, mobiusTreeValue 16 mobiusTable1200001 n) = (4 : ℤ) ∧
    (∑ n ∈ Ico 83264 83328, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 83264 83328, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (239971 : ℤ) ∧
    (∑ n ∈ Ico 83264 83328, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (4799470594274173621087720788 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_83200_83328 :
    (∑ n ∈ Ico 83200 83328, mobiusTreeValue 16 mobiusTable1200001 n) = (7 : ℤ) ∧
    (∑ n ∈ Ico 83200 83328, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (79 : ℕ) ∧
    (∑ n ∈ Ico 83200 83328, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (420132 : ℤ) ∧
    (∑ n ∈ Ico 83200 83328, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (8402699072855474854624652270 : ℤ) := by
  rcases cdemPrefixStats_83200_83264 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_83264_83328 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 83200 ≤ 83264) (by norm_num : 83264 ≤ 83328), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 83200 ≤ 83264) (by norm_num : 83264 ≤ 83328), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 83200 ≤ 83264) (by norm_num : 83264 ≤ 83328), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 83200 ≤ 83264) (by norm_num : 83264 ≤ 83328), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_83328_83392 :
    (∑ n ∈ Ico 83328 83392, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 83328 83392, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 83328 83392, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (59961 : ℤ) ∧
    (∑ n ∈ Ico 83328 83392, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1199199071944136214643273829 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_83392_83456 :
    (∑ n ∈ Ico 83392 83456, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 83392 83456, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 83392 83456, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-59978 : ℤ) ∧
    (∑ n ∈ Ico 83392 83456, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-1199600809673994014129422016 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_83328_83456 :
    (∑ n ∈ Ico 83328 83456, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 83328 83456, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 83328 83456, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-17 : ℤ) ∧
    (∑ n ∈ Ico 83328 83456, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-401737729857799486148187 : ℤ) := by
  rcases cdemPrefixStats_83328_83392 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_83392_83456 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 83328 ≤ 83392) (by norm_num : 83392 ≤ 83456), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 83328 ≤ 83392) (by norm_num : 83392 ≤ 83456), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 83328 ≤ 83392) (by norm_num : 83392 ≤ 83456), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 83328 ≤ 83392) (by norm_num : 83392 ≤ 83456), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_83200_83456 :
    (∑ n ∈ Ico 83200 83456, mobiusTreeValue 16 mobiusTable1200001 n) = (7 : ℤ) ∧
    (∑ n ∈ Ico 83200 83456, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (157 : ℕ) ∧
    (∑ n ∈ Ico 83200 83456, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (420115 : ℤ) ∧
    (∑ n ∈ Ico 83200 83456, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (8402297335125617055138504083 : ℤ) := by
  rcases cdemPrefixStats_83200_83328 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_83328_83456 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 83200 ≤ 83328) (by norm_num : 83328 ≤ 83456), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 83200 ≤ 83328) (by norm_num : 83328 ≤ 83456), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 83200 ≤ 83328) (by norm_num : 83328 ≤ 83456), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 83200 ≤ 83328) (by norm_num : 83328 ≤ 83456), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_82944_83456 :
    (∑ n ∈ Ico 82944 83456, mobiusTreeValue 16 mobiusTable1200001 n) = (20 : ℤ) ∧
    (∑ n ∈ Ico 82944 83456, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (312 : ℕ) ∧
    (∑ n ∈ Ico 82944 83456, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (1201777 : ℤ) ∧
    (∑ n ∈ Ico 82944 83456, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (24035627829970073466046842856 : ℤ) := by
  rcases cdemPrefixStats_82944_83200 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_83200_83456 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 82944 ≤ 83200) (by norm_num : 83200 ≤ 83456), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 82944 ≤ 83200) (by norm_num : 83200 ≤ 83456), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 82944 ≤ 83200) (by norm_num : 83200 ≤ 83456), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 82944 ≤ 83200) (by norm_num : 83200 ≤ 83456), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_83456_83520 :
    (∑ n ∈ Ico 83456 83520, mobiusTreeValue 16 mobiusTable1200001 n) = (9 : ℤ) ∧
    (∑ n ∈ Ico 83456 83520, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 83456 83520, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (538889 : ℤ) ∧
    (∑ n ∈ Ico 83456 83520, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (10777826938160261656697260198 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_83520_83584 :
    (∑ n ∈ Ico 83520 83584, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 83520 83584, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (36 : ℕ) ∧
    (∑ n ∈ Ico 83520 83584, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (24 : ℤ) ∧
    (∑ n ∈ Ico 83520 83584, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (515508773684806658822417 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_83456_83584 :
    (∑ n ∈ Ico 83456 83584, mobiusTreeValue 16 mobiusTable1200001 n) = (9 : ℤ) ∧
    (∑ n ∈ Ico 83456 83584, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (75 : ℕ) ∧
    (∑ n ∈ Ico 83456 83584, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (538913 : ℤ) ∧
    (∑ n ∈ Ico 83456 83584, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (10778342446933946463356082615 : ℤ) := by
  rcases cdemPrefixStats_83456_83520 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_83520_83584 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 83456 ≤ 83520) (by norm_num : 83520 ≤ 83584), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 83456 ≤ 83520) (by norm_num : 83520 ≤ 83584), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 83456 ≤ 83520) (by norm_num : 83520 ≤ 83584), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 83456 ≤ 83520) (by norm_num : 83520 ≤ 83584), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_83584_83648 :
    (∑ n ∈ Ico 83584 83648, mobiusTreeValue 16 mobiusTable1200001 n) = (-8 : ℤ) ∧
    (∑ n ∈ Ico 83584 83648, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 83584 83648, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-478412 : ℤ) ∧
    (∑ n ∈ Ico 83584 83648, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-9568333616588395539301232186 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_83648_83712 :
    (∑ n ∈ Ico 83648 83712, mobiusTreeValue 16 mobiusTable1200001 n) = (8 : ℤ) ∧
    (∑ n ∈ Ico 83648 83712, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 83648 83712, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (477975 : ℤ) ∧
    (∑ n ∈ Ico 83648 83712, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (9559601625592815705592115474 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_83584_83712 :
    (∑ n ∈ Ico 83584 83712, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 83584 83712, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 83584 83712, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-437 : ℤ) ∧
    (∑ n ∈ Ico 83584 83712, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-8731990995579833709116712 : ℤ) := by
  rcases cdemPrefixStats_83584_83648 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_83648_83712 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 83584 ≤ 83648) (by norm_num : 83648 ≤ 83712), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 83584 ≤ 83648) (by norm_num : 83648 ≤ 83712), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 83584 ≤ 83648) (by norm_num : 83648 ≤ 83712), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 83584 ≤ 83648) (by norm_num : 83648 ≤ 83712), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_83456_83712 :
    (∑ n ∈ Ico 83456 83712, mobiusTreeValue 16 mobiusTable1200001 n) = (9 : ℤ) ∧
    (∑ n ∈ Ico 83456 83712, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (153 : ℕ) ∧
    (∑ n ∈ Ico 83456 83712, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (538476 : ℤ) ∧
    (∑ n ∈ Ico 83456 83712, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (10769610455938366629646965903 : ℤ) := by
  rcases cdemPrefixStats_83456_83584 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_83584_83712 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 83456 ≤ 83584) (by norm_num : 83584 ≤ 83712), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 83456 ≤ 83584) (by norm_num : 83584 ≤ 83712), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 83456 ≤ 83584) (by norm_num : 83584 ≤ 83712), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 83456 ≤ 83584) (by norm_num : 83584 ≤ 83712), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_83712_83776 :
    (∑ n ∈ Ico 83712 83776, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 83712 83776, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 83712 83776, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (59664 : ℤ) ∧
    (∑ n ∈ Ico 83712 83776, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1193316751842822092304171222 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_83776_83840 :
    (∑ n ∈ Ico 83776 83840, mobiusTreeValue 16 mobiusTable1200001 n) = (15 : ℤ) ∧
    (∑ n ∈ Ico 83776 83840, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 83776 83840, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (894805 : ℤ) ∧
    (∑ n ∈ Ico 83776 83840, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (17896287653498821157529472315 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_83712_83840 :
    (∑ n ∈ Ico 83712 83840, mobiusTreeValue 16 mobiusTable1200001 n) = (16 : ℤ) ∧
    (∑ n ∈ Ico 83712 83840, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 83712 83840, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (954469 : ℤ) ∧
    (∑ n ∈ Ico 83712 83840, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (19089604405341643249833643537 : ℤ) := by
  rcases cdemPrefixStats_83712_83776 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_83776_83840 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 83712 ≤ 83776) (by norm_num : 83776 ≤ 83840), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 83712 ≤ 83776) (by norm_num : 83776 ≤ 83840), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 83712 ≤ 83776) (by norm_num : 83776 ≤ 83840), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 83712 ≤ 83776) (by norm_num : 83776 ≤ 83840), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_83840_83904 :
    (∑ n ∈ Ico 83840 83904, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 83840 83904, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 83840 83904, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-59590 : ℤ) ∧
    (∑ n ∈ Ico 83840 83904, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-1191837811078516227481560774 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_83904_83968 :
    (∑ n ∈ Ico 83904 83968, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 83904 83968, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 83904 83968, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-53 : ℤ) ∧
    (∑ n ∈ Ico 83904 83968, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-1007583352095861125689883 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_83840_83968 :
    (∑ n ∈ Ico 83840 83968, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 83840 83968, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (81 : ℕ) ∧
    (∑ n ∈ Ico 83840 83968, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-59643 : ℤ) ∧
    (∑ n ∈ Ico 83840 83968, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-1192845394430612088607250657 : ℤ) := by
  rcases cdemPrefixStats_83840_83904 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_83904_83968 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 83840 ≤ 83904) (by norm_num : 83904 ≤ 83968), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 83840 ≤ 83904) (by norm_num : 83904 ≤ 83968), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 83840 ≤ 83904) (by norm_num : 83904 ≤ 83968), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 83840 ≤ 83904) (by norm_num : 83904 ≤ 83968), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_83712_83968 :
    (∑ n ∈ Ico 83712 83968, mobiusTreeValue 16 mobiusTable1200001 n) = (15 : ℤ) ∧
    (∑ n ∈ Ico 83712 83968, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (159 : ℕ) ∧
    (∑ n ∈ Ico 83712 83968, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (894826 : ℤ) ∧
    (∑ n ∈ Ico 83712 83968, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (17896759010911031161226392880 : ℤ) := by
  rcases cdemPrefixStats_83712_83840 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_83840_83968 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 83712 ≤ 83840) (by norm_num : 83840 ≤ 83968), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 83712 ≤ 83840) (by norm_num : 83840 ≤ 83968), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 83712 ≤ 83840) (by norm_num : 83840 ≤ 83968), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 83712 ≤ 83840) (by norm_num : 83840 ≤ 83968), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_83456_83968 :
    (∑ n ∈ Ico 83456 83968, mobiusTreeValue 16 mobiusTable1200001 n) = (24 : ℤ) ∧
    (∑ n ∈ Ico 83456 83968, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (312 : ℕ) ∧
    (∑ n ∈ Ico 83456 83968, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (1433302 : ℤ) ∧
    (∑ n ∈ Ico 83456 83968, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (28666369466849397790873358783 : ℤ) := by
  rcases cdemPrefixStats_83456_83712 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_83712_83968 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 83456 ≤ 83712) (by norm_num : 83712 ≤ 83968), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 83456 ≤ 83712) (by norm_num : 83712 ≤ 83968), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 83456 ≤ 83712) (by norm_num : 83712 ≤ 83968), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 83456 ≤ 83712) (by norm_num : 83712 ≤ 83968), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_82944_83968 :
    (∑ n ∈ Ico 82944 83968, mobiusTreeValue 16 mobiusTable1200001 n) = (44 : ℤ) ∧
    (∑ n ∈ Ico 82944 83968, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (624 : ℕ) ∧
    (∑ n ∈ Ico 82944 83968, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (2635079 : ℤ) ∧
    (∑ n ∈ Ico 82944 83968, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (52701997296819471256920201639 : ℤ) := by
  rcases cdemPrefixStats_82944_83456 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_83456_83968 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 82944 ≤ 83456) (by norm_num : 83456 ≤ 83968), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 82944 ≤ 83456) (by norm_num : 83456 ≤ 83968), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 82944 ≤ 83456) (by norm_num : 83456 ≤ 83968), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 82944 ≤ 83456) (by norm_num : 83456 ≤ 83968), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_81920_83968 :
    (∑ n ∈ Ico 81920 83968, mobiusTreeValue 16 mobiusTable1200001 n) = (15 : ℤ) ∧
    (∑ n ∈ Ico 81920 83968, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (1251 : ℕ) ∧
    (∑ n ∈ Ico 81920 83968, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (866372 : ℤ) ∧
    (∑ n ∈ Ico 81920 83968, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (17327533883702224047211878100 : ℤ) := by
  rcases cdemPrefixStats_81920_82944 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_82944_83968 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 81920 ≤ 82944) (by norm_num : 82944 ≤ 83968), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 81920 ≤ 82944) (by norm_num : 82944 ≤ 83968), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 81920 ≤ 82944) (by norm_num : 82944 ≤ 83968), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 81920 ≤ 82944) (by norm_num : 82944 ≤ 83968), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_83968_84032 :
    (∑ n ∈ Ico 83968 84032, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 83968 84032, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 83968 84032, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-30 : ℤ) ∧
    (∑ n ∈ Ico 83968 84032, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-595116780148229393776421 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_84032_84096 :
    (∑ n ∈ Ico 84032 84096, mobiusTreeValue 16 mobiusTable1200001 n) = (4 : ℤ) ∧
    (∑ n ∈ Ico 84032 84096, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 84032 84096, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (237990 : ℤ) ∧
    (∑ n ∈ Ico 84032 84096, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (4759878974475238449803144236 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_83968_84096 :
    (∑ n ∈ Ico 83968 84096, mobiusTreeValue 16 mobiusTable1200001 n) = (4 : ℤ) ∧
    (∑ n ∈ Ico 83968 84096, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (76 : ℕ) ∧
    (∑ n ∈ Ico 83968 84096, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (237960 : ℤ) ∧
    (∑ n ∈ Ico 83968 84096, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (4759283857695090220409367815 : ℤ) := by
  rcases cdemPrefixStats_83968_84032 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_84032_84096 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 83968 ≤ 84032) (by norm_num : 84032 ≤ 84096), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 83968 ≤ 84032) (by norm_num : 84032 ≤ 84096), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 83968 ≤ 84032) (by norm_num : 84032 ≤ 84096), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 83968 ≤ 84032) (by norm_num : 84032 ≤ 84096), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_84096_84160 :
    (∑ n ∈ Ico 84096 84160, mobiusTreeValue 16 mobiusTable1200001 n) = (7 : ℤ) ∧
    (∑ n ∈ Ico 84096 84160, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 84096 84160, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (416056 : ℤ) ∧
    (∑ n ∈ Ico 84096 84160, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (8321177621619548412790759953 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_84160_84224 :
    (∑ n ∈ Ico 84160 84224, mobiusTreeValue 16 mobiusTable1200001 n) = (-2 : ℤ) ∧
    (∑ n ∈ Ico 84160 84224, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 84160 84224, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-118644 : ℤ) ∧
    (∑ n ∈ Ico 84160 84224, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-2372898875627945091516843519 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_84096_84224 :
    (∑ n ∈ Ico 84096 84224, mobiusTreeValue 16 mobiusTable1200001 n) = (5 : ℤ) ∧
    (∑ n ∈ Ico 84096 84224, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 84096 84224, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (297412 : ℤ) ∧
    (∑ n ∈ Ico 84096 84224, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (5948278745991603321273916434 : ℤ) := by
  rcases cdemPrefixStats_84096_84160 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_84160_84224 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 84096 ≤ 84160) (by norm_num : 84160 ≤ 84224), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 84096 ≤ 84160) (by norm_num : 84160 ≤ 84224), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 84096 ≤ 84160) (by norm_num : 84160 ≤ 84224), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 84096 ≤ 84160) (by norm_num : 84160 ≤ 84224), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_83968_84224 :
    (∑ n ∈ Ico 83968 84224, mobiusTreeValue 16 mobiusTable1200001 n) = (9 : ℤ) ∧
    (∑ n ∈ Ico 83968 84224, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (153 : ℕ) ∧
    (∑ n ∈ Ico 83968 84224, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (535372 : ℤ) ∧
    (∑ n ∈ Ico 83968 84224, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (10707562603686693541683284249 : ℤ) := by
  rcases cdemPrefixStats_83968_84096 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_84096_84224 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 83968 ≤ 84096) (by norm_num : 84096 ≤ 84224), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 83968 ≤ 84096) (by norm_num : 84096 ≤ 84224), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 83968 ≤ 84096) (by norm_num : 84096 ≤ 84224), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 83968 ≤ 84096) (by norm_num : 84096 ≤ 84224), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_84224_84288 :
    (∑ n ∈ Ico 84224 84288, mobiusTreeValue 16 mobiusTable1200001 n) = (9 : ℤ) ∧
    (∑ n ∈ Ico 84224 84288, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 84224 84288, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (533979 : ℤ) ∧
    (∑ n ∈ Ico 84224 84288, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (10679675727927873160056283570 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_84288_84352 :
    (∑ n ∈ Ico 84288 84352, mobiusTreeValue 16 mobiusTable1200001 n) = (-16 : ℤ) ∧
    (∑ n ∈ Ico 84288 84352, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 84288 84352, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-948724 : ℤ) ∧
    (∑ n ∈ Ico 84288 84352, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-18974643842242695293797003599 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_84224_84352 :
    (∑ n ∈ Ico 84224 84352, mobiusTreeValue 16 mobiusTable1200001 n) = (-7 : ℤ) ∧
    (∑ n ∈ Ico 84224 84352, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 84224 84352, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-414745 : ℤ) ∧
    (∑ n ∈ Ico 84224 84352, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-8294968114314822133740720029 : ℤ) := by
  rcases cdemPrefixStats_84224_84288 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_84288_84352 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 84224 ≤ 84288) (by norm_num : 84288 ≤ 84352), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 84224 ≤ 84288) (by norm_num : 84288 ≤ 84352), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 84224 ≤ 84288) (by norm_num : 84288 ≤ 84352), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 84224 ≤ 84288) (by norm_num : 84288 ≤ 84352), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_84352_84416 :
    (∑ n ∈ Ico 84352 84416, mobiusTreeValue 16 mobiusTable1200001 n) = (3 : ℤ) ∧
    (∑ n ∈ Ico 84352 84416, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 84352 84416, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (177875 : ℤ) ∧
    (∑ n ∈ Ico 84352 84416, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (3557564583748902825425951172 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_84416_84480 :
    (∑ n ∈ Ico 84416 84480, mobiusTreeValue 16 mobiusTable1200001 n) = (-4 : ℤ) ∧
    (∑ n ∈ Ico 84416 84480, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 84416 84480, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-236835 : ℤ) ∧
    (∑ n ∈ Ico 84416 84480, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-4736839467085495988349755079 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_84352_84480 :
    (∑ n ∈ Ico 84352 84480, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 84352 84480, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (79 : ℕ) ∧
    (∑ n ∈ Ico 84352 84480, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-58960 : ℤ) ∧
    (∑ n ∈ Ico 84352 84480, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-1179274883336593162923803907 : ℤ) := by
  rcases cdemPrefixStats_84352_84416 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_84416_84480 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 84352 ≤ 84416) (by norm_num : 84416 ≤ 84480), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 84352 ≤ 84416) (by norm_num : 84416 ≤ 84480), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 84352 ≤ 84416) (by norm_num : 84416 ≤ 84480), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 84352 ≤ 84416) (by norm_num : 84416 ≤ 84480), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_84224_84480 :
    (∑ n ∈ Ico 84224 84480, mobiusTreeValue 16 mobiusTable1200001 n) = (-8 : ℤ) ∧
    (∑ n ∈ Ico 84224 84480, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (156 : ℕ) ∧
    (∑ n ∈ Ico 84224 84480, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-473705 : ℤ) ∧
    (∑ n ∈ Ico 84224 84480, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-9474242997651415296664523936 : ℤ) := by
  rcases cdemPrefixStats_84224_84352 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_84352_84480 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 84224 ≤ 84352) (by norm_num : 84352 ≤ 84480), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 84224 ≤ 84352) (by norm_num : 84352 ≤ 84480), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 84224 ≤ 84352) (by norm_num : 84352 ≤ 84480), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 84224 ≤ 84352) (by norm_num : 84352 ≤ 84480), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_83968_84480 :
    (∑ n ∈ Ico 83968 84480, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 83968 84480, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (309 : ℕ) ∧
    (∑ n ∈ Ico 83968 84480, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (61667 : ℤ) ∧
    (∑ n ∈ Ico 83968 84480, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1233319606035278245018760313 : ℤ) := by
  rcases cdemPrefixStats_83968_84224 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_84224_84480 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 83968 ≤ 84224) (by norm_num : 84224 ≤ 84480), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 83968 ≤ 84224) (by norm_num : 84224 ≤ 84480), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 83968 ≤ 84224) (by norm_num : 84224 ≤ 84480), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 83968 ≤ 84224) (by norm_num : 84224 ≤ 84480), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_84480_84544 :
    (∑ n ∈ Ico 84480 84544, mobiusTreeValue 16 mobiusTable1200001 n) = (-2 : ℤ) ∧
    (∑ n ∈ Ico 84480 84544, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (42 : ℕ) ∧
    (∑ n ∈ Ico 84480 84544, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-118392 : ℤ) ∧
    (∑ n ∈ Ico 84480 84544, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-2367886453730210741732770016 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_84544_84608 :
    (∑ n ∈ Ico 84544 84608, mobiusTreeValue 16 mobiusTable1200001 n) = (7 : ℤ) ∧
    (∑ n ∈ Ico 84544 84608, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 84544 84608, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (413746 : ℤ) ∧
    (∑ n ∈ Ico 84544 84608, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (8275000237598067137774982407 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_84480_84608 :
    (∑ n ∈ Ico 84480 84608, mobiusTreeValue 16 mobiusTable1200001 n) = (5 : ℤ) ∧
    (∑ n ∈ Ico 84480 84608, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (81 : ℕ) ∧
    (∑ n ∈ Ico 84480 84608, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (295354 : ℤ) ∧
    (∑ n ∈ Ico 84480 84608, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (5907113783867856396042212391 : ℤ) := by
  rcases cdemPrefixStats_84480_84544 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_84544_84608 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 84480 ≤ 84544) (by norm_num : 84544 ≤ 84608), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 84480 ≤ 84544) (by norm_num : 84544 ≤ 84608), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 84480 ≤ 84544) (by norm_num : 84544 ≤ 84608), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 84480 ≤ 84544) (by norm_num : 84544 ≤ 84608), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_84608_84672 :
    (∑ n ∈ Ico 84608 84672, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 84608 84672, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 84608 84672, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-47 : ℤ) ∧
    (∑ n ∈ Ico 84608 84672, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-962928200022353356458905 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_84672_84736 :
    (∑ n ∈ Ico 84672 84736, mobiusTreeValue 16 mobiusTable1200001 n) = (6 : ℤ) ∧
    (∑ n ∈ Ico 84672 84736, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 84672 84736, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (354268 : ℤ) ∧
    (∑ n ∈ Ico 84672 84736, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (7085414420154953340781031747 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_84608_84736 :
    (∑ n ∈ Ico 84608 84736, mobiusTreeValue 16 mobiusTable1200001 n) = (6 : ℤ) ∧
    (∑ n ∈ Ico 84608 84736, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (76 : ℕ) ∧
    (∑ n ∈ Ico 84608 84736, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (354221 : ℤ) ∧
    (∑ n ∈ Ico 84608 84736, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (7084451491954930987424572842 : ℤ) := by
  rcases cdemPrefixStats_84608_84672 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_84672_84736 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 84608 ≤ 84672) (by norm_num : 84672 ≤ 84736), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 84608 ≤ 84672) (by norm_num : 84672 ≤ 84736), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 84608 ≤ 84672) (by norm_num : 84672 ≤ 84736), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 84608 ≤ 84672) (by norm_num : 84672 ≤ 84736), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_84480_84736 :
    (∑ n ∈ Ico 84480 84736, mobiusTreeValue 16 mobiusTable1200001 n) = (11 : ℤ) ∧
    (∑ n ∈ Ico 84480 84736, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (157 : ℕ) ∧
    (∑ n ∈ Ico 84480 84736, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (649575 : ℤ) ∧
    (∑ n ∈ Ico 84480 84736, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (12991565275822787383466785233 : ℤ) := by
  rcases cdemPrefixStats_84480_84608 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_84608_84736 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 84480 ≤ 84608) (by norm_num : 84608 ≤ 84736), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 84480 ≤ 84608) (by norm_num : 84608 ≤ 84736), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 84480 ≤ 84608) (by norm_num : 84608 ≤ 84736), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 84480 ≤ 84608) (by norm_num : 84608 ≤ 84736), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_84736_84800 :
    (∑ n ∈ Ico 84736 84800, mobiusTreeValue 16 mobiusTable1200001 n) = (6 : ℤ) ∧
    (∑ n ∈ Ico 84736 84800, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 84736 84800, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (353885 : ℤ) ∧
    (∑ n ∈ Ico 84736 84800, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (7077753181570601125377210988 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_84800_84864 :
    (∑ n ∈ Ico 84800 84864, mobiusTreeValue 16 mobiusTable1200001 n) = (4 : ℤ) ∧
    (∑ n ∈ Ico 84800 84864, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 84800 84864, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (235792 : ℤ) ∧
    (∑ n ∈ Ico 84800 84864, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (4715854261277019687891609545 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_84736_84864 :
    (∑ n ∈ Ico 84736 84864, mobiusTreeValue 16 mobiusTable1200001 n) = (10 : ℤ) ∧
    (∑ n ∈ Ico 84736 84864, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 84736 84864, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (589677 : ℤ) ∧
    (∑ n ∈ Ico 84736 84864, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (11793607442847620813268820533 : ℤ) := by
  rcases cdemPrefixStats_84736_84800 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_84800_84864 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 84736 ≤ 84800) (by norm_num : 84800 ≤ 84864), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 84736 ≤ 84800) (by norm_num : 84800 ≤ 84864), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 84736 ≤ 84800) (by norm_num : 84800 ≤ 84864), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 84736 ≤ 84800) (by norm_num : 84800 ≤ 84864), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_84864_84928 :
    (∑ n ∈ Ico 84864 84928, mobiusTreeValue 16 mobiusTable1200001 n) = (15 : ℤ) ∧
    (∑ n ∈ Ico 84864 84928, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 84864 84928, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (883336 : ℤ) ∧
    (∑ n ∈ Ico 84864 84928, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (17666901554757153977578310000 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_84928_84992 :
    (∑ n ∈ Ico 84928 84992, mobiusTreeValue 16 mobiusTable1200001 n) = (-6 : ℤ) ∧
    (∑ n ∈ Ico 84928 84992, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 84928 84992, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-353117 : ℤ) ∧
    (∑ n ∈ Ico 84928 84992, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-7062424259334862799211925848 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_84864_84992 :
    (∑ n ∈ Ico 84864 84992, mobiusTreeValue 16 mobiusTable1200001 n) = (9 : ℤ) ∧
    (∑ n ∈ Ico 84864 84992, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 84864 84992, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (530219 : ℤ) ∧
    (∑ n ∈ Ico 84864 84992, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (10604477295422291178366384152 : ℤ) := by
  rcases cdemPrefixStats_84864_84928 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_84928_84992 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 84864 ≤ 84928) (by norm_num : 84928 ≤ 84992), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 84864 ≤ 84928) (by norm_num : 84928 ≤ 84992), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 84864 ≤ 84928) (by norm_num : 84928 ≤ 84992), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 84864 ≤ 84928) (by norm_num : 84928 ≤ 84992), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_84736_84992 :
    (∑ n ∈ Ico 84736 84992, mobiusTreeValue 16 mobiusTable1200001 n) = (19 : ℤ) ∧
    (∑ n ∈ Ico 84736 84992, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (155 : ℕ) ∧
    (∑ n ∈ Ico 84736 84992, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (1119896 : ℤ) ∧
    (∑ n ∈ Ico 84736 84992, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (22398084738269911991635204685 : ℤ) := by
  rcases cdemPrefixStats_84736_84864 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_84864_84992 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 84736 ≤ 84864) (by norm_num : 84864 ≤ 84992), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 84736 ≤ 84864) (by norm_num : 84864 ≤ 84992), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 84736 ≤ 84864) (by norm_num : 84864 ≤ 84992), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 84736 ≤ 84864) (by norm_num : 84864 ≤ 84992), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_84480_84992 :
    (∑ n ∈ Ico 84480 84992, mobiusTreeValue 16 mobiusTable1200001 n) = (30 : ℤ) ∧
    (∑ n ∈ Ico 84480 84992, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (312 : ℕ) ∧
    (∑ n ∈ Ico 84480 84992, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (1769471 : ℤ) ∧
    (∑ n ∈ Ico 84480 84992, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (35389650014092699375101989918 : ℤ) := by
  rcases cdemPrefixStats_84480_84736 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_84736_84992 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 84480 ≤ 84736) (by norm_num : 84736 ≤ 84992), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 84480 ≤ 84736) (by norm_num : 84736 ≤ 84992), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 84480 ≤ 84736) (by norm_num : 84736 ≤ 84992), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 84480 ≤ 84736) (by norm_num : 84736 ≤ 84992), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_83968_84992 :
    (∑ n ∈ Ico 83968 84992, mobiusTreeValue 16 mobiusTable1200001 n) = (31 : ℤ) ∧
    (∑ n ∈ Ico 83968 84992, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (621 : ℕ) ∧
    (∑ n ∈ Ico 83968 84992, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (1831138 : ℤ) ∧
    (∑ n ∈ Ico 83968 84992, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (36622969620127977620120750231 : ℤ) := by
  rcases cdemPrefixStats_83968_84480 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_84480_84992 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 83968 ≤ 84480) (by norm_num : 84480 ≤ 84992), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 83968 ≤ 84480) (by norm_num : 84480 ≤ 84992), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 83968 ≤ 84480) (by norm_num : 84480 ≤ 84992), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 83968 ≤ 84480) (by norm_num : 84480 ≤ 84992), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_84992_85056 :
    (∑ n ∈ Ico 84992 85056, mobiusTreeValue 16 mobiusTable1200001 n) = (-3 : ℤ) ∧
    (∑ n ∈ Ico 84992 85056, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 84992 85056, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-176435 : ℤ) ∧
    (∑ n ∈ Ico 84992 85056, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-3528747198043701944930206687 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_85056_85120 :
    (∑ n ∈ Ico 85056 85120, mobiusTreeValue 16 mobiusTable1200001 n) = (-3 : ℤ) ∧
    (∑ n ∈ Ico 85056 85120, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 85056 85120, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-176296 : ℤ) ∧
    (∑ n ∈ Ico 85056 85120, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-3525872125013930120411718040 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_84992_85120 :
    (∑ n ∈ Ico 84992 85120, mobiusTreeValue 16 mobiusTable1200001 n) = (-6 : ℤ) ∧
    (∑ n ∈ Ico 84992 85120, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (80 : ℕ) ∧
    (∑ n ∈ Ico 84992 85120, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-352731 : ℤ) ∧
    (∑ n ∈ Ico 84992 85120, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-7054619323057632065341924727 : ℤ) := by
  rcases cdemPrefixStats_84992_85056 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_85056_85120 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 84992 ≤ 85056) (by norm_num : 85056 ≤ 85120), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 84992 ≤ 85056) (by norm_num : 85056 ≤ 85120), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 84992 ≤ 85056) (by norm_num : 85056 ≤ 85120), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 84992 ≤ 85056) (by norm_num : 85056 ≤ 85120), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_85120_85184 :
    (∑ n ∈ Ico 85120 85184, mobiusTreeValue 16 mobiusTable1200001 n) = (10 : ℤ) ∧
    (∑ n ∈ Ico 85120 85184, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 85120 85184, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (587162 : ℤ) ∧
    (∑ n ∈ Ico 85120 85184, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (11743319371324078993968869173 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_85184_85248 :
    (∑ n ∈ Ico 85184 85248, mobiusTreeValue 16 mobiusTable1200001 n) = (-8 : ℤ) ∧
    (∑ n ∈ Ico 85184 85248, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 85184 85248, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-469322 : ℤ) ∧
    (∑ n ∈ Ico 85184 85248, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-9386587227906750550097992372 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_85120_85248 :
    (∑ n ∈ Ico 85120 85248, mobiusTreeValue 16 mobiusTable1200001 n) = (2 : ℤ) ∧
    (∑ n ∈ Ico 85120 85248, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 85120 85248, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (117840 : ℤ) ∧
    (∑ n ∈ Ico 85120 85248, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (2356732143417328443870876801 : ℤ) := by
  rcases cdemPrefixStats_85120_85184 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_85184_85248 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 85120 ≤ 85184) (by norm_num : 85184 ≤ 85248), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 85120 ≤ 85184) (by norm_num : 85184 ≤ 85248), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 85120 ≤ 85184) (by norm_num : 85184 ≤ 85248), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 85120 ≤ 85184) (by norm_num : 85184 ≤ 85248), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_84992_85248 :
    (∑ n ∈ Ico 84992 85248, mobiusTreeValue 16 mobiusTable1200001 n) = (-4 : ℤ) ∧
    (∑ n ∈ Ico 84992 85248, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (158 : ℕ) ∧
    (∑ n ∈ Ico 84992 85248, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-234891 : ℤ) ∧
    (∑ n ∈ Ico 84992 85248, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-4697887179640303621471047926 : ℤ) := by
  rcases cdemPrefixStats_84992_85120 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_85120_85248 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 84992 ≤ 85120) (by norm_num : 85120 ≤ 85248), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 84992 ≤ 85120) (by norm_num : 85120 ≤ 85248), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 84992 ≤ 85120) (by norm_num : 85120 ≤ 85248), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 84992 ≤ 85120) (by norm_num : 85120 ≤ 85248), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_85248_85312 :
    (∑ n ∈ Ico 85248 85312, mobiusTreeValue 16 mobiusTable1200001 n) = (3 : ℤ) ∧
    (∑ n ∈ Ico 85248 85312, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 85248 85312, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (175763 : ℤ) ∧
    (∑ n ∈ Ico 85248 85312, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (3515266186251575734513101505 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_85312_85376 :
    (∑ n ∈ Ico 85312 85376, mobiusTreeValue 16 mobiusTable1200001 n) = (-2 : ℤ) ∧
    (∑ n ∈ Ico 85312 85376, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 85312 85376, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-117197 : ℤ) ∧
    (∑ n ∈ Ico 85312 85376, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-2343951246751101807391469770 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_85248_85376 :
    (∑ n ∈ Ico 85248 85376, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 85248 85376, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (75 : ℕ) ∧
    (∑ n ∈ Ico 85248 85376, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (58566 : ℤ) ∧
    (∑ n ∈ Ico 85248 85376, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1171314939500473927121631735 : ℤ) := by
  rcases cdemPrefixStats_85248_85312 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_85312_85376 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 85248 ≤ 85312) (by norm_num : 85312 ≤ 85376), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 85248 ≤ 85312) (by norm_num : 85312 ≤ 85376), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 85248 ≤ 85312) (by norm_num : 85312 ≤ 85376), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 85248 ≤ 85312) (by norm_num : 85312 ≤ 85376), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_85376_85440 :
    (∑ n ∈ Ico 85376 85440, mobiusTreeValue 16 mobiusTable1200001 n) = (6 : ℤ) ∧
    (∑ n ∈ Ico 85376 85440, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 85376 85440, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (351253 : ℤ) ∧
    (∑ n ∈ Ico 85376 85440, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (7025157968382525457695551663 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_85440_85504 :
    (∑ n ∈ Ico 85440 85504, mobiusTreeValue 16 mobiusTable1200001 n) = (5 : ℤ) ∧
    (∑ n ∈ Ico 85440 85504, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 85440 85504, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (292363 : ℤ) ∧
    (∑ n ∈ Ico 85440 85504, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (5847295979756684492054042981 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_85376_85504 :
    (∑ n ∈ Ico 85376 85504, mobiusTreeValue 16 mobiusTable1200001 n) = (11 : ℤ) ∧
    (∑ n ∈ Ico 85376 85504, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (81 : ℕ) ∧
    (∑ n ∈ Ico 85376 85504, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (643616 : ℤ) ∧
    (∑ n ∈ Ico 85376 85504, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (12872453948139209949749594644 : ℤ) := by
  rcases cdemPrefixStats_85376_85440 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_85440_85504 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 85376 ≤ 85440) (by norm_num : 85440 ≤ 85504), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 85376 ≤ 85440) (by norm_num : 85440 ≤ 85504), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 85376 ≤ 85440) (by norm_num : 85440 ≤ 85504), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 85376 ≤ 85440) (by norm_num : 85440 ≤ 85504), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_85248_85504 :
    (∑ n ∈ Ico 85248 85504, mobiusTreeValue 16 mobiusTable1200001 n) = (12 : ℤ) ∧
    (∑ n ∈ Ico 85248 85504, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (156 : ℕ) ∧
    (∑ n ∈ Ico 85248 85504, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (702182 : ℤ) ∧
    (∑ n ∈ Ico 85248 85504, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (14043768887639683876871226379 : ℤ) := by
  rcases cdemPrefixStats_85248_85376 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_85376_85504 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 85248 ≤ 85376) (by norm_num : 85376 ≤ 85504), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 85248 ≤ 85376) (by norm_num : 85376 ≤ 85504), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 85248 ≤ 85376) (by norm_num : 85376 ≤ 85504), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 85248 ≤ 85376) (by norm_num : 85376 ≤ 85504), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_84992_85504 :
    (∑ n ∈ Ico 84992 85504, mobiusTreeValue 16 mobiusTable1200001 n) = (8 : ℤ) ∧
    (∑ n ∈ Ico 84992 85504, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (314 : ℕ) ∧
    (∑ n ∈ Ico 84992 85504, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (467291 : ℤ) ∧
    (∑ n ∈ Ico 84992 85504, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (9345881707999380255400178453 : ℤ) := by
  rcases cdemPrefixStats_84992_85248 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_85248_85504 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 84992 ≤ 85248) (by norm_num : 85248 ≤ 85504), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 84992 ≤ 85248) (by norm_num : 85248 ≤ 85504), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 84992 ≤ 85248) (by norm_num : 85248 ≤ 85504), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 84992 ≤ 85248) (by norm_num : 85248 ≤ 85504), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_85504_85568 :
    (∑ n ∈ Ico 85504 85568, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 85504 85568, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (35 : ℕ) ∧
    (∑ n ∈ Ico 85504 85568, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (58406 : ℤ) ∧
    (∑ n ∈ Ico 85504 85568, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1168100490500831889080758211 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_85568_85632 :
    (∑ n ∈ Ico 85568 85632, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 85568 85632, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 85568 85632, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-58386 : ℤ) ∧
    (∑ n ∈ Ico 85568 85632, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-1167665023478673122936545488 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_85504_85632 :
    (∑ n ∈ Ico 85504 85632, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 85504 85632, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (74 : ℕ) ∧
    (∑ n ∈ Ico 85504 85632, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (20 : ℤ) ∧
    (∑ n ∈ Ico 85504 85632, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (435467022158766144212723 : ℤ) := by
  rcases cdemPrefixStats_85504_85568 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_85568_85632 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 85504 ≤ 85568) (by norm_num : 85568 ≤ 85632), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 85504 ≤ 85568) (by norm_num : 85568 ≤ 85632), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 85504 ≤ 85568) (by norm_num : 85568 ≤ 85632), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 85504 ≤ 85568) (by norm_num : 85568 ≤ 85632), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_85632_85696 :
    (∑ n ∈ Ico 85632 85696, mobiusTreeValue 16 mobiusTable1200001 n) = (8 : ℤ) ∧
    (∑ n ∈ Ico 85632 85696, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 85632 85696, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (466920 : ℤ) ∧
    (∑ n ∈ Ico 85632 85696, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (9338485562531571353209719512 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_85696_85760 :
    (∑ n ∈ Ico 85696 85760, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 85696 85760, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 85696 85760, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-58313 : ℤ) ∧
    (∑ n ∈ Ico 85696 85760, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-1166235264749832834596604001 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_85632_85760 :
    (∑ n ∈ Ico 85632 85760, mobiusTreeValue 16 mobiusTable1200001 n) = (7 : ℤ) ∧
    (∑ n ∈ Ico 85632 85760, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (79 : ℕ) ∧
    (∑ n ∈ Ico 85632 85760, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (408607 : ℤ) ∧
    (∑ n ∈ Ico 85632 85760, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (8172250297781738518613115511 : ℤ) := by
  rcases cdemPrefixStats_85632_85696 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_85696_85760 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 85632 ≤ 85696) (by norm_num : 85696 ≤ 85760), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 85632 ≤ 85696) (by norm_num : 85696 ≤ 85760), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 85632 ≤ 85696) (by norm_num : 85696 ≤ 85760), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 85632 ≤ 85696) (by norm_num : 85696 ≤ 85760), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_85504_85760 :
    (∑ n ∈ Ico 85504 85760, mobiusTreeValue 16 mobiusTable1200001 n) = (7 : ℤ) ∧
    (∑ n ∈ Ico 85504 85760, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (153 : ℕ) ∧
    (∑ n ∈ Ico 85504 85760, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (408627 : ℤ) ∧
    (∑ n ∈ Ico 85504 85760, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (8172685764803897284757328234 : ℤ) := by
  rcases cdemPrefixStats_85504_85632 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_85632_85760 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 85504 ≤ 85632) (by norm_num : 85632 ≤ 85760), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 85504 ≤ 85632) (by norm_num : 85632 ≤ 85760), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 85504 ≤ 85632) (by norm_num : 85632 ≤ 85760), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 85504 ≤ 85632) (by norm_num : 85632 ≤ 85760), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_85760_85824 :
    (∑ n ∈ Ico 85760 85824, mobiusTreeValue 16 mobiusTable1200001 n) = (9 : ℤ) ∧
    (∑ n ∈ Ico 85760 85824, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 85760 85824, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (524567 : ℤ) ∧
    (∑ n ∈ Ico 85760 85824, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (10491385712221209853549469811 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_85824_85888 :
    (∑ n ∈ Ico 85824 85888, mobiusTreeValue 16 mobiusTable1200001 n) = (10 : ℤ) ∧
    (∑ n ∈ Ico 85824 85888, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 85824 85888, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (582263 : ℤ) ∧
    (∑ n ∈ Ico 85824 85888, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (11645361286096320167304810410 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_85760_85888 :
    (∑ n ∈ Ico 85760 85888, mobiusTreeValue 16 mobiusTable1200001 n) = (19 : ℤ) ∧
    (∑ n ∈ Ico 85760 85888, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (75 : ℕ) ∧
    (∑ n ∈ Ico 85760 85888, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (1106830 : ℤ) ∧
    (∑ n ∈ Ico 85760 85888, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (22136746998317530020854280221 : ℤ) := by
  rcases cdemPrefixStats_85760_85824 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_85824_85888 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 85760 ≤ 85824) (by norm_num : 85824 ≤ 85888), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 85760 ≤ 85824) (by norm_num : 85824 ≤ 85888), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 85760 ≤ 85824) (by norm_num : 85824 ≤ 85888), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 85760 ≤ 85824) (by norm_num : 85824 ≤ 85888), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_85888_85952 :
    (∑ n ∈ Ico 85888 85952, mobiusTreeValue 16 mobiusTable1200001 n) = (2 : ℤ) ∧
    (∑ n ∈ Ico 85888 85952, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 85888 85952, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (116315 : ℤ) ∧
    (∑ n ∈ Ico 85888 85952, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (2326297182609243197057706867 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_85952_86016 :
    (∑ n ∈ Ico 85952 86016, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 85952 86016, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (42 : ℕ) ∧
    (∑ n ∈ Ico 85952 86016, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (34 : ℤ) ∧
    (∑ n ∈ Ico 85952 86016, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (743725902911775497927556 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_85888_86016 :
    (∑ n ∈ Ico 85888 86016, mobiusTreeValue 16 mobiusTable1200001 n) = (2 : ℤ) ∧
    (∑ n ∈ Ico 85888 86016, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (80 : ℕ) ∧
    (∑ n ∈ Ico 85888 86016, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (116349 : ℤ) ∧
    (∑ n ∈ Ico 85888 86016, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (2327040908512154972555634423 : ℤ) := by
  rcases cdemPrefixStats_85888_85952 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_85952_86016 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 85888 ≤ 85952) (by norm_num : 85952 ≤ 86016), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 85888 ≤ 85952) (by norm_num : 85952 ≤ 86016), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 85888 ≤ 85952) (by norm_num : 85952 ≤ 86016), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 85888 ≤ 85952) (by norm_num : 85952 ≤ 86016), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_85760_86016 :
    (∑ n ∈ Ico 85760 86016, mobiusTreeValue 16 mobiusTable1200001 n) = (21 : ℤ) ∧
    (∑ n ∈ Ico 85760 86016, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (155 : ℕ) ∧
    (∑ n ∈ Ico 85760 86016, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (1223179 : ℤ) ∧
    (∑ n ∈ Ico 85760 86016, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (24463787906829684993409914644 : ℤ) := by
  rcases cdemPrefixStats_85760_85888 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_85888_86016 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 85760 ≤ 85888) (by norm_num : 85888 ≤ 86016), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 85760 ≤ 85888) (by norm_num : 85888 ≤ 86016), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 85760 ≤ 85888) (by norm_num : 85888 ≤ 86016), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 85760 ≤ 85888) (by norm_num : 85888 ≤ 86016), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_85504_86016 :
    (∑ n ∈ Ico 85504 86016, mobiusTreeValue 16 mobiusTable1200001 n) = (28 : ℤ) ∧
    (∑ n ∈ Ico 85504 86016, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (308 : ℕ) ∧
    (∑ n ∈ Ico 85504 86016, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (1631806 : ℤ) ∧
    (∑ n ∈ Ico 85504 86016, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (32636473671633582278167242878 : ℤ) := by
  rcases cdemPrefixStats_85504_85760 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_85760_86016 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 85504 ≤ 85760) (by norm_num : 85760 ≤ 86016), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 85504 ≤ 85760) (by norm_num : 85760 ≤ 86016), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 85504 ≤ 85760) (by norm_num : 85760 ≤ 86016), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 85504 ≤ 85760) (by norm_num : 85760 ≤ 86016), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_84992_86016 :
    (∑ n ∈ Ico 84992 86016, mobiusTreeValue 16 mobiusTable1200001 n) = (36 : ℤ) ∧
    (∑ n ∈ Ico 84992 86016, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (622 : ℕ) ∧
    (∑ n ∈ Ico 84992 86016, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (2099097 : ℤ) ∧
    (∑ n ∈ Ico 84992 86016, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (41982355379632962533567421331 : ℤ) := by
  rcases cdemPrefixStats_84992_85504 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_85504_86016 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 84992 ≤ 85504) (by norm_num : 85504 ≤ 86016), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 84992 ≤ 85504) (by norm_num : 85504 ≤ 86016), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 84992 ≤ 85504) (by norm_num : 85504 ≤ 86016), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 84992 ≤ 85504) (by norm_num : 85504 ≤ 86016), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_83968_86016 :
    (∑ n ∈ Ico 83968 86016, mobiusTreeValue 16 mobiusTable1200001 n) = (67 : ℤ) ∧
    (∑ n ∈ Ico 83968 86016, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (1243 : ℕ) ∧
    (∑ n ∈ Ico 83968 86016, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (3930235 : ℤ) ∧
    (∑ n ∈ Ico 83968 86016, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (78605324999760940153688171562 : ℤ) := by
  rcases cdemPrefixStats_83968_84992 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_84992_86016 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 83968 ≤ 84992) (by norm_num : 84992 ≤ 86016), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 83968 ≤ 84992) (by norm_num : 84992 ≤ 86016), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 83968 ≤ 84992) (by norm_num : 84992 ≤ 86016), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 83968 ≤ 84992) (by norm_num : 84992 ≤ 86016), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_81920_86016 :
    (∑ n ∈ Ico 81920 86016, mobiusTreeValue 16 mobiusTable1200001 n) = (82 : ℤ) ∧
    (∑ n ∈ Ico 81920 86016, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (2494 : ℕ) ∧
    (∑ n ∈ Ico 81920 86016, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (4796607 : ℤ) ∧
    (∑ n ∈ Ico 81920 86016, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (95932858883463164200900049662 : ℤ) := by
  rcases cdemPrefixStats_81920_83968 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_83968_86016 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 81920 ≤ 83968) (by norm_num : 83968 ≤ 86016), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 81920 ≤ 83968) (by norm_num : 83968 ≤ 86016), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 81920 ≤ 83968) (by norm_num : 83968 ≤ 86016), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 81920 ≤ 83968) (by norm_num : 83968 ≤ 86016), hR1, hR2] <;> norm_num

theorem cdemPrefixGroup020_checked_complete :
    (∑ n ∈ Ico 81920 86016, mobiusTreeValue 16 mobiusTable1200001 n) = (82 : ℤ) ∧
    (∑ n ∈ Ico 81920 86016, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (2494 : ℕ) ∧
    (∑ n ∈ Ico 81920 86016, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (4796607 : ℤ) ∧
    (∑ n ∈ Ico 81920 86016, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (95932858883463164200900049662 : ℤ) := cdemPrefixStats_81920_86016
end Helfgott
#print axioms Helfgott.cdemPrefixGroup020_checked_complete

open Helfgott Finset
open scoped BigOperators

theorem solution :
    (∑ n ∈ Ico 81920 86016, mobiusTreeValue 16 mobiusTable1200001 n) = (82 : ℤ) ∧
    (∑ n ∈ Ico 81920 86016, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (2494 : ℕ) ∧
    (∑ n ∈ Ico 81920 86016, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (4796607 : ℤ) ∧
    (∑ n ∈ Ico 81920 86016, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (95932858883463164200900049662 : ℤ) := Helfgott.cdemPrefixGroup020_checked_complete
#print axioms solution
