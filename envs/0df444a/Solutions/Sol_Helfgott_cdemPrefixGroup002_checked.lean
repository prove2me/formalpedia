-- Prove2me | solution 1 for Helfgott.cdemPrefixGroup002_checked
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-09T01:17:14.840723+00:00
-- url     : https://prove2.me/submissions/c819c08c-f125-4c17-b6ed-91f867f7031e

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
private theorem cdemPrefixStats_8192_8256 :
    (∑ n ∈ Ico 8192 8256, mobiusTreeValue 16 mobiusTable1200001 n) = (-8 : ℤ) ∧
    (∑ n ∈ Ico 8192 8256, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 8192 8256, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-4859592 : ℤ) ∧
    (∑ n ∈ Ico 8192 8256, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-97191905568683386779703804039 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_8256_8320 :
    (∑ n ∈ Ico 8256 8320, mobiusTreeValue 16 mobiusTable1200001 n) = (2 : ℤ) ∧
    (∑ n ∈ Ico 8256 8320, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 8256 8320, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (1213440 : ℤ) ∧
    (∑ n ∈ Ico 8256 8320, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (24268809291629982686410343220 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_8192_8320 :
    (∑ n ∈ Ico 8192 8320, mobiusTreeValue 16 mobiusTable1200001 n) = (-6 : ℤ) ∧
    (∑ n ∈ Ico 8192 8320, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (80 : ℕ) ∧
    (∑ n ∈ Ico 8192 8320, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-3646152 : ℤ) ∧
    (∑ n ∈ Ico 8192 8320, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-72923096277053404093293460819 : ℤ) := by
  rcases cdemPrefixStats_8192_8256 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_8256_8320 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 8192 ≤ 8256) (by norm_num : 8256 ≤ 8320), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 8192 ≤ 8256) (by norm_num : 8256 ≤ 8320), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 8192 ≤ 8256) (by norm_num : 8256 ≤ 8320), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 8192 ≤ 8256) (by norm_num : 8256 ≤ 8320), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_8320_8384 :
    (∑ n ∈ Ico 8320 8384, mobiusTreeValue 16 mobiusTable1200001 n) = (5 : ℤ) ∧
    (∑ n ∈ Ico 8320 8384, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 8320 8384, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (2998684 : ℤ) ∧
    (∑ n ∈ Ico 8320 8384, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (59973717662536312396823519409 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_8384_8448 :
    (∑ n ∈ Ico 8384 8448, mobiusTreeValue 16 mobiusTable1200001 n) = (-3 : ℤ) ∧
    (∑ n ∈ Ico 8384 8448, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 8384 8448, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-1773751 : ℤ) ∧
    (∑ n ∈ Ico 8384 8448, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-35475033700518833667660311999 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_8320_8448 :
    (∑ n ∈ Ico 8320 8448, mobiusTreeValue 16 mobiusTable1200001 n) = (2 : ℤ) ∧
    (∑ n ∈ Ico 8320 8448, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (76 : ℕ) ∧
    (∑ n ∈ Ico 8320 8448, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (1224933 : ℤ) ∧
    (∑ n ∈ Ico 8320 8448, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (24498683962017478729163207410 : ℤ) := by
  rcases cdemPrefixStats_8320_8384 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_8384_8448 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 8320 ≤ 8384) (by norm_num : 8384 ≤ 8448), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 8320 ≤ 8384) (by norm_num : 8384 ≤ 8448), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 8320 ≤ 8384) (by norm_num : 8384 ≤ 8448), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 8320 ≤ 8384) (by norm_num : 8384 ≤ 8448), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_8192_8448 :
    (∑ n ∈ Ico 8192 8448, mobiusTreeValue 16 mobiusTable1200001 n) = (-4 : ℤ) ∧
    (∑ n ∈ Ico 8192 8448, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (156 : ℕ) ∧
    (∑ n ∈ Ico 8192 8448, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-2421219 : ℤ) ∧
    (∑ n ∈ Ico 8192 8448, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-48424412315035925364130253409 : ℤ) := by
  rcases cdemPrefixStats_8192_8320 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_8320_8448 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 8192 ≤ 8320) (by norm_num : 8320 ≤ 8448), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 8192 ≤ 8320) (by norm_num : 8320 ≤ 8448), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 8192 ≤ 8320) (by norm_num : 8320 ≤ 8448), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 8192 ≤ 8320) (by norm_num : 8320 ≤ 8448), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_8448_8512 :
    (∑ n ∈ Ico 8448 8512, mobiusTreeValue 16 mobiusTable1200001 n) = (17 : ℤ) ∧
    (∑ n ∈ Ico 8448 8512, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 8448 8512, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (10012220 : ℤ) ∧
    (∑ n ∈ Ico 8448 8512, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (200244578351842723100631605667 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_8512_8576 :
    (∑ n ∈ Ico 8512 8576, mobiusTreeValue 16 mobiusTable1200001 n) = (-4 : ℤ) ∧
    (∑ n ∈ Ico 8512 8576, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 8512 8576, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-2343114 : ℤ) ∧
    (∑ n ∈ Ico 8512 8576, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-46862292537615356628838825976 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_8448_8576 :
    (∑ n ∈ Ico 8448 8576, mobiusTreeValue 16 mobiusTable1200001 n) = (13 : ℤ) ∧
    (∑ n ∈ Ico 8448 8576, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (79 : ℕ) ∧
    (∑ n ∈ Ico 8448 8576, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (7669106 : ℤ) ∧
    (∑ n ∈ Ico 8448 8576, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (153382285814227366471792779691 : ℤ) := by
  rcases cdemPrefixStats_8448_8512 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_8512_8576 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 8448 ≤ 8512) (by norm_num : 8512 ≤ 8576), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 8448 ≤ 8512) (by norm_num : 8512 ≤ 8576), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 8448 ≤ 8512) (by norm_num : 8512 ≤ 8576), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 8448 ≤ 8512) (by norm_num : 8512 ≤ 8576), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_8576_8640 :
    (∑ n ∈ Ico 8576 8640, mobiusTreeValue 16 mobiusTable1200001 n) = (-7 : ℤ) ∧
    (∑ n ∈ Ico 8576 8640, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 8576 8640, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-4060930 : ℤ) ∧
    (∑ n ∈ Ico 8576 8640, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-81218675748739583490161248916 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_8640_8704 :
    (∑ n ∈ Ico 8640 8704, mobiusTreeValue 16 mobiusTable1200001 n) = (-8 : ℤ) ∧
    (∑ n ∈ Ico 8640 8704, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 8640 8704, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-4602868 : ℤ) ∧
    (∑ n ∈ Ico 8640 8704, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-92057434503835839850932009507 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_8576_8704 :
    (∑ n ∈ Ico 8576 8704, mobiusTreeValue 16 mobiusTable1200001 n) = (-15 : ℤ) ∧
    (∑ n ∈ Ico 8576 8704, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 8576 8704, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-8663798 : ℤ) ∧
    (∑ n ∈ Ico 8576 8704, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-173276110252575423341093258423 : ℤ) := by
  rcases cdemPrefixStats_8576_8640 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_8640_8704 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 8576 ≤ 8640) (by norm_num : 8640 ≤ 8704), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 8576 ≤ 8640) (by norm_num : 8640 ≤ 8704), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 8576 ≤ 8640) (by norm_num : 8640 ≤ 8704), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 8576 ≤ 8640) (by norm_num : 8640 ≤ 8704), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_8448_8704 :
    (∑ n ∈ Ico 8448 8704, mobiusTreeValue 16 mobiusTable1200001 n) = (-2 : ℤ) ∧
    (∑ n ∈ Ico 8448 8704, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (156 : ℕ) ∧
    (∑ n ∈ Ico 8448 8704, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-994692 : ℤ) ∧
    (∑ n ∈ Ico 8448 8704, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-19893824438348056869300478732 : ℤ) := by
  rcases cdemPrefixStats_8448_8576 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_8576_8704 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 8448 ≤ 8576) (by norm_num : 8576 ≤ 8704), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 8448 ≤ 8576) (by norm_num : 8576 ≤ 8704), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 8448 ≤ 8576) (by norm_num : 8576 ≤ 8704), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 8448 ≤ 8576) (by norm_num : 8576 ≤ 8704), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_8192_8704 :
    (∑ n ∈ Ico 8192 8704, mobiusTreeValue 16 mobiusTable1200001 n) = (-6 : ℤ) ∧
    (∑ n ∈ Ico 8192 8704, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (312 : ℕ) ∧
    (∑ n ∈ Ico 8192 8704, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-3415911 : ℤ) ∧
    (∑ n ∈ Ico 8192 8704, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-68318236753383982233430732141 : ℤ) := by
  rcases cdemPrefixStats_8192_8448 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_8448_8704 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 8192 ≤ 8448) (by norm_num : 8448 ≤ 8704), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 8192 ≤ 8448) (by norm_num : 8448 ≤ 8704), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 8192 ≤ 8448) (by norm_num : 8448 ≤ 8704), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 8192 ≤ 8448) (by norm_num : 8448 ≤ 8704), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_8704_8768 :
    (∑ n ∈ Ico 8704 8768, mobiusTreeValue 16 mobiusTable1200001 n) = (-2 : ℤ) ∧
    (∑ n ∈ Ico 8704 8768, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 8704 8768, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-1139836 : ℤ) ∧
    (∑ n ∈ Ico 8704 8768, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-22796708272991277555519574788 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_8768_8832 :
    (∑ n ∈ Ico 8768 8832, mobiusTreeValue 16 mobiusTable1200001 n) = (-9 : ℤ) ∧
    (∑ n ∈ Ico 8768 8832, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 8768 8832, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-5108642 : ℤ) ∧
    (∑ n ∈ Ico 8768 8832, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-102172981334498659980865706331 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_8704_8832 :
    (∑ n ∈ Ico 8704 8832, mobiusTreeValue 16 mobiusTable1200001 n) = (-11 : ℤ) ∧
    (∑ n ∈ Ico 8704 8832, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (81 : ℕ) ∧
    (∑ n ∈ Ico 8704 8832, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-6248478 : ℤ) ∧
    (∑ n ∈ Ico 8704 8832, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-124969689607489937536385281119 : ℤ) := by
  rcases cdemPrefixStats_8704_8768 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_8768_8832 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 8704 ≤ 8768) (by norm_num : 8768 ≤ 8832), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 8704 ≤ 8768) (by norm_num : 8768 ≤ 8832), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 8704 ≤ 8768) (by norm_num : 8768 ≤ 8832), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 8704 ≤ 8768) (by norm_num : 8768 ≤ 8832), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_8832_8896 :
    (∑ n ∈ Ico 8832 8896, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 8832 8896, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 8832 8896, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (557714 : ℤ) ∧
    (∑ n ∈ Ico 8832 8896, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (11154298944435215258218918686 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_8896_8960 :
    (∑ n ∈ Ico 8896 8960, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 8896 8960, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (36 : ℕ) ∧
    (∑ n ∈ Ico 8896 8960, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (6832 : ℤ) ∧
    (∑ n ∈ Ico 8896 8960, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (136649597683134904004572208 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_8832_8960 :
    (∑ n ∈ Ico 8832 8960, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 8832 8960, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (75 : ℕ) ∧
    (∑ n ∈ Ico 8832 8960, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (564546 : ℤ) ∧
    (∑ n ∈ Ico 8832 8960, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (11290948542118350162223490894 : ℤ) := by
  rcases cdemPrefixStats_8832_8896 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_8896_8960 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 8832 ≤ 8896) (by norm_num : 8896 ≤ 8960), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 8832 ≤ 8896) (by norm_num : 8896 ≤ 8960), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 8832 ≤ 8896) (by norm_num : 8896 ≤ 8960), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 8832 ≤ 8896) (by norm_num : 8896 ≤ 8960), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_8704_8960 :
    (∑ n ∈ Ico 8704 8960, mobiusTreeValue 16 mobiusTable1200001 n) = (-10 : ℤ) ∧
    (∑ n ∈ Ico 8704 8960, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (156 : ℕ) ∧
    (∑ n ∈ Ico 8704 8960, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-5683932 : ℤ) ∧
    (∑ n ∈ Ico 8704 8960, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-113678741065371587374161790225 : ℤ) := by
  rcases cdemPrefixStats_8704_8832 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_8832_8960 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 8704 ≤ 8832) (by norm_num : 8832 ≤ 8960), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 8704 ≤ 8832) (by norm_num : 8832 ≤ 8960), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 8704 ≤ 8832) (by norm_num : 8832 ≤ 8960), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 8704 ≤ 8832) (by norm_num : 8832 ≤ 8960), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_8960_9024 :
    (∑ n ∈ Ico 8960 9024, mobiusTreeValue 16 mobiusTable1200001 n) = (-5 : ℤ) ∧
    (∑ n ∈ Ico 8960 9024, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 8960 9024, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-2785583 : ℤ) ∧
    (∑ n ∈ Ico 8960 9024, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-55711680948003954093915259963 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_9024_9088 :
    (∑ n ∈ Ico 9024 9088, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 9024 9088, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 9024 9088, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (553898 : ℤ) ∧
    (∑ n ∈ Ico 9024 9088, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (11077963570600273287293979312 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_8960_9088 :
    (∑ n ∈ Ico 8960 9088, mobiusTreeValue 16 mobiusTable1200001 n) = (-4 : ℤ) ∧
    (∑ n ∈ Ico 8960 9088, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 8960 9088, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-2231685 : ℤ) ∧
    (∑ n ∈ Ico 8960 9088, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-44633717377403680806621280651 : ℤ) := by
  rcases cdemPrefixStats_8960_9024 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_9024_9088 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 8960 ≤ 9024) (by norm_num : 9024 ≤ 9088), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 8960 ≤ 9024) (by norm_num : 9024 ≤ 9088), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 8960 ≤ 9024) (by norm_num : 9024 ≤ 9088), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 8960 ≤ 9024) (by norm_num : 9024 ≤ 9088), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_9088_9152 :
    (∑ n ∈ Ico 9088 9152, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 9088 9152, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 9088 9152, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (6725 : ℤ) ∧
    (∑ n ∈ Ico 9088 9152, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (134473058010395812989052959 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_9152_9216 :
    (∑ n ∈ Ico 9152 9216, mobiusTreeValue 16 mobiusTable1200001 n) = (-4 : ℤ) ∧
    (∑ n ∈ Ico 9152 9216, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 9152 9216, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-2172978 : ℤ) ∧
    (∑ n ∈ Ico 9152 9216, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-43459621225145547072195414700 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_9088_9216 :
    (∑ n ∈ Ico 9088 9216, mobiusTreeValue 16 mobiusTable1200001 n) = (-4 : ℤ) ∧
    (∑ n ∈ Ico 9088 9216, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (80 : ℕ) ∧
    (∑ n ∈ Ico 9088 9216, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-2166253 : ℤ) ∧
    (∑ n ∈ Ico 9088 9216, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-43325148167135151259206361741 : ℤ) := by
  rcases cdemPrefixStats_9088_9152 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_9152_9216 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 9088 ≤ 9152) (by norm_num : 9152 ≤ 9216), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 9088 ≤ 9152) (by norm_num : 9152 ≤ 9216), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 9088 ≤ 9152) (by norm_num : 9152 ≤ 9216), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 9088 ≤ 9152) (by norm_num : 9152 ≤ 9216), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_8960_9216 :
    (∑ n ∈ Ico 8960 9216, mobiusTreeValue 16 mobiusTable1200001 n) = (-8 : ℤ) ∧
    (∑ n ∈ Ico 8960 9216, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (158 : ℕ) ∧
    (∑ n ∈ Ico 8960 9216, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-4397938 : ℤ) ∧
    (∑ n ∈ Ico 8960 9216, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-87958865544538832065827642392 : ℤ) := by
  rcases cdemPrefixStats_8960_9088 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_9088_9216 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 8960 ≤ 9088) (by norm_num : 9088 ≤ 9216), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 8960 ≤ 9088) (by norm_num : 9088 ≤ 9216), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 8960 ≤ 9088) (by norm_num : 9088 ≤ 9216), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 8960 ≤ 9088) (by norm_num : 9088 ≤ 9216), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_8704_9216 :
    (∑ n ∈ Ico 8704 9216, mobiusTreeValue 16 mobiusTable1200001 n) = (-18 : ℤ) ∧
    (∑ n ∈ Ico 8704 9216, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (314 : ℕ) ∧
    (∑ n ∈ Ico 8704 9216, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-10081870 : ℤ) ∧
    (∑ n ∈ Ico 8704 9216, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-201637606609910419439989432617 : ℤ) := by
  rcases cdemPrefixStats_8704_8960 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_8960_9216 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 8704 ≤ 8960) (by norm_num : 8960 ≤ 9216), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 8704 ≤ 8960) (by norm_num : 8960 ≤ 9216), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 8704 ≤ 8960) (by norm_num : 8960 ≤ 9216), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 8704 ≤ 8960) (by norm_num : 8960 ≤ 9216), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_8192_9216 :
    (∑ n ∈ Ico 8192 9216, mobiusTreeValue 16 mobiusTable1200001 n) = (-24 : ℤ) ∧
    (∑ n ∈ Ico 8192 9216, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (626 : ℕ) ∧
    (∑ n ∈ Ico 8192 9216, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-13497781 : ℤ) ∧
    (∑ n ∈ Ico 8192 9216, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-269955843363294401673420164758 : ℤ) := by
  rcases cdemPrefixStats_8192_8704 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_8704_9216 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 8192 ≤ 8704) (by norm_num : 8704 ≤ 9216), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 8192 ≤ 8704) (by norm_num : 8704 ≤ 9216), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 8192 ≤ 8704) (by norm_num : 8704 ≤ 9216), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 8192 ≤ 8704) (by norm_num : 8704 ≤ 9216), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_9216_9280 :
    (∑ n ∈ Ico 9216 9280, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 9216 9280, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 9216 9280, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (1222 : ℤ) ∧
    (∑ n ∈ Ico 9216 9280, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (24483655695633958722480313 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_9280_9344 :
    (∑ n ∈ Ico 9280 9344, mobiusTreeValue 16 mobiusTable1200001 n) = (-5 : ℤ) ∧
    (∑ n ∈ Ico 9280 9344, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 9280 9344, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-2684507 : ℤ) ∧
    (∑ n ∈ Ico 9280 9344, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-53690138121353048336625418055 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_9216_9344 :
    (∑ n ∈ Ico 9216 9344, mobiusTreeValue 16 mobiusTable1200001 n) = (-5 : ℤ) ∧
    (∑ n ∈ Ico 9216 9344, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 9216 9344, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-2683285 : ℤ) ∧
    (∑ n ∈ Ico 9216 9344, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-53665654465657414377902937742 : ℤ) := by
  rcases cdemPrefixStats_9216_9280 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_9280_9344 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 9216 ≤ 9280) (by norm_num : 9280 ≤ 9344), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 9216 ≤ 9280) (by norm_num : 9280 ≤ 9344), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 9216 ≤ 9280) (by norm_num : 9280 ≤ 9344), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 9216 ≤ 9280) (by norm_num : 9280 ≤ 9344), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_9344_9408 :
    (∑ n ∈ Ico 9344 9408, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 9344 9408, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 9344 9408, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (540910 : ℤ) ∧
    (∑ n ∈ Ico 9344 9408, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (10818205082934893762149616517 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_9408_9472 :
    (∑ n ∈ Ico 9408 9472, mobiusTreeValue 16 mobiusTable1200001 n) = (-11 : ℤ) ∧
    (∑ n ∈ Ico 9408 9472, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 9408 9472, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-5835268 : ℤ) ∧
    (∑ n ∈ Ico 9408 9472, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-116705454697650390548345107107 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_9344_9472 :
    (∑ n ∈ Ico 9344 9472, mobiusTreeValue 16 mobiusTable1200001 n) = (-10 : ℤ) ∧
    (∑ n ∈ Ico 9344 9472, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 9344 9472, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-5294358 : ℤ) ∧
    (∑ n ∈ Ico 9344 9472, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-105887249614715496786195490590 : ℤ) := by
  rcases cdemPrefixStats_9344_9408 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_9408_9472 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 9344 ≤ 9408) (by norm_num : 9408 ≤ 9472), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 9344 ≤ 9408) (by norm_num : 9408 ≤ 9472), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 9344 ≤ 9408) (by norm_num : 9408 ≤ 9472), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 9344 ≤ 9408) (by norm_num : 9408 ≤ 9472), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_9216_9472 :
    (∑ n ∈ Ico 9216 9472, mobiusTreeValue 16 mobiusTable1200001 n) = (-15 : ℤ) ∧
    (∑ n ∈ Ico 9216 9472, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (155 : ℕ) ∧
    (∑ n ∈ Ico 9216 9472, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-7977643 : ℤ) ∧
    (∑ n ∈ Ico 9216 9472, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-159552904080372911164098428332 : ℤ) := by
  rcases cdemPrefixStats_9216_9344 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_9344_9472 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 9216 ≤ 9344) (by norm_num : 9344 ≤ 9472), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 9216 ≤ 9344) (by norm_num : 9344 ≤ 9472), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 9216 ≤ 9344) (by norm_num : 9344 ≤ 9472), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 9216 ≤ 9344) (by norm_num : 9344 ≤ 9472), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_9472_9536 :
    (∑ n ∈ Ico 9472 9536, mobiusTreeValue 16 mobiusTable1200001 n) = (-3 : ℤ) ∧
    (∑ n ∈ Ico 9472 9536, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 9472 9536, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-1587375 : ℤ) ∧
    (∑ n ∈ Ico 9472 9536, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-31747505507509642207566899830 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_9536_9600 :
    (∑ n ∈ Ico 9536 9600, mobiusTreeValue 16 mobiusTable1200001 n) = (3 : ℤ) ∧
    (∑ n ∈ Ico 9536 9600, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 9536 9600, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (1559735 : ℤ) ∧
    (∑ n ∈ Ico 9536 9600, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (31194797117312339467858230887 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_9472_9600 :
    (∑ n ∈ Ico 9472 9600, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 9472 9600, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (76 : ℕ) ∧
    (∑ n ∈ Ico 9472 9600, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-27640 : ℤ) ∧
    (∑ n ∈ Ico 9472 9600, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-552708390197302739708668943 : ℤ) := by
  rcases cdemPrefixStats_9472_9536 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_9536_9600 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 9472 ≤ 9536) (by norm_num : 9536 ≤ 9600), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 9472 ≤ 9536) (by norm_num : 9536 ≤ 9600), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 9472 ≤ 9536) (by norm_num : 9536 ≤ 9600), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 9472 ≤ 9536) (by norm_num : 9536 ≤ 9600), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_9600_9664 :
    (∑ n ∈ Ico 9600 9664, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 9600 9664, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 9600 9664, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-1988 : ℤ) ∧
    (∑ n ∈ Ico 9600 9664, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-39746274471883882299825448 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_9664_9728 :
    (∑ n ∈ Ico 9664 9728, mobiusTreeValue 16 mobiusTable1200001 n) = (-16 : ℤ) ∧
    (∑ n ∈ Ico 9664 9728, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (42 : ℕ) ∧
    (∑ n ∈ Ico 9664 9728, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-8246584 : ℤ) ∧
    (∑ n ∈ Ico 9664 9728, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-164931756327213752100362186901 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_9600_9728 :
    (∑ n ∈ Ico 9600 9728, mobiusTreeValue 16 mobiusTable1200001 n) = (-16 : ℤ) ∧
    (∑ n ∈ Ico 9600 9728, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (80 : ℕ) ∧
    (∑ n ∈ Ico 9600 9728, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-8248572 : ℤ) ∧
    (∑ n ∈ Ico 9600 9728, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-164971502601685635982662012349 : ℤ) := by
  rcases cdemPrefixStats_9600_9664 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_9664_9728 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 9600 ≤ 9664) (by norm_num : 9664 ≤ 9728), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 9600 ≤ 9664) (by norm_num : 9664 ≤ 9728), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 9600 ≤ 9664) (by norm_num : 9664 ≤ 9728), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 9600 ≤ 9664) (by norm_num : 9664 ≤ 9728), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_9472_9728 :
    (∑ n ∈ Ico 9472 9728, mobiusTreeValue 16 mobiusTable1200001 n) = (-16 : ℤ) ∧
    (∑ n ∈ Ico 9472 9728, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (156 : ℕ) ∧
    (∑ n ∈ Ico 9472 9728, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-8276212 : ℤ) ∧
    (∑ n ∈ Ico 9472 9728, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-165524210991882938722370681292 : ℤ) := by
  rcases cdemPrefixStats_9472_9600 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_9600_9728 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 9472 ≤ 9600) (by norm_num : 9600 ≤ 9728), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 9472 ≤ 9600) (by norm_num : 9600 ≤ 9728), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 9472 ≤ 9600) (by norm_num : 9600 ≤ 9728), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 9472 ≤ 9600) (by norm_num : 9600 ≤ 9728), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_9216_9728 :
    (∑ n ∈ Ico 9216 9728, mobiusTreeValue 16 mobiusTable1200001 n) = (-31 : ℤ) ∧
    (∑ n ∈ Ico 9216 9728, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (311 : ℕ) ∧
    (∑ n ∈ Ico 9216 9728, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-16253855 : ℤ) ∧
    (∑ n ∈ Ico 9216 9728, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-325077115072255849886469109624 : ℤ) := by
  rcases cdemPrefixStats_9216_9472 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_9472_9728 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 9216 ≤ 9472) (by norm_num : 9472 ≤ 9728), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 9216 ≤ 9472) (by norm_num : 9472 ≤ 9728), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 9216 ≤ 9472) (by norm_num : 9472 ≤ 9728), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 9216 ≤ 9472) (by norm_num : 9472 ≤ 9728), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_9728_9792 :
    (∑ n ∈ Ico 9728 9792, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 9728 9792, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 9728 9792, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-508530 : ℤ) ∧
    (∑ n ∈ Ico 9728 9792, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-10170588132741357378601458042 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_9792_9856 :
    (∑ n ∈ Ico 9792 9856, mobiusTreeValue 16 mobiusTable1200001 n) = (-7 : ℤ) ∧
    (∑ n ∈ Ico 9792 9856, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 9792 9856, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-3560940 : ℤ) ∧
    (∑ n ∈ Ico 9792 9856, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-71218866184166613329518890731 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_9728_9856 :
    (∑ n ∈ Ico 9728 9856, mobiusTreeValue 16 mobiusTable1200001 n) = (-8 : ℤ) ∧
    (∑ n ∈ Ico 9728 9856, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (76 : ℕ) ∧
    (∑ n ∈ Ico 9728 9856, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-4069470 : ℤ) ∧
    (∑ n ∈ Ico 9728 9856, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-81389454316907970708120348773 : ℤ) := by
  rcases cdemPrefixStats_9728_9792 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_9792_9856 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 9728 ≤ 9792) (by norm_num : 9792 ≤ 9856), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 9728 ≤ 9792) (by norm_num : 9792 ≤ 9856), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 9728 ≤ 9792) (by norm_num : 9792 ≤ 9856), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 9728 ≤ 9792) (by norm_num : 9792 ≤ 9856), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_9856_9920 :
    (∑ n ∈ Ico 9856 9920, mobiusTreeValue 16 mobiusTable1200001 n) = (3 : ℤ) ∧
    (∑ n ∈ Ico 9856 9920, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 9856 9920, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (1517707 : ℤ) ∧
    (∑ n ∈ Ico 9856 9920, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (30354173064679636085905733819 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_9920_9984 :
    (∑ n ∈ Ico 9920 9984, mobiusTreeValue 16 mobiusTable1200001 n) = (7 : ℤ) ∧
    (∑ n ∈ Ico 9920 9984, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 9920 9984, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (3513763 : ℤ) ∧
    (∑ n ∈ Ico 9920 9984, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (70275335419718574452892415910 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_9856_9984 :
    (∑ n ∈ Ico 9856 9984, mobiusTreeValue 16 mobiusTable1200001 n) = (10 : ℤ) ∧
    (∑ n ∈ Ico 9856 9984, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 9856 9984, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (5031470 : ℤ) ∧
    (∑ n ∈ Ico 9856 9984, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (100629508484398210538798149729 : ℤ) := by
  rcases cdemPrefixStats_9856_9920 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_9920_9984 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 9856 ≤ 9920) (by norm_num : 9920 ≤ 9984), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 9856 ≤ 9920) (by norm_num : 9920 ≤ 9984), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 9856 ≤ 9920) (by norm_num : 9920 ≤ 9984), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 9856 ≤ 9920) (by norm_num : 9920 ≤ 9984), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_9728_9984 :
    (∑ n ∈ Ico 9728 9984, mobiusTreeValue 16 mobiusTable1200001 n) = (2 : ℤ) ∧
    (∑ n ∈ Ico 9728 9984, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (154 : ℕ) ∧
    (∑ n ∈ Ico 9728 9984, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (962000 : ℤ) ∧
    (∑ n ∈ Ico 9728 9984, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (19240054167490239830677800956 : ℤ) := by
  rcases cdemPrefixStats_9728_9856 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_9856_9984 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 9728 ≤ 9856) (by norm_num : 9856 ≤ 9984), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 9728 ≤ 9856) (by norm_num : 9856 ≤ 9984), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 9728 ≤ 9856) (by norm_num : 9856 ≤ 9984), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 9728 ≤ 9856) (by norm_num : 9856 ≤ 9984), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_9984_10048 :
    (∑ n ∈ Ico 9984 10048, mobiusTreeValue 16 mobiusTable1200001 n) = (14 : ℤ) ∧
    (∑ n ∈ Ico 9984 10048, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 9984 10048, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (6994631 : ℤ) ∧
    (∑ n ∈ Ico 9984 10048, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (139892675165908622087171083196 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_10048_10112 :
    (∑ n ∈ Ico 10048 10112, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 10048 10112, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (36 : ℕ) ∧
    (∑ n ∈ Ico 10048 10112, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (3148 : ℤ) ∧
    (∑ n ∈ Ico 10048 10112, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (62944714658558697861652956 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_9984_10112 :
    (∑ n ∈ Ico 9984 10112, mobiusTreeValue 16 mobiusTable1200001 n) = (14 : ℤ) ∧
    (∑ n ∈ Ico 9984 10112, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (76 : ℕ) ∧
    (∑ n ∈ Ico 9984 10112, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (6997779 : ℤ) ∧
    (∑ n ∈ Ico 9984 10112, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (139955619880567180785032736152 : ℤ) := by
  rcases cdemPrefixStats_9984_10048 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_10048_10112 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 9984 ≤ 10048) (by norm_num : 10048 ≤ 10112), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 9984 ≤ 10048) (by norm_num : 10048 ≤ 10112), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 9984 ≤ 10048) (by norm_num : 10048 ≤ 10112), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 9984 ≤ 10048) (by norm_num : 10048 ≤ 10112), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_10112_10176 :
    (∑ n ∈ Ico 10112 10176, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 10112 10176, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 10112 10176, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (1042 : ℤ) ∧
    (∑ n ∈ Ico 10112 10176, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (20848337916726852031210001 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_10176_10240 :
    (∑ n ∈ Ico 10176 10240, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 10176 10240, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 10176 10240, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (478876 : ℤ) ∧
    (∑ n ∈ Ico 10176 10240, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (9577486071231521952793803176 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_10112_10240 :
    (∑ n ∈ Ico 10112 10240, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 10112 10240, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (81 : ℕ) ∧
    (∑ n ∈ Ico 10112 10240, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (479918 : ℤ) ∧
    (∑ n ∈ Ico 10112 10240, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (9598334409148248804825013177 : ℤ) := by
  rcases cdemPrefixStats_10112_10176 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_10176_10240 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 10112 ≤ 10176) (by norm_num : 10176 ≤ 10240), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 10112 ≤ 10176) (by norm_num : 10176 ≤ 10240), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 10112 ≤ 10176) (by norm_num : 10176 ≤ 10240), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 10112 ≤ 10176) (by norm_num : 10176 ≤ 10240), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_9984_10240 :
    (∑ n ∈ Ico 9984 10240, mobiusTreeValue 16 mobiusTable1200001 n) = (15 : ℤ) ∧
    (∑ n ∈ Ico 9984 10240, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (157 : ℕ) ∧
    (∑ n ∈ Ico 9984 10240, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (7477697 : ℤ) ∧
    (∑ n ∈ Ico 9984 10240, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (149553954289715429589857749329 : ℤ) := by
  rcases cdemPrefixStats_9984_10112 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_10112_10240 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 9984 ≤ 10112) (by norm_num : 10112 ≤ 10240), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 9984 ≤ 10112) (by norm_num : 10112 ≤ 10240), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 9984 ≤ 10112) (by norm_num : 10112 ≤ 10240), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 9984 ≤ 10112) (by norm_num : 10112 ≤ 10240), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_9728_10240 :
    (∑ n ∈ Ico 9728 10240, mobiusTreeValue 16 mobiusTable1200001 n) = (17 : ℤ) ∧
    (∑ n ∈ Ico 9728 10240, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (311 : ℕ) ∧
    (∑ n ∈ Ico 9728 10240, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (8439697 : ℤ) ∧
    (∑ n ∈ Ico 9728 10240, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (168794008457205669420535550285 : ℤ) := by
  rcases cdemPrefixStats_9728_9984 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_9984_10240 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 9728 ≤ 9984) (by norm_num : 9984 ≤ 10240), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 9728 ≤ 9984) (by norm_num : 9984 ≤ 10240), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 9728 ≤ 9984) (by norm_num : 9984 ≤ 10240), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 9728 ≤ 9984) (by norm_num : 9984 ≤ 10240), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_9216_10240 :
    (∑ n ∈ Ico 9216 10240, mobiusTreeValue 16 mobiusTable1200001 n) = (-14 : ℤ) ∧
    (∑ n ∈ Ico 9216 10240, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (622 : ℕ) ∧
    (∑ n ∈ Ico 9216 10240, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-7814158 : ℤ) ∧
    (∑ n ∈ Ico 9216 10240, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-156283106615050180465933559339 : ℤ) := by
  rcases cdemPrefixStats_9216_9728 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_9728_10240 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 9216 ≤ 9728) (by norm_num : 9728 ≤ 10240), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 9216 ≤ 9728) (by norm_num : 9728 ≤ 10240), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 9216 ≤ 9728) (by norm_num : 9728 ≤ 10240), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 9216 ≤ 9728) (by norm_num : 9728 ≤ 10240), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_8192_10240 :
    (∑ n ∈ Ico 8192 10240, mobiusTreeValue 16 mobiusTable1200001 n) = (-38 : ℤ) ∧
    (∑ n ∈ Ico 8192 10240, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (1248 : ℕ) ∧
    (∑ n ∈ Ico 8192 10240, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-21311939 : ℤ) ∧
    (∑ n ∈ Ico 8192 10240, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-426238949978344582139353724097 : ℤ) := by
  rcases cdemPrefixStats_8192_9216 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_9216_10240 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 8192 ≤ 9216) (by norm_num : 9216 ≤ 10240), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 8192 ≤ 9216) (by norm_num : 9216 ≤ 10240), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 8192 ≤ 9216) (by norm_num : 9216 ≤ 10240), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 8192 ≤ 9216) (by norm_num : 9216 ≤ 10240), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_10240_10304 :
    (∑ n ∈ Ico 10240 10304, mobiusTreeValue 16 mobiusTable1200001 n) = (-14 : ℤ) ∧
    (∑ n ∈ Ico 10240 10304, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 10240 10304, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-6820344 : ℤ) ∧
    (∑ n ∈ Ico 10240 10304, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-136407023054465112275464216732 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_10304_10368 :
    (∑ n ∈ Ico 10304 10368, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 10304 10368, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 10304 10368, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-488001 : ℤ) ∧
    (∑ n ∈ Ico 10304 10368, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-9759973474803589469705964235 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_10240_10368 :
    (∑ n ∈ Ico 10240 10368, mobiusTreeValue 16 mobiusTable1200001 n) = (-15 : ℤ) ∧
    (∑ n ∈ Ico 10240 10368, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 10240 10368, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-7308345 : ℤ) ∧
    (∑ n ∈ Ico 10240 10368, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-146166996529268701745170180967 : ℤ) := by
  rcases cdemPrefixStats_10240_10304 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_10304_10368 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 10240 ≤ 10304) (by norm_num : 10304 ≤ 10368), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 10240 ≤ 10304) (by norm_num : 10304 ≤ 10368), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 10240 ≤ 10304) (by norm_num : 10304 ≤ 10368), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 10240 ≤ 10304) (by norm_num : 10304 ≤ 10368), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_10368_10432 :
    (∑ n ∈ Ico 10368 10432, mobiusTreeValue 16 mobiusTable1200001 n) = (7 : ℤ) ∧
    (∑ n ∈ Ico 10368 10432, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 10368 10432, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (3363537 : ℤ) ∧
    (∑ n ∈ Ico 10368 10432, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (67270758861027742960452187620 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_10432_10496 :
    (∑ n ∈ Ico 10432 10496, mobiusTreeValue 16 mobiusTable1200001 n) = (4 : ℤ) ∧
    (∑ n ∈ Ico 10432 10496, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (36 : ℕ) ∧
    (∑ n ∈ Ico 10432 10496, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (1909902 : ℤ) ∧
    (∑ n ∈ Ico 10432 10496, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (38198048425542719424299170116 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_10368_10496 :
    (∑ n ∈ Ico 10368 10496, mobiusTreeValue 16 mobiusTable1200001 n) = (11 : ℤ) ∧
    (∑ n ∈ Ico 10368 10496, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (75 : ℕ) ∧
    (∑ n ∈ Ico 10368 10496, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (5273439 : ℤ) ∧
    (∑ n ∈ Ico 10368 10496, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (105468807286570462384751357736 : ℤ) := by
  rcases cdemPrefixStats_10368_10432 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_10432_10496 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 10368 ≤ 10432) (by norm_num : 10432 ≤ 10496), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 10368 ≤ 10432) (by norm_num : 10432 ≤ 10496), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 10368 ≤ 10432) (by norm_num : 10432 ≤ 10496), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 10368 ≤ 10432) (by norm_num : 10432 ≤ 10496), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_10240_10496 :
    (∑ n ∈ Ico 10240 10496, mobiusTreeValue 16 mobiusTable1200001 n) = (-4 : ℤ) ∧
    (∑ n ∈ Ico 10240 10496, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (152 : ℕ) ∧
    (∑ n ∈ Ico 10240 10496, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-2034906 : ℤ) ∧
    (∑ n ∈ Ico 10240 10496, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-40698189242698239360418823231 : ℤ) := by
  rcases cdemPrefixStats_10240_10368 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_10368_10496 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 10240 ≤ 10368) (by norm_num : 10368 ≤ 10496), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 10240 ≤ 10368) (by norm_num : 10368 ≤ 10496), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 10240 ≤ 10368) (by norm_num : 10368 ≤ 10496), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 10240 ≤ 10368) (by norm_num : 10368 ≤ 10496), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_10496_10560 :
    (∑ n ∈ Ico 10496 10560, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 10496 10560, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 10496 10560, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-486793 : ℤ) ∧
    (∑ n ∈ Ico 10496 10560, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-9735871596187380353164715755 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_10560_10624 :
    (∑ n ∈ Ico 10560 10624, mobiusTreeValue 16 mobiusTable1200001 n) = (3 : ℤ) ∧
    (∑ n ∈ Ico 10560 10624, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 10560 10624, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (1422004 : ℤ) ∧
    (∑ n ∈ Ico 10560 10624, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (28440120582867430559484258044 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_10496_10624 :
    (∑ n ∈ Ico 10496 10624, mobiusTreeValue 16 mobiusTable1200001 n) = (2 : ℤ) ∧
    (∑ n ∈ Ico 10496 10624, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (80 : ℕ) ∧
    (∑ n ∈ Ico 10496 10624, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (935211 : ℤ) ∧
    (∑ n ∈ Ico 10496 10624, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (18704248986680050206319542289 : ℤ) := by
  rcases cdemPrefixStats_10496_10560 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_10560_10624 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 10496 ≤ 10560) (by norm_num : 10560 ≤ 10624), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 10496 ≤ 10560) (by norm_num : 10560 ≤ 10624), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 10496 ≤ 10560) (by norm_num : 10560 ≤ 10624), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 10496 ≤ 10560) (by norm_num : 10560 ≤ 10624), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_10624_10688 :
    (∑ n ∈ Ico 10624 10688, mobiusTreeValue 16 mobiusTable1200001 n) = (2 : ℤ) ∧
    (∑ n ∈ Ico 10624 10688, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (36 : ℕ) ∧
    (∑ n ∈ Ico 10624 10688, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (927646 : ℤ) ∧
    (∑ n ∈ Ico 10624 10688, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (18552940813739876270143243959 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_10688_10752 :
    (∑ n ∈ Ico 10688 10752, mobiusTreeValue 16 mobiusTable1200001 n) = (-3 : ℤ) ∧
    (∑ n ∈ Ico 10688 10752, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 10688 10752, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-1402728 : ℤ) ∧
    (∑ n ∈ Ico 10688 10752, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-28054640803467858231020049802 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_10624_10752 :
    (∑ n ∈ Ico 10624 10752, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 10624 10752, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (75 : ℕ) ∧
    (∑ n ∈ Ico 10624 10752, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-475082 : ℤ) ∧
    (∑ n ∈ Ico 10624 10752, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-9501699989727981960876805843 : ℤ) := by
  rcases cdemPrefixStats_10624_10688 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_10688_10752 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 10624 ≤ 10688) (by norm_num : 10688 ≤ 10752), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 10624 ≤ 10688) (by norm_num : 10688 ≤ 10752), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 10624 ≤ 10688) (by norm_num : 10688 ≤ 10752), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 10624 ≤ 10688) (by norm_num : 10688 ≤ 10752), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_10496_10752 :
    (∑ n ∈ Ico 10496 10752, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 10496 10752, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (155 : ℕ) ∧
    (∑ n ∈ Ico 10496 10752, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (460129 : ℤ) ∧
    (∑ n ∈ Ico 10496 10752, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (9202548996952068245442736446 : ℤ) := by
  rcases cdemPrefixStats_10496_10624 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_10624_10752 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 10496 ≤ 10624) (by norm_num : 10624 ≤ 10752), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 10496 ≤ 10624) (by norm_num : 10624 ≤ 10752), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 10496 ≤ 10624) (by norm_num : 10624 ≤ 10752), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 10496 ≤ 10624) (by norm_num : 10624 ≤ 10752), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_10240_10752 :
    (∑ n ∈ Ico 10240 10752, mobiusTreeValue 16 mobiusTable1200001 n) = (-3 : ℤ) ∧
    (∑ n ∈ Ico 10240 10752, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (307 : ℕ) ∧
    (∑ n ∈ Ico 10240 10752, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-1574777 : ℤ) ∧
    (∑ n ∈ Ico 10240 10752, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-31495640245746171114976086785 : ℤ) := by
  rcases cdemPrefixStats_10240_10496 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_10496_10752 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 10240 ≤ 10496) (by norm_num : 10496 ≤ 10752), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 10240 ≤ 10496) (by norm_num : 10496 ≤ 10752), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 10240 ≤ 10496) (by norm_num : 10496 ≤ 10752), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 10240 ≤ 10496) (by norm_num : 10496 ≤ 10752), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_10752_10816 :
    (∑ n ∈ Ico 10752 10816, mobiusTreeValue 16 mobiusTable1200001 n) = (5 : ℤ) ∧
    (∑ n ∈ Ico 10752 10816, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 10752 10816, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (2311727 : ℤ) ∧
    (∑ n ∈ Ico 10752 10816, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (46234543442216269356096448402 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_10816_10880 :
    (∑ n ∈ Ico 10816 10880, mobiusTreeValue 16 mobiusTable1200001 n) = (5 : ℤ) ∧
    (∑ n ∈ Ico 10816 10880, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 10816 10880, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (2309088 : ℤ) ∧
    (∑ n ∈ Ico 10816 10880, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (46181769307744340679788086097 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_10752_10880 :
    (∑ n ∈ Ico 10752 10880, mobiusTreeValue 16 mobiusTable1200001 n) = (10 : ℤ) ∧
    (∑ n ∈ Ico 10752 10880, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 10752 10880, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (4620815 : ℤ) ∧
    (∑ n ∈ Ico 10752 10880, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (92416312749960610035884534499 : ℤ) := by
  rcases cdemPrefixStats_10752_10816 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_10816_10880 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 10752 ≤ 10816) (by norm_num : 10816 ≤ 10880), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 10752 ≤ 10816) (by norm_num : 10816 ≤ 10880), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 10752 ≤ 10816) (by norm_num : 10816 ≤ 10880), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 10752 ≤ 10816) (by norm_num : 10816 ≤ 10880), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_10880_10944 :
    (∑ n ∈ Ico 10880 10944, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 10880 10944, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 10880 10944, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (458502 : ℤ) ∧
    (∑ n ∈ Ico 10880 10944, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (9170022054767839509768358319 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_10944_11008 :
    (∑ n ∈ Ico 10944 11008, mobiusTreeValue 16 mobiusTable1200001 n) = (-2 : ℤ) ∧
    (∑ n ∈ Ico 10944 11008, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 10944 11008, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-911836 : ℤ) ∧
    (∑ n ∈ Ico 10944 11008, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-18236731089053877439728447908 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_10880_11008 :
    (∑ n ∈ Ico 10880 11008, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 10880 11008, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 10880 11008, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-453334 : ℤ) ∧
    (∑ n ∈ Ico 10880 11008, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-9066709034286037929960089589 : ℤ) := by
  rcases cdemPrefixStats_10880_10944 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_10944_11008 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 10880 ≤ 10944) (by norm_num : 10944 ≤ 11008), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 10880 ≤ 10944) (by norm_num : 10944 ≤ 11008), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 10880 ≤ 10944) (by norm_num : 10944 ≤ 11008), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 10880 ≤ 10944) (by norm_num : 10944 ≤ 11008), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_10752_11008 :
    (∑ n ∈ Ico 10752 11008, mobiusTreeValue 16 mobiusTable1200001 n) = (9 : ℤ) ∧
    (∑ n ∈ Ico 10752 11008, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (155 : ℕ) ∧
    (∑ n ∈ Ico 10752 11008, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (4167481 : ℤ) ∧
    (∑ n ∈ Ico 10752 11008, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (83349603715674572105924444910 : ℤ) := by
  rcases cdemPrefixStats_10752_10880 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_10880_11008 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 10752 ≤ 10880) (by norm_num : 10880 ≤ 11008), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 10752 ≤ 10880) (by norm_num : 10880 ≤ 11008), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 10752 ≤ 10880) (by norm_num : 10880 ≤ 11008), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 10752 ≤ 10880) (by norm_num : 10880 ≤ 11008), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_11008_11072 :
    (∑ n ∈ Ico 11008 11072, mobiusTreeValue 16 mobiusTable1200001 n) = (10 : ℤ) ∧
    (∑ n ∈ Ico 11008 11072, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 11008 11072, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (4537243 : ℤ) ∧
    (∑ n ∈ Ico 11008 11072, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (90744936450514788059942266853 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_11072_11136 :
    (∑ n ∈ Ico 11072 11136, mobiusTreeValue 16 mobiusTable1200001 n) = (-3 : ℤ) ∧
    (∑ n ∈ Ico 11072 11136, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 11072 11136, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-1351769 : ℤ) ∧
    (∑ n ∈ Ico 11072 11136, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-27035436047242618907583083929 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_11008_11136 :
    (∑ n ∈ Ico 11008 11136, mobiusTreeValue 16 mobiusTable1200001 n) = (7 : ℤ) ∧
    (∑ n ∈ Ico 11008 11136, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 11008 11136, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (3185474 : ℤ) ∧
    (∑ n ∈ Ico 11008 11136, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (63709500403272169152359182924 : ℤ) := by
  rcases cdemPrefixStats_11008_11072 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_11072_11136 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 11008 ≤ 11072) (by norm_num : 11072 ≤ 11136), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 11008 ≤ 11072) (by norm_num : 11072 ≤ 11136), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 11008 ≤ 11072) (by norm_num : 11072 ≤ 11136), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 11008 ≤ 11072) (by norm_num : 11072 ≤ 11136), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_11136_11200 :
    (∑ n ∈ Ico 11136 11200, mobiusTreeValue 16 mobiusTable1200001 n) = (4 : ℤ) ∧
    (∑ n ∈ Ico 11136 11200, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 11136 11200, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (1787393 : ℤ) ∧
    (∑ n ∈ Ico 11136 11200, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (35747843805751519197084965473 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_11200_11264 :
    (∑ n ∈ Ico 11200 11264, mobiusTreeValue 16 mobiusTable1200001 n) = (-3 : ℤ) ∧
    (∑ n ∈ Ico 11200 11264, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 11200 11264, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-1329487 : ℤ) ∧
    (∑ n ∈ Ico 11200 11264, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-26589777145859210430489909389 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_11136_11264 :
    (∑ n ∈ Ico 11136 11264, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 11136 11264, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 11136 11264, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (457906 : ℤ) ∧
    (∑ n ∈ Ico 11136 11264, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (9158066659892308766595056084 : ℤ) := by
  rcases cdemPrefixStats_11136_11200 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_11200_11264 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 11136 ≤ 11200) (by norm_num : 11200 ≤ 11264), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 11136 ≤ 11200) (by norm_num : 11200 ≤ 11264), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 11136 ≤ 11200) (by norm_num : 11200 ≤ 11264), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 11136 ≤ 11200) (by norm_num : 11200 ≤ 11264), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_11008_11264 :
    (∑ n ∈ Ico 11008 11264, mobiusTreeValue 16 mobiusTable1200001 n) = (8 : ℤ) ∧
    (∑ n ∈ Ico 11008 11264, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (154 : ℕ) ∧
    (∑ n ∈ Ico 11008 11264, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (3643380 : ℤ) ∧
    (∑ n ∈ Ico 11008 11264, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (72867567063164477918954239008 : ℤ) := by
  rcases cdemPrefixStats_11008_11136 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_11136_11264 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 11008 ≤ 11136) (by norm_num : 11136 ≤ 11264), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 11008 ≤ 11136) (by norm_num : 11136 ≤ 11264), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 11008 ≤ 11136) (by norm_num : 11136 ≤ 11264), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 11008 ≤ 11136) (by norm_num : 11136 ≤ 11264), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_10752_11264 :
    (∑ n ∈ Ico 10752 11264, mobiusTreeValue 16 mobiusTable1200001 n) = (17 : ℤ) ∧
    (∑ n ∈ Ico 10752 11264, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (309 : ℕ) ∧
    (∑ n ∈ Ico 10752 11264, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (7810861 : ℤ) ∧
    (∑ n ∈ Ico 10752 11264, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (156217170778839050024878683918 : ℤ) := by
  rcases cdemPrefixStats_10752_11008 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_11008_11264 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 10752 ≤ 11008) (by norm_num : 11008 ≤ 11264), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 10752 ≤ 11008) (by norm_num : 11008 ≤ 11264), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 10752 ≤ 11008) (by norm_num : 11008 ≤ 11264), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 10752 ≤ 11008) (by norm_num : 11008 ≤ 11264), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_10240_11264 :
    (∑ n ∈ Ico 10240 11264, mobiusTreeValue 16 mobiusTable1200001 n) = (14 : ℤ) ∧
    (∑ n ∈ Ico 10240 11264, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (616 : ℕ) ∧
    (∑ n ∈ Ico 10240 11264, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (6236084 : ℤ) ∧
    (∑ n ∈ Ico 10240 11264, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (124721530533092878909902597133 : ℤ) := by
  rcases cdemPrefixStats_10240_10752 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_10752_11264 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 10240 ≤ 10752) (by norm_num : 10752 ≤ 11264), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 10240 ≤ 10752) (by norm_num : 10752 ≤ 11264), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 10240 ≤ 10752) (by norm_num : 10752 ≤ 11264), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 10240 ≤ 10752) (by norm_num : 10752 ≤ 11264), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_11264_11328 :
    (∑ n ∈ Ico 11264 11328, mobiusTreeValue 16 mobiusTable1200001 n) = (3 : ℤ) ∧
    (∑ n ∈ Ico 11264 11328, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 11264 11328, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (1326486 : ℤ) ∧
    (∑ n ∈ Ico 11264 11328, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (26529767891515863065416660708 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_11328_11392 :
    (∑ n ∈ Ico 11328 11392, mobiusTreeValue 16 mobiusTable1200001 n) = (14 : ℤ) ∧
    (∑ n ∈ Ico 11328 11392, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 11328 11392, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (6155054 : ℤ) ∧
    (∑ n ∈ Ico 11328 11392, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (123101198007973264854989833474 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_11264_11392 :
    (∑ n ∈ Ico 11264 11392, mobiusTreeValue 16 mobiusTable1200001 n) = (17 : ℤ) ∧
    (∑ n ∈ Ico 11264 11392, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 11264 11392, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (7481540 : ℤ) ∧
    (∑ n ∈ Ico 11264 11392, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (149630965899489127920406494182 : ℤ) := by
  rcases cdemPrefixStats_11264_11328 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_11328_11392 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 11264 ≤ 11328) (by norm_num : 11328 ≤ 11392), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 11264 ≤ 11328) (by norm_num : 11328 ≤ 11392), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 11264 ≤ 11328) (by norm_num : 11328 ≤ 11392), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 11264 ≤ 11328) (by norm_num : 11328 ≤ 11392), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_11392_11456 :
    (∑ n ∈ Ico 11392 11456, mobiusTreeValue 16 mobiusTable1200001 n) = (-5 : ℤ) ∧
    (∑ n ∈ Ico 11392 11456, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 11392 11456, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-2190376 : ℤ) ∧
    (∑ n ∈ Ico 11392 11456, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-43807593360916722316689308207 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_11456_11520 :
    (∑ n ∈ Ico 11456 11520, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 11456 11520, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 11456 11520, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (3788 : ℤ) ∧
    (∑ n ∈ Ico 11456 11520, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (75755427440595795733213885 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_11392_11520 :
    (∑ n ∈ Ico 11392 11520, mobiusTreeValue 16 mobiusTable1200001 n) = (-5 : ℤ) ∧
    (∑ n ∈ Ico 11392 11520, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (79 : ℕ) ∧
    (∑ n ∈ Ico 11392 11520, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-2186588 : ℤ) ∧
    (∑ n ∈ Ico 11392 11520, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-43731837933476126520956094322 : ℤ) := by
  rcases cdemPrefixStats_11392_11456 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_11456_11520 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 11392 ≤ 11456) (by norm_num : 11456 ≤ 11520), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 11392 ≤ 11456) (by norm_num : 11456 ≤ 11520), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 11392 ≤ 11456) (by norm_num : 11456 ≤ 11520), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 11392 ≤ 11456) (by norm_num : 11456 ≤ 11520), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_11264_11520 :
    (∑ n ∈ Ico 11264 11520, mobiusTreeValue 16 mobiusTable1200001 n) = (12 : ℤ) ∧
    (∑ n ∈ Ico 11264 11520, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (156 : ℕ) ∧
    (∑ n ∈ Ico 11264 11520, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (5294952 : ℤ) ∧
    (∑ n ∈ Ico 11264 11520, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (105899127966013001399450399860 : ℤ) := by
  rcases cdemPrefixStats_11264_11392 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_11392_11520 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 11264 ≤ 11392) (by norm_num : 11392 ≤ 11520), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 11264 ≤ 11392) (by norm_num : 11392 ≤ 11520), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 11264 ≤ 11392) (by norm_num : 11392 ≤ 11520), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 11264 ≤ 11392) (by norm_num : 11392 ≤ 11520), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_11520_11584 :
    (∑ n ∈ Ico 11520 11584, mobiusTreeValue 16 mobiusTable1200001 n) = (7 : ℤ) ∧
    (∑ n ∈ Ico 11520 11584, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 11520 11584, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (3024087 : ℤ) ∧
    (∑ n ∈ Ico 11520 11584, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (60481745774439469314022088471 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_11584_11648 :
    (∑ n ∈ Ico 11584 11648, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 11584 11648, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 11584 11648, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-5959 : ℤ) ∧
    (∑ n ∈ Ico 11584 11648, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-119252001407333890401738859 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_11520_11648 :
    (∑ n ∈ Ico 11520 11648, mobiusTreeValue 16 mobiusTable1200001 n) = (7 : ℤ) ∧
    (∑ n ∈ Ico 11520 11648, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (79 : ℕ) ∧
    (∑ n ∈ Ico 11520 11648, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (3018128 : ℤ) ∧
    (∑ n ∈ Ico 11520 11648, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (60362493773032135423620349612 : ℤ) := by
  rcases cdemPrefixStats_11520_11584 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_11584_11648 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 11520 ≤ 11584) (by norm_num : 11584 ≤ 11648), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 11520 ≤ 11584) (by norm_num : 11584 ≤ 11648), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 11520 ≤ 11584) (by norm_num : 11584 ≤ 11648), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 11520 ≤ 11584) (by norm_num : 11584 ≤ 11648), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_11648_11712 :
    (∑ n ∈ Ico 11648 11712, mobiusTreeValue 16 mobiusTable1200001 n) = (6 : ℤ) ∧
    (∑ n ∈ Ico 11648 11712, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 11648 11712, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (2573887 : ℤ) ∧
    (∑ n ∈ Ico 11648 11712, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (51477719330546422810852886664 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_11712_11776 :
    (∑ n ∈ Ico 11712 11776, mobiusTreeValue 16 mobiusTable1200001 n) = (19 : ℤ) ∧
    (∑ n ∈ Ico 11712 11776, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 11712 11776, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (8085362 : ℤ) ∧
    (∑ n ∈ Ico 11712 11776, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (161707510783427961064823362884 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_11648_11776 :
    (∑ n ∈ Ico 11648 11776, mobiusTreeValue 16 mobiusTable1200001 n) = (25 : ℤ) ∧
    (∑ n ∈ Ico 11648 11776, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (75 : ℕ) ∧
    (∑ n ∈ Ico 11648 11776, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (10659249 : ℤ) ∧
    (∑ n ∈ Ico 11648 11776, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (213185230113974383875676249548 : ℤ) := by
  rcases cdemPrefixStats_11648_11712 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_11712_11776 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 11648 ≤ 11712) (by norm_num : 11712 ≤ 11776), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 11648 ≤ 11712) (by norm_num : 11712 ≤ 11776), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 11648 ≤ 11712) (by norm_num : 11712 ≤ 11776), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 11648 ≤ 11712) (by norm_num : 11712 ≤ 11776), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_11520_11776 :
    (∑ n ∈ Ico 11520 11776, mobiusTreeValue 16 mobiusTable1200001 n) = (32 : ℤ) ∧
    (∑ n ∈ Ico 11520 11776, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (154 : ℕ) ∧
    (∑ n ∈ Ico 11520 11776, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (13677377 : ℤ) ∧
    (∑ n ∈ Ico 11520 11776, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (273547723887006519299296599160 : ℤ) := by
  rcases cdemPrefixStats_11520_11648 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_11648_11776 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 11520 ≤ 11648) (by norm_num : 11648 ≤ 11776), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 11520 ≤ 11648) (by norm_num : 11648 ≤ 11776), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 11520 ≤ 11648) (by norm_num : 11648 ≤ 11776), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 11520 ≤ 11648) (by norm_num : 11648 ≤ 11776), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_11264_11776 :
    (∑ n ∈ Ico 11264 11776, mobiusTreeValue 16 mobiusTable1200001 n) = (44 : ℤ) ∧
    (∑ n ∈ Ico 11264 11776, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (310 : ℕ) ∧
    (∑ n ∈ Ico 11264 11776, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (18972329 : ℤ) ∧
    (∑ n ∈ Ico 11264 11776, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (379446851853019520698746999020 : ℤ) := by
  rcases cdemPrefixStats_11264_11520 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_11520_11776 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 11264 ≤ 11520) (by norm_num : 11520 ≤ 11776), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 11264 ≤ 11520) (by norm_num : 11520 ≤ 11776), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 11264 ≤ 11520) (by norm_num : 11520 ≤ 11776), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 11264 ≤ 11520) (by norm_num : 11520 ≤ 11776), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_11776_11840 :
    (∑ n ∈ Ico 11776 11840, mobiusTreeValue 16 mobiusTable1200001 n) = (-15 : ℤ) ∧
    (∑ n ∈ Ico 11776 11840, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 11776 11840, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-6345831 : ℤ) ∧
    (∑ n ∈ Ico 11776 11840, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-126916734434270841443095019226 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_11840_11904 :
    (∑ n ∈ Ico 11840 11904, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 11840 11904, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 11840 11904, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (2342 : ℤ) ∧
    (∑ n ∈ Ico 11840 11904, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (46878509625213337422639226 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_11776_11904 :
    (∑ n ∈ Ico 11776 11904, mobiusTreeValue 16 mobiusTable1200001 n) = (-15 : ℤ) ∧
    (∑ n ∈ Ico 11776 11904, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 11776 11904, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-6343489 : ℤ) ∧
    (∑ n ∈ Ico 11776 11904, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-126869855924645628105672380000 : ℤ) := by
  rcases cdemPrefixStats_11776_11840 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_11840_11904 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 11776 ≤ 11840) (by norm_num : 11840 ≤ 11904), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 11776 ≤ 11840) (by norm_num : 11840 ≤ 11904), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 11776 ≤ 11840) (by norm_num : 11840 ≤ 11904), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 11776 ≤ 11840) (by norm_num : 11840 ≤ 11904), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_11904_11968 :
    (∑ n ∈ Ico 11904 11968, mobiusTreeValue 16 mobiusTable1200001 n) = (-7 : ℤ) ∧
    (∑ n ∈ Ico 11904 11968, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 11904 11968, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-2930364 : ℤ) ∧
    (∑ n ∈ Ico 11904 11968, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-58607336171273783001434882807 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_11968_12032 :
    (∑ n ∈ Ico 11968 12032, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 11968 12032, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 11968 12032, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-424133 : ℤ) ∧
    (∑ n ∈ Ico 11968 12032, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-8482679754349323439281340482 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_11904_12032 :
    (∑ n ∈ Ico 11904 12032, mobiusTreeValue 16 mobiusTable1200001 n) = (-8 : ℤ) ∧
    (∑ n ∈ Ico 11904 12032, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (80 : ℕ) ∧
    (∑ n ∈ Ico 11904 12032, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-3354497 : ℤ) ∧
    (∑ n ∈ Ico 11904 12032, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-67090015925623106440716223289 : ℤ) := by
  rcases cdemPrefixStats_11904_11968 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_11968_12032 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 11904 ≤ 11968) (by norm_num : 11968 ≤ 12032), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 11904 ≤ 11968) (by norm_num : 11968 ≤ 12032), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 11904 ≤ 11968) (by norm_num : 11968 ≤ 12032), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 11904 ≤ 11968) (by norm_num : 11968 ≤ 12032), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_11776_12032 :
    (∑ n ∈ Ico 11776 12032, mobiusTreeValue 16 mobiusTable1200001 n) = (-23 : ℤ) ∧
    (∑ n ∈ Ico 11776 12032, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (157 : ℕ) ∧
    (∑ n ∈ Ico 11776 12032, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-9697986 : ℤ) ∧
    (∑ n ∈ Ico 11776 12032, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-193959871850268734546388603289 : ℤ) := by
  rcases cdemPrefixStats_11776_11904 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_11904_12032 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 11776 ≤ 11904) (by norm_num : 11904 ≤ 12032), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 11776 ≤ 11904) (by norm_num : 11904 ≤ 12032), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 11776 ≤ 11904) (by norm_num : 11904 ≤ 12032), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 11776 ≤ 11904) (by norm_num : 11904 ≤ 12032), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_12032_12096 :
    (∑ n ∈ Ico 12032 12096, mobiusTreeValue 16 mobiusTable1200001 n) = (3 : ℤ) ∧
    (∑ n ∈ Ico 12032 12096, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 12032 12096, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (1239138 : ℤ) ∧
    (∑ n ∈ Ico 12032 12096, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (24782696178760744628421225740 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_12096_12160 :
    (∑ n ∈ Ico 12096 12160, mobiusTreeValue 16 mobiusTable1200001 n) = (-5 : ℤ) ∧
    (∑ n ∈ Ico 12096 12160, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 12096 12160, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-2069307 : ℤ) ∧
    (∑ n ∈ Ico 12096 12160, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-41386211207019537875636634137 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_12032_12160 :
    (∑ n ∈ Ico 12032 12160, mobiusTreeValue 16 mobiusTable1200001 n) = (-2 : ℤ) ∧
    (∑ n ∈ Ico 12032 12160, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 12032 12160, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-830169 : ℤ) ∧
    (∑ n ∈ Ico 12032 12160, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-16603515028258793247215408397 : ℤ) := by
  rcases cdemPrefixStats_12032_12096 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_12096_12160 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 12032 ≤ 12096) (by norm_num : 12096 ≤ 12160), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 12032 ≤ 12096) (by norm_num : 12096 ≤ 12160), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 12032 ≤ 12096) (by norm_num : 12096 ≤ 12160), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 12032 ≤ 12096) (by norm_num : 12096 ≤ 12160), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_12160_12224 :
    (∑ n ∈ Ico 12160 12224, mobiusTreeValue 16 mobiusTable1200001 n) = (3 : ℤ) ∧
    (∑ n ∈ Ico 12160 12224, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 12160 12224, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (1228927 : ℤ) ∧
    (∑ n ∈ Ico 12160 12224, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (24578586220879275435893528092 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_12224_12288 :
    (∑ n ∈ Ico 12224 12288, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 12224 12288, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 12224 12288, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (405505 : ℤ) ∧
    (∑ n ∈ Ico 12224 12288, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (8110181528815277291682565337 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_12160_12288 :
    (∑ n ∈ Ico 12160 12288, mobiusTreeValue 16 mobiusTable1200001 n) = (4 : ℤ) ∧
    (∑ n ∈ Ico 12160 12288, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 12160 12288, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (1634432 : ℤ) ∧
    (∑ n ∈ Ico 12160 12288, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (32688767749694552727576093429 : ℤ) := by
  rcases cdemPrefixStats_12160_12224 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_12224_12288 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 12160 ≤ 12224) (by norm_num : 12224 ≤ 12288), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 12160 ≤ 12224) (by norm_num : 12224 ≤ 12288), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 12160 ≤ 12224) (by norm_num : 12224 ≤ 12288), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 12160 ≤ 12224) (by norm_num : 12224 ≤ 12288), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_12032_12288 :
    (∑ n ∈ Ico 12032 12288, mobiusTreeValue 16 mobiusTable1200001 n) = (2 : ℤ) ∧
    (∑ n ∈ Ico 12032 12288, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (156 : ℕ) ∧
    (∑ n ∈ Ico 12032 12288, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (804263 : ℤ) ∧
    (∑ n ∈ Ico 12032 12288, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (16085252721435759480360685032 : ℤ) := by
  rcases cdemPrefixStats_12032_12160 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_12160_12288 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 12032 ≤ 12160) (by norm_num : 12160 ≤ 12288), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 12032 ≤ 12160) (by norm_num : 12160 ≤ 12288), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 12032 ≤ 12160) (by norm_num : 12160 ≤ 12288), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 12032 ≤ 12160) (by norm_num : 12160 ≤ 12288), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_11776_12288 :
    (∑ n ∈ Ico 11776 12288, mobiusTreeValue 16 mobiusTable1200001 n) = (-21 : ℤ) ∧
    (∑ n ∈ Ico 11776 12288, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (313 : ℕ) ∧
    (∑ n ∈ Ico 11776 12288, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-8893723 : ℤ) ∧
    (∑ n ∈ Ico 11776 12288, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-177874619128832975066027918257 : ℤ) := by
  rcases cdemPrefixStats_11776_12032 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_12032_12288 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 11776 ≤ 12032) (by norm_num : 12032 ≤ 12288), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 11776 ≤ 12032) (by norm_num : 12032 ≤ 12288), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 11776 ≤ 12032) (by norm_num : 12032 ≤ 12288), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 11776 ≤ 12032) (by norm_num : 12032 ≤ 12288), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_11264_12288 :
    (∑ n ∈ Ico 11264 12288, mobiusTreeValue 16 mobiusTable1200001 n) = (23 : ℤ) ∧
    (∑ n ∈ Ico 11264 12288, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (623 : ℕ) ∧
    (∑ n ∈ Ico 11264 12288, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (10078606 : ℤ) ∧
    (∑ n ∈ Ico 11264 12288, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (201572232724186545632719080763 : ℤ) := by
  rcases cdemPrefixStats_11264_11776 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_11776_12288 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 11264 ≤ 11776) (by norm_num : 11776 ≤ 12288), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 11264 ≤ 11776) (by norm_num : 11776 ≤ 12288), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 11264 ≤ 11776) (by norm_num : 11776 ≤ 12288), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 11264 ≤ 11776) (by norm_num : 11776 ≤ 12288), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_10240_12288 :
    (∑ n ∈ Ico 10240 12288, mobiusTreeValue 16 mobiusTable1200001 n) = (37 : ℤ) ∧
    (∑ n ∈ Ico 10240 12288, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (1239 : ℕ) ∧
    (∑ n ∈ Ico 10240 12288, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (16314690 : ℤ) ∧
    (∑ n ∈ Ico 10240 12288, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (326293763257279424542621677896 : ℤ) := by
  rcases cdemPrefixStats_10240_11264 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_11264_12288 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 10240 ≤ 11264) (by norm_num : 11264 ≤ 12288), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 10240 ≤ 11264) (by norm_num : 11264 ≤ 12288), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 10240 ≤ 11264) (by norm_num : 11264 ≤ 12288), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 10240 ≤ 11264) (by norm_num : 11264 ≤ 12288), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_8192_12288 :
    (∑ n ∈ Ico 8192 12288, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 8192 12288, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (2487 : ℕ) ∧
    (∑ n ∈ Ico 8192 12288, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-4997249 : ℤ) ∧
    (∑ n ∈ Ico 8192 12288, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-99945186721065157596732046201 : ℤ) := by
  rcases cdemPrefixStats_8192_10240 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_10240_12288 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 8192 ≤ 10240) (by norm_num : 10240 ≤ 12288), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 8192 ≤ 10240) (by norm_num : 10240 ≤ 12288), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 8192 ≤ 10240) (by norm_num : 10240 ≤ 12288), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 8192 ≤ 10240) (by norm_num : 10240 ≤ 12288), hR1, hR2] <;> norm_num

theorem cdemPrefixGroup002_checked_complete :
    (∑ n ∈ Ico 8192 12288, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 8192 12288, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (2487 : ℕ) ∧
    (∑ n ∈ Ico 8192 12288, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-4997249 : ℤ) ∧
    (∑ n ∈ Ico 8192 12288, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-99945186721065157596732046201 : ℤ) := cdemPrefixStats_8192_12288
end Helfgott
#print axioms Helfgott.cdemPrefixGroup002_checked_complete

open Helfgott Finset
open scoped BigOperators

theorem solution :
    (∑ n ∈ Ico 8192 12288, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 8192 12288, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (2487 : ℕ) ∧
    (∑ n ∈ Ico 8192 12288, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-4997249 : ℤ) ∧
    (∑ n ∈ Ico 8192 12288, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-99945186721065157596732046201 : ℤ) := Helfgott.cdemPrefixGroup002_checked_complete
#print axioms solution
