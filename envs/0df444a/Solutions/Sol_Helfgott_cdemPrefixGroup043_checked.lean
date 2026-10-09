-- Prove2me | solution 1 for Helfgott.cdemPrefixGroup043_checked
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-09T02:51:14.505552+00:00
-- url     : https://prove2.me/submissions/987ec784-0cf0-4562-a8b9-de687c10f755

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
private theorem cdemPrefixStats_176128_176192 :
    (∑ n ∈ Ico 176128 176192, mobiusTreeValue 16 mobiusTable1200001 n) = (-5 : ℤ) ∧
    (∑ n ∈ Ico 176128 176192, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 176128 176192, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-141905 : ℤ) ∧
    (∑ n ∈ Ico 176128 176192, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-2838122528942733264869144379 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_176192_176256 :
    (∑ n ∈ Ico 176192 176256, mobiusTreeValue 16 mobiusTable1200001 n) = (-11 : ℤ) ∧
    (∑ n ∈ Ico 176192 176256, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 176192 176256, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-312092 : ℤ) ∧
    (∑ n ∈ Ico 176192 176256, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-6241978365123518195763551871 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_176128_176256 :
    (∑ n ∈ Ico 176128 176256, mobiusTreeValue 16 mobiusTable1200001 n) = (-16 : ℤ) ∧
    (∑ n ∈ Ico 176128 176256, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (80 : ℕ) ∧
    (∑ n ∈ Ico 176128 176256, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-453997 : ℤ) ∧
    (∑ n ∈ Ico 176128 176256, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-9080100894066251460632696250 : ℤ) := by
  rcases cdemPrefixStats_176128_176192 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_176192_176256 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 176128 ≤ 176192) (by norm_num : 176192 ≤ 176256), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 176128 ≤ 176192) (by norm_num : 176192 ≤ 176256), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 176128 ≤ 176192) (by norm_num : 176192 ≤ 176256), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 176128 ≤ 176192) (by norm_num : 176192 ≤ 176256), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_176256_176320 :
    (∑ n ∈ Ico 176256 176320, mobiusTreeValue 16 mobiusTable1200001 n) = (-5 : ℤ) ∧
    (∑ n ∈ Ico 176256 176320, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 176256 176320, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-141771 : ℤ) ∧
    (∑ n ∈ Ico 176256 176320, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-2835460309793139803914638585 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_176320_176384 :
    (∑ n ∈ Ico 176320 176384, mobiusTreeValue 16 mobiusTable1200001 n) = (-7 : ℤ) ∧
    (∑ n ∈ Ico 176320 176384, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 176320 176384, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-198493 : ℤ) ∧
    (∑ n ∈ Ico 176320 176384, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-3969957915795288757333041712 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_176256_176384 :
    (∑ n ∈ Ico 176256 176384, mobiusTreeValue 16 mobiusTable1200001 n) = (-12 : ℤ) ∧
    (∑ n ∈ Ico 176256 176384, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (76 : ℕ) ∧
    (∑ n ∈ Ico 176256 176384, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-340264 : ℤ) ∧
    (∑ n ∈ Ico 176256 176384, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-6805418225588428561247680297 : ℤ) := by
  rcases cdemPrefixStats_176256_176320 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_176320_176384 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 176256 ≤ 176320) (by norm_num : 176320 ≤ 176384), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 176256 ≤ 176320) (by norm_num : 176320 ≤ 176384), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 176256 ≤ 176320) (by norm_num : 176320 ≤ 176384), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 176256 ≤ 176320) (by norm_num : 176320 ≤ 176384), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_176128_176384 :
    (∑ n ∈ Ico 176128 176384, mobiusTreeValue 16 mobiusTable1200001 n) = (-28 : ℤ) ∧
    (∑ n ∈ Ico 176128 176384, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (156 : ℕ) ∧
    (∑ n ∈ Ico 176128 176384, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-794261 : ℤ) ∧
    (∑ n ∈ Ico 176128 176384, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-15885519119654680021880376547 : ℤ) := by
  rcases cdemPrefixStats_176128_176256 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_176256_176384 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 176128 ≤ 176256) (by norm_num : 176256 ≤ 176384), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 176128 ≤ 176256) (by norm_num : 176256 ≤ 176384), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 176128 ≤ 176256) (by norm_num : 176256 ≤ 176384), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 176128 ≤ 176256) (by norm_num : 176256 ≤ 176384), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_176384_176448 :
    (∑ n ∈ Ico 176384 176448, mobiusTreeValue 16 mobiusTable1200001 n) = (-5 : ℤ) ∧
    (∑ n ∈ Ico 176384 176448, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 176384 176448, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-141707 : ℤ) ∧
    (∑ n ∈ Ico 176384 176448, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-2834190731734060867335310966 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_176448_176512 :
    (∑ n ∈ Ico 176448 176512, mobiusTreeValue 16 mobiusTable1200001 n) = (-8 : ℤ) ∧
    (∑ n ∈ Ico 176448 176512, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 176448 176512, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-226666 : ℤ) ∧
    (∑ n ∈ Ico 176448 176512, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-4533361345609701482164046083 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_176384_176512 :
    (∑ n ∈ Ico 176384 176512, mobiusTreeValue 16 mobiusTable1200001 n) = (-13 : ℤ) ∧
    (∑ n ∈ Ico 176384 176512, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (79 : ℕ) ∧
    (∑ n ∈ Ico 176384 176512, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-368373 : ℤ) ∧
    (∑ n ∈ Ico 176384 176512, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-7367552077343762349499357049 : ℤ) := by
  rcases cdemPrefixStats_176384_176448 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_176448_176512 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 176384 ≤ 176448) (by norm_num : 176448 ≤ 176512), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 176384 ≤ 176448) (by norm_num : 176448 ≤ 176512), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 176384 ≤ 176448) (by norm_num : 176448 ≤ 176512), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 176384 ≤ 176448) (by norm_num : 176448 ≤ 176512), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_176512_176576 :
    (∑ n ∈ Ico 176512 176576, mobiusTreeValue 16 mobiusTable1200001 n) = (-12 : ℤ) ∧
    (∑ n ∈ Ico 176512 176576, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (36 : ℕ) ∧
    (∑ n ∈ Ico 176512 176576, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-339852 : ℤ) ∧
    (∑ n ∈ Ico 176512 176576, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-6797143562709815380905356108 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_176576_176640 :
    (∑ n ∈ Ico 176576 176640, mobiusTreeValue 16 mobiusTable1200001 n) = (-3 : ℤ) ∧
    (∑ n ∈ Ico 176576 176640, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 176576 176640, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-84938 : ℤ) ∧
    (∑ n ∈ Ico 176576 176640, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-1698773465069171511903169737 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_176512_176640 :
    (∑ n ∈ Ico 176512 176640, mobiusTreeValue 16 mobiusTable1200001 n) = (-15 : ℤ) ∧
    (∑ n ∈ Ico 176512 176640, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (75 : ℕ) ∧
    (∑ n ∈ Ico 176512 176640, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-424790 : ℤ) ∧
    (∑ n ∈ Ico 176512 176640, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-8495917027778986892808525845 : ℤ) := by
  rcases cdemPrefixStats_176512_176576 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_176576_176640 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 176512 ≤ 176576) (by norm_num : 176576 ≤ 176640), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 176512 ≤ 176576) (by norm_num : 176576 ≤ 176640), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 176512 ≤ 176576) (by norm_num : 176576 ≤ 176640), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 176512 ≤ 176576) (by norm_num : 176576 ≤ 176640), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_176384_176640 :
    (∑ n ∈ Ico 176384 176640, mobiusTreeValue 16 mobiusTable1200001 n) = (-28 : ℤ) ∧
    (∑ n ∈ Ico 176384 176640, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (154 : ℕ) ∧
    (∑ n ∈ Ico 176384 176640, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-793163 : ℤ) ∧
    (∑ n ∈ Ico 176384 176640, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-15863469105122749242307882894 : ℤ) := by
  rcases cdemPrefixStats_176384_176512 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_176512_176640 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 176384 ≤ 176512) (by norm_num : 176512 ≤ 176640), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 176384 ≤ 176512) (by norm_num : 176512 ≤ 176640), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 176384 ≤ 176512) (by norm_num : 176512 ≤ 176640), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 176384 ≤ 176512) (by norm_num : 176512 ≤ 176640), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_176128_176640 :
    (∑ n ∈ Ico 176128 176640, mobiusTreeValue 16 mobiusTable1200001 n) = (-56 : ℤ) ∧
    (∑ n ∈ Ico 176128 176640, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (310 : ℕ) ∧
    (∑ n ∈ Ico 176128 176640, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-1587424 : ℤ) ∧
    (∑ n ∈ Ico 176128 176640, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-31748988224777429264188259441 : ℤ) := by
  rcases cdemPrefixStats_176128_176384 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_176384_176640 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 176128 ≤ 176384) (by norm_num : 176384 ≤ 176640), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 176128 ≤ 176384) (by norm_num : 176384 ≤ 176640), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 176128 ≤ 176384) (by norm_num : 176384 ≤ 176640), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 176128 ≤ 176384) (by norm_num : 176384 ≤ 176640), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_176640_176704 :
    (∑ n ∈ Ico 176640 176704, mobiusTreeValue 16 mobiusTable1200001 n) = (4 : ℤ) ∧
    (∑ n ∈ Ico 176640 176704, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 176640 176704, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (113207 : ℤ) ∧
    (∑ n ∈ Ico 176640 176704, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (2264140297203004869319117706 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_176704_176768 :
    (∑ n ∈ Ico 176704 176768, mobiusTreeValue 16 mobiusTable1200001 n) = (6 : ℤ) ∧
    (∑ n ∈ Ico 176704 176768, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 176704 176768, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (169721 : ℤ) ∧
    (∑ n ∈ Ico 176704 176768, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (3394487581581084495164601383 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_176640_176768 :
    (∑ n ∈ Ico 176640 176768, mobiusTreeValue 16 mobiusTable1200001 n) = (10 : ℤ) ∧
    (∑ n ∈ Ico 176640 176768, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 176640 176768, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (282928 : ℤ) ∧
    (∑ n ∈ Ico 176640 176768, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (5658627878784089364483719089 : ℤ) := by
  rcases cdemPrefixStats_176640_176704 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_176704_176768 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 176640 ≤ 176704) (by norm_num : 176704 ≤ 176768), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 176640 ≤ 176704) (by norm_num : 176704 ≤ 176768), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 176640 ≤ 176704) (by norm_num : 176704 ≤ 176768), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 176640 ≤ 176704) (by norm_num : 176704 ≤ 176768), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_176768_176832 :
    (∑ n ∈ Ico 176768 176832, mobiusTreeValue 16 mobiusTable1200001 n) = (-2 : ℤ) ∧
    (∑ n ∈ Ico 176768 176832, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 176768 176832, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-56577 : ℤ) ∧
    (∑ n ∈ Ico 176768 176832, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-1131627952923890751396719502 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_176832_176896 :
    (∑ n ∈ Ico 176832 176896, mobiusTreeValue 16 mobiusTable1200001 n) = (-2 : ℤ) ∧
    (∑ n ∈ Ico 176832 176896, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 176832 176896, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-56545 : ℤ) ∧
    (∑ n ∈ Ico 176832 176896, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-1130924318225762609104184573 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_176768_176896 :
    (∑ n ∈ Ico 176768 176896, mobiusTreeValue 16 mobiusTable1200001 n) = (-4 : ℤ) ∧
    (∑ n ∈ Ico 176768 176896, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 176768 176896, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-113122 : ℤ) ∧
    (∑ n ∈ Ico 176768 176896, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-2262552271149653360500904075 : ℤ) := by
  rcases cdemPrefixStats_176768_176832 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_176832_176896 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 176768 ≤ 176832) (by norm_num : 176832 ≤ 176896), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 176768 ≤ 176832) (by norm_num : 176832 ≤ 176896), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 176768 ≤ 176832) (by norm_num : 176832 ≤ 176896), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 176768 ≤ 176832) (by norm_num : 176832 ≤ 176896), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_176640_176896 :
    (∑ n ∈ Ico 176640 176896, mobiusTreeValue 16 mobiusTable1200001 n) = (6 : ℤ) ∧
    (∑ n ∈ Ico 176640 176896, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (156 : ℕ) ∧
    (∑ n ∈ Ico 176640 176896, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (169806 : ℤ) ∧
    (∑ n ∈ Ico 176640 176896, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (3396075607634436003982815014 : ℤ) := by
  rcases cdemPrefixStats_176640_176768 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_176768_176896 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 176640 ≤ 176768) (by norm_num : 176768 ≤ 176896), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 176640 ≤ 176768) (by norm_num : 176768 ≤ 176896), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 176640 ≤ 176768) (by norm_num : 176768 ≤ 176896), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 176640 ≤ 176768) (by norm_num : 176768 ≤ 176896), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_176896_176960 :
    (∑ n ∈ Ico 176896 176960, mobiusTreeValue 16 mobiusTable1200001 n) = (-8 : ℤ) ∧
    (∑ n ∈ Ico 176896 176960, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 176896 176960, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-226103 : ℤ) ∧
    (∑ n ∈ Ico 176896 176960, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-4522118103155094616675090090 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_176960_177024 :
    (∑ n ∈ Ico 176960 177024, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 176960 177024, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 176960 177024, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-28246 : ℤ) ∧
    (∑ n ∈ Ico 176960 177024, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-564863267101347790162074585 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_176896_177024 :
    (∑ n ∈ Ico 176896 177024, mobiusTreeValue 16 mobiusTable1200001 n) = (-9 : ℤ) ∧
    (∑ n ∈ Ico 176896 177024, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (79 : ℕ) ∧
    (∑ n ∈ Ico 176896 177024, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-254349 : ℤ) ∧
    (∑ n ∈ Ico 176896 177024, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-5086981370256442406837164675 : ℤ) := by
  rcases cdemPrefixStats_176896_176960 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_176960_177024 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 176896 ≤ 176960) (by norm_num : 176960 ≤ 177024), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 176896 ≤ 176960) (by norm_num : 176960 ≤ 177024), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 176896 ≤ 176960) (by norm_num : 176960 ≤ 177024), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 176896 ≤ 176960) (by norm_num : 176960 ≤ 177024), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_177024_177088 :
    (∑ n ∈ Ico 177024 177088, mobiusTreeValue 16 mobiusTable1200001 n) = (11 : ℤ) ∧
    (∑ n ∈ Ico 177024 177088, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 177024 177088, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (310657 : ℤ) ∧
    (∑ n ∈ Ico 177024 177088, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (6213211790825268026163298052 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_177088_177152 :
    (∑ n ∈ Ico 177088 177152, mobiusTreeValue 16 mobiusTable1200001 n) = (3 : ℤ) ∧
    (∑ n ∈ Ico 177088 177152, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 177088 177152, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (84685 : ℤ) ∧
    (∑ n ∈ Ico 177088 177152, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1693722319769558106622377363 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_177024_177152 :
    (∑ n ∈ Ico 177024 177152, mobiusTreeValue 16 mobiusTable1200001 n) = (14 : ℤ) ∧
    (∑ n ∈ Ico 177024 177152, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 177024 177152, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (395342 : ℤ) ∧
    (∑ n ∈ Ico 177024 177152, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (7906934110594826132785675415 : ℤ) := by
  rcases cdemPrefixStats_177024_177088 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_177088_177152 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 177024 ≤ 177088) (by norm_num : 177088 ≤ 177152), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 177024 ≤ 177088) (by norm_num : 177088 ≤ 177152), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 177024 ≤ 177088) (by norm_num : 177088 ≤ 177152), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 177024 ≤ 177088) (by norm_num : 177088 ≤ 177152), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_176896_177152 :
    (∑ n ∈ Ico 176896 177152, mobiusTreeValue 16 mobiusTable1200001 n) = (5 : ℤ) ∧
    (∑ n ∈ Ico 176896 177152, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (157 : ℕ) ∧
    (∑ n ∈ Ico 176896 177152, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (140993 : ℤ) ∧
    (∑ n ∈ Ico 176896 177152, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (2819952740338383725948510740 : ℤ) := by
  rcases cdemPrefixStats_176896_177024 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_177024_177152 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 176896 ≤ 177024) (by norm_num : 177024 ≤ 177152), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 176896 ≤ 177024) (by norm_num : 177024 ≤ 177152), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 176896 ≤ 177024) (by norm_num : 177024 ≤ 177152), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 176896 ≤ 177024) (by norm_num : 177024 ≤ 177152), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_176640_177152 :
    (∑ n ∈ Ico 176640 177152, mobiusTreeValue 16 mobiusTable1200001 n) = (11 : ℤ) ∧
    (∑ n ∈ Ico 176640 177152, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (313 : ℕ) ∧
    (∑ n ∈ Ico 176640 177152, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (310799 : ℤ) ∧
    (∑ n ∈ Ico 176640 177152, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (6216028347972819729931325754 : ℤ) := by
  rcases cdemPrefixStats_176640_176896 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_176896_177152 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 176640 ≤ 176896) (by norm_num : 176896 ≤ 177152), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 176640 ≤ 176896) (by norm_num : 176896 ≤ 177152), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 176640 ≤ 176896) (by norm_num : 176896 ≤ 177152), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 176640 ≤ 176896) (by norm_num : 176896 ≤ 177152), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_176128_177152 :
    (∑ n ∈ Ico 176128 177152, mobiusTreeValue 16 mobiusTable1200001 n) = (-45 : ℤ) ∧
    (∑ n ∈ Ico 176128 177152, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (623 : ℕ) ∧
    (∑ n ∈ Ico 176128 177152, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-1276625 : ℤ) ∧
    (∑ n ∈ Ico 176128 177152, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-25532959876804609534256933687 : ℤ) := by
  rcases cdemPrefixStats_176128_176640 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_176640_177152 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 176128 ≤ 176640) (by norm_num : 176640 ≤ 177152), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 176128 ≤ 176640) (by norm_num : 176640 ≤ 177152), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 176128 ≤ 176640) (by norm_num : 176640 ≤ 177152), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 176128 ≤ 176640) (by norm_num : 176640 ≤ 177152), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_177152_177216 :
    (∑ n ∈ Ico 177152 177216, mobiusTreeValue 16 mobiusTable1200001 n) = (-4 : ℤ) ∧
    (∑ n ∈ Ico 177152 177216, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 177152 177216, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-112874 : ℤ) ∧
    (∑ n ∈ Ico 177152 177216, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-2257546616092840371057174861 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_177216_177280 :
    (∑ n ∈ Ico 177216 177280, mobiusTreeValue 16 mobiusTable1200001 n) = (8 : ℤ) ∧
    (∑ n ∈ Ico 177216 177280, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (36 : ℕ) ∧
    (∑ n ∈ Ico 177216 177280, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (225680 : ℤ) ∧
    (∑ n ∈ Ico 177216 177280, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (4513660161329189340223881322 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_177152_177280 :
    (∑ n ∈ Ico 177152 177280, mobiusTreeValue 16 mobiusTable1200001 n) = (4 : ℤ) ∧
    (∑ n ∈ Ico 177152 177280, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (76 : ℕ) ∧
    (∑ n ∈ Ico 177152 177280, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (112806 : ℤ) ∧
    (∑ n ∈ Ico 177152 177280, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (2256113545236348969166706461 : ℤ) := by
  rcases cdemPrefixStats_177152_177216 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_177216_177280 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 177152 ≤ 177216) (by norm_num : 177216 ≤ 177280), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 177152 ≤ 177216) (by norm_num : 177216 ≤ 177280), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 177152 ≤ 177216) (by norm_num : 177216 ≤ 177280), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 177152 ≤ 177216) (by norm_num : 177216 ≤ 177280), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_177280_177344 :
    (∑ n ∈ Ico 177280 177344, mobiusTreeValue 16 mobiusTable1200001 n) = (4 : ℤ) ∧
    (∑ n ∈ Ico 177280 177344, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 177280 177344, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (112775 : ℤ) ∧
    (∑ n ∈ Ico 177280 177344, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (2255579749672731425263071394 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_177344_177408 :
    (∑ n ∈ Ico 177344 177408, mobiusTreeValue 16 mobiusTable1200001 n) = (-7 : ℤ) ∧
    (∑ n ∈ Ico 177344 177408, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 177344 177408, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-197314 : ℤ) ∧
    (∑ n ∈ Ico 177344 177408, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-3946314050629422487731576449 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_177280_177408 :
    (∑ n ∈ Ico 177280 177408, mobiusTreeValue 16 mobiusTable1200001 n) = (-3 : ℤ) ∧
    (∑ n ∈ Ico 177280 177408, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (79 : ℕ) ∧
    (∑ n ∈ Ico 177280 177408, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-84539 : ℤ) ∧
    (∑ n ∈ Ico 177280 177408, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-1690734300956691062468505055 : ℤ) := by
  rcases cdemPrefixStats_177280_177344 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_177344_177408 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 177280 ≤ 177344) (by norm_num : 177344 ≤ 177408), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 177280 ≤ 177344) (by norm_num : 177344 ≤ 177408), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 177280 ≤ 177344) (by norm_num : 177344 ≤ 177408), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 177280 ≤ 177344) (by norm_num : 177344 ≤ 177408), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_177152_177408 :
    (∑ n ∈ Ico 177152 177408, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 177152 177408, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (155 : ℕ) ∧
    (∑ n ∈ Ico 177152 177408, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (28267 : ℤ) ∧
    (∑ n ∈ Ico 177152 177408, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (565379244279657906698201406 : ℤ) := by
  rcases cdemPrefixStats_177152_177280 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_177280_177408 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 177152 ≤ 177280) (by norm_num : 177280 ≤ 177408), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 177152 ≤ 177280) (by norm_num : 177280 ≤ 177408), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 177152 ≤ 177280) (by norm_num : 177280 ≤ 177408), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 177152 ≤ 177280) (by norm_num : 177280 ≤ 177408), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_177408_177472 :
    (∑ n ∈ Ico 177408 177472, mobiusTreeValue 16 mobiusTable1200001 n) = (-4 : ℤ) ∧
    (∑ n ∈ Ico 177408 177472, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (36 : ℕ) ∧
    (∑ n ∈ Ico 177408 177472, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-112723 : ℤ) ∧
    (∑ n ∈ Ico 177408 177472, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-2254562709724840442726550748 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_177472_177536 :
    (∑ n ∈ Ico 177472 177536, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 177472 177536, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 177472 177536, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (28162 : ℤ) ∧
    (∑ n ∈ Ico 177472 177536, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (563266048935143891189045915 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_177408_177536 :
    (∑ n ∈ Ico 177408 177536, mobiusTreeValue 16 mobiusTable1200001 n) = (-3 : ℤ) ∧
    (∑ n ∈ Ico 177408 177536, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (75 : ℕ) ∧
    (∑ n ∈ Ico 177408 177536, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-84561 : ℤ) ∧
    (∑ n ∈ Ico 177408 177536, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-1691296660789696551537504833 : ℤ) := by
  rcases cdemPrefixStats_177408_177472 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_177472_177536 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 177408 ≤ 177472) (by norm_num : 177472 ≤ 177536), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 177408 ≤ 177472) (by norm_num : 177472 ≤ 177536), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 177408 ≤ 177472) (by norm_num : 177472 ≤ 177536), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 177408 ≤ 177472) (by norm_num : 177472 ≤ 177536), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_177536_177600 :
    (∑ n ∈ Ico 177536 177600, mobiusTreeValue 16 mobiusTable1200001 n) = (3 : ℤ) ∧
    (∑ n ∈ Ico 177536 177600, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 177536 177600, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (84496 : ℤ) ∧
    (∑ n ∈ Ico 177536 177600, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1689902717081247575998800770 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_177600_177664 :
    (∑ n ∈ Ico 177600 177664, mobiusTreeValue 16 mobiusTable1200001 n) = (14 : ℤ) ∧
    (∑ n ∈ Ico 177600 177664, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 177600 177664, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (394068 : ℤ) ∧
    (∑ n ∈ Ico 177600 177664, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (7881440642790121288265963111 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_177536_177664 :
    (∑ n ∈ Ico 177536 177664, mobiusTreeValue 16 mobiusTable1200001 n) = (17 : ℤ) ∧
    (∑ n ∈ Ico 177536 177664, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (81 : ℕ) ∧
    (∑ n ∈ Ico 177536 177664, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (478564 : ℤ) ∧
    (∑ n ∈ Ico 177536 177664, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (9571343359871368864264763881 : ℤ) := by
  rcases cdemPrefixStats_177536_177600 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_177600_177664 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 177536 ≤ 177600) (by norm_num : 177600 ≤ 177664), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 177536 ≤ 177600) (by norm_num : 177600 ≤ 177664), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 177536 ≤ 177600) (by norm_num : 177600 ≤ 177664), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 177536 ≤ 177600) (by norm_num : 177600 ≤ 177664), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_177408_177664 :
    (∑ n ∈ Ico 177408 177664, mobiusTreeValue 16 mobiusTable1200001 n) = (14 : ℤ) ∧
    (∑ n ∈ Ico 177408 177664, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (156 : ℕ) ∧
    (∑ n ∈ Ico 177408 177664, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (394003 : ℤ) ∧
    (∑ n ∈ Ico 177408 177664, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (7880046699081672312727259048 : ℤ) := by
  rcases cdemPrefixStats_177408_177536 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_177536_177664 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 177408 ≤ 177536) (by norm_num : 177536 ≤ 177664), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 177408 ≤ 177536) (by norm_num : 177536 ≤ 177664), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 177408 ≤ 177536) (by norm_num : 177536 ≤ 177664), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 177408 ≤ 177536) (by norm_num : 177536 ≤ 177664), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_177152_177664 :
    (∑ n ∈ Ico 177152 177664, mobiusTreeValue 16 mobiusTable1200001 n) = (15 : ℤ) ∧
    (∑ n ∈ Ico 177152 177664, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (311 : ℕ) ∧
    (∑ n ∈ Ico 177152 177664, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (422270 : ℤ) ∧
    (∑ n ∈ Ico 177152 177664, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (8445425943361330219425460454 : ℤ) := by
  rcases cdemPrefixStats_177152_177408 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_177408_177664 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 177152 ≤ 177408) (by norm_num : 177408 ≤ 177664), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 177152 ≤ 177408) (by norm_num : 177408 ≤ 177664), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 177152 ≤ 177408) (by norm_num : 177408 ≤ 177664), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 177152 ≤ 177408) (by norm_num : 177408 ≤ 177664), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_177664_177728 :
    (∑ n ∈ Ico 177664 177728, mobiusTreeValue 16 mobiusTable1200001 n) = (5 : ℤ) ∧
    (∑ n ∈ Ico 177664 177728, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 177664 177728, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (140659 : ℤ) ∧
    (∑ n ∈ Ico 177664 177728, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (2813262313263443683432575058 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_177728_177792 :
    (∑ n ∈ Ico 177728 177792, mobiusTreeValue 16 mobiusTable1200001 n) = (-3 : ℤ) ∧
    (∑ n ∈ Ico 177728 177792, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 177728 177792, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-84355 : ℤ) ∧
    (∑ n ∈ Ico 177728 177792, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-1687165534378252531783271920 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_177664_177792 :
    (∑ n ∈ Ico 177664 177792, mobiusTreeValue 16 mobiusTable1200001 n) = (2 : ℤ) ∧
    (∑ n ∈ Ico 177664 177792, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 177664 177792, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (56304 : ℤ) ∧
    (∑ n ∈ Ico 177664 177792, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1126096778885191151649303138 : ℤ) := by
  rcases cdemPrefixStats_177664_177728 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_177728_177792 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 177664 ≤ 177728) (by norm_num : 177728 ≤ 177792), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 177664 ≤ 177728) (by norm_num : 177728 ≤ 177792), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 177664 ≤ 177728) (by norm_num : 177728 ≤ 177792), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 177664 ≤ 177728) (by norm_num : 177728 ≤ 177792), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_177792_177856 :
    (∑ n ∈ Ico 177792 177856, mobiusTreeValue 16 mobiusTable1200001 n) = (8 : ℤ) ∧
    (∑ n ∈ Ico 177792 177856, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 177792 177856, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (224930 : ℤ) ∧
    (∑ n ∈ Ico 177792 177856, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (4498602643037369668876948366 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_177856_177920 :
    (∑ n ∈ Ico 177856 177920, mobiusTreeValue 16 mobiusTable1200001 n) = (-2 : ℤ) ∧
    (∑ n ∈ Ico 177856 177920, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 177856 177920, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-56196 : ℤ) ∧
    (∑ n ∈ Ico 177856 177920, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-1123971099692864662463210386 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_177792_177920 :
    (∑ n ∈ Ico 177792 177920, mobiusTreeValue 16 mobiusTable1200001 n) = (6 : ℤ) ∧
    (∑ n ∈ Ico 177792 177920, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (80 : ℕ) ∧
    (∑ n ∈ Ico 177792 177920, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (168734 : ℤ) ∧
    (∑ n ∈ Ico 177792 177920, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (3374631543344505006413737980 : ℤ) := by
  rcases cdemPrefixStats_177792_177856 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_177856_177920 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 177792 ≤ 177856) (by norm_num : 177856 ≤ 177920), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 177792 ≤ 177856) (by norm_num : 177856 ≤ 177920), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 177792 ≤ 177856) (by norm_num : 177856 ≤ 177920), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 177792 ≤ 177856) (by norm_num : 177856 ≤ 177920), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_177664_177920 :
    (∑ n ∈ Ico 177664 177920, mobiusTreeValue 16 mobiusTable1200001 n) = (8 : ℤ) ∧
    (∑ n ∈ Ico 177664 177920, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (158 : ℕ) ∧
    (∑ n ∈ Ico 177664 177920, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (225038 : ℤ) ∧
    (∑ n ∈ Ico 177664 177920, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (4500728322229696158063041118 : ℤ) := by
  rcases cdemPrefixStats_177664_177792 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_177792_177920 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 177664 ≤ 177792) (by norm_num : 177792 ≤ 177920), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 177664 ≤ 177792) (by norm_num : 177792 ≤ 177920), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 177664 ≤ 177792) (by norm_num : 177792 ≤ 177920), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 177664 ≤ 177792) (by norm_num : 177792 ≤ 177920), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_177920_177984 :
    (∑ n ∈ Ico 177920 177984, mobiusTreeValue 16 mobiusTable1200001 n) = (-6 : ℤ) ∧
    (∑ n ∈ Ico 177920 177984, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 177920 177984, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-168575 : ℤ) ∧
    (∑ n ∈ Ico 177920 177984, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-3371550495494121103224442323 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_177984_178048 :
    (∑ n ∈ Ico 177984 178048, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 177984 178048, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 177984 178048, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-28087 : ℤ) ∧
    (∑ n ∈ Ico 177984 178048, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-561800952739403141818378632 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_177920_178048 :
    (∑ n ∈ Ico 177920 178048, mobiusTreeValue 16 mobiusTable1200001 n) = (-7 : ℤ) ∧
    (∑ n ∈ Ico 177920 178048, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 177920 178048, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-196662 : ℤ) ∧
    (∑ n ∈ Ico 177920 178048, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-3933351448233524245042820955 : ℤ) := by
  rcases cdemPrefixStats_177920_177984 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_177984_178048 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 177920 ≤ 177984) (by norm_num : 177984 ≤ 178048), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 177920 ≤ 177984) (by norm_num : 177984 ≤ 178048), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 177920 ≤ 177984) (by norm_num : 177984 ≤ 178048), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 177920 ≤ 177984) (by norm_num : 177984 ≤ 178048), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_178048_178112 :
    (∑ n ∈ Ico 178048 178112, mobiusTreeValue 16 mobiusTable1200001 n) = (12 : ℤ) ∧
    (∑ n ∈ Ico 178048 178112, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 178048 178112, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (336911 : ℤ) ∧
    (∑ n ∈ Ico 178048 178112, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (6738355358684024816792989367 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_178112_178176 :
    (∑ n ∈ Ico 178112 178176, mobiusTreeValue 16 mobiusTable1200001 n) = (10 : ℤ) ∧
    (∑ n ∈ Ico 178112 178176, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 178112 178176, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (280672 : ℤ) ∧
    (∑ n ∈ Ico 178112 178176, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (5613565576415232434201701251 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_178048_178176 :
    (∑ n ∈ Ico 178048 178176, mobiusTreeValue 16 mobiusTable1200001 n) = (22 : ℤ) ∧
    (∑ n ∈ Ico 178048 178176, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 178048 178176, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (617583 : ℤ) ∧
    (∑ n ∈ Ico 178048 178176, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (12351920935099257250994690618 : ℤ) := by
  rcases cdemPrefixStats_178048_178112 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_178112_178176 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 178048 ≤ 178112) (by norm_num : 178112 ≤ 178176), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 178048 ≤ 178112) (by norm_num : 178112 ≤ 178176), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 178048 ≤ 178112) (by norm_num : 178112 ≤ 178176), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 178048 ≤ 178112) (by norm_num : 178112 ≤ 178176), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_177920_178176 :
    (∑ n ∈ Ico 177920 178176, mobiusTreeValue 16 mobiusTable1200001 n) = (15 : ℤ) ∧
    (∑ n ∈ Ico 177920 178176, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (155 : ℕ) ∧
    (∑ n ∈ Ico 177920 178176, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (420921 : ℤ) ∧
    (∑ n ∈ Ico 177920 178176, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (8418569486865733005951869663 : ℤ) := by
  rcases cdemPrefixStats_177920_178048 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_178048_178176 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 177920 ≤ 178048) (by norm_num : 178048 ≤ 178176), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 177920 ≤ 178048) (by norm_num : 178048 ≤ 178176), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 177920 ≤ 178048) (by norm_num : 178048 ≤ 178176), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 177920 ≤ 178048) (by norm_num : 178048 ≤ 178176), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_177664_178176 :
    (∑ n ∈ Ico 177664 178176, mobiusTreeValue 16 mobiusTable1200001 n) = (23 : ℤ) ∧
    (∑ n ∈ Ico 177664 178176, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (313 : ℕ) ∧
    (∑ n ∈ Ico 177664 178176, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (645959 : ℤ) ∧
    (∑ n ∈ Ico 177664 178176, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (12919297809095429164014910781 : ℤ) := by
  rcases cdemPrefixStats_177664_177920 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_177920_178176 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 177664 ≤ 177920) (by norm_num : 177920 ≤ 178176), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 177664 ≤ 177920) (by norm_num : 177920 ≤ 178176), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 177664 ≤ 177920) (by norm_num : 177920 ≤ 178176), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 177664 ≤ 177920) (by norm_num : 177920 ≤ 178176), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_177152_178176 :
    (∑ n ∈ Ico 177152 178176, mobiusTreeValue 16 mobiusTable1200001 n) = (38 : ℤ) ∧
    (∑ n ∈ Ico 177152 178176, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (624 : ℕ) ∧
    (∑ n ∈ Ico 177152 178176, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (1068229 : ℤ) ∧
    (∑ n ∈ Ico 177152 178176, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (21364723752456759383440371235 : ℤ) := by
  rcases cdemPrefixStats_177152_177664 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_177664_178176 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 177152 ≤ 177664) (by norm_num : 177664 ≤ 178176), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 177152 ≤ 177664) (by norm_num : 177664 ≤ 178176), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 177152 ≤ 177664) (by norm_num : 177664 ≤ 178176), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 177152 ≤ 177664) (by norm_num : 177664 ≤ 178176), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_176128_178176 :
    (∑ n ∈ Ico 176128 178176, mobiusTreeValue 16 mobiusTable1200001 n) = (-7 : ℤ) ∧
    (∑ n ∈ Ico 176128 178176, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (1247 : ℕ) ∧
    (∑ n ∈ Ico 176128 178176, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-208396 : ℤ) ∧
    (∑ n ∈ Ico 176128 178176, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-4168236124347850150816562452 : ℤ) := by
  rcases cdemPrefixStats_176128_177152 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_177152_178176 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 176128 ≤ 177152) (by norm_num : 177152 ≤ 178176), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 176128 ≤ 177152) (by norm_num : 177152 ≤ 178176), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 176128 ≤ 177152) (by norm_num : 177152 ≤ 178176), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 176128 ≤ 177152) (by norm_num : 177152 ≤ 178176), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_178176_178240 :
    (∑ n ∈ Ico 178176 178240, mobiusTreeValue 16 mobiusTable1200001 n) = (2 : ℤ) ∧
    (∑ n ∈ Ico 178176 178240, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 178176 178240, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (56090 : ℤ) ∧
    (∑ n ∈ Ico 178176 178240, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1121789716847182211197057694 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_178240_178304 :
    (∑ n ∈ Ico 178240 178304, mobiusTreeValue 16 mobiusTable1200001 n) = (-3 : ℤ) ∧
    (∑ n ∈ Ico 178240 178304, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 178240 178304, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-84097 : ℤ) ∧
    (∑ n ∈ Ico 178240 178304, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-1682006820368689957004640005 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_178176_178304 :
    (∑ n ∈ Ico 178176 178304, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 178176 178304, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (75 : ℕ) ∧
    (∑ n ∈ Ico 178176 178304, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-28007 : ℤ) ∧
    (∑ n ∈ Ico 178176 178304, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-560217103521507745807582311 : ℤ) := by
  rcases cdemPrefixStats_178176_178240 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_178240_178304 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 178176 ≤ 178240) (by norm_num : 178240 ≤ 178304), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 178176 ≤ 178240) (by norm_num : 178240 ≤ 178304), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 178176 ≤ 178240) (by norm_num : 178240 ≤ 178304), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 178176 ≤ 178240) (by norm_num : 178240 ≤ 178304), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_178304_178368 :
    (∑ n ∈ Ico 178304 178368, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 178304 178368, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 178304 178368, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-28010 : ℤ) ∧
    (∑ n ∈ Ico 178304 178368, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-560192188866896346427349150 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_178368_178432 :
    (∑ n ∈ Ico 178368 178432, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 178368 178432, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 178368 178432, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (28007 : ℤ) ∧
    (∑ n ∈ Ico 178368 178432, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (560154835128648502805370359 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_178304_178432 :
    (∑ n ∈ Ico 178304 178432, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 178304 178432, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 178304 178432, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-3 : ℤ) ∧
    (∑ n ∈ Ico 178304 178432, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-37353738247843621978791 : ℤ) := by
  rcases cdemPrefixStats_178304_178368 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_178368_178432 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 178304 ≤ 178368) (by norm_num : 178368 ≤ 178432), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 178304 ≤ 178368) (by norm_num : 178368 ≤ 178432), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 178304 ≤ 178368) (by norm_num : 178368 ≤ 178432), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 178304 ≤ 178368) (by norm_num : 178368 ≤ 178432), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_178176_178432 :
    (∑ n ∈ Ico 178176 178432, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 178176 178432, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (153 : ℕ) ∧
    (∑ n ∈ Ico 178176 178432, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-28010 : ℤ) ∧
    (∑ n ∈ Ico 178176 178432, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-560254457259755589429561102 : ℤ) := by
  rcases cdemPrefixStats_178176_178304 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_178304_178432 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 178176 ≤ 178304) (by norm_num : 178304 ≤ 178432), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 178176 ≤ 178304) (by norm_num : 178304 ≤ 178432), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 178176 ≤ 178304) (by norm_num : 178304 ≤ 178432), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 178176 ≤ 178304) (by norm_num : 178304 ≤ 178432), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_178432_178496 :
    (∑ n ∈ Ico 178432 178496, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 178432 178496, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 178432 178496, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-15 : ℤ) ∧
    (∑ n ∈ Ico 178432 178496, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-301463353923255766309623 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_178496_178560 :
    (∑ n ∈ Ico 178496 178560, mobiusTreeValue 16 mobiusTable1200001 n) = (-5 : ℤ) ∧
    (∑ n ∈ Ico 178496 178560, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 178496 178560, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-140029 : ℤ) ∧
    (∑ n ∈ Ico 178496 178560, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-2800612179054776093000716771 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_178432_178560 :
    (∑ n ∈ Ico 178432 178560, mobiusTreeValue 16 mobiusTable1200001 n) = (-5 : ℤ) ∧
    (∑ n ∈ Ico 178432 178560, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (79 : ℕ) ∧
    (∑ n ∈ Ico 178432 178560, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-140044 : ℤ) ∧
    (∑ n ∈ Ico 178432 178560, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-2800913642408699348767026394 : ℤ) := by
  rcases cdemPrefixStats_178432_178496 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_178496_178560 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 178432 ≤ 178496) (by norm_num : 178496 ≤ 178560), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 178432 ≤ 178496) (by norm_num : 178496 ≤ 178560), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 178432 ≤ 178496) (by norm_num : 178496 ≤ 178560), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 178432 ≤ 178496) (by norm_num : 178496 ≤ 178560), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_178560_178624 :
    (∑ n ∈ Ico 178560 178624, mobiusTreeValue 16 mobiusTable1200001 n) = (-6 : ℤ) ∧
    (∑ n ∈ Ico 178560 178624, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 178560 178624, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-167978 : ℤ) ∧
    (∑ n ∈ Ico 178560 178624, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-3359597306543035298400778552 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_178624_178688 :
    (∑ n ∈ Ico 178624 178688, mobiusTreeValue 16 mobiusTable1200001 n) = (5 : ℤ) ∧
    (∑ n ∈ Ico 178624 178688, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 178624 178688, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (139934 : ℤ) ∧
    (∑ n ∈ Ico 178624 178688, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (2798730901343463999098347416 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_178560_178688 :
    (∑ n ∈ Ico 178560 178688, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 178560 178688, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (79 : ℕ) ∧
    (∑ n ∈ Ico 178560 178688, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-28044 : ℤ) ∧
    (∑ n ∈ Ico 178560 178688, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-560866405199571299302431136 : ℤ) := by
  rcases cdemPrefixStats_178560_178624 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_178624_178688 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 178560 ≤ 178624) (by norm_num : 178624 ≤ 178688), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 178560 ≤ 178624) (by norm_num : 178624 ≤ 178688), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 178560 ≤ 178624) (by norm_num : 178624 ≤ 178688), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 178560 ≤ 178624) (by norm_num : 178624 ≤ 178688), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_178432_178688 :
    (∑ n ∈ Ico 178432 178688, mobiusTreeValue 16 mobiusTable1200001 n) = (-6 : ℤ) ∧
    (∑ n ∈ Ico 178432 178688, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (158 : ℕ) ∧
    (∑ n ∈ Ico 178432 178688, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-168088 : ℤ) ∧
    (∑ n ∈ Ico 178432 178688, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-3361780047608270648069457530 : ℤ) := by
  rcases cdemPrefixStats_178432_178560 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_178560_178688 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 178432 ≤ 178560) (by norm_num : 178560 ≤ 178688), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 178432 ≤ 178560) (by norm_num : 178560 ≤ 178688), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 178432 ≤ 178560) (by norm_num : 178560 ≤ 178688), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 178432 ≤ 178560) (by norm_num : 178560 ≤ 178688), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_178176_178688 :
    (∑ n ∈ Ico 178176 178688, mobiusTreeValue 16 mobiusTable1200001 n) = (-7 : ℤ) ∧
    (∑ n ∈ Ico 178176 178688, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (311 : ℕ) ∧
    (∑ n ∈ Ico 178176 178688, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-196098 : ℤ) ∧
    (∑ n ∈ Ico 178176 178688, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-3922034504868026237499018632 : ℤ) := by
  rcases cdemPrefixStats_178176_178432 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_178432_178688 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 178176 ≤ 178432) (by norm_num : 178432 ≤ 178688), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 178176 ≤ 178432) (by norm_num : 178432 ≤ 178688), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 178176 ≤ 178432) (by norm_num : 178432 ≤ 178688), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 178176 ≤ 178432) (by norm_num : 178432 ≤ 178688), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_178688_178752 :
    (∑ n ∈ Ico 178688 178752, mobiusTreeValue 16 mobiusTable1200001 n) = (2 : ℤ) ∧
    (∑ n ∈ Ico 178688 178752, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 178688 178752, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (55917 : ℤ) ∧
    (∑ n ∈ Ico 178688 178752, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1118345750853507782509296169 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_178752_178816 :
    (∑ n ∈ Ico 178752 178816, mobiusTreeValue 16 mobiusTable1200001 n) = (-6 : ℤ) ∧
    (∑ n ∈ Ico 178752 178816, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 178752 178816, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-167775 : ℤ) ∧
    (∑ n ∈ Ico 178752 178816, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-3355579606492947531256753143 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_178688_178816 :
    (∑ n ∈ Ico 178688 178816, mobiusTreeValue 16 mobiusTable1200001 n) = (-4 : ℤ) ∧
    (∑ n ∈ Ico 178688 178816, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (76 : ℕ) ∧
    (∑ n ∈ Ico 178688 178816, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-111858 : ℤ) ∧
    (∑ n ∈ Ico 178688 178816, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-2237233855639439748747456974 : ℤ) := by
  rcases cdemPrefixStats_178688_178752 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_178752_178816 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 178688 ≤ 178752) (by norm_num : 178752 ≤ 178816), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 178688 ≤ 178752) (by norm_num : 178752 ≤ 178816), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 178688 ≤ 178752) (by norm_num : 178752 ≤ 178816), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 178688 ≤ 178752) (by norm_num : 178752 ≤ 178816), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_178816_178880 :
    (∑ n ∈ Ico 178816 178880, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 178816 178880, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 178816 178880, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-27977 : ℤ) ∧
    (∑ n ∈ Ico 178816 178880, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-559543595264483036601903318 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_178880_178944 :
    (∑ n ∈ Ico 178880 178944, mobiusTreeValue 16 mobiusTable1200001 n) = (-4 : ℤ) ∧
    (∑ n ∈ Ico 178880 178944, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 178880 178944, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-111786 : ℤ) ∧
    (∑ n ∈ Ico 178880 178944, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-2235660961701370006939214374 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_178816_178944 :
    (∑ n ∈ Ico 178816 178944, mobiusTreeValue 16 mobiusTable1200001 n) = (-5 : ℤ) ∧
    (∑ n ∈ Ico 178816 178944, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (79 : ℕ) ∧
    (∑ n ∈ Ico 178816 178944, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-139763 : ℤ) ∧
    (∑ n ∈ Ico 178816 178944, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-2795204556965853043541117692 : ℤ) := by
  rcases cdemPrefixStats_178816_178880 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_178880_178944 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 178816 ≤ 178880) (by norm_num : 178880 ≤ 178944), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 178816 ≤ 178880) (by norm_num : 178880 ≤ 178944), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 178816 ≤ 178880) (by norm_num : 178880 ≤ 178944), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 178816 ≤ 178880) (by norm_num : 178880 ≤ 178944), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_178688_178944 :
    (∑ n ∈ Ico 178688 178944, mobiusTreeValue 16 mobiusTable1200001 n) = (-9 : ℤ) ∧
    (∑ n ∈ Ico 178688 178944, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (155 : ℕ) ∧
    (∑ n ∈ Ico 178688 178944, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-251621 : ℤ) ∧
    (∑ n ∈ Ico 178688 178944, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-5032438412605292792288574666 : ℤ) := by
  rcases cdemPrefixStats_178688_178816 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_178816_178944 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 178688 ≤ 178816) (by norm_num : 178816 ≤ 178944), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 178688 ≤ 178816) (by norm_num : 178816 ≤ 178944), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 178688 ≤ 178816) (by norm_num : 178816 ≤ 178944), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 178688 ≤ 178816) (by norm_num : 178816 ≤ 178944), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_178944_179008 :
    (∑ n ∈ Ico 178944 179008, mobiusTreeValue 16 mobiusTable1200001 n) = (8 : ℤ) ∧
    (∑ n ∈ Ico 178944 179008, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 178944 179008, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (223462 : ℤ) ∧
    (∑ n ∈ Ico 178944 179008, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (4469248748735155927568898457 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_179008_179072 :
    (∑ n ∈ Ico 179008 179072, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 179008 179072, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 179008 179072, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-27929 : ℤ) ∧
    (∑ n ∈ Ico 179008 179072, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-558503210694565281283011160 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_178944_179072 :
    (∑ n ∈ Ico 178944 179072, mobiusTreeValue 16 mobiusTable1200001 n) = (7 : ℤ) ∧
    (∑ n ∈ Ico 178944 179072, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (79 : ℕ) ∧
    (∑ n ∈ Ico 178944 179072, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (195533 : ℤ) ∧
    (∑ n ∈ Ico 178944 179072, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (3910745538040590646285887297 : ℤ) := by
  rcases cdemPrefixStats_178944_179008 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_179008_179072 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 178944 ≤ 179008) (by norm_num : 179008 ≤ 179072), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 178944 ≤ 179008) (by norm_num : 179008 ≤ 179072), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 178944 ≤ 179008) (by norm_num : 179008 ≤ 179072), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 178944 ≤ 179008) (by norm_num : 179008 ≤ 179072), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_179072_179136 :
    (∑ n ∈ Ico 179072 179136, mobiusTreeValue 16 mobiusTable1200001 n) = (-9 : ℤ) ∧
    (∑ n ∈ Ico 179072 179136, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 179072 179136, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-251246 : ℤ) ∧
    (∑ n ∈ Ico 179072 179136, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-5025019632075608159089715941 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_179136_179200 :
    (∑ n ∈ Ico 179136 179200, mobiusTreeValue 16 mobiusTable1200001 n) = (9 : ℤ) ∧
    (∑ n ∈ Ico 179136 179200, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 179136 179200, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (251153 : ℤ) ∧
    (∑ n ∈ Ico 179136 179200, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (5023093868029583092764206765 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_179072_179200 :
    (∑ n ∈ Ico 179072 179200, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 179072 179200, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (76 : ℕ) ∧
    (∑ n ∈ Ico 179072 179200, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-93 : ℤ) ∧
    (∑ n ∈ Ico 179072 179200, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-1925764046025066325509176 : ℤ) := by
  rcases cdemPrefixStats_179072_179136 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_179136_179200 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 179072 ≤ 179136) (by norm_num : 179136 ≤ 179200), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 179072 ≤ 179136) (by norm_num : 179136 ≤ 179200), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 179072 ≤ 179136) (by norm_num : 179136 ≤ 179200), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 179072 ≤ 179136) (by norm_num : 179136 ≤ 179200), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_178944_179200 :
    (∑ n ∈ Ico 178944 179200, mobiusTreeValue 16 mobiusTable1200001 n) = (7 : ℤ) ∧
    (∑ n ∈ Ico 178944 179200, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (155 : ℕ) ∧
    (∑ n ∈ Ico 178944 179200, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (195440 : ℤ) ∧
    (∑ n ∈ Ico 178944 179200, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (3908819773994565579960378121 : ℤ) := by
  rcases cdemPrefixStats_178944_179072 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_179072_179200 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 178944 ≤ 179072) (by norm_num : 179072 ≤ 179200), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 178944 ≤ 179072) (by norm_num : 179072 ≤ 179200), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 178944 ≤ 179072) (by norm_num : 179072 ≤ 179200), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 178944 ≤ 179072) (by norm_num : 179072 ≤ 179200), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_178688_179200 :
    (∑ n ∈ Ico 178688 179200, mobiusTreeValue 16 mobiusTable1200001 n) = (-2 : ℤ) ∧
    (∑ n ∈ Ico 178688 179200, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (310 : ℕ) ∧
    (∑ n ∈ Ico 178688 179200, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-56181 : ℤ) ∧
    (∑ n ∈ Ico 178688 179200, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-1123618638610727212328196545 : ℤ) := by
  rcases cdemPrefixStats_178688_178944 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_178944_179200 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 178688 ≤ 178944) (by norm_num : 178944 ≤ 179200), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 178688 ≤ 178944) (by norm_num : 178944 ≤ 179200), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 178688 ≤ 178944) (by norm_num : 178944 ≤ 179200), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 178688 ≤ 178944) (by norm_num : 178944 ≤ 179200), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_178176_179200 :
    (∑ n ∈ Ico 178176 179200, mobiusTreeValue 16 mobiusTable1200001 n) = (-9 : ℤ) ∧
    (∑ n ∈ Ico 178176 179200, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (621 : ℕ) ∧
    (∑ n ∈ Ico 178176 179200, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-252279 : ℤ) ∧
    (∑ n ∈ Ico 178176 179200, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-5045653143478753449827215177 : ℤ) := by
  rcases cdemPrefixStats_178176_178688 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_178688_179200 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 178176 ≤ 178688) (by norm_num : 178688 ≤ 179200), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 178176 ≤ 178688) (by norm_num : 178688 ≤ 179200), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 178176 ≤ 178688) (by norm_num : 178688 ≤ 179200), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 178176 ≤ 178688) (by norm_num : 178688 ≤ 179200), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_179200_179264 :
    (∑ n ∈ Ico 179200 179264, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 179200 179264, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 179200 179264, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (27883 : ℤ) ∧
    (∑ n ∈ Ico 179200 179264, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (557696404064512185258979336 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_179264_179328 :
    (∑ n ∈ Ico 179264 179328, mobiusTreeValue 16 mobiusTable1200001 n) = (-9 : ℤ) ∧
    (∑ n ∈ Ico 179264 179328, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 179264 179328, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-250999 : ℤ) ∧
    (∑ n ∈ Ico 179264 179328, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-5020039911772255867206955739 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_179200_179328 :
    (∑ n ∈ Ico 179200 179328, mobiusTreeValue 16 mobiusTable1200001 n) = (-8 : ℤ) ∧
    (∑ n ∈ Ico 179200 179328, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 179200 179328, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-223116 : ℤ) ∧
    (∑ n ∈ Ico 179200 179328, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-4462343507707743681947976403 : ℤ) := by
  rcases cdemPrefixStats_179200_179264 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_179264_179328 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 179200 ≤ 179264) (by norm_num : 179264 ≤ 179328), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 179200 ≤ 179264) (by norm_num : 179264 ≤ 179328), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 179200 ≤ 179264) (by norm_num : 179264 ≤ 179328), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 179200 ≤ 179264) (by norm_num : 179264 ≤ 179328), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_179328_179392 :
    (∑ n ∈ Ico 179328 179392, mobiusTreeValue 16 mobiusTable1200001 n) = (11 : ℤ) ∧
    (∑ n ∈ Ico 179328 179392, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 179328 179392, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (306682 : ℤ) ∧
    (∑ n ∈ Ico 179328 179392, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (6133762622337789795344837479 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_179392_179456 :
    (∑ n ∈ Ico 179392 179456, mobiusTreeValue 16 mobiusTable1200001 n) = (-9 : ℤ) ∧
    (∑ n ∈ Ico 179392 179456, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 179392 179456, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-250833 : ℤ) ∧
    (∑ n ∈ Ico 179392 179456, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-5016737894506296852609283517 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_179328_179456 :
    (∑ n ∈ Ico 179328 179456, mobiusTreeValue 16 mobiusTable1200001 n) = (2 : ℤ) ∧
    (∑ n ∈ Ico 179328 179456, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (74 : ℕ) ∧
    (∑ n ∈ Ico 179328 179456, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (55849 : ℤ) ∧
    (∑ n ∈ Ico 179328 179456, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1117024727831492942735553962 : ℤ) := by
  rcases cdemPrefixStats_179328_179392 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_179392_179456 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 179328 ≤ 179392) (by norm_num : 179392 ≤ 179456), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 179328 ≤ 179392) (by norm_num : 179392 ≤ 179456), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 179328 ≤ 179392) (by norm_num : 179392 ≤ 179456), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 179328 ≤ 179392) (by norm_num : 179392 ≤ 179456), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_179200_179456 :
    (∑ n ∈ Ico 179200 179456, mobiusTreeValue 16 mobiusTable1200001 n) = (-6 : ℤ) ∧
    (∑ n ∈ Ico 179200 179456, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (152 : ℕ) ∧
    (∑ n ∈ Ico 179200 179456, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-167267 : ℤ) ∧
    (∑ n ∈ Ico 179200 179456, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-3345318779876250739212422441 : ℤ) := by
  rcases cdemPrefixStats_179200_179328 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_179328_179456 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 179200 ≤ 179328) (by norm_num : 179328 ≤ 179456), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 179200 ≤ 179328) (by norm_num : 179328 ≤ 179456), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 179200 ≤ 179328) (by norm_num : 179328 ≤ 179456), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 179200 ≤ 179328) (by norm_num : 179328 ≤ 179456), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_179456_179520 :
    (∑ n ∈ Ico 179456 179520, mobiusTreeValue 16 mobiusTable1200001 n) = (2 : ℤ) ∧
    (∑ n ∈ Ico 179456 179520, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (42 : ℕ) ∧
    (∑ n ∈ Ico 179456 179520, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (55677 : ℤ) ∧
    (∑ n ∈ Ico 179456 179520, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1113572872688027216347364480 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_179520_179584 :
    (∑ n ∈ Ico 179520 179584, mobiusTreeValue 16 mobiusTable1200001 n) = (-16 : ℤ) ∧
    (∑ n ∈ Ico 179520 179584, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 179520 179584, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-445539 : ℤ) ∧
    (∑ n ∈ Ico 179520 179584, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-8910931150817818539889080655 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_179456_179584 :
    (∑ n ∈ Ico 179456 179584, mobiusTreeValue 16 mobiusTable1200001 n) = (-14 : ℤ) ∧
    (∑ n ∈ Ico 179456 179584, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (82 : ℕ) ∧
    (∑ n ∈ Ico 179456 179584, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-389862 : ℤ) ∧
    (∑ n ∈ Ico 179456 179584, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-7797358278129791323541716175 : ℤ) := by
  rcases cdemPrefixStats_179456_179520 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_179520_179584 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 179456 ≤ 179520) (by norm_num : 179520 ≤ 179584), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 179456 ≤ 179520) (by norm_num : 179520 ≤ 179584), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 179456 ≤ 179520) (by norm_num : 179520 ≤ 179584), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 179456 ≤ 179520) (by norm_num : 179520 ≤ 179584), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_179584_179648 :
    (∑ n ∈ Ico 179584 179648, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 179584 179648, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 179584 179648, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (27825 : ℤ) ∧
    (∑ n ∈ Ico 179584 179648, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (556538726415537352077790068 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_179648_179712 :
    (∑ n ∈ Ico 179648 179712, mobiusTreeValue 16 mobiusTable1200001 n) = (-8 : ℤ) ∧
    (∑ n ∈ Ico 179648 179712, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 179648 179712, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-222611 : ℤ) ∧
    (∑ n ∈ Ico 179648 179712, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-4452319549421159869124489758 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_179584_179712 :
    (∑ n ∈ Ico 179584 179712, mobiusTreeValue 16 mobiusTable1200001 n) = (-7 : ℤ) ∧
    (∑ n ∈ Ico 179584 179712, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 179584 179712, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-194786 : ℤ) ∧
    (∑ n ∈ Ico 179584 179712, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-3895780823005622517046699690 : ℤ) := by
  rcases cdemPrefixStats_179584_179648 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_179648_179712 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 179584 ≤ 179648) (by norm_num : 179648 ≤ 179712), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 179584 ≤ 179648) (by norm_num : 179648 ≤ 179712), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 179584 ≤ 179648) (by norm_num : 179648 ≤ 179712), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 179584 ≤ 179648) (by norm_num : 179648 ≤ 179712), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_179456_179712 :
    (∑ n ∈ Ico 179456 179712, mobiusTreeValue 16 mobiusTable1200001 n) = (-21 : ℤ) ∧
    (∑ n ∈ Ico 179456 179712, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (159 : ℕ) ∧
    (∑ n ∈ Ico 179456 179712, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-584648 : ℤ) ∧
    (∑ n ∈ Ico 179456 179712, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-11693139101135413840588415865 : ℤ) := by
  rcases cdemPrefixStats_179456_179584 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_179584_179712 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 179456 ≤ 179584) (by norm_num : 179584 ≤ 179712), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 179456 ≤ 179584) (by norm_num : 179584 ≤ 179712), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 179456 ≤ 179584) (by norm_num : 179584 ≤ 179712), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 179456 ≤ 179584) (by norm_num : 179584 ≤ 179712), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_179200_179712 :
    (∑ n ∈ Ico 179200 179712, mobiusTreeValue 16 mobiusTable1200001 n) = (-27 : ℤ) ∧
    (∑ n ∈ Ico 179200 179712, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (311 : ℕ) ∧
    (∑ n ∈ Ico 179200 179712, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-751915 : ℤ) ∧
    (∑ n ∈ Ico 179200 179712, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-15038457881011664579800838306 : ℤ) := by
  rcases cdemPrefixStats_179200_179456 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_179456_179712 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 179200 ≤ 179456) (by norm_num : 179456 ≤ 179712), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 179200 ≤ 179456) (by norm_num : 179456 ≤ 179712), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 179200 ≤ 179456) (by norm_num : 179456 ≤ 179712), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 179200 ≤ 179456) (by norm_num : 179456 ≤ 179712), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_179712_179776 :
    (∑ n ∈ Ico 179712 179776, mobiusTreeValue 16 mobiusTable1200001 n) = (-5 : ℤ) ∧
    (∑ n ∈ Ico 179712 179776, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 179712 179776, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-139090 : ℤ) ∧
    (∑ n ∈ Ico 179712 179776, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-2781891977439963648259707621 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_179776_179840 :
    (∑ n ∈ Ico 179776 179840, mobiusTreeValue 16 mobiusTable1200001 n) = (-4 : ℤ) ∧
    (∑ n ∈ Ico 179776 179840, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 179776 179840, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-111217 : ℤ) ∧
    (∑ n ∈ Ico 179776 179840, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-2224406441141526264612498462 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_179712_179840 :
    (∑ n ∈ Ico 179712 179840, mobiusTreeValue 16 mobiusTable1200001 n) = (-9 : ℤ) ∧
    (∑ n ∈ Ico 179712 179840, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 179712 179840, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-250307 : ℤ) ∧
    (∑ n ∈ Ico 179712 179840, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-5006298418581489912872206083 : ℤ) := by
  rcases cdemPrefixStats_179712_179776 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_179776_179840 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 179712 ≤ 179776) (by norm_num : 179776 ≤ 179840), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 179712 ≤ 179776) (by norm_num : 179776 ≤ 179840), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 179712 ≤ 179776) (by norm_num : 179776 ≤ 179840), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 179712 ≤ 179776) (by norm_num : 179776 ≤ 179840), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_179840_179904 :
    (∑ n ∈ Ico 179840 179904, mobiusTreeValue 16 mobiusTable1200001 n) = (-7 : ℤ) ∧
    (∑ n ∈ Ico 179840 179904, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 179840 179904, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-194565 : ℤ) ∧
    (∑ n ∈ Ico 179840 179904, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-3891319484536585167943779929 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_179904_179968 :
    (∑ n ∈ Ico 179904 179968, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 179904 179968, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 179904 179968, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (11 : ℤ) ∧
    (∑ n ∈ Ico 179904 179968, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (200737756299487739478305 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_179840_179968 :
    (∑ n ∈ Ico 179840 179968, mobiusTreeValue 16 mobiusTable1200001 n) = (-7 : ℤ) ∧
    (∑ n ∈ Ico 179840 179968, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (79 : ℕ) ∧
    (∑ n ∈ Ico 179840 179968, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-194554 : ℤ) ∧
    (∑ n ∈ Ico 179840 179968, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-3891118746780285680204301624 : ℤ) := by
  rcases cdemPrefixStats_179840_179904 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_179904_179968 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 179840 ≤ 179904) (by norm_num : 179904 ≤ 179968), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 179840 ≤ 179904) (by norm_num : 179904 ≤ 179968), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 179840 ≤ 179904) (by norm_num : 179904 ≤ 179968), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 179840 ≤ 179904) (by norm_num : 179904 ≤ 179968), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_179712_179968 :
    (∑ n ∈ Ico 179712 179968, mobiusTreeValue 16 mobiusTable1200001 n) = (-16 : ℤ) ∧
    (∑ n ∈ Ico 179712 179968, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (156 : ℕ) ∧
    (∑ n ∈ Ico 179712 179968, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-444861 : ℤ) ∧
    (∑ n ∈ Ico 179712 179968, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-8897417165361775593076507707 : ℤ) := by
  rcases cdemPrefixStats_179712_179840 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_179840_179968 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 179712 ≤ 179840) (by norm_num : 179840 ≤ 179968), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 179712 ≤ 179840) (by norm_num : 179840 ≤ 179968), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 179712 ≤ 179840) (by norm_num : 179840 ≤ 179968), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 179712 ≤ 179840) (by norm_num : 179840 ≤ 179968), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_179968_180032 :
    (∑ n ∈ Ico 179968 180032, mobiusTreeValue 16 mobiusTable1200001 n) = (6 : ℤ) ∧
    (∑ n ∈ Ico 179968 180032, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (36 : ℕ) ∧
    (∑ n ∈ Ico 179968 180032, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (166647 : ℤ) ∧
    (∑ n ∈ Ico 179968 180032, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (3333012356954992306864917815 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_180032_180096 :
    (∑ n ∈ Ico 180032 180096, mobiusTreeValue 16 mobiusTable1200001 n) = (-2 : ℤ) ∧
    (∑ n ∈ Ico 180032 180096, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 180032 180096, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-55512 : ℤ) ∧
    (∑ n ∈ Ico 180032 180096, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-1110225810697728621241682487 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_179968_180096 :
    (∑ n ∈ Ico 179968 180096, mobiusTreeValue 16 mobiusTable1200001 n) = (4 : ℤ) ∧
    (∑ n ∈ Ico 179968 180096, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (76 : ℕ) ∧
    (∑ n ∈ Ico 179968 180096, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (111135 : ℤ) ∧
    (∑ n ∈ Ico 179968 180096, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (2222786546257263685623235328 : ℤ) := by
  rcases cdemPrefixStats_179968_180032 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_180032_180096 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 179968 ≤ 180032) (by norm_num : 180032 ≤ 180096), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 179968 ≤ 180032) (by norm_num : 180032 ≤ 180096), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 179968 ≤ 180032) (by norm_num : 180032 ≤ 180096), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 179968 ≤ 180032) (by norm_num : 180032 ≤ 180096), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_180096_180160 :
    (∑ n ∈ Ico 180096 180160, mobiusTreeValue 16 mobiusTable1200001 n) = (13 : ℤ) ∧
    (∑ n ∈ Ico 180096 180160, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 180096 180160, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (360831 : ℤ) ∧
    (∑ n ∈ Ico 180096 180160, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (7216658653039359691297111970 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_180160_180224 :
    (∑ n ∈ Ico 180160 180224, mobiusTreeValue 16 mobiusTable1200001 n) = (9 : ℤ) ∧
    (∑ n ∈ Ico 180160 180224, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 180160 180224, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (249725 : ℤ) ∧
    (∑ n ∈ Ico 180160 180224, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (4994573824779597525618735780 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_180096_180224 :
    (∑ n ∈ Ico 180096 180224, mobiusTreeValue 16 mobiusTable1200001 n) = (22 : ℤ) ∧
    (∑ n ∈ Ico 180096 180224, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 180096 180224, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (610556 : ℤ) ∧
    (∑ n ∈ Ico 180096 180224, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (12211232477818957216915847750 : ℤ) := by
  rcases cdemPrefixStats_180096_180160 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_180160_180224 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 180096 ≤ 180160) (by norm_num : 180160 ≤ 180224), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 180096 ≤ 180160) (by norm_num : 180160 ≤ 180224), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 180096 ≤ 180160) (by norm_num : 180160 ≤ 180224), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 180096 ≤ 180160) (by norm_num : 180160 ≤ 180224), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_179968_180224 :
    (∑ n ∈ Ico 179968 180224, mobiusTreeValue 16 mobiusTable1200001 n) = (26 : ℤ) ∧
    (∑ n ∈ Ico 179968 180224, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (154 : ℕ) ∧
    (∑ n ∈ Ico 179968 180224, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (721691 : ℤ) ∧
    (∑ n ∈ Ico 179968 180224, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (14434019024076220902539083078 : ℤ) := by
  rcases cdemPrefixStats_179968_180096 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_180096_180224 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 179968 ≤ 180096) (by norm_num : 180096 ≤ 180224), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 179968 ≤ 180096) (by norm_num : 180096 ≤ 180224), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 179968 ≤ 180096) (by norm_num : 180096 ≤ 180224), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 179968 ≤ 180096) (by norm_num : 180096 ≤ 180224), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_179712_180224 :
    (∑ n ∈ Ico 179712 180224, mobiusTreeValue 16 mobiusTable1200001 n) = (10 : ℤ) ∧
    (∑ n ∈ Ico 179712 180224, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (310 : ℕ) ∧
    (∑ n ∈ Ico 179712 180224, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (276830 : ℤ) ∧
    (∑ n ∈ Ico 179712 180224, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (5536601858714445309462575371 : ℤ) := by
  rcases cdemPrefixStats_179712_179968 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_179968_180224 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 179712 ≤ 179968) (by norm_num : 179968 ≤ 180224), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 179712 ≤ 179968) (by norm_num : 179968 ≤ 180224), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 179712 ≤ 179968) (by norm_num : 179968 ≤ 180224), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 179712 ≤ 179968) (by norm_num : 179968 ≤ 180224), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_179200_180224 :
    (∑ n ∈ Ico 179200 180224, mobiusTreeValue 16 mobiusTable1200001 n) = (-17 : ℤ) ∧
    (∑ n ∈ Ico 179200 180224, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (621 : ℕ) ∧
    (∑ n ∈ Ico 179200 180224, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-475085 : ℤ) ∧
    (∑ n ∈ Ico 179200 180224, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-9501856022297219270338262935 : ℤ) := by
  rcases cdemPrefixStats_179200_179712 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_179712_180224 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 179200 ≤ 179712) (by norm_num : 179712 ≤ 180224), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 179200 ≤ 179712) (by norm_num : 179712 ≤ 180224), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 179200 ≤ 179712) (by norm_num : 179712 ≤ 180224), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 179200 ≤ 179712) (by norm_num : 179712 ≤ 180224), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_178176_180224 :
    (∑ n ∈ Ico 178176 180224, mobiusTreeValue 16 mobiusTable1200001 n) = (-26 : ℤ) ∧
    (∑ n ∈ Ico 178176 180224, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (1242 : ℕ) ∧
    (∑ n ∈ Ico 178176 180224, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-727364 : ℤ) ∧
    (∑ n ∈ Ico 178176 180224, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-14547509165775972720165478112 : ℤ) := by
  rcases cdemPrefixStats_178176_179200 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_179200_180224 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 178176 ≤ 179200) (by norm_num : 179200 ≤ 180224), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 178176 ≤ 179200) (by norm_num : 179200 ≤ 180224), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 178176 ≤ 179200) (by norm_num : 179200 ≤ 180224), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 178176 ≤ 179200) (by norm_num : 179200 ≤ 180224), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_176128_180224 :
    (∑ n ∈ Ico 176128 180224, mobiusTreeValue 16 mobiusTable1200001 n) = (-33 : ℤ) ∧
    (∑ n ∈ Ico 176128 180224, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (2489 : ℕ) ∧
    (∑ n ∈ Ico 176128 180224, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-935760 : ℤ) ∧
    (∑ n ∈ Ico 176128 180224, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-18715745290123822870982040564 : ℤ) := by
  rcases cdemPrefixStats_176128_178176 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_178176_180224 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 176128 ≤ 178176) (by norm_num : 178176 ≤ 180224), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 176128 ≤ 178176) (by norm_num : 178176 ≤ 180224), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 176128 ≤ 178176) (by norm_num : 178176 ≤ 180224), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 176128 ≤ 178176) (by norm_num : 178176 ≤ 180224), hR1, hR2] <;> norm_num

theorem cdemPrefixGroup043_checked_complete :
    (∑ n ∈ Ico 176128 180224, mobiusTreeValue 16 mobiusTable1200001 n) = (-33 : ℤ) ∧
    (∑ n ∈ Ico 176128 180224, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (2489 : ℕ) ∧
    (∑ n ∈ Ico 176128 180224, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-935760 : ℤ) ∧
    (∑ n ∈ Ico 176128 180224, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-18715745290123822870982040564 : ℤ) := cdemPrefixStats_176128_180224
end Helfgott
#print axioms Helfgott.cdemPrefixGroup043_checked_complete

open Helfgott Finset
open scoped BigOperators

theorem solution :
    (∑ n ∈ Ico 176128 180224, mobiusTreeValue 16 mobiusTable1200001 n) = (-33 : ℤ) ∧
    (∑ n ∈ Ico 176128 180224, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (2489 : ℕ) ∧
    (∑ n ∈ Ico 176128 180224, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-935760 : ℤ) ∧
    (∑ n ∈ Ico 176128 180224, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-18715745290123822870982040564 : ℤ) := Helfgott.cdemPrefixGroup043_checked_complete
#print axioms solution
