-- Prove2me | solution 1 for Helfgott.cdemPrefixGroup021_checked
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-09T01:56:03.461044+00:00
-- url     : https://prove2.me/submissions/36e9b678-aa5c-4d7b-aefc-95aa3725827c

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
private theorem cdemPrefixStats_86016_86080 :
    (∑ n ∈ Ico 86016 86080, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 86016 86080, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 86016 86080, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-57986 : ℤ) ∧
    (∑ n ∈ Ico 86016 86080, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-1159684881853071404955445668 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_86080_86144 :
    (∑ n ∈ Ico 86080 86144, mobiusTreeValue 16 mobiusTable1200001 n) = (-2 : ℤ) ∧
    (∑ n ∈ Ico 86080 86144, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 86080 86144, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-116142 : ℤ) ∧
    (∑ n ∈ Ico 86080 86144, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-2322826889357147967220036495 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_86016_86144 :
    (∑ n ∈ Ico 86016 86144, mobiusTreeValue 16 mobiusTable1200001 n) = (-3 : ℤ) ∧
    (∑ n ∈ Ico 86016 86144, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 86016 86144, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-174128 : ℤ) ∧
    (∑ n ∈ Ico 86016 86144, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-3482511771210219372175482163 : ℤ) := by
  rcases cdemPrefixStats_86016_86080 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_86080_86144 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 86016 ≤ 86080) (by norm_num : 86080 ≤ 86144), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 86016 ≤ 86080) (by norm_num : 86080 ≤ 86144), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 86016 ≤ 86080) (by norm_num : 86080 ≤ 86144), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 86016 ≤ 86080) (by norm_num : 86080 ≤ 86144), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_86144_86208 :
    (∑ n ∈ Ico 86144 86208, mobiusTreeValue 16 mobiusTable1200001 n) = (-5 : ℤ) ∧
    (∑ n ∈ Ico 86144 86208, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 86144 86208, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-290079 : ℤ) ∧
    (∑ n ∈ Ico 86144 86208, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-5801662249666830840902276116 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_86208_86272 :
    (∑ n ∈ Ico 86208 86272, mobiusTreeValue 16 mobiusTable1200001 n) = (-4 : ℤ) ∧
    (∑ n ∈ Ico 86208 86272, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 86208 86272, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-231981 : ℤ) ∧
    (∑ n ∈ Ico 86208 86272, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-4639617676396151730222980061 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_86144_86272 :
    (∑ n ∈ Ico 86144 86272, mobiusTreeValue 16 mobiusTable1200001 n) = (-9 : ℤ) ∧
    (∑ n ∈ Ico 86144 86272, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (79 : ℕ) ∧
    (∑ n ∈ Ico 86144 86272, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-522060 : ℤ) ∧
    (∑ n ∈ Ico 86144 86272, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-10441279926062982571125256177 : ℤ) := by
  rcases cdemPrefixStats_86144_86208 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_86208_86272 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 86144 ≤ 86208) (by norm_num : 86208 ≤ 86272), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 86144 ≤ 86208) (by norm_num : 86208 ≤ 86272), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 86144 ≤ 86208) (by norm_num : 86208 ≤ 86272), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 86144 ≤ 86208) (by norm_num : 86208 ≤ 86272), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_86016_86272 :
    (∑ n ∈ Ico 86016 86272, mobiusTreeValue 16 mobiusTable1200001 n) = (-12 : ℤ) ∧
    (∑ n ∈ Ico 86016 86272, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (156 : ℕ) ∧
    (∑ n ∈ Ico 86016 86272, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-696188 : ℤ) ∧
    (∑ n ∈ Ico 86016 86272, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-13923791697273201943300738340 : ℤ) := by
  rcases cdemPrefixStats_86016_86144 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_86144_86272 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 86016 ≤ 86144) (by norm_num : 86144 ≤ 86272), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 86016 ≤ 86144) (by norm_num : 86144 ≤ 86272), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 86016 ≤ 86144) (by norm_num : 86144 ≤ 86272), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 86016 ≤ 86144) (by norm_num : 86144 ≤ 86272), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_86272_86336 :
    (∑ n ∈ Ico 86272 86336, mobiusTreeValue 16 mobiusTable1200001 n) = (-4 : ℤ) ∧
    (∑ n ∈ Ico 86272 86336, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 86272 86336, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-231692 : ℤ) ∧
    (∑ n ∈ Ico 86272 86336, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-4633866790146199819598861446 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_86336_86400 :
    (∑ n ∈ Ico 86336 86400, mobiusTreeValue 16 mobiusTable1200001 n) = (-8 : ℤ) ∧
    (∑ n ∈ Ico 86336 86400, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (36 : ℕ) ∧
    (∑ n ∈ Ico 86336 86400, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-463187 : ℤ) ∧
    (∑ n ∈ Ico 86336 86400, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-9263857157022840510672109567 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_86272_86400 :
    (∑ n ∈ Ico 86272 86400, mobiusTreeValue 16 mobiusTable1200001 n) = (-12 : ℤ) ∧
    (∑ n ∈ Ico 86272 86400, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (74 : ℕ) ∧
    (∑ n ∈ Ico 86272 86400, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-694879 : ℤ) ∧
    (∑ n ∈ Ico 86272 86400, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-13897723947169040330270971013 : ℤ) := by
  rcases cdemPrefixStats_86272_86336 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_86336_86400 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 86272 ≤ 86336) (by norm_num : 86336 ≤ 86400), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 86272 ≤ 86336) (by norm_num : 86336 ≤ 86400), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 86272 ≤ 86336) (by norm_num : 86336 ≤ 86400), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 86272 ≤ 86336) (by norm_num : 86336 ≤ 86400), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_86400_86464 :
    (∑ n ∈ Ico 86400 86464, mobiusTreeValue 16 mobiusTable1200001 n) = (-5 : ℤ) ∧
    (∑ n ∈ Ico 86400 86464, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 86400 86464, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-289205 : ℤ) ∧
    (∑ n ∈ Ico 86400 86464, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-5784171716498793390868114805 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_86464_86528 :
    (∑ n ∈ Ico 86464 86528, mobiusTreeValue 16 mobiusTable1200001 n) = (-3 : ℤ) ∧
    (∑ n ∈ Ico 86464 86528, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 86464 86528, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-173444 : ℤ) ∧
    (∑ n ∈ Ico 86464 86528, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-3468889995996488217137710549 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_86400_86528 :
    (∑ n ∈ Ico 86400 86528, mobiusTreeValue 16 mobiusTable1200001 n) = (-8 : ℤ) ∧
    (∑ n ∈ Ico 86400 86528, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 86400 86528, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-462649 : ℤ) ∧
    (∑ n ∈ Ico 86400 86528, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-9253061712495281608005825354 : ℤ) := by
  rcases cdemPrefixStats_86400_86464 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_86464_86528 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 86400 ≤ 86464) (by norm_num : 86464 ≤ 86528), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 86400 ≤ 86464) (by norm_num : 86464 ≤ 86528), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 86400 ≤ 86464) (by norm_num : 86464 ≤ 86528), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 86400 ≤ 86464) (by norm_num : 86464 ≤ 86528), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_86272_86528 :
    (∑ n ∈ Ico 86272 86528, mobiusTreeValue 16 mobiusTable1200001 n) = (-20 : ℤ) ∧
    (∑ n ∈ Ico 86272 86528, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (152 : ℕ) ∧
    (∑ n ∈ Ico 86272 86528, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-1157528 : ℤ) ∧
    (∑ n ∈ Ico 86272 86528, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-23150785659664321938276796367 : ℤ) := by
  rcases cdemPrefixStats_86272_86400 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_86400_86528 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 86272 ≤ 86400) (by norm_num : 86400 ≤ 86528), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 86272 ≤ 86400) (by norm_num : 86400 ≤ 86528), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 86272 ≤ 86400) (by norm_num : 86400 ≤ 86528), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 86272 ≤ 86400) (by norm_num : 86400 ≤ 86528), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_86016_86528 :
    (∑ n ∈ Ico 86016 86528, mobiusTreeValue 16 mobiusTable1200001 n) = (-32 : ℤ) ∧
    (∑ n ∈ Ico 86016 86528, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (308 : ℕ) ∧
    (∑ n ∈ Ico 86016 86528, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-1853716 : ℤ) ∧
    (∑ n ∈ Ico 86016 86528, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-37074577356937523881577534707 : ℤ) := by
  rcases cdemPrefixStats_86016_86272 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_86272_86528 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 86016 ≤ 86272) (by norm_num : 86272 ≤ 86528), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 86016 ≤ 86272) (by norm_num : 86272 ≤ 86528), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 86016 ≤ 86272) (by norm_num : 86272 ≤ 86528), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 86016 ≤ 86272) (by norm_num : 86272 ≤ 86528), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_86528_86592 :
    (∑ n ∈ Ico 86528 86592, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 86528 86592, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 86528 86592, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (57731 : ℤ) ∧
    (∑ n ∈ Ico 86528 86592, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1154600865954847485809832726 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_86592_86656 :
    (∑ n ∈ Ico 86592 86656, mobiusTreeValue 16 mobiusTable1200001 n) = (13 : ℤ) ∧
    (∑ n ∈ Ico 86592 86656, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 86592 86656, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (750316 : ℤ) ∧
    (∑ n ∈ Ico 86592 86656, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (15006402931029831959139978328 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_86528_86656 :
    (∑ n ∈ Ico 86528 86656, mobiusTreeValue 16 mobiusTable1200001 n) = (14 : ℤ) ∧
    (∑ n ∈ Ico 86528 86656, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (80 : ℕ) ∧
    (∑ n ∈ Ico 86528 86656, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (808047 : ℤ) ∧
    (∑ n ∈ Ico 86528 86656, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (16161003796984679444949811054 : ℤ) := by
  rcases cdemPrefixStats_86528_86592 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_86592_86656 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 86528 ≤ 86592) (by norm_num : 86592 ≤ 86656), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 86528 ≤ 86592) (by norm_num : 86592 ≤ 86656), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 86528 ≤ 86592) (by norm_num : 86592 ≤ 86656), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 86528 ≤ 86592) (by norm_num : 86592 ≤ 86656), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_86656_86720 :
    (∑ n ∈ Ico 86656 86720, mobiusTreeValue 16 mobiusTable1200001 n) = (-2 : ℤ) ∧
    (∑ n ∈ Ico 86656 86720, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 86656 86720, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-115348 : ℤ) ∧
    (∑ n ∈ Ico 86656 86720, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-2306937788727920764129952918 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_86720_86784 :
    (∑ n ∈ Ico 86720 86784, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 86720 86784, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 86720 86784, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-57730 : ℤ) ∧
    (∑ n ∈ Ico 86720 86784, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-1154611627906453080675542215 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_86656_86784 :
    (∑ n ∈ Ico 86656 86784, mobiusTreeValue 16 mobiusTable1200001 n) = (-3 : ℤ) ∧
    (∑ n ∈ Ico 86656 86784, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 86656 86784, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-173078 : ℤ) ∧
    (∑ n ∈ Ico 86656 86784, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-3461549416634373844805495133 : ℤ) := by
  rcases cdemPrefixStats_86656_86720 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_86720_86784 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 86656 ≤ 86720) (by norm_num : 86720 ≤ 86784), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 86656 ≤ 86720) (by norm_num : 86720 ≤ 86784), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 86656 ≤ 86720) (by norm_num : 86720 ≤ 86784), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 86656 ≤ 86720) (by norm_num : 86720 ≤ 86784), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_86528_86784 :
    (∑ n ∈ Ico 86528 86784, mobiusTreeValue 16 mobiusTable1200001 n) = (11 : ℤ) ∧
    (∑ n ∈ Ico 86528 86784, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (157 : ℕ) ∧
    (∑ n ∈ Ico 86528 86784, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (634969 : ℤ) ∧
    (∑ n ∈ Ico 86528 86784, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (12699454380350305600144315921 : ℤ) := by
  rcases cdemPrefixStats_86528_86656 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_86656_86784 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 86528 ≤ 86656) (by norm_num : 86656 ≤ 86784), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 86528 ≤ 86656) (by norm_num : 86656 ≤ 86784), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 86528 ≤ 86656) (by norm_num : 86656 ≤ 86784), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 86528 ≤ 86656) (by norm_num : 86656 ≤ 86784), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_86784_86848 :
    (∑ n ∈ Ico 86784 86848, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 86784 86848, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (42 : ℕ) ∧
    (∑ n ∈ Ico 86784 86848, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-3 : ℤ) ∧
    (∑ n ∈ Ico 86784 86848, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-40021619672911184268854 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_86848_86912 :
    (∑ n ∈ Ico 86848 86912, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 86848 86912, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 86848 86912, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-57703 : ℤ) ∧
    (∑ n ∈ Ico 86848 86912, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-1154073193263526692294370308 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_86784_86912 :
    (∑ n ∈ Ico 86784 86912, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 86784 86912, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (81 : ℕ) ∧
    (∑ n ∈ Ico 86784 86912, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-57706 : ℤ) ∧
    (∑ n ∈ Ico 86784 86912, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-1154113214883199603478639162 : ℤ) := by
  rcases cdemPrefixStats_86784_86848 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_86848_86912 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 86784 ≤ 86848) (by norm_num : 86848 ≤ 86912), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 86784 ≤ 86848) (by norm_num : 86848 ≤ 86912), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 86784 ≤ 86848) (by norm_num : 86848 ≤ 86912), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 86784 ≤ 86848) (by norm_num : 86848 ≤ 86912), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_86912_86976 :
    (∑ n ∈ Ico 86912 86976, mobiusTreeValue 16 mobiusTable1200001 n) = (-2 : ℤ) ∧
    (∑ n ∈ Ico 86912 86976, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 86912 86976, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-115045 : ℤ) ∧
    (∑ n ∈ Ico 86912 86976, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-2300939646318680128783444814 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_86976_87040 :
    (∑ n ∈ Ico 86976 87040, mobiusTreeValue 16 mobiusTable1200001 n) = (-7 : ℤ) ∧
    (∑ n ∈ Ico 86976 87040, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 86976 87040, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-402282 : ℤ) ∧
    (∑ n ∈ Ico 86976 87040, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-8045699929762918254826877579 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_86912_87040 :
    (∑ n ∈ Ico 86912 87040, mobiusTreeValue 16 mobiusTable1200001 n) = (-9 : ℤ) ∧
    (∑ n ∈ Ico 86912 87040, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (75 : ℕ) ∧
    (∑ n ∈ Ico 86912 87040, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-517327 : ℤ) ∧
    (∑ n ∈ Ico 86912 87040, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-10346639576081598383610322393 : ℤ) := by
  rcases cdemPrefixStats_86912_86976 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_86976_87040 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 86912 ≤ 86976) (by norm_num : 86976 ≤ 87040), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 86912 ≤ 86976) (by norm_num : 86976 ≤ 87040), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 86912 ≤ 86976) (by norm_num : 86976 ≤ 87040), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 86912 ≤ 86976) (by norm_num : 86976 ≤ 87040), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_86784_87040 :
    (∑ n ∈ Ico 86784 87040, mobiusTreeValue 16 mobiusTable1200001 n) = (-10 : ℤ) ∧
    (∑ n ∈ Ico 86784 87040, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (156 : ℕ) ∧
    (∑ n ∈ Ico 86784 87040, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-575033 : ℤ) ∧
    (∑ n ∈ Ico 86784 87040, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-11500752790964797987088961555 : ℤ) := by
  rcases cdemPrefixStats_86784_86912 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_86912_87040 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 86784 ≤ 86912) (by norm_num : 86912 ≤ 87040), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 86784 ≤ 86912) (by norm_num : 86912 ≤ 87040), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 86784 ≤ 86912) (by norm_num : 86912 ≤ 87040), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 86784 ≤ 86912) (by norm_num : 86912 ≤ 87040), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_86528_87040 :
    (∑ n ∈ Ico 86528 87040, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 86528 87040, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (313 : ℕ) ∧
    (∑ n ∈ Ico 86528 87040, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (59936 : ℤ) ∧
    (∑ n ∈ Ico 86528 87040, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1198701589385507613055354366 : ℤ) := by
  rcases cdemPrefixStats_86528_86784 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_86784_87040 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 86528 ≤ 86784) (by norm_num : 86784 ≤ 87040), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 86528 ≤ 86784) (by norm_num : 86784 ≤ 87040), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 86528 ≤ 86784) (by norm_num : 86784 ≤ 87040), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 86528 ≤ 86784) (by norm_num : 86784 ≤ 87040), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_86016_87040 :
    (∑ n ∈ Ico 86016 87040, mobiusTreeValue 16 mobiusTable1200001 n) = (-31 : ℤ) ∧
    (∑ n ∈ Ico 86016 87040, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (621 : ℕ) ∧
    (∑ n ∈ Ico 86016 87040, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-1793780 : ℤ) ∧
    (∑ n ∈ Ico 86016 87040, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-35875875767552016268522180341 : ℤ) := by
  rcases cdemPrefixStats_86016_86528 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_86528_87040 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 86016 ≤ 86528) (by norm_num : 86528 ≤ 87040), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 86016 ≤ 86528) (by norm_num : 86528 ≤ 87040), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 86016 ≤ 86528) (by norm_num : 86528 ≤ 87040), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 86016 ≤ 86528) (by norm_num : 86528 ≤ 87040), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_87040_87104 :
    (∑ n ∈ Ico 87040 87104, mobiusTreeValue 16 mobiusTable1200001 n) = (8 : ℤ) ∧
    (∑ n ∈ Ico 87040 87104, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 87040 87104, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (459359 : ℤ) ∧
    (∑ n ∈ Ico 87040 87104, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (9187257979177186548672982971 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_87104_87168 :
    (∑ n ∈ Ico 87104 87168, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 87104 87168, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 87104 87168, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (57242 : ℤ) ∧
    (∑ n ∈ Ico 87104 87168, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1144839279696693640055817197 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_87040_87168 :
    (∑ n ∈ Ico 87040 87168, mobiusTreeValue 16 mobiusTable1200001 n) = (9 : ℤ) ∧
    (∑ n ∈ Ico 87040 87168, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (79 : ℕ) ∧
    (∑ n ∈ Ico 87040 87168, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (516601 : ℤ) ∧
    (∑ n ∈ Ico 87040 87168, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (10332097258873880188728800168 : ℤ) := by
  rcases cdemPrefixStats_87040_87104 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_87104_87168 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 87040 ≤ 87104) (by norm_num : 87104 ≤ 87168), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 87040 ≤ 87104) (by norm_num : 87104 ≤ 87168), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 87040 ≤ 87104) (by norm_num : 87104 ≤ 87168), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 87040 ≤ 87104) (by norm_num : 87104 ≤ 87168), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_87168_87232 :
    (∑ n ∈ Ico 87168 87232, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 87168 87232, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 87168 87232, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (85 : ℤ) ∧
    (∑ n ∈ Ico 87168 87232, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1657567698840707956679296 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_87232_87296 :
    (∑ n ∈ Ico 87232 87296, mobiusTreeValue 16 mobiusTable1200001 n) = (-6 : ℤ) ∧
    (∑ n ∈ Ico 87232 87296, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (36 : ℕ) ∧
    (∑ n ∈ Ico 87232 87296, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-343765 : ℤ) ∧
    (∑ n ∈ Ico 87232 87296, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-6875372915916205341720320762 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_87168_87296 :
    (∑ n ∈ Ico 87168 87296, mobiusTreeValue 16 mobiusTable1200001 n) = (-6 : ℤ) ∧
    (∑ n ∈ Ico 87168 87296, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (76 : ℕ) ∧
    (∑ n ∈ Ico 87168 87296, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-343680 : ℤ) ∧
    (∑ n ∈ Ico 87168 87296, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-6873715348217364633763641466 : ℤ) := by
  rcases cdemPrefixStats_87168_87232 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_87232_87296 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 87168 ≤ 87232) (by norm_num : 87232 ≤ 87296), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 87168 ≤ 87232) (by norm_num : 87232 ≤ 87296), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 87168 ≤ 87232) (by norm_num : 87232 ≤ 87296), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 87168 ≤ 87232) (by norm_num : 87232 ≤ 87296), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_87040_87296 :
    (∑ n ∈ Ico 87040 87296, mobiusTreeValue 16 mobiusTable1200001 n) = (3 : ℤ) ∧
    (∑ n ∈ Ico 87040 87296, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (155 : ℕ) ∧
    (∑ n ∈ Ico 87040 87296, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (172921 : ℤ) ∧
    (∑ n ∈ Ico 87040 87296, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (3458381910656515554965158702 : ℤ) := by
  rcases cdemPrefixStats_87040_87168 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_87168_87296 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 87040 ≤ 87168) (by norm_num : 87168 ≤ 87296), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 87040 ≤ 87168) (by norm_num : 87168 ≤ 87296), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 87040 ≤ 87168) (by norm_num : 87168 ≤ 87296), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 87040 ≤ 87168) (by norm_num : 87168 ≤ 87296), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_87296_87360 :
    (∑ n ∈ Ico 87296 87360, mobiusTreeValue 16 mobiusTable1200001 n) = (-5 : ℤ) ∧
    (∑ n ∈ Ico 87296 87360, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 87296 87360, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-286292 : ℤ) ∧
    (∑ n ∈ Ico 87296 87360, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-5725881544050655494125108213 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_87360_87424 :
    (∑ n ∈ Ico 87360 87424, mobiusTreeValue 16 mobiusTable1200001 n) = (4 : ℤ) ∧
    (∑ n ∈ Ico 87360 87424, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 87360 87424, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (228818 : ℤ) ∧
    (∑ n ∈ Ico 87360 87424, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (4576384195098740613552400535 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_87296_87424 :
    (∑ n ∈ Ico 87296 87424, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 87296 87424, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (79 : ℕ) ∧
    (∑ n ∈ Ico 87296 87424, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-57474 : ℤ) ∧
    (∑ n ∈ Ico 87296 87424, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-1149497348951914880572707678 : ℤ) := by
  rcases cdemPrefixStats_87296_87360 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_87360_87424 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 87296 ≤ 87360) (by norm_num : 87360 ≤ 87424), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 87296 ≤ 87360) (by norm_num : 87360 ≤ 87424), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 87296 ≤ 87360) (by norm_num : 87360 ≤ 87424), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 87296 ≤ 87360) (by norm_num : 87360 ≤ 87424), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_87424_87488 :
    (∑ n ∈ Ico 87424 87488, mobiusTreeValue 16 mobiusTable1200001 n) = (5 : ℤ) ∧
    (∑ n ∈ Ico 87424 87488, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 87424 87488, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (285783 : ℤ) ∧
    (∑ n ∈ Ico 87424 87488, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (5715722667589142867109500074 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_87488_87552 :
    (∑ n ∈ Ico 87488 87552, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 87488 87552, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 87488 87552, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (57167 : ℤ) ∧
    (∑ n ∈ Ico 87488 87552, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1143327408031317742111260473 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_87424_87552 :
    (∑ n ∈ Ico 87424 87552, mobiusTreeValue 16 mobiusTable1200001 n) = (6 : ℤ) ∧
    (∑ n ∈ Ico 87424 87552, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (76 : ℕ) ∧
    (∑ n ∈ Ico 87424 87552, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (342950 : ℤ) ∧
    (∑ n ∈ Ico 87424 87552, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (6859050075620460609220760547 : ℤ) := by
  rcases cdemPrefixStats_87424_87488 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_87488_87552 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 87424 ≤ 87488) (by norm_num : 87488 ≤ 87552), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 87424 ≤ 87488) (by norm_num : 87488 ≤ 87552), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 87424 ≤ 87488) (by norm_num : 87488 ≤ 87552), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 87424 ≤ 87488) (by norm_num : 87488 ≤ 87552), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_87296_87552 :
    (∑ n ∈ Ico 87296 87552, mobiusTreeValue 16 mobiusTable1200001 n) = (5 : ℤ) ∧
    (∑ n ∈ Ico 87296 87552, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (155 : ℕ) ∧
    (∑ n ∈ Ico 87296 87552, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (285476 : ℤ) ∧
    (∑ n ∈ Ico 87296 87552, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (5709552726668545728648052869 : ℤ) := by
  rcases cdemPrefixStats_87296_87424 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_87424_87552 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 87296 ≤ 87424) (by norm_num : 87424 ≤ 87552), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 87296 ≤ 87424) (by norm_num : 87424 ≤ 87552), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 87296 ≤ 87424) (by norm_num : 87424 ≤ 87552), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 87296 ≤ 87424) (by norm_num : 87424 ≤ 87552), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_87040_87552 :
    (∑ n ∈ Ico 87040 87552, mobiusTreeValue 16 mobiusTable1200001 n) = (8 : ℤ) ∧
    (∑ n ∈ Ico 87040 87552, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (310 : ℕ) ∧
    (∑ n ∈ Ico 87040 87552, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (458397 : ℤ) ∧
    (∑ n ∈ Ico 87040 87552, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (9167934637325061283613211571 : ℤ) := by
  rcases cdemPrefixStats_87040_87296 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_87296_87552 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 87040 ≤ 87296) (by norm_num : 87296 ≤ 87552), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 87040 ≤ 87296) (by norm_num : 87296 ≤ 87552), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 87040 ≤ 87296) (by norm_num : 87296 ≤ 87552), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 87040 ≤ 87296) (by norm_num : 87296 ≤ 87552), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_87552_87616 :
    (∑ n ∈ Ico 87552 87616, mobiusTreeValue 16 mobiusTable1200001 n) = (7 : ℤ) ∧
    (∑ n ∈ Ico 87552 87616, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 87552 87616, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (399608 : ℤ) ∧
    (∑ n ∈ Ico 87552 87616, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (7992288093033935171602347783 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_87616_87680 :
    (∑ n ∈ Ico 87616 87680, mobiusTreeValue 16 mobiusTable1200001 n) = (-13 : ℤ) ∧
    (∑ n ∈ Ico 87616 87680, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 87616 87680, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-741596 : ℤ) ∧
    (∑ n ∈ Ico 87616 87680, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-14832055317267116512191218868 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_87552_87680 :
    (∑ n ∈ Ico 87552 87680, mobiusTreeValue 16 mobiusTable1200001 n) = (-6 : ℤ) ∧
    (∑ n ∈ Ico 87552 87680, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 87552 87680, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-341988 : ℤ) ∧
    (∑ n ∈ Ico 87552 87680, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-6839767224233181340588871085 : ℤ) := by
  rcases cdemPrefixStats_87552_87616 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_87616_87680 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 87552 ≤ 87616) (by norm_num : 87616 ≤ 87680), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 87552 ≤ 87616) (by norm_num : 87616 ≤ 87680), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 87552 ≤ 87616) (by norm_num : 87616 ≤ 87680), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 87552 ≤ 87616) (by norm_num : 87616 ≤ 87680), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_87680_87744 :
    (∑ n ∈ Ico 87680 87744, mobiusTreeValue 16 mobiusTable1200001 n) = (-6 : ℤ) ∧
    (∑ n ∈ Ico 87680 87744, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 87680 87744, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-342022 : ℤ) ∧
    (∑ n ∈ Ico 87680 87744, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-6840517883986895329724811811 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_87744_87808 :
    (∑ n ∈ Ico 87744 87808, mobiusTreeValue 16 mobiusTable1200001 n) = (-8 : ℤ) ∧
    (∑ n ∈ Ico 87744 87808, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (42 : ℕ) ∧
    (∑ n ∈ Ico 87744 87808, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-455665 : ℤ) ∧
    (∑ n ∈ Ico 87744 87808, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-9113408036348628952030449221 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_87680_87808 :
    (∑ n ∈ Ico 87680 87808, mobiusTreeValue 16 mobiusTable1200001 n) = (-14 : ℤ) ∧
    (∑ n ∈ Ico 87680 87808, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (82 : ℕ) ∧
    (∑ n ∈ Ico 87680 87808, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-797687 : ℤ) ∧
    (∑ n ∈ Ico 87680 87808, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-15953925920335524281755261032 : ℤ) := by
  rcases cdemPrefixStats_87680_87744 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_87744_87808 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 87680 ≤ 87744) (by norm_num : 87744 ≤ 87808), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 87680 ≤ 87744) (by norm_num : 87744 ≤ 87808), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 87680 ≤ 87744) (by norm_num : 87744 ≤ 87808), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 87680 ≤ 87744) (by norm_num : 87744 ≤ 87808), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_87552_87808 :
    (∑ n ∈ Ico 87552 87808, mobiusTreeValue 16 mobiusTable1200001 n) = (-20 : ℤ) ∧
    (∑ n ∈ Ico 87552 87808, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (160 : ℕ) ∧
    (∑ n ∈ Ico 87552 87808, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-1139675 : ℤ) ∧
    (∑ n ∈ Ico 87552 87808, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-22793693144568705622344132117 : ℤ) := by
  rcases cdemPrefixStats_87552_87680 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_87680_87808 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 87552 ≤ 87680) (by norm_num : 87680 ≤ 87808), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 87552 ≤ 87680) (by norm_num : 87680 ≤ 87808), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 87552 ≤ 87680) (by norm_num : 87680 ≤ 87808), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 87552 ≤ 87680) (by norm_num : 87680 ≤ 87808), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_87808_87872 :
    (∑ n ∈ Ico 87808 87872, mobiusTreeValue 16 mobiusTable1200001 n) = (7 : ℤ) ∧
    (∑ n ∈ Ico 87808 87872, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 87808 87872, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (398455 : ℤ) ∧
    (∑ n ∈ Ico 87808 87872, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (7969190655913940583366123338 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_87872_87936 :
    (∑ n ∈ Ico 87872 87936, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 87872 87936, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 87872 87936, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-117 : ℤ) ∧
    (∑ n ∈ Ico 87872 87936, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-2290815522019206017727957 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_87808_87936 :
    (∑ n ∈ Ico 87808 87936, mobiusTreeValue 16 mobiusTable1200001 n) = (7 : ℤ) ∧
    (∑ n ∈ Ico 87808 87936, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 87808 87936, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (398338 : ℤ) ∧
    (∑ n ∈ Ico 87808 87936, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (7966899840391921377348395381 : ℤ) := by
  rcases cdemPrefixStats_87808_87872 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_87872_87936 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 87808 ≤ 87872) (by norm_num : 87872 ≤ 87936), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 87808 ≤ 87872) (by norm_num : 87872 ≤ 87936), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 87808 ≤ 87872) (by norm_num : 87872 ≤ 87936), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 87808 ≤ 87872) (by norm_num : 87872 ≤ 87936), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_87936_88000 :
    (∑ n ∈ Ico 87936 88000, mobiusTreeValue 16 mobiusTable1200001 n) = (2 : ℤ) ∧
    (∑ n ∈ Ico 87936 88000, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 87936 88000, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (113687 : ℤ) ∧
    (∑ n ∈ Ico 87936 88000, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (2273760877378904913354201212 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_88000_88064 :
    (∑ n ∈ Ico 88000 88064, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 88000 88064, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 88000 88064, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (56563 : ℤ) ∧
    (∑ n ∈ Ico 88000 88064, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1131201932637791045232318669 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_87936_88064 :
    (∑ n ∈ Ico 87936 88064, mobiusTreeValue 16 mobiusTable1200001 n) = (3 : ℤ) ∧
    (∑ n ∈ Ico 87936 88064, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (79 : ℕ) ∧
    (∑ n ∈ Ico 87936 88064, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (170250 : ℤ) ∧
    (∑ n ∈ Ico 87936 88064, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (3404962810016695958586519881 : ℤ) := by
  rcases cdemPrefixStats_87936_88000 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_88000_88064 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 87936 ≤ 88000) (by norm_num : 88000 ≤ 88064), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 87936 ≤ 88000) (by norm_num : 88000 ≤ 88064), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 87936 ≤ 88000) (by norm_num : 88000 ≤ 88064), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 87936 ≤ 88000) (by norm_num : 88000 ≤ 88064), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_87808_88064 :
    (∑ n ∈ Ico 87808 88064, mobiusTreeValue 16 mobiusTable1200001 n) = (10 : ℤ) ∧
    (∑ n ∈ Ico 87808 88064, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (156 : ℕ) ∧
    (∑ n ∈ Ico 87808 88064, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (568588 : ℤ) ∧
    (∑ n ∈ Ico 87808 88064, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (11371862650408617335934915262 : ℤ) := by
  rcases cdemPrefixStats_87808_87936 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_87936_88064 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 87808 ≤ 87936) (by norm_num : 87936 ≤ 88064), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 87808 ≤ 87936) (by norm_num : 87936 ≤ 88064), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 87808 ≤ 87936) (by norm_num : 87936 ≤ 88064), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 87808 ≤ 87936) (by norm_num : 87936 ≤ 88064), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_87552_88064 :
    (∑ n ∈ Ico 87552 88064, mobiusTreeValue 16 mobiusTable1200001 n) = (-10 : ℤ) ∧
    (∑ n ∈ Ico 87552 88064, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (316 : ℕ) ∧
    (∑ n ∈ Ico 87552 88064, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-571087 : ℤ) ∧
    (∑ n ∈ Ico 87552 88064, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-11421830494160088286409216855 : ℤ) := by
  rcases cdemPrefixStats_87552_87808 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_87808_88064 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 87552 ≤ 87808) (by norm_num : 87808 ≤ 88064), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 87552 ≤ 87808) (by norm_num : 87808 ≤ 88064), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 87552 ≤ 87808) (by norm_num : 87808 ≤ 88064), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 87552 ≤ 87808) (by norm_num : 87808 ≤ 88064), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_87040_88064 :
    (∑ n ∈ Ico 87040 88064, mobiusTreeValue 16 mobiusTable1200001 n) = (-2 : ℤ) ∧
    (∑ n ∈ Ico 87040 88064, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (626 : ℕ) ∧
    (∑ n ∈ Ico 87040 88064, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-112690 : ℤ) ∧
    (∑ n ∈ Ico 87040 88064, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-2253895856835027002796005284 : ℤ) := by
  rcases cdemPrefixStats_87040_87552 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_87552_88064 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 87040 ≤ 87552) (by norm_num : 87552 ≤ 88064), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 87040 ≤ 87552) (by norm_num : 87552 ≤ 88064), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 87040 ≤ 87552) (by norm_num : 87552 ≤ 88064), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 87040 ≤ 87552) (by norm_num : 87552 ≤ 88064), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_86016_88064 :
    (∑ n ∈ Ico 86016 88064, mobiusTreeValue 16 mobiusTable1200001 n) = (-33 : ℤ) ∧
    (∑ n ∈ Ico 86016 88064, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (1247 : ℕ) ∧
    (∑ n ∈ Ico 86016 88064, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-1906470 : ℤ) ∧
    (∑ n ∈ Ico 86016 88064, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-38129771624387043271318185625 : ℤ) := by
  rcases cdemPrefixStats_86016_87040 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_87040_88064 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 86016 ≤ 87040) (by norm_num : 87040 ≤ 88064), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 86016 ≤ 87040) (by norm_num : 87040 ≤ 88064), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 86016 ≤ 87040) (by norm_num : 87040 ≤ 88064), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 86016 ≤ 87040) (by norm_num : 87040 ≤ 88064), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_88064_88128 :
    (∑ n ∈ Ico 88064 88128, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 88064 88128, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 88064 88128, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (56684 : ℤ) ∧
    (∑ n ∈ Ico 88064 88128, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1133656201204169828347957979 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_88128_88192 :
    (∑ n ∈ Ico 88128 88192, mobiusTreeValue 16 mobiusTable1200001 n) = (12 : ℤ) ∧
    (∑ n ∈ Ico 88128 88192, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 88128 88192, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (680615 : ℤ) ∧
    (∑ n ∈ Ico 88128 88192, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (13612426147628725649137867473 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_88064_88192 :
    (∑ n ∈ Ico 88064 88192, mobiusTreeValue 16 mobiusTable1200001 n) = (13 : ℤ) ∧
    (∑ n ∈ Ico 88064 88192, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 88064 88192, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (737299 : ℤ) ∧
    (∑ n ∈ Ico 88064 88192, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (14746082348832895477485825452 : ℤ) := by
  rcases cdemPrefixStats_88064_88128 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_88128_88192 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 88064 ≤ 88128) (by norm_num : 88128 ≤ 88192), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 88064 ≤ 88128) (by norm_num : 88128 ≤ 88192), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 88064 ≤ 88128) (by norm_num : 88128 ≤ 88192), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 88064 ≤ 88128) (by norm_num : 88128 ≤ 88192), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_88192_88256 :
    (∑ n ∈ Ico 88192 88256, mobiusTreeValue 16 mobiusTable1200001 n) = (-4 : ℤ) ∧
    (∑ n ∈ Ico 88192 88256, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 88192 88256, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-226552 : ℤ) ∧
    (∑ n ∈ Ico 88192 88256, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-4531048896243737212739568637 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_88256_88320 :
    (∑ n ∈ Ico 88256 88320, mobiusTreeValue 16 mobiusTable1200001 n) = (8 : ℤ) ∧
    (∑ n ∈ Ico 88256 88320, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 88256 88320, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (453073 : ℤ) ∧
    (∑ n ∈ Ico 88256 88320, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (9061562693777417829992817107 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_88192_88320 :
    (∑ n ∈ Ico 88192 88320, mobiusTreeValue 16 mobiusTable1200001 n) = (4 : ℤ) ∧
    (∑ n ∈ Ico 88192 88320, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (80 : ℕ) ∧
    (∑ n ∈ Ico 88192 88320, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (226521 : ℤ) ∧
    (∑ n ∈ Ico 88192 88320, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (4530513797533680617253248470 : ℤ) := by
  rcases cdemPrefixStats_88192_88256 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_88256_88320 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 88192 ≤ 88256) (by norm_num : 88256 ≤ 88320), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 88192 ≤ 88256) (by norm_num : 88256 ≤ 88320), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 88192 ≤ 88256) (by norm_num : 88256 ≤ 88320), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 88192 ≤ 88256) (by norm_num : 88256 ≤ 88320), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_88064_88320 :
    (∑ n ∈ Ico 88064 88320, mobiusTreeValue 16 mobiusTable1200001 n) = (17 : ℤ) ∧
    (∑ n ∈ Ico 88064 88320, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (157 : ℕ) ∧
    (∑ n ∈ Ico 88064 88320, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (963820 : ℤ) ∧
    (∑ n ∈ Ico 88064 88320, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (19276596146366576094739073922 : ℤ) := by
  rcases cdemPrefixStats_88064_88192 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_88192_88320 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 88064 ≤ 88192) (by norm_num : 88192 ≤ 88320), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 88064 ≤ 88192) (by norm_num : 88192 ≤ 88320), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 88064 ≤ 88192) (by norm_num : 88192 ≤ 88320), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 88064 ≤ 88192) (by norm_num : 88192 ≤ 88320), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_88320_88384 :
    (∑ n ∈ Ico 88320 88384, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 88320 88384, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 88320 88384, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (56540 : ℤ) ∧
    (∑ n ∈ Ico 88320 88384, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1130772929972273371170609231 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_88384_88448 :
    (∑ n ∈ Ico 88384 88448, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 88384 88448, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 88384 88448, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-48 : ℤ) ∧
    (∑ n ∈ Ico 88384 88448, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-921101010013346803735544 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_88320_88448 :
    (∑ n ∈ Ico 88320 88448, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 88320 88448, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 88320 88448, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (56492 : ℤ) ∧
    (∑ n ∈ Ico 88320 88448, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1129851828962260024366873687 : ℤ) := by
  rcases cdemPrefixStats_88320_88384 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_88384_88448 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 88320 ≤ 88384) (by norm_num : 88384 ≤ 88448), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 88320 ≤ 88384) (by norm_num : 88384 ≤ 88448), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 88320 ≤ 88384) (by norm_num : 88384 ≤ 88448), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 88320 ≤ 88384) (by norm_num : 88384 ≤ 88448), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_88448_88512 :
    (∑ n ∈ Ico 88448 88512, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 88448 88512, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 88448 88512, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (56503 : ℤ) ∧
    (∑ n ∈ Ico 88448 88512, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1130007604896912328658708411 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_88512_88576 :
    (∑ n ∈ Ico 88512 88576, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 88512 88576, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 88512 88576, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-56591 : ℤ) ∧
    (∑ n ∈ Ico 88512 88576, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-1131818359247888391147051828 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_88448_88576 :
    (∑ n ∈ Ico 88448 88576, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 88448 88576, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 88448 88576, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-88 : ℤ) ∧
    (∑ n ∈ Ico 88448 88576, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-1810754350976062488343417 : ℤ) := by
  rcases cdemPrefixStats_88448_88512 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_88512_88576 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 88448 ≤ 88512) (by norm_num : 88512 ≤ 88576), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 88448 ≤ 88512) (by norm_num : 88512 ≤ 88576), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 88448 ≤ 88512) (by norm_num : 88512 ≤ 88576), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 88448 ≤ 88512) (by norm_num : 88512 ≤ 88576), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_88320_88576 :
    (∑ n ∈ Ico 88320 88576, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 88320 88576, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (155 : ℕ) ∧
    (∑ n ∈ Ico 88320 88576, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (56404 : ℤ) ∧
    (∑ n ∈ Ico 88320 88576, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1128041074611283961878530270 : ℤ) := by
  rcases cdemPrefixStats_88320_88448 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_88448_88576 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 88320 ≤ 88448) (by norm_num : 88448 ≤ 88576), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 88320 ≤ 88448) (by norm_num : 88448 ≤ 88576), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 88320 ≤ 88448) (by norm_num : 88448 ≤ 88576), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 88320 ≤ 88448) (by norm_num : 88448 ≤ 88576), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_88064_88576 :
    (∑ n ∈ Ico 88064 88576, mobiusTreeValue 16 mobiusTable1200001 n) = (18 : ℤ) ∧
    (∑ n ∈ Ico 88064 88576, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (312 : ℕ) ∧
    (∑ n ∈ Ico 88064 88576, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (1020224 : ℤ) ∧
    (∑ n ∈ Ico 88064 88576, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (20404637220977860056617604192 : ℤ) := by
  rcases cdemPrefixStats_88064_88320 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_88320_88576 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 88064 ≤ 88320) (by norm_num : 88320 ≤ 88576), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 88064 ≤ 88320) (by norm_num : 88320 ≤ 88576), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 88064 ≤ 88320) (by norm_num : 88320 ≤ 88576), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 88064 ≤ 88320) (by norm_num : 88320 ≤ 88576), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_88576_88640 :
    (∑ n ∈ Ico 88576 88640, mobiusTreeValue 16 mobiusTable1200001 n) = (-2 : ℤ) ∧
    (∑ n ∈ Ico 88576 88640, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (42 : ℕ) ∧
    (∑ n ∈ Ico 88576 88640, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-112816 : ℤ) ∧
    (∑ n ∈ Ico 88576 88640, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-2256342338640326820472931172 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_88640_88704 :
    (∑ n ∈ Ico 88640 88704, mobiusTreeValue 16 mobiusTable1200001 n) = (-3 : ℤ) ∧
    (∑ n ∈ Ico 88640 88704, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 88640 88704, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-169325 : ℤ) ∧
    (∑ n ∈ Ico 88640 88704, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-3386536058651799151794221949 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_88576_88704 :
    (∑ n ∈ Ico 88576 88704, mobiusTreeValue 16 mobiusTable1200001 n) = (-5 : ℤ) ∧
    (∑ n ∈ Ico 88576 88704, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (81 : ℕ) ∧
    (∑ n ∈ Ico 88576 88704, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-282141 : ℤ) ∧
    (∑ n ∈ Ico 88576 88704, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-5642878397292125972267153121 : ℤ) := by
  rcases cdemPrefixStats_88576_88640 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_88640_88704 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 88576 ≤ 88640) (by norm_num : 88640 ≤ 88704), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 88576 ≤ 88640) (by norm_num : 88640 ≤ 88704), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 88576 ≤ 88640) (by norm_num : 88640 ≤ 88704), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 88576 ≤ 88640) (by norm_num : 88640 ≤ 88704), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_88704_88768 :
    (∑ n ∈ Ico 88704 88768, mobiusTreeValue 16 mobiusTable1200001 n) = (10 : ℤ) ∧
    (∑ n ∈ Ico 88704 88768, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 88704 88768, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (563452 : ℤ) ∧
    (∑ n ∈ Ico 88704 88768, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (11269142556564721718718426577 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_88768_88832 :
    (∑ n ∈ Ico 88768 88832, mobiusTreeValue 16 mobiusTable1200001 n) = (-7 : ℤ) ∧
    (∑ n ∈ Ico 88768 88832, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 88768 88832, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-394153 : ℤ) ∧
    (∑ n ∈ Ico 88768 88832, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-7883073216192615635929302149 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_88704_88832 :
    (∑ n ∈ Ico 88704 88832, mobiusTreeValue 16 mobiusTable1200001 n) = (3 : ℤ) ∧
    (∑ n ∈ Ico 88704 88832, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 88704 88832, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (169299 : ℤ) ∧
    (∑ n ∈ Ico 88704 88832, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (3386069340372106082789124428 : ℤ) := by
  rcases cdemPrefixStats_88704_88768 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_88768_88832 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 88704 ≤ 88768) (by norm_num : 88768 ≤ 88832), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 88704 ≤ 88768) (by norm_num : 88768 ≤ 88832), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 88704 ≤ 88768) (by norm_num : 88768 ≤ 88832), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 88704 ≤ 88768) (by norm_num : 88768 ≤ 88832), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_88576_88832 :
    (∑ n ∈ Ico 88576 88832, mobiusTreeValue 16 mobiusTable1200001 n) = (-2 : ℤ) ∧
    (∑ n ∈ Ico 88576 88832, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (158 : ℕ) ∧
    (∑ n ∈ Ico 88576 88832, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-112842 : ℤ) ∧
    (∑ n ∈ Ico 88576 88832, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-2256809056920019889478028693 : ℤ) := by
  rcases cdemPrefixStats_88576_88704 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_88704_88832 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 88576 ≤ 88704) (by norm_num : 88704 ≤ 88832), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 88576 ≤ 88704) (by norm_num : 88704 ≤ 88832), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 88576 ≤ 88704) (by norm_num : 88704 ≤ 88832), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 88576 ≤ 88704) (by norm_num : 88704 ≤ 88832), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_88832_88896 :
    (∑ n ∈ Ico 88832 88896, mobiusTreeValue 16 mobiusTable1200001 n) = (-11 : ℤ) ∧
    (∑ n ∈ Ico 88832 88896, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 88832 88896, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-618957 : ℤ) ∧
    (∑ n ∈ Ico 88832 88896, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-12379238520779964398849875024 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_88896_88960 :
    (∑ n ∈ Ico 88896 88960, mobiusTreeValue 16 mobiusTable1200001 n) = (-6 : ℤ) ∧
    (∑ n ∈ Ico 88896 88960, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 88896 88960, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-337284 : ℤ) ∧
    (∑ n ∈ Ico 88896 88960, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-6745754395415052443880081416 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_88832_88960 :
    (∑ n ∈ Ico 88832 88960, mobiusTreeValue 16 mobiusTable1200001 n) = (-17 : ℤ) ∧
    (∑ n ∈ Ico 88832 88960, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (79 : ℕ) ∧
    (∑ n ∈ Ico 88832 88960, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-956241 : ℤ) ∧
    (∑ n ∈ Ico 88832 88960, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-19124992916195016842729956440 : ℤ) := by
  rcases cdemPrefixStats_88832_88896 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_88896_88960 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 88832 ≤ 88896) (by norm_num : 88896 ≤ 88960), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 88832 ≤ 88896) (by norm_num : 88896 ≤ 88960), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 88832 ≤ 88896) (by norm_num : 88896 ≤ 88960), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 88832 ≤ 88896) (by norm_num : 88896 ≤ 88960), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_88960_89024 :
    (∑ n ∈ Ico 88960 89024, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 88960 89024, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 88960 89024, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (34 : ℤ) ∧
    (∑ n ∈ Ico 88960 89024, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (681727544269173176576263 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_89024_89088 :
    (∑ n ∈ Ico 89024 89088, mobiusTreeValue 16 mobiusTable1200001 n) = (-7 : ℤ) ∧
    (∑ n ∈ Ico 89024 89088, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 89024 89088, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-392947 : ℤ) ∧
    (∑ n ∈ Ico 89024 89088, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-7859025042964008965428862456 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_88960_89088 :
    (∑ n ∈ Ico 88960 89088, mobiusTreeValue 16 mobiusTable1200001 n) = (-7 : ℤ) ∧
    (∑ n ∈ Ico 88960 89088, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 88960 89088, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-392913 : ℤ) ∧
    (∑ n ∈ Ico 88960 89088, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-7858343315419739792252286193 : ℤ) := by
  rcases cdemPrefixStats_88960_89024 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_89024_89088 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 88960 ≤ 89024) (by norm_num : 89024 ≤ 89088), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 88960 ≤ 89024) (by norm_num : 89024 ≤ 89088), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 88960 ≤ 89024) (by norm_num : 89024 ≤ 89088), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 88960 ≤ 89024) (by norm_num : 89024 ≤ 89088), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_88832_89088 :
    (∑ n ∈ Ico 88832 89088, mobiusTreeValue 16 mobiusTable1200001 n) = (-24 : ℤ) ∧
    (∑ n ∈ Ico 88832 89088, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (156 : ℕ) ∧
    (∑ n ∈ Ico 88832 89088, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-1349154 : ℤ) ∧
    (∑ n ∈ Ico 88832 89088, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-26983336231614756634982242633 : ℤ) := by
  rcases cdemPrefixStats_88832_88960 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_88960_89088 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 88832 ≤ 88960) (by norm_num : 88960 ≤ 89088), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 88832 ≤ 88960) (by norm_num : 88960 ≤ 89088), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 88832 ≤ 88960) (by norm_num : 88960 ≤ 89088), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 88832 ≤ 88960) (by norm_num : 88960 ≤ 89088), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_88576_89088 :
    (∑ n ∈ Ico 88576 89088, mobiusTreeValue 16 mobiusTable1200001 n) = (-26 : ℤ) ∧
    (∑ n ∈ Ico 88576 89088, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (314 : ℕ) ∧
    (∑ n ∈ Ico 88576 89088, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-1461996 : ℤ) ∧
    (∑ n ∈ Ico 88576 89088, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-29240145288534776524460271326 : ℤ) := by
  rcases cdemPrefixStats_88576_88832 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_88832_89088 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 88576 ≤ 88832) (by norm_num : 88832 ≤ 89088), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 88576 ≤ 88832) (by norm_num : 88832 ≤ 89088), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 88576 ≤ 88832) (by norm_num : 88832 ≤ 89088), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 88576 ≤ 88832) (by norm_num : 88832 ≤ 89088), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_88064_89088 :
    (∑ n ∈ Ico 88064 89088, mobiusTreeValue 16 mobiusTable1200001 n) = (-8 : ℤ) ∧
    (∑ n ∈ Ico 88064 89088, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (626 : ℕ) ∧
    (∑ n ∈ Ico 88064 89088, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-441772 : ℤ) ∧
    (∑ n ∈ Ico 88064 89088, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-8835508067556916467842667134 : ℤ) := by
  rcases cdemPrefixStats_88064_88576 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_88576_89088 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 88064 ≤ 88576) (by norm_num : 88576 ≤ 89088), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 88064 ≤ 88576) (by norm_num : 88576 ≤ 89088), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 88064 ≤ 88576) (by norm_num : 88576 ≤ 89088), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 88064 ≤ 88576) (by norm_num : 88576 ≤ 89088), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_89088_89152 :
    (∑ n ∈ Ico 89088 89152, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 89088 89152, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 89088 89152, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-78 : ℤ) ∧
    (∑ n ∈ Ico 89088 89152, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-1547989213840447624311721 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_89152_89216 :
    (∑ n ∈ Ico 89152 89216, mobiusTreeValue 16 mobiusTable1200001 n) = (4 : ℤ) ∧
    (∑ n ∈ Ico 89152 89216, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 89152 89216, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (224261 : ℤ) ∧
    (∑ n ∈ Ico 89152 89216, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (4485234539576520473920325238 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_89088_89216 :
    (∑ n ∈ Ico 89088 89216, mobiusTreeValue 16 mobiusTable1200001 n) = (4 : ℤ) ∧
    (∑ n ∈ Ico 89088 89216, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 89088 89216, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (224183 : ℤ) ∧
    (∑ n ∈ Ico 89088 89216, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (4483686550362680026296013517 : ℤ) := by
  rcases cdemPrefixStats_89088_89152 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_89152_89216 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 89088 ≤ 89152) (by norm_num : 89152 ≤ 89216), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 89088 ≤ 89152) (by norm_num : 89152 ≤ 89216), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 89088 ≤ 89152) (by norm_num : 89152 ≤ 89216), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 89088 ≤ 89152) (by norm_num : 89152 ≤ 89216), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_89216_89280 :
    (∑ n ∈ Ico 89216 89280, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 89216 89280, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 89216 89280, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (55993 : ℤ) ∧
    (∑ n ∈ Ico 89216 89280, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1119883280142878642032831071 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_89280_89344 :
    (∑ n ∈ Ico 89280 89344, mobiusTreeValue 16 mobiusTable1200001 n) = (-4 : ℤ) ∧
    (∑ n ∈ Ico 89280 89344, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 89280 89344, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-223891 : ℤ) ∧
    (∑ n ∈ Ico 89280 89344, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-4477803732697513814475551480 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_89216_89344 :
    (∑ n ∈ Ico 89216 89344, mobiusTreeValue 16 mobiusTable1200001 n) = (-3 : ℤ) ∧
    (∑ n ∈ Ico 89216 89344, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 89216 89344, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-167898 : ℤ) ∧
    (∑ n ∈ Ico 89216 89344, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-3357920452554635172442720409 : ℤ) := by
  rcases cdemPrefixStats_89216_89280 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_89280_89344 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 89216 ≤ 89280) (by norm_num : 89280 ≤ 89344), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 89216 ≤ 89280) (by norm_num : 89280 ≤ 89344), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 89216 ≤ 89280) (by norm_num : 89280 ≤ 89344), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 89216 ≤ 89280) (by norm_num : 89280 ≤ 89344), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_89088_89344 :
    (∑ n ∈ Ico 89088 89344, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 89088 89344, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (155 : ℕ) ∧
    (∑ n ∈ Ico 89088 89344, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (56285 : ℤ) ∧
    (∑ n ∈ Ico 89088 89344, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1125766097808044853853293108 : ℤ) := by
  rcases cdemPrefixStats_89088_89216 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_89216_89344 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 89088 ≤ 89216) (by norm_num : 89216 ≤ 89344), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 89088 ≤ 89216) (by norm_num : 89216 ≤ 89344), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 89088 ≤ 89216) (by norm_num : 89216 ≤ 89344), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 89088 ≤ 89216) (by norm_num : 89216 ≤ 89344), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_89344_89408 :
    (∑ n ∈ Ico 89344 89408, mobiusTreeValue 16 mobiusTable1200001 n) = (6 : ℤ) ∧
    (∑ n ∈ Ico 89344 89408, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 89344 89408, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (335660 : ℤ) ∧
    (∑ n ∈ Ico 89344 89408, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (6713224462352756527485339172 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_89408_89472 :
    (∑ n ∈ Ico 89408 89472, mobiusTreeValue 16 mobiusTable1200001 n) = (-8 : ℤ) ∧
    (∑ n ∈ Ico 89408 89472, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 89408 89472, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-447246 : ℤ) ∧
    (∑ n ∈ Ico 89408 89472, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-8944994115879529195605444360 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_89344_89472 :
    (∑ n ∈ Ico 89344 89472, mobiusTreeValue 16 mobiusTable1200001 n) = (-2 : ℤ) ∧
    (∑ n ∈ Ico 89344 89472, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 89344 89472, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-111586 : ℤ) ∧
    (∑ n ∈ Ico 89344 89472, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-2231769653526772668120105188 : ℤ) := by
  rcases cdemPrefixStats_89344_89408 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_89408_89472 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 89344 ≤ 89408) (by norm_num : 89408 ≤ 89472), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 89344 ≤ 89408) (by norm_num : 89408 ≤ 89472), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 89344 ≤ 89408) (by norm_num : 89408 ≤ 89472), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 89344 ≤ 89408) (by norm_num : 89408 ≤ 89472), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_89472_89536 :
    (∑ n ∈ Ico 89472 89536, mobiusTreeValue 16 mobiusTable1200001 n) = (-10 : ℤ) ∧
    (∑ n ∈ Ico 89472 89536, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 89472 89536, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-558580 : ℤ) ∧
    (∑ n ∈ Ico 89472 89536, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-11171674203025001681616461101 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_89536_89600 :
    (∑ n ∈ Ico 89536 89600, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 89536 89600, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 89536 89600, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (22 : ℤ) ∧
    (∑ n ∈ Ico 89536 89600, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (473973895730748633674605 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_89472_89600 :
    (∑ n ∈ Ico 89472 89600, mobiusTreeValue 16 mobiusTable1200001 n) = (-10 : ℤ) ∧
    (∑ n ∈ Ico 89472 89600, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 89472 89600, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-558558 : ℤ) ∧
    (∑ n ∈ Ico 89472 89600, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-11171200229129270932982786496 : ℤ) := by
  rcases cdemPrefixStats_89472_89536 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_89536_89600 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 89472 ≤ 89536) (by norm_num : 89536 ≤ 89600), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 89472 ≤ 89536) (by norm_num : 89536 ≤ 89600), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 89472 ≤ 89536) (by norm_num : 89536 ≤ 89600), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 89472 ≤ 89536) (by norm_num : 89536 ≤ 89600), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_89344_89600 :
    (∑ n ∈ Ico 89344 89600, mobiusTreeValue 16 mobiusTable1200001 n) = (-12 : ℤ) ∧
    (∑ n ∈ Ico 89344 89600, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (156 : ℕ) ∧
    (∑ n ∈ Ico 89344 89600, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-670144 : ℤ) ∧
    (∑ n ∈ Ico 89344 89600, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-13402969882656043601102891684 : ℤ) := by
  rcases cdemPrefixStats_89344_89472 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_89472_89600 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 89344 ≤ 89472) (by norm_num : 89472 ≤ 89600), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 89344 ≤ 89472) (by norm_num : 89472 ≤ 89600), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 89344 ≤ 89472) (by norm_num : 89472 ≤ 89600), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 89344 ≤ 89472) (by norm_num : 89472 ≤ 89600), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_89088_89600 :
    (∑ n ∈ Ico 89088 89600, mobiusTreeValue 16 mobiusTable1200001 n) = (-11 : ℤ) ∧
    (∑ n ∈ Ico 89088 89600, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (311 : ℕ) ∧
    (∑ n ∈ Ico 89088 89600, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-613859 : ℤ) ∧
    (∑ n ∈ Ico 89088 89600, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-12277203784847998747249598576 : ℤ) := by
  rcases cdemPrefixStats_89088_89344 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_89344_89600 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 89088 ≤ 89344) (by norm_num : 89344 ≤ 89600), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 89088 ≤ 89344) (by norm_num : 89344 ≤ 89600), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 89088 ≤ 89344) (by norm_num : 89344 ≤ 89600), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 89088 ≤ 89344) (by norm_num : 89344 ≤ 89600), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_89600_89664 :
    (∑ n ∈ Ico 89600 89664, mobiusTreeValue 16 mobiusTable1200001 n) = (3 : ℤ) ∧
    (∑ n ∈ Ico 89600 89664, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 89600 89664, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (167328 : ℤ) ∧
    (∑ n ∈ Ico 89600 89664, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (3346595588544738266082068783 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_89664_89728 :
    (∑ n ∈ Ico 89664 89728, mobiusTreeValue 16 mobiusTable1200001 n) = (-11 : ℤ) ∧
    (∑ n ∈ Ico 89664 89728, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 89664 89728, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-613240 : ℤ) ∧
    (∑ n ∈ Ico 89664 89728, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-12264902629694396968665116384 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_89600_89728 :
    (∑ n ∈ Ico 89600 89728, mobiusTreeValue 16 mobiusTable1200001 n) = (-8 : ℤ) ∧
    (∑ n ∈ Ico 89600 89728, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 89600 89728, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-445912 : ℤ) ∧
    (∑ n ∈ Ico 89600 89728, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-8918307041149658702583047601 : ℤ) := by
  rcases cdemPrefixStats_89600_89664 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_89664_89728 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 89600 ≤ 89664) (by norm_num : 89664 ≤ 89728), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 89600 ≤ 89664) (by norm_num : 89664 ≤ 89728), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 89600 ≤ 89664) (by norm_num : 89664 ≤ 89728), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 89600 ≤ 89664) (by norm_num : 89664 ≤ 89728), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_89728_89792 :
    (∑ n ∈ Ico 89728 89792, mobiusTreeValue 16 mobiusTable1200001 n) = (6 : ℤ) ∧
    (∑ n ∈ Ico 89728 89792, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 89728 89792, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (334220 : ℤ) ∧
    (∑ n ∈ Ico 89728 89792, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (6684417886810190679700115251 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_89792_89856 :
    (∑ n ∈ Ico 89792 89856, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 89792 89856, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 89792 89856, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (55615 : ℤ) ∧
    (∑ n ∈ Ico 89792 89856, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1112321689031805538343589870 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_89728_89856 :
    (∑ n ∈ Ico 89728 89856, mobiusTreeValue 16 mobiusTable1200001 n) = (7 : ℤ) ∧
    (∑ n ∈ Ico 89728 89856, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (79 : ℕ) ∧
    (∑ n ∈ Ico 89728 89856, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (389835 : ℤ) ∧
    (∑ n ∈ Ico 89728 89856, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (7796739575841996218043705121 : ℤ) := by
  rcases cdemPrefixStats_89728_89792 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_89792_89856 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 89728 ≤ 89792) (by norm_num : 89792 ≤ 89856), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 89728 ≤ 89792) (by norm_num : 89792 ≤ 89856), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 89728 ≤ 89792) (by norm_num : 89792 ≤ 89856), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 89728 ≤ 89792) (by norm_num : 89792 ≤ 89856), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_89600_89856 :
    (∑ n ∈ Ico 89600 89856, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 89600 89856, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (157 : ℕ) ∧
    (∑ n ∈ Ico 89600 89856, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-56077 : ℤ) ∧
    (∑ n ∈ Ico 89600 89856, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-1121567465307662484539342480 : ℤ) := by
  rcases cdemPrefixStats_89600_89728 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_89728_89856 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 89600 ≤ 89728) (by norm_num : 89728 ≤ 89856), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 89600 ≤ 89728) (by norm_num : 89728 ≤ 89856), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 89600 ≤ 89728) (by norm_num : 89728 ≤ 89856), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 89600 ≤ 89728) (by norm_num : 89728 ≤ 89856), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_89856_89920 :
    (∑ n ∈ Ico 89856 89920, mobiusTreeValue 16 mobiusTable1200001 n) = (4 : ℤ) ∧
    (∑ n ∈ Ico 89856 89920, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (36 : ℕ) ∧
    (∑ n ∈ Ico 89856 89920, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (222506 : ℤ) ∧
    (∑ n ∈ Ico 89856 89920, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (4450168229130085426105608497 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_89920_89984 :
    (∑ n ∈ Ico 89920 89984, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 89920 89984, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 89920 89984, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (55699 : ℤ) ∧
    (∑ n ∈ Ico 89920 89984, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1114039795846555072171305557 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_89856_89984 :
    (∑ n ∈ Ico 89856 89984, mobiusTreeValue 16 mobiusTable1200001 n) = (5 : ℤ) ∧
    (∑ n ∈ Ico 89856 89984, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (75 : ℕ) ∧
    (∑ n ∈ Ico 89856 89984, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (278205 : ℤ) ∧
    (∑ n ∈ Ico 89856 89984, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (5564208024976640498276914054 : ℤ) := by
  rcases cdemPrefixStats_89856_89920 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_89920_89984 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 89856 ≤ 89920) (by norm_num : 89920 ≤ 89984), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 89856 ≤ 89920) (by norm_num : 89920 ≤ 89984), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 89856 ≤ 89920) (by norm_num : 89920 ≤ 89984), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 89856 ≤ 89920) (by norm_num : 89920 ≤ 89984), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_89984_90048 :
    (∑ n ∈ Ico 89984 90048, mobiusTreeValue 16 mobiusTable1200001 n) = (-4 : ℤ) ∧
    (∑ n ∈ Ico 89984 90048, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 89984 90048, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-222297 : ℤ) ∧
    (∑ n ∈ Ico 89984 90048, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-4445962302773908660986941209 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_90048_90112 :
    (∑ n ∈ Ico 90048 90112, mobiusTreeValue 16 mobiusTable1200001 n) = (-18 : ℤ) ∧
    (∑ n ∈ Ico 90048 90112, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 90048 90112, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-999066 : ℤ) ∧
    (∑ n ∈ Ico 90048 90112, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-19981523740620996756488204271 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_89984_90112 :
    (∑ n ∈ Ico 89984 90112, mobiusTreeValue 16 mobiusTable1200001 n) = (-22 : ℤ) ∧
    (∑ n ∈ Ico 89984 90112, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 89984 90112, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-1221363 : ℤ) ∧
    (∑ n ∈ Ico 89984 90112, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-24427486043394905417475145480 : ℤ) := by
  rcases cdemPrefixStats_89984_90048 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_90048_90112 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 89984 ≤ 90048) (by norm_num : 90048 ≤ 90112), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 89984 ≤ 90048) (by norm_num : 90048 ≤ 90112), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 89984 ≤ 90048) (by norm_num : 90048 ≤ 90112), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 89984 ≤ 90048) (by norm_num : 90048 ≤ 90112), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_89856_90112 :
    (∑ n ∈ Ico 89856 90112, mobiusTreeValue 16 mobiusTable1200001 n) = (-17 : ℤ) ∧
    (∑ n ∈ Ico 89856 90112, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (153 : ℕ) ∧
    (∑ n ∈ Ico 89856 90112, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-943158 : ℤ) ∧
    (∑ n ∈ Ico 89856 90112, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-18863278018418264919198231426 : ℤ) := by
  rcases cdemPrefixStats_89856_89984 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_89984_90112 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 89856 ≤ 89984) (by norm_num : 89984 ≤ 90112), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 89856 ≤ 89984) (by norm_num : 89984 ≤ 90112), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 89856 ≤ 89984) (by norm_num : 89984 ≤ 90112), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 89856 ≤ 89984) (by norm_num : 89984 ≤ 90112), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_89600_90112 :
    (∑ n ∈ Ico 89600 90112, mobiusTreeValue 16 mobiusTable1200001 n) = (-18 : ℤ) ∧
    (∑ n ∈ Ico 89600 90112, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (310 : ℕ) ∧
    (∑ n ∈ Ico 89600 90112, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-999235 : ℤ) ∧
    (∑ n ∈ Ico 89600 90112, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-19984845483725927403737573906 : ℤ) := by
  rcases cdemPrefixStats_89600_89856 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_89856_90112 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 89600 ≤ 89856) (by norm_num : 89856 ≤ 90112), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 89600 ≤ 89856) (by norm_num : 89856 ≤ 90112), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 89600 ≤ 89856) (by norm_num : 89856 ≤ 90112), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 89600 ≤ 89856) (by norm_num : 89856 ≤ 90112), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_89088_90112 :
    (∑ n ∈ Ico 89088 90112, mobiusTreeValue 16 mobiusTable1200001 n) = (-29 : ℤ) ∧
    (∑ n ∈ Ico 89088 90112, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (621 : ℕ) ∧
    (∑ n ∈ Ico 89088 90112, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-1613094 : ℤ) ∧
    (∑ n ∈ Ico 89088 90112, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-32262049268573926150987172482 : ℤ) := by
  rcases cdemPrefixStats_89088_89600 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_89600_90112 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 89088 ≤ 89600) (by norm_num : 89600 ≤ 90112), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 89088 ≤ 89600) (by norm_num : 89600 ≤ 90112), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 89088 ≤ 89600) (by norm_num : 89600 ≤ 90112), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 89088 ≤ 89600) (by norm_num : 89600 ≤ 90112), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_88064_90112 :
    (∑ n ∈ Ico 88064 90112, mobiusTreeValue 16 mobiusTable1200001 n) = (-37 : ℤ) ∧
    (∑ n ∈ Ico 88064 90112, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (1247 : ℕ) ∧
    (∑ n ∈ Ico 88064 90112, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-2054866 : ℤ) ∧
    (∑ n ∈ Ico 88064 90112, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-41097557336130842618829839616 : ℤ) := by
  rcases cdemPrefixStats_88064_89088 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_89088_90112 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 88064 ≤ 89088) (by norm_num : 89088 ≤ 90112), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 88064 ≤ 89088) (by norm_num : 89088 ≤ 90112), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 88064 ≤ 89088) (by norm_num : 89088 ≤ 90112), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 88064 ≤ 89088) (by norm_num : 89088 ≤ 90112), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_86016_90112 :
    (∑ n ∈ Ico 86016 90112, mobiusTreeValue 16 mobiusTable1200001 n) = (-70 : ℤ) ∧
    (∑ n ∈ Ico 86016 90112, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (2494 : ℕ) ∧
    (∑ n ∈ Ico 86016 90112, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-3961336 : ℤ) ∧
    (∑ n ∈ Ico 86016 90112, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-79227328960517885890148025241 : ℤ) := by
  rcases cdemPrefixStats_86016_88064 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_88064_90112 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 86016 ≤ 88064) (by norm_num : 88064 ≤ 90112), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 86016 ≤ 88064) (by norm_num : 88064 ≤ 90112), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 86016 ≤ 88064) (by norm_num : 88064 ≤ 90112), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 86016 ≤ 88064) (by norm_num : 88064 ≤ 90112), hR1, hR2] <;> norm_num

theorem cdemPrefixGroup021_checked_complete :
    (∑ n ∈ Ico 86016 90112, mobiusTreeValue 16 mobiusTable1200001 n) = (-70 : ℤ) ∧
    (∑ n ∈ Ico 86016 90112, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (2494 : ℕ) ∧
    (∑ n ∈ Ico 86016 90112, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-3961336 : ℤ) ∧
    (∑ n ∈ Ico 86016 90112, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-79227328960517885890148025241 : ℤ) := cdemPrefixStats_86016_90112
end Helfgott
#print axioms Helfgott.cdemPrefixGroup021_checked_complete

open Helfgott Finset
open scoped BigOperators

theorem solution :
    (∑ n ∈ Ico 86016 90112, mobiusTreeValue 16 mobiusTable1200001 n) = (-70 : ℤ) ∧
    (∑ n ∈ Ico 86016 90112, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (2494 : ℕ) ∧
    (∑ n ∈ Ico 86016 90112, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-3961336 : ℤ) ∧
    (∑ n ∈ Ico 86016 90112, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-79227328960517885890148025241 : ℤ) := Helfgott.cdemPrefixGroup021_checked_complete
#print axioms solution
