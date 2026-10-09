-- Prove2me | solution 1 for Helfgott.cdemPrefixGroup025_checked
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-09T02:03:26.900029+00:00
-- url     : https://prove2.me/submissions/e0f3951e-ec05-4e4b-85b9-8bf67c834408

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
private theorem cdemPrefixStats_102400_102464 :
    (∑ n ∈ Ico 102400 102464, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 102400 102464, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 102400 102464, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (22 : ℤ) ∧
    (∑ n ∈ Ico 102400 102464, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (447984635322848615733778 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_102464_102528 :
    (∑ n ∈ Ico 102464 102528, mobiusTreeValue 16 mobiusTable1200001 n) = (7 : ℤ) ∧
    (∑ n ∈ Ico 102464 102528, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 102464 102528, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (341509 : ℤ) ∧
    (∑ n ∈ Ico 102464 102528, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (6830173068160563250176059183 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_102400_102528 :
    (∑ n ∈ Ico 102400 102528, mobiusTreeValue 16 mobiusTable1200001 n) = (7 : ℤ) ∧
    (∑ n ∈ Ico 102400 102528, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 102400 102528, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (341531 : ℤ) ∧
    (∑ n ∈ Ico 102400 102528, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (6830621052795886098791792961 : ℤ) := by
  rcases cdemPrefixStats_102400_102464 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_102464_102528 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 102400 ≤ 102464) (by norm_num : 102464 ≤ 102528), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 102400 ≤ 102464) (by norm_num : 102464 ≤ 102528), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 102400 ≤ 102464) (by norm_num : 102464 ≤ 102528), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 102400 ≤ 102464) (by norm_num : 102464 ≤ 102528), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_102528_102592 :
    (∑ n ∈ Ico 102528 102592, mobiusTreeValue 16 mobiusTable1200001 n) = (-3 : ℤ) ∧
    (∑ n ∈ Ico 102528 102592, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 102528 102592, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-146268 : ℤ) ∧
    (∑ n ∈ Ico 102528 102592, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-2925440294595098449188436067 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_102592_102656 :
    (∑ n ∈ Ico 102592 102656, mobiusTreeValue 16 mobiusTable1200001 n) = (-6 : ℤ) ∧
    (∑ n ∈ Ico 102592 102656, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (36 : ℕ) ∧
    (∑ n ∈ Ico 102592 102656, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-292388 : ℤ) ∧
    (∑ n ∈ Ico 102592 102656, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-5847877306383409764065058155 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_102528_102656 :
    (∑ n ∈ Ico 102528 102656, mobiusTreeValue 16 mobiusTable1200001 n) = (-9 : ℤ) ∧
    (∑ n ∈ Ico 102528 102656, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (73 : ℕ) ∧
    (∑ n ∈ Ico 102528 102656, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-438656 : ℤ) ∧
    (∑ n ∈ Ico 102528 102656, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-8773317600978508213253494222 : ℤ) := by
  rcases cdemPrefixStats_102528_102592 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_102592_102656 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 102528 ≤ 102592) (by norm_num : 102592 ≤ 102656), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 102528 ≤ 102592) (by norm_num : 102592 ≤ 102656), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 102528 ≤ 102592) (by norm_num : 102592 ≤ 102656), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 102528 ≤ 102592) (by norm_num : 102592 ≤ 102656), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_102400_102656 :
    (∑ n ∈ Ico 102400 102656, mobiusTreeValue 16 mobiusTable1200001 n) = (-2 : ℤ) ∧
    (∑ n ∈ Ico 102400 102656, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (150 : ℕ) ∧
    (∑ n ∈ Ico 102400 102656, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-97125 : ℤ) ∧
    (∑ n ∈ Ico 102400 102656, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-1942696548182622114461701261 : ℤ) := by
  rcases cdemPrefixStats_102400_102528 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_102528_102656 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 102400 ≤ 102528) (by norm_num : 102528 ≤ 102656), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 102400 ≤ 102528) (by norm_num : 102528 ≤ 102656), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 102400 ≤ 102528) (by norm_num : 102528 ≤ 102656), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 102400 ≤ 102528) (by norm_num : 102528 ≤ 102656), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_102656_102720 :
    (∑ n ∈ Ico 102656 102720, mobiusTreeValue 16 mobiusTable1200001 n) = (6 : ℤ) ∧
    (∑ n ∈ Ico 102656 102720, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (42 : ℕ) ∧
    (∑ n ∈ Ico 102656 102720, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (292099 : ℤ) ∧
    (∑ n ∈ Ico 102656 102720, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (5841984005241659506696716989 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_102720_102784 :
    (∑ n ∈ Ico 102720 102784, mobiusTreeValue 16 mobiusTable1200001 n) = (7 : ℤ) ∧
    (∑ n ∈ Ico 102720 102784, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 102720 102784, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (340586 : ℤ) ∧
    (∑ n ∈ Ico 102720 102784, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (6811762200702323440851602022 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_102656_102784 :
    (∑ n ∈ Ico 102656 102784, mobiusTreeValue 16 mobiusTable1200001 n) = (13 : ℤ) ∧
    (∑ n ∈ Ico 102656 102784, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (81 : ℕ) ∧
    (∑ n ∈ Ico 102656 102784, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (632685 : ℤ) ∧
    (∑ n ∈ Ico 102656 102784, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (12653746205943982947548319011 : ℤ) := by
  rcases cdemPrefixStats_102656_102720 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_102720_102784 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 102656 ≤ 102720) (by norm_num : 102720 ≤ 102784), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 102656 ≤ 102720) (by norm_num : 102720 ≤ 102784), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 102656 ≤ 102720) (by norm_num : 102720 ≤ 102784), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 102656 ≤ 102720) (by norm_num : 102720 ≤ 102784), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_102784_102848 :
    (∑ n ∈ Ico 102784 102848, mobiusTreeValue 16 mobiusTable1200001 n) = (-6 : ℤ) ∧
    (∑ n ∈ Ico 102784 102848, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 102784 102848, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-291817 : ℤ) ∧
    (∑ n ∈ Ico 102784 102848, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-5836433814292286301617883221 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_102848_102912 :
    (∑ n ∈ Ico 102848 102912, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 102848 102912, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 102848 102912, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (48582 : ℤ) ∧
    (∑ n ∈ Ico 102848 102912, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (971571797783452656331221108 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_102784_102912 :
    (∑ n ∈ Ico 102784 102912, mobiusTreeValue 16 mobiusTable1200001 n) = (-5 : ℤ) ∧
    (∑ n ∈ Ico 102784 102912, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (79 : ℕ) ∧
    (∑ n ∈ Ico 102784 102912, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-243235 : ℤ) ∧
    (∑ n ∈ Ico 102784 102912, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-4864862016508833645286662113 : ℤ) := by
  rcases cdemPrefixStats_102784_102848 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_102848_102912 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 102784 ≤ 102848) (by norm_num : 102848 ≤ 102912), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 102784 ≤ 102848) (by norm_num : 102848 ≤ 102912), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 102784 ≤ 102848) (by norm_num : 102848 ≤ 102912), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 102784 ≤ 102848) (by norm_num : 102848 ≤ 102912), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_102656_102912 :
    (∑ n ∈ Ico 102656 102912, mobiusTreeValue 16 mobiusTable1200001 n) = (8 : ℤ) ∧
    (∑ n ∈ Ico 102656 102912, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (160 : ℕ) ∧
    (∑ n ∈ Ico 102656 102912, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (389450 : ℤ) ∧
    (∑ n ∈ Ico 102656 102912, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (7788884189435149302261656898 : ℤ) := by
  rcases cdemPrefixStats_102656_102784 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_102784_102912 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 102656 ≤ 102784) (by norm_num : 102784 ≤ 102912), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 102656 ≤ 102784) (by norm_num : 102784 ≤ 102912), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 102656 ≤ 102784) (by norm_num : 102784 ≤ 102912), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 102656 ≤ 102784) (by norm_num : 102784 ≤ 102912), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_102400_102912 :
    (∑ n ∈ Ico 102400 102912, mobiusTreeValue 16 mobiusTable1200001 n) = (6 : ℤ) ∧
    (∑ n ∈ Ico 102400 102912, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (310 : ℕ) ∧
    (∑ n ∈ Ico 102400 102912, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (292325 : ℤ) ∧
    (∑ n ∈ Ico 102400 102912, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (5846187641252527187799955637 : ℤ) := by
  rcases cdemPrefixStats_102400_102656 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_102656_102912 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 102400 ≤ 102656) (by norm_num : 102656 ≤ 102912), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 102400 ≤ 102656) (by norm_num : 102656 ≤ 102912), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 102400 ≤ 102656) (by norm_num : 102656 ≤ 102912), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 102400 ≤ 102656) (by norm_num : 102656 ≤ 102912), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_102912_102976 :
    (∑ n ∈ Ico 102912 102976, mobiusTreeValue 16 mobiusTable1200001 n) = (7 : ℤ) ∧
    (∑ n ∈ Ico 102912 102976, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (35 : ℕ) ∧
    (∑ n ∈ Ico 102912 102976, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (339952 : ℤ) ∧
    (∑ n ∈ Ico 102912 102976, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (6799115408715957062337234416 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_102976_103040 :
    (∑ n ∈ Ico 102976 103040, mobiusTreeValue 16 mobiusTable1200001 n) = (3 : ℤ) ∧
    (∑ n ∈ Ico 102976 103040, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 102976 103040, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (145592 : ℤ) ∧
    (∑ n ∈ Ico 102976 103040, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (2911867537702196427859924865 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_102912_103040 :
    (∑ n ∈ Ico 102912 103040, mobiusTreeValue 16 mobiusTable1200001 n) = (10 : ℤ) ∧
    (∑ n ∈ Ico 102912 103040, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (76 : ℕ) ∧
    (∑ n ∈ Ico 102912 103040, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (485544 : ℤ) ∧
    (∑ n ∈ Ico 102912 103040, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (9710982946418153490197159281 : ℤ) := by
  rcases cdemPrefixStats_102912_102976 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_102976_103040 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 102912 ≤ 102976) (by norm_num : 102976 ≤ 103040), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 102912 ≤ 102976) (by norm_num : 102976 ≤ 103040), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 102912 ≤ 102976) (by norm_num : 102976 ≤ 103040), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 102912 ≤ 102976) (by norm_num : 102976 ≤ 103040), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_103040_103104 :
    (∑ n ∈ Ico 103040 103104, mobiusTreeValue 16 mobiusTable1200001 n) = (4 : ℤ) ∧
    (∑ n ∈ Ico 103040 103104, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 103040 103104, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (194055 : ℤ) ∧
    (∑ n ∈ Ico 103040 103104, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (3881158895748737530959870115 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_103104_103168 :
    (∑ n ∈ Ico 103104 103168, mobiusTreeValue 16 mobiusTable1200001 n) = (4 : ℤ) ∧
    (∑ n ∈ Ico 103104 103168, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 103104 103168, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (193903 : ℤ) ∧
    (∑ n ∈ Ico 103104 103168, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (3878082762131222796628222393 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_103040_103168 :
    (∑ n ∈ Ico 103040 103168, mobiusTreeValue 16 mobiusTable1200001 n) = (8 : ℤ) ∧
    (∑ n ∈ Ico 103040 103168, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (76 : ℕ) ∧
    (∑ n ∈ Ico 103040 103168, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (387958 : ℤ) ∧
    (∑ n ∈ Ico 103040 103168, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (7759241657879960327588092508 : ℤ) := by
  rcases cdemPrefixStats_103040_103104 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_103104_103168 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 103040 ≤ 103104) (by norm_num : 103104 ≤ 103168), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 103040 ≤ 103104) (by norm_num : 103104 ≤ 103168), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 103040 ≤ 103104) (by norm_num : 103104 ≤ 103168), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 103040 ≤ 103104) (by norm_num : 103104 ≤ 103168), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_102912_103168 :
    (∑ n ∈ Ico 102912 103168, mobiusTreeValue 16 mobiusTable1200001 n) = (18 : ℤ) ∧
    (∑ n ∈ Ico 102912 103168, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (152 : ℕ) ∧
    (∑ n ∈ Ico 102912 103168, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (873502 : ℤ) ∧
    (∑ n ∈ Ico 102912 103168, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (17470224604298113817785251789 : ℤ) := by
  rcases cdemPrefixStats_102912_103040 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_103040_103168 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 102912 ≤ 103040) (by norm_num : 103040 ≤ 103168), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 102912 ≤ 103040) (by norm_num : 103040 ≤ 103168), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 102912 ≤ 103040) (by norm_num : 103040 ≤ 103168), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 102912 ≤ 103040) (by norm_num : 103040 ≤ 103168), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_103168_103232 :
    (∑ n ∈ Ico 103168 103232, mobiusTreeValue 16 mobiusTable1200001 n) = (5 : ℤ) ∧
    (∑ n ∈ Ico 103168 103232, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 103168 103232, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (242171 : ℤ) ∧
    (∑ n ∈ Ico 103168 103232, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (4843468081262031196469202469 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_103232_103296 :
    (∑ n ∈ Ico 103232 103296, mobiusTreeValue 16 mobiusTable1200001 n) = (-4 : ℤ) ∧
    (∑ n ∈ Ico 103232 103296, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 103232 103296, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-193741 : ℤ) ∧
    (∑ n ∈ Ico 103232 103296, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-3874833324048317608901581523 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_103168_103296 :
    (∑ n ∈ Ico 103168 103296, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 103168 103296, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 103168 103296, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (48430 : ℤ) ∧
    (∑ n ∈ Ico 103168 103296, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (968634757213713587567620946 : ℤ) := by
  rcases cdemPrefixStats_103168_103232 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_103232_103296 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 103168 ≤ 103232) (by norm_num : 103232 ≤ 103296), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 103168 ≤ 103232) (by norm_num : 103232 ≤ 103296), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 103168 ≤ 103232) (by norm_num : 103232 ≤ 103296), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 103168 ≤ 103232) (by norm_num : 103232 ≤ 103296), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_103296_103360 :
    (∑ n ∈ Ico 103296 103360, mobiusTreeValue 16 mobiusTable1200001 n) = (4 : ℤ) ∧
    (∑ n ∈ Ico 103296 103360, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 103296 103360, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (193658 : ℤ) ∧
    (∑ n ∈ Ico 103296 103360, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (3873228150101403013316238049 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_103360_103424 :
    (∑ n ∈ Ico 103360 103424, mobiusTreeValue 16 mobiusTable1200001 n) = (12 : ℤ) ∧
    (∑ n ∈ Ico 103360 103424, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 103360 103424, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (580340 : ℤ) ∧
    (∑ n ∈ Ico 103360 103424, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (11606959737722653366749512362 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_103296_103424 :
    (∑ n ∈ Ico 103296 103424, mobiusTreeValue 16 mobiusTable1200001 n) = (16 : ℤ) ∧
    (∑ n ∈ Ico 103296 103424, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 103296 103424, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (773998 : ℤ) ∧
    (∑ n ∈ Ico 103296 103424, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (15480187887824056380065750411 : ℤ) := by
  rcases cdemPrefixStats_103296_103360 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_103360_103424 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 103296 ≤ 103360) (by norm_num : 103360 ≤ 103424), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 103296 ≤ 103360) (by norm_num : 103360 ≤ 103424), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 103296 ≤ 103360) (by norm_num : 103360 ≤ 103424), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 103296 ≤ 103360) (by norm_num : 103360 ≤ 103424), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_103168_103424 :
    (∑ n ∈ Ico 103168 103424, mobiusTreeValue 16 mobiusTable1200001 n) = (17 : ℤ) ∧
    (∑ n ∈ Ico 103168 103424, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (155 : ℕ) ∧
    (∑ n ∈ Ico 103168 103424, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (822428 : ℤ) ∧
    (∑ n ∈ Ico 103168 103424, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (16448822645037769967633371357 : ℤ) := by
  rcases cdemPrefixStats_103168_103296 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_103296_103424 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 103168 ≤ 103296) (by norm_num : 103296 ≤ 103424), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 103168 ≤ 103296) (by norm_num : 103296 ≤ 103424), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 103168 ≤ 103296) (by norm_num : 103296 ≤ 103424), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 103168 ≤ 103296) (by norm_num : 103296 ≤ 103424), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_102912_103424 :
    (∑ n ∈ Ico 102912 103424, mobiusTreeValue 16 mobiusTable1200001 n) = (35 : ℤ) ∧
    (∑ n ∈ Ico 102912 103424, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (307 : ℕ) ∧
    (∑ n ∈ Ico 102912 103424, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (1695930 : ℤ) ∧
    (∑ n ∈ Ico 102912 103424, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (33919047249335883785418623146 : ℤ) := by
  rcases cdemPrefixStats_102912_103168 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_103168_103424 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 102912 ≤ 103168) (by norm_num : 103168 ≤ 103424), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 102912 ≤ 103168) (by norm_num : 103168 ≤ 103424), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 102912 ≤ 103168) (by norm_num : 103168 ≤ 103424), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 102912 ≤ 103168) (by norm_num : 103168 ≤ 103424), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_102400_103424 :
    (∑ n ∈ Ico 102400 103424, mobiusTreeValue 16 mobiusTable1200001 n) = (41 : ℤ) ∧
    (∑ n ∈ Ico 102400 103424, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (617 : ℕ) ∧
    (∑ n ∈ Ico 102400 103424, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (1988255 : ℤ) ∧
    (∑ n ∈ Ico 102400 103424, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (39765234890588410973218578783 : ℤ) := by
  rcases cdemPrefixStats_102400_102912 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_102912_103424 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 102400 ≤ 102912) (by norm_num : 102912 ≤ 103424), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 102400 ≤ 102912) (by norm_num : 102912 ≤ 103424), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 102400 ≤ 102912) (by norm_num : 102912 ≤ 103424), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 102400 ≤ 102912) (by norm_num : 102912 ≤ 103424), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_103424_103488 :
    (∑ n ∈ Ico 103424 103488, mobiusTreeValue 16 mobiusTable1200001 n) = (3 : ℤ) ∧
    (∑ n ∈ Ico 103424 103488, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 103424 103488, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (145017 : ℤ) ∧
    (∑ n ∈ Ico 103424 103488, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (2900334652093515567494735988 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_103488_103552 :
    (∑ n ∈ Ico 103488 103552, mobiusTreeValue 16 mobiusTable1200001 n) = (7 : ℤ) ∧
    (∑ n ∈ Ico 103488 103552, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 103488 103552, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (338115 : ℤ) ∧
    (∑ n ∈ Ico 103488 103552, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (6762361143355583357487809844 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_103424_103552 :
    (∑ n ∈ Ico 103424 103552, mobiusTreeValue 16 mobiusTable1200001 n) = (10 : ℤ) ∧
    (∑ n ∈ Ico 103424 103552, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (76 : ℕ) ∧
    (∑ n ∈ Ico 103424 103552, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (483132 : ℤ) ∧
    (∑ n ∈ Ico 103424 103552, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (9662695795449098924982545832 : ℤ) := by
  rcases cdemPrefixStats_103424_103488 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_103488_103552 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 103424 ≤ 103488) (by norm_num : 103488 ≤ 103552), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 103424 ≤ 103488) (by norm_num : 103488 ≤ 103552), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 103424 ≤ 103488) (by norm_num : 103488 ≤ 103552), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 103424 ≤ 103488) (by norm_num : 103488 ≤ 103552), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_103552_103616 :
    (∑ n ∈ Ico 103552 103616, mobiusTreeValue 16 mobiusTable1200001 n) = (9 : ℤ) ∧
    (∑ n ∈ Ico 103552 103616, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 103552 103616, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (434326 : ℤ) ∧
    (∑ n ∈ Ico 103552 103616, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (8686625067772254528319485344 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_103616_103680 :
    (∑ n ∈ Ico 103616 103680, mobiusTreeValue 16 mobiusTable1200001 n) = (5 : ℤ) ∧
    (∑ n ∈ Ico 103616 103680, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 103616 103680, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (241160 : ℤ) ∧
    (∑ n ∈ Ico 103616 103680, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (4823275112993320470913572215 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_103552_103680 :
    (∑ n ∈ Ico 103552 103680, mobiusTreeValue 16 mobiusTable1200001 n) = (14 : ℤ) ∧
    (∑ n ∈ Ico 103552 103680, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 103552 103680, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (675486 : ℤ) ∧
    (∑ n ∈ Ico 103552 103680, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (13509900180765574999233057559 : ℤ) := by
  rcases cdemPrefixStats_103552_103616 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_103616_103680 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 103552 ≤ 103616) (by norm_num : 103616 ≤ 103680), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 103552 ≤ 103616) (by norm_num : 103616 ≤ 103680), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 103552 ≤ 103616) (by norm_num : 103616 ≤ 103680), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 103552 ≤ 103616) (by norm_num : 103616 ≤ 103680), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_103424_103680 :
    (∑ n ∈ Ico 103424 103680, mobiusTreeValue 16 mobiusTable1200001 n) = (24 : ℤ) ∧
    (∑ n ∈ Ico 103424 103680, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (154 : ℕ) ∧
    (∑ n ∈ Ico 103424 103680, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (1158618 : ℤ) ∧
    (∑ n ∈ Ico 103424 103680, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (23172595976214673924215603391 : ℤ) := by
  rcases cdemPrefixStats_103424_103552 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_103552_103680 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 103424 ≤ 103552) (by norm_num : 103552 ≤ 103680), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 103424 ≤ 103552) (by norm_num : 103552 ≤ 103680), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 103424 ≤ 103552) (by norm_num : 103552 ≤ 103680), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 103424 ≤ 103552) (by norm_num : 103552 ≤ 103680), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_103680_103744 :
    (∑ n ∈ Ico 103680 103744, mobiusTreeValue 16 mobiusTable1200001 n) = (2 : ℤ) ∧
    (∑ n ∈ Ico 103680 103744, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 103680 103744, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (96338 : ℤ) ∧
    (∑ n ∈ Ico 103680 103744, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1926780953701185232660240687 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_103744_103808 :
    (∑ n ∈ Ico 103744 103808, mobiusTreeValue 16 mobiusTable1200001 n) = (6 : ℤ) ∧
    (∑ n ∈ Ico 103744 103808, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 103744 103808, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (289057 : ℤ) ∧
    (∑ n ∈ Ico 103744 103808, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (5781173010363544767537388924 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_103680_103808 :
    (∑ n ∈ Ico 103680 103808, mobiusTreeValue 16 mobiusTable1200001 n) = (8 : ℤ) ∧
    (∑ n ∈ Ico 103680 103808, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 103680 103808, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (385395 : ℤ) ∧
    (∑ n ∈ Ico 103680 103808, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (7707953964064730000197629611 : ℤ) := by
  rcases cdemPrefixStats_103680_103744 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_103744_103808 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 103680 ≤ 103744) (by norm_num : 103744 ≤ 103808), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 103680 ≤ 103744) (by norm_num : 103744 ≤ 103808), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 103680 ≤ 103744) (by norm_num : 103744 ≤ 103808), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 103680 ≤ 103744) (by norm_num : 103744 ≤ 103808), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_103808_103872 :
    (∑ n ∈ Ico 103808 103872, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 103808 103872, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 103808 103872, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (35 : ℤ) ∧
    (∑ n ∈ Ico 103808 103872, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (714279016085417341337385 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_103872_103936 :
    (∑ n ∈ Ico 103872 103936, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 103872 103936, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 103872 103936, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (2 : ℤ) ∧
    (∑ n ∈ Ico 103872 103936, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (92737266731502157939288 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_103808_103936 :
    (∑ n ∈ Ico 103808 103936, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 103808 103936, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (76 : ℕ) ∧
    (∑ n ∈ Ico 103808 103936, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (37 : ℤ) ∧
    (∑ n ∈ Ico 103808 103936, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (807016282816919499276673 : ℤ) := by
  rcases cdemPrefixStats_103808_103872 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_103872_103936 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 103808 ≤ 103872) (by norm_num : 103872 ≤ 103936), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 103808 ≤ 103872) (by norm_num : 103872 ≤ 103936), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 103808 ≤ 103872) (by norm_num : 103872 ≤ 103936), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 103808 ≤ 103872) (by norm_num : 103872 ≤ 103936), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_103680_103936 :
    (∑ n ∈ Ico 103680 103936, mobiusTreeValue 16 mobiusTable1200001 n) = (8 : ℤ) ∧
    (∑ n ∈ Ico 103680 103936, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (154 : ℕ) ∧
    (∑ n ∈ Ico 103680 103936, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (385432 : ℤ) ∧
    (∑ n ∈ Ico 103680 103936, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (7708760980347546919696906284 : ℤ) := by
  rcases cdemPrefixStats_103680_103808 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_103808_103936 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 103680 ≤ 103808) (by norm_num : 103808 ≤ 103936), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 103680 ≤ 103808) (by norm_num : 103808 ≤ 103936), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 103680 ≤ 103808) (by norm_num : 103808 ≤ 103936), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 103680 ≤ 103808) (by norm_num : 103808 ≤ 103936), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_103424_103936 :
    (∑ n ∈ Ico 103424 103936, mobiusTreeValue 16 mobiusTable1200001 n) = (32 : ℤ) ∧
    (∑ n ∈ Ico 103424 103936, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (308 : ℕ) ∧
    (∑ n ∈ Ico 103424 103936, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (1544050 : ℤ) ∧
    (∑ n ∈ Ico 103424 103936, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (30881356956562220843912509675 : ℤ) := by
  rcases cdemPrefixStats_103424_103680 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_103680_103936 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 103424 ≤ 103680) (by norm_num : 103680 ≤ 103936), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 103424 ≤ 103680) (by norm_num : 103680 ≤ 103936), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 103424 ≤ 103680) (by norm_num : 103680 ≤ 103936), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 103424 ≤ 103680) (by norm_num : 103680 ≤ 103936), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_103936_104000 :
    (∑ n ∈ Ico 103936 104000, mobiusTreeValue 16 mobiusTable1200001 n) = (-7 : ℤ) ∧
    (∑ n ∈ Ico 103936 104000, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 103936 104000, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-336492 : ℤ) ∧
    (∑ n ∈ Ico 103936 104000, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-6729899067236348460755416453 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_104000_104064 :
    (∑ n ∈ Ico 104000 104064, mobiusTreeValue 16 mobiusTable1200001 n) = (-2 : ℤ) ∧
    (∑ n ∈ Ico 104000 104064, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 104000 104064, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-96177 : ℤ) ∧
    (∑ n ∈ Ico 104000 104064, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-1923566483438332379391779542 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_103936_104064 :
    (∑ n ∈ Ico 103936 104064, mobiusTreeValue 16 mobiusTable1200001 n) = (-9 : ℤ) ∧
    (∑ n ∈ Ico 103936 104064, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (79 : ℕ) ∧
    (∑ n ∈ Ico 103936 104064, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-432669 : ℤ) ∧
    (∑ n ∈ Ico 103936 104064, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-8653465550674680840147195995 : ℤ) := by
  rcases cdemPrefixStats_103936_104000 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_104000_104064 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 103936 ≤ 104000) (by norm_num : 104000 ≤ 104064), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 103936 ≤ 104000) (by norm_num : 104000 ≤ 104064), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 103936 ≤ 104000) (by norm_num : 104000 ≤ 104064), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 103936 ≤ 104000) (by norm_num : 104000 ≤ 104064), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_104064_104128 :
    (∑ n ∈ Ico 104064 104128, mobiusTreeValue 16 mobiusTable1200001 n) = (-5 : ℤ) ∧
    (∑ n ∈ Ico 104064 104128, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 104064 104128, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-240122 : ℤ) ∧
    (∑ n ∈ Ico 104064 104128, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-4802502187703048364283870761 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_104128_104192 :
    (∑ n ∈ Ico 104128 104192, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 104128 104192, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 104128 104192, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (71 : ℤ) ∧
    (∑ n ∈ Ico 104128 104192, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1419677777803191555958379 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_104064_104192 :
    (∑ n ∈ Ico 104064 104192, mobiusTreeValue 16 mobiusTable1200001 n) = (-5 : ℤ) ∧
    (∑ n ∈ Ico 104064 104192, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (81 : ℕ) ∧
    (∑ n ∈ Ico 104064 104192, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-240051 : ℤ) ∧
    (∑ n ∈ Ico 104064 104192, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-4801082509925245172727912382 : ℤ) := by
  rcases cdemPrefixStats_104064_104128 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_104128_104192 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 104064 ≤ 104128) (by norm_num : 104128 ≤ 104192), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 104064 ≤ 104128) (by norm_num : 104128 ≤ 104192), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 104064 ≤ 104128) (by norm_num : 104128 ≤ 104192), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 104064 ≤ 104128) (by norm_num : 104128 ≤ 104192), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_103936_104192 :
    (∑ n ∈ Ico 103936 104192, mobiusTreeValue 16 mobiusTable1200001 n) = (-14 : ℤ) ∧
    (∑ n ∈ Ico 103936 104192, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (160 : ℕ) ∧
    (∑ n ∈ Ico 103936 104192, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-672720 : ℤ) ∧
    (∑ n ∈ Ico 103936 104192, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-13454548060599926012875108377 : ℤ) := by
  rcases cdemPrefixStats_103936_104064 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_104064_104192 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 103936 ≤ 104064) (by norm_num : 104064 ≤ 104192), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 103936 ≤ 104064) (by norm_num : 104064 ≤ 104192), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 103936 ≤ 104064) (by norm_num : 104064 ≤ 104192), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 103936 ≤ 104064) (by norm_num : 104064 ≤ 104192), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_104192_104256 :
    (∑ n ∈ Ico 104192 104256, mobiusTreeValue 16 mobiusTable1200001 n) = (7 : ℤ) ∧
    (∑ n ∈ Ico 104192 104256, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 104192 104256, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (335813 : ℤ) ∧
    (∑ n ∈ Ico 104192 104256, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (6716367896049946991244195436 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_104256_104320 :
    (∑ n ∈ Ico 104256 104320, mobiusTreeValue 16 mobiusTable1200001 n) = (-5 : ℤ) ∧
    (∑ n ∈ Ico 104256 104320, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 104256 104320, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-239642 : ℤ) ∧
    (∑ n ∈ Ico 104256 104320, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-4792815624251953269736119260 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_104192_104320 :
    (∑ n ∈ Ico 104192 104320, mobiusTreeValue 16 mobiusTable1200001 n) = (2 : ℤ) ∧
    (∑ n ∈ Ico 104192 104320, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (76 : ℕ) ∧
    (∑ n ∈ Ico 104192 104320, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (96171 : ℤ) ∧
    (∑ n ∈ Ico 104192 104320, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1923552271797993721508076176 : ℤ) := by
  rcases cdemPrefixStats_104192_104256 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_104256_104320 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 104192 ≤ 104256) (by norm_num : 104256 ≤ 104320), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 104192 ≤ 104256) (by norm_num : 104256 ≤ 104320), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 104192 ≤ 104256) (by norm_num : 104256 ≤ 104320), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 104192 ≤ 104256) (by norm_num : 104256 ≤ 104320), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_104320_104384 :
    (∑ n ∈ Ico 104320 104384, mobiusTreeValue 16 mobiusTable1200001 n) = (-7 : ℤ) ∧
    (∑ n ∈ Ico 104320 104384, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 104320 104384, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-335391 : ℤ) ∧
    (∑ n ∈ Ico 104320 104384, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-6707854184932114530123166395 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_104384_104448 :
    (∑ n ∈ Ico 104384 104448, mobiusTreeValue 16 mobiusTable1200001 n) = (4 : ℤ) ∧
    (∑ n ∈ Ico 104384 104448, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 104384 104448, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (191583 : ℤ) ∧
    (∑ n ∈ Ico 104384 104448, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (3831665268106985588550417848 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_104320_104448 :
    (∑ n ∈ Ico 104320 104448, mobiusTreeValue 16 mobiusTable1200001 n) = (-3 : ℤ) ∧
    (∑ n ∈ Ico 104320 104448, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (75 : ℕ) ∧
    (∑ n ∈ Ico 104320 104448, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-143808 : ℤ) ∧
    (∑ n ∈ Ico 104320 104448, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-2876188916825128941572748547 : ℤ) := by
  rcases cdemPrefixStats_104320_104384 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_104384_104448 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 104320 ≤ 104384) (by norm_num : 104384 ≤ 104448), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 104320 ≤ 104384) (by norm_num : 104384 ≤ 104448), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 104320 ≤ 104384) (by norm_num : 104384 ≤ 104448), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 104320 ≤ 104384) (by norm_num : 104384 ≤ 104448), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_104192_104448 :
    (∑ n ∈ Ico 104192 104448, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 104192 104448, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (151 : ℕ) ∧
    (∑ n ∈ Ico 104192 104448, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-47637 : ℤ) ∧
    (∑ n ∈ Ico 104192 104448, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-952636645027135220064672371 : ℤ) := by
  rcases cdemPrefixStats_104192_104320 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_104320_104448 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 104192 ≤ 104320) (by norm_num : 104320 ≤ 104448), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 104192 ≤ 104320) (by norm_num : 104320 ≤ 104448), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 104192 ≤ 104320) (by norm_num : 104320 ≤ 104448), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 104192 ≤ 104320) (by norm_num : 104320 ≤ 104448), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_103936_104448 :
    (∑ n ∈ Ico 103936 104448, mobiusTreeValue 16 mobiusTable1200001 n) = (-15 : ℤ) ∧
    (∑ n ∈ Ico 103936 104448, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (311 : ℕ) ∧
    (∑ n ∈ Ico 103936 104448, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-720357 : ℤ) ∧
    (∑ n ∈ Ico 103936 104448, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-14407184705627061232939780748 : ℤ) := by
  rcases cdemPrefixStats_103936_104192 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_104192_104448 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 103936 ≤ 104192) (by norm_num : 104192 ≤ 104448), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 103936 ≤ 104192) (by norm_num : 104192 ≤ 104448), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 103936 ≤ 104192) (by norm_num : 104192 ≤ 104448), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 103936 ≤ 104192) (by norm_num : 104192 ≤ 104448), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_103424_104448 :
    (∑ n ∈ Ico 103424 104448, mobiusTreeValue 16 mobiusTable1200001 n) = (17 : ℤ) ∧
    (∑ n ∈ Ico 103424 104448, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (619 : ℕ) ∧
    (∑ n ∈ Ico 103424 104448, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (823693 : ℤ) ∧
    (∑ n ∈ Ico 103424 104448, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (16474172250935159610972728927 : ℤ) := by
  rcases cdemPrefixStats_103424_103936 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_103936_104448 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 103424 ≤ 103936) (by norm_num : 103936 ≤ 104448), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 103424 ≤ 103936) (by norm_num : 103936 ≤ 104448), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 103424 ≤ 103936) (by norm_num : 103936 ≤ 104448), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 103424 ≤ 103936) (by norm_num : 103936 ≤ 104448), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_102400_104448 :
    (∑ n ∈ Ico 102400 104448, mobiusTreeValue 16 mobiusTable1200001 n) = (58 : ℤ) ∧
    (∑ n ∈ Ico 102400 104448, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (1236 : ℕ) ∧
    (∑ n ∈ Ico 102400 104448, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (2811948 : ℤ) ∧
    (∑ n ∈ Ico 102400 104448, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (56239407141523570584191307710 : ℤ) := by
  rcases cdemPrefixStats_102400_103424 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_103424_104448 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 102400 ≤ 103424) (by norm_num : 103424 ≤ 104448), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 102400 ≤ 103424) (by norm_num : 103424 ≤ 104448), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 102400 ≤ 103424) (by norm_num : 103424 ≤ 104448), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 102400 ≤ 103424) (by norm_num : 103424 ≤ 104448), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_104448_104512 :
    (∑ n ∈ Ico 104448 104512, mobiusTreeValue 16 mobiusTable1200001 n) = (5 : ℤ) ∧
    (∑ n ∈ Ico 104448 104512, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 104448 104512, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (239228 : ℤ) ∧
    (∑ n ∈ Ico 104448 104512, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (4784634059650233412919970115 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_104512_104576 :
    (∑ n ∈ Ico 104512 104576, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 104512 104576, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 104512 104576, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-5 : ℤ) ∧
    (∑ n ∈ Ico 104512 104576, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-182793930880923125709805 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_104448_104576 :
    (∑ n ∈ Ico 104448 104576, mobiusTreeValue 16 mobiusTable1200001 n) = (5 : ℤ) ∧
    (∑ n ∈ Ico 104448 104576, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (79 : ℕ) ∧
    (∑ n ∈ Ico 104448 104576, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (239223 : ℤ) ∧
    (∑ n ∈ Ico 104448 104576, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (4784451265719352489794260310 : ℤ) := by
  rcases cdemPrefixStats_104448_104512 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_104512_104576 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 104448 ≤ 104512) (by norm_num : 104512 ≤ 104576), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 104448 ≤ 104512) (by norm_num : 104512 ≤ 104576), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 104448 ≤ 104512) (by norm_num : 104512 ≤ 104576), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 104448 ≤ 104512) (by norm_num : 104512 ≤ 104576), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_104576_104640 :
    (∑ n ∈ Ico 104576 104640, mobiusTreeValue 16 mobiusTable1200001 n) = (-2 : ℤ) ∧
    (∑ n ∈ Ico 104576 104640, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 104576 104640, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-95597 : ℤ) ∧
    (∑ n ∈ Ico 104576 104640, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-1911945661153781611548545797 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_104640_104704 :
    (∑ n ∈ Ico 104640 104704, mobiusTreeValue 16 mobiusTable1200001 n) = (-7 : ℤ) ∧
    (∑ n ∈ Ico 104640 104704, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 104640 104704, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-334274 : ℤ) ∧
    (∑ n ∈ Ico 104640 104704, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-6685494465941151722744522919 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_104576_104704 :
    (∑ n ∈ Ico 104576 104704, mobiusTreeValue 16 mobiusTable1200001 n) = (-9 : ℤ) ∧
    (∑ n ∈ Ico 104576 104704, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (79 : ℕ) ∧
    (∑ n ∈ Ico 104576 104704, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-429871 : ℤ) ∧
    (∑ n ∈ Ico 104576 104704, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-8597440127094933334293068716 : ℤ) := by
  rcases cdemPrefixStats_104576_104640 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_104640_104704 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 104576 ≤ 104640) (by norm_num : 104640 ≤ 104704), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 104576 ≤ 104640) (by norm_num : 104640 ≤ 104704), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 104576 ≤ 104640) (by norm_num : 104640 ≤ 104704), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 104576 ≤ 104640) (by norm_num : 104640 ≤ 104704), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_104448_104704 :
    (∑ n ∈ Ico 104448 104704, mobiusTreeValue 16 mobiusTable1200001 n) = (-4 : ℤ) ∧
    (∑ n ∈ Ico 104448 104704, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (158 : ℕ) ∧
    (∑ n ∈ Ico 104448 104704, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-190648 : ℤ) ∧
    (∑ n ∈ Ico 104448 104704, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-3812988861375580844498808406 : ℤ) := by
  rcases cdemPrefixStats_104448_104576 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_104576_104704 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 104448 ≤ 104576) (by norm_num : 104576 ≤ 104704), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 104448 ≤ 104576) (by norm_num : 104576 ≤ 104704), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 104448 ≤ 104576) (by norm_num : 104576 ≤ 104704), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 104448 ≤ 104576) (by norm_num : 104576 ≤ 104704), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_104704_104768 :
    (∑ n ∈ Ico 104704 104768, mobiusTreeValue 16 mobiusTable1200001 n) = (-8 : ℤ) ∧
    (∑ n ∈ Ico 104704 104768, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 104704 104768, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-381920 : ℤ) ∧
    (∑ n ∈ Ico 104704 104768, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-7638507840553987154338551149 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_104768_104832 :
    (∑ n ∈ Ico 104768 104832, mobiusTreeValue 16 mobiusTable1200001 n) = (-6 : ℤ) ∧
    (∑ n ∈ Ico 104768 104832, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 104768 104832, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-286242 : ℤ) ∧
    (∑ n ∈ Ico 104768 104832, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-5724963416739321138108800802 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_104704_104832 :
    (∑ n ∈ Ico 104704 104832, mobiusTreeValue 16 mobiusTable1200001 n) = (-14 : ℤ) ∧
    (∑ n ∈ Ico 104704 104832, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (76 : ℕ) ∧
    (∑ n ∈ Ico 104704 104832, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-668162 : ℤ) ∧
    (∑ n ∈ Ico 104704 104832, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-13363471257293308292447351951 : ℤ) := by
  rcases cdemPrefixStats_104704_104768 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_104768_104832 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 104704 ≤ 104768) (by norm_num : 104768 ≤ 104832), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 104704 ≤ 104768) (by norm_num : 104768 ≤ 104832), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 104704 ≤ 104768) (by norm_num : 104768 ≤ 104832), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 104704 ≤ 104768) (by norm_num : 104768 ≤ 104832), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_104832_104896 :
    (∑ n ∈ Ico 104832 104896, mobiusTreeValue 16 mobiusTable1200001 n) = (-4 : ℤ) ∧
    (∑ n ∈ Ico 104832 104896, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 104832 104896, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-190679 : ℤ) ∧
    (∑ n ∈ Ico 104832 104896, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-3813636576867345191299429028 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_104896_104960 :
    (∑ n ∈ Ico 104896 104960, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 104896 104960, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 104896 104960, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-47567 : ℤ) ∧
    (∑ n ∈ Ico 104896 104960, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-951363257156406639072145187 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_104832_104960 :
    (∑ n ∈ Ico 104832 104960, mobiusTreeValue 16 mobiusTable1200001 n) = (-5 : ℤ) ∧
    (∑ n ∈ Ico 104832 104960, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (79 : ℕ) ∧
    (∑ n ∈ Ico 104832 104960, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-238246 : ℤ) ∧
    (∑ n ∈ Ico 104832 104960, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-4764999834023751830371574215 : ℤ) := by
  rcases cdemPrefixStats_104832_104896 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_104896_104960 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 104832 ≤ 104896) (by norm_num : 104896 ≤ 104960), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 104832 ≤ 104896) (by norm_num : 104896 ≤ 104960), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 104832 ≤ 104896) (by norm_num : 104896 ≤ 104960), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 104832 ≤ 104896) (by norm_num : 104896 ≤ 104960), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_104704_104960 :
    (∑ n ∈ Ico 104704 104960, mobiusTreeValue 16 mobiusTable1200001 n) = (-19 : ℤ) ∧
    (∑ n ∈ Ico 104704 104960, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (155 : ℕ) ∧
    (∑ n ∈ Ico 104704 104960, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-906408 : ℤ) ∧
    (∑ n ∈ Ico 104704 104960, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-18128471091317060122818926166 : ℤ) := by
  rcases cdemPrefixStats_104704_104832 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_104832_104960 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 104704 ≤ 104832) (by norm_num : 104832 ≤ 104960), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 104704 ≤ 104832) (by norm_num : 104832 ≤ 104960), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 104704 ≤ 104832) (by norm_num : 104832 ≤ 104960), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 104704 ≤ 104832) (by norm_num : 104832 ≤ 104960), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_104448_104960 :
    (∑ n ∈ Ico 104448 104960, mobiusTreeValue 16 mobiusTable1200001 n) = (-23 : ℤ) ∧
    (∑ n ∈ Ico 104448 104960, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (313 : ℕ) ∧
    (∑ n ∈ Ico 104448 104960, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-1097056 : ℤ) ∧
    (∑ n ∈ Ico 104448 104960, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-21941459952692640967317734572 : ℤ) := by
  rcases cdemPrefixStats_104448_104704 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_104704_104960 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 104448 ≤ 104704) (by norm_num : 104704 ≤ 104960), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 104448 ≤ 104704) (by norm_num : 104704 ≤ 104960), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 104448 ≤ 104704) (by norm_num : 104704 ≤ 104960), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 104448 ≤ 104704) (by norm_num : 104704 ≤ 104960), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_104960_105024 :
    (∑ n ∈ Ico 104960 105024, mobiusTreeValue 16 mobiusTable1200001 n) = (-3 : ℤ) ∧
    (∑ n ∈ Ico 104960 105024, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 104960 105024, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-142896 : ℤ) ∧
    (∑ n ∈ Ico 104960 105024, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-2857977375946726068267044051 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_105024_105088 :
    (∑ n ∈ Ico 105024 105088, mobiusTreeValue 16 mobiusTable1200001 n) = (-2 : ℤ) ∧
    (∑ n ∈ Ico 105024 105088, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 105024 105088, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-95257 : ℤ) ∧
    (∑ n ∈ Ico 105024 105088, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-1905133035205128213606911408 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_104960_105088 :
    (∑ n ∈ Ico 104960 105088, mobiusTreeValue 16 mobiusTable1200001 n) = (-5 : ℤ) ∧
    (∑ n ∈ Ico 104960 105088, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (81 : ℕ) ∧
    (∑ n ∈ Ico 104960 105088, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-238153 : ℤ) ∧
    (∑ n ∈ Ico 104960 105088, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-4763110411151854281873955459 : ℤ) := by
  rcases cdemPrefixStats_104960_105024 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_105024_105088 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 104960 ≤ 105024) (by norm_num : 105024 ≤ 105088), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 104960 ≤ 105024) (by norm_num : 105024 ≤ 105088), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 104960 ≤ 105024) (by norm_num : 105024 ≤ 105088), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 104960 ≤ 105024) (by norm_num : 105024 ≤ 105088), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_105088_105152 :
    (∑ n ∈ Ico 105088 105152, mobiusTreeValue 16 mobiusTable1200001 n) = (5 : ℤ) ∧
    (∑ n ∈ Ico 105088 105152, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 105088 105152, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (237865 : ℤ) ∧
    (∑ n ∈ Ico 105088 105152, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (4757382908519841956631637020 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_105152_105216 :
    (∑ n ∈ Ico 105152 105216, mobiusTreeValue 16 mobiusTable1200001 n) = (2 : ℤ) ∧
    (∑ n ∈ Ico 105152 105216, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 105152 105216, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (95206 : ℤ) ∧
    (∑ n ∈ Ico 105152 105216, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1904150557651715715835019760 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_105088_105216 :
    (∑ n ∈ Ico 105088 105216, mobiusTreeValue 16 mobiusTable1200001 n) = (7 : ℤ) ∧
    (∑ n ∈ Ico 105088 105216, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 105088 105216, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (333071 : ℤ) ∧
    (∑ n ∈ Ico 105088 105216, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (6661533466171557672466656780 : ℤ) := by
  rcases cdemPrefixStats_105088_105152 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_105152_105216 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 105088 ≤ 105152) (by norm_num : 105152 ≤ 105216), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 105088 ≤ 105152) (by norm_num : 105152 ≤ 105216), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 105088 ≤ 105152) (by norm_num : 105152 ≤ 105216), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 105088 ≤ 105152) (by norm_num : 105152 ≤ 105216), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_104960_105216 :
    (∑ n ∈ Ico 104960 105216, mobiusTreeValue 16 mobiusTable1200001 n) = (2 : ℤ) ∧
    (∑ n ∈ Ico 104960 105216, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (158 : ℕ) ∧
    (∑ n ∈ Ico 104960 105216, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (94918 : ℤ) ∧
    (∑ n ∈ Ico 104960 105216, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1898423055019703390592701321 : ℤ) := by
  rcases cdemPrefixStats_104960_105088 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_105088_105216 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 104960 ≤ 105088) (by norm_num : 105088 ≤ 105216), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 104960 ≤ 105088) (by norm_num : 105088 ≤ 105216), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 104960 ≤ 105088) (by norm_num : 105088 ≤ 105216), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 104960 ≤ 105088) (by norm_num : 105088 ≤ 105216), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_105216_105280 :
    (∑ n ∈ Ico 105216 105280, mobiusTreeValue 16 mobiusTable1200001 n) = (-6 : ℤ) ∧
    (∑ n ∈ Ico 105216 105280, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 105216 105280, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-285013 : ℤ) ∧
    (∑ n ∈ Ico 105216 105280, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-5700342527656542829979818400 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_105280_105344 :
    (∑ n ∈ Ico 105280 105344, mobiusTreeValue 16 mobiusTable1200001 n) = (-6 : ℤ) ∧
    (∑ n ∈ Ico 105280 105344, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 105280 105344, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-284851 : ℤ) ∧
    (∑ n ∈ Ico 105280 105344, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-5697086058531490299340763976 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_105216_105344 :
    (∑ n ∈ Ico 105216 105344, mobiusTreeValue 16 mobiusTable1200001 n) = (-12 : ℤ) ∧
    (∑ n ∈ Ico 105216 105344, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 105216 105344, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-569864 : ℤ) ∧
    (∑ n ∈ Ico 105216 105344, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-11397428586188033129320582376 : ℤ) := by
  rcases cdemPrefixStats_105216_105280 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_105280_105344 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 105216 ≤ 105280) (by norm_num : 105280 ≤ 105344), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 105216 ≤ 105280) (by norm_num : 105280 ≤ 105344), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 105216 ≤ 105280) (by norm_num : 105280 ≤ 105344), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 105216 ≤ 105280) (by norm_num : 105280 ≤ 105344), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_105344_105408 :
    (∑ n ∈ Ico 105344 105408, mobiusTreeValue 16 mobiusTable1200001 n) = (-2 : ℤ) ∧
    (∑ n ∈ Ico 105344 105408, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 105344 105408, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-94847 : ℤ) ∧
    (∑ n ∈ Ico 105344 105408, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-1896929899346311311925959982 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_105408_105472 :
    (∑ n ∈ Ico 105408 105472, mobiusTreeValue 16 mobiusTable1200001 n) = (15 : ℤ) ∧
    (∑ n ∈ Ico 105408 105472, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 105408 105472, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (711252 : ℤ) ∧
    (∑ n ∈ Ico 105408 105472, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (14225237156913786371218308382 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_105344_105472 :
    (∑ n ∈ Ico 105344 105472, mobiusTreeValue 16 mobiusTable1200001 n) = (13 : ℤ) ∧
    (∑ n ∈ Ico 105344 105472, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 105344 105472, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (616405 : ℤ) ∧
    (∑ n ∈ Ico 105344 105472, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (12328307257567475059292348400 : ℤ) := by
  rcases cdemPrefixStats_105344_105408 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_105408_105472 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 105344 ≤ 105408) (by norm_num : 105408 ≤ 105472), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 105344 ≤ 105408) (by norm_num : 105408 ≤ 105472), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 105344 ≤ 105408) (by norm_num : 105408 ≤ 105472), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 105344 ≤ 105408) (by norm_num : 105408 ≤ 105472), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_105216_105472 :
    (∑ n ∈ Ico 105216 105472, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 105216 105472, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (155 : ℕ) ∧
    (∑ n ∈ Ico 105216 105472, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (46541 : ℤ) ∧
    (∑ n ∈ Ico 105216 105472, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (930878671379441929971766024 : ℤ) := by
  rcases cdemPrefixStats_105216_105344 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_105344_105472 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 105216 ≤ 105344) (by norm_num : 105344 ≤ 105472), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 105216 ≤ 105344) (by norm_num : 105344 ≤ 105472), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 105216 ≤ 105344) (by norm_num : 105344 ≤ 105472), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 105216 ≤ 105344) (by norm_num : 105344 ≤ 105472), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_104960_105472 :
    (∑ n ∈ Ico 104960 105472, mobiusTreeValue 16 mobiusTable1200001 n) = (3 : ℤ) ∧
    (∑ n ∈ Ico 104960 105472, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (313 : ℕ) ∧
    (∑ n ∈ Ico 104960 105472, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (141459 : ℤ) ∧
    (∑ n ∈ Ico 104960 105472, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (2829301726399145320564467345 : ℤ) := by
  rcases cdemPrefixStats_104960_105216 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_105216_105472 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 104960 ≤ 105216) (by norm_num : 105216 ≤ 105472), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 104960 ≤ 105216) (by norm_num : 105216 ≤ 105472), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 104960 ≤ 105216) (by norm_num : 105216 ≤ 105472), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 104960 ≤ 105216) (by norm_num : 105216 ≤ 105472), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_104448_105472 :
    (∑ n ∈ Ico 104448 105472, mobiusTreeValue 16 mobiusTable1200001 n) = (-20 : ℤ) ∧
    (∑ n ∈ Ico 104448 105472, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (626 : ℕ) ∧
    (∑ n ∈ Ico 104448 105472, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-955597 : ℤ) ∧
    (∑ n ∈ Ico 104448 105472, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-19112158226293495646753267227 : ℤ) := by
  rcases cdemPrefixStats_104448_104960 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_104960_105472 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 104448 ≤ 104960) (by norm_num : 104960 ≤ 105472), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 104448 ≤ 104960) (by norm_num : 104960 ≤ 105472), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 104448 ≤ 104960) (by norm_num : 104960 ≤ 105472), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 104448 ≤ 104960) (by norm_num : 104960 ≤ 105472), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_105472_105536 :
    (∑ n ∈ Ico 105472 105536, mobiusTreeValue 16 mobiusTable1200001 n) = (-6 : ℤ) ∧
    (∑ n ∈ Ico 105472 105536, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 105472 105536, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-284341 : ℤ) ∧
    (∑ n ∈ Ico 105472 105536, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-5686844689449176713382700364 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_105536_105600 :
    (∑ n ∈ Ico 105536 105600, mobiusTreeValue 16 mobiusTable1200001 n) = (-3 : ℤ) ∧
    (∑ n ∈ Ico 105536 105600, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 105536 105600, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-142090 : ℤ) ∧
    (∑ n ∈ Ico 105536 105600, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-2841806277020023290687268926 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_105472_105600 :
    (∑ n ∈ Ico 105472 105600, mobiusTreeValue 16 mobiusTable1200001 n) = (-9 : ℤ) ∧
    (∑ n ∈ Ico 105472 105600, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (79 : ℕ) ∧
    (∑ n ∈ Ico 105472 105600, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-426431 : ℤ) ∧
    (∑ n ∈ Ico 105472 105600, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-8528650966469200004069969290 : ℤ) := by
  rcases cdemPrefixStats_105472_105536 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_105536_105600 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 105472 ≤ 105536) (by norm_num : 105536 ≤ 105600), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 105472 ≤ 105536) (by norm_num : 105536 ≤ 105600), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 105472 ≤ 105536) (by norm_num : 105536 ≤ 105600), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 105472 ≤ 105536) (by norm_num : 105536 ≤ 105600), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_105600_105664 :
    (∑ n ∈ Ico 105600 105664, mobiusTreeValue 16 mobiusTable1200001 n) = (3 : ℤ) ∧
    (∑ n ∈ Ico 105600 105664, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 105600 105664, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (142083 : ℤ) ∧
    (∑ n ∈ Ico 105600 105664, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (2841661710291389241284879892 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_105664_105728 :
    (∑ n ∈ Ico 105664 105728, mobiusTreeValue 16 mobiusTable1200001 n) = (-6 : ℤ) ∧
    (∑ n ∈ Ico 105664 105728, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 105664 105728, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-283902 : ℤ) ∧
    (∑ n ∈ Ico 105664 105728, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-5678045101259698466178318992 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_105600_105728 :
    (∑ n ∈ Ico 105600 105728, mobiusTreeValue 16 mobiusTable1200001 n) = (-3 : ℤ) ∧
    (∑ n ∈ Ico 105600 105728, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (79 : ℕ) ∧
    (∑ n ∈ Ico 105600 105728, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-141819 : ℤ) ∧
    (∑ n ∈ Ico 105600 105728, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-2836383390968309224893439100 : ℤ) := by
  rcases cdemPrefixStats_105600_105664 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_105664_105728 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 105600 ≤ 105664) (by norm_num : 105664 ≤ 105728), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 105600 ≤ 105664) (by norm_num : 105664 ≤ 105728), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 105600 ≤ 105664) (by norm_num : 105664 ≤ 105728), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 105600 ≤ 105664) (by norm_num : 105664 ≤ 105728), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_105472_105728 :
    (∑ n ∈ Ico 105472 105728, mobiusTreeValue 16 mobiusTable1200001 n) = (-12 : ℤ) ∧
    (∑ n ∈ Ico 105472 105728, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (158 : ℕ) ∧
    (∑ n ∈ Ico 105472 105728, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-568250 : ℤ) ∧
    (∑ n ∈ Ico 105472 105728, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-11365034357437509228963408390 : ℤ) := by
  rcases cdemPrefixStats_105472_105600 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_105600_105728 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 105472 ≤ 105600) (by norm_num : 105600 ≤ 105728), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 105472 ≤ 105600) (by norm_num : 105600 ≤ 105728), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 105472 ≤ 105600) (by norm_num : 105600 ≤ 105728), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 105472 ≤ 105600) (by norm_num : 105600 ≤ 105728), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_105728_105792 :
    (∑ n ∈ Ico 105728 105792, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 105728 105792, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 105728 105792, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-47273 : ℤ) ∧
    (∑ n ∈ Ico 105728 105792, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-945483525255386104862415425 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_105792_105856 :
    (∑ n ∈ Ico 105792 105856, mobiusTreeValue 16 mobiusTable1200001 n) = (8 : ℤ) ∧
    (∑ n ∈ Ico 105792 105856, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 105792 105856, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (377992 : ℤ) ∧
    (∑ n ∈ Ico 105792 105856, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (7559891877256682800960883054 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_105728_105856 :
    (∑ n ∈ Ico 105728 105856, mobiusTreeValue 16 mobiusTable1200001 n) = (7 : ℤ) ∧
    (∑ n ∈ Ico 105728 105856, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 105728 105856, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (330719 : ℤ) ∧
    (∑ n ∈ Ico 105728 105856, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (6614408352001296696098467629 : ℤ) := by
  rcases cdemPrefixStats_105728_105792 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_105792_105856 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 105728 ≤ 105792) (by norm_num : 105792 ≤ 105856), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 105728 ≤ 105792) (by norm_num : 105792 ≤ 105856), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 105728 ≤ 105792) (by norm_num : 105792 ≤ 105856), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 105728 ≤ 105792) (by norm_num : 105792 ≤ 105856), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_105856_105920 :
    (∑ n ∈ Ico 105856 105920, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 105856 105920, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 105856 105920, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-58 : ℤ) ∧
    (∑ n ∈ Ico 105856 105920, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-1159317645928566183536498 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_105920_105984 :
    (∑ n ∈ Ico 105920 105984, mobiusTreeValue 16 mobiusTable1200001 n) = (4 : ℤ) ∧
    (∑ n ∈ Ico 105920 105984, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 105920 105984, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (188800 : ℤ) ∧
    (∑ n ∈ Ico 105920 105984, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (3776042779659966725845905008 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_105856_105984 :
    (∑ n ∈ Ico 105856 105984, mobiusTreeValue 16 mobiusTable1200001 n) = (4 : ℤ) ∧
    (∑ n ∈ Ico 105856 105984, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 105856 105984, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (188742 : ℤ) ∧
    (∑ n ∈ Ico 105856 105984, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (3774883462014038159662368510 : ℤ) := by
  rcases cdemPrefixStats_105856_105920 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_105920_105984 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 105856 ≤ 105920) (by norm_num : 105920 ≤ 105984), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 105856 ≤ 105920) (by norm_num : 105920 ≤ 105984), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 105856 ≤ 105920) (by norm_num : 105920 ≤ 105984), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 105856 ≤ 105920) (by norm_num : 105920 ≤ 105984), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_105728_105984 :
    (∑ n ∈ Ico 105728 105984, mobiusTreeValue 16 mobiusTable1200001 n) = (11 : ℤ) ∧
    (∑ n ∈ Ico 105728 105984, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (155 : ℕ) ∧
    (∑ n ∈ Ico 105728 105984, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (519461 : ℤ) ∧
    (∑ n ∈ Ico 105728 105984, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (10389291814015334855760836139 : ℤ) := by
  rcases cdemPrefixStats_105728_105856 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_105856_105984 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 105728 ≤ 105856) (by norm_num : 105856 ≤ 105984), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 105728 ≤ 105856) (by norm_num : 105856 ≤ 105984), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 105728 ≤ 105856) (by norm_num : 105856 ≤ 105984), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 105728 ≤ 105856) (by norm_num : 105856 ≤ 105984), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_105472_105984 :
    (∑ n ∈ Ico 105472 105984, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 105472 105984, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (313 : ℕ) ∧
    (∑ n ∈ Ico 105472 105984, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-48789 : ℤ) ∧
    (∑ n ∈ Ico 105472 105984, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-975742543422174373202572251 : ℤ) := by
  rcases cdemPrefixStats_105472_105728 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_105728_105984 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 105472 ≤ 105728) (by norm_num : 105728 ≤ 105984), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 105472 ≤ 105728) (by norm_num : 105728 ≤ 105984), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 105472 ≤ 105728) (by norm_num : 105728 ≤ 105984), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 105472 ≤ 105728) (by norm_num : 105728 ≤ 105984), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_105984_106048 :
    (∑ n ∈ Ico 105984 106048, mobiusTreeValue 16 mobiusTable1200001 n) = (2 : ℤ) ∧
    (∑ n ∈ Ico 105984 106048, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 105984 106048, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (94367 : ℤ) ∧
    (∑ n ∈ Ico 105984 106048, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1887415200594068553517406303 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_106048_106112 :
    (∑ n ∈ Ico 106048 106112, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 106048 106112, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 106048 106112, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-47125 : ℤ) ∧
    (∑ n ∈ Ico 106048 106112, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-942515934968499312855693840 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_105984_106112 :
    (∑ n ∈ Ico 105984 106112, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 105984 106112, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 105984 106112, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (47242 : ℤ) ∧
    (∑ n ∈ Ico 105984 106112, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (944899265625569240661712463 : ℤ) := by
  rcases cdemPrefixStats_105984_106048 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_106048_106112 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 105984 ≤ 106048) (by norm_num : 106048 ≤ 106112), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 105984 ≤ 106048) (by norm_num : 106048 ≤ 106112), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 105984 ≤ 106048) (by norm_num : 106048 ≤ 106112), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 105984 ≤ 106048) (by norm_num : 106048 ≤ 106112), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_106112_106176 :
    (∑ n ∈ Ico 106112 106176, mobiusTreeValue 16 mobiusTable1200001 n) = (-2 : ℤ) ∧
    (∑ n ∈ Ico 106112 106176, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 106112 106176, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-94246 : ℤ) ∧
    (∑ n ∈ Ico 106112 106176, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-1884934133696119179706591404 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_106176_106240 :
    (∑ n ∈ Ico 106176 106240, mobiusTreeValue 16 mobiusTable1200001 n) = (4 : ℤ) ∧
    (∑ n ∈ Ico 106176 106240, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 106176 106240, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (188312 : ℤ) ∧
    (∑ n ∈ Ico 106176 106240, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (3766221399741204479116535613 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_106112_106240 :
    (∑ n ∈ Ico 106112 106240, mobiusTreeValue 16 mobiusTable1200001 n) = (2 : ℤ) ∧
    (∑ n ∈ Ico 106112 106240, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 106112 106240, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (94066 : ℤ) ∧
    (∑ n ∈ Ico 106112 106240, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1881287266045085299409944209 : ℤ) := by
  rcases cdemPrefixStats_106112_106176 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_106176_106240 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 106112 ≤ 106176) (by norm_num : 106176 ≤ 106240), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 106112 ≤ 106176) (by norm_num : 106176 ≤ 106240), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 106112 ≤ 106176) (by norm_num : 106176 ≤ 106240), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 106112 ≤ 106176) (by norm_num : 106176 ≤ 106240), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_105984_106240 :
    (∑ n ∈ Ico 105984 106240, mobiusTreeValue 16 mobiusTable1200001 n) = (3 : ℤ) ∧
    (∑ n ∈ Ico 105984 106240, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (155 : ℕ) ∧
    (∑ n ∈ Ico 105984 106240, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (141308 : ℤ) ∧
    (∑ n ∈ Ico 105984 106240, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (2826186531670654540071656672 : ℤ) := by
  rcases cdemPrefixStats_105984_106112 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_106112_106240 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 105984 ≤ 106112) (by norm_num : 106112 ≤ 106240), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 105984 ≤ 106112) (by norm_num : 106112 ≤ 106240), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 105984 ≤ 106112) (by norm_num : 106112 ≤ 106240), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 105984 ≤ 106112) (by norm_num : 106112 ≤ 106240), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_106240_106304 :
    (∑ n ∈ Ico 106240 106304, mobiusTreeValue 16 mobiusTable1200001 n) = (-9 : ℤ) ∧
    (∑ n ∈ Ico 106240 106304, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 106240 106304, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-423425 : ℤ) ∧
    (∑ n ∈ Ico 106240 106304, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-8468622440845672715236453301 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_106304_106368 :
    (∑ n ∈ Ico 106304 106368, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 106304 106368, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 106304 106368, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (31 : ℤ) ∧
    (∑ n ∈ Ico 106304 106368, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (671888689419145760992712 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_106240_106368 :
    (∑ n ∈ Ico 106240 106368, mobiusTreeValue 16 mobiusTable1200001 n) = (-9 : ℤ) ∧
    (∑ n ∈ Ico 106240 106368, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 106240 106368, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-423394 : ℤ) ∧
    (∑ n ∈ Ico 106240 106368, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-8467950552156253569475460589 : ℤ) := by
  rcases cdemPrefixStats_106240_106304 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_106304_106368 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 106240 ≤ 106304) (by norm_num : 106304 ≤ 106368), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 106240 ≤ 106304) (by norm_num : 106304 ≤ 106368), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 106240 ≤ 106304) (by norm_num : 106304 ≤ 106368), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 106240 ≤ 106304) (by norm_num : 106304 ≤ 106368), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_106368_106432 :
    (∑ n ∈ Ico 106368 106432, mobiusTreeValue 16 mobiusTable1200001 n) = (-5 : ℤ) ∧
    (∑ n ∈ Ico 106368 106432, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 106368 106432, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-234920 : ℤ) ∧
    (∑ n ∈ Ico 106368 106432, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-4698488601528830804135638777 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_106432_106496 :
    (∑ n ∈ Ico 106432 106496, mobiusTreeValue 16 mobiusTable1200001 n) = (3 : ℤ) ∧
    (∑ n ∈ Ico 106432 106496, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 106432 106496, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (140806 : ℤ) ∧
    (∑ n ∈ Ico 106432 106496, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (2816124598373968122446453965 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_106368_106496 :
    (∑ n ∈ Ico 106368 106496, mobiusTreeValue 16 mobiusTable1200001 n) = (-2 : ℤ) ∧
    (∑ n ∈ Ico 106368 106496, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (80 : ℕ) ∧
    (∑ n ∈ Ico 106368 106496, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-94114 : ℤ) ∧
    (∑ n ∈ Ico 106368 106496, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-1882364003154862681689184812 : ℤ) := by
  rcases cdemPrefixStats_106368_106432 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_106432_106496 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 106368 ≤ 106432) (by norm_num : 106432 ≤ 106496), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 106368 ≤ 106432) (by norm_num : 106432 ≤ 106496), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 106368 ≤ 106432) (by norm_num : 106432 ≤ 106496), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 106368 ≤ 106432) (by norm_num : 106432 ≤ 106496), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_106240_106496 :
    (∑ n ∈ Ico 106240 106496, mobiusTreeValue 16 mobiusTable1200001 n) = (-11 : ℤ) ∧
    (∑ n ∈ Ico 106240 106496, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (157 : ℕ) ∧
    (∑ n ∈ Ico 106240 106496, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-517508 : ℤ) ∧
    (∑ n ∈ Ico 106240 106496, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-10350314555311116251164645401 : ℤ) := by
  rcases cdemPrefixStats_106240_106368 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_106368_106496 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 106240 ≤ 106368) (by norm_num : 106368 ≤ 106496), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 106240 ≤ 106368) (by norm_num : 106368 ≤ 106496), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 106240 ≤ 106368) (by norm_num : 106368 ≤ 106496), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 106240 ≤ 106368) (by norm_num : 106368 ≤ 106496), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_105984_106496 :
    (∑ n ∈ Ico 105984 106496, mobiusTreeValue 16 mobiusTable1200001 n) = (-8 : ℤ) ∧
    (∑ n ∈ Ico 105984 106496, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (312 : ℕ) ∧
    (∑ n ∈ Ico 105984 106496, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-376200 : ℤ) ∧
    (∑ n ∈ Ico 105984 106496, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-7524128023640461711092988729 : ℤ) := by
  rcases cdemPrefixStats_105984_106240 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_106240_106496 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 105984 ≤ 106240) (by norm_num : 106240 ≤ 106496), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 105984 ≤ 106240) (by norm_num : 106240 ≤ 106496), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 105984 ≤ 106240) (by norm_num : 106240 ≤ 106496), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 105984 ≤ 106240) (by norm_num : 106240 ≤ 106496), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_105472_106496 :
    (∑ n ∈ Ico 105472 106496, mobiusTreeValue 16 mobiusTable1200001 n) = (-9 : ℤ) ∧
    (∑ n ∈ Ico 105472 106496, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (625 : ℕ) ∧
    (∑ n ∈ Ico 105472 106496, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-424989 : ℤ) ∧
    (∑ n ∈ Ico 105472 106496, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-8499870567062636084295560980 : ℤ) := by
  rcases cdemPrefixStats_105472_105984 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_105984_106496 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 105472 ≤ 105984) (by norm_num : 105984 ≤ 106496), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 105472 ≤ 105984) (by norm_num : 105984 ≤ 106496), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 105472 ≤ 105984) (by norm_num : 105984 ≤ 106496), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 105472 ≤ 105984) (by norm_num : 105984 ≤ 106496), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_104448_106496 :
    (∑ n ∈ Ico 104448 106496, mobiusTreeValue 16 mobiusTable1200001 n) = (-29 : ℤ) ∧
    (∑ n ∈ Ico 104448 106496, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (1251 : ℕ) ∧
    (∑ n ∈ Ico 104448 106496, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-1380586 : ℤ) ∧
    (∑ n ∈ Ico 104448 106496, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-27612028793356131731048828207 : ℤ) := by
  rcases cdemPrefixStats_104448_105472 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_105472_106496 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 104448 ≤ 105472) (by norm_num : 105472 ≤ 106496), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 104448 ≤ 105472) (by norm_num : 105472 ≤ 106496), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 104448 ≤ 105472) (by norm_num : 105472 ≤ 106496), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 104448 ≤ 105472) (by norm_num : 105472 ≤ 106496), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_102400_106496 :
    (∑ n ∈ Ico 102400 106496, mobiusTreeValue 16 mobiusTable1200001 n) = (29 : ℤ) ∧
    (∑ n ∈ Ico 102400 106496, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (2487 : ℕ) ∧
    (∑ n ∈ Ico 102400 106496, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (1431362 : ℤ) ∧
    (∑ n ∈ Ico 102400 106496, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (28627378348167438853142479503 : ℤ) := by
  rcases cdemPrefixStats_102400_104448 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_104448_106496 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 102400 ≤ 104448) (by norm_num : 104448 ≤ 106496), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 102400 ≤ 104448) (by norm_num : 104448 ≤ 106496), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 102400 ≤ 104448) (by norm_num : 104448 ≤ 106496), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 102400 ≤ 104448) (by norm_num : 104448 ≤ 106496), hR1, hR2] <;> norm_num

theorem cdemPrefixGroup025_checked_complete :
    (∑ n ∈ Ico 102400 106496, mobiusTreeValue 16 mobiusTable1200001 n) = (29 : ℤ) ∧
    (∑ n ∈ Ico 102400 106496, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (2487 : ℕ) ∧
    (∑ n ∈ Ico 102400 106496, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (1431362 : ℤ) ∧
    (∑ n ∈ Ico 102400 106496, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (28627378348167438853142479503 : ℤ) := cdemPrefixStats_102400_106496
end Helfgott
#print axioms Helfgott.cdemPrefixGroup025_checked_complete

open Helfgott Finset
open scoped BigOperators

theorem solution :
    (∑ n ∈ Ico 102400 106496, mobiusTreeValue 16 mobiusTable1200001 n) = (29 : ℤ) ∧
    (∑ n ∈ Ico 102400 106496, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (2487 : ℕ) ∧
    (∑ n ∈ Ico 102400 106496, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (1431362 : ℤ) ∧
    (∑ n ∈ Ico 102400 106496, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (28627378348167438853142479503 : ℤ) := Helfgott.cdemPrefixGroup025_checked_complete
#print axioms solution
