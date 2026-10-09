-- Prove2me | solution 1 for Helfgott.cdemPrefixGroup030_checked
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-09T02:20:59.812118+00:00
-- url     : https://prove2.me/submissions/f1efab19-4ffd-451c-9870-bfb5fd7ef193

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
private theorem cdemPrefixStats_122880_122944 :
    (∑ n ∈ Ico 122880 122944, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 122880 122944, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 122880 122944, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (40675 : ℤ) ∧
    (∑ n ∈ Ico 122880 122944, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (813543905976166260336827922 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_122944_123008 :
    (∑ n ∈ Ico 122944 123008, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 122944 123008, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 122944 123008, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-40616 : ℤ) ∧
    (∑ n ∈ Ico 122944 123008, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-812353677748770348058063937 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_122880_123008 :
    (∑ n ∈ Ico 122880 123008, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 122880 123008, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (80 : ℕ) ∧
    (∑ n ∈ Ico 122880 123008, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (59 : ℤ) ∧
    (∑ n ∈ Ico 122880 123008, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1190228227395912278763985 : ℤ) := by
  rcases cdemPrefixStats_122880_122944 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_122944_123008 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 122880 ≤ 122944) (by norm_num : 122944 ≤ 123008), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 122880 ≤ 122944) (by norm_num : 122944 ≤ 123008), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 122880 ≤ 122944) (by norm_num : 122944 ≤ 123008), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 122880 ≤ 122944) (by norm_num : 122944 ≤ 123008), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_123008_123072 :
    (∑ n ∈ Ico 123008 123072, mobiusTreeValue 16 mobiusTable1200001 n) = (5 : ℤ) ∧
    (∑ n ∈ Ico 123008 123072, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 123008 123072, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (203142 : ℤ) ∧
    (∑ n ∈ Ico 123008 123072, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (4062913357462877522994647769 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_123072_123136 :
    (∑ n ∈ Ico 123072 123136, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 123072 123136, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 123072 123136, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-21 : ℤ) ∧
    (∑ n ∈ Ico 123072 123136, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-475039542775688531535578 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_123008_123136 :
    (∑ n ∈ Ico 123008 123136, mobiusTreeValue 16 mobiusTable1200001 n) = (5 : ℤ) ∧
    (∑ n ∈ Ico 123008 123136, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (81 : ℕ) ∧
    (∑ n ∈ Ico 123008 123136, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (203121 : ℤ) ∧
    (∑ n ∈ Ico 123008 123136, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (4062438317920101834463112191 : ℤ) := by
  rcases cdemPrefixStats_123008_123072 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_123072_123136 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 123008 ≤ 123072) (by norm_num : 123072 ≤ 123136), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 123008 ≤ 123072) (by norm_num : 123072 ≤ 123136), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 123008 ≤ 123072) (by norm_num : 123072 ≤ 123136), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 123008 ≤ 123072) (by norm_num : 123072 ≤ 123136), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_122880_123136 :
    (∑ n ∈ Ico 122880 123136, mobiusTreeValue 16 mobiusTable1200001 n) = (5 : ℤ) ∧
    (∑ n ∈ Ico 122880 123136, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (161 : ℕ) ∧
    (∑ n ∈ Ico 122880 123136, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (203180 : ℤ) ∧
    (∑ n ∈ Ico 122880 123136, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (4063628546147497746741876176 : ℤ) := by
  rcases cdemPrefixStats_122880_123008 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_123008_123136 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 122880 ≤ 123008) (by norm_num : 123008 ≤ 123136), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 122880 ≤ 123008) (by norm_num : 123008 ≤ 123136), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 122880 ≤ 123008) (by norm_num : 123008 ≤ 123136), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 122880 ≤ 123008) (by norm_num : 123008 ≤ 123136), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_123136_123200 :
    (∑ n ∈ Ico 123136 123200, mobiusTreeValue 16 mobiusTable1200001 n) = (6 : ℤ) ∧
    (∑ n ∈ Ico 123136 123200, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 123136 123200, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (243550 : ℤ) ∧
    (∑ n ∈ Ico 123136 123200, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (4871085403498273332414007596 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_123200_123264 :
    (∑ n ∈ Ico 123200 123264, mobiusTreeValue 16 mobiusTable1200001 n) = (-7 : ℤ) ∧
    (∑ n ∈ Ico 123200 123264, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 123200 123264, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-284054 : ℤ) ∧
    (∑ n ∈ Ico 123200 123264, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-5681159498942266606228895097 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_123136_123264 :
    (∑ n ∈ Ico 123136 123264, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 123136 123264, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (75 : ℕ) ∧
    (∑ n ∈ Ico 123136 123264, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-40504 : ℤ) ∧
    (∑ n ∈ Ico 123136 123264, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-810074095443993273814887501 : ℤ) := by
  rcases cdemPrefixStats_123136_123200 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_123200_123264 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 123136 ≤ 123200) (by norm_num : 123200 ≤ 123264), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 123136 ≤ 123200) (by norm_num : 123200 ≤ 123264), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 123136 ≤ 123200) (by norm_num : 123200 ≤ 123264), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 123136 ≤ 123200) (by norm_num : 123200 ≤ 123264), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_123264_123328 :
    (∑ n ∈ Ico 123264 123328, mobiusTreeValue 16 mobiusTable1200001 n) = (-7 : ℤ) ∧
    (∑ n ∈ Ico 123264 123328, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 123264 123328, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-283885 : ℤ) ∧
    (∑ n ∈ Ico 123264 123328, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-5677756147164140289791993775 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_123328_123392 :
    (∑ n ∈ Ico 123328 123392, mobiusTreeValue 16 mobiusTable1200001 n) = (8 : ℤ) ∧
    (∑ n ∈ Ico 123328 123392, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 123328 123392, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (324253 : ℤ) ∧
    (∑ n ∈ Ico 123328 123392, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (6485130517359314862644546117 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_123264_123392 :
    (∑ n ∈ Ico 123264 123392, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 123264 123392, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 123264 123392, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (40368 : ℤ) ∧
    (∑ n ∈ Ico 123264 123392, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (807374370195174572852552342 : ℤ) := by
  rcases cdemPrefixStats_123264_123328 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_123328_123392 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 123264 ≤ 123328) (by norm_num : 123328 ≤ 123392), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 123264 ≤ 123328) (by norm_num : 123328 ≤ 123392), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 123264 ≤ 123328) (by norm_num : 123328 ≤ 123392), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 123264 ≤ 123328) (by norm_num : 123328 ≤ 123392), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_123136_123392 :
    (∑ n ∈ Ico 123136 123392, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 123136 123392, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (152 : ℕ) ∧
    (∑ n ∈ Ico 123136 123392, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-136 : ℤ) ∧
    (∑ n ∈ Ico 123136 123392, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-2699725248818700962335159 : ℤ) := by
  rcases cdemPrefixStats_123136_123264 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_123264_123392 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 123136 ≤ 123264) (by norm_num : 123264 ≤ 123392), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 123136 ≤ 123264) (by norm_num : 123264 ≤ 123392), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 123136 ≤ 123264) (by norm_num : 123264 ≤ 123392), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 123136 ≤ 123264) (by norm_num : 123264 ≤ 123392), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_122880_123392 :
    (∑ n ∈ Ico 122880 123392, mobiusTreeValue 16 mobiusTable1200001 n) = (5 : ℤ) ∧
    (∑ n ∈ Ico 122880 123392, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (313 : ℕ) ∧
    (∑ n ∈ Ico 122880 123392, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (203044 : ℤ) ∧
    (∑ n ∈ Ico 122880 123392, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (4060928820898679045779541017 : ℤ) := by
  rcases cdemPrefixStats_122880_123136 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_123136_123392 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 122880 ≤ 123136) (by norm_num : 123136 ≤ 123392), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 122880 ≤ 123136) (by norm_num : 123136 ≤ 123392), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 122880 ≤ 123136) (by norm_num : 123136 ≤ 123392), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 122880 ≤ 123136) (by norm_num : 123136 ≤ 123392), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_123392_123456 :
    (∑ n ∈ Ico 123392 123456, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 123392 123456, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 123392 123456, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (40524 : ℤ) ∧
    (∑ n ∈ Ico 123392 123456, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (810471265420253243692563412 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_123456_123520 :
    (∑ n ∈ Ico 123456 123520, mobiusTreeValue 16 mobiusTable1200001 n) = (-12 : ℤ) ∧
    (∑ n ∈ Ico 123456 123520, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (42 : ℕ) ∧
    (∑ n ∈ Ico 123456 123520, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-485853 : ℤ) ∧
    (∑ n ∈ Ico 123456 123520, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-9717228810471423242743160940 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_123392_123520 :
    (∑ n ∈ Ico 123392 123520, mobiusTreeValue 16 mobiusTable1200001 n) = (-11 : ℤ) ∧
    (∑ n ∈ Ico 123392 123520, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (81 : ℕ) ∧
    (∑ n ∈ Ico 123392 123520, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-445329 : ℤ) ∧
    (∑ n ∈ Ico 123392 123520, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-8906757545051169999050597528 : ℤ) := by
  rcases cdemPrefixStats_123392_123456 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_123456_123520 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 123392 ≤ 123456) (by norm_num : 123456 ≤ 123520), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 123392 ≤ 123456) (by norm_num : 123456 ≤ 123520), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 123392 ≤ 123456) (by norm_num : 123456 ≤ 123520), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 123392 ≤ 123456) (by norm_num : 123456 ≤ 123520), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_123520_123584 :
    (∑ n ∈ Ico 123520 123584, mobiusTreeValue 16 mobiusTable1200001 n) = (-6 : ℤ) ∧
    (∑ n ∈ Ico 123520 123584, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (36 : ℕ) ∧
    (∑ n ∈ Ico 123520 123584, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-242808 : ℤ) ∧
    (∑ n ∈ Ico 123520 123584, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-4856150074848982150432389416 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_123584_123648 :
    (∑ n ∈ Ico 123584 123648, mobiusTreeValue 16 mobiusTable1200001 n) = (-7 : ℤ) ∧
    (∑ n ∈ Ico 123584 123648, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 123584 123648, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-283141 : ℤ) ∧
    (∑ n ∈ Ico 123584 123648, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-5662939677800988736270545874 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_123520_123648 :
    (∑ n ∈ Ico 123520 123648, mobiusTreeValue 16 mobiusTable1200001 n) = (-13 : ℤ) ∧
    (∑ n ∈ Ico 123520 123648, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 123520 123648, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-525949 : ℤ) ∧
    (∑ n ∈ Ico 123520 123648, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-10519089752649970886702935290 : ℤ) := by
  rcases cdemPrefixStats_123520_123584 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_123584_123648 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 123520 ≤ 123584) (by norm_num : 123584 ≤ 123648), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 123520 ≤ 123584) (by norm_num : 123584 ≤ 123648), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 123520 ≤ 123584) (by norm_num : 123584 ≤ 123648), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 123520 ≤ 123584) (by norm_num : 123584 ≤ 123648), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_123392_123648 :
    (∑ n ∈ Ico 123392 123648, mobiusTreeValue 16 mobiusTable1200001 n) = (-24 : ℤ) ∧
    (∑ n ∈ Ico 123392 123648, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (158 : ℕ) ∧
    (∑ n ∈ Ico 123392 123648, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-971278 : ℤ) ∧
    (∑ n ∈ Ico 123392 123648, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-19425847297701140885753532818 : ℤ) := by
  rcases cdemPrefixStats_123392_123520 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_123520_123648 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 123392 ≤ 123520) (by norm_num : 123520 ≤ 123648), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 123392 ≤ 123520) (by norm_num : 123520 ≤ 123648), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 123392 ≤ 123520) (by norm_num : 123520 ≤ 123648), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 123392 ≤ 123520) (by norm_num : 123520 ≤ 123648), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_123648_123712 :
    (∑ n ∈ Ico 123648 123712, mobiusTreeValue 16 mobiusTable1200001 n) = (6 : ℤ) ∧
    (∑ n ∈ Ico 123648 123712, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 123648 123712, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (242536 : ℤ) ∧
    (∑ n ∈ Ico 123648 123712, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (4850843277871461921247764213 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_123712_123776 :
    (∑ n ∈ Ico 123712 123776, mobiusTreeValue 16 mobiusTable1200001 n) = (2 : ℤ) ∧
    (∑ n ∈ Ico 123712 123776, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 123712 123776, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (80761 : ℤ) ∧
    (∑ n ∈ Ico 123712 123776, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1615267003255408263435929953 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_123648_123776 :
    (∑ n ∈ Ico 123648 123776, mobiusTreeValue 16 mobiusTable1200001 n) = (8 : ℤ) ∧
    (∑ n ∈ Ico 123648 123776, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (80 : ℕ) ∧
    (∑ n ∈ Ico 123648 123776, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (323297 : ℤ) ∧
    (∑ n ∈ Ico 123648 123776, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (6466110281126870184683694166 : ℤ) := by
  rcases cdemPrefixStats_123648_123712 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_123712_123776 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 123648 ≤ 123712) (by norm_num : 123712 ≤ 123776), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 123648 ≤ 123712) (by norm_num : 123712 ≤ 123776), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 123648 ≤ 123712) (by norm_num : 123712 ≤ 123776), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 123648 ≤ 123712) (by norm_num : 123712 ≤ 123776), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_123776_123840 :
    (∑ n ∈ Ico 123776 123840, mobiusTreeValue 16 mobiusTable1200001 n) = (-5 : ℤ) ∧
    (∑ n ∈ Ico 123776 123840, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 123776 123840, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-201913 : ℤ) ∧
    (∑ n ∈ Ico 123776 123840, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-4038361269078083133837894499 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_123840_123904 :
    (∑ n ∈ Ico 123840 123904, mobiusTreeValue 16 mobiusTable1200001 n) = (6 : ℤ) ∧
    (∑ n ∈ Ico 123840 123904, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 123840 123904, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (242194 : ℤ) ∧
    (∑ n ∈ Ico 123840 123904, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (4843963946783203618685676233 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_123776_123904 :
    (∑ n ∈ Ico 123776 123904, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 123776 123904, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 123776 123904, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (40281 : ℤ) ∧
    (∑ n ∈ Ico 123776 123904, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (805602677705120484847781734 : ℤ) := by
  rcases cdemPrefixStats_123776_123840 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_123840_123904 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 123776 ≤ 123840) (by norm_num : 123840 ≤ 123904), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 123776 ≤ 123840) (by norm_num : 123840 ≤ 123904), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 123776 ≤ 123840) (by norm_num : 123840 ≤ 123904), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 123776 ≤ 123840) (by norm_num : 123840 ≤ 123904), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_123648_123904 :
    (∑ n ∈ Ico 123648 123904, mobiusTreeValue 16 mobiusTable1200001 n) = (9 : ℤ) ∧
    (∑ n ∈ Ico 123648 123904, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (157 : ℕ) ∧
    (∑ n ∈ Ico 123648 123904, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (363578 : ℤ) ∧
    (∑ n ∈ Ico 123648 123904, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (7271712958831990669531475900 : ℤ) := by
  rcases cdemPrefixStats_123648_123776 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_123776_123904 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 123648 ≤ 123776) (by norm_num : 123776 ≤ 123904), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 123648 ≤ 123776) (by norm_num : 123776 ≤ 123904), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 123648 ≤ 123776) (by norm_num : 123776 ≤ 123904), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 123648 ≤ 123776) (by norm_num : 123776 ≤ 123904), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_123392_123904 :
    (∑ n ∈ Ico 123392 123904, mobiusTreeValue 16 mobiusTable1200001 n) = (-15 : ℤ) ∧
    (∑ n ∈ Ico 123392 123904, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (315 : ℕ) ∧
    (∑ n ∈ Ico 123392 123904, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-607700 : ℤ) ∧
    (∑ n ∈ Ico 123392 123904, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-12154134338869150216222056918 : ℤ) := by
  rcases cdemPrefixStats_123392_123648 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_123648_123904 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 123392 ≤ 123648) (by norm_num : 123648 ≤ 123904), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 123392 ≤ 123648) (by norm_num : 123648 ≤ 123904), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 123392 ≤ 123648) (by norm_num : 123648 ≤ 123904), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 123392 ≤ 123648) (by norm_num : 123648 ≤ 123904), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_122880_123904 :
    (∑ n ∈ Ico 122880 123904, mobiusTreeValue 16 mobiusTable1200001 n) = (-10 : ℤ) ∧
    (∑ n ∈ Ico 122880 123904, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (628 : ℕ) ∧
    (∑ n ∈ Ico 122880 123904, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-404656 : ℤ) ∧
    (∑ n ∈ Ico 122880 123904, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-8093205517970471170442515901 : ℤ) := by
  rcases cdemPrefixStats_122880_123392 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_123392_123904 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 122880 ≤ 123392) (by norm_num : 123392 ≤ 123904), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 122880 ≤ 123392) (by norm_num : 123392 ≤ 123904), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 122880 ≤ 123392) (by norm_num : 123392 ≤ 123904), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 122880 ≤ 123392) (by norm_num : 123392 ≤ 123904), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_123904_123968 :
    (∑ n ∈ Ico 123904 123968, mobiusTreeValue 16 mobiusTable1200001 n) = (-3 : ℤ) ∧
    (∑ n ∈ Ico 123904 123968, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 123904 123968, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-121026 : ℤ) ∧
    (∑ n ∈ Ico 123904 123968, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-2420578033590948942426280459 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_123968_124032 :
    (∑ n ∈ Ico 123968 124032, mobiusTreeValue 16 mobiusTable1200001 n) = (4 : ℤ) ∧
    (∑ n ∈ Ico 123968 124032, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 123968 124032, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (161233 : ℤ) ∧
    (∑ n ∈ Ico 123968 124032, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (3224713945754668700639432105 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_123904_124032 :
    (∑ n ∈ Ico 123904 124032, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 123904 124032, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (79 : ℕ) ∧
    (∑ n ∈ Ico 123904 124032, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (40207 : ℤ) ∧
    (∑ n ∈ Ico 123904 124032, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (804135912163719758213151646 : ℤ) := by
  rcases cdemPrefixStats_123904_123968 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_123968_124032 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 123904 ≤ 123968) (by norm_num : 123968 ≤ 124032), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 123904 ≤ 123968) (by norm_num : 123968 ≤ 124032), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 123904 ≤ 123968) (by norm_num : 123968 ≤ 124032), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 123904 ≤ 123968) (by norm_num : 123968 ≤ 124032), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_124032_124096 :
    (∑ n ∈ Ico 124032 124096, mobiusTreeValue 16 mobiusTable1200001 n) = (6 : ℤ) ∧
    (∑ n ∈ Ico 124032 124096, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 124032 124096, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (241832 : ℤ) ∧
    (∑ n ∈ Ico 124032 124096, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (4836694460978828531187003028 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_124096_124160 :
    (∑ n ∈ Ico 124096 124160, mobiusTreeValue 16 mobiusTable1200001 n) = (-5 : ℤ) ∧
    (∑ n ∈ Ico 124096 124160, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 124096 124160, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-201381 : ℤ) ∧
    (∑ n ∈ Ico 124096 124160, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-4027684743428725203123281949 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_124032_124160 :
    (∑ n ∈ Ico 124032 124160, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 124032 124160, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (79 : ℕ) ∧
    (∑ n ∈ Ico 124032 124160, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (40451 : ℤ) ∧
    (∑ n ∈ Ico 124032 124160, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (809009717550103328063721079 : ℤ) := by
  rcases cdemPrefixStats_124032_124096 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_124096_124160 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 124032 ≤ 124096) (by norm_num : 124096 ≤ 124160), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 124032 ≤ 124096) (by norm_num : 124096 ≤ 124160), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 124032 ≤ 124096) (by norm_num : 124096 ≤ 124160), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 124032 ≤ 124096) (by norm_num : 124096 ≤ 124160), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_123904_124160 :
    (∑ n ∈ Ico 123904 124160, mobiusTreeValue 16 mobiusTable1200001 n) = (2 : ℤ) ∧
    (∑ n ∈ Ico 123904 124160, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (158 : ℕ) ∧
    (∑ n ∈ Ico 123904 124160, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (80658 : ℤ) ∧
    (∑ n ∈ Ico 123904 124160, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1613145629713823086276872725 : ℤ) := by
  rcases cdemPrefixStats_123904_124032 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_124032_124160 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 123904 ≤ 124032) (by norm_num : 124032 ≤ 124160), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 123904 ≤ 124032) (by norm_num : 124032 ≤ 124160), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 123904 ≤ 124032) (by norm_num : 124032 ≤ 124160), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 123904 ≤ 124032) (by norm_num : 124032 ≤ 124160), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_124160_124224 :
    (∑ n ∈ Ico 124160 124224, mobiusTreeValue 16 mobiusTable1200001 n) = (2 : ℤ) ∧
    (∑ n ∈ Ico 124160 124224, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 124160 124224, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (80543 : ℤ) ∧
    (∑ n ∈ Ico 124160 124224, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1610857203611884214016056464 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_124224_124288 :
    (∑ n ∈ Ico 124224 124288, mobiusTreeValue 16 mobiusTable1200001 n) = (6 : ℤ) ∧
    (∑ n ∈ Ico 124224 124288, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 124224 124288, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (241420 : ℤ) ∧
    (∑ n ∈ Ico 124224 124288, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (4828475151006108989322721418 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_124160_124288 :
    (∑ n ∈ Ico 124160 124288, mobiusTreeValue 16 mobiusTable1200001 n) = (8 : ℤ) ∧
    (∑ n ∈ Ico 124160 124288, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 124160 124288, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (321963 : ℤ) ∧
    (∑ n ∈ Ico 124160 124288, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (6439332354617993203338777882 : ℤ) := by
  rcases cdemPrefixStats_124160_124224 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_124224_124288 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 124160 ≤ 124224) (by norm_num : 124224 ≤ 124288), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 124160 ≤ 124224) (by norm_num : 124224 ≤ 124288), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 124160 ≤ 124224) (by norm_num : 124224 ≤ 124288), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 124160 ≤ 124224) (by norm_num : 124224 ≤ 124288), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_124288_124352 :
    (∑ n ∈ Ico 124288 124352, mobiusTreeValue 16 mobiusTable1200001 n) = (-17 : ℤ) ∧
    (∑ n ∈ Ico 124288 124352, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 124288 124352, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-683703 : ℤ) ∧
    (∑ n ∈ Ico 124288 124352, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-13674207867543086158819117578 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_124352_124416 :
    (∑ n ∈ Ico 124352 124416, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 124352 124416, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 124352 124416, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (40167 : ℤ) ∧
    (∑ n ∈ Ico 124352 124416, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (803302537502713876298698788 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_124288_124416 :
    (∑ n ∈ Ico 124288 124416, mobiusTreeValue 16 mobiusTable1200001 n) = (-16 : ℤ) ∧
    (∑ n ∈ Ico 124288 124416, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 124288 124416, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-643536 : ℤ) ∧
    (∑ n ∈ Ico 124288 124416, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-12870905330040372282520418790 : ℤ) := by
  rcases cdemPrefixStats_124288_124352 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_124352_124416 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 124288 ≤ 124352) (by norm_num : 124352 ≤ 124416), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 124288 ≤ 124352) (by norm_num : 124352 ≤ 124416), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 124288 ≤ 124352) (by norm_num : 124352 ≤ 124416), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 124288 ≤ 124352) (by norm_num : 124352 ≤ 124416), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_124160_124416 :
    (∑ n ∈ Ico 124160 124416, mobiusTreeValue 16 mobiusTable1200001 n) = (-8 : ℤ) ∧
    (∑ n ∈ Ico 124160 124416, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (156 : ℕ) ∧
    (∑ n ∈ Ico 124160 124416, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-321573 : ℤ) ∧
    (∑ n ∈ Ico 124160 124416, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-6431572975422379079181640908 : ℤ) := by
  rcases cdemPrefixStats_124160_124288 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_124288_124416 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 124160 ≤ 124288) (by norm_num : 124288 ≤ 124416), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 124160 ≤ 124288) (by norm_num : 124288 ≤ 124416), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 124160 ≤ 124288) (by norm_num : 124288 ≤ 124416), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 124160 ≤ 124288) (by norm_num : 124288 ≤ 124416), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_123904_124416 :
    (∑ n ∈ Ico 123904 124416, mobiusTreeValue 16 mobiusTable1200001 n) = (-6 : ℤ) ∧
    (∑ n ∈ Ico 123904 124416, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (314 : ℕ) ∧
    (∑ n ∈ Ico 123904 124416, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-240915 : ℤ) ∧
    (∑ n ∈ Ico 123904 124416, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-4818427345708555992904768183 : ℤ) := by
  rcases cdemPrefixStats_123904_124160 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_124160_124416 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 123904 ≤ 124160) (by norm_num : 124160 ≤ 124416), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 123904 ≤ 124160) (by norm_num : 124160 ≤ 124416), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 123904 ≤ 124160) (by norm_num : 124160 ≤ 124416), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 123904 ≤ 124160) (by norm_num : 124160 ≤ 124416), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_124416_124480 :
    (∑ n ∈ Ico 124416 124480, mobiusTreeValue 16 mobiusTable1200001 n) = (-2 : ℤ) ∧
    (∑ n ∈ Ico 124416 124480, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 124416 124480, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-80346 : ℤ) ∧
    (∑ n ∈ Ico 124416 124480, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-1606922625687220630987980693 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_124480_124544 :
    (∑ n ∈ Ico 124480 124544, mobiusTreeValue 16 mobiusTable1200001 n) = (-5 : ℤ) ∧
    (∑ n ∈ Ico 124480 124544, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 124480 124544, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-200797 : ℤ) ∧
    (∑ n ∈ Ico 124480 124544, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-4015980418631539093217706363 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_124416_124544 :
    (∑ n ∈ Ico 124416 124544, mobiusTreeValue 16 mobiusTable1200001 n) = (-7 : ℤ) ∧
    (∑ n ∈ Ico 124416 124544, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (81 : ℕ) ∧
    (∑ n ∈ Ico 124416 124544, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-281143 : ℤ) ∧
    (∑ n ∈ Ico 124416 124544, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-5622903044318759724205687056 : ℤ) := by
  rcases cdemPrefixStats_124416_124480 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_124480_124544 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 124416 ≤ 124480) (by norm_num : 124480 ≤ 124544), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 124416 ≤ 124480) (by norm_num : 124480 ≤ 124544), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 124416 ≤ 124480) (by norm_num : 124480 ≤ 124544), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 124416 ≤ 124480) (by norm_num : 124480 ≤ 124544), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_124544_124608 :
    (∑ n ∈ Ico 124544 124608, mobiusTreeValue 16 mobiusTable1200001 n) = (5 : ℤ) ∧
    (∑ n ∈ Ico 124544 124608, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (35 : ℕ) ∧
    (∑ n ∈ Ico 124544 124608, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (200648 : ℤ) ∧
    (∑ n ∈ Ico 124544 124608, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (4012995816141352838277008173 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_124608_124672 :
    (∑ n ∈ Ico 124608 124672, mobiusTreeValue 16 mobiusTable1200001 n) = (2 : ℤ) ∧
    (∑ n ∈ Ico 124608 124672, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 124608 124672, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (80295 : ℤ) ∧
    (∑ n ∈ Ico 124608 124672, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1605927950443161838741222816 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_124544_124672 :
    (∑ n ∈ Ico 124544 124672, mobiusTreeValue 16 mobiusTable1200001 n) = (7 : ℤ) ∧
    (∑ n ∈ Ico 124544 124672, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (75 : ℕ) ∧
    (∑ n ∈ Ico 124544 124672, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (280943 : ℤ) ∧
    (∑ n ∈ Ico 124544 124672, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (5618923766584514677018230989 : ℤ) := by
  rcases cdemPrefixStats_124544_124608 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_124608_124672 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 124544 ≤ 124608) (by norm_num : 124608 ≤ 124672), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 124544 ≤ 124608) (by norm_num : 124608 ≤ 124672), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 124544 ≤ 124608) (by norm_num : 124608 ≤ 124672), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 124544 ≤ 124608) (by norm_num : 124608 ≤ 124672), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_124416_124672 :
    (∑ n ∈ Ico 124416 124672, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 124416 124672, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (156 : ℕ) ∧
    (∑ n ∈ Ico 124416 124672, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-200 : ℤ) ∧
    (∑ n ∈ Ico 124416 124672, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-3979277734245047187456067 : ℤ) := by
  rcases cdemPrefixStats_124416_124544 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_124544_124672 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 124416 ≤ 124544) (by norm_num : 124544 ≤ 124672), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 124416 ≤ 124544) (by norm_num : 124544 ≤ 124672), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 124416 ≤ 124544) (by norm_num : 124544 ≤ 124672), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 124416 ≤ 124544) (by norm_num : 124544 ≤ 124672), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_124672_124736 :
    (∑ n ∈ Ico 124672 124736, mobiusTreeValue 16 mobiusTable1200001 n) = (-3 : ℤ) ∧
    (∑ n ∈ Ico 124672 124736, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 124672 124736, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-120274 : ℤ) ∧
    (∑ n ∈ Ico 124672 124736, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-2405497348281439499603981713 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_124736_124800 :
    (∑ n ∈ Ico 124736 124800, mobiusTreeValue 16 mobiusTable1200001 n) = (-11 : ℤ) ∧
    (∑ n ∈ Ico 124736 124800, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 124736 124800, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-440785 : ℤ) ∧
    (∑ n ∈ Ico 124736 124800, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-8815753249150759871131968368 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_124672_124800 :
    (∑ n ∈ Ico 124672 124800, mobiusTreeValue 16 mobiusTable1200001 n) = (-14 : ℤ) ∧
    (∑ n ∈ Ico 124672 124800, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 124672 124800, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-561059 : ℤ) ∧
    (∑ n ∈ Ico 124672 124800, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-11221250597432199370735950081 : ℤ) := by
  rcases cdemPrefixStats_124672_124736 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_124736_124800 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 124672 ≤ 124736) (by norm_num : 124736 ≤ 124800), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 124672 ≤ 124736) (by norm_num : 124736 ≤ 124800), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 124672 ≤ 124736) (by norm_num : 124736 ≤ 124800), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 124672 ≤ 124736) (by norm_num : 124736 ≤ 124800), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_124800_124864 :
    (∑ n ∈ Ico 124800 124864, mobiusTreeValue 16 mobiusTable1200001 n) = (9 : ℤ) ∧
    (∑ n ∈ Ico 124800 124864, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 124800 124864, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (360485 : ℤ) ∧
    (∑ n ∈ Ico 124800 124864, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (7209850442595414843780164934 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_124864_124928 :
    (∑ n ∈ Ico 124864 124928, mobiusTreeValue 16 mobiusTable1200001 n) = (5 : ℤ) ∧
    (∑ n ∈ Ico 124864 124928, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 124864 124928, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (200178 : ℤ) ∧
    (∑ n ∈ Ico 124864 124928, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (4003561623431453157003755282 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_124800_124928 :
    (∑ n ∈ Ico 124800 124928, mobiusTreeValue 16 mobiusTable1200001 n) = (14 : ℤ) ∧
    (∑ n ∈ Ico 124800 124928, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (80 : ℕ) ∧
    (∑ n ∈ Ico 124800 124928, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (560663 : ℤ) ∧
    (∑ n ∈ Ico 124800 124928, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (11213412066026868000783920216 : ℤ) := by
  rcases cdemPrefixStats_124800_124864 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_124864_124928 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 124800 ≤ 124864) (by norm_num : 124864 ≤ 124928), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 124800 ≤ 124864) (by norm_num : 124864 ≤ 124928), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 124800 ≤ 124864) (by norm_num : 124864 ≤ 124928), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 124800 ≤ 124864) (by norm_num : 124864 ≤ 124928), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_124672_124928 :
    (∑ n ∈ Ico 124672 124928, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 124672 124928, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (158 : ℕ) ∧
    (∑ n ∈ Ico 124672 124928, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-396 : ℤ) ∧
    (∑ n ∈ Ico 124672 124928, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-7838531405331369952029865 : ℤ) := by
  rcases cdemPrefixStats_124672_124800 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_124800_124928 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 124672 ≤ 124800) (by norm_num : 124800 ≤ 124928), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 124672 ≤ 124800) (by norm_num : 124800 ≤ 124928), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 124672 ≤ 124800) (by norm_num : 124800 ≤ 124928), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 124672 ≤ 124800) (by norm_num : 124800 ≤ 124928), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_124416_124928 :
    (∑ n ∈ Ico 124416 124928, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 124416 124928, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (314 : ℕ) ∧
    (∑ n ∈ Ico 124416 124928, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-596 : ℤ) ∧
    (∑ n ∈ Ico 124416 124928, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-11817809139576417139485932 : ℤ) := by
  rcases cdemPrefixStats_124416_124672 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_124672_124928 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 124416 ≤ 124672) (by norm_num : 124672 ≤ 124928), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 124416 ≤ 124672) (by norm_num : 124672 ≤ 124928), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 124416 ≤ 124672) (by norm_num : 124672 ≤ 124928), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 124416 ≤ 124672) (by norm_num : 124672 ≤ 124928), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_123904_124928 :
    (∑ n ∈ Ico 123904 124928, mobiusTreeValue 16 mobiusTable1200001 n) = (-6 : ℤ) ∧
    (∑ n ∈ Ico 123904 124928, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (628 : ℕ) ∧
    (∑ n ∈ Ico 123904 124928, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-241511 : ℤ) ∧
    (∑ n ∈ Ico 123904 124928, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-4830245154848132410044254115 : ℤ) := by
  rcases cdemPrefixStats_123904_124416 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_124416_124928 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 123904 ≤ 124416) (by norm_num : 124416 ≤ 124928), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 123904 ≤ 124416) (by norm_num : 124416 ≤ 124928), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 123904 ≤ 124416) (by norm_num : 124416 ≤ 124928), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 123904 ≤ 124416) (by norm_num : 124416 ≤ 124928), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_122880_124928 :
    (∑ n ∈ Ico 122880 124928, mobiusTreeValue 16 mobiusTable1200001 n) = (-16 : ℤ) ∧
    (∑ n ∈ Ico 122880 124928, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (1256 : ℕ) ∧
    (∑ n ∈ Ico 122880 124928, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-646167 : ℤ) ∧
    (∑ n ∈ Ico 122880 124928, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-12923450672818603580486770016 : ℤ) := by
  rcases cdemPrefixStats_122880_123904 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_123904_124928 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 122880 ≤ 123904) (by norm_num : 123904 ≤ 124928), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 122880 ≤ 123904) (by norm_num : 123904 ≤ 124928), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 122880 ≤ 123904) (by norm_num : 123904 ≤ 124928), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 122880 ≤ 123904) (by norm_num : 123904 ≤ 124928), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_124928_124992 :
    (∑ n ∈ Ico 124928 124992, mobiusTreeValue 16 mobiusTable1200001 n) = (5 : ℤ) ∧
    (∑ n ∈ Ico 124928 124992, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 124928 124992, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (200109 : ℤ) ∧
    (∑ n ∈ Ico 124928 124992, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (4002209041758297669777813835 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_124992_125056 :
    (∑ n ∈ Ico 124992 125056, mobiusTreeValue 16 mobiusTable1200001 n) = (-6 : ℤ) ∧
    (∑ n ∈ Ico 124992 125056, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 124992 125056, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-239901 : ℤ) ∧
    (∑ n ∈ Ico 124992 125056, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-4798010108513449238575587214 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_124928_125056 :
    (∑ n ∈ Ico 124928 125056, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 124928 125056, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 124928 125056, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-39792 : ℤ) ∧
    (∑ n ∈ Ico 124928 125056, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-795801066755151568797773379 : ℤ) := by
  rcases cdemPrefixStats_124928_124992 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_124992_125056 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 124928 ≤ 124992) (by norm_num : 124992 ≤ 125056), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 124928 ≤ 124992) (by norm_num : 124992 ≤ 125056), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 124928 ≤ 124992) (by norm_num : 124992 ≤ 125056), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 124928 ≤ 124992) (by norm_num : 124992 ≤ 125056), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_125056_125120 :
    (∑ n ∈ Ico 125056 125120, mobiusTreeValue 16 mobiusTable1200001 n) = (-4 : ℤ) ∧
    (∑ n ∈ Ico 125056 125120, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 125056 125120, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-159828 : ℤ) ∧
    (∑ n ∈ Ico 125056 125120, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-3196681544943178318765561851 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_125120_125184 :
    (∑ n ∈ Ico 125120 125184, mobiusTreeValue 16 mobiusTable1200001 n) = (-2 : ℤ) ∧
    (∑ n ∈ Ico 125120 125184, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 125120 125184, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-79938 : ℤ) ∧
    (∑ n ∈ Ico 125120 125184, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-1598790995741913217462415212 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_125056_125184 :
    (∑ n ∈ Ico 125056 125184, mobiusTreeValue 16 mobiusTable1200001 n) = (-6 : ℤ) ∧
    (∑ n ∈ Ico 125056 125184, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 125056 125184, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-239766 : ℤ) ∧
    (∑ n ∈ Ico 125056 125184, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-4795472540685091536227977063 : ℤ) := by
  rcases cdemPrefixStats_125056_125120 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_125120_125184 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 125056 ≤ 125120) (by norm_num : 125120 ≤ 125184), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 125056 ≤ 125120) (by norm_num : 125120 ≤ 125184), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 125056 ≤ 125120) (by norm_num : 125120 ≤ 125184), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 125056 ≤ 125120) (by norm_num : 125120 ≤ 125184), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_124928_125184 :
    (∑ n ∈ Ico 124928 125184, mobiusTreeValue 16 mobiusTable1200001 n) = (-7 : ℤ) ∧
    (∑ n ∈ Ico 124928 125184, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (155 : ℕ) ∧
    (∑ n ∈ Ico 124928 125184, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-279558 : ℤ) ∧
    (∑ n ∈ Ico 124928 125184, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-5591273607440243105025750442 : ℤ) := by
  rcases cdemPrefixStats_124928_125056 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_125056_125184 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 124928 ≤ 125056) (by norm_num : 125056 ≤ 125184), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 124928 ≤ 125056) (by norm_num : 125056 ≤ 125184), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 124928 ≤ 125056) (by norm_num : 125056 ≤ 125184), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 124928 ≤ 125056) (by norm_num : 125056 ≤ 125184), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_125184_125248 :
    (∑ n ∈ Ico 125184 125248, mobiusTreeValue 16 mobiusTable1200001 n) = (-4 : ℤ) ∧
    (∑ n ∈ Ico 125184 125248, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 125184 125248, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-159677 : ℤ) ∧
    (∑ n ∈ Ico 125184 125248, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-3193574493577794505863943707 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_125248_125312 :
    (∑ n ∈ Ico 125248 125312, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 125248 125312, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 125248 125312, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-39882 : ℤ) ∧
    (∑ n ∈ Ico 125248 125312, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-797740496519868901055341470 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_125184_125312 :
    (∑ n ∈ Ico 125184 125312, mobiusTreeValue 16 mobiusTable1200001 n) = (-5 : ℤ) ∧
    (∑ n ∈ Ico 125184 125312, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 125184 125312, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-199559 : ℤ) ∧
    (∑ n ∈ Ico 125184 125312, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-3991314990097663406919285177 : ℤ) := by
  rcases cdemPrefixStats_125184_125248 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_125248_125312 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 125184 ≤ 125248) (by norm_num : 125248 ≤ 125312), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 125184 ≤ 125248) (by norm_num : 125248 ≤ 125312), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 125184 ≤ 125248) (by norm_num : 125248 ≤ 125312), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 125184 ≤ 125248) (by norm_num : 125248 ≤ 125312), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_125312_125376 :
    (∑ n ∈ Ico 125312 125376, mobiusTreeValue 16 mobiusTable1200001 n) = (7 : ℤ) ∧
    (∑ n ∈ Ico 125312 125376, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 125312 125376, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (279177 : ℤ) ∧
    (∑ n ∈ Ico 125312 125376, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (5583644693940276654666488282 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_125376_125440 :
    (∑ n ∈ Ico 125376 125440, mobiusTreeValue 16 mobiusTable1200001 n) = (-5 : ℤ) ∧
    (∑ n ∈ Ico 125376 125440, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 125376 125440, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-199338 : ℤ) ∧
    (∑ n ∈ Ico 125376 125440, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-3986859245993443815800655555 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_125312_125440 :
    (∑ n ∈ Ico 125312 125440, mobiusTreeValue 16 mobiusTable1200001 n) = (2 : ℤ) ∧
    (∑ n ∈ Ico 125312 125440, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 125312 125440, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (79839 : ℤ) ∧
    (∑ n ∈ Ico 125312 125440, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1596785447946832838865832727 : ℤ) := by
  rcases cdemPrefixStats_125312_125376 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_125376_125440 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 125312 ≤ 125376) (by norm_num : 125376 ≤ 125440), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 125312 ≤ 125376) (by norm_num : 125376 ≤ 125440), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 125312 ≤ 125376) (by norm_num : 125376 ≤ 125440), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 125312 ≤ 125376) (by norm_num : 125376 ≤ 125440), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_125184_125440 :
    (∑ n ∈ Ico 125184 125440, mobiusTreeValue 16 mobiusTable1200001 n) = (-3 : ℤ) ∧
    (∑ n ∈ Ico 125184 125440, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (155 : ℕ) ∧
    (∑ n ∈ Ico 125184 125440, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-119720 : ℤ) ∧
    (∑ n ∈ Ico 125184 125440, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-2394529542150830568053452450 : ℤ) := by
  rcases cdemPrefixStats_125184_125312 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_125312_125440 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 125184 ≤ 125312) (by norm_num : 125312 ≤ 125440), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 125184 ≤ 125312) (by norm_num : 125312 ≤ 125440), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 125184 ≤ 125312) (by norm_num : 125312 ≤ 125440), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 125184 ≤ 125312) (by norm_num : 125312 ≤ 125440), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_124928_125440 :
    (∑ n ∈ Ico 124928 125440, mobiusTreeValue 16 mobiusTable1200001 n) = (-10 : ℤ) ∧
    (∑ n ∈ Ico 124928 125440, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (310 : ℕ) ∧
    (∑ n ∈ Ico 124928 125440, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-399278 : ℤ) ∧
    (∑ n ∈ Ico 124928 125440, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-7985803149591073673079202892 : ℤ) := by
  rcases cdemPrefixStats_124928_125184 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_125184_125440 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 124928 ≤ 125184) (by norm_num : 125184 ≤ 125440), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 124928 ≤ 125184) (by norm_num : 125184 ≤ 125440), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 124928 ≤ 125184) (by norm_num : 125184 ≤ 125440), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 124928 ≤ 125184) (by norm_num : 125184 ≤ 125440), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_125440_125504 :
    (∑ n ∈ Ico 125440 125504, mobiusTreeValue 16 mobiusTable1200001 n) = (-3 : ℤ) ∧
    (∑ n ∈ Ico 125440 125504, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 125440 125504, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-119547 : ℤ) ∧
    (∑ n ∈ Ico 125440 125504, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-2391048001464274253347676543 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_125504_125568 :
    (∑ n ∈ Ico 125504 125568, mobiusTreeValue 16 mobiusTable1200001 n) = (3 : ℤ) ∧
    (∑ n ∈ Ico 125504 125568, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 125504 125568, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (119455 : ℤ) ∧
    (∑ n ∈ Ico 125504 125568, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (2389105608883786020375559867 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_125440_125568 :
    (∑ n ∈ Ico 125440 125568, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 125440 125568, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 125440 125568, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-92 : ℤ) ∧
    (∑ n ∈ Ico 125440 125568, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-1942392580488232972116676 : ℤ) := by
  rcases cdemPrefixStats_125440_125504 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_125504_125568 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 125440 ≤ 125504) (by norm_num : 125504 ≤ 125568), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 125440 ≤ 125504) (by norm_num : 125504 ≤ 125568), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 125440 ≤ 125504) (by norm_num : 125504 ≤ 125568), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 125440 ≤ 125504) (by norm_num : 125504 ≤ 125568), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_125568_125632 :
    (∑ n ∈ Ico 125568 125632, mobiusTreeValue 16 mobiusTable1200001 n) = (-8 : ℤ) ∧
    (∑ n ∈ Ico 125568 125632, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 125568 125632, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-318417 : ℤ) ∧
    (∑ n ∈ Ico 125568 125632, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-6368444278146203211734958201 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_125632_125696 :
    (∑ n ∈ Ico 125632 125696, mobiusTreeValue 16 mobiusTable1200001 n) = (-9 : ℤ) ∧
    (∑ n ∈ Ico 125632 125696, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 125632 125696, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-358059 : ℤ) ∧
    (∑ n ∈ Ico 125632 125696, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-7161271868956761326555027245 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_125568_125696 :
    (∑ n ∈ Ico 125568 125696, mobiusTreeValue 16 mobiusTable1200001 n) = (-17 : ℤ) ∧
    (∑ n ∈ Ico 125568 125696, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (79 : ℕ) ∧
    (∑ n ∈ Ico 125568 125696, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-676476 : ℤ) ∧
    (∑ n ∈ Ico 125568 125696, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-13529716147102964538289985446 : ℤ) := by
  rcases cdemPrefixStats_125568_125632 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_125632_125696 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 125568 ≤ 125632) (by norm_num : 125632 ≤ 125696), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 125568 ≤ 125632) (by norm_num : 125632 ≤ 125696), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 125568 ≤ 125632) (by norm_num : 125632 ≤ 125696), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 125568 ≤ 125632) (by norm_num : 125632 ≤ 125696), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_125440_125696 :
    (∑ n ∈ Ico 125440 125696, mobiusTreeValue 16 mobiusTable1200001 n) = (-17 : ℤ) ∧
    (∑ n ∈ Ico 125440 125696, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (157 : ℕ) ∧
    (∑ n ∈ Ico 125440 125696, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-676568 : ℤ) ∧
    (∑ n ∈ Ico 125440 125696, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-13531658539683452771262102122 : ℤ) := by
  rcases cdemPrefixStats_125440_125568 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_125568_125696 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 125440 ≤ 125568) (by norm_num : 125568 ≤ 125696), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 125440 ≤ 125568) (by norm_num : 125568 ≤ 125696), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 125440 ≤ 125568) (by norm_num : 125568 ≤ 125696), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 125440 ≤ 125568) (by norm_num : 125568 ≤ 125696), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_125696_125760 :
    (∑ n ∈ Ico 125696 125760, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 125696 125760, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 125696 125760, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (28 : ℤ) ∧
    (∑ n ∈ Ico 125696 125760, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (499737859145507676620237 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_125760_125824 :
    (∑ n ∈ Ico 125760 125824, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 125760 125824, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (42 : ℕ) ∧
    (∑ n ∈ Ico 125760 125824, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (36 : ℤ) ∧
    (∑ n ∈ Ico 125760 125824, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (720652898897184128913677 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_125696_125824 :
    (∑ n ∈ Ico 125696 125824, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 125696 125824, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (80 : ℕ) ∧
    (∑ n ∈ Ico 125696 125824, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (64 : ℤ) ∧
    (∑ n ∈ Ico 125696 125824, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1220390758042691805533914 : ℤ) := by
  rcases cdemPrefixStats_125696_125760 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_125760_125824 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 125696 ≤ 125760) (by norm_num : 125760 ≤ 125824), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 125696 ≤ 125760) (by norm_num : 125760 ≤ 125824), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 125696 ≤ 125760) (by norm_num : 125760 ≤ 125824), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 125696 ≤ 125760) (by norm_num : 125760 ≤ 125824), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_125824_125888 :
    (∑ n ∈ Ico 125824 125888, mobiusTreeValue 16 mobiusTable1200001 n) = (16 : ℤ) ∧
    (∑ n ∈ Ico 125824 125888, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 125824 125888, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (635677 : ℤ) ∧
    (∑ n ∈ Ico 125824 125888, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (12713655181437148142721729777 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_125888_125952 :
    (∑ n ∈ Ico 125888 125952, mobiusTreeValue 16 mobiusTable1200001 n) = (-3 : ℤ) ∧
    (∑ n ∈ Ico 125888 125952, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (35 : ℕ) ∧
    (∑ n ∈ Ico 125888 125952, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-119151 : ℤ) ∧
    (∑ n ∈ Ico 125888 125952, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-2383070661981219930083755895 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_125824_125952 :
    (∑ n ∈ Ico 125824 125952, mobiusTreeValue 16 mobiusTable1200001 n) = (13 : ℤ) ∧
    (∑ n ∈ Ico 125824 125952, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (73 : ℕ) ∧
    (∑ n ∈ Ico 125824 125952, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (516526 : ℤ) ∧
    (∑ n ∈ Ico 125824 125952, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (10330584519455928212637973882 : ℤ) := by
  rcases cdemPrefixStats_125824_125888 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_125888_125952 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 125824 ≤ 125888) (by norm_num : 125888 ≤ 125952), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 125824 ≤ 125888) (by norm_num : 125888 ≤ 125952), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 125824 ≤ 125888) (by norm_num : 125888 ≤ 125952), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 125824 ≤ 125888) (by norm_num : 125888 ≤ 125952), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_125696_125952 :
    (∑ n ∈ Ico 125696 125952, mobiusTreeValue 16 mobiusTable1200001 n) = (13 : ℤ) ∧
    (∑ n ∈ Ico 125696 125952, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (153 : ℕ) ∧
    (∑ n ∈ Ico 125696 125952, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (516590 : ℤ) ∧
    (∑ n ∈ Ico 125696 125952, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (10331804910213970904443507796 : ℤ) := by
  rcases cdemPrefixStats_125696_125824 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_125824_125952 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 125696 ≤ 125824) (by norm_num : 125824 ≤ 125952), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 125696 ≤ 125824) (by norm_num : 125824 ≤ 125952), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 125696 ≤ 125824) (by norm_num : 125824 ≤ 125952), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 125696 ≤ 125824) (by norm_num : 125824 ≤ 125952), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_125440_125952 :
    (∑ n ∈ Ico 125440 125952, mobiusTreeValue 16 mobiusTable1200001 n) = (-4 : ℤ) ∧
    (∑ n ∈ Ico 125440 125952, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (310 : ℕ) ∧
    (∑ n ∈ Ico 125440 125952, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-159978 : ℤ) ∧
    (∑ n ∈ Ico 125440 125952, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-3199853629469481866818594326 : ℤ) := by
  rcases cdemPrefixStats_125440_125696 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_125696_125952 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 125440 ≤ 125696) (by norm_num : 125696 ≤ 125952), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 125440 ≤ 125696) (by norm_num : 125696 ≤ 125952), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 125440 ≤ 125696) (by norm_num : 125696 ≤ 125952), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 125440 ≤ 125696) (by norm_num : 125696 ≤ 125952), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_124928_125952 :
    (∑ n ∈ Ico 124928 125952, mobiusTreeValue 16 mobiusTable1200001 n) = (-14 : ℤ) ∧
    (∑ n ∈ Ico 124928 125952, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (620 : ℕ) ∧
    (∑ n ∈ Ico 124928 125952, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-559256 : ℤ) ∧
    (∑ n ∈ Ico 124928 125952, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-11185656779060555539897797218 : ℤ) := by
  rcases cdemPrefixStats_124928_125440 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_125440_125952 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 124928 ≤ 125440) (by norm_num : 125440 ≤ 125952), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 124928 ≤ 125440) (by norm_num : 125440 ≤ 125952), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 124928 ≤ 125440) (by norm_num : 125440 ≤ 125952), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 124928 ≤ 125440) (by norm_num : 125440 ≤ 125952), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_125952_126016 :
    (∑ n ∈ Ico 125952 126016, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 125952 126016, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 125952 126016, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (61 : ℤ) ∧
    (∑ n ∈ Ico 125952 126016, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1285118423535335475129542 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_126016_126080 :
    (∑ n ∈ Ico 126016 126080, mobiusTreeValue 16 mobiusTable1200001 n) = (6 : ℤ) ∧
    (∑ n ∈ Ico 126016 126080, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 126016 126080, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (238023 : ℤ) ∧
    (∑ n ∈ Ico 126016 126080, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (4760506792276017706542128042 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_125952_126080 :
    (∑ n ∈ Ico 125952 126080, mobiusTreeValue 16 mobiusTable1200001 n) = (6 : ℤ) ∧
    (∑ n ∈ Ico 125952 126080, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (76 : ℕ) ∧
    (∑ n ∈ Ico 125952 126080, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (238084 : ℤ) ∧
    (∑ n ∈ Ico 125952 126080, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (4761791910699553042017257584 : ℤ) := by
  rcases cdemPrefixStats_125952_126016 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_126016_126080 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 125952 ≤ 126016) (by norm_num : 126016 ≤ 126080), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 125952 ≤ 126016) (by norm_num : 126016 ≤ 126080), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 125952 ≤ 126016) (by norm_num : 126016 ≤ 126080), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 125952 ≤ 126016) (by norm_num : 126016 ≤ 126080), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_126080_126144 :
    (∑ n ∈ Ico 126080 126144, mobiusTreeValue 16 mobiusTable1200001 n) = (-12 : ℤ) ∧
    (∑ n ∈ Ico 126080 126144, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 126080 126144, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-475706 : ℤ) ∧
    (∑ n ∈ Ico 126080 126144, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-9514263868506815592880107894 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_126144_126208 :
    (∑ n ∈ Ico 126144 126208, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 126144 126208, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 126144 126208, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (39605 : ℤ) ∧
    (∑ n ∈ Ico 126144 126208, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (792192024666206235650058537 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_126080_126208 :
    (∑ n ∈ Ico 126080 126208, mobiusTreeValue 16 mobiusTable1200001 n) = (-11 : ℤ) ∧
    (∑ n ∈ Ico 126080 126208, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (79 : ℕ) ∧
    (∑ n ∈ Ico 126080 126208, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-436101 : ℤ) ∧
    (∑ n ∈ Ico 126080 126208, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-8722071843840609357230049357 : ℤ) := by
  rcases cdemPrefixStats_126080_126144 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_126144_126208 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 126080 ≤ 126144) (by norm_num : 126144 ≤ 126208), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 126080 ≤ 126144) (by norm_num : 126144 ≤ 126208), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 126080 ≤ 126144) (by norm_num : 126144 ≤ 126208), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 126080 ≤ 126144) (by norm_num : 126144 ≤ 126208), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_125952_126208 :
    (∑ n ∈ Ico 125952 126208, mobiusTreeValue 16 mobiusTable1200001 n) = (-5 : ℤ) ∧
    (∑ n ∈ Ico 125952 126208, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (155 : ℕ) ∧
    (∑ n ∈ Ico 125952 126208, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-198017 : ℤ) ∧
    (∑ n ∈ Ico 125952 126208, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-3960279933141056315212791773 : ℤ) := by
  rcases cdemPrefixStats_125952_126080 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_126080_126208 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 125952 ≤ 126080) (by norm_num : 126080 ≤ 126208), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 125952 ≤ 126080) (by norm_num : 126080 ≤ 126208), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 125952 ≤ 126080) (by norm_num : 126080 ≤ 126208), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 125952 ≤ 126080) (by norm_num : 126080 ≤ 126208), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_126208_126272 :
    (∑ n ∈ Ico 126208 126272, mobiusTreeValue 16 mobiusTable1200001 n) = (8 : ℤ) ∧
    (∑ n ∈ Ico 126208 126272, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (42 : ℕ) ∧
    (∑ n ∈ Ico 126208 126272, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (316828 : ℤ) ∧
    (∑ n ∈ Ico 126208 126272, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (6336677664580519398339436064 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_126272_126336 :
    (∑ n ∈ Ico 126272 126336, mobiusTreeValue 16 mobiusTable1200001 n) = (6 : ℤ) ∧
    (∑ n ∈ Ico 126272 126336, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 126272 126336, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (237546 : ℤ) ∧
    (∑ n ∈ Ico 126272 126336, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (4750995028395568286472649621 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_126208_126336 :
    (∑ n ∈ Ico 126208 126336, mobiusTreeValue 16 mobiusTable1200001 n) = (14 : ℤ) ∧
    (∑ n ∈ Ico 126208 126336, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (80 : ℕ) ∧
    (∑ n ∈ Ico 126208 126336, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (554374 : ℤ) ∧
    (∑ n ∈ Ico 126208 126336, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (11087672692976087684812085685 : ℤ) := by
  rcases cdemPrefixStats_126208_126272 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_126272_126336 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 126208 ≤ 126272) (by norm_num : 126272 ≤ 126336), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 126208 ≤ 126272) (by norm_num : 126272 ≤ 126336), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 126208 ≤ 126272) (by norm_num : 126272 ≤ 126336), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 126208 ≤ 126272) (by norm_num : 126272 ≤ 126336), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_126336_126400 :
    (∑ n ∈ Ico 126336 126400, mobiusTreeValue 16 mobiusTable1200001 n) = (-2 : ℤ) ∧
    (∑ n ∈ Ico 126336 126400, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 126336 126400, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-79199 : ℤ) ∧
    (∑ n ∈ Ico 126336 126400, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-1584013083725446339680953100 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_126400_126464 :
    (∑ n ∈ Ico 126400 126464, mobiusTreeValue 16 mobiusTable1200001 n) = (-3 : ℤ) ∧
    (∑ n ∈ Ico 126400 126464, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 126400 126464, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-118571 : ℤ) ∧
    (∑ n ∈ Ico 126400 126464, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-2371422127490376500041092912 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_126336_126464 :
    (∑ n ∈ Ico 126336 126464, mobiusTreeValue 16 mobiusTable1200001 n) = (-5 : ℤ) ∧
    (∑ n ∈ Ico 126336 126464, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (79 : ℕ) ∧
    (∑ n ∈ Ico 126336 126464, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-197770 : ℤ) ∧
    (∑ n ∈ Ico 126336 126464, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-3955435211215822839722046012 : ℤ) := by
  rcases cdemPrefixStats_126336_126400 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_126400_126464 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 126336 ≤ 126400) (by norm_num : 126400 ≤ 126464), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 126336 ≤ 126400) (by norm_num : 126400 ≤ 126464), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 126336 ≤ 126400) (by norm_num : 126400 ≤ 126464), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 126336 ≤ 126400) (by norm_num : 126400 ≤ 126464), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_126208_126464 :
    (∑ n ∈ Ico 126208 126464, mobiusTreeValue 16 mobiusTable1200001 n) = (9 : ℤ) ∧
    (∑ n ∈ Ico 126208 126464, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (159 : ℕ) ∧
    (∑ n ∈ Ico 126208 126464, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (356604 : ℤ) ∧
    (∑ n ∈ Ico 126208 126464, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (7132237481760264845090039673 : ℤ) := by
  rcases cdemPrefixStats_126208_126336 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_126336_126464 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 126208 ≤ 126336) (by norm_num : 126336 ≤ 126464), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 126208 ≤ 126336) (by norm_num : 126336 ≤ 126464), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 126208 ≤ 126336) (by norm_num : 126336 ≤ 126464), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 126208 ≤ 126336) (by norm_num : 126336 ≤ 126464), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_125952_126464 :
    (∑ n ∈ Ico 125952 126464, mobiusTreeValue 16 mobiusTable1200001 n) = (4 : ℤ) ∧
    (∑ n ∈ Ico 125952 126464, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (314 : ℕ) ∧
    (∑ n ∈ Ico 125952 126464, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (158587 : ℤ) ∧
    (∑ n ∈ Ico 125952 126464, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (3171957548619208529877247900 : ℤ) := by
  rcases cdemPrefixStats_125952_126208 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_126208_126464 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 125952 ≤ 126208) (by norm_num : 126208 ≤ 126464), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 125952 ≤ 126208) (by norm_num : 126208 ≤ 126464), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 125952 ≤ 126208) (by norm_num : 126208 ≤ 126464), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 125952 ≤ 126208) (by norm_num : 126208 ≤ 126464), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_126464_126528 :
    (∑ n ∈ Ico 126464 126528, mobiusTreeValue 16 mobiusTable1200001 n) = (-4 : ℤ) ∧
    (∑ n ∈ Ico 126464 126528, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 126464 126528, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-158142 : ℤ) ∧
    (∑ n ∈ Ico 126464 126528, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-3162917763434484876202176013 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_126528_126592 :
    (∑ n ∈ Ico 126528 126592, mobiusTreeValue 16 mobiusTable1200001 n) = (4 : ℤ) ∧
    (∑ n ∈ Ico 126528 126592, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 126528 126592, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (158041 : ℤ) ∧
    (∑ n ∈ Ico 126528 126592, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (3160843510500857468834744725 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_126464_126592 :
    (∑ n ∈ Ico 126464 126592, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 126464 126592, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (76 : ℕ) ∧
    (∑ n ∈ Ico 126464 126592, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-101 : ℤ) ∧
    (∑ n ∈ Ico 126464 126592, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-2074252933627407367431288 : ℤ) := by
  rcases cdemPrefixStats_126464_126528 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_126528_126592 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 126464 ≤ 126528) (by norm_num : 126528 ≤ 126592), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 126464 ≤ 126528) (by norm_num : 126528 ≤ 126592), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 126464 ≤ 126528) (by norm_num : 126528 ≤ 126592), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 126464 ≤ 126528) (by norm_num : 126528 ≤ 126592), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_126592_126656 :
    (∑ n ∈ Ico 126592 126656, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 126592 126656, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 126592 126656, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (39509 : ℤ) ∧
    (∑ n ∈ Ico 126592 126656, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (790176083992330584961765652 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_126656_126720 :
    (∑ n ∈ Ico 126656 126720, mobiusTreeValue 16 mobiusTable1200001 n) = (5 : ℤ) ∧
    (∑ n ∈ Ico 126656 126720, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 126656 126720, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (197430 : ℤ) ∧
    (∑ n ∈ Ico 126656 126720, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (3948635378678356857260687357 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_126592_126720 :
    (∑ n ∈ Ico 126592 126720, mobiusTreeValue 16 mobiusTable1200001 n) = (6 : ℤ) ∧
    (∑ n ∈ Ico 126592 126720, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (80 : ℕ) ∧
    (∑ n ∈ Ico 126592 126720, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (236939 : ℤ) ∧
    (∑ n ∈ Ico 126592 126720, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (4738811462670687442222453009 : ℤ) := by
  rcases cdemPrefixStats_126592_126656 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_126656_126720 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 126592 ≤ 126656) (by norm_num : 126656 ≤ 126720), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 126592 ≤ 126656) (by norm_num : 126656 ≤ 126720), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 126592 ≤ 126656) (by norm_num : 126656 ≤ 126720), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 126592 ≤ 126656) (by norm_num : 126656 ≤ 126720), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_126464_126720 :
    (∑ n ∈ Ico 126464 126720, mobiusTreeValue 16 mobiusTable1200001 n) = (6 : ℤ) ∧
    (∑ n ∈ Ico 126464 126720, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (156 : ℕ) ∧
    (∑ n ∈ Ico 126464 126720, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (236838 : ℤ) ∧
    (∑ n ∈ Ico 126464 126720, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (4736737209737060034855021721 : ℤ) := by
  rcases cdemPrefixStats_126464_126592 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_126592_126720 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 126464 ≤ 126592) (by norm_num : 126592 ≤ 126720), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 126464 ≤ 126592) (by norm_num : 126592 ≤ 126720), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 126464 ≤ 126592) (by norm_num : 126592 ≤ 126720), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 126464 ≤ 126592) (by norm_num : 126592 ≤ 126720), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_126720_126784 :
    (∑ n ∈ Ico 126720 126784, mobiusTreeValue 16 mobiusTable1200001 n) = (-2 : ℤ) ∧
    (∑ n ∈ Ico 126720 126784, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 126720 126784, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-78960 : ℤ) ∧
    (∑ n ∈ Ico 126720 126784, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-1579160351794763625349868150 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_126784_126848 :
    (∑ n ∈ Ico 126784 126848, mobiusTreeValue 16 mobiusTable1200001 n) = (6 : ℤ) ∧
    (∑ n ∈ Ico 126784 126848, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (42 : ℕ) ∧
    (∑ n ∈ Ico 126784 126848, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (236573 : ℤ) ∧
    (∑ n ∈ Ico 126784 126848, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (4731513067552959128689617120 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_126720_126848 :
    (∑ n ∈ Ico 126720 126848, mobiusTreeValue 16 mobiusTable1200001 n) = (4 : ℤ) ∧
    (∑ n ∈ Ico 126720 126848, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (80 : ℕ) ∧
    (∑ n ∈ Ico 126720 126848, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (157613 : ℤ) ∧
    (∑ n ∈ Ico 126720 126848, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (3152352715758195503339748970 : ℤ) := by
  rcases cdemPrefixStats_126720_126784 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_126784_126848 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 126720 ≤ 126784) (by norm_num : 126784 ≤ 126848), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 126720 ≤ 126784) (by norm_num : 126784 ≤ 126848), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 126720 ≤ 126784) (by norm_num : 126784 ≤ 126848), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 126720 ≤ 126784) (by norm_num : 126784 ≤ 126848), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_126848_126912 :
    (∑ n ∈ Ico 126848 126912, mobiusTreeValue 16 mobiusTable1200001 n) = (2 : ℤ) ∧
    (∑ n ∈ Ico 126848 126912, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 126848 126912, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (78797 : ℤ) ∧
    (∑ n ∈ Ico 126848 126912, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1575950805438800788019817221 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_126912_126976 :
    (∑ n ∈ Ico 126912 126976, mobiusTreeValue 16 mobiusTable1200001 n) = (3 : ℤ) ∧
    (∑ n ∈ Ico 126912 126976, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 126912 126976, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (118143 : ℤ) ∧
    (∑ n ∈ Ico 126912 126976, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (2362911796304977424527027584 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_126848_126976 :
    (∑ n ∈ Ico 126848 126976, mobiusTreeValue 16 mobiusTable1200001 n) = (5 : ℤ) ∧
    (∑ n ∈ Ico 126848 126976, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (75 : ℕ) ∧
    (∑ n ∈ Ico 126848 126976, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (196940 : ℤ) ∧
    (∑ n ∈ Ico 126848 126976, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (3938862601743778212546844805 : ℤ) := by
  rcases cdemPrefixStats_126848_126912 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_126912_126976 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 126848 ≤ 126912) (by norm_num : 126912 ≤ 126976), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 126848 ≤ 126912) (by norm_num : 126912 ≤ 126976), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 126848 ≤ 126912) (by norm_num : 126912 ≤ 126976), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 126848 ≤ 126912) (by norm_num : 126912 ≤ 126976), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_126720_126976 :
    (∑ n ∈ Ico 126720 126976, mobiusTreeValue 16 mobiusTable1200001 n) = (9 : ℤ) ∧
    (∑ n ∈ Ico 126720 126976, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (155 : ℕ) ∧
    (∑ n ∈ Ico 126720 126976, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (354553 : ℤ) ∧
    (∑ n ∈ Ico 126720 126976, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (7091215317501973715886593775 : ℤ) := by
  rcases cdemPrefixStats_126720_126848 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_126848_126976 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 126720 ≤ 126848) (by norm_num : 126848 ≤ 126976), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 126720 ≤ 126848) (by norm_num : 126848 ≤ 126976), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 126720 ≤ 126848) (by norm_num : 126848 ≤ 126976), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 126720 ≤ 126848) (by norm_num : 126848 ≤ 126976), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_126464_126976 :
    (∑ n ∈ Ico 126464 126976, mobiusTreeValue 16 mobiusTable1200001 n) = (15 : ℤ) ∧
    (∑ n ∈ Ico 126464 126976, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (311 : ℕ) ∧
    (∑ n ∈ Ico 126464 126976, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (591391 : ℤ) ∧
    (∑ n ∈ Ico 126464 126976, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (11827952527239033750741615496 : ℤ) := by
  rcases cdemPrefixStats_126464_126720 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_126720_126976 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 126464 ≤ 126720) (by norm_num : 126720 ≤ 126976), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 126464 ≤ 126720) (by norm_num : 126720 ≤ 126976), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 126464 ≤ 126720) (by norm_num : 126720 ≤ 126976), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 126464 ≤ 126720) (by norm_num : 126720 ≤ 126976), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_125952_126976 :
    (∑ n ∈ Ico 125952 126976, mobiusTreeValue 16 mobiusTable1200001 n) = (19 : ℤ) ∧
    (∑ n ∈ Ico 125952 126976, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (625 : ℕ) ∧
    (∑ n ∈ Ico 125952 126976, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (749978 : ℤ) ∧
    (∑ n ∈ Ico 125952 126976, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (14999910075858242280618863396 : ℤ) := by
  rcases cdemPrefixStats_125952_126464 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_126464_126976 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 125952 ≤ 126464) (by norm_num : 126464 ≤ 126976), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 125952 ≤ 126464) (by norm_num : 126464 ≤ 126976), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 125952 ≤ 126464) (by norm_num : 126464 ≤ 126976), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 125952 ≤ 126464) (by norm_num : 126464 ≤ 126976), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_124928_126976 :
    (∑ n ∈ Ico 124928 126976, mobiusTreeValue 16 mobiusTable1200001 n) = (5 : ℤ) ∧
    (∑ n ∈ Ico 124928 126976, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (1245 : ℕ) ∧
    (∑ n ∈ Ico 124928 126976, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (190722 : ℤ) ∧
    (∑ n ∈ Ico 124928 126976, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (3814253296797686740721066178 : ℤ) := by
  rcases cdemPrefixStats_124928_125952 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_125952_126976 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 124928 ≤ 125952) (by norm_num : 125952 ≤ 126976), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 124928 ≤ 125952) (by norm_num : 125952 ≤ 126976), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 124928 ≤ 125952) (by norm_num : 125952 ≤ 126976), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 124928 ≤ 125952) (by norm_num : 125952 ≤ 126976), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_122880_126976 :
    (∑ n ∈ Ico 122880 126976, mobiusTreeValue 16 mobiusTable1200001 n) = (-11 : ℤ) ∧
    (∑ n ∈ Ico 122880 126976, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (2501 : ℕ) ∧
    (∑ n ∈ Ico 122880 126976, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-455445 : ℤ) ∧
    (∑ n ∈ Ico 122880 126976, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-9109197376020916839765703838 : ℤ) := by
  rcases cdemPrefixStats_122880_124928 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_124928_126976 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 122880 ≤ 124928) (by norm_num : 124928 ≤ 126976), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 122880 ≤ 124928) (by norm_num : 124928 ≤ 126976), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 122880 ≤ 124928) (by norm_num : 124928 ≤ 126976), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 122880 ≤ 124928) (by norm_num : 124928 ≤ 126976), hR1, hR2] <;> norm_num

theorem cdemPrefixGroup030_checked_complete :
    (∑ n ∈ Ico 122880 126976, mobiusTreeValue 16 mobiusTable1200001 n) = (-11 : ℤ) ∧
    (∑ n ∈ Ico 122880 126976, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (2501 : ℕ) ∧
    (∑ n ∈ Ico 122880 126976, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-455445 : ℤ) ∧
    (∑ n ∈ Ico 122880 126976, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-9109197376020916839765703838 : ℤ) := cdemPrefixStats_122880_126976
end Helfgott
#print axioms Helfgott.cdemPrefixGroup030_checked_complete

open Helfgott Finset
open scoped BigOperators

theorem solution :
    (∑ n ∈ Ico 122880 126976, mobiusTreeValue 16 mobiusTable1200001 n) = (-11 : ℤ) ∧
    (∑ n ∈ Ico 122880 126976, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (2501 : ℕ) ∧
    (∑ n ∈ Ico 122880 126976, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-455445 : ℤ) ∧
    (∑ n ∈ Ico 122880 126976, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-9109197376020916839765703838 : ℤ) := Helfgott.cdemPrefixGroup030_checked_complete
#print axioms solution
