-- Prove2me | solution 1 for Helfgott.cdemPrefixGroup037_checked
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-09T02:34:21.210561+00:00
-- url     : https://prove2.me/submissions/697a077b-bc43-48e4-a628-d41a750f0f10

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
private theorem cdemPrefixStats_151552_151616 :
    (∑ n ∈ Ico 151552 151616, mobiusTreeValue 16 mobiusTable1200001 n) = (-7 : ℤ) ∧
    (∑ n ∈ Ico 151552 151616, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 151552 151616, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-230888 : ℤ) ∧
    (∑ n ∈ Ico 151552 151616, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-4617853898844293022222350144 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_151616_151680 :
    (∑ n ∈ Ico 151616 151680, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 151616 151680, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 151616 151680, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (32980 : ℤ) ∧
    (∑ n ∈ Ico 151616 151680, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (659608788509885577703181249 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_151552_151680 :
    (∑ n ∈ Ico 151552 151680, mobiusTreeValue 16 mobiusTable1200001 n) = (-6 : ℤ) ∧
    (∑ n ∈ Ico 151552 151680, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (76 : ℕ) ∧
    (∑ n ∈ Ico 151552 151680, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-197908 : ℤ) ∧
    (∑ n ∈ Ico 151552 151680, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-3958245110334407444519168895 : ℤ) := by
  rcases cdemPrefixStats_151552_151616 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_151616_151680 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 151552 ≤ 151616) (by norm_num : 151616 ≤ 151680), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 151552 ≤ 151616) (by norm_num : 151616 ≤ 151680), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 151552 ≤ 151616) (by norm_num : 151616 ≤ 151680), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 151552 ≤ 151616) (by norm_num : 151616 ≤ 151680), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_151680_151744 :
    (∑ n ∈ Ico 151680 151744, mobiusTreeValue 16 mobiusTable1200001 n) = (-13 : ℤ) ∧
    (∑ n ∈ Ico 151680 151744, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 151680 151744, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-428459 : ℤ) ∧
    (∑ n ∈ Ico 151680 151744, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-8569301917115725308680441314 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_151744_151808 :
    (∑ n ∈ Ico 151744 151808, mobiusTreeValue 16 mobiusTable1200001 n) = (5 : ℤ) ∧
    (∑ n ∈ Ico 151744 151808, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 151744 151808, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (164765 : ℤ) ∧
    (∑ n ∈ Ico 151744 151808, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (3295352995885210740417574621 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_151680_151808 :
    (∑ n ∈ Ico 151680 151808, mobiusTreeValue 16 mobiusTable1200001 n) = (-8 : ℤ) ∧
    (∑ n ∈ Ico 151680 151808, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 151680 151808, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-263694 : ℤ) ∧
    (∑ n ∈ Ico 151680 151808, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-5273948921230514568262866693 : ℤ) := by
  rcases cdemPrefixStats_151680_151744 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_151744_151808 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 151680 ≤ 151744) (by norm_num : 151744 ≤ 151808), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 151680 ≤ 151744) (by norm_num : 151744 ≤ 151808), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 151680 ≤ 151744) (by norm_num : 151744 ≤ 151808), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 151680 ≤ 151744) (by norm_num : 151744 ≤ 151808), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_151552_151808 :
    (∑ n ∈ Ico 151552 151808, mobiusTreeValue 16 mobiusTable1200001 n) = (-14 : ℤ) ∧
    (∑ n ∈ Ico 151552 151808, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (154 : ℕ) ∧
    (∑ n ∈ Ico 151552 151808, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-461602 : ℤ) ∧
    (∑ n ∈ Ico 151552 151808, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-9232194031564922012782035588 : ℤ) := by
  rcases cdemPrefixStats_151552_151680 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_151680_151808 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 151552 ≤ 151680) (by norm_num : 151680 ≤ 151808), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 151552 ≤ 151680) (by norm_num : 151680 ≤ 151808), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 151552 ≤ 151680) (by norm_num : 151680 ≤ 151808), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 151552 ≤ 151680) (by norm_num : 151680 ≤ 151808), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_151808_151872 :
    (∑ n ∈ Ico 151808 151872, mobiusTreeValue 16 mobiusTable1200001 n) = (-5 : ℤ) ∧
    (∑ n ∈ Ico 151808 151872, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 151808 151872, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-164660 : ℤ) ∧
    (∑ n ∈ Ico 151808 151872, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-3293239331024981126430698993 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_151872_151936 :
    (∑ n ∈ Ico 151872 151936, mobiusTreeValue 16 mobiusTable1200001 n) = (-5 : ℤ) ∧
    (∑ n ∈ Ico 151872 151936, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 151872 151936, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-164560 : ℤ) ∧
    (∑ n ∈ Ico 151872 151936, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-3291292426997587158335981432 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_151808_151936 :
    (∑ n ∈ Ico 151808 151936, mobiusTreeValue 16 mobiusTable1200001 n) = (-10 : ℤ) ∧
    (∑ n ∈ Ico 151808 151936, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 151808 151936, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-329220 : ℤ) ∧
    (∑ n ∈ Ico 151808 151936, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-6584531758022568284766680425 : ℤ) := by
  rcases cdemPrefixStats_151808_151872 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_151872_151936 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 151808 ≤ 151872) (by norm_num : 151872 ≤ 151936), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 151808 ≤ 151872) (by norm_num : 151872 ≤ 151936), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 151808 ≤ 151872) (by norm_num : 151872 ≤ 151936), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 151808 ≤ 151872) (by norm_num : 151872 ≤ 151936), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_151936_152000 :
    (∑ n ∈ Ico 151936 152000, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 151936 152000, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 151936 152000, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (32882 : ℤ) ∧
    (∑ n ∈ Ico 151936 152000, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (657621934373859438750811786 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_152000_152064 :
    (∑ n ∈ Ico 152000 152064, mobiusTreeValue 16 mobiusTable1200001 n) = (-6 : ℤ) ∧
    (∑ n ∈ Ico 152000 152064, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 152000 152064, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-197301 : ℤ) ∧
    (∑ n ∈ Ico 152000 152064, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-3946027035431741358020174117 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_151936_152064 :
    (∑ n ∈ Ico 151936 152064, mobiusTreeValue 16 mobiusTable1200001 n) = (-5 : ℤ) ∧
    (∑ n ∈ Ico 151936 152064, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (75 : ℕ) ∧
    (∑ n ∈ Ico 151936 152064, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-164419 : ℤ) ∧
    (∑ n ∈ Ico 151936 152064, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-3288405101057881919269362331 : ℤ) := by
  rcases cdemPrefixStats_151936_152000 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_152000_152064 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 151936 ≤ 152000) (by norm_num : 152000 ≤ 152064), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 151936 ≤ 152000) (by norm_num : 152000 ≤ 152064), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 151936 ≤ 152000) (by norm_num : 152000 ≤ 152064), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 151936 ≤ 152000) (by norm_num : 152000 ≤ 152064), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_151808_152064 :
    (∑ n ∈ Ico 151808 152064, mobiusTreeValue 16 mobiusTable1200001 n) = (-15 : ℤ) ∧
    (∑ n ∈ Ico 151808 152064, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (153 : ℕ) ∧
    (∑ n ∈ Ico 151808 152064, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-493639 : ℤ) ∧
    (∑ n ∈ Ico 151808 152064, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-9872936859080450204036042756 : ℤ) := by
  rcases cdemPrefixStats_151808_151936 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_151936_152064 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 151808 ≤ 151936) (by norm_num : 151936 ≤ 152064), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 151808 ≤ 151936) (by norm_num : 151936 ≤ 152064), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 151808 ≤ 151936) (by norm_num : 151936 ≤ 152064), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 151808 ≤ 151936) (by norm_num : 151936 ≤ 152064), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_151552_152064 :
    (∑ n ∈ Ico 151552 152064, mobiusTreeValue 16 mobiusTable1200001 n) = (-29 : ℤ) ∧
    (∑ n ∈ Ico 151552 152064, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (307 : ℕ) ∧
    (∑ n ∈ Ico 151552 152064, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-955241 : ℤ) ∧
    (∑ n ∈ Ico 151552 152064, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-19105130890645372216818078344 : ℤ) := by
  rcases cdemPrefixStats_151552_151808 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_151808_152064 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 151552 ≤ 151808) (by norm_num : 151808 ≤ 152064), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 151552 ≤ 151808) (by norm_num : 151808 ≤ 152064), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 151552 ≤ 151808) (by norm_num : 151808 ≤ 152064), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 151552 ≤ 151808) (by norm_num : 151808 ≤ 152064), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_152064_152128 :
    (∑ n ∈ Ico 152064 152128, mobiusTreeValue 16 mobiusTable1200001 n) = (-13 : ℤ) ∧
    (∑ n ∈ Ico 152064 152128, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 152064 152128, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-427359 : ℤ) ∧
    (∑ n ∈ Ico 152064 152128, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-8547281031629813167974667098 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_152128_152192 :
    (∑ n ∈ Ico 152128 152192, mobiusTreeValue 16 mobiusTable1200001 n) = (7 : ℤ) ∧
    (∑ n ∈ Ico 152128 152192, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 152128 152192, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (230047 : ℤ) ∧
    (∑ n ∈ Ico 152128 152192, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (4601033903080831871259043358 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_152064_152192 :
    (∑ n ∈ Ico 152064 152192, mobiusTreeValue 16 mobiusTable1200001 n) = (-6 : ℤ) ∧
    (∑ n ∈ Ico 152064 152192, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (80 : ℕ) ∧
    (∑ n ∈ Ico 152064 152192, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-197312 : ℤ) ∧
    (∑ n ∈ Ico 152064 152192, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-3946247128548981296715623740 : ℤ) := by
  rcases cdemPrefixStats_152064_152128 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_152128_152192 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 152064 ≤ 152128) (by norm_num : 152128 ≤ 152192), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 152064 ≤ 152128) (by norm_num : 152128 ≤ 152192), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 152064 ≤ 152128) (by norm_num : 152128 ≤ 152192), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 152064 ≤ 152128) (by norm_num : 152128 ≤ 152192), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_152192_152256 :
    (∑ n ∈ Ico 152192 152256, mobiusTreeValue 16 mobiusTable1200001 n) = (-7 : ℤ) ∧
    (∑ n ∈ Ico 152192 152256, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 152192 152256, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-229923 : ℤ) ∧
    (∑ n ∈ Ico 152192 152256, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-4598490903103691500381835354 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_152256_152320 :
    (∑ n ∈ Ico 152256 152320, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 152256 152320, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 152256 152320, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (12 : ℤ) ∧
    (∑ n ∈ Ico 152256 152320, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (241530376187571224819459 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_152192_152320 :
    (∑ n ∈ Ico 152192 152320, mobiusTreeValue 16 mobiusTable1200001 n) = (-7 : ℤ) ∧
    (∑ n ∈ Ico 152192 152320, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 152192 152320, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-229911 : ℤ) ∧
    (∑ n ∈ Ico 152192 152320, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-4598249372727503929157015895 : ℤ) := by
  rcases cdemPrefixStats_152192_152256 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_152256_152320 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 152192 ≤ 152256) (by norm_num : 152256 ≤ 152320), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 152192 ≤ 152256) (by norm_num : 152256 ≤ 152320), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 152192 ≤ 152256) (by norm_num : 152256 ≤ 152320), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 152192 ≤ 152256) (by norm_num : 152256 ≤ 152320), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_152064_152320 :
    (∑ n ∈ Ico 152064 152320, mobiusTreeValue 16 mobiusTable1200001 n) = (-13 : ℤ) ∧
    (∑ n ∈ Ico 152064 152320, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (157 : ℕ) ∧
    (∑ n ∈ Ico 152064 152320, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-427223 : ℤ) ∧
    (∑ n ∈ Ico 152064 152320, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-8544496501276485225872639635 : ℤ) := by
  rcases cdemPrefixStats_152064_152192 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_152192_152320 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 152064 ≤ 152192) (by norm_num : 152192 ≤ 152320), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 152064 ≤ 152192) (by norm_num : 152192 ≤ 152320), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 152064 ≤ 152192) (by norm_num : 152192 ≤ 152320), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 152064 ≤ 152192) (by norm_num : 152192 ≤ 152320), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_152320_152384 :
    (∑ n ∈ Ico 152320 152384, mobiusTreeValue 16 mobiusTable1200001 n) = (5 : ℤ) ∧
    (∑ n ∈ Ico 152320 152384, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 152320 152384, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (164129 : ℤ) ∧
    (∑ n ∈ Ico 152320 152384, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (3282653370059145612749452719 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_152384_152448 :
    (∑ n ∈ Ico 152384 152448, mobiusTreeValue 16 mobiusTable1200001 n) = (-14 : ℤ) ∧
    (∑ n ∈ Ico 152384 152448, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 152384 152448, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-459268 : ℤ) ∧
    (∑ n ∈ Ico 152384 152448, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-9185533903106739623239249026 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_152320_152448 :
    (∑ n ∈ Ico 152320 152448, mobiusTreeValue 16 mobiusTable1200001 n) = (-9 : ℤ) ∧
    (∑ n ∈ Ico 152320 152448, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (75 : ℕ) ∧
    (∑ n ∈ Ico 152320 152448, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-295139 : ℤ) ∧
    (∑ n ∈ Ico 152320 152448, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-5902880533047594010489796307 : ℤ) := by
  rcases cdemPrefixStats_152320_152384 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_152384_152448 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 152320 ≤ 152384) (by norm_num : 152384 ≤ 152448), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 152320 ≤ 152384) (by norm_num : 152384 ≤ 152448), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 152320 ≤ 152384) (by norm_num : 152384 ≤ 152448), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 152320 ≤ 152384) (by norm_num : 152384 ≤ 152448), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_152448_152512 :
    (∑ n ∈ Ico 152448 152512, mobiusTreeValue 16 mobiusTable1200001 n) = (9 : ℤ) ∧
    (∑ n ∈ Ico 152448 152512, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 152448 152512, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (295069 : ℤ) ∧
    (∑ n ∈ Ico 152448 152512, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (5901454364831069775437841957 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_152512_152576 :
    (∑ n ∈ Ico 152512 152576, mobiusTreeValue 16 mobiusTable1200001 n) = (5 : ℤ) ∧
    (∑ n ∈ Ico 152512 152576, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 152512 152576, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (163872 : ℤ) ∧
    (∑ n ∈ Ico 152512 152576, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (3277463612435999797710400806 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_152448_152576 :
    (∑ n ∈ Ico 152448 152576, mobiusTreeValue 16 mobiusTable1200001 n) = (14 : ℤ) ∧
    (∑ n ∈ Ico 152448 152576, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (80 : ℕ) ∧
    (∑ n ∈ Ico 152448 152576, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (458941 : ℤ) ∧
    (∑ n ∈ Ico 152448 152576, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (9178917977267069573148242763 : ℤ) := by
  rcases cdemPrefixStats_152448_152512 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_152512_152576 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 152448 ≤ 152512) (by norm_num : 152512 ≤ 152576), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 152448 ≤ 152512) (by norm_num : 152512 ≤ 152576), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 152448 ≤ 152512) (by norm_num : 152512 ≤ 152576), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 152448 ≤ 152512) (by norm_num : 152512 ≤ 152576), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_152320_152576 :
    (∑ n ∈ Ico 152320 152576, mobiusTreeValue 16 mobiusTable1200001 n) = (5 : ℤ) ∧
    (∑ n ∈ Ico 152320 152576, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (155 : ℕ) ∧
    (∑ n ∈ Ico 152320 152576, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (163802 : ℤ) ∧
    (∑ n ∈ Ico 152320 152576, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (3276037444219475562658446456 : ℤ) := by
  rcases cdemPrefixStats_152320_152448 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_152448_152576 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 152320 ≤ 152448) (by norm_num : 152448 ≤ 152576), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 152320 ≤ 152448) (by norm_num : 152448 ≤ 152576), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 152320 ≤ 152448) (by norm_num : 152448 ≤ 152576), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 152320 ≤ 152448) (by norm_num : 152448 ≤ 152576), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_152064_152576 :
    (∑ n ∈ Ico 152064 152576, mobiusTreeValue 16 mobiusTable1200001 n) = (-8 : ℤ) ∧
    (∑ n ∈ Ico 152064 152576, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (312 : ℕ) ∧
    (∑ n ∈ Ico 152064 152576, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-263421 : ℤ) ∧
    (∑ n ∈ Ico 152064 152576, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-5268459057057009663214193179 : ℤ) := by
  rcases cdemPrefixStats_152064_152320 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_152320_152576 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 152064 ≤ 152320) (by norm_num : 152320 ≤ 152576), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 152064 ≤ 152320) (by norm_num : 152320 ≤ 152576), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 152064 ≤ 152320) (by norm_num : 152320 ≤ 152576), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 152064 ≤ 152320) (by norm_num : 152320 ≤ 152576), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_151552_152576 :
    (∑ n ∈ Ico 151552 152576, mobiusTreeValue 16 mobiusTable1200001 n) = (-37 : ℤ) ∧
    (∑ n ∈ Ico 151552 152576, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (619 : ℕ) ∧
    (∑ n ∈ Ico 151552 152576, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-1218662 : ℤ) ∧
    (∑ n ∈ Ico 151552 152576, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-24373589947702381880032271523 : ℤ) := by
  rcases cdemPrefixStats_151552_152064 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_152064_152576 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 151552 ≤ 152064) (by norm_num : 152064 ≤ 152576), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 151552 ≤ 152064) (by norm_num : 152064 ≤ 152576), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 151552 ≤ 152064) (by norm_num : 152064 ≤ 152576), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 151552 ≤ 152064) (by norm_num : 152064 ≤ 152576), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_152576_152640 :
    (∑ n ∈ Ico 152576 152640, mobiusTreeValue 16 mobiusTable1200001 n) = (-7 : ℤ) ∧
    (∑ n ∈ Ico 152576 152640, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 152576 152640, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-229292 : ℤ) ∧
    (∑ n ∈ Ico 152576 152640, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-4585919460039529193471345953 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_152640_152704 :
    (∑ n ∈ Ico 152640 152704, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 152640 152704, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 152640 152704, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-32777 : ℤ) ∧
    (∑ n ∈ Ico 152640 152704, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-655543759725818496461557987 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_152576_152704 :
    (∑ n ∈ Ico 152576 152704, mobiusTreeValue 16 mobiusTable1200001 n) = (-8 : ℤ) ∧
    (∑ n ∈ Ico 152576 152704, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (76 : ℕ) ∧
    (∑ n ∈ Ico 152576 152704, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-262069 : ℤ) ∧
    (∑ n ∈ Ico 152576 152704, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-5241463219765347689932903940 : ℤ) := by
  rcases cdemPrefixStats_152576_152640 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_152640_152704 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 152576 ≤ 152640) (by norm_num : 152640 ≤ 152704), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 152576 ≤ 152640) (by norm_num : 152640 ≤ 152704), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 152576 ≤ 152640) (by norm_num : 152640 ≤ 152704), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 152576 ≤ 152640) (by norm_num : 152640 ≤ 152704), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_152704_152768 :
    (∑ n ∈ Ico 152704 152768, mobiusTreeValue 16 mobiusTable1200001 n) = (-6 : ℤ) ∧
    (∑ n ∈ Ico 152704 152768, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 152704 152768, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-196432 : ℤ) ∧
    (∑ n ∈ Ico 152704 152768, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-3928719993856959242602015769 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_152768_152832 :
    (∑ n ∈ Ico 152768 152832, mobiusTreeValue 16 mobiusTable1200001 n) = (-8 : ℤ) ∧
    (∑ n ∈ Ico 152768 152832, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 152768 152832, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-261738 : ℤ) ∧
    (∑ n ∈ Ico 152768 152832, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-5234882587043396282067295793 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_152704_152832 :
    (∑ n ∈ Ico 152704 152832, mobiusTreeValue 16 mobiusTable1200001 n) = (-14 : ℤ) ∧
    (∑ n ∈ Ico 152704 152832, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 152704 152832, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-458170 : ℤ) ∧
    (∑ n ∈ Ico 152704 152832, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-9163602580900355524669311562 : ℤ) := by
  rcases cdemPrefixStats_152704_152768 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_152768_152832 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 152704 ≤ 152768) (by norm_num : 152768 ≤ 152832), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 152704 ≤ 152768) (by norm_num : 152768 ≤ 152832), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 152704 ≤ 152768) (by norm_num : 152768 ≤ 152832), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 152704 ≤ 152768) (by norm_num : 152768 ≤ 152832), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_152576_152832 :
    (∑ n ∈ Ico 152576 152832, mobiusTreeValue 16 mobiusTable1200001 n) = (-22 : ℤ) ∧
    (∑ n ∈ Ico 152576 152832, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (154 : ℕ) ∧
    (∑ n ∈ Ico 152576 152832, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-720239 : ℤ) ∧
    (∑ n ∈ Ico 152576 152832, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-14405065800665703214602215502 : ℤ) := by
  rcases cdemPrefixStats_152576_152704 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_152704_152832 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 152576 ≤ 152704) (by norm_num : 152704 ≤ 152832), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 152576 ≤ 152704) (by norm_num : 152704 ≤ 152832), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 152576 ≤ 152704) (by norm_num : 152704 ≤ 152832), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 152576 ≤ 152704) (by norm_num : 152704 ≤ 152832), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_152832_152896 :
    (∑ n ∈ Ico 152832 152896, mobiusTreeValue 16 mobiusTable1200001 n) = (2 : ℤ) ∧
    (∑ n ∈ Ico 152832 152896, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 152832 152896, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (65389 : ℤ) ∧
    (∑ n ∈ Ico 152832 152896, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1307800439288051525169355189 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_152896_152960 :
    (∑ n ∈ Ico 152896 152960, mobiusTreeValue 16 mobiusTable1200001 n) = (-6 : ℤ) ∧
    (∑ n ∈ Ico 152896 152960, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 152896 152960, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-196147 : ℤ) ∧
    (∑ n ∈ Ico 152896 152960, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-3923000300976240392209362426 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_152832_152960 :
    (∑ n ∈ Ico 152832 152960, mobiusTreeValue 16 mobiusTable1200001 n) = (-4 : ℤ) ∧
    (∑ n ∈ Ico 152832 152960, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 152832 152960, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-130758 : ℤ) ∧
    (∑ n ∈ Ico 152832 152960, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-2615199861688188867040007237 : ℤ) := by
  rcases cdemPrefixStats_152832_152896 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_152896_152960 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 152832 ≤ 152896) (by norm_num : 152896 ≤ 152960), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 152832 ≤ 152896) (by norm_num : 152896 ≤ 152960), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 152832 ≤ 152896) (by norm_num : 152896 ≤ 152960), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 152832 ≤ 152896) (by norm_num : 152896 ≤ 152960), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_152960_153024 :
    (∑ n ∈ Ico 152960 153024, mobiusTreeValue 16 mobiusTable1200001 n) = (5 : ℤ) ∧
    (∑ n ∈ Ico 152960 153024, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 152960 153024, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (163427 : ℤ) ∧
    (∑ n ∈ Ico 152960 153024, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (3268546474283464137126099946 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_153024_153088 :
    (∑ n ∈ Ico 153024 153088, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 153024 153088, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 153024 153088, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (20 : ℤ) ∧
    (∑ n ∈ Ico 153024 153088, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (431168407223364023454127 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_152960_153088 :
    (∑ n ∈ Ico 152960 153088, mobiusTreeValue 16 mobiusTable1200001 n) = (5 : ℤ) ∧
    (∑ n ∈ Ico 152960 153088, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 152960 153088, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (163447 : ℤ) ∧
    (∑ n ∈ Ico 152960 153088, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (3268977642690687501149554073 : ℤ) := by
  rcases cdemPrefixStats_152960_153024 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_153024_153088 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 152960 ≤ 153024) (by norm_num : 153024 ≤ 153088), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 152960 ≤ 153024) (by norm_num : 153024 ≤ 153088), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 152960 ≤ 153024) (by norm_num : 153024 ≤ 153088), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 152960 ≤ 153024) (by norm_num : 153024 ≤ 153088), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_152832_153088 :
    (∑ n ∈ Ico 152832 153088, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 152832 153088, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (155 : ℕ) ∧
    (∑ n ∈ Ico 152832 153088, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (32689 : ℤ) ∧
    (∑ n ∈ Ico 152832 153088, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (653777781002498634109546836 : ℤ) := by
  rcases cdemPrefixStats_152832_152960 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_152960_153088 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 152832 ≤ 152960) (by norm_num : 152960 ≤ 153088), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 152832 ≤ 152960) (by norm_num : 152960 ≤ 153088), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 152832 ≤ 152960) (by norm_num : 152960 ≤ 153088), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 152832 ≤ 152960) (by norm_num : 152960 ≤ 153088), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_152576_153088 :
    (∑ n ∈ Ico 152576 153088, mobiusTreeValue 16 mobiusTable1200001 n) = (-21 : ℤ) ∧
    (∑ n ∈ Ico 152576 153088, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (309 : ℕ) ∧
    (∑ n ∈ Ico 152576 153088, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-687550 : ℤ) ∧
    (∑ n ∈ Ico 152576 153088, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-13751288019663204580492668666 : ℤ) := by
  rcases cdemPrefixStats_152576_152832 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_152832_153088 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 152576 ≤ 152832) (by norm_num : 152832 ≤ 153088), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 152576 ≤ 152832) (by norm_num : 152832 ≤ 153088), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 152576 ≤ 152832) (by norm_num : 152832 ≤ 153088), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 152576 ≤ 152832) (by norm_num : 152832 ≤ 153088), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_153088_153152 :
    (∑ n ∈ Ico 153088 153152, mobiusTreeValue 16 mobiusTable1200001 n) = (-6 : ℤ) ∧
    (∑ n ∈ Ico 153088 153152, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 153088 153152, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-195900 : ℤ) ∧
    (∑ n ∈ Ico 153088 153152, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-3918077404184033507364367325 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_153152_153216 :
    (∑ n ∈ Ico 153152 153216, mobiusTreeValue 16 mobiusTable1200001 n) = (16 : ℤ) ∧
    (∑ n ∈ Ico 153152 153216, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 153152 153216, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (522232 : ℤ) ∧
    (∑ n ∈ Ico 153152 153216, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (10444806113870580175693975319 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_153088_153216 :
    (∑ n ∈ Ico 153088 153216, mobiusTreeValue 16 mobiusTable1200001 n) = (10 : ℤ) ∧
    (∑ n ∈ Ico 153088 153216, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 153088 153216, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (326332 : ℤ) ∧
    (∑ n ∈ Ico 153088 153216, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (6526728709686546668329607994 : ℤ) := by
  rcases cdemPrefixStats_153088_153152 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_153152_153216 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 153088 ≤ 153152) (by norm_num : 153152 ≤ 153216), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 153088 ≤ 153152) (by norm_num : 153152 ≤ 153216), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 153088 ≤ 153152) (by norm_num : 153152 ≤ 153216), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 153088 ≤ 153152) (by norm_num : 153152 ≤ 153216), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_153216_153280 :
    (∑ n ∈ Ico 153216 153280, mobiusTreeValue 16 mobiusTable1200001 n) = (-7 : ℤ) ∧
    (∑ n ∈ Ico 153216 153280, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 153216 153280, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-228368 : ℤ) ∧
    (∑ n ∈ Ico 153216 153280, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-4567410433973556045225124657 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_153280_153344 :
    (∑ n ∈ Ico 153280 153344, mobiusTreeValue 16 mobiusTable1200001 n) = (-7 : ℤ) ∧
    (∑ n ∈ Ico 153280 153344, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 153280 153344, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-228266 : ℤ) ∧
    (∑ n ∈ Ico 153280 153344, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-4565414555704915567278898704 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_153216_153344 :
    (∑ n ∈ Ico 153216 153344, mobiusTreeValue 16 mobiusTable1200001 n) = (-14 : ℤ) ∧
    (∑ n ∈ Ico 153216 153344, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 153216 153344, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-456634 : ℤ) ∧
    (∑ n ∈ Ico 153216 153344, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-9132824989678471612504023361 : ℤ) := by
  rcases cdemPrefixStats_153216_153280 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_153280_153344 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 153216 ≤ 153280) (by norm_num : 153280 ≤ 153344), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 153216 ≤ 153280) (by norm_num : 153280 ≤ 153344), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 153216 ≤ 153280) (by norm_num : 153280 ≤ 153344), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 153216 ≤ 153280) (by norm_num : 153280 ≤ 153344), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_153088_153344 :
    (∑ n ∈ Ico 153088 153344, mobiusTreeValue 16 mobiusTable1200001 n) = (-4 : ℤ) ∧
    (∑ n ∈ Ico 153088 153344, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (156 : ℕ) ∧
    (∑ n ∈ Ico 153088 153344, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-130302 : ℤ) ∧
    (∑ n ∈ Ico 153088 153344, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-2606096279991924944174415367 : ℤ) := by
  rcases cdemPrefixStats_153088_153216 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_153216_153344 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 153088 ≤ 153216) (by norm_num : 153216 ≤ 153344), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 153088 ≤ 153216) (by norm_num : 153216 ≤ 153344), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 153088 ≤ 153216) (by norm_num : 153216 ≤ 153344), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 153088 ≤ 153216) (by norm_num : 153216 ≤ 153344), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_153344_153408 :
    (∑ n ∈ Ico 153344 153408, mobiusTreeValue 16 mobiusTable1200001 n) = (6 : ℤ) ∧
    (∑ n ∈ Ico 153344 153408, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 153344 153408, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (195571 : ℤ) ∧
    (∑ n ∈ Ico 153344 153408, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (3911432159276391015356000275 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_153408_153472 :
    (∑ n ∈ Ico 153408 153472, mobiusTreeValue 16 mobiusTable1200001 n) = (-6 : ℤ) ∧
    (∑ n ∈ Ico 153408 153472, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 153408 153472, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-195533 : ℤ) ∧
    (∑ n ∈ Ico 153408 153472, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-3910739534978962894851594750 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_153344_153472 :
    (∑ n ∈ Ico 153344 153472, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 153344 153472, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 153344 153472, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (38 : ℤ) ∧
    (∑ n ∈ Ico 153344 153472, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (692624297428120504405525 : ℤ) := by
  rcases cdemPrefixStats_153344_153408 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_153408_153472 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 153344 ≤ 153408) (by norm_num : 153408 ≤ 153472), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 153344 ≤ 153408) (by norm_num : 153408 ≤ 153472), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 153344 ≤ 153408) (by norm_num : 153408 ≤ 153472), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 153344 ≤ 153408) (by norm_num : 153408 ≤ 153472), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_153472_153536 :
    (∑ n ∈ Ico 153472 153536, mobiusTreeValue 16 mobiusTable1200001 n) = (-7 : ℤ) ∧
    (∑ n ∈ Ico 153472 153536, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 153472 153536, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-227979 : ℤ) ∧
    (∑ n ∈ Ico 153472 153536, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-4559670751106536024442661602 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_153536_153600 :
    (∑ n ∈ Ico 153536 153600, mobiusTreeValue 16 mobiusTable1200001 n) = (12 : ℤ) ∧
    (∑ n ∈ Ico 153536 153600, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 153536 153600, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (390743 : ℤ) ∧
    (∑ n ∈ Ico 153536 153600, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (7814959221828644515854119667 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_153472_153600 :
    (∑ n ∈ Ico 153472 153600, mobiusTreeValue 16 mobiusTable1200001 n) = (5 : ℤ) ∧
    (∑ n ∈ Ico 153472 153600, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (79 : ℕ) ∧
    (∑ n ∈ Ico 153472 153600, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (162764 : ℤ) ∧
    (∑ n ∈ Ico 153472 153600, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (3255288470722108491411458065 : ℤ) := by
  rcases cdemPrefixStats_153472_153536 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_153536_153600 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 153472 ≤ 153536) (by norm_num : 153536 ≤ 153600), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 153472 ≤ 153536) (by norm_num : 153536 ≤ 153600), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 153472 ≤ 153536) (by norm_num : 153536 ≤ 153600), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 153472 ≤ 153536) (by norm_num : 153536 ≤ 153600), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_153344_153600 :
    (∑ n ∈ Ico 153344 153600, mobiusTreeValue 16 mobiusTable1200001 n) = (5 : ℤ) ∧
    (∑ n ∈ Ico 153344 153600, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (157 : ℕ) ∧
    (∑ n ∈ Ico 153344 153600, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (162802 : ℤ) ∧
    (∑ n ∈ Ico 153344 153600, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (3255981095019536611915863590 : ℤ) := by
  rcases cdemPrefixStats_153344_153472 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_153472_153600 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 153344 ≤ 153472) (by norm_num : 153472 ≤ 153600), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 153344 ≤ 153472) (by norm_num : 153472 ≤ 153600), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 153344 ≤ 153472) (by norm_num : 153472 ≤ 153600), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 153344 ≤ 153472) (by norm_num : 153472 ≤ 153600), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_153088_153600 :
    (∑ n ∈ Ico 153088 153600, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 153088 153600, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (313 : ℕ) ∧
    (∑ n ∈ Ico 153088 153600, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (32500 : ℤ) ∧
    (∑ n ∈ Ico 153088 153600, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (649884815027611667741448223 : ℤ) := by
  rcases cdemPrefixStats_153088_153344 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_153344_153600 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 153088 ≤ 153344) (by norm_num : 153344 ≤ 153600), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 153088 ≤ 153344) (by norm_num : 153344 ≤ 153600), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 153088 ≤ 153344) (by norm_num : 153344 ≤ 153600), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 153088 ≤ 153344) (by norm_num : 153344 ≤ 153600), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_152576_153600 :
    (∑ n ∈ Ico 152576 153600, mobiusTreeValue 16 mobiusTable1200001 n) = (-20 : ℤ) ∧
    (∑ n ∈ Ico 152576 153600, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (622 : ℕ) ∧
    (∑ n ∈ Ico 152576 153600, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-655050 : ℤ) ∧
    (∑ n ∈ Ico 152576 153600, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-13101403204635592912751220443 : ℤ) := by
  rcases cdemPrefixStats_152576_153088 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_153088_153600 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 152576 ≤ 153088) (by norm_num : 153088 ≤ 153600), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 152576 ≤ 153088) (by norm_num : 153088 ≤ 153600), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 152576 ≤ 153088) (by norm_num : 153088 ≤ 153600), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 152576 ≤ 153088) (by norm_num : 153088 ≤ 153600), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_151552_153600 :
    (∑ n ∈ Ico 151552 153600, mobiusTreeValue 16 mobiusTable1200001 n) = (-57 : ℤ) ∧
    (∑ n ∈ Ico 151552 153600, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (1241 : ℕ) ∧
    (∑ n ∈ Ico 151552 153600, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-1873712 : ℤ) ∧
    (∑ n ∈ Ico 151552 153600, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-37474993152337974792783491966 : ℤ) := by
  rcases cdemPrefixStats_151552_152576 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_152576_153600 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 151552 ≤ 152576) (by norm_num : 152576 ≤ 153600), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 151552 ≤ 152576) (by norm_num : 152576 ≤ 153600), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 151552 ≤ 152576) (by norm_num : 152576 ≤ 153600), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 151552 ≤ 152576) (by norm_num : 152576 ≤ 153600), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_153600_153664 :
    (∑ n ∈ Ico 153600 153664, mobiusTreeValue 16 mobiusTable1200001 n) = (-4 : ℤ) ∧
    (∑ n ∈ Ico 153600 153664, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 153600 153664, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-130197 : ℤ) ∧
    (∑ n ∈ Ico 153600 153664, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-2603980108869671791749751802 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_153664_153728 :
    (∑ n ∈ Ico 153664 153728, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 153664 153728, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 153664 153728, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (17 : ℤ) ∧
    (∑ n ∈ Ico 153664 153728, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (325951408172826424784933 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_153600_153728 :
    (∑ n ∈ Ico 153600 153728, mobiusTreeValue 16 mobiusTable1200001 n) = (-4 : ℤ) ∧
    (∑ n ∈ Ico 153600 153728, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (80 : ℕ) ∧
    (∑ n ∈ Ico 153600 153728, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-130180 : ℤ) ∧
    (∑ n ∈ Ico 153600 153728, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-2603654157461498965324966869 : ℤ) := by
  rcases cdemPrefixStats_153600_153664 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_153664_153728 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 153600 ≤ 153664) (by norm_num : 153664 ≤ 153728), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 153600 ≤ 153664) (by norm_num : 153664 ≤ 153728), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 153600 ≤ 153664) (by norm_num : 153664 ≤ 153728), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 153600 ≤ 153664) (by norm_num : 153664 ≤ 153728), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_153728_153792 :
    (∑ n ∈ Ico 153728 153792, mobiusTreeValue 16 mobiusTable1200001 n) = (2 : ℤ) ∧
    (∑ n ∈ Ico 153728 153792, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (36 : ℕ) ∧
    (∑ n ∈ Ico 153728 153792, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (65018 : ℤ) ∧
    (∑ n ∈ Ico 153728 153792, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1300364711839629415999450903 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_153792_153856 :
    (∑ n ∈ Ico 153792 153856, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 153792 153856, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 153792 153856, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-32530 : ℤ) ∧
    (∑ n ∈ Ico 153792 153856, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-650575505597042725941755032 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_153728_153856 :
    (∑ n ∈ Ico 153728 153856, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 153728 153856, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (75 : ℕ) ∧
    (∑ n ∈ Ico 153728 153856, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (32488 : ℤ) ∧
    (∑ n ∈ Ico 153728 153856, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (649789206242586690057695871 : ℤ) := by
  rcases cdemPrefixStats_153728_153792 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_153792_153856 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 153728 ≤ 153792) (by norm_num : 153792 ≤ 153856), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 153728 ≤ 153792) (by norm_num : 153792 ≤ 153856), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 153728 ≤ 153792) (by norm_num : 153792 ≤ 153856), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 153728 ≤ 153792) (by norm_num : 153792 ≤ 153856), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_153600_153856 :
    (∑ n ∈ Ico 153600 153856, mobiusTreeValue 16 mobiusTable1200001 n) = (-3 : ℤ) ∧
    (∑ n ∈ Ico 153600 153856, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (155 : ℕ) ∧
    (∑ n ∈ Ico 153600 153856, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-97692 : ℤ) ∧
    (∑ n ∈ Ico 153600 153856, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-1953864951218912275267270998 : ℤ) := by
  rcases cdemPrefixStats_153600_153728 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_153728_153856 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 153600 ≤ 153728) (by norm_num : 153728 ≤ 153856), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 153600 ≤ 153728) (by norm_num : 153728 ≤ 153856), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 153600 ≤ 153728) (by norm_num : 153728 ≤ 153856), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 153600 ≤ 153728) (by norm_num : 153728 ≤ 153856), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_153856_153920 :
    (∑ n ∈ Ico 153856 153920, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 153856 153920, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 153856 153920, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (32485 : ℤ) ∧
    (∑ n ∈ Ico 153856 153920, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (649650140177886256761174471 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_153920_153984 :
    (∑ n ∈ Ico 153920 153984, mobiusTreeValue 16 mobiusTable1200001 n) = (3 : ℤ) ∧
    (∑ n ∈ Ico 153920 153984, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 153920 153984, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (97381 : ℤ) ∧
    (∑ n ∈ Ico 153920 153984, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1947672164813763008895072633 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_153856_153984 :
    (∑ n ∈ Ico 153856 153984, mobiusTreeValue 16 mobiusTable1200001 n) = (4 : ℤ) ∧
    (∑ n ∈ Ico 153856 153984, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 153856 153984, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (129866 : ℤ) ∧
    (∑ n ∈ Ico 153856 153984, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (2597322304991649265656247104 : ℤ) := by
  rcases cdemPrefixStats_153856_153920 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_153920_153984 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 153856 ≤ 153920) (by norm_num : 153920 ≤ 153984), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 153856 ≤ 153920) (by norm_num : 153920 ≤ 153984), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 153856 ≤ 153920) (by norm_num : 153920 ≤ 153984), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 153856 ≤ 153920) (by norm_num : 153920 ≤ 153984), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_153984_154048 :
    (∑ n ∈ Ico 153984 154048, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 153984 154048, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 153984 154048, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (32443 : ℤ) ∧
    (∑ n ∈ Ico 153984 154048, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (648849051530654210487668944 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_154048_154112 :
    (∑ n ∈ Ico 154048 154112, mobiusTreeValue 16 mobiusTable1200001 n) = (-7 : ℤ) ∧
    (∑ n ∈ Ico 154048 154112, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 154048 154112, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-227166 : ℤ) ∧
    (∑ n ∈ Ico 154048 154112, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-4543330463918214838048854760 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_153984_154112 :
    (∑ n ∈ Ico 153984 154112, mobiusTreeValue 16 mobiusTable1200001 n) = (-6 : ℤ) ∧
    (∑ n ∈ Ico 153984 154112, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 153984 154112, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-194723 : ℤ) ∧
    (∑ n ∈ Ico 153984 154112, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-3894481412387560627561185816 : ℤ) := by
  rcases cdemPrefixStats_153984_154048 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_154048_154112 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 153984 ≤ 154048) (by norm_num : 154048 ≤ 154112), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 153984 ≤ 154048) (by norm_num : 154048 ≤ 154112), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 153984 ≤ 154048) (by norm_num : 154048 ≤ 154112), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 153984 ≤ 154048) (by norm_num : 154048 ≤ 154112), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_153856_154112 :
    (∑ n ∈ Ico 153856 154112, mobiusTreeValue 16 mobiusTable1200001 n) = (-2 : ℤ) ∧
    (∑ n ∈ Ico 153856 154112, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (156 : ℕ) ∧
    (∑ n ∈ Ico 153856 154112, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-64857 : ℤ) ∧
    (∑ n ∈ Ico 153856 154112, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-1297159107395911361904938712 : ℤ) := by
  rcases cdemPrefixStats_153856_153984 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_153984_154112 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 153856 ≤ 153984) (by norm_num : 153984 ≤ 154112), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 153856 ≤ 153984) (by norm_num : 153984 ≤ 154112), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 153856 ≤ 153984) (by norm_num : 153984 ≤ 154112), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 153856 ≤ 153984) (by norm_num : 153984 ≤ 154112), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_153600_154112 :
    (∑ n ∈ Ico 153600 154112, mobiusTreeValue 16 mobiusTable1200001 n) = (-5 : ℤ) ∧
    (∑ n ∈ Ico 153600 154112, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (311 : ℕ) ∧
    (∑ n ∈ Ico 153600 154112, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-162549 : ℤ) ∧
    (∑ n ∈ Ico 153600 154112, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-3251024058614823637172209710 : ℤ) := by
  rcases cdemPrefixStats_153600_153856 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_153856_154112 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 153600 ≤ 153856) (by norm_num : 153856 ≤ 154112), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 153600 ≤ 153856) (by norm_num : 153856 ≤ 154112), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 153600 ≤ 153856) (by norm_num : 153856 ≤ 154112), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 153600 ≤ 153856) (by norm_num : 153856 ≤ 154112), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_154112_154176 :
    (∑ n ∈ Ico 154112 154176, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 154112 154176, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 154112 154176, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-32441 : ℤ) ∧
    (∑ n ∈ Ico 154112 154176, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-648807201388801467729744359 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_154176_154240 :
    (∑ n ∈ Ico 154176 154240, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 154176 154240, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 154176 154240, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (32450 : ℤ) ∧
    (∑ n ∈ Ico 154176 154240, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (648979415015392411068338242 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_154112_154240 :
    (∑ n ∈ Ico 154112 154240, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 154112 154240, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (80 : ℕ) ∧
    (∑ n ∈ Ico 154112 154240, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (9 : ℤ) ∧
    (∑ n ∈ Ico 154112 154240, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (172213626590943338593883 : ℤ) := by
  rcases cdemPrefixStats_154112_154176 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_154176_154240 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 154112 ≤ 154176) (by norm_num : 154176 ≤ 154240), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 154112 ≤ 154176) (by norm_num : 154176 ≤ 154240), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 154112 ≤ 154176) (by norm_num : 154176 ≤ 154240), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 154112 ≤ 154176) (by norm_num : 154176 ≤ 154240), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_154240_154304 :
    (∑ n ∈ Ico 154240 154304, mobiusTreeValue 16 mobiusTable1200001 n) = (-3 : ℤ) ∧
    (∑ n ∈ Ico 154240 154304, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 154240 154304, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-97219 : ℤ) ∧
    (∑ n ∈ Ico 154240 154304, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-1944474580884030177503114700 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_154304_154368 :
    (∑ n ∈ Ico 154304 154368, mobiusTreeValue 16 mobiusTable1200001 n) = (4 : ℤ) ∧
    (∑ n ∈ Ico 154304 154368, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 154304 154368, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (129583 : ℤ) ∧
    (∑ n ∈ Ico 154304 154368, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (2591752194553008170098414036 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_154240_154368 :
    (∑ n ∈ Ico 154240 154368, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 154240 154368, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (79 : ℕ) ∧
    (∑ n ∈ Ico 154240 154368, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (32364 : ℤ) ∧
    (∑ n ∈ Ico 154240 154368, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (647277613668977992595299336 : ℤ) := by
  rcases cdemPrefixStats_154240_154304 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_154304_154368 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 154240 ≤ 154304) (by norm_num : 154304 ≤ 154368), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 154240 ≤ 154304) (by norm_num : 154304 ≤ 154368), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 154240 ≤ 154304) (by norm_num : 154304 ≤ 154368), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 154240 ≤ 154304) (by norm_num : 154304 ≤ 154368), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_154112_154368 :
    (∑ n ∈ Ico 154112 154368, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 154112 154368, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (159 : ℕ) ∧
    (∑ n ∈ Ico 154112 154368, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (32373 : ℤ) ∧
    (∑ n ∈ Ico 154112 154368, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (647449827295568935933893219 : ℤ) := by
  rcases cdemPrefixStats_154112_154240 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_154240_154368 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 154112 ≤ 154240) (by norm_num : 154240 ≤ 154368), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 154112 ≤ 154240) (by norm_num : 154240 ≤ 154368), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 154112 ≤ 154240) (by norm_num : 154240 ≤ 154368), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 154112 ≤ 154240) (by norm_num : 154240 ≤ 154368), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_154368_154432 :
    (∑ n ∈ Ico 154368 154432, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 154368 154432, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 154368 154432, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (32411 : ℤ) ∧
    (∑ n ∈ Ico 154368 154432, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (648226222707113080930083614 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_154432_154496 :
    (∑ n ∈ Ico 154432 154496, mobiusTreeValue 16 mobiusTable1200001 n) = (8 : ℤ) ∧
    (∑ n ∈ Ico 154432 154496, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 154432 154496, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (258972 : ℤ) ∧
    (∑ n ∈ Ico 154432 154496, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (5179577570581462010988765011 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_154368_154496 :
    (∑ n ∈ Ico 154368 154496, mobiusTreeValue 16 mobiusTable1200001 n) = (9 : ℤ) ∧
    (∑ n ∈ Ico 154368 154496, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 154368 154496, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (291383 : ℤ) ∧
    (∑ n ∈ Ico 154368 154496, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (5827803793288575091918848625 : ℤ) := by
  rcases cdemPrefixStats_154368_154432 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_154432_154496 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 154368 ≤ 154432) (by norm_num : 154432 ≤ 154496), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 154368 ≤ 154432) (by norm_num : 154432 ≤ 154496), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 154368 ≤ 154432) (by norm_num : 154432 ≤ 154496), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 154368 ≤ 154432) (by norm_num : 154432 ≤ 154496), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_154496_154560 :
    (∑ n ∈ Ico 154496 154560, mobiusTreeValue 16 mobiusTable1200001 n) = (9 : ℤ) ∧
    (∑ n ∈ Ico 154496 154560, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 154496 154560, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (291170 : ℤ) ∧
    (∑ n ∈ Ico 154496 154560, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (5823534020266847406583535423 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_154560_154624 :
    (∑ n ∈ Ico 154560 154624, mobiusTreeValue 16 mobiusTable1200001 n) = (-8 : ℤ) ∧
    (∑ n ∈ Ico 154560 154624, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 154560 154624, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-258752 : ℤ) ∧
    (∑ n ∈ Ico 154560 154624, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-5175154774722743236338242423 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_154496_154624 :
    (∑ n ∈ Ico 154496 154624, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 154496 154624, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 154496 154624, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (32418 : ℤ) ∧
    (∑ n ∈ Ico 154496 154624, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (648379245544104170245293000 : ℤ) := by
  rcases cdemPrefixStats_154496_154560 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_154560_154624 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 154496 ≤ 154560) (by norm_num : 154560 ≤ 154624), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 154496 ≤ 154560) (by norm_num : 154560 ≤ 154624), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 154496 ≤ 154560) (by norm_num : 154560 ≤ 154624), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 154496 ≤ 154560) (by norm_num : 154560 ≤ 154624), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_154368_154624 :
    (∑ n ∈ Ico 154368 154624, mobiusTreeValue 16 mobiusTable1200001 n) = (10 : ℤ) ∧
    (∑ n ∈ Ico 154368 154624, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (154 : ℕ) ∧
    (∑ n ∈ Ico 154368 154624, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (323801 : ℤ) ∧
    (∑ n ∈ Ico 154368 154624, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (6476183038832679262164141625 : ℤ) := by
  rcases cdemPrefixStats_154368_154496 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_154496_154624 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 154368 ≤ 154496) (by norm_num : 154496 ≤ 154624), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 154368 ≤ 154496) (by norm_num : 154496 ≤ 154624), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 154368 ≤ 154496) (by norm_num : 154496 ≤ 154624), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 154368 ≤ 154496) (by norm_num : 154496 ≤ 154624), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_154112_154624 :
    (∑ n ∈ Ico 154112 154624, mobiusTreeValue 16 mobiusTable1200001 n) = (11 : ℤ) ∧
    (∑ n ∈ Ico 154112 154624, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (313 : ℕ) ∧
    (∑ n ∈ Ico 154112 154624, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (356174 : ℤ) ∧
    (∑ n ∈ Ico 154112 154624, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (7123632866128248198098034844 : ℤ) := by
  rcases cdemPrefixStats_154112_154368 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_154368_154624 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 154112 ≤ 154368) (by norm_num : 154368 ≤ 154624), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 154112 ≤ 154368) (by norm_num : 154368 ≤ 154624), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 154112 ≤ 154368) (by norm_num : 154368 ≤ 154624), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 154112 ≤ 154368) (by norm_num : 154368 ≤ 154624), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_153600_154624 :
    (∑ n ∈ Ico 153600 154624, mobiusTreeValue 16 mobiusTable1200001 n) = (6 : ℤ) ∧
    (∑ n ∈ Ico 153600 154624, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (624 : ℕ) ∧
    (∑ n ∈ Ico 153600 154624, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (193625 : ℤ) ∧
    (∑ n ∈ Ico 153600 154624, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (3872608807513424560925825134 : ℤ) := by
  rcases cdemPrefixStats_153600_154112 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_154112_154624 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 153600 ≤ 154112) (by norm_num : 154112 ≤ 154624), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 153600 ≤ 154112) (by norm_num : 154112 ≤ 154624), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 153600 ≤ 154112) (by norm_num : 154112 ≤ 154624), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 153600 ≤ 154112) (by norm_num : 154112 ≤ 154624), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_154624_154688 :
    (∑ n ∈ Ico 154624 154688, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 154624 154688, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 154624 154688, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (32352 : ℤ) ∧
    (∑ n ∈ Ico 154624 154688, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (647085483176424961629978917 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_154688_154752 :
    (∑ n ∈ Ico 154688 154752, mobiusTreeValue 16 mobiusTable1200001 n) = (7 : ℤ) ∧
    (∑ n ∈ Ico 154688 154752, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 154688 154752, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (226215 : ℤ) ∧
    (∑ n ∈ Ico 154688 154752, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (4524364688924368562358034383 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_154624_154752 :
    (∑ n ∈ Ico 154624 154752, mobiusTreeValue 16 mobiusTable1200001 n) = (8 : ℤ) ∧
    (∑ n ∈ Ico 154624 154752, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (74 : ℕ) ∧
    (∑ n ∈ Ico 154624 154752, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (258567 : ℤ) ∧
    (∑ n ∈ Ico 154624 154752, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (5171450172100793523988013300 : ℤ) := by
  rcases cdemPrefixStats_154624_154688 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_154688_154752 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 154624 ≤ 154688) (by norm_num : 154688 ≤ 154752), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 154624 ≤ 154688) (by norm_num : 154688 ≤ 154752), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 154624 ≤ 154688) (by norm_num : 154688 ≤ 154752), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 154624 ≤ 154688) (by norm_num : 154688 ≤ 154752), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_154752_154816 :
    (∑ n ∈ Ico 154752 154816, mobiusTreeValue 16 mobiusTable1200001 n) = (-7 : ℤ) ∧
    (∑ n ∈ Ico 154752 154816, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 154752 154816, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-226129 : ℤ) ∧
    (∑ n ∈ Ico 154752 154816, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-4522648404701943001216489442 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_154816_154880 :
    (∑ n ∈ Ico 154816 154880, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 154816 154880, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 154816 154880, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-32300 : ℤ) ∧
    (∑ n ∈ Ico 154816 154880, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-646003117396244801692819273 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_154752_154880 :
    (∑ n ∈ Ico 154752 154880, mobiusTreeValue 16 mobiusTable1200001 n) = (-8 : ℤ) ∧
    (∑ n ∈ Ico 154752 154880, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (80 : ℕ) ∧
    (∑ n ∈ Ico 154752 154880, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-258429 : ℤ) ∧
    (∑ n ∈ Ico 154752 154880, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-5168651522098187802909308715 : ℤ) := by
  rcases cdemPrefixStats_154752_154816 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_154816_154880 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 154752 ≤ 154816) (by norm_num : 154816 ≤ 154880), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 154752 ≤ 154816) (by norm_num : 154816 ≤ 154880), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 154752 ≤ 154816) (by norm_num : 154816 ≤ 154880), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 154752 ≤ 154816) (by norm_num : 154816 ≤ 154880), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_154624_154880 :
    (∑ n ∈ Ico 154624 154880, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 154624 154880, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (154 : ℕ) ∧
    (∑ n ∈ Ico 154624 154880, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (138 : ℤ) ∧
    (∑ n ∈ Ico 154624 154880, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (2798650002605721078704585 : ℤ) := by
  rcases cdemPrefixStats_154624_154752 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_154752_154880 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 154624 ≤ 154752) (by norm_num : 154752 ≤ 154880), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 154624 ≤ 154752) (by norm_num : 154752 ≤ 154880), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 154624 ≤ 154752) (by norm_num : 154752 ≤ 154880), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 154624 ≤ 154752) (by norm_num : 154752 ≤ 154880), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_154880_154944 :
    (∑ n ∈ Ico 154880 154944, mobiusTreeValue 16 mobiusTable1200001 n) = (-3 : ℤ) ∧
    (∑ n ∈ Ico 154880 154944, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 154880 154944, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-96826 : ℤ) ∧
    (∑ n ∈ Ico 154880 154944, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-1936575057431564958949762975 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_154944_155008 :
    (∑ n ∈ Ico 154944 155008, mobiusTreeValue 16 mobiusTable1200001 n) = (4 : ℤ) ∧
    (∑ n ∈ Ico 154944 155008, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (36 : ℕ) ∧
    (∑ n ∈ Ico 154944 155008, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (129098 : ℤ) ∧
    (∑ n ∈ Ico 154944 155008, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (2582064939604430800685218844 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_154880_155008 :
    (∑ n ∈ Ico 154880 155008, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 154880 155008, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (75 : ℕ) ∧
    (∑ n ∈ Ico 154880 155008, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (32272 : ℤ) ∧
    (∑ n ∈ Ico 154880 155008, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (645489882172865841735455869 : ℤ) := by
  rcases cdemPrefixStats_154880_154944 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_154944_155008 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 154880 ≤ 154944) (by norm_num : 154944 ≤ 155008), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 154880 ≤ 154944) (by norm_num : 154944 ≤ 155008), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 154880 ≤ 154944) (by norm_num : 154944 ≤ 155008), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 154880 ≤ 154944) (by norm_num : 154944 ≤ 155008), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_155008_155072 :
    (∑ n ∈ Ico 155008 155072, mobiusTreeValue 16 mobiusTable1200001 n) = (10 : ℤ) ∧
    (∑ n ∈ Ico 155008 155072, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (42 : ℕ) ∧
    (∑ n ∈ Ico 155008 155072, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (322473 : ℤ) ∧
    (∑ n ∈ Ico 155008 155072, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (6449586537403550382152683395 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_155072_155136 :
    (∑ n ∈ Ico 155072 155136, mobiusTreeValue 16 mobiusTable1200001 n) = (6 : ℤ) ∧
    (∑ n ∈ Ico 155072 155136, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 155072 155136, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (193357 : ℤ) ∧
    (∑ n ∈ Ico 155072 155136, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (3867229122937576764980242591 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_155008_155136 :
    (∑ n ∈ Ico 155008 155136, mobiusTreeValue 16 mobiusTable1200001 n) = (16 : ℤ) ∧
    (∑ n ∈ Ico 155008 155136, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (80 : ℕ) ∧
    (∑ n ∈ Ico 155008 155136, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (515830 : ℤ) ∧
    (∑ n ∈ Ico 155008 155136, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (10316815660341127147132925986 : ℤ) := by
  rcases cdemPrefixStats_155008_155072 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_155072_155136 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 155008 ≤ 155072) (by norm_num : 155072 ≤ 155136), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 155008 ≤ 155072) (by norm_num : 155072 ≤ 155136), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 155008 ≤ 155072) (by norm_num : 155072 ≤ 155136), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 155008 ≤ 155072) (by norm_num : 155072 ≤ 155136), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_154880_155136 :
    (∑ n ∈ Ico 154880 155136, mobiusTreeValue 16 mobiusTable1200001 n) = (17 : ℤ) ∧
    (∑ n ∈ Ico 154880 155136, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (155 : ℕ) ∧
    (∑ n ∈ Ico 154880 155136, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (548102 : ℤ) ∧
    (∑ n ∈ Ico 154880 155136, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (10962305542513992988868381855 : ℤ) := by
  rcases cdemPrefixStats_154880_155008 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_155008_155136 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 154880 ≤ 155008) (by norm_num : 155008 ≤ 155136), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 154880 ≤ 155008) (by norm_num : 155008 ≤ 155136), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 154880 ≤ 155008) (by norm_num : 155008 ≤ 155136), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 154880 ≤ 155008) (by norm_num : 155008 ≤ 155136), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_154624_155136 :
    (∑ n ∈ Ico 154624 155136, mobiusTreeValue 16 mobiusTable1200001 n) = (17 : ℤ) ∧
    (∑ n ∈ Ico 154624 155136, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (309 : ℕ) ∧
    (∑ n ∈ Ico 154624 155136, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (548240 : ℤ) ∧
    (∑ n ∈ Ico 154624 155136, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (10965104192516598709947086440 : ℤ) := by
  rcases cdemPrefixStats_154624_154880 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_154880_155136 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 154624 ≤ 154880) (by norm_num : 154880 ≤ 155136), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 154624 ≤ 154880) (by norm_num : 154880 ≤ 155136), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 154624 ≤ 154880) (by norm_num : 154880 ≤ 155136), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 154624 ≤ 154880) (by norm_num : 154880 ≤ 155136), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_155136_155200 :
    (∑ n ∈ Ico 155136 155200, mobiusTreeValue 16 mobiusTable1200001 n) = (7 : ℤ) ∧
    (∑ n ∈ Ico 155136 155200, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 155136 155200, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (225569 : ℤ) ∧
    (∑ n ∈ Ico 155136 155200, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (4511397286844601214469327501 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_155200_155264 :
    (∑ n ∈ Ico 155200 155264, mobiusTreeValue 16 mobiusTable1200001 n) = (-5 : ℤ) ∧
    (∑ n ∈ Ico 155200 155264, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 155200 155264, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-161097 : ℤ) ∧
    (∑ n ∈ Ico 155200 155264, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-3221981377626106764180503327 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_155136_155264 :
    (∑ n ∈ Ico 155136 155264, mobiusTreeValue 16 mobiusTable1200001 n) = (2 : ℤ) ∧
    (∑ n ∈ Ico 155136 155264, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 155136 155264, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (64472 : ℤ) ∧
    (∑ n ∈ Ico 155136 155264, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1289415909218494450288824174 : ℤ) := by
  rcases cdemPrefixStats_155136_155200 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_155200_155264 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 155136 ≤ 155200) (by norm_num : 155200 ≤ 155264), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 155136 ≤ 155200) (by norm_num : 155200 ≤ 155264), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 155136 ≤ 155200) (by norm_num : 155200 ≤ 155264), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 155136 ≤ 155200) (by norm_num : 155200 ≤ 155264), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_155264_155328 :
    (∑ n ∈ Ico 155264 155328, mobiusTreeValue 16 mobiusTable1200001 n) = (-9 : ℤ) ∧
    (∑ n ∈ Ico 155264 155328, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 155264 155328, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-289778 : ℤ) ∧
    (∑ n ∈ Ico 155264 155328, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-5795678814342423751913882595 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_155328_155392 :
    (∑ n ∈ Ico 155328 155392, mobiusTreeValue 16 mobiusTable1200001 n) = (7 : ℤ) ∧
    (∑ n ∈ Ico 155328 155392, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 155328 155392, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (225282 : ℤ) ∧
    (∑ n ∈ Ico 155328 155392, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (4505639450699287057591748009 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_155264_155392 :
    (∑ n ∈ Ico 155264 155392, mobiusTreeValue 16 mobiusTable1200001 n) = (-2 : ℤ) ∧
    (∑ n ∈ Ico 155264 155392, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 155264 155392, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-64496 : ℤ) ∧
    (∑ n ∈ Ico 155264 155392, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-1290039363643136694322134586 : ℤ) := by
  rcases cdemPrefixStats_155264_155328 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_155328_155392 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 155264 ≤ 155328) (by norm_num : 155328 ≤ 155392), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 155264 ≤ 155328) (by norm_num : 155328 ≤ 155392), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 155264 ≤ 155328) (by norm_num : 155328 ≤ 155392), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 155264 ≤ 155328) (by norm_num : 155328 ≤ 155392), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_155136_155392 :
    (∑ n ∈ Ico 155136 155392, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 155136 155392, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (156 : ℕ) ∧
    (∑ n ∈ Ico 155136 155392, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-24 : ℤ) ∧
    (∑ n ∈ Ico 155136 155392, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-623454424642244033310412 : ℤ) := by
  rcases cdemPrefixStats_155136_155264 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_155264_155392 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 155136 ≤ 155264) (by norm_num : 155264 ≤ 155392), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 155136 ≤ 155264) (by norm_num : 155264 ≤ 155392), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 155136 ≤ 155264) (by norm_num : 155264 ≤ 155392), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 155136 ≤ 155264) (by norm_num : 155264 ≤ 155392), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_155392_155456 :
    (∑ n ∈ Ico 155392 155456, mobiusTreeValue 16 mobiusTable1200001 n) = (8 : ℤ) ∧
    (∑ n ∈ Ico 155392 155456, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 155392 155456, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (257356 : ℤ) ∧
    (∑ n ∈ Ico 155392 155456, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (5147231036969910079599553691 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_155456_155520 :
    (∑ n ∈ Ico 155456 155520, mobiusTreeValue 16 mobiusTable1200001 n) = (3 : ℤ) ∧
    (∑ n ∈ Ico 155456 155520, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 155456 155520, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (96511 : ℤ) ∧
    (∑ n ∈ Ico 155456 155520, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1930294466291354398478550170 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_155392_155520 :
    (∑ n ∈ Ico 155392 155520, mobiusTreeValue 16 mobiusTable1200001 n) = (11 : ℤ) ∧
    (∑ n ∈ Ico 155392 155520, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (79 : ℕ) ∧
    (∑ n ∈ Ico 155392 155520, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (353867 : ℤ) ∧
    (∑ n ∈ Ico 155392 155520, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (7077525503261264478078103861 : ℤ) := by
  rcases cdemPrefixStats_155392_155456 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_155456_155520 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 155392 ≤ 155456) (by norm_num : 155456 ≤ 155520), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 155392 ≤ 155456) (by norm_num : 155456 ≤ 155520), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 155392 ≤ 155456) (by norm_num : 155456 ≤ 155520), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 155392 ≤ 155456) (by norm_num : 155456 ≤ 155520), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_155520_155584 :
    (∑ n ∈ Ico 155520 155584, mobiusTreeValue 16 mobiusTable1200001 n) = (-6 : ℤ) ∧
    (∑ n ∈ Ico 155520 155584, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 155520 155584, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-192872 : ℤ) ∧
    (∑ n ∈ Ico 155520 155584, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-3857512159454302753686084451 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_155584_155648 :
    (∑ n ∈ Ico 155584 155648, mobiusTreeValue 16 mobiusTable1200001 n) = (3 : ℤ) ∧
    (∑ n ∈ Ico 155584 155648, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 155584 155648, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (96405 : ℤ) ∧
    (∑ n ∈ Ico 155584 155648, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1928160885959472396761599560 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_155520_155648 :
    (∑ n ∈ Ico 155520 155648, mobiusTreeValue 16 mobiusTable1200001 n) = (-3 : ℤ) ∧
    (∑ n ∈ Ico 155520 155648, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 155520 155648, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-96467 : ℤ) ∧
    (∑ n ∈ Ico 155520 155648, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-1929351273494830356924484891 : ℤ) := by
  rcases cdemPrefixStats_155520_155584 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_155584_155648 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 155520 ≤ 155584) (by norm_num : 155584 ≤ 155648), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 155520 ≤ 155584) (by norm_num : 155584 ≤ 155648), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 155520 ≤ 155584) (by norm_num : 155584 ≤ 155648), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 155520 ≤ 155584) (by norm_num : 155584 ≤ 155648), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_155392_155648 :
    (∑ n ∈ Ico 155392 155648, mobiusTreeValue 16 mobiusTable1200001 n) = (8 : ℤ) ∧
    (∑ n ∈ Ico 155392 155648, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (156 : ℕ) ∧
    (∑ n ∈ Ico 155392 155648, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (257400 : ℤ) ∧
    (∑ n ∈ Ico 155392 155648, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (5148174229766434121153618970 : ℤ) := by
  rcases cdemPrefixStats_155392_155520 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_155520_155648 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 155392 ≤ 155520) (by norm_num : 155520 ≤ 155648), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 155392 ≤ 155520) (by norm_num : 155520 ≤ 155648), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 155392 ≤ 155520) (by norm_num : 155520 ≤ 155648), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 155392 ≤ 155520) (by norm_num : 155520 ≤ 155648), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_155136_155648 :
    (∑ n ∈ Ico 155136 155648, mobiusTreeValue 16 mobiusTable1200001 n) = (8 : ℤ) ∧
    (∑ n ∈ Ico 155136 155648, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (312 : ℕ) ∧
    (∑ n ∈ Ico 155136 155648, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (257376 : ℤ) ∧
    (∑ n ∈ Ico 155136 155648, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (5147550775341791877120308558 : ℤ) := by
  rcases cdemPrefixStats_155136_155392 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_155392_155648 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 155136 ≤ 155392) (by norm_num : 155392 ≤ 155648), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 155136 ≤ 155392) (by norm_num : 155392 ≤ 155648), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 155136 ≤ 155392) (by norm_num : 155392 ≤ 155648), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 155136 ≤ 155392) (by norm_num : 155392 ≤ 155648), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_154624_155648 :
    (∑ n ∈ Ico 154624 155648, mobiusTreeValue 16 mobiusTable1200001 n) = (25 : ℤ) ∧
    (∑ n ∈ Ico 154624 155648, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (621 : ℕ) ∧
    (∑ n ∈ Ico 154624 155648, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (805616 : ℤ) ∧
    (∑ n ∈ Ico 154624 155648, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (16112654967858390587067394998 : ℤ) := by
  rcases cdemPrefixStats_154624_155136 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_155136_155648 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 154624 ≤ 155136) (by norm_num : 155136 ≤ 155648), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 154624 ≤ 155136) (by norm_num : 155136 ≤ 155648), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 154624 ≤ 155136) (by norm_num : 155136 ≤ 155648), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 154624 ≤ 155136) (by norm_num : 155136 ≤ 155648), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_153600_155648 :
    (∑ n ∈ Ico 153600 155648, mobiusTreeValue 16 mobiusTable1200001 n) = (31 : ℤ) ∧
    (∑ n ∈ Ico 153600 155648, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (1245 : ℕ) ∧
    (∑ n ∈ Ico 153600 155648, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (999241 : ℤ) ∧
    (∑ n ∈ Ico 153600 155648, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (19985263775371815147993220132 : ℤ) := by
  rcases cdemPrefixStats_153600_154624 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_154624_155648 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 153600 ≤ 154624) (by norm_num : 154624 ≤ 155648), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 153600 ≤ 154624) (by norm_num : 154624 ≤ 155648), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 153600 ≤ 154624) (by norm_num : 154624 ≤ 155648), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 153600 ≤ 154624) (by norm_num : 154624 ≤ 155648), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_151552_155648 :
    (∑ n ∈ Ico 151552 155648, mobiusTreeValue 16 mobiusTable1200001 n) = (-26 : ℤ) ∧
    (∑ n ∈ Ico 151552 155648, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (2486 : ℕ) ∧
    (∑ n ∈ Ico 151552 155648, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-874471 : ℤ) ∧
    (∑ n ∈ Ico 151552 155648, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-17489729376966159644790271834 : ℤ) := by
  rcases cdemPrefixStats_151552_153600 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_153600_155648 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 151552 ≤ 153600) (by norm_num : 153600 ≤ 155648), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 151552 ≤ 153600) (by norm_num : 153600 ≤ 155648), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 151552 ≤ 153600) (by norm_num : 153600 ≤ 155648), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 151552 ≤ 153600) (by norm_num : 153600 ≤ 155648), hR1, hR2] <;> norm_num

theorem cdemPrefixGroup037_checked_complete :
    (∑ n ∈ Ico 151552 155648, mobiusTreeValue 16 mobiusTable1200001 n) = (-26 : ℤ) ∧
    (∑ n ∈ Ico 151552 155648, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (2486 : ℕ) ∧
    (∑ n ∈ Ico 151552 155648, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-874471 : ℤ) ∧
    (∑ n ∈ Ico 151552 155648, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-17489729376966159644790271834 : ℤ) := cdemPrefixStats_151552_155648
end Helfgott
#print axioms Helfgott.cdemPrefixGroup037_checked_complete

open Helfgott Finset
open scoped BigOperators

theorem solution :
    (∑ n ∈ Ico 151552 155648, mobiusTreeValue 16 mobiusTable1200001 n) = (-26 : ℤ) ∧
    (∑ n ∈ Ico 151552 155648, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (2486 : ℕ) ∧
    (∑ n ∈ Ico 151552 155648, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-874471 : ℤ) ∧
    (∑ n ∈ Ico 151552 155648, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-17489729376966159644790271834 : ℤ) := Helfgott.cdemPrefixGroup037_checked_complete
#print axioms solution
