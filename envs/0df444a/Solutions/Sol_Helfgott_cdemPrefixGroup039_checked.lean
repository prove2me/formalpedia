-- Prove2me | solution 1 for Helfgott.cdemPrefixGroup039_checked
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-09T02:41:35.171121+00:00
-- url     : https://prove2.me/submissions/ba09407f-b570-4fae-a866-039dd8e8f5c9

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
private theorem cdemPrefixStats_159744_159808 :
    (∑ n ∈ Ico 159744 159808, mobiusTreeValue 16 mobiusTable1200001 n) = (-3 : ℤ) ∧
    (∑ n ∈ Ico 159744 159808, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 159744 159808, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-93876 : ℤ) ∧
    (∑ n ∈ Ico 159744 159808, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-1877530769282391891606381550 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_159808_159872 :
    (∑ n ∈ Ico 159808 159872, mobiusTreeValue 16 mobiusTable1200001 n) = (-6 : ℤ) ∧
    (∑ n ∈ Ico 159808 159872, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (36 : ℕ) ∧
    (∑ n ∈ Ico 159808 159872, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-187659 : ℤ) ∧
    (∑ n ∈ Ico 159808 159872, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-3753264561837581040018044380 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_159744_159872 :
    (∑ n ∈ Ico 159744 159872, mobiusTreeValue 16 mobiusTable1200001 n) = (-9 : ℤ) ∧
    (∑ n ∈ Ico 159744 159872, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (75 : ℕ) ∧
    (∑ n ∈ Ico 159744 159872, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-281535 : ℤ) ∧
    (∑ n ∈ Ico 159744 159872, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-5630795331119972931624425930 : ℤ) := by
  rcases cdemPrefixStats_159744_159808 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_159808_159872 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 159744 ≤ 159808) (by norm_num : 159808 ≤ 159872), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 159744 ≤ 159808) (by norm_num : 159808 ≤ 159872), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 159744 ≤ 159808) (by norm_num : 159808 ≤ 159872), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 159744 ≤ 159808) (by norm_num : 159808 ≤ 159872), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_159872_159936 :
    (∑ n ∈ Ico 159872 159936, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 159872 159936, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 159872 159936, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (18 : ℤ) ∧
    (∑ n ∈ Ico 159872 159936, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (363722995596562277194384 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_159936_160000 :
    (∑ n ∈ Ico 159936 160000, mobiusTreeValue 16 mobiusTable1200001 n) = (9 : ℤ) ∧
    (∑ n ∈ Ico 159936 160000, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 159936 160000, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (281281 : ℤ) ∧
    (∑ n ∈ Ico 159936 160000, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (5625718814084486983980551891 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_159872_160000 :
    (∑ n ∈ Ico 159872 160000, mobiusTreeValue 16 mobiusTable1200001 n) = (9 : ℤ) ∧
    (∑ n ∈ Ico 159872 160000, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 159872 160000, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (281299 : ℤ) ∧
    (∑ n ∈ Ico 159872 160000, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (5626082537080083546257746275 : ℤ) := by
  rcases cdemPrefixStats_159872_159936 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_159936_160000 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 159872 ≤ 159936) (by norm_num : 159936 ≤ 160000), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 159872 ≤ 159936) (by norm_num : 159936 ≤ 160000), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 159872 ≤ 159936) (by norm_num : 159936 ≤ 160000), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 159872 ≤ 159936) (by norm_num : 159936 ≤ 160000), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_159744_160000 :
    (∑ n ∈ Ico 159744 160000, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 159744 160000, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (152 : ℕ) ∧
    (∑ n ∈ Ico 159744 160000, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-236 : ℤ) ∧
    (∑ n ∈ Ico 159744 160000, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-4712794039889385366679655 : ℤ) := by
  rcases cdemPrefixStats_159744_159872 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_159872_160000 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 159744 ≤ 159872) (by norm_num : 159872 ≤ 160000), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 159744 ≤ 159872) (by norm_num : 159872 ≤ 160000), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 159744 ≤ 159872) (by norm_num : 159872 ≤ 160000), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 159744 ≤ 159872) (by norm_num : 159872 ≤ 160000), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_160000_160064 :
    (∑ n ∈ Ico 160000 160064, mobiusTreeValue 16 mobiusTable1200001 n) = (4 : ℤ) ∧
    (∑ n ∈ Ico 160000 160064, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 160000 160064, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (124958 : ℤ) ∧
    (∑ n ∈ Ico 160000 160064, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (2499211160818348959365501835 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_160064_160128 :
    (∑ n ∈ Ico 160064 160128, mobiusTreeValue 16 mobiusTable1200001 n) = (-5 : ℤ) ∧
    (∑ n ∈ Ico 160064 160128, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 160064 160128, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-156166 : ℤ) ∧
    (∑ n ∈ Ico 160064 160128, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-3123293982431256114740570566 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_160000_160128 :
    (∑ n ∈ Ico 160000 160128, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 160000 160128, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (75 : ℕ) ∧
    (∑ n ∈ Ico 160000 160128, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-31208 : ℤ) ∧
    (∑ n ∈ Ico 160000 160128, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-624082821612907155375068731 : ℤ) := by
  rcases cdemPrefixStats_160000_160064 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_160064_160128 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 160000 ≤ 160064) (by norm_num : 160064 ≤ 160128), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 160000 ≤ 160064) (by norm_num : 160064 ≤ 160128), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 160000 ≤ 160064) (by norm_num : 160064 ≤ 160128), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 160000 ≤ 160064) (by norm_num : 160064 ≤ 160128), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_160128_160192 :
    (∑ n ∈ Ico 160128 160192, mobiusTreeValue 16 mobiusTable1200001 n) = (10 : ℤ) ∧
    (∑ n ∈ Ico 160128 160192, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 160128 160192, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (312208 : ℤ) ∧
    (∑ n ∈ Ico 160128 160192, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (6244302256385145913433251687 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_160192_160256 :
    (∑ n ∈ Ico 160192 160256, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 160192 160256, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 160192 160256, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-31196 : ℤ) ∧
    (∑ n ∈ Ico 160192 160256, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-623989897564164079520856589 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_160128_160256 :
    (∑ n ∈ Ico 160128 160256, mobiusTreeValue 16 mobiusTable1200001 n) = (9 : ℤ) ∧
    (∑ n ∈ Ico 160128 160256, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 160128 160256, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (281012 : ℤ) ∧
    (∑ n ∈ Ico 160128 160256, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (5620312358820981833912395098 : ℤ) := by
  rcases cdemPrefixStats_160128_160192 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_160192_160256 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 160128 ≤ 160192) (by norm_num : 160192 ≤ 160256), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 160128 ≤ 160192) (by norm_num : 160192 ≤ 160256), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 160128 ≤ 160192) (by norm_num : 160192 ≤ 160256), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 160128 ≤ 160192) (by norm_num : 160192 ≤ 160256), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_160000_160256 :
    (∑ n ∈ Ico 160000 160256, mobiusTreeValue 16 mobiusTable1200001 n) = (8 : ℤ) ∧
    (∑ n ∈ Ico 160000 160256, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (152 : ℕ) ∧
    (∑ n ∈ Ico 160000 160256, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (249804 : ℤ) ∧
    (∑ n ∈ Ico 160000 160256, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (4996229537208074678537326367 : ℤ) := by
  rcases cdemPrefixStats_160000_160128 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_160128_160256 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 160000 ≤ 160128) (by norm_num : 160128 ≤ 160256), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 160000 ≤ 160128) (by norm_num : 160128 ≤ 160256), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 160000 ≤ 160128) (by norm_num : 160128 ≤ 160256), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 160000 ≤ 160128) (by norm_num : 160128 ≤ 160256), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_159744_160256 :
    (∑ n ∈ Ico 159744 160256, mobiusTreeValue 16 mobiusTable1200001 n) = (8 : ℤ) ∧
    (∑ n ∈ Ico 159744 160256, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (304 : ℕ) ∧
    (∑ n ∈ Ico 159744 160256, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (249568 : ℤ) ∧
    (∑ n ∈ Ico 159744 160256, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (4991516743168185293170646712 : ℤ) := by
  rcases cdemPrefixStats_159744_160000 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_160000_160256 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 159744 ≤ 160000) (by norm_num : 160000 ≤ 160256), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 159744 ≤ 160000) (by norm_num : 160000 ≤ 160256), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 159744 ≤ 160000) (by norm_num : 160000 ≤ 160256), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 159744 ≤ 160000) (by norm_num : 160000 ≤ 160256), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_160256_160320 :
    (∑ n ∈ Ico 160256 160320, mobiusTreeValue 16 mobiusTable1200001 n) = (7 : ℤ) ∧
    (∑ n ∈ Ico 160256 160320, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 160256 160320, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (218358 : ℤ) ∧
    (∑ n ∈ Ico 160256 160320, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (4367220826754430771630776883 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_160320_160384 :
    (∑ n ∈ Ico 160320 160384, mobiusTreeValue 16 mobiusTable1200001 n) = (2 : ℤ) ∧
    (∑ n ∈ Ico 160320 160384, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 160320 160384, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (62395 : ℤ) ∧
    (∑ n ∈ Ico 160320 160384, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1247921026337815855601120608 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_160256_160384 :
    (∑ n ∈ Ico 160256 160384, mobiusTreeValue 16 mobiusTable1200001 n) = (9 : ℤ) ∧
    (∑ n ∈ Ico 160256 160384, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 160256 160384, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (280753 : ℤ) ∧
    (∑ n ∈ Ico 160256 160384, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (5615141853092246627231897491 : ℤ) := by
  rcases cdemPrefixStats_160256_160320 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_160320_160384 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 160256 ≤ 160320) (by norm_num : 160320 ≤ 160384), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 160256 ≤ 160320) (by norm_num : 160320 ≤ 160384), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 160256 ≤ 160320) (by norm_num : 160320 ≤ 160384), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 160256 ≤ 160320) (by norm_num : 160320 ≤ 160384), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_160384_160448 :
    (∑ n ∈ Ico 160384 160448, mobiusTreeValue 16 mobiusTable1200001 n) = (5 : ℤ) ∧
    (∑ n ∈ Ico 160384 160448, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 160384 160448, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (155820 : ℤ) ∧
    (∑ n ∈ Ico 160384 160448, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (3116464777250024019597811524 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_160448_160512 :
    (∑ n ∈ Ico 160448 160512, mobiusTreeValue 16 mobiusTable1200001 n) = (8 : ℤ) ∧
    (∑ n ∈ Ico 160448 160512, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 160448 160512, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (249256 : ℤ) ∧
    (∑ n ∈ Ico 160448 160512, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (4985188605815682184529007910 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_160384_160512 :
    (∑ n ∈ Ico 160384 160512, mobiusTreeValue 16 mobiusTable1200001 n) = (13 : ℤ) ∧
    (∑ n ∈ Ico 160384 160512, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (79 : ℕ) ∧
    (∑ n ∈ Ico 160384 160512, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (405076 : ℤ) ∧
    (∑ n ∈ Ico 160384 160512, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (8101653383065706204126819434 : ℤ) := by
  rcases cdemPrefixStats_160384_160448 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_160448_160512 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 160384 ≤ 160448) (by norm_num : 160448 ≤ 160512), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 160384 ≤ 160448) (by norm_num : 160448 ≤ 160512), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 160384 ≤ 160448) (by norm_num : 160448 ≤ 160512), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 160384 ≤ 160448) (by norm_num : 160448 ≤ 160512), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_160256_160512 :
    (∑ n ∈ Ico 160256 160512, mobiusTreeValue 16 mobiusTable1200001 n) = (22 : ℤ) ∧
    (∑ n ∈ Ico 160256 160512, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (156 : ℕ) ∧
    (∑ n ∈ Ico 160256 160512, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (685829 : ℤ) ∧
    (∑ n ∈ Ico 160256 160512, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (13716795236157952831358716925 : ℤ) := by
  rcases cdemPrefixStats_160256_160384 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_160384_160512 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 160256 ≤ 160384) (by norm_num : 160384 ≤ 160512), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 160256 ≤ 160384) (by norm_num : 160384 ≤ 160512), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 160256 ≤ 160384) (by norm_num : 160384 ≤ 160512), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 160256 ≤ 160384) (by norm_num : 160384 ≤ 160512), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_160512_160576 :
    (∑ n ∈ Ico 160512 160576, mobiusTreeValue 16 mobiusTable1200001 n) = (2 : ℤ) ∧
    (∑ n ∈ Ico 160512 160576, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 160512 160576, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (62288 : ℤ) ∧
    (∑ n ∈ Ico 160512 160576, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1245787746525238468182333494 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_160576_160640 :
    (∑ n ∈ Ico 160576 160640, mobiusTreeValue 16 mobiusTable1200001 n) = (-10 : ℤ) ∧
    (∑ n ∈ Ico 160576 160640, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 160576 160640, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-311307 : ℤ) ∧
    (∑ n ∈ Ico 160576 160640, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-6226258600327971078043752032 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_160512_160640 :
    (∑ n ∈ Ico 160512 160640, mobiusTreeValue 16 mobiusTable1200001 n) = (-8 : ℤ) ∧
    (∑ n ∈ Ico 160512 160640, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 160512 160640, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-249019 : ℤ) ∧
    (∑ n ∈ Ico 160512 160640, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-4980470853802732609861418538 : ℤ) := by
  rcases cdemPrefixStats_160512_160576 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_160576_160640 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 160512 ≤ 160576) (by norm_num : 160576 ≤ 160640), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 160512 ≤ 160576) (by norm_num : 160576 ≤ 160640), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 160512 ≤ 160576) (by norm_num : 160576 ≤ 160640), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 160512 ≤ 160576) (by norm_num : 160576 ≤ 160640), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_160640_160704 :
    (∑ n ∈ Ico 160640 160704, mobiusTreeValue 16 mobiusTable1200001 n) = (-11 : ℤ) ∧
    (∑ n ∈ Ico 160640 160704, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 160640 160704, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-342298 : ℤ) ∧
    (∑ n ∈ Ico 160640 160704, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-6846032823367330844118768424 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_160704_160768 :
    (∑ n ∈ Ico 160704 160768, mobiusTreeValue 16 mobiusTable1200001 n) = (-3 : ℤ) ∧
    (∑ n ∈ Ico 160704 160768, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 160704 160768, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-93299 : ℤ) ∧
    (∑ n ∈ Ico 160704 160768, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-1865965510120496666528731112 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_160640_160768 :
    (∑ n ∈ Ico 160640 160768, mobiusTreeValue 16 mobiusTable1200001 n) = (-14 : ℤ) ∧
    (∑ n ∈ Ico 160640 160768, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 160640 160768, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-435597 : ℤ) ∧
    (∑ n ∈ Ico 160640 160768, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-8711998333487827510647499536 : ℤ) := by
  rcases cdemPrefixStats_160640_160704 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_160704_160768 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 160640 ≤ 160704) (by norm_num : 160704 ≤ 160768), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 160640 ≤ 160704) (by norm_num : 160704 ≤ 160768), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 160640 ≤ 160704) (by norm_num : 160704 ≤ 160768), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 160640 ≤ 160704) (by norm_num : 160704 ≤ 160768), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_160512_160768 :
    (∑ n ∈ Ico 160512 160768, mobiusTreeValue 16 mobiusTable1200001 n) = (-22 : ℤ) ∧
    (∑ n ∈ Ico 160512 160768, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (156 : ℕ) ∧
    (∑ n ∈ Ico 160512 160768, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-684616 : ℤ) ∧
    (∑ n ∈ Ico 160512 160768, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-13692469187290560120508918074 : ℤ) := by
  rcases cdemPrefixStats_160512_160640 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_160640_160768 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 160512 ≤ 160640) (by norm_num : 160640 ≤ 160768), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 160512 ≤ 160640) (by norm_num : 160640 ≤ 160768), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 160512 ≤ 160640) (by norm_num : 160640 ≤ 160768), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 160512 ≤ 160640) (by norm_num : 160640 ≤ 160768), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_160256_160768 :
    (∑ n ∈ Ico 160256 160768, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 160256 160768, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (312 : ℕ) ∧
    (∑ n ∈ Ico 160256 160768, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (1213 : ℤ) ∧
    (∑ n ∈ Ico 160256 160768, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (24326048867392710849798851 : ℤ) := by
  rcases cdemPrefixStats_160256_160512 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_160512_160768 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 160256 ≤ 160512) (by norm_num : 160512 ≤ 160768), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 160256 ≤ 160512) (by norm_num : 160512 ≤ 160768), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 160256 ≤ 160512) (by norm_num : 160512 ≤ 160768), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 160256 ≤ 160512) (by norm_num : 160512 ≤ 160768), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_159744_160768 :
    (∑ n ∈ Ico 159744 160768, mobiusTreeValue 16 mobiusTable1200001 n) = (8 : ℤ) ∧
    (∑ n ∈ Ico 159744 160768, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (616 : ℕ) ∧
    (∑ n ∈ Ico 159744 160768, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (250781 : ℤ) ∧
    (∑ n ∈ Ico 159744 160768, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (5015842792035578004020445563 : ℤ) := by
  rcases cdemPrefixStats_159744_160256 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_160256_160768 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 159744 ≤ 160256) (by norm_num : 160256 ≤ 160768), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 159744 ≤ 160256) (by norm_num : 160256 ≤ 160768), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 159744 ≤ 160256) (by norm_num : 160256 ≤ 160768), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 159744 ≤ 160256) (by norm_num : 160256 ≤ 160768), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_160768_160832 :
    (∑ n ∈ Ico 160768 160832, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 160768 160832, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 160768 160832, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-31096 : ℤ) ∧
    (∑ n ∈ Ico 160768 160832, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-621867362115571933571290235 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_160832_160896 :
    (∑ n ∈ Ico 160832 160896, mobiusTreeValue 16 mobiusTable1200001 n) = (2 : ℤ) ∧
    (∑ n ∈ Ico 160832 160896, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 160832 160896, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (62172 : ℤ) ∧
    (∑ n ∈ Ico 160832 160896, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1243471780204996706582397055 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_160768_160896 :
    (∑ n ∈ Ico 160768 160896, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 160768 160896, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 160768 160896, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (31076 : ℤ) ∧
    (∑ n ∈ Ico 160768 160896, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (621604418089424773011106820 : ℤ) := by
  rcases cdemPrefixStats_160768_160832 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_160832_160896 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 160768 ≤ 160832) (by norm_num : 160832 ≤ 160896), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 160768 ≤ 160832) (by norm_num : 160832 ≤ 160896), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 160768 ≤ 160832) (by norm_num : 160832 ≤ 160896), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 160768 ≤ 160832) (by norm_num : 160832 ≤ 160896), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_160896_160960 :
    (∑ n ∈ Ico 160896 160960, mobiusTreeValue 16 mobiusTable1200001 n) = (4 : ℤ) ∧
    (∑ n ∈ Ico 160896 160960, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 160896 160960, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (124283 : ℤ) ∧
    (∑ n ∈ Ico 160896 160960, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (2485707263360343308491767565 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_160960_161024 :
    (∑ n ∈ Ico 160960 161024, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 160960 161024, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 160960 161024, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (3 : ℤ) ∧
    (∑ n ∈ Ico 160960 161024, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (54129991551612156042675 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_160896_161024 :
    (∑ n ∈ Ico 160896 161024, mobiusTreeValue 16 mobiusTable1200001 n) = (4 : ℤ) ∧
    (∑ n ∈ Ico 160896 161024, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 160896 161024, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (124286 : ℤ) ∧
    (∑ n ∈ Ico 160896 161024, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (2485761393351894920647810240 : ℤ) := by
  rcases cdemPrefixStats_160896_160960 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_160960_161024 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 160896 ≤ 160960) (by norm_num : 160960 ≤ 161024), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 160896 ≤ 160960) (by norm_num : 160960 ≤ 161024), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 160896 ≤ 160960) (by norm_num : 160960 ≤ 161024), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 160896 ≤ 160960) (by norm_num : 160960 ≤ 161024), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_160768_161024 :
    (∑ n ∈ Ico 160768 161024, mobiusTreeValue 16 mobiusTable1200001 n) = (5 : ℤ) ∧
    (∑ n ∈ Ico 160768 161024, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (155 : ℕ) ∧
    (∑ n ∈ Ico 160768 161024, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (155362 : ℤ) ∧
    (∑ n ∈ Ico 160768 161024, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (3107365811441319693658917060 : ℤ) := by
  rcases cdemPrefixStats_160768_160896 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_160896_161024 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 160768 ≤ 160896) (by norm_num : 160896 ≤ 161024), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 160768 ≤ 160896) (by norm_num : 160896 ≤ 161024), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 160768 ≤ 160896) (by norm_num : 160896 ≤ 161024), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 160768 ≤ 160896) (by norm_num : 160896 ≤ 161024), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_161024_161088 :
    (∑ n ∈ Ico 161024 161088, mobiusTreeValue 16 mobiusTable1200001 n) = (-7 : ℤ) ∧
    (∑ n ∈ Ico 161024 161088, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 161024 161088, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-217313 : ℤ) ∧
    (∑ n ∈ Ico 161024 161088, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-4346322060151872818898448566 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_161088_161152 :
    (∑ n ∈ Ico 161088 161152, mobiusTreeValue 16 mobiusTable1200001 n) = (7 : ℤ) ∧
    (∑ n ∈ Ico 161088 161152, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 161088 161152, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (217226 : ℤ) ∧
    (∑ n ∈ Ico 161088 161152, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (4344584111599393590506427093 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_161024_161152 :
    (∑ n ∈ Ico 161024 161152, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 161024 161152, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 161024 161152, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-87 : ℤ) ∧
    (∑ n ∈ Ico 161024 161152, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-1737948552479228392021473 : ℤ) := by
  rcases cdemPrefixStats_161024_161088 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_161088_161152 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 161024 ≤ 161088) (by norm_num : 161088 ≤ 161152), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 161024 ≤ 161088) (by norm_num : 161088 ≤ 161152), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 161024 ≤ 161088) (by norm_num : 161088 ≤ 161152), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 161024 ≤ 161088) (by norm_num : 161088 ≤ 161152), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_161152_161216 :
    (∑ n ∈ Ico 161152 161216, mobiusTreeValue 16 mobiusTable1200001 n) = (8 : ℤ) ∧
    (∑ n ∈ Ico 161152 161216, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 161152 161216, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (248116 : ℤ) ∧
    (∑ n ∈ Ico 161152 161216, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (4962444293729483866661907238 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_161216_161280 :
    (∑ n ∈ Ico 161216 161280, mobiusTreeValue 16 mobiusTable1200001 n) = (-7 : ℤ) ∧
    (∑ n ∈ Ico 161216 161280, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 161216 161280, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-217055 : ℤ) ∧
    (∑ n ∈ Ico 161216 161280, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-4341162276491292991964823840 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_161152_161280 :
    (∑ n ∈ Ico 161152 161280, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 161152 161280, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 161152 161280, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (31061 : ℤ) ∧
    (∑ n ∈ Ico 161152 161280, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (621282017238190874697083398 : ℤ) := by
  rcases cdemPrefixStats_161152_161216 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_161216_161280 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 161152 ≤ 161216) (by norm_num : 161216 ≤ 161280), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 161152 ≤ 161216) (by norm_num : 161216 ≤ 161280), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 161152 ≤ 161216) (by norm_num : 161216 ≤ 161280), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 161152 ≤ 161216) (by norm_num : 161216 ≤ 161280), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_161024_161280 :
    (∑ n ∈ Ico 161024 161280, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 161024 161280, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (155 : ℕ) ∧
    (∑ n ∈ Ico 161024 161280, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (30974 : ℤ) ∧
    (∑ n ∈ Ico 161024 161280, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (619544068685711646305061925 : ℤ) := by
  rcases cdemPrefixStats_161024_161152 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_161152_161280 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 161024 ≤ 161152) (by norm_num : 161152 ≤ 161280), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 161024 ≤ 161152) (by norm_num : 161152 ≤ 161280), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 161024 ≤ 161152) (by norm_num : 161152 ≤ 161280), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 161024 ≤ 161152) (by norm_num : 161152 ≤ 161280), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_160768_161280 :
    (∑ n ∈ Ico 160768 161280, mobiusTreeValue 16 mobiusTable1200001 n) = (6 : ℤ) ∧
    (∑ n ∈ Ico 160768 161280, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (310 : ℕ) ∧
    (∑ n ∈ Ico 160768 161280, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (186336 : ℤ) ∧
    (∑ n ∈ Ico 160768 161280, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (3726909880127031339963978985 : ℤ) := by
  rcases cdemPrefixStats_160768_161024 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_161024_161280 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 160768 ≤ 161024) (by norm_num : 161024 ≤ 161280), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 160768 ≤ 161024) (by norm_num : 161024 ≤ 161280), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 160768 ≤ 161024) (by norm_num : 161024 ≤ 161280), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 160768 ≤ 161024) (by norm_num : 161024 ≤ 161280), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_161280_161344 :
    (∑ n ∈ Ico 161280 161344, mobiusTreeValue 16 mobiusTable1200001 n) = (-6 : ℤ) ∧
    (∑ n ∈ Ico 161280 161344, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 161280 161344, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-185966 : ℤ) ∧
    (∑ n ∈ Ico 161280 161344, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-3719434864974400566731021104 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_161344_161408 :
    (∑ n ∈ Ico 161344 161408, mobiusTreeValue 16 mobiusTable1200001 n) = (11 : ℤ) ∧
    (∑ n ∈ Ico 161344 161408, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 161344 161408, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (340826 : ℤ) ∧
    (∑ n ∈ Ico 161344 161408, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (6816594278685391407201009534 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_161280_161408 :
    (∑ n ∈ Ico 161280 161408, mobiusTreeValue 16 mobiusTable1200001 n) = (5 : ℤ) ∧
    (∑ n ∈ Ico 161280 161408, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 161280 161408, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (154860 : ℤ) ∧
    (∑ n ∈ Ico 161280 161408, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (3097159413710990840469988430 : ℤ) := by
  rcases cdemPrefixStats_161280_161344 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_161344_161408 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 161280 ≤ 161344) (by norm_num : 161344 ≤ 161408), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 161280 ≤ 161344) (by norm_num : 161344 ≤ 161408), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 161280 ≤ 161344) (by norm_num : 161344 ≤ 161408), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 161280 ≤ 161344) (by norm_num : 161344 ≤ 161408), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_161408_161472 :
    (∑ n ∈ Ico 161408 161472, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 161408 161472, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 161408 161472, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (30954 : ℤ) ∧
    (∑ n ∈ Ico 161408 161472, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (619064457935955539197334464 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_161472_161536 :
    (∑ n ∈ Ico 161472 161536, mobiusTreeValue 16 mobiusTable1200001 n) = (8 : ℤ) ∧
    (∑ n ∈ Ico 161472 161536, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 161472 161536, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (247700 : ℤ) ∧
    (∑ n ∈ Ico 161472 161536, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (4954074142807422635403281348 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_161408_161536 :
    (∑ n ∈ Ico 161408 161536, mobiusTreeValue 16 mobiusTable1200001 n) = (9 : ℤ) ∧
    (∑ n ∈ Ico 161408 161536, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (79 : ℕ) ∧
    (∑ n ∈ Ico 161408 161536, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (278654 : ℤ) ∧
    (∑ n ∈ Ico 161408 161536, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (5573138600743378174600615812 : ℤ) := by
  rcases cdemPrefixStats_161408_161472 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_161472_161536 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 161408 ≤ 161472) (by norm_num : 161472 ≤ 161536), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 161408 ≤ 161472) (by norm_num : 161472 ≤ 161536), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 161408 ≤ 161472) (by norm_num : 161472 ≤ 161536), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 161408 ≤ 161472) (by norm_num : 161472 ≤ 161536), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_161280_161536 :
    (∑ n ∈ Ico 161280 161536, mobiusTreeValue 16 mobiusTable1200001 n) = (14 : ℤ) ∧
    (∑ n ∈ Ico 161280 161536, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (156 : ℕ) ∧
    (∑ n ∈ Ico 161280 161536, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (433514 : ℤ) ∧
    (∑ n ∈ Ico 161280 161536, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (8670298014454369015070604242 : ℤ) := by
  rcases cdemPrefixStats_161280_161408 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_161408_161536 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 161280 ≤ 161408) (by norm_num : 161408 ≤ 161536), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 161280 ≤ 161408) (by norm_num : 161408 ≤ 161536), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 161280 ≤ 161408) (by norm_num : 161408 ≤ 161536), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 161280 ≤ 161408) (by norm_num : 161408 ≤ 161536), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_161536_161600 :
    (∑ n ∈ Ico 161536 161600, mobiusTreeValue 16 mobiusTable1200001 n) = (-2 : ℤ) ∧
    (∑ n ∈ Ico 161536 161600, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 161536 161600, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-61882 : ℤ) ∧
    (∑ n ∈ Ico 161536 161600, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-1237642879411984289830765530 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_161600_161664 :
    (∑ n ∈ Ico 161600 161664, mobiusTreeValue 16 mobiusTable1200001 n) = (5 : ℤ) ∧
    (∑ n ∈ Ico 161600 161664, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 161600 161664, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (154665 : ℤ) ∧
    (∑ n ∈ Ico 161600 161664, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (3093389522607988442582909360 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_161536_161664 :
    (∑ n ∈ Ico 161536 161664, mobiusTreeValue 16 mobiusTable1200001 n) = (3 : ℤ) ∧
    (∑ n ∈ Ico 161536 161664, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 161536 161664, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (92783 : ℤ) ∧
    (∑ n ∈ Ico 161536 161664, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1855746643196004152752143830 : ℤ) := by
  rcases cdemPrefixStats_161536_161600 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_161600_161664 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 161536 ≤ 161600) (by norm_num : 161600 ≤ 161664), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 161536 ≤ 161600) (by norm_num : 161600 ≤ 161664), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 161536 ≤ 161600) (by norm_num : 161600 ≤ 161664), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 161536 ≤ 161600) (by norm_num : 161600 ≤ 161664), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_161664_161728 :
    (∑ n ∈ Ico 161664 161728, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 161664 161728, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 161664 161728, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-30914 : ℤ) ∧
    (∑ n ∈ Ico 161664 161728, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-618253223764326128483289508 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_161728_161792 :
    (∑ n ∈ Ico 161728 161792, mobiusTreeValue 16 mobiusTable1200001 n) = (-9 : ℤ) ∧
    (∑ n ∈ Ico 161728 161792, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 161728 161792, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-278180 : ℤ) ∧
    (∑ n ∈ Ico 161728 161792, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-5563706610484714433008306592 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_161664_161792 :
    (∑ n ∈ Ico 161664 161792, mobiusTreeValue 16 mobiusTable1200001 n) = (-10 : ℤ) ∧
    (∑ n ∈ Ico 161664 161792, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (80 : ℕ) ∧
    (∑ n ∈ Ico 161664 161792, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-309094 : ℤ) ∧
    (∑ n ∈ Ico 161664 161792, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-6181959834249040561491596100 : ℤ) := by
  rcases cdemPrefixStats_161664_161728 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_161728_161792 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 161664 ≤ 161728) (by norm_num : 161728 ≤ 161792), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 161664 ≤ 161728) (by norm_num : 161728 ≤ 161792), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 161664 ≤ 161728) (by norm_num : 161728 ≤ 161792), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 161664 ≤ 161728) (by norm_num : 161728 ≤ 161792), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_161536_161792 :
    (∑ n ∈ Ico 161536 161792, mobiusTreeValue 16 mobiusTable1200001 n) = (-7 : ℤ) ∧
    (∑ n ∈ Ico 161536 161792, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (157 : ℕ) ∧
    (∑ n ∈ Ico 161536 161792, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-216311 : ℤ) ∧
    (∑ n ∈ Ico 161536 161792, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-4326213191053036408739452270 : ℤ) := by
  rcases cdemPrefixStats_161536_161664 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_161664_161792 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 161536 ≤ 161664) (by norm_num : 161664 ≤ 161792), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 161536 ≤ 161664) (by norm_num : 161664 ≤ 161792), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 161536 ≤ 161664) (by norm_num : 161664 ≤ 161792), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 161536 ≤ 161664) (by norm_num : 161664 ≤ 161792), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_161280_161792 :
    (∑ n ∈ Ico 161280 161792, mobiusTreeValue 16 mobiusTable1200001 n) = (7 : ℤ) ∧
    (∑ n ∈ Ico 161280 161792, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (313 : ℕ) ∧
    (∑ n ∈ Ico 161280 161792, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (217203 : ℤ) ∧
    (∑ n ∈ Ico 161280 161792, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (4344084823401332606331151972 : ℤ) := by
  rcases cdemPrefixStats_161280_161536 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_161536_161792 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 161280 ≤ 161536) (by norm_num : 161536 ≤ 161792), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 161280 ≤ 161536) (by norm_num : 161536 ≤ 161792), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 161280 ≤ 161536) (by norm_num : 161536 ≤ 161792), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 161280 ≤ 161536) (by norm_num : 161536 ≤ 161792), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_160768_161792 :
    (∑ n ∈ Ico 160768 161792, mobiusTreeValue 16 mobiusTable1200001 n) = (13 : ℤ) ∧
    (∑ n ∈ Ico 160768 161792, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (623 : ℕ) ∧
    (∑ n ∈ Ico 160768 161792, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (403539 : ℤ) ∧
    (∑ n ∈ Ico 160768 161792, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (8070994703528363946295130957 : ℤ) := by
  rcases cdemPrefixStats_160768_161280 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_161280_161792 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 160768 ≤ 161280) (by norm_num : 161280 ≤ 161792), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 160768 ≤ 161280) (by norm_num : 161280 ≤ 161792), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 160768 ≤ 161280) (by norm_num : 161280 ≤ 161792), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 160768 ≤ 161280) (by norm_num : 161280 ≤ 161792), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_159744_161792 :
    (∑ n ∈ Ico 159744 161792, mobiusTreeValue 16 mobiusTable1200001 n) = (21 : ℤ) ∧
    (∑ n ∈ Ico 159744 161792, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (1239 : ℕ) ∧
    (∑ n ∈ Ico 159744 161792, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (654320 : ℤ) ∧
    (∑ n ∈ Ico 159744 161792, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (13086837495563941950315576520 : ℤ) := by
  rcases cdemPrefixStats_159744_160768 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_160768_161792 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 159744 ≤ 160768) (by norm_num : 160768 ≤ 161792), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 159744 ≤ 160768) (by norm_num : 160768 ≤ 161792), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 159744 ≤ 160768) (by norm_num : 160768 ≤ 161792), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 159744 ≤ 160768) (by norm_num : 160768 ≤ 161792), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_161792_161856 :
    (∑ n ∈ Ico 161792 161856, mobiusTreeValue 16 mobiusTable1200001 n) = (9 : ℤ) ∧
    (∑ n ∈ Ico 161792 161856, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 161792 161856, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (278079 : ℤ) ∧
    (∑ n ∈ Ico 161792 161856, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (5561708643358322364089188668 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_161856_161920 :
    (∑ n ∈ Ico 161856 161920, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 161856 161920, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 161856 161920, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-30869 : ℤ) ∧
    (∑ n ∈ Ico 161856 161920, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-617447731153193560580971163 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_161792_161920 :
    (∑ n ∈ Ico 161792 161920, mobiusTreeValue 16 mobiusTable1200001 n) = (8 : ℤ) ∧
    (∑ n ∈ Ico 161792 161920, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 161792 161920, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (247210 : ℤ) ∧
    (∑ n ∈ Ico 161792 161920, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (4944260912205128803508217505 : ℤ) := by
  rcases cdemPrefixStats_161792_161856 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_161856_161920 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 161792 ≤ 161856) (by norm_num : 161856 ≤ 161920), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 161792 ≤ 161856) (by norm_num : 161856 ≤ 161920), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 161792 ≤ 161856) (by norm_num : 161856 ≤ 161920), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 161792 ≤ 161856) (by norm_num : 161856 ≤ 161920), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_161920_161984 :
    (∑ n ∈ Ico 161920 161984, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 161920 161984, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 161920 161984, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-30860 : ℤ) ∧
    (∑ n ∈ Ico 161920 161984, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-617192402263273957238153578 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_161984_162048 :
    (∑ n ∈ Ico 161984 162048, mobiusTreeValue 16 mobiusTable1200001 n) = (5 : ℤ) ∧
    (∑ n ∈ Ico 161984 162048, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 161984 162048, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (154262 : ℤ) ∧
    (∑ n ∈ Ico 161984 162048, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (3085265492965389519181533368 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_161920_162048 :
    (∑ n ∈ Ico 161920 162048, mobiusTreeValue 16 mobiusTable1200001 n) = (4 : ℤ) ∧
    (∑ n ∈ Ico 161920 162048, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 161920 162048, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (123402 : ℤ) ∧
    (∑ n ∈ Ico 161920 162048, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (2468073090702115561943379790 : ℤ) := by
  rcases cdemPrefixStats_161920_161984 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_161984_162048 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 161920 ≤ 161984) (by norm_num : 161984 ≤ 162048), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 161920 ≤ 161984) (by norm_num : 161984 ≤ 162048), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 161920 ≤ 161984) (by norm_num : 161984 ≤ 162048), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 161920 ≤ 161984) (by norm_num : 161984 ≤ 162048), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_161792_162048 :
    (∑ n ∈ Ico 161792 162048, mobiusTreeValue 16 mobiusTable1200001 n) = (12 : ℤ) ∧
    (∑ n ∈ Ico 161792 162048, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (156 : ℕ) ∧
    (∑ n ∈ Ico 161792 162048, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (370612 : ℤ) ∧
    (∑ n ∈ Ico 161792 162048, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (7412334002907244365451597295 : ℤ) := by
  rcases cdemPrefixStats_161792_161920 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_161920_162048 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 161792 ≤ 161920) (by norm_num : 161920 ≤ 162048), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 161792 ≤ 161920) (by norm_num : 161920 ≤ 162048), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 161792 ≤ 161920) (by norm_num : 161920 ≤ 162048), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 161792 ≤ 161920) (by norm_num : 161920 ≤ 162048), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_162048_162112 :
    (∑ n ∈ Ico 162048 162112, mobiusTreeValue 16 mobiusTable1200001 n) = (3 : ℤ) ∧
    (∑ n ∈ Ico 162048 162112, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 162048 162112, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (92548 : ℤ) ∧
    (∑ n ∈ Ico 162048 162112, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1851021566373053974052362329 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_162112_162176 :
    (∑ n ∈ Ico 162112 162176, mobiusTreeValue 16 mobiusTable1200001 n) = (19 : ℤ) ∧
    (∑ n ∈ Ico 162112 162176, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 162112 162176, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (585888 : ℤ) ∧
    (∑ n ∈ Ico 162112 162176, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (11717895498104346663678942943 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_162048_162176 :
    (∑ n ∈ Ico 162048 162176, mobiusTreeValue 16 mobiusTable1200001 n) = (22 : ℤ) ∧
    (∑ n ∈ Ico 162048 162176, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (76 : ℕ) ∧
    (∑ n ∈ Ico 162048 162176, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (678436 : ℤ) ∧
    (∑ n ∈ Ico 162048 162176, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (13568917064477400637731305272 : ℤ) := by
  rcases cdemPrefixStats_162048_162112 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_162112_162176 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 162048 ≤ 162112) (by norm_num : 162112 ≤ 162176), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 162048 ≤ 162112) (by norm_num : 162112 ≤ 162176), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 162048 ≤ 162112) (by norm_num : 162112 ≤ 162176), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 162048 ≤ 162112) (by norm_num : 162112 ≤ 162176), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_162176_162240 :
    (∑ n ∈ Ico 162176 162240, mobiusTreeValue 16 mobiusTable1200001 n) = (7 : ℤ) ∧
    (∑ n ∈ Ico 162176 162240, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 162176 162240, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (215792 : ℤ) ∧
    (∑ n ∈ Ico 162176 162240, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (4315902899463496591502818118 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_162240_162304 :
    (∑ n ∈ Ico 162240 162304, mobiusTreeValue 16 mobiusTable1200001 n) = (-6 : ℤ) ∧
    (∑ n ∈ Ico 162240 162304, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 162240 162304, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-184861 : ℤ) ∧
    (∑ n ∈ Ico 162240 162304, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-3697233544332595982472664735 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_162176_162304 :
    (∑ n ∈ Ico 162176 162304, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 162176 162304, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (81 : ℕ) ∧
    (∑ n ∈ Ico 162176 162304, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (30931 : ℤ) ∧
    (∑ n ∈ Ico 162176 162304, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (618669355130900609030153383 : ℤ) := by
  rcases cdemPrefixStats_162176_162240 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_162240_162304 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 162176 ≤ 162240) (by norm_num : 162240 ≤ 162304), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 162176 ≤ 162240) (by norm_num : 162240 ≤ 162304), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 162176 ≤ 162240) (by norm_num : 162240 ≤ 162304), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 162176 ≤ 162240) (by norm_num : 162240 ≤ 162304), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_162048_162304 :
    (∑ n ∈ Ico 162048 162304, mobiusTreeValue 16 mobiusTable1200001 n) = (23 : ℤ) ∧
    (∑ n ∈ Ico 162048 162304, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (157 : ℕ) ∧
    (∑ n ∈ Ico 162048 162304, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (709367 : ℤ) ∧
    (∑ n ∈ Ico 162048 162304, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (14187586419608301246761458655 : ℤ) := by
  rcases cdemPrefixStats_162048_162176 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_162176_162304 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 162048 ≤ 162176) (by norm_num : 162176 ≤ 162304), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 162048 ≤ 162176) (by norm_num : 162176 ≤ 162304), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 162048 ≤ 162176) (by norm_num : 162176 ≤ 162304), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 162048 ≤ 162176) (by norm_num : 162176 ≤ 162304), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_161792_162304 :
    (∑ n ∈ Ico 161792 162304, mobiusTreeValue 16 mobiusTable1200001 n) = (35 : ℤ) ∧
    (∑ n ∈ Ico 161792 162304, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (313 : ℕ) ∧
    (∑ n ∈ Ico 161792 162304, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (1079979 : ℤ) ∧
    (∑ n ∈ Ico 161792 162304, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (21599920422515545612213055950 : ℤ) := by
  rcases cdemPrefixStats_161792_162048 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_162048_162304 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 161792 ≤ 162048) (by norm_num : 162048 ≤ 162304), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 161792 ≤ 162048) (by norm_num : 162048 ≤ 162304), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 161792 ≤ 162048) (by norm_num : 162048 ≤ 162304), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 161792 ≤ 162048) (by norm_num : 162048 ≤ 162304), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_162304_162368 :
    (∑ n ∈ Ico 162304 162368, mobiusTreeValue 16 mobiusTable1200001 n) = (9 : ℤ) ∧
    (∑ n ∈ Ico 162304 162368, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 162304 162368, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (277214 : ℤ) ∧
    (∑ n ∈ Ico 162304 162368, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (5544330075903149779762388429 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_162368_162432 :
    (∑ n ∈ Ico 162368 162432, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 162368 162432, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (35 : ℕ) ∧
    (∑ n ∈ Ico 162368 162432, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (30804 : ℤ) ∧
    (∑ n ∈ Ico 162368 162432, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (616066864827107389984887185 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_162304_162432 :
    (∑ n ∈ Ico 162304 162432, mobiusTreeValue 16 mobiusTable1200001 n) = (10 : ℤ) ∧
    (∑ n ∈ Ico 162304 162432, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (74 : ℕ) ∧
    (∑ n ∈ Ico 162304 162432, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (308018 : ℤ) ∧
    (∑ n ∈ Ico 162304 162432, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (6160396940730257169747275614 : ℤ) := by
  rcases cdemPrefixStats_162304_162368 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_162368_162432 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 162304 ≤ 162368) (by norm_num : 162368 ≤ 162432), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 162304 ≤ 162368) (by norm_num : 162368 ≤ 162432), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 162304 ≤ 162368) (by norm_num : 162368 ≤ 162432), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 162304 ≤ 162368) (by norm_num : 162368 ≤ 162432), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_162432_162496 :
    (∑ n ∈ Ico 162432 162496, mobiusTreeValue 16 mobiusTable1200001 n) = (-6 : ℤ) ∧
    (∑ n ∈ Ico 162432 162496, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 162432 162496, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-184637 : ℤ) ∧
    (∑ n ∈ Ico 162432 162496, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-3692875878810935366127989861 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_162496_162560 :
    (∑ n ∈ Ico 162496 162560, mobiusTreeValue 16 mobiusTable1200001 n) = (-5 : ℤ) ∧
    (∑ n ∈ Ico 162496 162560, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 162496 162560, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-153816 : ℤ) ∧
    (∑ n ∈ Ico 162496 162560, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-3076370311809063709936398995 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_162432_162560 :
    (∑ n ∈ Ico 162432 162560, mobiusTreeValue 16 mobiusTable1200001 n) = (-11 : ℤ) ∧
    (∑ n ∈ Ico 162432 162560, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (79 : ℕ) ∧
    (∑ n ∈ Ico 162432 162560, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-338453 : ℤ) ∧
    (∑ n ∈ Ico 162432 162560, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-6769246190619999076064388856 : ℤ) := by
  rcases cdemPrefixStats_162432_162496 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_162496_162560 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 162432 ≤ 162496) (by norm_num : 162496 ≤ 162560), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 162432 ≤ 162496) (by norm_num : 162496 ≤ 162560), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 162432 ≤ 162496) (by norm_num : 162496 ≤ 162560), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 162432 ≤ 162496) (by norm_num : 162496 ≤ 162560), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_162304_162560 :
    (∑ n ∈ Ico 162304 162560, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 162304 162560, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (153 : ℕ) ∧
    (∑ n ∈ Ico 162304 162560, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-30435 : ℤ) ∧
    (∑ n ∈ Ico 162304 162560, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-608849249889741906317113242 : ℤ) := by
  rcases cdemPrefixStats_162304_162432 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_162432_162560 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 162304 ≤ 162432) (by norm_num : 162432 ≤ 162560), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 162304 ≤ 162432) (by norm_num : 162432 ≤ 162560), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 162304 ≤ 162432) (by norm_num : 162432 ≤ 162560), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 162304 ≤ 162432) (by norm_num : 162432 ≤ 162560), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_162560_162624 :
    (∑ n ∈ Ico 162560 162624, mobiusTreeValue 16 mobiusTable1200001 n) = (2 : ℤ) ∧
    (∑ n ∈ Ico 162560 162624, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 162560 162624, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (61515 : ℤ) ∧
    (∑ n ∈ Ico 162560 162624, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1230371625928166879639202742 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_162624_162688 :
    (∑ n ∈ Ico 162624 162688, mobiusTreeValue 16 mobiusTable1200001 n) = (-8 : ℤ) ∧
    (∑ n ∈ Ico 162624 162688, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 162624 162688, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-245922 : ℤ) ∧
    (∑ n ∈ Ico 162624 162688, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-4918525454141476314341186599 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_162560_162688 :
    (∑ n ∈ Ico 162560 162688, mobiusTreeValue 16 mobiusTable1200001 n) = (-6 : ℤ) ∧
    (∑ n ∈ Ico 162560 162688, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (80 : ℕ) ∧
    (∑ n ∈ Ico 162560 162688, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-184407 : ℤ) ∧
    (∑ n ∈ Ico 162560 162688, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-3688153828213309434701983857 : ℤ) := by
  rcases cdemPrefixStats_162560_162624 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_162624_162688 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 162560 ≤ 162624) (by norm_num : 162624 ≤ 162688), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 162560 ≤ 162624) (by norm_num : 162624 ≤ 162688), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 162560 ≤ 162624) (by norm_num : 162624 ≤ 162688), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 162560 ≤ 162624) (by norm_num : 162624 ≤ 162688), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_162688_162752 :
    (∑ n ∈ Ico 162688 162752, mobiusTreeValue 16 mobiusTable1200001 n) = (-4 : ℤ) ∧
    (∑ n ∈ Ico 162688 162752, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 162688 162752, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-122910 : ℤ) ∧
    (∑ n ∈ Ico 162688 162752, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-2458221794483227273287566198 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_162752_162816 :
    (∑ n ∈ Ico 162752 162816, mobiusTreeValue 16 mobiusTable1200001 n) = (-4 : ℤ) ∧
    (∑ n ∈ Ico 162752 162816, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 162752 162816, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-122878 : ℤ) ∧
    (∑ n ∈ Ico 162752 162816, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-2457625123440008257122477977 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_162688_162816 :
    (∑ n ∈ Ico 162688 162816, mobiusTreeValue 16 mobiusTable1200001 n) = (-8 : ℤ) ∧
    (∑ n ∈ Ico 162688 162816, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 162688 162816, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-245788 : ℤ) ∧
    (∑ n ∈ Ico 162688 162816, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-4915846917923235530410044175 : ℤ) := by
  rcases cdemPrefixStats_162688_162752 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_162752_162816 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 162688 ≤ 162752) (by norm_num : 162752 ≤ 162816), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 162688 ≤ 162752) (by norm_num : 162752 ≤ 162816), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 162688 ≤ 162752) (by norm_num : 162752 ≤ 162816), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 162688 ≤ 162752) (by norm_num : 162752 ≤ 162816), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_162560_162816 :
    (∑ n ∈ Ico 162560 162816, mobiusTreeValue 16 mobiusTable1200001 n) = (-14 : ℤ) ∧
    (∑ n ∈ Ico 162560 162816, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (158 : ℕ) ∧
    (∑ n ∈ Ico 162560 162816, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-430195 : ℤ) ∧
    (∑ n ∈ Ico 162560 162816, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-8604000746136544965112028032 : ℤ) := by
  rcases cdemPrefixStats_162560_162688 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_162688_162816 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 162560 ≤ 162688) (by norm_num : 162688 ≤ 162816), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 162560 ≤ 162688) (by norm_num : 162688 ≤ 162816), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 162560 ≤ 162688) (by norm_num : 162688 ≤ 162816), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 162560 ≤ 162688) (by norm_num : 162688 ≤ 162816), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_162304_162816 :
    (∑ n ∈ Ico 162304 162816, mobiusTreeValue 16 mobiusTable1200001 n) = (-15 : ℤ) ∧
    (∑ n ∈ Ico 162304 162816, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (311 : ℕ) ∧
    (∑ n ∈ Ico 162304 162816, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-460630 : ℤ) ∧
    (∑ n ∈ Ico 162304 162816, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-9212849996026286871429141274 : ℤ) := by
  rcases cdemPrefixStats_162304_162560 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_162560_162816 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 162304 ≤ 162560) (by norm_num : 162560 ≤ 162816), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 162304 ≤ 162560) (by norm_num : 162560 ≤ 162816), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 162304 ≤ 162560) (by norm_num : 162560 ≤ 162816), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 162304 ≤ 162560) (by norm_num : 162560 ≤ 162816), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_161792_162816 :
    (∑ n ∈ Ico 161792 162816, mobiusTreeValue 16 mobiusTable1200001 n) = (20 : ℤ) ∧
    (∑ n ∈ Ico 161792 162816, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (624 : ℕ) ∧
    (∑ n ∈ Ico 161792 162816, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (619349 : ℤ) ∧
    (∑ n ∈ Ico 161792 162816, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (12387070426489258740783914676 : ℤ) := by
  rcases cdemPrefixStats_161792_162304 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_162304_162816 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 161792 ≤ 162304) (by norm_num : 162304 ≤ 162816), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 161792 ≤ 162304) (by norm_num : 162304 ≤ 162816), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 161792 ≤ 162304) (by norm_num : 162304 ≤ 162816), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 161792 ≤ 162304) (by norm_num : 162304 ≤ 162816), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_162816_162880 :
    (∑ n ∈ Ico 162816 162880, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 162816 162880, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 162816 162880, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-30716 : ℤ) ∧
    (∑ n ∈ Ico 162816 162880, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-614348522919364264030310869 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_162880_162944 :
    (∑ n ∈ Ico 162880 162944, mobiusTreeValue 16 mobiusTable1200001 n) = (-4 : ℤ) ∧
    (∑ n ∈ Ico 162880 162944, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 162880 162944, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-122803 : ℤ) ∧
    (∑ n ∈ Ico 162880 162944, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-2456093261351458937939186779 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_162816_162944 :
    (∑ n ∈ Ico 162816 162944, mobiusTreeValue 16 mobiusTable1200001 n) = (-5 : ℤ) ∧
    (∑ n ∈ Ico 162816 162944, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 162816 162944, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-153519 : ℤ) ∧
    (∑ n ∈ Ico 162816 162944, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-3070441784270823201969497648 : ℤ) := by
  rcases cdemPrefixStats_162816_162880 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_162880_162944 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 162816 ≤ 162880) (by norm_num : 162880 ≤ 162944), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 162816 ≤ 162880) (by norm_num : 162880 ≤ 162944), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 162816 ≤ 162880) (by norm_num : 162880 ≤ 162944), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 162816 ≤ 162880) (by norm_num : 162880 ≤ 162944), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_162944_163008 :
    (∑ n ∈ Ico 162944 163008, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 162944 163008, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 162944 163008, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (30 : ℤ) ∧
    (∑ n ∈ Ico 162944 163008, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (542133766072217526602346 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_163008_163072 :
    (∑ n ∈ Ico 163008 163072, mobiusTreeValue 16 mobiusTable1200001 n) = (12 : ℤ) ∧
    (∑ n ∈ Ico 163008 163072, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 163008 163072, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (367960 : ℤ) ∧
    (∑ n ∈ Ico 163008 163072, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (7359280556411602173272517396 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_162944_163072 :
    (∑ n ∈ Ico 162944 163072, mobiusTreeValue 16 mobiusTable1200001 n) = (12 : ℤ) ∧
    (∑ n ∈ Ico 162944 163072, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (76 : ℕ) ∧
    (∑ n ∈ Ico 162944 163072, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (367990 : ℤ) ∧
    (∑ n ∈ Ico 162944 163072, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (7359822690177674390799119742 : ℤ) := by
  rcases cdemPrefixStats_162944_163008 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_163008_163072 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 162944 ≤ 163008) (by norm_num : 163008 ≤ 163072), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 162944 ≤ 163008) (by norm_num : 163008 ≤ 163072), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 162944 ≤ 163008) (by norm_num : 163008 ≤ 163072), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 162944 ≤ 163008) (by norm_num : 163008 ≤ 163072), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_162816_163072 :
    (∑ n ∈ Ico 162816 163072, mobiusTreeValue 16 mobiusTable1200001 n) = (7 : ℤ) ∧
    (∑ n ∈ Ico 162816 163072, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (153 : ℕ) ∧
    (∑ n ∈ Ico 162816 163072, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (214471 : ℤ) ∧
    (∑ n ∈ Ico 162816 163072, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (4289380905906851188829622094 : ℤ) := by
  rcases cdemPrefixStats_162816_162944 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_162944_163072 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 162816 ≤ 162944) (by norm_num : 162944 ≤ 163072), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 162816 ≤ 162944) (by norm_num : 162944 ≤ 163072), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 162816 ≤ 162944) (by norm_num : 162944 ≤ 163072), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 162816 ≤ 162944) (by norm_num : 162944 ≤ 163072), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_163072_163136 :
    (∑ n ∈ Ico 163072 163136, mobiusTreeValue 16 mobiusTable1200001 n) = (16 : ℤ) ∧
    (∑ n ∈ Ico 163072 163136, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 163072 163136, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (490448 : ℤ) ∧
    (∑ n ∈ Ico 163072 163136, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (9809128187081508062247381100 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_163136_163200 :
    (∑ n ∈ Ico 163136 163200, mobiusTreeValue 16 mobiusTable1200001 n) = (-8 : ℤ) ∧
    (∑ n ∈ Ico 163136 163200, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 163136 163200, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-245109 : ℤ) ∧
    (∑ n ∈ Ico 163136 163200, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-4902219801607907542953387354 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_163072_163200 :
    (∑ n ∈ Ico 163072 163200, mobiusTreeValue 16 mobiusTable1200001 n) = (8 : ℤ) ∧
    (∑ n ∈ Ico 163072 163200, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (80 : ℕ) ∧
    (∑ n ∈ Ico 163072 163200, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (245339 : ℤ) ∧
    (∑ n ∈ Ico 163072 163200, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (4906908385473600519293993746 : ℤ) := by
  rcases cdemPrefixStats_163072_163136 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_163136_163200 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 163072 ≤ 163136) (by norm_num : 163136 ≤ 163200), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 163072 ≤ 163136) (by norm_num : 163136 ≤ 163200), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 163072 ≤ 163136) (by norm_num : 163136 ≤ 163200), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 163072 ≤ 163136) (by norm_num : 163136 ≤ 163200), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_163200_163264 :
    (∑ n ∈ Ico 163200 163264, mobiusTreeValue 16 mobiusTable1200001 n) = (4 : ℤ) ∧
    (∑ n ∈ Ico 163200 163264, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 163200 163264, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (122527 : ℤ) ∧
    (∑ n ∈ Ico 163200 163264, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (2450537468045150764726957388 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_163264_163328 :
    (∑ n ∈ Ico 163264 163328, mobiusTreeValue 16 mobiusTable1200001 n) = (6 : ℤ) ∧
    (∑ n ∈ Ico 163264 163328, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 163264 163328, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (183746 : ℤ) ∧
    (∑ n ∈ Ico 163264 163328, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (3674946742358532200477626826 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_163200_163328 :
    (∑ n ∈ Ico 163200 163328, mobiusTreeValue 16 mobiusTable1200001 n) = (10 : ℤ) ∧
    (∑ n ∈ Ico 163200 163328, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (76 : ℕ) ∧
    (∑ n ∈ Ico 163200 163328, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (306273 : ℤ) ∧
    (∑ n ∈ Ico 163200 163328, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (6125484210403682965204584214 : ℤ) := by
  rcases cdemPrefixStats_163200_163264 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_163264_163328 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 163200 ≤ 163264) (by norm_num : 163264 ≤ 163328), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 163200 ≤ 163264) (by norm_num : 163264 ≤ 163328), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 163200 ≤ 163264) (by norm_num : 163264 ≤ 163328), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 163200 ≤ 163264) (by norm_num : 163264 ≤ 163328), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_163072_163328 :
    (∑ n ∈ Ico 163072 163328, mobiusTreeValue 16 mobiusTable1200001 n) = (18 : ℤ) ∧
    (∑ n ∈ Ico 163072 163328, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (156 : ℕ) ∧
    (∑ n ∈ Ico 163072 163328, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (551612 : ℤ) ∧
    (∑ n ∈ Ico 163072 163328, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (11032392595877283484498577960 : ℤ) := by
  rcases cdemPrefixStats_163072_163200 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_163200_163328 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 163072 ≤ 163200) (by norm_num : 163200 ≤ 163328), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 163072 ≤ 163200) (by norm_num : 163200 ≤ 163328), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 163072 ≤ 163200) (by norm_num : 163200 ≤ 163328), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 163072 ≤ 163200) (by norm_num : 163200 ≤ 163328), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_162816_163328 :
    (∑ n ∈ Ico 162816 163328, mobiusTreeValue 16 mobiusTable1200001 n) = (25 : ℤ) ∧
    (∑ n ∈ Ico 162816 163328, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (309 : ℕ) ∧
    (∑ n ∈ Ico 162816 163328, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (766083 : ℤ) ∧
    (∑ n ∈ Ico 162816 163328, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (15321773501784134673328200054 : ℤ) := by
  rcases cdemPrefixStats_162816_163072 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_163072_163328 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 162816 ≤ 163072) (by norm_num : 163072 ≤ 163328), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 162816 ≤ 163072) (by norm_num : 163072 ≤ 163328), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 162816 ≤ 163072) (by norm_num : 163072 ≤ 163328), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 162816 ≤ 163072) (by norm_num : 163072 ≤ 163328), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_163328_163392 :
    (∑ n ∈ Ico 163328 163392, mobiusTreeValue 16 mobiusTable1200001 n) = (6 : ℤ) ∧
    (∑ n ∈ Ico 163328 163392, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 163328 163392, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (183669 : ℤ) ∧
    (∑ n ∈ Ico 163328 163392, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (3673394365413294697487449194 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_163392_163456 :
    (∑ n ∈ Ico 163392 163456, mobiusTreeValue 16 mobiusTable1200001 n) = (3 : ℤ) ∧
    (∑ n ∈ Ico 163392 163456, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 163392 163456, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (91783 : ℤ) ∧
    (∑ n ∈ Ico 163392 163456, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1835674621242505776337111410 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_163328_163456 :
    (∑ n ∈ Ico 163328 163456, mobiusTreeValue 16 mobiusTable1200001 n) = (9 : ℤ) ∧
    (∑ n ∈ Ico 163328 163456, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (79 : ℕ) ∧
    (∑ n ∈ Ico 163328 163456, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (275452 : ℤ) ∧
    (∑ n ∈ Ico 163328 163456, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (5509068986655800473824560604 : ℤ) := by
  rcases cdemPrefixStats_163328_163392 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_163392_163456 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 163328 ≤ 163392) (by norm_num : 163392 ≤ 163456), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 163328 ≤ 163392) (by norm_num : 163392 ≤ 163456), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 163328 ≤ 163392) (by norm_num : 163392 ≤ 163456), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 163328 ≤ 163392) (by norm_num : 163392 ≤ 163456), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_163456_163520 :
    (∑ n ∈ Ico 163456 163520, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 163456 163520, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 163456 163520, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-20 : ℤ) ∧
    (∑ n ∈ Ico 163456 163520, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-355379178610256798753374 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_163520_163584 :
    (∑ n ∈ Ico 163520 163584, mobiusTreeValue 16 mobiusTable1200001 n) = (7 : ℤ) ∧
    (∑ n ∈ Ico 163520 163584, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 163520 163584, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (214011 : ℤ) ∧
    (∑ n ∈ Ico 163520 163584, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (4280298469860463949296825686 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_163456_163584 :
    (∑ n ∈ Ico 163456 163584, mobiusTreeValue 16 mobiusTable1200001 n) = (7 : ℤ) ∧
    (∑ n ∈ Ico 163456 163584, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (75 : ℕ) ∧
    (∑ n ∈ Ico 163456 163584, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (213991 : ℤ) ∧
    (∑ n ∈ Ico 163456 163584, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (4279943090681853692498072312 : ℤ) := by
  rcases cdemPrefixStats_163456_163520 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_163520_163584 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 163456 ≤ 163520) (by norm_num : 163520 ≤ 163584), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 163456 ≤ 163520) (by norm_num : 163520 ≤ 163584), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 163456 ≤ 163520) (by norm_num : 163520 ≤ 163584), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 163456 ≤ 163520) (by norm_num : 163520 ≤ 163584), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_163328_163584 :
    (∑ n ∈ Ico 163328 163584, mobiusTreeValue 16 mobiusTable1200001 n) = (16 : ℤ) ∧
    (∑ n ∈ Ico 163328 163584, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (154 : ℕ) ∧
    (∑ n ∈ Ico 163328 163584, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (489443 : ℤ) ∧
    (∑ n ∈ Ico 163328 163584, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (9789012077337654166322632916 : ℤ) := by
  rcases cdemPrefixStats_163328_163456 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_163456_163584 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 163328 ≤ 163456) (by norm_num : 163456 ≤ 163584), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 163328 ≤ 163456) (by norm_num : 163456 ≤ 163584), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 163328 ≤ 163456) (by norm_num : 163456 ≤ 163584), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 163328 ≤ 163456) (by norm_num : 163456 ≤ 163584), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_163584_163648 :
    (∑ n ∈ Ico 163584 163648, mobiusTreeValue 16 mobiusTable1200001 n) = (-14 : ℤ) ∧
    (∑ n ∈ Ico 163584 163648, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 163584 163648, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-427780 : ℤ) ∧
    (∑ n ∈ Ico 163584 163648, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-8555783704068471147712314333 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_163648_163712 :
    (∑ n ∈ Ico 163648 163712, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 163648 163712, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 163648 163712, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-14 : ℤ) ∧
    (∑ n ∈ Ico 163648 163712, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-227651736230686131585885 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_163584_163712 :
    (∑ n ∈ Ico 163584 163712, mobiusTreeValue 16 mobiusTable1200001 n) = (-14 : ℤ) ∧
    (∑ n ∈ Ico 163584 163712, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (80 : ℕ) ∧
    (∑ n ∈ Ico 163584 163712, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-427794 : ℤ) ∧
    (∑ n ∈ Ico 163584 163712, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-8556011355804701833843900218 : ℤ) := by
  rcases cdemPrefixStats_163584_163648 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_163648_163712 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 163584 ≤ 163648) (by norm_num : 163648 ≤ 163712), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 163584 ≤ 163648) (by norm_num : 163648 ≤ 163712), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 163584 ≤ 163648) (by norm_num : 163648 ≤ 163712), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 163584 ≤ 163648) (by norm_num : 163648 ≤ 163712), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_163712_163776 :
    (∑ n ∈ Ico 163712 163776, mobiusTreeValue 16 mobiusTable1200001 n) = (3 : ℤ) ∧
    (∑ n ∈ Ico 163712 163776, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 163712 163776, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (91615 : ℤ) ∧
    (∑ n ∈ Ico 163712 163776, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1832366834018389466573969497 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_163776_163840 :
    (∑ n ∈ Ico 163776 163840, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 163776 163840, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 163776 163840, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (30532 : ℤ) ∧
    (∑ n ∈ Ico 163776 163840, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (610679503588067413757337712 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_163712_163840 :
    (∑ n ∈ Ico 163712 163840, mobiusTreeValue 16 mobiusTable1200001 n) = (4 : ℤ) ∧
    (∑ n ∈ Ico 163712 163840, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (76 : ℕ) ∧
    (∑ n ∈ Ico 163712 163840, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (122147 : ℤ) ∧
    (∑ n ∈ Ico 163712 163840, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (2443046337606456880331307209 : ℤ) := by
  rcases cdemPrefixStats_163712_163776 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_163776_163840 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 163712 ≤ 163776) (by norm_num : 163776 ≤ 163840), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 163712 ≤ 163776) (by norm_num : 163776 ≤ 163840), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 163712 ≤ 163776) (by norm_num : 163776 ≤ 163840), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 163712 ≤ 163776) (by norm_num : 163776 ≤ 163840), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_163584_163840 :
    (∑ n ∈ Ico 163584 163840, mobiusTreeValue 16 mobiusTable1200001 n) = (-10 : ℤ) ∧
    (∑ n ∈ Ico 163584 163840, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (156 : ℕ) ∧
    (∑ n ∈ Ico 163584 163840, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-305647 : ℤ) ∧
    (∑ n ∈ Ico 163584 163840, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-6112965018198244953512593009 : ℤ) := by
  rcases cdemPrefixStats_163584_163712 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_163712_163840 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 163584 ≤ 163712) (by norm_num : 163712 ≤ 163840), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 163584 ≤ 163712) (by norm_num : 163712 ≤ 163840), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 163584 ≤ 163712) (by norm_num : 163712 ≤ 163840), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 163584 ≤ 163712) (by norm_num : 163712 ≤ 163840), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_163328_163840 :
    (∑ n ∈ Ico 163328 163840, mobiusTreeValue 16 mobiusTable1200001 n) = (6 : ℤ) ∧
    (∑ n ∈ Ico 163328 163840, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (310 : ℕ) ∧
    (∑ n ∈ Ico 163328 163840, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (183796 : ℤ) ∧
    (∑ n ∈ Ico 163328 163840, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (3676047059139409212810039907 : ℤ) := by
  rcases cdemPrefixStats_163328_163584 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_163584_163840 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 163328 ≤ 163584) (by norm_num : 163584 ≤ 163840), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 163328 ≤ 163584) (by norm_num : 163584 ≤ 163840), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 163328 ≤ 163584) (by norm_num : 163584 ≤ 163840), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 163328 ≤ 163584) (by norm_num : 163584 ≤ 163840), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_162816_163840 :
    (∑ n ∈ Ico 162816 163840, mobiusTreeValue 16 mobiusTable1200001 n) = (31 : ℤ) ∧
    (∑ n ∈ Ico 162816 163840, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (619 : ℕ) ∧
    (∑ n ∈ Ico 162816 163840, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (949879 : ℤ) ∧
    (∑ n ∈ Ico 162816 163840, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (18997820560923543886138239961 : ℤ) := by
  rcases cdemPrefixStats_162816_163328 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_163328_163840 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 162816 ≤ 163328) (by norm_num : 163328 ≤ 163840), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 162816 ≤ 163328) (by norm_num : 163328 ≤ 163840), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 162816 ≤ 163328) (by norm_num : 163328 ≤ 163840), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 162816 ≤ 163328) (by norm_num : 163328 ≤ 163840), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_161792_163840 :
    (∑ n ∈ Ico 161792 163840, mobiusTreeValue 16 mobiusTable1200001 n) = (51 : ℤ) ∧
    (∑ n ∈ Ico 161792 163840, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (1243 : ℕ) ∧
    (∑ n ∈ Ico 161792 163840, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (1569228 : ℤ) ∧
    (∑ n ∈ Ico 161792 163840, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (31384890987412802626922154637 : ℤ) := by
  rcases cdemPrefixStats_161792_162816 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_162816_163840 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 161792 ≤ 162816) (by norm_num : 162816 ≤ 163840), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 161792 ≤ 162816) (by norm_num : 162816 ≤ 163840), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 161792 ≤ 162816) (by norm_num : 162816 ≤ 163840), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 161792 ≤ 162816) (by norm_num : 162816 ≤ 163840), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_159744_163840 :
    (∑ n ∈ Ico 159744 163840, mobiusTreeValue 16 mobiusTable1200001 n) = (72 : ℤ) ∧
    (∑ n ∈ Ico 159744 163840, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (2482 : ℕ) ∧
    (∑ n ∈ Ico 159744 163840, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (2223548 : ℤ) ∧
    (∑ n ∈ Ico 159744 163840, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (44471728482976744577237731157 : ℤ) := by
  rcases cdemPrefixStats_159744_161792 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_161792_163840 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 159744 ≤ 161792) (by norm_num : 161792 ≤ 163840), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 159744 ≤ 161792) (by norm_num : 161792 ≤ 163840), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 159744 ≤ 161792) (by norm_num : 161792 ≤ 163840), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 159744 ≤ 161792) (by norm_num : 161792 ≤ 163840), hR1, hR2] <;> norm_num

theorem cdemPrefixGroup039_checked_complete :
    (∑ n ∈ Ico 159744 163840, mobiusTreeValue 16 mobiusTable1200001 n) = (72 : ℤ) ∧
    (∑ n ∈ Ico 159744 163840, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (2482 : ℕ) ∧
    (∑ n ∈ Ico 159744 163840, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (2223548 : ℤ) ∧
    (∑ n ∈ Ico 159744 163840, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (44471728482976744577237731157 : ℤ) := cdemPrefixStats_159744_163840
end Helfgott
#print axioms Helfgott.cdemPrefixGroup039_checked_complete

open Helfgott Finset
open scoped BigOperators

theorem solution :
    (∑ n ∈ Ico 159744 163840, mobiusTreeValue 16 mobiusTable1200001 n) = (72 : ℤ) ∧
    (∑ n ∈ Ico 159744 163840, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (2482 : ℕ) ∧
    (∑ n ∈ Ico 159744 163840, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (2223548 : ℤ) ∧
    (∑ n ∈ Ico 159744 163840, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (44471728482976744577237731157 : ℤ) := Helfgott.cdemPrefixGroup039_checked_complete
#print axioms solution
