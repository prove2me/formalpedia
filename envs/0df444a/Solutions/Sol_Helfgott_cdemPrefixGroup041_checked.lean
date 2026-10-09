-- Prove2me | solution 1 for Helfgott.cdemPrefixGroup041_checked
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-09T02:45:17.391259+00:00
-- url     : https://prove2.me/submissions/93da71d0-15aa-46e8-85a7-6d0255c33877

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
private theorem cdemPrefixStats_167936_168000 :
    (∑ n ∈ Ico 167936 168000, mobiusTreeValue 16 mobiusTable1200001 n) = (8 : ℤ) ∧
    (∑ n ∈ Ico 167936 168000, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 167936 168000, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (238160 : ℤ) ∧
    (∑ n ∈ Ico 167936 168000, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (4763343742620383779332962032 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_168000_168064 :
    (∑ n ∈ Ico 168000 168064, mobiusTreeValue 16 mobiusTable1200001 n) = (13 : ℤ) ∧
    (∑ n ∈ Ico 168000 168064, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 168000 168064, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (386821 : ℤ) ∧
    (∑ n ∈ Ico 168000 168064, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (7736497759681531295048641228 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_167936_168064 :
    (∑ n ∈ Ico 167936 168064, mobiusTreeValue 16 mobiusTable1200001 n) = (21 : ℤ) ∧
    (∑ n ∈ Ico 167936 168064, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (81 : ℕ) ∧
    (∑ n ∈ Ico 167936 168064, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (624981 : ℤ) ∧
    (∑ n ∈ Ico 167936 168064, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (12499841502301915074381603260 : ℤ) := by
  rcases cdemPrefixStats_167936_168000 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_168000_168064 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 167936 ≤ 168000) (by norm_num : 168000 ≤ 168064), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 167936 ≤ 168000) (by norm_num : 168000 ≤ 168064), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 167936 ≤ 168000) (by norm_num : 168000 ≤ 168064), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 167936 ≤ 168000) (by norm_num : 168000 ≤ 168064), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_168064_168128 :
    (∑ n ∈ Ico 168064 168128, mobiusTreeValue 16 mobiusTable1200001 n) = (3 : ℤ) ∧
    (∑ n ∈ Ico 168064 168128, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 168064 168128, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (89199 : ℤ) ∧
    (∑ n ∈ Ico 168064 168128, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1784000855310507737528589118 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_168128_168192 :
    (∑ n ∈ Ico 168128 168192, mobiusTreeValue 16 mobiusTable1200001 n) = (6 : ℤ) ∧
    (∑ n ∈ Ico 168128 168192, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 168128 168192, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (178410 : ℤ) ∧
    (∑ n ∈ Ico 168128 168192, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (3568171983593612782033171802 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_168064_168192 :
    (∑ n ∈ Ico 168064 168192, mobiusTreeValue 16 mobiusTable1200001 n) = (9 : ℤ) ∧
    (∑ n ∈ Ico 168064 168192, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 168064 168192, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (267609 : ℤ) ∧
    (∑ n ∈ Ico 168064 168192, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (5352172838904120519561760920 : ℤ) := by
  rcases cdemPrefixStats_168064_168128 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_168128_168192 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 168064 ≤ 168128) (by norm_num : 168128 ≤ 168192), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 168064 ≤ 168128) (by norm_num : 168128 ≤ 168192), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 168064 ≤ 168128) (by norm_num : 168128 ≤ 168192), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 168064 ≤ 168128) (by norm_num : 168128 ≤ 168192), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_167936_168192 :
    (∑ n ∈ Ico 167936 168192, mobiusTreeValue 16 mobiusTable1200001 n) = (30 : ℤ) ∧
    (∑ n ∈ Ico 167936 168192, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (158 : ℕ) ∧
    (∑ n ∈ Ico 167936 168192, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (892590 : ℤ) ∧
    (∑ n ∈ Ico 167936 168192, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (17852014341206035593943364180 : ℤ) := by
  rcases cdemPrefixStats_167936_168064 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_168064_168192 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 167936 ≤ 168064) (by norm_num : 168064 ≤ 168192), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 167936 ≤ 168064) (by norm_num : 168064 ≤ 168192), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 167936 ≤ 168064) (by norm_num : 168064 ≤ 168192), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 167936 ≤ 168064) (by norm_num : 168064 ≤ 168192), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_168192_168256 :
    (∑ n ∈ Ico 168192 168256, mobiusTreeValue 16 mobiusTable1200001 n) = (-4 : ℤ) ∧
    (∑ n ∈ Ico 168192 168256, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (36 : ℕ) ∧
    (∑ n ∈ Ico 168192 168256, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-118929 : ℤ) ∧
    (∑ n ∈ Ico 168192 168256, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-2378552409415286499228646547 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_168256_168320 :
    (∑ n ∈ Ico 168256 168320, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 168256 168320, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 168256 168320, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-7 : ℤ) ∧
    (∑ n ∈ Ico 168256 168320, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-88217679318424715545751 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_168192_168320 :
    (∑ n ∈ Ico 168192 168320, mobiusTreeValue 16 mobiusTable1200001 n) = (-4 : ℤ) ∧
    (∑ n ∈ Ico 168192 168320, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (74 : ℕ) ∧
    (∑ n ∈ Ico 168192 168320, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-118936 : ℤ) ∧
    (∑ n ∈ Ico 168192 168320, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-2378640627094604923944192298 : ℤ) := by
  rcases cdemPrefixStats_168192_168256 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_168256_168320 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 168192 ≤ 168256) (by norm_num : 168256 ≤ 168320), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 168192 ≤ 168256) (by norm_num : 168256 ≤ 168320), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 168192 ≤ 168256) (by norm_num : 168256 ≤ 168320), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 168192 ≤ 168256) (by norm_num : 168256 ≤ 168320), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_168320_168384 :
    (∑ n ∈ Ico 168320 168384, mobiusTreeValue 16 mobiusTable1200001 n) = (-2 : ℤ) ∧
    (∑ n ∈ Ico 168320 168384, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 168320 168384, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-59448 : ℤ) ∧
    (∑ n ∈ Ico 168320 168384, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-1188974986183296011564248502 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_168384_168448 :
    (∑ n ∈ Ico 168384 168448, mobiusTreeValue 16 mobiusTable1200001 n) = (10 : ℤ) ∧
    (∑ n ∈ Ico 168384 168448, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 168384 168448, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (296865 : ℤ) ∧
    (∑ n ∈ Ico 168384 168448, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (5937417367238883014684166919 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_168320_168448 :
    (∑ n ∈ Ico 168320 168448, mobiusTreeValue 16 mobiusTable1200001 n) = (8 : ℤ) ∧
    (∑ n ∈ Ico 168320 168448, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (80 : ℕ) ∧
    (∑ n ∈ Ico 168320 168448, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (237417 : ℤ) ∧
    (∑ n ∈ Ico 168320 168448, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (4748442381055587003119918417 : ℤ) := by
  rcases cdemPrefixStats_168320_168384 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_168384_168448 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 168320 ≤ 168384) (by norm_num : 168384 ≤ 168448), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 168320 ≤ 168384) (by norm_num : 168384 ≤ 168448), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 168320 ≤ 168384) (by norm_num : 168384 ≤ 168448), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 168320 ≤ 168384) (by norm_num : 168384 ≤ 168448), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_168192_168448 :
    (∑ n ∈ Ico 168192 168448, mobiusTreeValue 16 mobiusTable1200001 n) = (4 : ℤ) ∧
    (∑ n ∈ Ico 168192 168448, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (154 : ℕ) ∧
    (∑ n ∈ Ico 168192 168448, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (118481 : ℤ) ∧
    (∑ n ∈ Ico 168192 168448, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (2369801753960982079175726119 : ℤ) := by
  rcases cdemPrefixStats_168192_168320 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_168320_168448 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 168192 ≤ 168320) (by norm_num : 168320 ≤ 168448), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 168192 ≤ 168320) (by norm_num : 168320 ≤ 168448), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 168192 ≤ 168320) (by norm_num : 168320 ≤ 168448), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 168192 ≤ 168320) (by norm_num : 168320 ≤ 168448), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_167936_168448 :
    (∑ n ∈ Ico 167936 168448, mobiusTreeValue 16 mobiusTable1200001 n) = (34 : ℤ) ∧
    (∑ n ∈ Ico 167936 168448, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (312 : ℕ) ∧
    (∑ n ∈ Ico 167936 168448, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (1011071 : ℤ) ∧
    (∑ n ∈ Ico 167936 168448, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (20221816095167017673119090299 : ℤ) := by
  rcases cdemPrefixStats_167936_168192 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_168192_168448 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 167936 ≤ 168192) (by norm_num : 168192 ≤ 168448), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 167936 ≤ 168192) (by norm_num : 168192 ≤ 168448), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 167936 ≤ 168192) (by norm_num : 168192 ≤ 168448), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 167936 ≤ 168192) (by norm_num : 168192 ≤ 168448), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_168448_168512 :
    (∑ n ∈ Ico 168448 168512, mobiusTreeValue 16 mobiusTable1200001 n) = (-7 : ℤ) ∧
    (∑ n ∈ Ico 168448 168512, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 168448 168512, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-207755 : ℤ) ∧
    (∑ n ∈ Ico 168448 168512, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-4155176397314314147884667655 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_168512_168576 :
    (∑ n ∈ Ico 168512 168576, mobiusTreeValue 16 mobiusTable1200001 n) = (2 : ℤ) ∧
    (∑ n ∈ Ico 168512 168576, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 168512 168576, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (59326 : ℤ) ∧
    (∑ n ∈ Ico 168512 168576, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1186482398695747537168095560 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_168448_168576 :
    (∑ n ∈ Ico 168448 168576, mobiusTreeValue 16 mobiusTable1200001 n) = (-5 : ℤ) ∧
    (∑ n ∈ Ico 168448 168576, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 168448 168576, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-148429 : ℤ) ∧
    (∑ n ∈ Ico 168448 168576, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-2968693998618566610716572095 : ℤ) := by
  rcases cdemPrefixStats_168448_168512 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_168512_168576 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 168448 ≤ 168512) (by norm_num : 168512 ≤ 168576), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 168448 ≤ 168512) (by norm_num : 168512 ≤ 168576), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 168448 ≤ 168512) (by norm_num : 168512 ≤ 168576), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 168448 ≤ 168512) (by norm_num : 168512 ≤ 168576), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_168576_168640 :
    (∑ n ∈ Ico 168576 168640, mobiusTreeValue 16 mobiusTable1200001 n) = (8 : ℤ) ∧
    (∑ n ∈ Ico 168576 168640, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 168576 168640, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (237222 : ℤ) ∧
    (∑ n ∈ Ico 168576 168640, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (4744497711347501259987951956 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_168640_168704 :
    (∑ n ∈ Ico 168640 168704, mobiusTreeValue 16 mobiusTable1200001 n) = (8 : ℤ) ∧
    (∑ n ∈ Ico 168640 168704, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 168640 168704, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (237136 : ℤ) ∧
    (∑ n ∈ Ico 168640 168704, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (4742827655132147853844885055 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_168576_168704 :
    (∑ n ∈ Ico 168576 168704, mobiusTreeValue 16 mobiusTable1200001 n) = (16 : ℤ) ∧
    (∑ n ∈ Ico 168576 168704, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 168576 168704, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (474358 : ℤ) ∧
    (∑ n ∈ Ico 168576 168704, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (9487325366479649113832837011 : ℤ) := by
  rcases cdemPrefixStats_168576_168640 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_168640_168704 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 168576 ≤ 168640) (by norm_num : 168640 ≤ 168704), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 168576 ≤ 168640) (by norm_num : 168640 ≤ 168704), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 168576 ≤ 168640) (by norm_num : 168640 ≤ 168704), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 168576 ≤ 168640) (by norm_num : 168640 ≤ 168704), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_168448_168704 :
    (∑ n ∈ Ico 168448 168704, mobiusTreeValue 16 mobiusTable1200001 n) = (11 : ℤ) ∧
    (∑ n ∈ Ico 168448 168704, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (155 : ℕ) ∧
    (∑ n ∈ Ico 168448 168704, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (325929 : ℤ) ∧
    (∑ n ∈ Ico 168448 168704, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (6518631367861082503116264916 : ℤ) := by
  rcases cdemPrefixStats_168448_168576 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_168576_168704 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 168448 ≤ 168576) (by norm_num : 168576 ≤ 168704), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 168448 ≤ 168576) (by norm_num : 168576 ≤ 168704), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 168448 ≤ 168576) (by norm_num : 168576 ≤ 168704), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 168448 ≤ 168576) (by norm_num : 168576 ≤ 168704), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_168704_168768 :
    (∑ n ∈ Ico 168704 168768, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 168704 168768, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 168704 168768, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-29646 : ℤ) ∧
    (∑ n ∈ Ico 168704 168768, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-592933289971532515606963773 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_168768_168832 :
    (∑ n ∈ Ico 168768 168832, mobiusTreeValue 16 mobiusTable1200001 n) = (9 : ℤ) ∧
    (∑ n ∈ Ico 168768 168832, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 168768 168832, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (266576 : ℤ) ∧
    (∑ n ∈ Ico 168768 168832, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (5331560573786470277881582823 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_168704_168832 :
    (∑ n ∈ Ico 168704 168832, mobiusTreeValue 16 mobiusTable1200001 n) = (8 : ℤ) ∧
    (∑ n ∈ Ico 168704 168832, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 168704 168832, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (236930 : ℤ) ∧
    (∑ n ∈ Ico 168704 168832, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (4738627283814937762274619050 : ℤ) := by
  rcases cdemPrefixStats_168704_168768 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_168768_168832 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 168704 ≤ 168768) (by norm_num : 168768 ≤ 168832), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 168704 ≤ 168768) (by norm_num : 168768 ≤ 168832), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 168704 ≤ 168768) (by norm_num : 168768 ≤ 168832), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 168704 ≤ 168768) (by norm_num : 168768 ≤ 168832), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_168832_168896 :
    (∑ n ∈ Ico 168832 168896, mobiusTreeValue 16 mobiusTable1200001 n) = (-2 : ℤ) ∧
    (∑ n ∈ Ico 168832 168896, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 168832 168896, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-59176 : ℤ) ∧
    (∑ n ∈ Ico 168832 168896, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-1183480305450425604200738530 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_168896_168960 :
    (∑ n ∈ Ico 168896 168960, mobiusTreeValue 16 mobiusTable1200001 n) = (11 : ℤ) ∧
    (∑ n ∈ Ico 168896 168960, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 168896 168960, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (325557 : ℤ) ∧
    (∑ n ∈ Ico 168896 168960, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (6511289055964320962762815165 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_168832_168960 :
    (∑ n ∈ Ico 168832 168960, mobiusTreeValue 16 mobiusTable1200001 n) = (9 : ℤ) ∧
    (∑ n ∈ Ico 168832 168960, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (81 : ℕ) ∧
    (∑ n ∈ Ico 168832 168960, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (266381 : ℤ) ∧
    (∑ n ∈ Ico 168832 168960, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (5327808750513895358562076635 : ℤ) := by
  rcases cdemPrefixStats_168832_168896 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_168896_168960 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 168832 ≤ 168896) (by norm_num : 168896 ≤ 168960), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 168832 ≤ 168896) (by norm_num : 168896 ≤ 168960), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 168832 ≤ 168896) (by norm_num : 168896 ≤ 168960), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 168832 ≤ 168896) (by norm_num : 168896 ≤ 168960), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_168704_168960 :
    (∑ n ∈ Ico 168704 168960, mobiusTreeValue 16 mobiusTable1200001 n) = (17 : ℤ) ∧
    (∑ n ∈ Ico 168704 168960, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (159 : ℕ) ∧
    (∑ n ∈ Ico 168704 168960, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (503311 : ℤ) ∧
    (∑ n ∈ Ico 168704 168960, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (10066436034328833120836695685 : ℤ) := by
  rcases cdemPrefixStats_168704_168832 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_168832_168960 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 168704 ≤ 168832) (by norm_num : 168832 ≤ 168960), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 168704 ≤ 168832) (by norm_num : 168832 ≤ 168960), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 168704 ≤ 168832) (by norm_num : 168832 ≤ 168960), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 168704 ≤ 168832) (by norm_num : 168832 ≤ 168960), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_168448_168960 :
    (∑ n ∈ Ico 168448 168960, mobiusTreeValue 16 mobiusTable1200001 n) = (28 : ℤ) ∧
    (∑ n ∈ Ico 168448 168960, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (314 : ℕ) ∧
    (∑ n ∈ Ico 168448 168960, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (829240 : ℤ) ∧
    (∑ n ∈ Ico 168448 168960, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (16585067402189915623952960601 : ℤ) := by
  rcases cdemPrefixStats_168448_168704 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_168704_168960 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 168448 ≤ 168704) (by norm_num : 168704 ≤ 168960), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 168448 ≤ 168704) (by norm_num : 168704 ≤ 168960), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 168448 ≤ 168704) (by norm_num : 168704 ≤ 168960), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 168448 ≤ 168704) (by norm_num : 168704 ≤ 168960), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_167936_168960 :
    (∑ n ∈ Ico 167936 168960, mobiusTreeValue 16 mobiusTable1200001 n) = (62 : ℤ) ∧
    (∑ n ∈ Ico 167936 168960, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (626 : ℕ) ∧
    (∑ n ∈ Ico 167936 168960, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (1840311 : ℤ) ∧
    (∑ n ∈ Ico 167936 168960, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (36806883497356933297072050900 : ℤ) := by
  rcases cdemPrefixStats_167936_168448 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_168448_168960 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 167936 ≤ 168448) (by norm_num : 168448 ≤ 168960), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 167936 ≤ 168448) (by norm_num : 168448 ≤ 168960), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 167936 ≤ 168448) (by norm_num : 168448 ≤ 168960), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 167936 ≤ 168448) (by norm_num : 168448 ≤ 168960), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_168960_169024 :
    (∑ n ∈ Ico 168960 169024, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 168960 169024, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (42 : ℕ) ∧
    (∑ n ∈ Ico 168960 169024, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (2 : ℤ) ∧
    (∑ n ∈ Ico 168960 169024, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-30997865802029808424 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_169024_169088 :
    (∑ n ∈ Ico 169024 169088, mobiusTreeValue 16 mobiusTable1200001 n) = (3 : ℤ) ∧
    (∑ n ∈ Ico 169024 169088, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 169024 169088, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (88742 : ℤ) ∧
    (∑ n ∈ Ico 169024 169088, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1774832795351341916314907782 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_168960_169088 :
    (∑ n ∈ Ico 168960 169088, mobiusTreeValue 16 mobiusTable1200001 n) = (3 : ℤ) ∧
    (∑ n ∈ Ico 168960 169088, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (79 : ℕ) ∧
    (∑ n ∈ Ico 168960 169088, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (88744 : ℤ) ∧
    (∑ n ∈ Ico 168960 169088, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1774832764353476114285099358 : ℤ) := by
  rcases cdemPrefixStats_168960_169024 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_169024_169088 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 168960 ≤ 169024) (by norm_num : 169024 ≤ 169088), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 168960 ≤ 169024) (by norm_num : 169024 ≤ 169088), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 168960 ≤ 169024) (by norm_num : 169024 ≤ 169088), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 168960 ≤ 169024) (by norm_num : 169024 ≤ 169088), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_169088_169152 :
    (∑ n ∈ Ico 169088 169152, mobiusTreeValue 16 mobiusTable1200001 n) = (2 : ℤ) ∧
    (∑ n ∈ Ico 169088 169152, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 169088 169152, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (59114 : ℤ) ∧
    (∑ n ∈ Ico 169088 169152, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1182274055330352227233518475 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_169152_169216 :
    (∑ n ∈ Ico 169152 169216, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 169152 169216, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 169152 169216, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-29571 : ℤ) ∧
    (∑ n ∈ Ico 169152 169216, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-591446312696941122994931567 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_169088_169216 :
    (∑ n ∈ Ico 169088 169216, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 169088 169216, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (79 : ℕ) ∧
    (∑ n ∈ Ico 169088 169216, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (29543 : ℤ) ∧
    (∑ n ∈ Ico 169088 169216, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (590827742633411104238586908 : ℤ) := by
  rcases cdemPrefixStats_169088_169152 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_169152_169216 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 169088 ≤ 169152) (by norm_num : 169152 ≤ 169216), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 169088 ≤ 169152) (by norm_num : 169152 ≤ 169216), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 169088 ≤ 169152) (by norm_num : 169152 ≤ 169216), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 169088 ≤ 169152) (by norm_num : 169152 ≤ 169216), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_168960_169216 :
    (∑ n ∈ Ico 168960 169216, mobiusTreeValue 16 mobiusTable1200001 n) = (4 : ℤ) ∧
    (∑ n ∈ Ico 168960 169216, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (158 : ℕ) ∧
    (∑ n ∈ Ico 168960 169216, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (118287 : ℤ) ∧
    (∑ n ∈ Ico 168960 169216, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (2365660506986887218523686266 : ℤ) := by
  rcases cdemPrefixStats_168960_169088 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_169088_169216 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 168960 ≤ 169088) (by norm_num : 169088 ≤ 169216), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 168960 ≤ 169088) (by norm_num : 169088 ≤ 169216), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 168960 ≤ 169088) (by norm_num : 169088 ≤ 169216), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 168960 ≤ 169088) (by norm_num : 169088 ≤ 169216), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_169216_169280 :
    (∑ n ∈ Ico 169216 169280, mobiusTreeValue 16 mobiusTable1200001 n) = (-2 : ℤ) ∧
    (∑ n ∈ Ico 169216 169280, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 169216 169280, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-59107 : ℤ) ∧
    (∑ n ∈ Ico 169216 169280, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-1182130795519789728970497390 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_169280_169344 :
    (∑ n ∈ Ico 169280 169344, mobiusTreeValue 16 mobiusTable1200001 n) = (-6 : ℤ) ∧
    (∑ n ∈ Ico 169280 169344, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 169280 169344, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-177170 : ℤ) ∧
    (∑ n ∈ Ico 169280 169344, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-3543436175110095653946603018 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_169216_169344 :
    (∑ n ∈ Ico 169216 169344, mobiusTreeValue 16 mobiusTable1200001 n) = (-8 : ℤ) ∧
    (∑ n ∈ Ico 169216 169344, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (76 : ℕ) ∧
    (∑ n ∈ Ico 169216 169344, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-236277 : ℤ) ∧
    (∑ n ∈ Ico 169216 169344, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-4725566970629885382917100408 : ℤ) := by
  rcases cdemPrefixStats_169216_169280 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_169280_169344 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 169216 ≤ 169280) (by norm_num : 169280 ≤ 169344), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 169216 ≤ 169280) (by norm_num : 169280 ≤ 169344), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 169216 ≤ 169280) (by norm_num : 169280 ≤ 169344), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 169216 ≤ 169280) (by norm_num : 169280 ≤ 169344), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_169344_169408 :
    (∑ n ∈ Ico 169344 169408, mobiusTreeValue 16 mobiusTable1200001 n) = (-2 : ℤ) ∧
    (∑ n ∈ Ico 169344 169408, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 169344 169408, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-59056 : ℤ) ∧
    (∑ n ∈ Ico 169344 169408, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-1181146479114707905501741091 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_169408_169472 :
    (∑ n ∈ Ico 169408 169472, mobiusTreeValue 16 mobiusTable1200001 n) = (7 : ℤ) ∧
    (∑ n ∈ Ico 169408 169472, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 169408 169472, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (206553 : ℤ) ∧
    (∑ n ∈ Ico 169408 169472, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (4131147943180364273537721944 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_169344_169472 :
    (∑ n ∈ Ico 169344 169472, mobiusTreeValue 16 mobiusTable1200001 n) = (5 : ℤ) ∧
    (∑ n ∈ Ico 169344 169472, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (79 : ℕ) ∧
    (∑ n ∈ Ico 169344 169472, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (147497 : ℤ) ∧
    (∑ n ∈ Ico 169344 169472, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (2950001464065656368035980853 : ℤ) := by
  rcases cdemPrefixStats_169344_169408 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_169408_169472 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 169344 ≤ 169408) (by norm_num : 169408 ≤ 169472), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 169344 ≤ 169408) (by norm_num : 169408 ≤ 169472), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 169344 ≤ 169408) (by norm_num : 169408 ≤ 169472), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 169344 ≤ 169408) (by norm_num : 169408 ≤ 169472), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_169216_169472 :
    (∑ n ∈ Ico 169216 169472, mobiusTreeValue 16 mobiusTable1200001 n) = (-3 : ℤ) ∧
    (∑ n ∈ Ico 169216 169472, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (155 : ℕ) ∧
    (∑ n ∈ Ico 169216 169472, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-88780 : ℤ) ∧
    (∑ n ∈ Ico 169216 169472, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-1775565506564229014881119555 : ℤ) := by
  rcases cdemPrefixStats_169216_169344 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_169344_169472 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 169216 ≤ 169344) (by norm_num : 169344 ≤ 169472), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 169216 ≤ 169344) (by norm_num : 169344 ≤ 169472), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 169216 ≤ 169344) (by norm_num : 169344 ≤ 169472), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 169216 ≤ 169344) (by norm_num : 169344 ≤ 169472), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_168960_169472 :
    (∑ n ∈ Ico 168960 169472, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 168960 169472, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (313 : ℕ) ∧
    (∑ n ∈ Ico 168960 169472, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (29507 : ℤ) ∧
    (∑ n ∈ Ico 168960 169472, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (590095000422658203642566711 : ℤ) := by
  rcases cdemPrefixStats_168960_169216 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_169216_169472 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 168960 ≤ 169216) (by norm_num : 169216 ≤ 169472), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 168960 ≤ 169216) (by norm_num : 169216 ≤ 169472), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 168960 ≤ 169216) (by norm_num : 169216 ≤ 169472), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 168960 ≤ 169216) (by norm_num : 169216 ≤ 169472), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_169472_169536 :
    (∑ n ∈ Ico 169472 169536, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 169472 169536, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 169472 169536, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-15 : ℤ) ∧
    (∑ n ∈ Ico 169472 169536, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-274949265487829779190325 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_169536_169600 :
    (∑ n ∈ Ico 169536 169600, mobiusTreeValue 16 mobiusTable1200001 n) = (4 : ℤ) ∧
    (∑ n ∈ Ico 169536 169600, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 169536 169600, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (117936 : ℤ) ∧
    (∑ n ∈ Ico 169536 169600, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (2358765275400854854700798363 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_169472_169600 :
    (∑ n ∈ Ico 169472 169600, mobiusTreeValue 16 mobiusTable1200001 n) = (4 : ℤ) ∧
    (∑ n ∈ Ico 169472 169600, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 169472 169600, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (117921 : ℤ) ∧
    (∑ n ∈ Ico 169472 169600, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (2358490326135367024921608038 : ℤ) := by
  rcases cdemPrefixStats_169472_169536 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_169536_169600 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 169472 ≤ 169536) (by norm_num : 169536 ≤ 169600), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 169472 ≤ 169536) (by norm_num : 169536 ≤ 169600), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 169472 ≤ 169536) (by norm_num : 169536 ≤ 169600), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 169472 ≤ 169536) (by norm_num : 169536 ≤ 169600), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_169600_169664 :
    (∑ n ∈ Ico 169600 169664, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 169600 169664, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 169600 169664, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (29 : ℤ) ∧
    (∑ n ∈ Ico 169600 169664, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (590768190065184479366154 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_169664_169728 :
    (∑ n ∈ Ico 169664 169728, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 169664 169728, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 169664 169728, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (29426 : ℤ) ∧
    (∑ n ∈ Ico 169664 169728, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (588469536676272602074556035 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_169600_169728 :
    (∑ n ∈ Ico 169600 169728, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 169600 169728, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 169600 169728, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (29455 : ℤ) ∧
    (∑ n ∈ Ico 169600 169728, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (589060304866337786553922189 : ℤ) := by
  rcases cdemPrefixStats_169600_169664 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_169664_169728 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 169600 ≤ 169664) (by norm_num : 169664 ≤ 169728), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 169600 ≤ 169664) (by norm_num : 169664 ≤ 169728), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 169600 ≤ 169664) (by norm_num : 169664 ≤ 169728), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 169600 ≤ 169664) (by norm_num : 169664 ≤ 169728), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_169472_169728 :
    (∑ n ∈ Ico 169472 169728, mobiusTreeValue 16 mobiusTable1200001 n) = (5 : ℤ) ∧
    (∑ n ∈ Ico 169472 169728, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (155 : ℕ) ∧
    (∑ n ∈ Ico 169472 169728, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (147376 : ℤ) ∧
    (∑ n ∈ Ico 169472 169728, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (2947550631001704811475530227 : ℤ) := by
  rcases cdemPrefixStats_169472_169600 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_169600_169728 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 169472 ≤ 169600) (by norm_num : 169600 ≤ 169728), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 169472 ≤ 169600) (by norm_num : 169600 ≤ 169728), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 169472 ≤ 169600) (by norm_num : 169600 ≤ 169728), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 169472 ≤ 169600) (by norm_num : 169600 ≤ 169728), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_169728_169792 :
    (∑ n ∈ Ico 169728 169792, mobiusTreeValue 16 mobiusTable1200001 n) = (-9 : ℤ) ∧
    (∑ n ∈ Ico 169728 169792, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 169728 169792, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-265055 : ℤ) ∧
    (∑ n ∈ Ico 169728 169792, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-5301175489476586870412605580 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_169792_169856 :
    (∑ n ∈ Ico 169792 169856, mobiusTreeValue 16 mobiusTable1200001 n) = (-10 : ℤ) ∧
    (∑ n ∈ Ico 169792 169856, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 169792 169856, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-294434 : ℤ) ∧
    (∑ n ∈ Ico 169792 169856, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-5888740558999955982156719595 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_169728_169856 :
    (∑ n ∈ Ico 169728 169856, mobiusTreeValue 16 mobiusTable1200001 n) = (-19 : ℤ) ∧
    (∑ n ∈ Ico 169728 169856, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 169728 169856, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-559489 : ℤ) ∧
    (∑ n ∈ Ico 169728 169856, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-11189916048476542852569325175 : ℤ) := by
  rcases cdemPrefixStats_169728_169792 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_169792_169856 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 169728 ≤ 169792) (by norm_num : 169792 ≤ 169856), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 169728 ≤ 169792) (by norm_num : 169792 ≤ 169856), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 169728 ≤ 169792) (by norm_num : 169792 ≤ 169856), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 169728 ≤ 169792) (by norm_num : 169792 ≤ 169856), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_169856_169920 :
    (∑ n ∈ Ico 169856 169920, mobiusTreeValue 16 mobiusTable1200001 n) = (-4 : ℤ) ∧
    (∑ n ∈ Ico 169856 169920, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 169856 169920, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-117719 : ℤ) ∧
    (∑ n ∈ Ico 169856 169920, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-2354433483888887912947125652 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_169920_169984 :
    (∑ n ∈ Ico 169920 169984, mobiusTreeValue 16 mobiusTable1200001 n) = (-2 : ℤ) ∧
    (∑ n ∈ Ico 169920 169984, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 169920 169984, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-58848 : ℤ) ∧
    (∑ n ∈ Ico 169920 169984, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-1177014006363584585796295345 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_169856_169984 :
    (∑ n ∈ Ico 169856 169984, mobiusTreeValue 16 mobiusTable1200001 n) = (-6 : ℤ) ∧
    (∑ n ∈ Ico 169856 169984, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 169856 169984, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-176567 : ℤ) ∧
    (∑ n ∈ Ico 169856 169984, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-3531447490252472498743420997 : ℤ) := by
  rcases cdemPrefixStats_169856_169920 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_169920_169984 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 169856 ≤ 169920) (by norm_num : 169920 ≤ 169984), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 169856 ≤ 169920) (by norm_num : 169920 ≤ 169984), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 169856 ≤ 169920) (by norm_num : 169920 ≤ 169984), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 169856 ≤ 169920) (by norm_num : 169920 ≤ 169984), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_169728_169984 :
    (∑ n ∈ Ico 169728 169984, mobiusTreeValue 16 mobiusTable1200001 n) = (-25 : ℤ) ∧
    (∑ n ∈ Ico 169728 169984, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (155 : ℕ) ∧
    (∑ n ∈ Ico 169728 169984, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-736056 : ℤ) ∧
    (∑ n ∈ Ico 169728 169984, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-14721363538729015351312746172 : ℤ) := by
  rcases cdemPrefixStats_169728_169856 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_169856_169984 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 169728 ≤ 169856) (by norm_num : 169856 ≤ 169984), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 169728 ≤ 169856) (by norm_num : 169856 ≤ 169984), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 169728 ≤ 169856) (by norm_num : 169856 ≤ 169984), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 169728 ≤ 169856) (by norm_num : 169856 ≤ 169984), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_169472_169984 :
    (∑ n ∈ Ico 169472 169984, mobiusTreeValue 16 mobiusTable1200001 n) = (-20 : ℤ) ∧
    (∑ n ∈ Ico 169472 169984, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (310 : ℕ) ∧
    (∑ n ∈ Ico 169472 169984, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-588680 : ℤ) ∧
    (∑ n ∈ Ico 169472 169984, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-11773812907727310539837215945 : ℤ) := by
  rcases cdemPrefixStats_169472_169728 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_169728_169984 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 169472 ≤ 169728) (by norm_num : 169728 ≤ 169984), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 169472 ≤ 169728) (by norm_num : 169728 ≤ 169984), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 169472 ≤ 169728) (by norm_num : 169728 ≤ 169984), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 169472 ≤ 169728) (by norm_num : 169728 ≤ 169984), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_168960_169984 :
    (∑ n ∈ Ico 168960 169984, mobiusTreeValue 16 mobiusTable1200001 n) = (-19 : ℤ) ∧
    (∑ n ∈ Ico 168960 169984, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (623 : ℕ) ∧
    (∑ n ∈ Ico 168960 169984, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-559173 : ℤ) ∧
    (∑ n ∈ Ico 168960 169984, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-11183717907304652336194649234 : ℤ) := by
  rcases cdemPrefixStats_168960_169472 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_169472_169984 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 168960 ≤ 169472) (by norm_num : 169472 ≤ 169984), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 168960 ≤ 169472) (by norm_num : 169472 ≤ 169984), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 168960 ≤ 169472) (by norm_num : 169472 ≤ 169984), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 168960 ≤ 169472) (by norm_num : 169472 ≤ 169984), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_167936_169984 :
    (∑ n ∈ Ico 167936 169984, mobiusTreeValue 16 mobiusTable1200001 n) = (43 : ℤ) ∧
    (∑ n ∈ Ico 167936 169984, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (1249 : ℕ) ∧
    (∑ n ∈ Ico 167936 169984, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (1281138 : ℤ) ∧
    (∑ n ∈ Ico 167936 169984, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (25623165590052280960877401666 : ℤ) := by
  rcases cdemPrefixStats_167936_168960 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_168960_169984 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 167936 ≤ 168960) (by norm_num : 168960 ≤ 169984), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 167936 ≤ 168960) (by norm_num : 168960 ≤ 169984), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 167936 ≤ 168960) (by norm_num : 168960 ≤ 169984), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 167936 ≤ 168960) (by norm_num : 168960 ≤ 169984), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_169984_170048 :
    (∑ n ∈ Ico 169984 170048, mobiusTreeValue 16 mobiusTable1200001 n) = (2 : ℤ) ∧
    (∑ n ∈ Ico 169984 170048, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 169984 170048, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (58815 : ℤ) ∧
    (∑ n ∈ Ico 169984 170048, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1176297660028536945354079131 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_170048_170112 :
    (∑ n ∈ Ico 170048 170112, mobiusTreeValue 16 mobiusTable1200001 n) = (-2 : ℤ) ∧
    (∑ n ∈ Ico 170048 170112, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 170048 170112, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-58772 : ℤ) ∧
    (∑ n ∈ Ico 170048 170112, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-1175440262255347008661080491 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_169984_170112 :
    (∑ n ∈ Ico 169984 170112, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 169984 170112, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (76 : ℕ) ∧
    (∑ n ∈ Ico 169984 170112, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (43 : ℤ) ∧
    (∑ n ∈ Ico 169984 170112, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (857397773189936692998640 : ℤ) := by
  rcases cdemPrefixStats_169984_170048 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_170048_170112 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 169984 ≤ 170048) (by norm_num : 170048 ≤ 170112), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 169984 ≤ 170048) (by norm_num : 170048 ≤ 170112), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 169984 ≤ 170048) (by norm_num : 170048 ≤ 170112), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 169984 ≤ 170048) (by norm_num : 170048 ≤ 170112), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_170112_170176 :
    (∑ n ∈ Ico 170112 170176, mobiusTreeValue 16 mobiusTable1200001 n) = (7 : ℤ) ∧
    (∑ n ∈ Ico 170112 170176, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 170112 170176, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (205705 : ℤ) ∧
    (∑ n ∈ Ico 170112 170176, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (4114151889939679651333965204 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_170176_170240 :
    (∑ n ∈ Ico 170176 170240, mobiusTreeValue 16 mobiusTable1200001 n) = (-2 : ℤ) ∧
    (∑ n ∈ Ico 170176 170240, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 170176 170240, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-58720 : ℤ) ∧
    (∑ n ∈ Ico 170176 170240, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-1174480674777652120636176552 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_170112_170240 :
    (∑ n ∈ Ico 170112 170240, mobiusTreeValue 16 mobiusTable1200001 n) = (5 : ℤ) ∧
    (∑ n ∈ Ico 170112 170240, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 170112 170240, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (146985 : ℤ) ∧
    (∑ n ∈ Ico 170112 170240, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (2939671215162027530697788652 : ℤ) := by
  rcases cdemPrefixStats_170112_170176 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_170176_170240 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 170112 ≤ 170176) (by norm_num : 170176 ≤ 170240), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 170112 ≤ 170176) (by norm_num : 170176 ≤ 170240), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 170112 ≤ 170176) (by norm_num : 170176 ≤ 170240), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 170112 ≤ 170176) (by norm_num : 170176 ≤ 170240), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_169984_170240 :
    (∑ n ∈ Ico 169984 170240, mobiusTreeValue 16 mobiusTable1200001 n) = (5 : ℤ) ∧
    (∑ n ∈ Ico 169984 170240, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (153 : ℕ) ∧
    (∑ n ∈ Ico 169984 170240, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (147028 : ℤ) ∧
    (∑ n ∈ Ico 169984 170240, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (2940528612935217467390787292 : ℤ) := by
  rcases cdemPrefixStats_169984_170112 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_170112_170240 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 169984 ≤ 170112) (by norm_num : 170112 ≤ 170240), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 169984 ≤ 170112) (by norm_num : 170112 ≤ 170240), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 169984 ≤ 170112) (by norm_num : 170112 ≤ 170240), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 169984 ≤ 170112) (by norm_num : 170112 ≤ 170240), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_170240_170304 :
    (∑ n ∈ Ico 170240 170304, mobiusTreeValue 16 mobiusTable1200001 n) = (-8 : ℤ) ∧
    (∑ n ∈ Ico 170240 170304, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 170240 170304, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-234917 : ℤ) ∧
    (∑ n ∈ Ico 170240 170304, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-4698458112254105269568719851 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_170304_170368 :
    (∑ n ∈ Ico 170304 170368, mobiusTreeValue 16 mobiusTable1200001 n) = (-5 : ℤ) ∧
    (∑ n ∈ Ico 170304 170368, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 170304 170368, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-146736 : ℤ) ∧
    (∑ n ∈ Ico 170304 170368, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-2934768232007950222522095899 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_170240_170368 :
    (∑ n ∈ Ico 170240 170368, mobiusTreeValue 16 mobiusTable1200001 n) = (-13 : ℤ) ∧
    (∑ n ∈ Ico 170240 170368, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (81 : ℕ) ∧
    (∑ n ∈ Ico 170240 170368, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-381653 : ℤ) ∧
    (∑ n ∈ Ico 170240 170368, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-7633226344262055492090815750 : ℤ) := by
  rcases cdemPrefixStats_170240_170304 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_170304_170368 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 170240 ≤ 170304) (by norm_num : 170304 ≤ 170368), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 170240 ≤ 170304) (by norm_num : 170304 ≤ 170368), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 170240 ≤ 170304) (by norm_num : 170304 ≤ 170368), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 170240 ≤ 170304) (by norm_num : 170304 ≤ 170368), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_170368_170432 :
    (∑ n ∈ Ico 170368 170432, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 170368 170432, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 170368 170432, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (29318 : ℤ) ∧
    (∑ n ∈ Ico 170368 170432, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (586365444160613949358019776 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_170432_170496 :
    (∑ n ∈ Ico 170432 170496, mobiusTreeValue 16 mobiusTable1200001 n) = (4 : ℤ) ∧
    (∑ n ∈ Ico 170432 170496, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 170432 170496, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (117303 : ℤ) ∧
    (∑ n ∈ Ico 170432 170496, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (2346127054555513610110541125 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_170368_170496 :
    (∑ n ∈ Ico 170368 170496, mobiusTreeValue 16 mobiusTable1200001 n) = (5 : ℤ) ∧
    (∑ n ∈ Ico 170368 170496, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 170368 170496, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (146621 : ℤ) ∧
    (∑ n ∈ Ico 170368 170496, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (2932492498716127559468560901 : ℤ) := by
  rcases cdemPrefixStats_170368_170432 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_170432_170496 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 170368 ≤ 170432) (by norm_num : 170432 ≤ 170496), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 170368 ≤ 170432) (by norm_num : 170432 ≤ 170496), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 170368 ≤ 170432) (by norm_num : 170432 ≤ 170496), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 170368 ≤ 170432) (by norm_num : 170432 ≤ 170496), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_170240_170496 :
    (∑ n ∈ Ico 170240 170496, mobiusTreeValue 16 mobiusTable1200001 n) = (-8 : ℤ) ∧
    (∑ n ∈ Ico 170240 170496, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (158 : ℕ) ∧
    (∑ n ∈ Ico 170240 170496, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-235032 : ℤ) ∧
    (∑ n ∈ Ico 170240 170496, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-4700733845545927932622254849 : ℤ) := by
  rcases cdemPrefixStats_170240_170368 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_170368_170496 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 170240 ≤ 170368) (by norm_num : 170368 ≤ 170496), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 170240 ≤ 170368) (by norm_num : 170368 ≤ 170496), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 170240 ≤ 170368) (by norm_num : 170368 ≤ 170496), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 170240 ≤ 170368) (by norm_num : 170368 ≤ 170496), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_169984_170496 :
    (∑ n ∈ Ico 169984 170496, mobiusTreeValue 16 mobiusTable1200001 n) = (-3 : ℤ) ∧
    (∑ n ∈ Ico 169984 170496, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (311 : ℕ) ∧
    (∑ n ∈ Ico 169984 170496, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-88004 : ℤ) ∧
    (∑ n ∈ Ico 169984 170496, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-1760205232610710465231467557 : ℤ) := by
  rcases cdemPrefixStats_169984_170240 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_170240_170496 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 169984 ≤ 170240) (by norm_num : 170240 ≤ 170496), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 169984 ≤ 170240) (by norm_num : 170240 ≤ 170496), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 169984 ≤ 170240) (by norm_num : 170240 ≤ 170496), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 169984 ≤ 170240) (by norm_num : 170240 ≤ 170496), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_170496_170560 :
    (∑ n ∈ Ico 170496 170560, mobiusTreeValue 16 mobiusTable1200001 n) = (-5 : ℤ) ∧
    (∑ n ∈ Ico 170496 170560, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 170496 170560, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-146567 : ℤ) ∧
    (∑ n ∈ Ico 170496 170560, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-2931478397158390622005503512 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_170560_170624 :
    (∑ n ∈ Ico 170560 170624, mobiusTreeValue 16 mobiusTable1200001 n) = (6 : ℤ) ∧
    (∑ n ∈ Ico 170560 170624, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 170560 170624, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (175835 : ℤ) ∧
    (∑ n ∈ Ico 170560 170624, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (3516706786531499315029206890 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_170496_170624 :
    (∑ n ∈ Ico 170496 170624, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 170496 170624, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 170496 170624, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (29268 : ℤ) ∧
    (∑ n ∈ Ico 170496 170624, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (585228389373108693023703378 : ℤ) := by
  rcases cdemPrefixStats_170496_170560 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_170560_170624 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 170496 ≤ 170560) (by norm_num : 170560 ≤ 170624), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 170496 ≤ 170560) (by norm_num : 170560 ≤ 170624), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 170496 ≤ 170560) (by norm_num : 170560 ≤ 170624), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 170496 ≤ 170560) (by norm_num : 170560 ≤ 170624), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_170624_170688 :
    (∑ n ∈ Ico 170624 170688, mobiusTreeValue 16 mobiusTable1200001 n) = (-2 : ℤ) ∧
    (∑ n ∈ Ico 170624 170688, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 170624 170688, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-58595 : ℤ) ∧
    (∑ n ∈ Ico 170624 170688, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-1171913988092180743723468755 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_170688_170752 :
    (∑ n ∈ Ico 170688 170752, mobiusTreeValue 16 mobiusTable1200001 n) = (8 : ℤ) ∧
    (∑ n ∈ Ico 170688 170752, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 170688 170752, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (234298 : ℤ) ∧
    (∑ n ∈ Ico 170688 170752, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (4686042471814795997238947483 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_170624_170752 :
    (∑ n ∈ Ico 170624 170752, mobiusTreeValue 16 mobiusTable1200001 n) = (6 : ℤ) ∧
    (∑ n ∈ Ico 170624 170752, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 170624 170752, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (175703 : ℤ) ∧
    (∑ n ∈ Ico 170624 170752, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (3514128483722615253515478728 : ℤ) := by
  rcases cdemPrefixStats_170624_170688 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_170688_170752 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 170624 ≤ 170688) (by norm_num : 170688 ≤ 170752), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 170624 ≤ 170688) (by norm_num : 170688 ≤ 170752), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 170624 ≤ 170688) (by norm_num : 170688 ≤ 170752), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 170624 ≤ 170688) (by norm_num : 170688 ≤ 170752), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_170496_170752 :
    (∑ n ∈ Ico 170496 170752, mobiusTreeValue 16 mobiusTable1200001 n) = (7 : ℤ) ∧
    (∑ n ∈ Ico 170496 170752, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (155 : ℕ) ∧
    (∑ n ∈ Ico 170496 170752, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (204971 : ℤ) ∧
    (∑ n ∈ Ico 170496 170752, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (4099356873095723946539182106 : ℤ) := by
  rcases cdemPrefixStats_170496_170624 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_170624_170752 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 170496 ≤ 170624) (by norm_num : 170624 ≤ 170752), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 170496 ≤ 170624) (by norm_num : 170624 ≤ 170752), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 170496 ≤ 170624) (by norm_num : 170624 ≤ 170752), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 170496 ≤ 170624) (by norm_num : 170624 ≤ 170752), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_170752_170816 :
    (∑ n ∈ Ico 170752 170816, mobiusTreeValue 16 mobiusTable1200001 n) = (-2 : ℤ) ∧
    (∑ n ∈ Ico 170752 170816, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 170752 170816, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-58539 : ℤ) ∧
    (∑ n ∈ Ico 170752 170816, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-1170785378593396965345365922 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_170816_170880 :
    (∑ n ∈ Ico 170816 170880, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 170816 170880, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 170816 170880, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (29229 : ℤ) ∧
    (∑ n ∈ Ico 170816 170880, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (584616736703070217985160277 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_170752_170880 :
    (∑ n ∈ Ico 170752 170880, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 170752 170880, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (75 : ℕ) ∧
    (∑ n ∈ Ico 170752 170880, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-29310 : ℤ) ∧
    (∑ n ∈ Ico 170752 170880, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-586168641890326747360205645 : ℤ) := by
  rcases cdemPrefixStats_170752_170816 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_170816_170880 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 170752 ≤ 170816) (by norm_num : 170816 ≤ 170880), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 170752 ≤ 170816) (by norm_num : 170816 ≤ 170880), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 170752 ≤ 170816) (by norm_num : 170816 ≤ 170880), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 170752 ≤ 170816) (by norm_num : 170816 ≤ 170880), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_170880_170944 :
    (∑ n ∈ Ico 170880 170944, mobiusTreeValue 16 mobiusTable1200001 n) = (4 : ℤ) ∧
    (∑ n ∈ Ico 170880 170944, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (42 : ℕ) ∧
    (∑ n ∈ Ico 170880 170944, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (117020 : ℤ) ∧
    (∑ n ∈ Ico 170880 170944, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (2340437051264054228135844886 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_170944_171008 :
    (∑ n ∈ Ico 170944 171008, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 170944 171008, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 170944 171008, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 170944 171008, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-44477307188278003854499 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_170880_171008 :
    (∑ n ∈ Ico 170880 171008, mobiusTreeValue 16 mobiusTable1200001 n) = (4 : ℤ) ∧
    (∑ n ∈ Ico 170880 171008, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (82 : ℕ) ∧
    (∑ n ∈ Ico 170880 171008, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (117019 : ℤ) ∧
    (∑ n ∈ Ico 170880 171008, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (2340392573956865950131990387 : ℤ) := by
  rcases cdemPrefixStats_170880_170944 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_170944_171008 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 170880 ≤ 170944) (by norm_num : 170944 ≤ 171008), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 170880 ≤ 170944) (by norm_num : 170944 ≤ 171008), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 170880 ≤ 170944) (by norm_num : 170944 ≤ 171008), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 170880 ≤ 170944) (by norm_num : 170944 ≤ 171008), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_170752_171008 :
    (∑ n ∈ Ico 170752 171008, mobiusTreeValue 16 mobiusTable1200001 n) = (3 : ℤ) ∧
    (∑ n ∈ Ico 170752 171008, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (157 : ℕ) ∧
    (∑ n ∈ Ico 170752 171008, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (87709 : ℤ) ∧
    (∑ n ∈ Ico 170752 171008, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1754223932066539202771784742 : ℤ) := by
  rcases cdemPrefixStats_170752_170880 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_170880_171008 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 170752 ≤ 170880) (by norm_num : 170880 ≤ 171008), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 170752 ≤ 170880) (by norm_num : 170880 ≤ 171008), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 170752 ≤ 170880) (by norm_num : 170880 ≤ 171008), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 170752 ≤ 170880) (by norm_num : 170880 ≤ 171008), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_170496_171008 :
    (∑ n ∈ Ico 170496 171008, mobiusTreeValue 16 mobiusTable1200001 n) = (10 : ℤ) ∧
    (∑ n ∈ Ico 170496 171008, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (312 : ℕ) ∧
    (∑ n ∈ Ico 170496 171008, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (292680 : ℤ) ∧
    (∑ n ∈ Ico 170496 171008, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (5853580805162263149310966848 : ℤ) := by
  rcases cdemPrefixStats_170496_170752 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_170752_171008 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 170496 ≤ 170752) (by norm_num : 170752 ≤ 171008), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 170496 ≤ 170752) (by norm_num : 170752 ≤ 171008), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 170496 ≤ 170752) (by norm_num : 170752 ≤ 171008), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 170496 ≤ 170752) (by norm_num : 170752 ≤ 171008), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_169984_171008 :
    (∑ n ∈ Ico 169984 171008, mobiusTreeValue 16 mobiusTable1200001 n) = (7 : ℤ) ∧
    (∑ n ∈ Ico 169984 171008, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (623 : ℕ) ∧
    (∑ n ∈ Ico 169984 171008, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (204676 : ℤ) ∧
    (∑ n ∈ Ico 169984 171008, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (4093375572551552684079499291 : ℤ) := by
  rcases cdemPrefixStats_169984_170496 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_170496_171008 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 169984 ≤ 170496) (by norm_num : 170496 ≤ 171008), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 169984 ≤ 170496) (by norm_num : 170496 ≤ 171008), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 169984 ≤ 170496) (by norm_num : 170496 ≤ 171008), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 169984 ≤ 170496) (by norm_num : 170496 ≤ 171008), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_171008_171072 :
    (∑ n ∈ Ico 171008 171072, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 171008 171072, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 171008 171072, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-29242 : ℤ) ∧
    (∑ n ∈ Ico 171008 171072, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-584897859608139652143083975 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_171072_171136 :
    (∑ n ∈ Ico 171072 171136, mobiusTreeValue 16 mobiusTable1200001 n) = (-2 : ℤ) ∧
    (∑ n ∈ Ico 171072 171136, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 171072 171136, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-58479 : ℤ) ∧
    (∑ n ∈ Ico 171072 171136, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-1169576588276177418154874269 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_171008_171136 :
    (∑ n ∈ Ico 171008 171136, mobiusTreeValue 16 mobiusTable1200001 n) = (-3 : ℤ) ∧
    (∑ n ∈ Ico 171008 171136, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (75 : ℕ) ∧
    (∑ n ∈ Ico 171008 171136, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-87721 : ℤ) ∧
    (∑ n ∈ Ico 171008 171136, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-1754474447884317070297958244 : ℤ) := by
  rcases cdemPrefixStats_171008_171072 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_171072_171136 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 171008 ≤ 171072) (by norm_num : 171072 ≤ 171136), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 171008 ≤ 171072) (by norm_num : 171072 ≤ 171136), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 171008 ≤ 171072) (by norm_num : 171072 ≤ 171136), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 171008 ≤ 171072) (by norm_num : 171072 ≤ 171136), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_171136_171200 :
    (∑ n ∈ Ico 171136 171200, mobiusTreeValue 16 mobiusTable1200001 n) = (4 : ℤ) ∧
    (∑ n ∈ Ico 171136 171200, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 171136 171200, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (116851 : ℤ) ∧
    (∑ n ∈ Ico 171136 171200, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (2337022002192040616855332501 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_171200_171264 :
    (∑ n ∈ Ico 171200 171264, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 171200 171264, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 171200 171264, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (29211 : ℤ) ∧
    (∑ n ∈ Ico 171200 171264, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (584159873395881813656400867 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_171136_171264 :
    (∑ n ∈ Ico 171136 171264, mobiusTreeValue 16 mobiusTable1200001 n) = (5 : ℤ) ∧
    (∑ n ∈ Ico 171136 171264, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 171136 171264, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (146062 : ℤ) ∧
    (∑ n ∈ Ico 171136 171264, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (2921181875587922430511733368 : ℤ) := by
  rcases cdemPrefixStats_171136_171200 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_171200_171264 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 171136 ≤ 171200) (by norm_num : 171200 ≤ 171264), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 171136 ≤ 171200) (by norm_num : 171200 ≤ 171264), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 171136 ≤ 171200) (by norm_num : 171200 ≤ 171264), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 171136 ≤ 171200) (by norm_num : 171200 ≤ 171264), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_171008_171264 :
    (∑ n ∈ Ico 171008 171264, mobiusTreeValue 16 mobiusTable1200001 n) = (2 : ℤ) ∧
    (∑ n ∈ Ico 171008 171264, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (152 : ℕ) ∧
    (∑ n ∈ Ico 171008 171264, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (58341 : ℤ) ∧
    (∑ n ∈ Ico 171008 171264, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1166707427703605360213775124 : ℤ) := by
  rcases cdemPrefixStats_171008_171136 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_171136_171264 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 171008 ≤ 171136) (by norm_num : 171136 ≤ 171264), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 171008 ≤ 171136) (by norm_num : 171136 ≤ 171264), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 171008 ≤ 171136) (by norm_num : 171136 ≤ 171264), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 171008 ≤ 171136) (by norm_num : 171136 ≤ 171264), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_171264_171328 :
    (∑ n ∈ Ico 171264 171328, mobiusTreeValue 16 mobiusTable1200001 n) = (9 : ℤ) ∧
    (∑ n ∈ Ico 171264 171328, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 171264 171328, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (262679 : ℤ) ∧
    (∑ n ∈ Ico 171264 171328, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (5253643985519159267757447114 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_171328_171392 :
    (∑ n ∈ Ico 171328 171392, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 171328 171392, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (35 : ℕ) ∧
    (∑ n ∈ Ico 171328 171392, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (29199 : ℤ) ∧
    (∑ n ∈ Ico 171328 171392, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (583931195563728370227676546 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_171264_171392 :
    (∑ n ∈ Ico 171264 171392, mobiusTreeValue 16 mobiusTable1200001 n) = (10 : ℤ) ∧
    (∑ n ∈ Ico 171264 171392, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (76 : ℕ) ∧
    (∑ n ∈ Ico 171264 171392, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (291878 : ℤ) ∧
    (∑ n ∈ Ico 171264 171392, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (5837575181082887637985123660 : ℤ) := by
  rcases cdemPrefixStats_171264_171328 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_171328_171392 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 171264 ≤ 171328) (by norm_num : 171328 ≤ 171392), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 171264 ≤ 171328) (by norm_num : 171328 ≤ 171392), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 171264 ≤ 171328) (by norm_num : 171328 ≤ 171392), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 171264 ≤ 171328) (by norm_num : 171328 ≤ 171392), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_171392_171456 :
    (∑ n ∈ Ico 171392 171456, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 171392 171456, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 171392 171456, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-29128 : ℤ) ∧
    (∑ n ∈ Ico 171392 171456, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-582549228933400922923111963 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_171456_171520 :
    (∑ n ∈ Ico 171456 171520, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 171456 171520, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 171456 171520, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (0 : ℤ) ∧
    (∑ n ∈ Ico 171456 171520, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (20411249216843459465501 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_171392_171520 :
    (∑ n ∈ Ico 171392 171520, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 171392 171520, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (79 : ℕ) ∧
    (∑ n ∈ Ico 171392 171520, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-29128 : ℤ) ∧
    (∑ n ∈ Ico 171392 171520, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-582528817684184079463646462 : ℤ) := by
  rcases cdemPrefixStats_171392_171456 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_171456_171520 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 171392 ≤ 171456) (by norm_num : 171456 ≤ 171520), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 171392 ≤ 171456) (by norm_num : 171456 ≤ 171520), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 171392 ≤ 171456) (by norm_num : 171456 ≤ 171520), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 171392 ≤ 171456) (by norm_num : 171456 ≤ 171520), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_171264_171520 :
    (∑ n ∈ Ico 171264 171520, mobiusTreeValue 16 mobiusTable1200001 n) = (9 : ℤ) ∧
    (∑ n ∈ Ico 171264 171520, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (155 : ℕ) ∧
    (∑ n ∈ Ico 171264 171520, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (262750 : ℤ) ∧
    (∑ n ∈ Ico 171264 171520, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (5255046363398703558521477198 : ℤ) := by
  rcases cdemPrefixStats_171264_171392 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_171392_171520 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 171264 ≤ 171392) (by norm_num : 171392 ≤ 171520), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 171264 ≤ 171392) (by norm_num : 171392 ≤ 171520), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 171264 ≤ 171392) (by norm_num : 171392 ≤ 171520), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 171264 ≤ 171392) (by norm_num : 171392 ≤ 171520), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_171008_171520 :
    (∑ n ∈ Ico 171008 171520, mobiusTreeValue 16 mobiusTable1200001 n) = (11 : ℤ) ∧
    (∑ n ∈ Ico 171008 171520, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (307 : ℕ) ∧
    (∑ n ∈ Ico 171008 171520, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (321091 : ℤ) ∧
    (∑ n ∈ Ico 171008 171520, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (6421753791102308918735252322 : ℤ) := by
  rcases cdemPrefixStats_171008_171264 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_171264_171520 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 171008 ≤ 171264) (by norm_num : 171264 ≤ 171520), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 171008 ≤ 171264) (by norm_num : 171264 ≤ 171520), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 171008 ≤ 171264) (by norm_num : 171264 ≤ 171520), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 171008 ≤ 171264) (by norm_num : 171264 ≤ 171520), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_171520_171584 :
    (∑ n ∈ Ico 171520 171584, mobiusTreeValue 16 mobiusTable1200001 n) = (-6 : ℤ) ∧
    (∑ n ∈ Ico 171520 171584, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 171520 171584, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-174892 : ℤ) ∧
    (∑ n ∈ Ico 171520 171584, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-3497876023627119045958797969 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_171584_171648 :
    (∑ n ∈ Ico 171584 171648, mobiusTreeValue 16 mobiusTable1200001 n) = (-2 : ℤ) ∧
    (∑ n ∈ Ico 171584 171648, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 171584 171648, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-58275 : ℤ) ∧
    (∑ n ∈ Ico 171584 171648, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-1165494430990791705374119149 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_171520_171648 :
    (∑ n ∈ Ico 171520 171648, mobiusTreeValue 16 mobiusTable1200001 n) = (-8 : ℤ) ∧
    (∑ n ∈ Ico 171520 171648, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (76 : ℕ) ∧
    (∑ n ∈ Ico 171520 171648, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-233167 : ℤ) ∧
    (∑ n ∈ Ico 171520 171648, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-4663370454617910751332917118 : ℤ) := by
  rcases cdemPrefixStats_171520_171584 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_171584_171648 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 171520 ≤ 171584) (by norm_num : 171584 ≤ 171648), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 171520 ≤ 171584) (by norm_num : 171584 ≤ 171648), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 171520 ≤ 171584) (by norm_num : 171584 ≤ 171648), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 171520 ≤ 171584) (by norm_num : 171584 ≤ 171648), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_171648_171712 :
    (∑ n ∈ Ico 171648 171712, mobiusTreeValue 16 mobiusTable1200001 n) = (-11 : ℤ) ∧
    (∑ n ∈ Ico 171648 171712, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 171648 171712, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-320364 : ℤ) ∧
    (∑ n ∈ Ico 171648 171712, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-6407320359015735756324902936 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_171712_171776 :
    (∑ n ∈ Ico 171712 171776, mobiusTreeValue 16 mobiusTable1200001 n) = (-12 : ℤ) ∧
    (∑ n ∈ Ico 171712 171776, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 171712 171776, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-349361 : ℤ) ∧
    (∑ n ∈ Ico 171712 171776, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-6987330276261102281976218558 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_171648_171776 :
    (∑ n ∈ Ico 171648 171776, mobiusTreeValue 16 mobiusTable1200001 n) = (-23 : ℤ) ∧
    (∑ n ∈ Ico 171648 171776, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 171648 171776, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-669725 : ℤ) ∧
    (∑ n ∈ Ico 171648 171776, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-13394650635276838038301121494 : ℤ) := by
  rcases cdemPrefixStats_171648_171712 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_171712_171776 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 171648 ≤ 171712) (by norm_num : 171712 ≤ 171776), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 171648 ≤ 171712) (by norm_num : 171712 ≤ 171776), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 171648 ≤ 171712) (by norm_num : 171712 ≤ 171776), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 171648 ≤ 171712) (by norm_num : 171712 ≤ 171776), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_171520_171776 :
    (∑ n ∈ Ico 171520 171776, mobiusTreeValue 16 mobiusTable1200001 n) = (-31 : ℤ) ∧
    (∑ n ∈ Ico 171520 171776, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (153 : ℕ) ∧
    (∑ n ∈ Ico 171520 171776, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-902892 : ℤ) ∧
    (∑ n ∈ Ico 171520 171776, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-18058021089894748789634038612 : ℤ) := by
  rcases cdemPrefixStats_171520_171648 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_171648_171776 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 171520 ≤ 171648) (by norm_num : 171648 ≤ 171776), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 171520 ≤ 171648) (by norm_num : 171648 ≤ 171776), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 171520 ≤ 171648) (by norm_num : 171648 ≤ 171776), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 171520 ≤ 171648) (by norm_num : 171648 ≤ 171776), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_171776_171840 :
    (∑ n ∈ Ico 171776 171840, mobiusTreeValue 16 mobiusTable1200001 n) = (9 : ℤ) ∧
    (∑ n ∈ Ico 171776 171840, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 171776 171840, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (261932 : ℤ) ∧
    (∑ n ∈ Ico 171776 171840, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (5238714033457831961783717237 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_171840_171904 :
    (∑ n ∈ Ico 171840 171904, mobiusTreeValue 16 mobiusTable1200001 n) = (-4 : ℤ) ∧
    (∑ n ∈ Ico 171840 171904, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 171840 171904, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-116337 : ℤ) ∧
    (∑ n ∈ Ico 171840 171904, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-2326829218017324856436038044 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_171776_171904 :
    (∑ n ∈ Ico 171776 171904, mobiusTreeValue 16 mobiusTable1200001 n) = (5 : ℤ) ∧
    (∑ n ∈ Ico 171776 171904, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (81 : ℕ) ∧
    (∑ n ∈ Ico 171776 171904, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (145595 : ℤ) ∧
    (∑ n ∈ Ico 171776 171904, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (2911884815440507105347679193 : ℤ) := by
  rcases cdemPrefixStats_171776_171840 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_171840_171904 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 171776 ≤ 171840) (by norm_num : 171840 ≤ 171904), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 171776 ≤ 171840) (by norm_num : 171840 ≤ 171904), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 171776 ≤ 171840) (by norm_num : 171840 ≤ 171904), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 171776 ≤ 171840) (by norm_num : 171840 ≤ 171904), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_171904_171968 :
    (∑ n ∈ Ico 171904 171968, mobiusTreeValue 16 mobiusTable1200001 n) = (-5 : ℤ) ∧
    (∑ n ∈ Ico 171904 171968, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 171904 171968, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-145398 : ℤ) ∧
    (∑ n ∈ Ico 171904 171968, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-2908058772677193401452418087 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_171968_172032 :
    (∑ n ∈ Ico 171968 172032, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 171968 172032, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 171968 172032, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (36 : ℤ) ∧
    (∑ n ∈ Ico 171968 172032, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (696351911051090021215373 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_171904_172032 :
    (∑ n ∈ Ico 171904 172032, mobiusTreeValue 16 mobiusTable1200001 n) = (-5 : ℤ) ∧
    (∑ n ∈ Ico 171904 172032, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 171904 172032, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-145362 : ℤ) ∧
    (∑ n ∈ Ico 171904 172032, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-2907362420766142311431202714 : ℤ) := by
  rcases cdemPrefixStats_171904_171968 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_171968_172032 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 171904 ≤ 171968) (by norm_num : 171968 ≤ 172032), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 171904 ≤ 171968) (by norm_num : 171968 ≤ 172032), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 171904 ≤ 171968) (by norm_num : 171968 ≤ 172032), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 171904 ≤ 171968) (by norm_num : 171968 ≤ 172032), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_171776_172032 :
    (∑ n ∈ Ico 171776 172032, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 171776 172032, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (158 : ℕ) ∧
    (∑ n ∈ Ico 171776 172032, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (233 : ℤ) ∧
    (∑ n ∈ Ico 171776 172032, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (4522394674364793916476479 : ℤ) := by
  rcases cdemPrefixStats_171776_171904 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_171904_172032 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 171776 ≤ 171904) (by norm_num : 171904 ≤ 172032), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 171776 ≤ 171904) (by norm_num : 171904 ≤ 172032), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 171776 ≤ 171904) (by norm_num : 171904 ≤ 172032), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 171776 ≤ 171904) (by norm_num : 171904 ≤ 172032), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_171520_172032 :
    (∑ n ∈ Ico 171520 172032, mobiusTreeValue 16 mobiusTable1200001 n) = (-31 : ℤ) ∧
    (∑ n ∈ Ico 171520 172032, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (311 : ℕ) ∧
    (∑ n ∈ Ico 171520 172032, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-902659 : ℤ) ∧
    (∑ n ∈ Ico 171520 172032, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-18053498695220383995717562133 : ℤ) := by
  rcases cdemPrefixStats_171520_171776 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_171776_172032 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 171520 ≤ 171776) (by norm_num : 171776 ≤ 172032), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 171520 ≤ 171776) (by norm_num : 171776 ≤ 172032), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 171520 ≤ 171776) (by norm_num : 171776 ≤ 172032), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 171520 ≤ 171776) (by norm_num : 171776 ≤ 172032), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_171008_172032 :
    (∑ n ∈ Ico 171008 172032, mobiusTreeValue 16 mobiusTable1200001 n) = (-20 : ℤ) ∧
    (∑ n ∈ Ico 171008 172032, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (618 : ℕ) ∧
    (∑ n ∈ Ico 171008 172032, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-581568 : ℤ) ∧
    (∑ n ∈ Ico 171008 172032, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-11631744904118075076982309811 : ℤ) := by
  rcases cdemPrefixStats_171008_171520 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_171520_172032 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 171008 ≤ 171520) (by norm_num : 171520 ≤ 172032), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 171008 ≤ 171520) (by norm_num : 171520 ≤ 172032), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 171008 ≤ 171520) (by norm_num : 171520 ≤ 172032), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 171008 ≤ 171520) (by norm_num : 171520 ≤ 172032), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_169984_172032 :
    (∑ n ∈ Ico 169984 172032, mobiusTreeValue 16 mobiusTable1200001 n) = (-13 : ℤ) ∧
    (∑ n ∈ Ico 169984 172032, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (1241 : ℕ) ∧
    (∑ n ∈ Ico 169984 172032, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-376892 : ℤ) ∧
    (∑ n ∈ Ico 169984 172032, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-7538369331566522392902810520 : ℤ) := by
  rcases cdemPrefixStats_169984_171008 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_171008_172032 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 169984 ≤ 171008) (by norm_num : 171008 ≤ 172032), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 169984 ≤ 171008) (by norm_num : 171008 ≤ 172032), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 169984 ≤ 171008) (by norm_num : 171008 ≤ 172032), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 169984 ≤ 171008) (by norm_num : 171008 ≤ 172032), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_167936_172032 :
    (∑ n ∈ Ico 167936 172032, mobiusTreeValue 16 mobiusTable1200001 n) = (30 : ℤ) ∧
    (∑ n ∈ Ico 167936 172032, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (2490 : ℕ) ∧
    (∑ n ∈ Ico 167936 172032, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (904246 : ℤ) ∧
    (∑ n ∈ Ico 167936 172032, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (18084796258485758567974591146 : ℤ) := by
  rcases cdemPrefixStats_167936_169984 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_169984_172032 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 167936 ≤ 169984) (by norm_num : 169984 ≤ 172032), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 167936 ≤ 169984) (by norm_num : 169984 ≤ 172032), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 167936 ≤ 169984) (by norm_num : 169984 ≤ 172032), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 167936 ≤ 169984) (by norm_num : 169984 ≤ 172032), hR1, hR2] <;> norm_num

theorem cdemPrefixGroup041_checked_complete :
    (∑ n ∈ Ico 167936 172032, mobiusTreeValue 16 mobiusTable1200001 n) = (30 : ℤ) ∧
    (∑ n ∈ Ico 167936 172032, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (2490 : ℕ) ∧
    (∑ n ∈ Ico 167936 172032, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (904246 : ℤ) ∧
    (∑ n ∈ Ico 167936 172032, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (18084796258485758567974591146 : ℤ) := cdemPrefixStats_167936_172032
end Helfgott
#print axioms Helfgott.cdemPrefixGroup041_checked_complete

open Helfgott Finset
open scoped BigOperators

theorem solution :
    (∑ n ∈ Ico 167936 172032, mobiusTreeValue 16 mobiusTable1200001 n) = (30 : ℤ) ∧
    (∑ n ∈ Ico 167936 172032, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (2490 : ℕ) ∧
    (∑ n ∈ Ico 167936 172032, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (904246 : ℤ) ∧
    (∑ n ∈ Ico 167936 172032, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (18084796258485758567974591146 : ℤ) := Helfgott.cdemPrefixGroup041_checked_complete
#print axioms solution
