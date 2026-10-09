-- Prove2me | solution 1 for Helfgott.cdemPrefixGroup044_checked
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-09T02:51:07.666099+00:00
-- url     : https://prove2.me/submissions/858a3214-990a-486a-9dba-9766e8d307d4

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
private theorem cdemPrefixStats_180224_180288 :
    (∑ n ∈ Ico 180224 180288, mobiusTreeValue 16 mobiusTable1200001 n) = (-3 : ℤ) ∧
    (∑ n ∈ Ico 180224 180288, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 180224 180288, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-83193 : ℤ) ∧
    (∑ n ∈ Ico 180224 180288, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-1663942676853393321647151525 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_180288_180352 :
    (∑ n ∈ Ico 180288 180352, mobiusTreeValue 16 mobiusTable1200001 n) = (4 : ℤ) ∧
    (∑ n ∈ Ico 180288 180352, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 180288 180352, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (110890 : ℤ) ∧
    (∑ n ∈ Ico 180288 180352, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (2217823455751831955010053659 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_180224_180352 :
    (∑ n ∈ Ico 180224 180352, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 180224 180352, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 180224 180352, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (27697 : ℤ) ∧
    (∑ n ∈ Ico 180224 180352, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (553880778898438633362902134 : ℤ) := by
  rcases cdemPrefixStats_180224_180288 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_180288_180352 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 180224 ≤ 180288) (by norm_num : 180288 ≤ 180352), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 180224 ≤ 180288) (by norm_num : 180288 ≤ 180352), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 180224 ≤ 180288) (by norm_num : 180288 ≤ 180352), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 180224 ≤ 180288) (by norm_num : 180288 ≤ 180352), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_180352_180416 :
    (∑ n ∈ Ico 180352 180416, mobiusTreeValue 16 mobiusTable1200001 n) = (3 : ℤ) ∧
    (∑ n ∈ Ico 180352 180416, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 180352 180416, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (83120 : ℤ) ∧
    (∑ n ∈ Ico 180352 180416, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1662408730443224312939702421 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_180416_180480 :
    (∑ n ∈ Ico 180416 180480, mobiusTreeValue 16 mobiusTable1200001 n) = (7 : ℤ) ∧
    (∑ n ∈ Ico 180416 180480, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 180416 180480, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (193941 : ℤ) ∧
    (∑ n ∈ Ico 180416 180480, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (3878942203619745015784637904 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_180352_180480 :
    (∑ n ∈ Ico 180352 180480, mobiusTreeValue 16 mobiusTable1200001 n) = (10 : ℤ) ∧
    (∑ n ∈ Ico 180352 180480, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 180352 180480, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (277061 : ℤ) ∧
    (∑ n ∈ Ico 180352 180480, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (5541350934062969328724340325 : ℤ) := by
  rcases cdemPrefixStats_180352_180416 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_180416_180480 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 180352 ≤ 180416) (by norm_num : 180416 ≤ 180480), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 180352 ≤ 180416) (by norm_num : 180416 ≤ 180480), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 180352 ≤ 180416) (by norm_num : 180416 ≤ 180480), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 180352 ≤ 180416) (by norm_num : 180416 ≤ 180480), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_180224_180480 :
    (∑ n ∈ Ico 180224 180480, mobiusTreeValue 16 mobiusTable1200001 n) = (11 : ℤ) ∧
    (∑ n ∈ Ico 180224 180480, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (155 : ℕ) ∧
    (∑ n ∈ Ico 180224 180480, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (304758 : ℤ) ∧
    (∑ n ∈ Ico 180224 180480, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (6095231712961407962087242459 : ℤ) := by
  rcases cdemPrefixStats_180224_180352 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_180352_180480 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 180224 ≤ 180352) (by norm_num : 180352 ≤ 180480), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 180224 ≤ 180352) (by norm_num : 180352 ≤ 180480), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 180224 ≤ 180352) (by norm_num : 180352 ≤ 180480), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 180224 ≤ 180352) (by norm_num : 180352 ≤ 180480), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_180480_180544 :
    (∑ n ∈ Ico 180480 180544, mobiusTreeValue 16 mobiusTable1200001 n) = (-4 : ℤ) ∧
    (∑ n ∈ Ico 180480 180544, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (42 : ℕ) ∧
    (∑ n ∈ Ico 180480 180544, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-110771 : ℤ) ∧
    (∑ n ∈ Ico 180480 180544, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-2215452677963346141494376935 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_180544_180608 :
    (∑ n ∈ Ico 180544 180608, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 180544 180608, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 180544 180608, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-27683 : ℤ) ∧
    (∑ n ∈ Ico 180544 180608, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-553666896144734314097223631 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_180480_180608 :
    (∑ n ∈ Ico 180480 180608, mobiusTreeValue 16 mobiusTable1200001 n) = (-5 : ℤ) ∧
    (∑ n ∈ Ico 180480 180608, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (81 : ℕ) ∧
    (∑ n ∈ Ico 180480 180608, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-138454 : ℤ) ∧
    (∑ n ∈ Ico 180480 180608, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-2769119574108080455591600566 : ℤ) := by
  rcases cdemPrefixStats_180480_180544 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_180544_180608 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 180480 ≤ 180544) (by norm_num : 180544 ≤ 180608), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 180480 ≤ 180544) (by norm_num : 180544 ≤ 180608), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 180480 ≤ 180544) (by norm_num : 180544 ≤ 180608), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 180480 ≤ 180544) (by norm_num : 180544 ≤ 180608), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_180608_180672 :
    (∑ n ∈ Ico 180608 180672, mobiusTreeValue 16 mobiusTable1200001 n) = (-5 : ℤ) ∧
    (∑ n ∈ Ico 180608 180672, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 180608 180672, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-138377 : ℤ) ∧
    (∑ n ∈ Ico 180608 180672, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-2767614491733958619939265957 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_180672_180736 :
    (∑ n ∈ Ico 180672 180736, mobiusTreeValue 16 mobiusTable1200001 n) = (-4 : ℤ) ∧
    (∑ n ∈ Ico 180672 180736, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (42 : ℕ) ∧
    (∑ n ∈ Ico 180672 180736, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-110669 : ℤ) ∧
    (∑ n ∈ Ico 180672 180736, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-2213445373318095163077489680 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_180608_180736 :
    (∑ n ∈ Ico 180608 180736, mobiusTreeValue 16 mobiusTable1200001 n) = (-9 : ℤ) ∧
    (∑ n ∈ Ico 180608 180736, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (79 : ℕ) ∧
    (∑ n ∈ Ico 180608 180736, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-249046 : ℤ) ∧
    (∑ n ∈ Ico 180608 180736, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-4981059865052053783016755637 : ℤ) := by
  rcases cdemPrefixStats_180608_180672 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_180672_180736 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 180608 ≤ 180672) (by norm_num : 180672 ≤ 180736), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 180608 ≤ 180672) (by norm_num : 180672 ≤ 180736), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 180608 ≤ 180672) (by norm_num : 180672 ≤ 180736), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 180608 ≤ 180672) (by norm_num : 180672 ≤ 180736), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_180480_180736 :
    (∑ n ∈ Ico 180480 180736, mobiusTreeValue 16 mobiusTable1200001 n) = (-14 : ℤ) ∧
    (∑ n ∈ Ico 180480 180736, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (160 : ℕ) ∧
    (∑ n ∈ Ico 180480 180736, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-387500 : ℤ) ∧
    (∑ n ∈ Ico 180480 180736, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-7750179439160134238608356203 : ℤ) := by
  rcases cdemPrefixStats_180480_180608 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_180608_180736 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 180480 ≤ 180608) (by norm_num : 180608 ≤ 180736), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 180480 ≤ 180608) (by norm_num : 180608 ≤ 180736), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 180480 ≤ 180608) (by norm_num : 180608 ≤ 180736), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 180480 ≤ 180608) (by norm_num : 180608 ≤ 180736), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_180224_180736 :
    (∑ n ∈ Ico 180224 180736, mobiusTreeValue 16 mobiusTable1200001 n) = (-3 : ℤ) ∧
    (∑ n ∈ Ico 180224 180736, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (315 : ℕ) ∧
    (∑ n ∈ Ico 180224 180736, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-82742 : ℤ) ∧
    (∑ n ∈ Ico 180224 180736, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-1654947726198726276521113744 : ℤ) := by
  rcases cdemPrefixStats_180224_180480 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_180480_180736 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 180224 ≤ 180480) (by norm_num : 180480 ≤ 180736), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 180224 ≤ 180480) (by norm_num : 180480 ≤ 180736), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 180224 ≤ 180480) (by norm_num : 180480 ≤ 180736), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 180224 ≤ 180480) (by norm_num : 180480 ≤ 180736), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_180736_180800 :
    (∑ n ∈ Ico 180736 180800, mobiusTreeValue 16 mobiusTable1200001 n) = (10 : ℤ) ∧
    (∑ n ∈ Ico 180736 180800, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 180736 180800, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (276596 : ℤ) ∧
    (∑ n ∈ Ico 180736 180800, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (5532004613905254760363945660 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_180800_180864 :
    (∑ n ∈ Ico 180800 180864, mobiusTreeValue 16 mobiusTable1200001 n) = (-4 : ℤ) ∧
    (∑ n ∈ Ico 180800 180864, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (36 : ℕ) ∧
    (∑ n ∈ Ico 180800 180864, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-110592 : ℤ) ∧
    (∑ n ∈ Ico 180800 180864, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-2211826602664046813170933901 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_180736_180864 :
    (∑ n ∈ Ico 180736 180864, mobiusTreeValue 16 mobiusTable1200001 n) = (6 : ℤ) ∧
    (∑ n ∈ Ico 180736 180864, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (76 : ℕ) ∧
    (∑ n ∈ Ico 180736 180864, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (166004 : ℤ) ∧
    (∑ n ∈ Ico 180736 180864, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (3320178011241207947193011759 : ℤ) := by
  rcases cdemPrefixStats_180736_180800 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_180800_180864 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 180736 ≤ 180800) (by norm_num : 180800 ≤ 180864), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 180736 ≤ 180800) (by norm_num : 180800 ≤ 180864), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 180736 ≤ 180800) (by norm_num : 180800 ≤ 180864), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 180736 ≤ 180800) (by norm_num : 180800 ≤ 180864), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_180864_180928 :
    (∑ n ∈ Ico 180864 180928, mobiusTreeValue 16 mobiusTable1200001 n) = (4 : ℤ) ∧
    (∑ n ∈ Ico 180864 180928, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 180864 180928, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (110566 : ℤ) ∧
    (∑ n ∈ Ico 180864 180928, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (2211395612887866956783854483 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_180928_180992 :
    (∑ n ∈ Ico 180928 180992, mobiusTreeValue 16 mobiusTable1200001 n) = (-3 : ℤ) ∧
    (∑ n ∈ Ico 180928 180992, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 180928 180992, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-82887 : ℤ) ∧
    (∑ n ∈ Ico 180928 180992, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-1657812730298325320083948476 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_180864_180992 :
    (∑ n ∈ Ico 180864 180992, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 180864 180992, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 180864 180992, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (27679 : ℤ) ∧
    (∑ n ∈ Ico 180864 180992, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (553582882589541636699906007 : ℤ) := by
  rcases cdemPrefixStats_180864_180928 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_180928_180992 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 180864 ≤ 180928) (by norm_num : 180928 ≤ 180992), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 180864 ≤ 180928) (by norm_num : 180928 ≤ 180992), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 180864 ≤ 180928) (by norm_num : 180928 ≤ 180992), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 180864 ≤ 180928) (by norm_num : 180928 ≤ 180992), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_180736_180992 :
    (∑ n ∈ Ico 180736 180992, mobiusTreeValue 16 mobiusTable1200001 n) = (7 : ℤ) ∧
    (∑ n ∈ Ico 180736 180992, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (153 : ℕ) ∧
    (∑ n ∈ Ico 180736 180992, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (193683 : ℤ) ∧
    (∑ n ∈ Ico 180736 180992, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (3873760893830749583892917766 : ℤ) := by
  rcases cdemPrefixStats_180736_180864 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_180864_180992 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 180736 ≤ 180864) (by norm_num : 180864 ≤ 180992), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 180736 ≤ 180864) (by norm_num : 180864 ≤ 180992), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 180736 ≤ 180864) (by norm_num : 180864 ≤ 180992), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 180736 ≤ 180864) (by norm_num : 180864 ≤ 180992), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_180992_181056 :
    (∑ n ∈ Ico 180992 181056, mobiusTreeValue 16 mobiusTable1200001 n) = (3 : ℤ) ∧
    (∑ n ∈ Ico 180992 181056, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 180992 181056, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (82875 : ℤ) ∧
    (∑ n ∈ Ico 180992 181056, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1657550130739486566471319926 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_181056_181120 :
    (∑ n ∈ Ico 181056 181120, mobiusTreeValue 16 mobiusTable1200001 n) = (6 : ℤ) ∧
    (∑ n ∈ Ico 181056 181120, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (42 : ℕ) ∧
    (∑ n ∈ Ico 181056 181120, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (165656 : ℤ) ∧
    (∑ n ∈ Ico 181056 181120, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (3313178265136508729607261781 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_180992_181120 :
    (∑ n ∈ Ico 180992 181120, mobiusTreeValue 16 mobiusTable1200001 n) = (9 : ℤ) ∧
    (∑ n ∈ Ico 180992 181120, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (81 : ℕ) ∧
    (∑ n ∈ Ico 180992 181120, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (248531 : ℤ) ∧
    (∑ n ∈ Ico 180992 181120, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (4970728395875995296078581707 : ℤ) := by
  rcases cdemPrefixStats_180992_181056 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_181056_181120 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 180992 ≤ 181056) (by norm_num : 181056 ≤ 181120), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 180992 ≤ 181056) (by norm_num : 181056 ≤ 181120), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 180992 ≤ 181056) (by norm_num : 181056 ≤ 181120), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 180992 ≤ 181056) (by norm_num : 181056 ≤ 181120), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_181120_181184 :
    (∑ n ∈ Ico 181120 181184, mobiusTreeValue 16 mobiusTable1200001 n) = (-3 : ℤ) ∧
    (∑ n ∈ Ico 181120 181184, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 181120 181184, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-82798 : ℤ) ∧
    (∑ n ∈ Ico 181120 181184, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-1655973401630172347092344684 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_181184_181248 :
    (∑ n ∈ Ico 181184 181248, mobiusTreeValue 16 mobiusTable1200001 n) = (-4 : ℤ) ∧
    (∑ n ∈ Ico 181184 181248, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 181184 181248, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-110375 : ℤ) ∧
    (∑ n ∈ Ico 181184 181248, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-2207581601446963541894568669 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_181120_181248 :
    (∑ n ∈ Ico 181120 181248, mobiusTreeValue 16 mobiusTable1200001 n) = (-7 : ℤ) ∧
    (∑ n ∈ Ico 181120 181248, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (75 : ℕ) ∧
    (∑ n ∈ Ico 181120 181248, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-193173 : ℤ) ∧
    (∑ n ∈ Ico 181120 181248, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-3863555003077135888986913353 : ℤ) := by
  rcases cdemPrefixStats_181120_181184 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_181184_181248 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 181120 ≤ 181184) (by norm_num : 181184 ≤ 181248), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 181120 ≤ 181184) (by norm_num : 181184 ≤ 181248), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 181120 ≤ 181184) (by norm_num : 181184 ≤ 181248), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 181120 ≤ 181184) (by norm_num : 181184 ≤ 181248), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_180992_181248 :
    (∑ n ∈ Ico 180992 181248, mobiusTreeValue 16 mobiusTable1200001 n) = (2 : ℤ) ∧
    (∑ n ∈ Ico 180992 181248, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (156 : ℕ) ∧
    (∑ n ∈ Ico 180992 181248, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (55358 : ℤ) ∧
    (∑ n ∈ Ico 180992 181248, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1107173392798859407091668354 : ℤ) := by
  rcases cdemPrefixStats_180992_181120 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_181120_181248 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 180992 ≤ 181120) (by norm_num : 181120 ≤ 181248), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 180992 ≤ 181120) (by norm_num : 181120 ≤ 181248), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 180992 ≤ 181120) (by norm_num : 181120 ≤ 181248), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 180992 ≤ 181120) (by norm_num : 181120 ≤ 181248), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_180736_181248 :
    (∑ n ∈ Ico 180736 181248, mobiusTreeValue 16 mobiusTable1200001 n) = (9 : ℤ) ∧
    (∑ n ∈ Ico 180736 181248, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (309 : ℕ) ∧
    (∑ n ∈ Ico 180736 181248, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (249041 : ℤ) ∧
    (∑ n ∈ Ico 180736 181248, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (4980934286629608990984586120 : ℤ) := by
  rcases cdemPrefixStats_180736_180992 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_180992_181248 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 180736 ≤ 180992) (by norm_num : 180992 ≤ 181248), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 180736 ≤ 180992) (by norm_num : 180992 ≤ 181248), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 180736 ≤ 180992) (by norm_num : 180992 ≤ 181248), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 180736 ≤ 180992) (by norm_num : 180992 ≤ 181248), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_180224_181248 :
    (∑ n ∈ Ico 180224 181248, mobiusTreeValue 16 mobiusTable1200001 n) = (6 : ℤ) ∧
    (∑ n ∈ Ico 180224 181248, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (624 : ℕ) ∧
    (∑ n ∈ Ico 180224 181248, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (166299 : ℤ) ∧
    (∑ n ∈ Ico 180224 181248, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (3325986560430882714463472376 : ℤ) := by
  rcases cdemPrefixStats_180224_180736 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_180736_181248 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 180224 ≤ 180736) (by norm_num : 180736 ≤ 181248), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 180224 ≤ 180736) (by norm_num : 180736 ≤ 181248), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 180224 ≤ 180736) (by norm_num : 180736 ≤ 181248), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 180224 ≤ 180736) (by norm_num : 180736 ≤ 181248), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_181248_181312 :
    (∑ n ∈ Ico 181248 181312, mobiusTreeValue 16 mobiusTable1200001 n) = (-2 : ℤ) ∧
    (∑ n ∈ Ico 181248 181312, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 181248 181312, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-55138 : ℤ) ∧
    (∑ n ∈ Ico 181248 181312, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-1102781874653849910300748608 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_181312_181376 :
    (∑ n ∈ Ico 181312 181376, mobiusTreeValue 16 mobiusTable1200001 n) = (11 : ℤ) ∧
    (∑ n ∈ Ico 181312 181376, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 181312 181376, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (303274 : ℤ) ∧
    (∑ n ∈ Ico 181312 181376, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (6065658546971243551517827474 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_181248_181376 :
    (∑ n ∈ Ico 181248 181376, mobiusTreeValue 16 mobiusTable1200001 n) = (9 : ℤ) ∧
    (∑ n ∈ Ico 181248 181376, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (79 : ℕ) ∧
    (∑ n ∈ Ico 181248 181376, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (248136 : ℤ) ∧
    (∑ n ∈ Ico 181248 181376, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (4962876672317393641217078866 : ℤ) := by
  rcases cdemPrefixStats_181248_181312 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_181312_181376 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 181248 ≤ 181312) (by norm_num : 181312 ≤ 181376), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 181248 ≤ 181312) (by norm_num : 181312 ≤ 181376), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 181248 ≤ 181312) (by norm_num : 181312 ≤ 181376), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 181248 ≤ 181312) (by norm_num : 181312 ≤ 181376), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_181376_181440 :
    (∑ n ∈ Ico 181376 181440, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 181376 181440, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 181376 181440, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-27566 : ℤ) ∧
    (∑ n ∈ Ico 181376 181440, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-551274048838856988758691605 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_181440_181504 :
    (∑ n ∈ Ico 181440 181504, mobiusTreeValue 16 mobiusTable1200001 n) = (-5 : ℤ) ∧
    (∑ n ∈ Ico 181440 181504, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 181440 181504, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-137769 : ℤ) ∧
    (∑ n ∈ Ico 181440 181504, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-2755385769025350324591317934 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_181376_181504 :
    (∑ n ∈ Ico 181376 181504, mobiusTreeValue 16 mobiusTable1200001 n) = (-6 : ℤ) ∧
    (∑ n ∈ Ico 181376 181504, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 181376 181504, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-165335 : ℤ) ∧
    (∑ n ∈ Ico 181376 181504, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-3306659817864207313350009539 : ℤ) := by
  rcases cdemPrefixStats_181376_181440 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_181440_181504 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 181376 ≤ 181440) (by norm_num : 181440 ≤ 181504), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 181376 ≤ 181440) (by norm_num : 181440 ≤ 181504), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 181376 ≤ 181440) (by norm_num : 181440 ≤ 181504), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 181376 ≤ 181440) (by norm_num : 181440 ≤ 181504), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_181248_181504 :
    (∑ n ∈ Ico 181248 181504, mobiusTreeValue 16 mobiusTable1200001 n) = (3 : ℤ) ∧
    (∑ n ∈ Ico 181248 181504, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (157 : ℕ) ∧
    (∑ n ∈ Ico 181248 181504, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (82801 : ℤ) ∧
    (∑ n ∈ Ico 181248 181504, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1656216854453186327867069327 : ℤ) := by
  rcases cdemPrefixStats_181248_181376 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_181376_181504 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 181248 ≤ 181376) (by norm_num : 181376 ≤ 181504), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 181248 ≤ 181376) (by norm_num : 181376 ≤ 181504), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 181248 ≤ 181376) (by norm_num : 181376 ≤ 181504), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 181248 ≤ 181376) (by norm_num : 181376 ≤ 181504), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_181504_181568 :
    (∑ n ∈ Ico 181504 181568, mobiusTreeValue 16 mobiusTable1200001 n) = (-7 : ℤ) ∧
    (∑ n ∈ Ico 181504 181568, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 181504 181568, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-192808 : ℤ) ∧
    (∑ n ∈ Ico 181504 181568, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-3856187847179768242461108782 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_181568_181632 :
    (∑ n ∈ Ico 181568 181632, mobiusTreeValue 16 mobiusTable1200001 n) = (-3 : ℤ) ∧
    (∑ n ∈ Ico 181568 181632, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 181568 181632, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-82566 : ℤ) ∧
    (∑ n ∈ Ico 181568 181632, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-1651354688247173224835500093 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_181504_181632 :
    (∑ n ∈ Ico 181504 181632, mobiusTreeValue 16 mobiusTable1200001 n) = (-10 : ℤ) ∧
    (∑ n ∈ Ico 181504 181632, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 181504 181632, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-275374 : ℤ) ∧
    (∑ n ∈ Ico 181504 181632, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-5507542535426941467296608875 : ℤ) := by
  rcases cdemPrefixStats_181504_181568 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_181568_181632 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 181504 ≤ 181568) (by norm_num : 181568 ≤ 181632), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 181504 ≤ 181568) (by norm_num : 181568 ≤ 181632), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 181504 ≤ 181568) (by norm_num : 181568 ≤ 181632), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 181504 ≤ 181568) (by norm_num : 181568 ≤ 181632), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_181632_181696 :
    (∑ n ∈ Ico 181632 181696, mobiusTreeValue 16 mobiusTable1200001 n) = (2 : ℤ) ∧
    (∑ n ∈ Ico 181632 181696, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 181632 181696, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (55037 : ℤ) ∧
    (∑ n ∈ Ico 181632 181696, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1100706314752063434454924337 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_181696_181760 :
    (∑ n ∈ Ico 181696 181760, mobiusTreeValue 16 mobiusTable1200001 n) = (-8 : ℤ) ∧
    (∑ n ∈ Ico 181696 181760, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 181696 181760, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-220086 : ℤ) ∧
    (∑ n ∈ Ico 181696 181760, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-4401747533608196271180127932 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_181632_181760 :
    (∑ n ∈ Ico 181632 181760, mobiusTreeValue 16 mobiusTable1200001 n) = (-6 : ℤ) ∧
    (∑ n ∈ Ico 181632 181760, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 181632 181760, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-165049 : ℤ) ∧
    (∑ n ∈ Ico 181632 181760, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-3301041218856132836725203595 : ℤ) := by
  rcases cdemPrefixStats_181632_181696 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_181696_181760 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 181632 ≤ 181696) (by norm_num : 181696 ≤ 181760), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 181632 ≤ 181696) (by norm_num : 181696 ≤ 181760), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 181632 ≤ 181696) (by norm_num : 181696 ≤ 181760), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 181632 ≤ 181696) (by norm_num : 181696 ≤ 181760), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_181504_181760 :
    (∑ n ∈ Ico 181504 181760, mobiusTreeValue 16 mobiusTable1200001 n) = (-16 : ℤ) ∧
    (∑ n ∈ Ico 181504 181760, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (156 : ℕ) ∧
    (∑ n ∈ Ico 181504 181760, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-440423 : ℤ) ∧
    (∑ n ∈ Ico 181504 181760, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-8808583754283074304021812470 : ℤ) := by
  rcases cdemPrefixStats_181504_181632 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_181632_181760 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 181504 ≤ 181632) (by norm_num : 181632 ≤ 181760), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 181504 ≤ 181632) (by norm_num : 181632 ≤ 181760), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 181504 ≤ 181632) (by norm_num : 181632 ≤ 181760), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 181504 ≤ 181632) (by norm_num : 181632 ≤ 181760), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_181248_181760 :
    (∑ n ∈ Ico 181248 181760, mobiusTreeValue 16 mobiusTable1200001 n) = (-13 : ℤ) ∧
    (∑ n ∈ Ico 181248 181760, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (313 : ℕ) ∧
    (∑ n ∈ Ico 181248 181760, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-357622 : ℤ) ∧
    (∑ n ∈ Ico 181248 181760, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-7152366899829887976154743143 : ℤ) := by
  rcases cdemPrefixStats_181248_181504 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_181504_181760 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 181248 ≤ 181504) (by norm_num : 181504 ≤ 181760), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 181248 ≤ 181504) (by norm_num : 181504 ≤ 181760), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 181248 ≤ 181504) (by norm_num : 181504 ≤ 181760), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 181248 ≤ 181504) (by norm_num : 181504 ≤ 181760), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_181760_181824 :
    (∑ n ∈ Ico 181760 181824, mobiusTreeValue 16 mobiusTable1200001 n) = (2 : ℤ) ∧
    (∑ n ∈ Ico 181760 181824, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 181760 181824, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (54970 : ℤ) ∧
    (∑ n ∈ Ico 181760 181824, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1099453409926692428362102782 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_181824_181888 :
    (∑ n ∈ Ico 181824 181888, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 181824 181888, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 181824 181888, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-27485 : ℤ) ∧
    (∑ n ∈ Ico 181824 181888, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-549707274663831197726427194 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_181760_181888 :
    (∑ n ∈ Ico 181760 181888, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 181760 181888, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (79 : ℕ) ∧
    (∑ n ∈ Ico 181760 181888, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (27485 : ℤ) ∧
    (∑ n ∈ Ico 181760 181888, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (549746135262861230635675588 : ℤ) := by
  rcases cdemPrefixStats_181760_181824 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_181824_181888 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 181760 ≤ 181824) (by norm_num : 181824 ≤ 181888), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 181760 ≤ 181824) (by norm_num : 181824 ≤ 181888), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 181760 ≤ 181824) (by norm_num : 181824 ≤ 181888), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 181760 ≤ 181824) (by norm_num : 181824 ≤ 181888), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_181888_181952 :
    (∑ n ∈ Ico 181888 181952, mobiusTreeValue 16 mobiusTable1200001 n) = (-6 : ℤ) ∧
    (∑ n ∈ Ico 181888 181952, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 181888 181952, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-164930 : ℤ) ∧
    (∑ n ∈ Ico 181888 181952, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-3298651582307426692931366286 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_181952_182016 :
    (∑ n ∈ Ico 181952 182016, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 181952 182016, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 181952 182016, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (27486 : ℤ) ∧
    (∑ n ∈ Ico 181952 182016, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (549722252083183571996878783 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_181888_182016 :
    (∑ n ∈ Ico 181888 182016, mobiusTreeValue 16 mobiusTable1200001 n) = (-5 : ℤ) ∧
    (∑ n ∈ Ico 181888 182016, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (79 : ℕ) ∧
    (∑ n ∈ Ico 181888 182016, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-137444 : ℤ) ∧
    (∑ n ∈ Ico 181888 182016, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-2748929330224243120934487503 : ℤ) := by
  rcases cdemPrefixStats_181888_181952 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_181952_182016 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 181888 ≤ 181952) (by norm_num : 181952 ≤ 182016), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 181888 ≤ 181952) (by norm_num : 181952 ≤ 182016), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 181888 ≤ 181952) (by norm_num : 181952 ≤ 182016), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 181888 ≤ 181952) (by norm_num : 181952 ≤ 182016), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_181760_182016 :
    (∑ n ∈ Ico 181760 182016, mobiusTreeValue 16 mobiusTable1200001 n) = (-4 : ℤ) ∧
    (∑ n ∈ Ico 181760 182016, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (158 : ℕ) ∧
    (∑ n ∈ Ico 181760 182016, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-109959 : ℤ) ∧
    (∑ n ∈ Ico 181760 182016, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-2199183194961381890298811915 : ℤ) := by
  rcases cdemPrefixStats_181760_181888 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_181888_182016 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 181760 ≤ 181888) (by norm_num : 181888 ≤ 182016), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 181760 ≤ 181888) (by norm_num : 181888 ≤ 182016), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 181760 ≤ 181888) (by norm_num : 181888 ≤ 182016), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 181760 ≤ 181888) (by norm_num : 181888 ≤ 182016), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_182016_182080 :
    (∑ n ∈ Ico 182016 182080, mobiusTreeValue 16 mobiusTable1200001 n) = (4 : ℤ) ∧
    (∑ n ∈ Ico 182016 182080, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 182016 182080, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (109871 : ℤ) ∧
    (∑ n ∈ Ico 182016 182080, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (2197503405034517020499084401 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_182080_182144 :
    (∑ n ∈ Ico 182080 182144, mobiusTreeValue 16 mobiusTable1200001 n) = (-11 : ℤ) ∧
    (∑ n ∈ Ico 182080 182144, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 182080 182144, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-301998 : ℤ) ∧
    (∑ n ∈ Ico 182080 182144, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-6040036981233124643333485989 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_182016_182144 :
    (∑ n ∈ Ico 182016 182144, mobiusTreeValue 16 mobiusTable1200001 n) = (-7 : ℤ) ∧
    (∑ n ∈ Ico 182016 182144, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (79 : ℕ) ∧
    (∑ n ∈ Ico 182016 182144, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-192127 : ℤ) ∧
    (∑ n ∈ Ico 182016 182144, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-3842533576198607622834401588 : ℤ) := by
  rcases cdemPrefixStats_182016_182080 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_182080_182144 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 182016 ≤ 182080) (by norm_num : 182080 ≤ 182144), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 182016 ≤ 182080) (by norm_num : 182080 ≤ 182144), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 182016 ≤ 182080) (by norm_num : 182080 ≤ 182144), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 182016 ≤ 182080) (by norm_num : 182080 ≤ 182144), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_182144_182208 :
    (∑ n ∈ Ico 182144 182208, mobiusTreeValue 16 mobiusTable1200001 n) = (-3 : ℤ) ∧
    (∑ n ∈ Ico 182144 182208, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 182144 182208, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-82340 : ℤ) ∧
    (∑ n ∈ Ico 182144 182208, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-1646783294779777060254900437 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_182208_182272 :
    (∑ n ∈ Ico 182208 182272, mobiusTreeValue 16 mobiusTable1200001 n) = (4 : ℤ) ∧
    (∑ n ∈ Ico 182208 182272, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 182208 182272, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (109705 : ℤ) ∧
    (∑ n ∈ Ico 182208 182272, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (2194170153103277804641647216 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_182144_182272 :
    (∑ n ∈ Ico 182144 182272, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 182144 182272, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (79 : ℕ) ∧
    (∑ n ∈ Ico 182144 182272, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (27365 : ℤ) ∧
    (∑ n ∈ Ico 182144 182272, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (547386858323500744386746779 : ℤ) := by
  rcases cdemPrefixStats_182144_182208 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_182208_182272 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 182144 ≤ 182208) (by norm_num : 182208 ≤ 182272), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 182144 ≤ 182208) (by norm_num : 182208 ≤ 182272), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 182144 ≤ 182208) (by norm_num : 182208 ≤ 182272), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 182144 ≤ 182208) (by norm_num : 182208 ≤ 182272), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_182016_182272 :
    (∑ n ∈ Ico 182016 182272, mobiusTreeValue 16 mobiusTable1200001 n) = (-6 : ℤ) ∧
    (∑ n ∈ Ico 182016 182272, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (158 : ℕ) ∧
    (∑ n ∈ Ico 182016 182272, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-164762 : ℤ) ∧
    (∑ n ∈ Ico 182016 182272, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-3295146717875106878447654809 : ℤ) := by
  rcases cdemPrefixStats_182016_182144 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_182144_182272 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 182016 ≤ 182144) (by norm_num : 182144 ≤ 182272), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 182016 ≤ 182144) (by norm_num : 182144 ≤ 182272), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 182016 ≤ 182144) (by norm_num : 182144 ≤ 182272), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 182016 ≤ 182144) (by norm_num : 182144 ≤ 182272), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_181760_182272 :
    (∑ n ∈ Ico 181760 182272, mobiusTreeValue 16 mobiusTable1200001 n) = (-10 : ℤ) ∧
    (∑ n ∈ Ico 181760 182272, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (316 : ℕ) ∧
    (∑ n ∈ Ico 181760 182272, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-274721 : ℤ) ∧
    (∑ n ∈ Ico 181760 182272, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-5494329912836488768746466724 : ℤ) := by
  rcases cdemPrefixStats_181760_182016 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_182016_182272 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 181760 ≤ 182016) (by norm_num : 182016 ≤ 182272), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 181760 ≤ 182016) (by norm_num : 182016 ≤ 182272), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 181760 ≤ 182016) (by norm_num : 182016 ≤ 182272), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 181760 ≤ 182016) (by norm_num : 182016 ≤ 182272), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_181248_182272 :
    (∑ n ∈ Ico 181248 182272, mobiusTreeValue 16 mobiusTable1200001 n) = (-23 : ℤ) ∧
    (∑ n ∈ Ico 181248 182272, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (629 : ℕ) ∧
    (∑ n ∈ Ico 181248 182272, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-632343 : ℤ) ∧
    (∑ n ∈ Ico 181248 182272, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-12646696812666376744901209867 : ℤ) := by
  rcases cdemPrefixStats_181248_181760 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_181760_182272 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 181248 ≤ 181760) (by norm_num : 181760 ≤ 182272), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 181248 ≤ 181760) (by norm_num : 181760 ≤ 182272), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 181248 ≤ 181760) (by norm_num : 181760 ≤ 182272), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 181248 ≤ 181760) (by norm_num : 181760 ≤ 182272), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_180224_182272 :
    (∑ n ∈ Ico 180224 182272, mobiusTreeValue 16 mobiusTable1200001 n) = (-17 : ℤ) ∧
    (∑ n ∈ Ico 180224 182272, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (1253 : ℕ) ∧
    (∑ n ∈ Ico 180224 182272, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-466044 : ℤ) ∧
    (∑ n ∈ Ico 180224 182272, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-9320710252235494030437737491 : ℤ) := by
  rcases cdemPrefixStats_180224_181248 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_181248_182272 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 180224 ≤ 181248) (by norm_num : 181248 ≤ 182272), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 180224 ≤ 181248) (by norm_num : 181248 ≤ 182272), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 180224 ≤ 181248) (by norm_num : 181248 ≤ 182272), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 180224 ≤ 181248) (by norm_num : 181248 ≤ 182272), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_182272_182336 :
    (∑ n ∈ Ico 182272 182336, mobiusTreeValue 16 mobiusTable1200001 n) = (8 : ℤ) ∧
    (∑ n ∈ Ico 182272 182336, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 182272 182336, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (219416 : ℤ) ∧
    (∑ n ∈ Ico 182272 182336, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (4388400936760574442591164604 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_182336_182400 :
    (∑ n ∈ Ico 182336 182400, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 182336 182400, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 182336 182400, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-27426 : ℤ) ∧
    (∑ n ∈ Ico 182336 182400, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-548501198901866840193912927 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_182272_182400 :
    (∑ n ∈ Ico 182272 182400, mobiusTreeValue 16 mobiusTable1200001 n) = (7 : ℤ) ∧
    (∑ n ∈ Ico 182272 182400, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (75 : ℕ) ∧
    (∑ n ∈ Ico 182272 182400, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (191990 : ℤ) ∧
    (∑ n ∈ Ico 182272 182400, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (3839899737858707602397251677 : ℤ) := by
  rcases cdemPrefixStats_182272_182336 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_182336_182400 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 182272 ≤ 182336) (by norm_num : 182336 ≤ 182400), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 182272 ≤ 182336) (by norm_num : 182336 ≤ 182400), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 182272 ≤ 182336) (by norm_num : 182336 ≤ 182400), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 182272 ≤ 182336) (by norm_num : 182336 ≤ 182400), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_182400_182464 :
    (∑ n ∈ Ico 182400 182464, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 182400 182464, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 182400 182464, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-27429 : ℤ) ∧
    (∑ n ∈ Ico 182400 182464, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-548651207432115247883744904 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_182464_182528 :
    (∑ n ∈ Ico 182464 182528, mobiusTreeValue 16 mobiusTable1200001 n) = (-6 : ℤ) ∧
    (∑ n ∈ Ico 182464 182528, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 182464 182528, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-164378 : ℤ) ∧
    (∑ n ∈ Ico 182464 182528, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-3287665246459100904826399763 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_182400_182528 :
    (∑ n ∈ Ico 182400 182528, mobiusTreeValue 16 mobiusTable1200001 n) = (-7 : ℤ) ∧
    (∑ n ∈ Ico 182400 182528, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (79 : ℕ) ∧
    (∑ n ∈ Ico 182400 182528, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-191807 : ℤ) ∧
    (∑ n ∈ Ico 182400 182528, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-3836316453891216152710144667 : ℤ) := by
  rcases cdemPrefixStats_182400_182464 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_182464_182528 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 182400 ≤ 182464) (by norm_num : 182464 ≤ 182528), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 182400 ≤ 182464) (by norm_num : 182464 ≤ 182528), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 182400 ≤ 182464) (by norm_num : 182464 ≤ 182528), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 182400 ≤ 182464) (by norm_num : 182464 ≤ 182528), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_182272_182528 :
    (∑ n ∈ Ico 182272 182528, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 182272 182528, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (154 : ℕ) ∧
    (∑ n ∈ Ico 182272 182528, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (183 : ℤ) ∧
    (∑ n ∈ Ico 182272 182528, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (3583283967491449687107010 : ℤ) := by
  rcases cdemPrefixStats_182272_182400 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_182400_182528 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 182272 ≤ 182400) (by norm_num : 182400 ≤ 182528), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 182272 ≤ 182400) (by norm_num : 182400 ≤ 182528), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 182272 ≤ 182400) (by norm_num : 182400 ≤ 182528), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 182272 ≤ 182400) (by norm_num : 182400 ≤ 182528), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_182528_182592 :
    (∑ n ∈ Ico 182528 182592, mobiusTreeValue 16 mobiusTable1200001 n) = (-9 : ℤ) ∧
    (∑ n ∈ Ico 182528 182592, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 182528 182592, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-246515 : ℤ) ∧
    (∑ n ∈ Ico 182528 182592, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-4930339173971121823973898181 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_182592_182656 :
    (∑ n ∈ Ico 182592 182656, mobiusTreeValue 16 mobiusTable1200001 n) = (-7 : ℤ) ∧
    (∑ n ∈ Ico 182592 182656, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 182592 182656, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-191649 : ℤ) ∧
    (∑ n ∈ Ico 182592 182656, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-3833072142667522858561111187 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_182528_182656 :
    (∑ n ∈ Ico 182528 182656, mobiusTreeValue 16 mobiusTable1200001 n) = (-16 : ℤ) ∧
    (∑ n ∈ Ico 182528 182656, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (76 : ℕ) ∧
    (∑ n ∈ Ico 182528 182656, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-438164 : ℤ) ∧
    (∑ n ∈ Ico 182528 182656, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-8763411316638644682535009368 : ℤ) := by
  rcases cdemPrefixStats_182528_182592 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_182592_182656 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 182528 ≤ 182592) (by norm_num : 182592 ≤ 182656), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 182528 ≤ 182592) (by norm_num : 182592 ≤ 182656), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 182528 ≤ 182592) (by norm_num : 182592 ≤ 182656), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 182528 ≤ 182592) (by norm_num : 182592 ≤ 182656), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_182656_182720 :
    (∑ n ∈ Ico 182656 182720, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 182656 182720, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 182656 182720, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (27376 : ℤ) ∧
    (∑ n ∈ Ico 182656 182720, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (547576162034002404275528622 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_182720_182784 :
    (∑ n ∈ Ico 182720 182784, mobiusTreeValue 16 mobiusTable1200001 n) = (14 : ℤ) ∧
    (∑ n ∈ Ico 182720 182784, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 182720 182784, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (383018 : ℤ) ∧
    (∑ n ∈ Ico 182720 182784, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (7660496206597496609407916034 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_182656_182784 :
    (∑ n ∈ Ico 182656 182784, mobiusTreeValue 16 mobiusTable1200001 n) = (15 : ℤ) ∧
    (∑ n ∈ Ico 182656 182784, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 182656 182784, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (410394 : ℤ) ∧
    (∑ n ∈ Ico 182656 182784, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (8208072368631499013683444656 : ℤ) := by
  rcases cdemPrefixStats_182656_182720 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_182720_182784 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 182656 ≤ 182720) (by norm_num : 182720 ≤ 182784), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 182656 ≤ 182720) (by norm_num : 182720 ≤ 182784), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 182656 ≤ 182720) (by norm_num : 182720 ≤ 182784), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 182656 ≤ 182720) (by norm_num : 182720 ≤ 182784), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_182528_182784 :
    (∑ n ∈ Ico 182528 182784, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 182528 182784, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (153 : ℕ) ∧
    (∑ n ∈ Ico 182528 182784, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-27770 : ℤ) ∧
    (∑ n ∈ Ico 182528 182784, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-555338948007145668851564712 : ℤ) := by
  rcases cdemPrefixStats_182528_182656 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_182656_182784 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 182528 ≤ 182656) (by norm_num : 182656 ≤ 182784), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 182528 ≤ 182656) (by norm_num : 182656 ≤ 182784), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 182528 ≤ 182656) (by norm_num : 182656 ≤ 182784), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 182528 ≤ 182656) (by norm_num : 182656 ≤ 182784), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_182272_182784 :
    (∑ n ∈ Ico 182272 182784, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 182272 182784, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (307 : ℕ) ∧
    (∑ n ∈ Ico 182272 182784, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-27587 : ℤ) ∧
    (∑ n ∈ Ico 182272 182784, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-551755664039654219164457702 : ℤ) := by
  rcases cdemPrefixStats_182272_182528 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_182528_182784 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 182272 ≤ 182528) (by norm_num : 182528 ≤ 182784), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 182272 ≤ 182528) (by norm_num : 182528 ≤ 182784), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 182272 ≤ 182528) (by norm_num : 182528 ≤ 182784), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 182272 ≤ 182528) (by norm_num : 182528 ≤ 182784), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_182784_182848 :
    (∑ n ∈ Ico 182784 182848, mobiusTreeValue 16 mobiusTable1200001 n) = (14 : ℤ) ∧
    (∑ n ∈ Ico 182784 182848, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 182784 182848, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (382907 : ℤ) ∧
    (∑ n ∈ Ico 182784 182848, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (7658284286145532933329408248 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_182848_182912 :
    (∑ n ∈ Ico 182848 182912, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 182848 182912, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 182848 182912, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-27334 : ℤ) ∧
    (∑ n ∈ Ico 182848 182912, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-546672053711563143093981323 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_182784_182912 :
    (∑ n ∈ Ico 182784 182912, mobiusTreeValue 16 mobiusTable1200001 n) = (13 : ℤ) ∧
    (∑ n ∈ Ico 182784 182912, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (79 : ℕ) ∧
    (∑ n ∈ Ico 182784 182912, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (355573 : ℤ) ∧
    (∑ n ∈ Ico 182784 182912, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (7111612232433969790235426925 : ℤ) := by
  rcases cdemPrefixStats_182784_182848 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_182848_182912 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 182784 ≤ 182848) (by norm_num : 182848 ≤ 182912), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 182784 ≤ 182848) (by norm_num : 182848 ≤ 182912), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 182784 ≤ 182848) (by norm_num : 182848 ≤ 182912), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 182784 ≤ 182848) (by norm_num : 182848 ≤ 182912), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_182912_182976 :
    (∑ n ∈ Ico 182912 182976, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 182912 182976, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 182912 182976, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (39 : ℤ) ∧
    (∑ n ∈ Ico 182912 182976, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (812693283096929953014145 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_182976_183040 :
    (∑ n ∈ Ico 182976 183040, mobiusTreeValue 16 mobiusTable1200001 n) = (4 : ℤ) ∧
    (∑ n ∈ Ico 182976 183040, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 182976 183040, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (109287 : ℤ) ∧
    (∑ n ∈ Ico 182976 183040, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (2185798361711729511095981636 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_182912_183040 :
    (∑ n ∈ Ico 182912 183040, mobiusTreeValue 16 mobiusTable1200001 n) = (4 : ℤ) ∧
    (∑ n ∈ Ico 182912 183040, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 182912 183040, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (109326 : ℤ) ∧
    (∑ n ∈ Ico 182912 183040, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (2186611054994826441048995781 : ℤ) := by
  rcases cdemPrefixStats_182912_182976 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_182976_183040 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 182912 ≤ 182976) (by norm_num : 182976 ≤ 183040), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 182912 ≤ 182976) (by norm_num : 182976 ≤ 183040), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 182912 ≤ 182976) (by norm_num : 182976 ≤ 183040), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 182912 ≤ 182976) (by norm_num : 182976 ≤ 183040), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_182784_183040 :
    (∑ n ∈ Ico 182784 183040, mobiusTreeValue 16 mobiusTable1200001 n) = (17 : ℤ) ∧
    (∑ n ∈ Ico 182784 183040, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (157 : ℕ) ∧
    (∑ n ∈ Ico 182784 183040, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (464899 : ℤ) ∧
    (∑ n ∈ Ico 182784 183040, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (9298223287428796231284422706 : ℤ) := by
  rcases cdemPrefixStats_182784_182912 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_182912_183040 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 182784 ≤ 182912) (by norm_num : 182912 ≤ 183040), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 182784 ≤ 182912) (by norm_num : 182912 ≤ 183040), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 182784 ≤ 182912) (by norm_num : 182912 ≤ 183040), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 182784 ≤ 182912) (by norm_num : 182912 ≤ 183040), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_183040_183104 :
    (∑ n ∈ Ico 183040 183104, mobiusTreeValue 16 mobiusTable1200001 n) = (-8 : ℤ) ∧
    (∑ n ∈ Ico 183040 183104, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 183040 183104, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-218483 : ℤ) ∧
    (∑ n ∈ Ico 183040 183104, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-4369749149435243075632065427 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_183104_183168 :
    (∑ n ∈ Ico 183104 183168, mobiusTreeValue 16 mobiusTable1200001 n) = (11 : ℤ) ∧
    (∑ n ∈ Ico 183104 183168, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 183104 183168, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (300317 : ℤ) ∧
    (∑ n ∈ Ico 183104 183168, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (6006399532150904330432233277 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_183040_183168 :
    (∑ n ∈ Ico 183040 183168, mobiusTreeValue 16 mobiusTable1200001 n) = (3 : ℤ) ∧
    (∑ n ∈ Ico 183040 183168, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (79 : ℕ) ∧
    (∑ n ∈ Ico 183040 183168, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (81834 : ℤ) ∧
    (∑ n ∈ Ico 183040 183168, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1636650382715661254800167850 : ℤ) := by
  rcases cdemPrefixStats_183040_183104 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_183104_183168 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 183040 ≤ 183104) (by norm_num : 183104 ≤ 183168), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 183040 ≤ 183104) (by norm_num : 183104 ≤ 183168), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 183040 ≤ 183104) (by norm_num : 183104 ≤ 183168), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 183040 ≤ 183104) (by norm_num : 183104 ≤ 183168), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_183168_183232 :
    (∑ n ∈ Ico 183168 183232, mobiusTreeValue 16 mobiusTable1200001 n) = (2 : ℤ) ∧
    (∑ n ∈ Ico 183168 183232, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (36 : ℕ) ∧
    (∑ n ∈ Ico 183168 183232, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (54579 : ℤ) ∧
    (∑ n ∈ Ico 183168 183232, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1091589886882515519913878493 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_183232_183296 :
    (∑ n ∈ Ico 183232 183296, mobiusTreeValue 16 mobiusTable1200001 n) = (-9 : ℤ) ∧
    (∑ n ∈ Ico 183232 183296, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 183232 183296, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-245537 : ℤ) ∧
    (∑ n ∈ Ico 183232 183296, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-4910841066946087335991684629 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_183168_183296 :
    (∑ n ∈ Ico 183168 183296, mobiusTreeValue 16 mobiusTable1200001 n) = (-7 : ℤ) ∧
    (∑ n ∈ Ico 183168 183296, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 183168 183296, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-190958 : ℤ) ∧
    (∑ n ∈ Ico 183168 183296, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-3819251180063571816077806136 : ℤ) := by
  rcases cdemPrefixStats_183168_183232 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_183232_183296 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 183168 ≤ 183232) (by norm_num : 183232 ≤ 183296), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 183168 ≤ 183232) (by norm_num : 183232 ≤ 183296), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 183168 ≤ 183232) (by norm_num : 183232 ≤ 183296), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 183168 ≤ 183232) (by norm_num : 183232 ≤ 183296), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_183040_183296 :
    (∑ n ∈ Ico 183040 183296, mobiusTreeValue 16 mobiusTable1200001 n) = (-4 : ℤ) ∧
    (∑ n ∈ Ico 183040 183296, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (156 : ℕ) ∧
    (∑ n ∈ Ico 183040 183296, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-109124 : ℤ) ∧
    (∑ n ∈ Ico 183040 183296, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-2182600797347910561277638286 : ℤ) := by
  rcases cdemPrefixStats_183040_183168 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_183168_183296 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 183040 ≤ 183168) (by norm_num : 183168 ≤ 183296), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 183040 ≤ 183168) (by norm_num : 183168 ≤ 183296), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 183040 ≤ 183168) (by norm_num : 183168 ≤ 183296), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 183040 ≤ 183168) (by norm_num : 183168 ≤ 183296), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_182784_183296 :
    (∑ n ∈ Ico 182784 183296, mobiusTreeValue 16 mobiusTable1200001 n) = (13 : ℤ) ∧
    (∑ n ∈ Ico 182784 183296, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (313 : ℕ) ∧
    (∑ n ∈ Ico 182784 183296, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (355775 : ℤ) ∧
    (∑ n ∈ Ico 182784 183296, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (7115622490080885670006784420 : ℤ) := by
  rcases cdemPrefixStats_182784_183040 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_183040_183296 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 182784 ≤ 183040) (by norm_num : 183040 ≤ 183296), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 182784 ≤ 183040) (by norm_num : 183040 ≤ 183296), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 182784 ≤ 183040) (by norm_num : 183040 ≤ 183296), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 182784 ≤ 183040) (by norm_num : 183040 ≤ 183296), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_182272_183296 :
    (∑ n ∈ Ico 182272 183296, mobiusTreeValue 16 mobiusTable1200001 n) = (12 : ℤ) ∧
    (∑ n ∈ Ico 182272 183296, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (620 : ℕ) ∧
    (∑ n ∈ Ico 182272 183296, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (328188 : ℤ) ∧
    (∑ n ∈ Ico 182272 183296, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (6563866826041231450842326718 : ℤ) := by
  rcases cdemPrefixStats_182272_182784 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_182784_183296 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 182272 ≤ 182784) (by norm_num : 182784 ≤ 183296), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 182272 ≤ 182784) (by norm_num : 182784 ≤ 183296), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 182272 ≤ 182784) (by norm_num : 182784 ≤ 183296), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 182272 ≤ 182784) (by norm_num : 182784 ≤ 183296), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_183296_183360 :
    (∑ n ∈ Ico 183296 183360, mobiusTreeValue 16 mobiusTable1200001 n) = (-14 : ℤ) ∧
    (∑ n ∈ Ico 183296 183360, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (36 : ℕ) ∧
    (∑ n ∈ Ico 183296 183360, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-381838 : ℤ) ∧
    (∑ n ∈ Ico 183296 183360, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-7636901253934466678092117870 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_183360_183424 :
    (∑ n ∈ Ico 183360 183424, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 183360 183424, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 183360 183424, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (27248 : ℤ) ∧
    (∑ n ∈ Ico 183360 183424, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (544979785826739784664052821 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_183296_183424 :
    (∑ n ∈ Ico 183296 183424, mobiusTreeValue 16 mobiusTable1200001 n) = (-13 : ℤ) ∧
    (∑ n ∈ Ico 183296 183424, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 183296 183424, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-354590 : ℤ) ∧
    (∑ n ∈ Ico 183296 183424, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-7091921468107726893428065049 : ℤ) := by
  rcases cdemPrefixStats_183296_183360 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_183360_183424 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 183296 ≤ 183360) (by norm_num : 183360 ≤ 183424), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 183296 ≤ 183360) (by norm_num : 183360 ≤ 183424), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 183296 ≤ 183360) (by norm_num : 183360 ≤ 183424), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 183296 ≤ 183360) (by norm_num : 183360 ≤ 183424), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_183424_183488 :
    (∑ n ∈ Ico 183424 183488, mobiusTreeValue 16 mobiusTable1200001 n) = (-8 : ℤ) ∧
    (∑ n ∈ Ico 183424 183488, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 183424 183488, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-218028 : ℤ) ∧
    (∑ n ∈ Ico 183424 183488, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-4360659273250480033811990301 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_183488_183552 :
    (∑ n ∈ Ico 183488 183552, mobiusTreeValue 16 mobiusTable1200001 n) = (-5 : ℤ) ∧
    (∑ n ∈ Ico 183488 183552, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 183488 183552, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-136236 : ℤ) ∧
    (∑ n ∈ Ico 183488 183552, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-2724727324036502330201243143 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_183424_183552 :
    (∑ n ∈ Ico 183424 183552, mobiusTreeValue 16 mobiusTable1200001 n) = (-13 : ℤ) ∧
    (∑ n ∈ Ico 183424 183552, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (75 : ℕ) ∧
    (∑ n ∈ Ico 183424 183552, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-354264 : ℤ) ∧
    (∑ n ∈ Ico 183424 183552, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-7085386597286982364013233444 : ℤ) := by
  rcases cdemPrefixStats_183424_183488 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_183488_183552 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 183424 ≤ 183488) (by norm_num : 183488 ≤ 183552), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 183424 ≤ 183488) (by norm_num : 183488 ≤ 183552), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 183424 ≤ 183488) (by norm_num : 183488 ≤ 183552), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 183424 ≤ 183488) (by norm_num : 183488 ≤ 183552), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_183296_183552 :
    (∑ n ∈ Ico 183296 183552, mobiusTreeValue 16 mobiusTable1200001 n) = (-26 : ℤ) ∧
    (∑ n ∈ Ico 183296 183552, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (152 : ℕ) ∧
    (∑ n ∈ Ico 183296 183552, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-708854 : ℤ) ∧
    (∑ n ∈ Ico 183296 183552, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-14177308065394709257441298493 : ℤ) := by
  rcases cdemPrefixStats_183296_183424 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_183424_183552 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 183296 ≤ 183424) (by norm_num : 183424 ≤ 183552), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 183296 ≤ 183424) (by norm_num : 183424 ≤ 183552), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 183296 ≤ 183424) (by norm_num : 183424 ≤ 183552), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 183296 ≤ 183424) (by norm_num : 183424 ≤ 183552), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_183552_183616 :
    (∑ n ∈ Ico 183552 183616, mobiusTreeValue 16 mobiusTable1200001 n) = (-6 : ℤ) ∧
    (∑ n ∈ Ico 183552 183616, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 183552 183616, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-163422 : ℤ) ∧
    (∑ n ∈ Ico 183552 183616, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-3268531633964847667530914548 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_183616_183680 :
    (∑ n ∈ Ico 183616 183680, mobiusTreeValue 16 mobiusTable1200001 n) = (7 : ℤ) ∧
    (∑ n ∈ Ico 183616 183680, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 183616 183680, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (190597 : ℤ) ∧
    (∑ n ∈ Ico 183616 183680, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (3811986589832639267793059629 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_183552_183680 :
    (∑ n ∈ Ico 183552 183680, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 183552 183680, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 183552 183680, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (27175 : ℤ) ∧
    (∑ n ∈ Ico 183552 183680, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (543454955867791600262145081 : ℤ) := by
  rcases cdemPrefixStats_183552_183616 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_183616_183680 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 183552 ≤ 183616) (by norm_num : 183616 ≤ 183680), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 183552 ≤ 183616) (by norm_num : 183616 ≤ 183680), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 183552 ≤ 183616) (by norm_num : 183616 ≤ 183680), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 183552 ≤ 183616) (by norm_num : 183616 ≤ 183680), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_183680_183744 :
    (∑ n ∈ Ico 183680 183744, mobiusTreeValue 16 mobiusTable1200001 n) = (5 : ℤ) ∧
    (∑ n ∈ Ico 183680 183744, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 183680 183744, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (136035 : ℤ) ∧
    (∑ n ∈ Ico 183680 183744, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (2720747631757249801882306326 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_183744_183808 :
    (∑ n ∈ Ico 183744 183808, mobiusTreeValue 16 mobiusTable1200001 n) = (-4 : ℤ) ∧
    (∑ n ∈ Ico 183744 183808, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 183744 183808, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-108812 : ℤ) ∧
    (∑ n ∈ Ico 183744 183808, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-2176281470430584208078078087 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_183680_183808 :
    (∑ n ∈ Ico 183680 183808, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 183680 183808, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 183680 183808, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (27223 : ℤ) ∧
    (∑ n ∈ Ico 183680 183808, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (544466161326665593804228239 : ℤ) := by
  rcases cdemPrefixStats_183680_183744 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_183744_183808 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 183680 ≤ 183744) (by norm_num : 183744 ≤ 183808), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 183680 ≤ 183744) (by norm_num : 183744 ≤ 183808), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 183680 ≤ 183744) (by norm_num : 183744 ≤ 183808), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 183680 ≤ 183744) (by norm_num : 183744 ≤ 183808), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_183552_183808 :
    (∑ n ∈ Ico 183552 183808, mobiusTreeValue 16 mobiusTable1200001 n) = (2 : ℤ) ∧
    (∑ n ∈ Ico 183552 183808, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (154 : ℕ) ∧
    (∑ n ∈ Ico 183552 183808, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (54398 : ℤ) ∧
    (∑ n ∈ Ico 183552 183808, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1087921117194457194066373320 : ℤ) := by
  rcases cdemPrefixStats_183552_183680 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_183680_183808 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 183552 ≤ 183680) (by norm_num : 183680 ≤ 183808), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 183552 ≤ 183680) (by norm_num : 183680 ≤ 183808), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 183552 ≤ 183680) (by norm_num : 183680 ≤ 183808), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 183552 ≤ 183680) (by norm_num : 183680 ≤ 183808), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_183296_183808 :
    (∑ n ∈ Ico 183296 183808, mobiusTreeValue 16 mobiusTable1200001 n) = (-24 : ℤ) ∧
    (∑ n ∈ Ico 183296 183808, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (306 : ℕ) ∧
    (∑ n ∈ Ico 183296 183808, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-654456 : ℤ) ∧
    (∑ n ∈ Ico 183296 183808, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-13089386948200252063374925173 : ℤ) := by
  rcases cdemPrefixStats_183296_183552 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_183552_183808 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 183296 ≤ 183552) (by norm_num : 183552 ≤ 183808), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 183296 ≤ 183552) (by norm_num : 183552 ≤ 183808), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 183296 ≤ 183552) (by norm_num : 183552 ≤ 183808), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 183296 ≤ 183552) (by norm_num : 183552 ≤ 183808), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_183808_183872 :
    (∑ n ∈ Ico 183808 183872, mobiusTreeValue 16 mobiusTable1200001 n) = (-2 : ℤ) ∧
    (∑ n ∈ Ico 183808 183872, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (42 : ℕ) ∧
    (∑ n ∈ Ico 183808 183872, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-54421 : ℤ) ∧
    (∑ n ∈ Ico 183808 183872, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-1088444054500939013963014812 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_183872_183936 :
    (∑ n ∈ Ico 183872 183936, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 183872 183936, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 183872 183936, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (27180 : ℤ) ∧
    (∑ n ∈ Ico 183872 183936, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (543655516697293509339294405 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_183808_183936 :
    (∑ n ∈ Ico 183808 183936, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 183808 183936, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (83 : ℕ) ∧
    (∑ n ∈ Ico 183808 183936, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-27241 : ℤ) ∧
    (∑ n ∈ Ico 183808 183936, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-544788537803645504623720407 : ℤ) := by
  rcases cdemPrefixStats_183808_183872 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_183872_183936 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 183808 ≤ 183872) (by norm_num : 183872 ≤ 183936), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 183808 ≤ 183872) (by norm_num : 183872 ≤ 183936), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 183808 ≤ 183872) (by norm_num : 183872 ≤ 183936), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 183808 ≤ 183872) (by norm_num : 183872 ≤ 183936), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_183936_184000 :
    (∑ n ∈ Ico 183936 184000, mobiusTreeValue 16 mobiusTable1200001 n) = (-5 : ℤ) ∧
    (∑ n ∈ Ico 183936 184000, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 183936 184000, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-135879 : ℤ) ∧
    (∑ n ∈ Ico 183936 184000, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-2717630521742458482631192382 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_184000_184064 :
    (∑ n ∈ Ico 184000 184064, mobiusTreeValue 16 mobiusTable1200001 n) = (-10 : ℤ) ∧
    (∑ n ∈ Ico 184000 184064, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 184000 184064, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-271668 : ℤ) ∧
    (∑ n ∈ Ico 184000 184064, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-5433483363892574503746131387 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_183936_184064 :
    (∑ n ∈ Ico 183936 184064, mobiusTreeValue 16 mobiusTable1200001 n) = (-15 : ℤ) ∧
    (∑ n ∈ Ico 183936 184064, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (79 : ℕ) ∧
    (∑ n ∈ Ico 183936 184064, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-407547 : ℤ) ∧
    (∑ n ∈ Ico 183936 184064, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-8151113885635032986377323769 : ℤ) := by
  rcases cdemPrefixStats_183936_184000 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_184000_184064 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 183936 ≤ 184000) (by norm_num : 184000 ≤ 184064), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 183936 ≤ 184000) (by norm_num : 184000 ≤ 184064), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 183936 ≤ 184000) (by norm_num : 184000 ≤ 184064), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 183936 ≤ 184000) (by norm_num : 184000 ≤ 184064), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_183808_184064 :
    (∑ n ∈ Ico 183808 184064, mobiusTreeValue 16 mobiusTable1200001 n) = (-16 : ℤ) ∧
    (∑ n ∈ Ico 183808 184064, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (162 : ℕ) ∧
    (∑ n ∈ Ico 183808 184064, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-434788 : ℤ) ∧
    (∑ n ∈ Ico 183808 184064, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-8695902423438678491001044176 : ℤ) := by
  rcases cdemPrefixStats_183808_183936 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_183936_184064 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 183808 ≤ 183936) (by norm_num : 183936 ≤ 184064), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 183808 ≤ 183936) (by norm_num : 183936 ≤ 184064), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 183808 ≤ 183936) (by norm_num : 183936 ≤ 184064), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 183808 ≤ 183936) (by norm_num : 183936 ≤ 184064), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_184064_184128 :
    (∑ n ∈ Ico 184064 184128, mobiusTreeValue 16 mobiusTable1200001 n) = (5 : ℤ) ∧
    (∑ n ∈ Ico 184064 184128, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 184064 184128, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (135817 : ℤ) ∧
    (∑ n ∈ Ico 184064 184128, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (2716422786461278730084051215 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_184128_184192 :
    (∑ n ∈ Ico 184128 184192, mobiusTreeValue 16 mobiusTable1200001 n) = (-3 : ℤ) ∧
    (∑ n ∈ Ico 184128 184192, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 184128 184192, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-81449 : ℤ) ∧
    (∑ n ∈ Ico 184128 184192, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-1628985875208663122992709478 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_184064_184192 :
    (∑ n ∈ Ico 184064 184192, mobiusTreeValue 16 mobiusTable1200001 n) = (2 : ℤ) ∧
    (∑ n ∈ Ico 184064 184192, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (76 : ℕ) ∧
    (∑ n ∈ Ico 184064 184192, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (54368 : ℤ) ∧
    (∑ n ∈ Ico 184064 184192, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1087436911252615607091341737 : ℤ) := by
  rcases cdemPrefixStats_184064_184128 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_184128_184192 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 184064 ≤ 184128) (by norm_num : 184128 ≤ 184192), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 184064 ≤ 184128) (by norm_num : 184128 ≤ 184192), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 184064 ≤ 184128) (by norm_num : 184128 ≤ 184192), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 184064 ≤ 184128) (by norm_num : 184128 ≤ 184192), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_184192_184256 :
    (∑ n ∈ Ico 184192 184256, mobiusTreeValue 16 mobiusTable1200001 n) = (10 : ℤ) ∧
    (∑ n ∈ Ico 184192 184256, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 184192 184256, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (271411 : ℤ) ∧
    (∑ n ∈ Ico 184192 184256, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (5428315883077834200384016643 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_184256_184320 :
    (∑ n ∈ Ico 184256 184320, mobiusTreeValue 16 mobiusTable1200001 n) = (-10 : ℤ) ∧
    (∑ n ∈ Ico 184256 184320, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 184256 184320, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-271329 : ℤ) ∧
    (∑ n ∈ Ico 184256 184320, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-5426689814114984200796579136 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_184192_184320 :
    (∑ n ∈ Ico 184192 184320, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 184192 184320, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (80 : ℕ) ∧
    (∑ n ∈ Ico 184192 184320, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (82 : ℤ) ∧
    (∑ n ∈ Ico 184192 184320, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1626068962849999587437507 : ℤ) := by
  rcases cdemPrefixStats_184192_184256 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_184256_184320 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 184192 ≤ 184256) (by norm_num : 184256 ≤ 184320), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 184192 ≤ 184256) (by norm_num : 184256 ≤ 184320), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 184192 ≤ 184256) (by norm_num : 184256 ≤ 184320), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 184192 ≤ 184256) (by norm_num : 184256 ≤ 184320), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_184064_184320 :
    (∑ n ∈ Ico 184064 184320, mobiusTreeValue 16 mobiusTable1200001 n) = (2 : ℤ) ∧
    (∑ n ∈ Ico 184064 184320, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (156 : ℕ) ∧
    (∑ n ∈ Ico 184064 184320, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (54450 : ℤ) ∧
    (∑ n ∈ Ico 184064 184320, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1089062980215465606678779244 : ℤ) := by
  rcases cdemPrefixStats_184064_184192 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_184192_184320 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 184064 ≤ 184192) (by norm_num : 184192 ≤ 184320), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 184064 ≤ 184192) (by norm_num : 184192 ≤ 184320), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 184064 ≤ 184192) (by norm_num : 184192 ≤ 184320), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 184064 ≤ 184192) (by norm_num : 184192 ≤ 184320), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_183808_184320 :
    (∑ n ∈ Ico 183808 184320, mobiusTreeValue 16 mobiusTable1200001 n) = (-14 : ℤ) ∧
    (∑ n ∈ Ico 183808 184320, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (318 : ℕ) ∧
    (∑ n ∈ Ico 183808 184320, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-380338 : ℤ) ∧
    (∑ n ∈ Ico 183808 184320, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-7606839443223212884322264932 : ℤ) := by
  rcases cdemPrefixStats_183808_184064 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_184064_184320 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 183808 ≤ 184064) (by norm_num : 184064 ≤ 184320), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 183808 ≤ 184064) (by norm_num : 184064 ≤ 184320), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 183808 ≤ 184064) (by norm_num : 184064 ≤ 184320), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 183808 ≤ 184064) (by norm_num : 184064 ≤ 184320), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_183296_184320 :
    (∑ n ∈ Ico 183296 184320, mobiusTreeValue 16 mobiusTable1200001 n) = (-38 : ℤ) ∧
    (∑ n ∈ Ico 183296 184320, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (624 : ℕ) ∧
    (∑ n ∈ Ico 183296 184320, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-1034794 : ℤ) ∧
    (∑ n ∈ Ico 183296 184320, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-20696226391423464947697190105 : ℤ) := by
  rcases cdemPrefixStats_183296_183808 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_183808_184320 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 183296 ≤ 183808) (by norm_num : 183808 ≤ 184320), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 183296 ≤ 183808) (by norm_num : 183808 ≤ 184320), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 183296 ≤ 183808) (by norm_num : 183808 ≤ 184320), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 183296 ≤ 183808) (by norm_num : 183808 ≤ 184320), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_182272_184320 :
    (∑ n ∈ Ico 182272 184320, mobiusTreeValue 16 mobiusTable1200001 n) = (-26 : ℤ) ∧
    (∑ n ∈ Ico 182272 184320, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (1244 : ℕ) ∧
    (∑ n ∈ Ico 182272 184320, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-706606 : ℤ) ∧
    (∑ n ∈ Ico 182272 184320, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-14132359565382233496854863387 : ℤ) := by
  rcases cdemPrefixStats_182272_183296 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_183296_184320 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 182272 ≤ 183296) (by norm_num : 183296 ≤ 184320), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 182272 ≤ 183296) (by norm_num : 183296 ≤ 184320), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 182272 ≤ 183296) (by norm_num : 183296 ≤ 184320), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 182272 ≤ 183296) (by norm_num : 183296 ≤ 184320), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_180224_184320 :
    (∑ n ∈ Ico 180224 184320, mobiusTreeValue 16 mobiusTable1200001 n) = (-43 : ℤ) ∧
    (∑ n ∈ Ico 180224 184320, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (2497 : ℕ) ∧
    (∑ n ∈ Ico 180224 184320, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-1172650 : ℤ) ∧
    (∑ n ∈ Ico 180224 184320, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-23453069817617727527292600878 : ℤ) := by
  rcases cdemPrefixStats_180224_182272 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_182272_184320 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 180224 ≤ 182272) (by norm_num : 182272 ≤ 184320), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 180224 ≤ 182272) (by norm_num : 182272 ≤ 184320), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 180224 ≤ 182272) (by norm_num : 182272 ≤ 184320), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 180224 ≤ 182272) (by norm_num : 182272 ≤ 184320), hR1, hR2] <;> norm_num

theorem cdemPrefixGroup044_checked_complete :
    (∑ n ∈ Ico 180224 184320, mobiusTreeValue 16 mobiusTable1200001 n) = (-43 : ℤ) ∧
    (∑ n ∈ Ico 180224 184320, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (2497 : ℕ) ∧
    (∑ n ∈ Ico 180224 184320, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-1172650 : ℤ) ∧
    (∑ n ∈ Ico 180224 184320, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-23453069817617727527292600878 : ℤ) := cdemPrefixStats_180224_184320
end Helfgott
#print axioms Helfgott.cdemPrefixGroup044_checked_complete

open Helfgott Finset
open scoped BigOperators

theorem solution :
    (∑ n ∈ Ico 180224 184320, mobiusTreeValue 16 mobiusTable1200001 n) = (-43 : ℤ) ∧
    (∑ n ∈ Ico 180224 184320, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (2497 : ℕ) ∧
    (∑ n ∈ Ico 180224 184320, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-1172650 : ℤ) ∧
    (∑ n ∈ Ico 180224 184320, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-23453069817617727527292600878 : ℤ) := Helfgott.cdemPrefixGroup044_checked_complete
#print axioms solution
