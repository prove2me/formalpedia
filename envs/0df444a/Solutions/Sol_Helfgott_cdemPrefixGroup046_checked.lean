-- Prove2me | solution 1 for Helfgott.cdemPrefixGroup046_checked
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-09T02:57:17.446285+00:00
-- url     : https://prove2.me/submissions/c932c799-4ffe-4e67-acb8-f4836183b19e

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
private theorem cdemPrefixStats_188416_188480 :
    (∑ n ∈ Ico 188416 188480, mobiusTreeValue 16 mobiusTable1200001 n) = (2 : ℤ) ∧
    (∑ n ∈ Ico 188416 188480, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 188416 188480, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (53020 : ℤ) ∧
    (∑ n ∈ Ico 188416 188480, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1060444690415640177182418913 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_188480_188544 :
    (∑ n ∈ Ico 188480 188544, mobiusTreeValue 16 mobiusTable1200001 n) = (2 : ℤ) ∧
    (∑ n ∈ Ico 188480 188544, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 188480 188544, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (53037 : ℤ) ∧
    (∑ n ∈ Ico 188480 188544, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1060816589671040430604389396 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_188416_188544 :
    (∑ n ∈ Ico 188416 188544, mobiusTreeValue 16 mobiusTable1200001 n) = (4 : ℤ) ∧
    (∑ n ∈ Ico 188416 188544, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (76 : ℕ) ∧
    (∑ n ∈ Ico 188416 188544, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (106057 : ℤ) ∧
    (∑ n ∈ Ico 188416 188544, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (2121261280086680607786808309 : ℤ) := by
  rcases cdemPrefixStats_188416_188480 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_188480_188544 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 188416 ≤ 188480) (by norm_num : 188480 ≤ 188544), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 188416 ≤ 188480) (by norm_num : 188480 ≤ 188544), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 188416 ≤ 188480) (by norm_num : 188480 ≤ 188544), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 188416 ≤ 188480) (by norm_num : 188480 ≤ 188544), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_188544_188608 :
    (∑ n ∈ Ico 188544 188608, mobiusTreeValue 16 mobiusTable1200001 n) = (2 : ℤ) ∧
    (∑ n ∈ Ico 188544 188608, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 188544 188608, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (53031 : ℤ) ∧
    (∑ n ∈ Ico 188544 188608, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1060650623674295733944566792 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_188608_188672 :
    (∑ n ∈ Ico 188608 188672, mobiusTreeValue 16 mobiusTable1200001 n) = (5 : ℤ) ∧
    (∑ n ∈ Ico 188608 188672, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 188608 188672, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (132531 : ℤ) ∧
    (∑ n ∈ Ico 188608 188672, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (2650635656361284255310790128 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_188544_188672 :
    (∑ n ∈ Ico 188544 188672, mobiusTreeValue 16 mobiusTable1200001 n) = (7 : ℤ) ∧
    (∑ n ∈ Ico 188544 188672, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (79 : ℕ) ∧
    (∑ n ∈ Ico 188544 188672, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (185562 : ℤ) ∧
    (∑ n ∈ Ico 188544 188672, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (3711286280035579989255356920 : ℤ) := by
  rcases cdemPrefixStats_188544_188608 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_188608_188672 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 188544 ≤ 188608) (by norm_num : 188608 ≤ 188672), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 188544 ≤ 188608) (by norm_num : 188608 ≤ 188672), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 188544 ≤ 188608) (by norm_num : 188608 ≤ 188672), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 188544 ≤ 188608) (by norm_num : 188608 ≤ 188672), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_188416_188672 :
    (∑ n ∈ Ico 188416 188672, mobiusTreeValue 16 mobiusTable1200001 n) = (11 : ℤ) ∧
    (∑ n ∈ Ico 188416 188672, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (155 : ℕ) ∧
    (∑ n ∈ Ico 188416 188672, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (291619 : ℤ) ∧
    (∑ n ∈ Ico 188416 188672, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (5832547560122260597042165229 : ℤ) := by
  rcases cdemPrefixStats_188416_188544 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_188544_188672 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 188416 ≤ 188544) (by norm_num : 188544 ≤ 188672), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 188416 ≤ 188544) (by norm_num : 188544 ≤ 188672), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 188416 ≤ 188544) (by norm_num : 188544 ≤ 188672), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 188416 ≤ 188544) (by norm_num : 188544 ≤ 188672), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_188672_188736 :
    (∑ n ∈ Ico 188672 188736, mobiusTreeValue 16 mobiusTable1200001 n) = (-9 : ℤ) ∧
    (∑ n ∈ Ico 188672 188736, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 188672 188736, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-238487 : ℤ) ∧
    (∑ n ∈ Ico 188672 188736, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-4769809641609513283894194292 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_188736_188800 :
    (∑ n ∈ Ico 188736 188800, mobiusTreeValue 16 mobiusTable1200001 n) = (7 : ℤ) ∧
    (∑ n ∈ Ico 188736 188800, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 188736 188800, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (185409 : ℤ) ∧
    (∑ n ∈ Ico 188736 188800, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (3708196766858105662737564440 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_188672_188800 :
    (∑ n ∈ Ico 188672 188800, mobiusTreeValue 16 mobiusTable1200001 n) = (-2 : ℤ) ∧
    (∑ n ∈ Ico 188672 188800, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 188672 188800, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-53078 : ℤ) ∧
    (∑ n ∈ Ico 188672 188800, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-1061612874751407621156629852 : ℤ) := by
  rcases cdemPrefixStats_188672_188736 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_188736_188800 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 188672 ≤ 188736) (by norm_num : 188736 ≤ 188800), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 188672 ≤ 188736) (by norm_num : 188736 ≤ 188800), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 188672 ≤ 188736) (by norm_num : 188736 ≤ 188800), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 188672 ≤ 188736) (by norm_num : 188736 ≤ 188800), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_188800_188864 :
    (∑ n ∈ Ico 188800 188864, mobiusTreeValue 16 mobiusTable1200001 n) = (-10 : ℤ) ∧
    (∑ n ∈ Ico 188800 188864, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 188800 188864, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-264759 : ℤ) ∧
    (∑ n ∈ Ico 188800 188864, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-5295280755285667933722169801 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_188864_188928 :
    (∑ n ∈ Ico 188864 188928, mobiusTreeValue 16 mobiusTable1200001 n) = (5 : ℤ) ∧
    (∑ n ∈ Ico 188864 188928, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 188864 188928, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (132349 : ℤ) ∧
    (∑ n ∈ Ico 188864 188928, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (2647032054567589783809254692 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_188800_188928 :
    (∑ n ∈ Ico 188800 188928, mobiusTreeValue 16 mobiusTable1200001 n) = (-5 : ℤ) ∧
    (∑ n ∈ Ico 188800 188928, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (75 : ℕ) ∧
    (∑ n ∈ Ico 188800 188928, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-132410 : ℤ) ∧
    (∑ n ∈ Ico 188800 188928, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-2648248700718078149912915109 : ℤ) := by
  rcases cdemPrefixStats_188800_188864 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_188864_188928 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 188800 ≤ 188864) (by norm_num : 188864 ≤ 188928), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 188800 ≤ 188864) (by norm_num : 188864 ≤ 188928), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 188800 ≤ 188864) (by norm_num : 188864 ≤ 188928), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 188800 ≤ 188864) (by norm_num : 188864 ≤ 188928), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_188672_188928 :
    (∑ n ∈ Ico 188672 188928, mobiusTreeValue 16 mobiusTable1200001 n) = (-7 : ℤ) ∧
    (∑ n ∈ Ico 188672 188928, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (153 : ℕ) ∧
    (∑ n ∈ Ico 188672 188928, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-185488 : ℤ) ∧
    (∑ n ∈ Ico 188672 188928, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-3709861575469485771069544961 : ℤ) := by
  rcases cdemPrefixStats_188672_188800 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_188800_188928 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 188672 ≤ 188800) (by norm_num : 188800 ≤ 188928), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 188672 ≤ 188800) (by norm_num : 188800 ≤ 188928), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 188672 ≤ 188800) (by norm_num : 188800 ≤ 188928), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 188672 ≤ 188800) (by norm_num : 188800 ≤ 188928), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_188416_188928 :
    (∑ n ∈ Ico 188416 188928, mobiusTreeValue 16 mobiusTable1200001 n) = (4 : ℤ) ∧
    (∑ n ∈ Ico 188416 188928, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (308 : ℕ) ∧
    (∑ n ∈ Ico 188416 188928, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (106131 : ℤ) ∧
    (∑ n ∈ Ico 188416 188928, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (2122685984652774825972620268 : ℤ) := by
  rcases cdemPrefixStats_188416_188672 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_188672_188928 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 188416 ≤ 188672) (by norm_num : 188672 ≤ 188928), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 188416 ≤ 188672) (by norm_num : 188672 ≤ 188928), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 188416 ≤ 188672) (by norm_num : 188672 ≤ 188928), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 188416 ≤ 188672) (by norm_num : 188672 ≤ 188928), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_188928_188992 :
    (∑ n ∈ Ico 188928 188992, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 188928 188992, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 188928 188992, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-26472 : ℤ) ∧
    (∑ n ∈ Ico 188928 188992, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-529450611918448691195292988 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_188992_189056 :
    (∑ n ∈ Ico 188992 189056, mobiusTreeValue 16 mobiusTable1200001 n) = (4 : ℤ) ∧
    (∑ n ∈ Ico 188992 189056, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (36 : ℕ) ∧
    (∑ n ∈ Ico 188992 189056, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (105790 : ℤ) ∧
    (∑ n ∈ Ico 188992 189056, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (2115892744188922831281711591 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_188928_189056 :
    (∑ n ∈ Ico 188928 189056, mobiusTreeValue 16 mobiusTable1200001 n) = (3 : ℤ) ∧
    (∑ n ∈ Ico 188928 189056, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (75 : ℕ) ∧
    (∑ n ∈ Ico 188928 189056, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (79318 : ℤ) ∧
    (∑ n ∈ Ico 188928 189056, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1586442132270474140086418603 : ℤ) := by
  rcases cdemPrefixStats_188928_188992 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_188992_189056 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 188928 ≤ 188992) (by norm_num : 188992 ≤ 189056), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 188928 ≤ 188992) (by norm_num : 188992 ≤ 189056), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 188928 ≤ 188992) (by norm_num : 188992 ≤ 189056), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 188928 ≤ 188992) (by norm_num : 188992 ≤ 189056), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_189056_189120 :
    (∑ n ∈ Ico 189056 189120, mobiusTreeValue 16 mobiusTable1200001 n) = (16 : ℤ) ∧
    (∑ n ∈ Ico 189056 189120, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 189056 189120, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (423079 : ℤ) ∧
    (∑ n ∈ Ico 189056 189120, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (8461766613476641347545900746 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_189120_189184 :
    (∑ n ∈ Ico 189120 189184, mobiusTreeValue 16 mobiusTable1200001 n) = (-5 : ℤ) ∧
    (∑ n ∈ Ico 189120 189184, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 189120 189184, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-132167 : ℤ) ∧
    (∑ n ∈ Ico 189120 189184, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-2643359987470318600745582743 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_189056_189184 :
    (∑ n ∈ Ico 189056 189184, mobiusTreeValue 16 mobiusTable1200001 n) = (11 : ℤ) ∧
    (∑ n ∈ Ico 189056 189184, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (79 : ℕ) ∧
    (∑ n ∈ Ico 189056 189184, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (290912 : ℤ) ∧
    (∑ n ∈ Ico 189056 189184, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (5818406626006322746800318003 : ℤ) := by
  rcases cdemPrefixStats_189056_189120 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_189120_189184 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 189056 ≤ 189120) (by norm_num : 189120 ≤ 189184), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 189056 ≤ 189120) (by norm_num : 189120 ≤ 189184), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 189056 ≤ 189120) (by norm_num : 189120 ≤ 189184), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 189056 ≤ 189120) (by norm_num : 189120 ≤ 189184), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_188928_189184 :
    (∑ n ∈ Ico 188928 189184, mobiusTreeValue 16 mobiusTable1200001 n) = (14 : ℤ) ∧
    (∑ n ∈ Ico 188928 189184, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (154 : ℕ) ∧
    (∑ n ∈ Ico 188928 189184, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (370230 : ℤ) ∧
    (∑ n ∈ Ico 188928 189184, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (7404848758276796886886736606 : ℤ) := by
  rcases cdemPrefixStats_188928_189056 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_189056_189184 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 188928 ≤ 189056) (by norm_num : 189056 ≤ 189184), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 188928 ≤ 189056) (by norm_num : 189056 ≤ 189184), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 188928 ≤ 189056) (by norm_num : 189056 ≤ 189184), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 188928 ≤ 189056) (by norm_num : 189056 ≤ 189184), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_189184_189248 :
    (∑ n ∈ Ico 189184 189248, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 189184 189248, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 189184 189248, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-26446 : ℤ) ∧
    (∑ n ∈ Ico 189184 189248, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-528887592930685101185754896 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_189248_189312 :
    (∑ n ∈ Ico 189248 189312, mobiusTreeValue 16 mobiusTable1200001 n) = (5 : ℤ) ∧
    (∑ n ∈ Ico 189248 189312, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 189248 189312, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (132041 : ℤ) ∧
    (∑ n ∈ Ico 189248 189312, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (2640880201341125769481063040 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_189184_189312 :
    (∑ n ∈ Ico 189184 189312, mobiusTreeValue 16 mobiusTable1200001 n) = (4 : ℤ) ∧
    (∑ n ∈ Ico 189184 189312, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (80 : ℕ) ∧
    (∑ n ∈ Ico 189184 189312, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (105595 : ℤ) ∧
    (∑ n ∈ Ico 189184 189312, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (2111992608410440668295308144 : ℤ) := by
  rcases cdemPrefixStats_189184_189248 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_189248_189312 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 189184 ≤ 189248) (by norm_num : 189248 ≤ 189312), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 189184 ≤ 189248) (by norm_num : 189248 ≤ 189312), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 189184 ≤ 189248) (by norm_num : 189248 ≤ 189312), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 189184 ≤ 189248) (by norm_num : 189248 ≤ 189312), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_189312_189376 :
    (∑ n ∈ Ico 189312 189376, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 189312 189376, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 189312 189376, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-14 : ℤ) ∧
    (∑ n ∈ Ico 189312 189376, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-206363569812787952520241 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_189376_189440 :
    (∑ n ∈ Ico 189376 189440, mobiusTreeValue 16 mobiusTable1200001 n) = (-9 : ℤ) ∧
    (∑ n ∈ Ico 189376 189440, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 189376 189440, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-237570 : ℤ) ∧
    (∑ n ∈ Ico 189376 189440, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-4751505131938153293064549491 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_189312_189440 :
    (∑ n ∈ Ico 189312 189440, mobiusTreeValue 16 mobiusTable1200001 n) = (-9 : ℤ) ∧
    (∑ n ∈ Ico 189312 189440, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 189312 189440, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-237584 : ℤ) ∧
    (∑ n ∈ Ico 189312 189440, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-4751711495507966081017069732 : ℤ) := by
  rcases cdemPrefixStats_189312_189376 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_189376_189440 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 189312 ≤ 189376) (by norm_num : 189376 ≤ 189440), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 189312 ≤ 189376) (by norm_num : 189376 ≤ 189440), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 189312 ≤ 189376) (by norm_num : 189376 ≤ 189440), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 189312 ≤ 189376) (by norm_num : 189376 ≤ 189440), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_189184_189440 :
    (∑ n ∈ Ico 189184 189440, mobiusTreeValue 16 mobiusTable1200001 n) = (-5 : ℤ) ∧
    (∑ n ∈ Ico 189184 189440, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (157 : ℕ) ∧
    (∑ n ∈ Ico 189184 189440, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-131989 : ℤ) ∧
    (∑ n ∈ Ico 189184 189440, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-2639718887097525412721761588 : ℤ) := by
  rcases cdemPrefixStats_189184_189312 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_189312_189440 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 189184 ≤ 189312) (by norm_num : 189312 ≤ 189440), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 189184 ≤ 189312) (by norm_num : 189312 ≤ 189440), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 189184 ≤ 189312) (by norm_num : 189312 ≤ 189440), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 189184 ≤ 189312) (by norm_num : 189312 ≤ 189440), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_188928_189440 :
    (∑ n ∈ Ico 188928 189440, mobiusTreeValue 16 mobiusTable1200001 n) = (9 : ℤ) ∧
    (∑ n ∈ Ico 188928 189440, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (311 : ℕ) ∧
    (∑ n ∈ Ico 188928 189440, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (238241 : ℤ) ∧
    (∑ n ∈ Ico 188928 189440, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (4765129871179271474164975018 : ℤ) := by
  rcases cdemPrefixStats_188928_189184 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_189184_189440 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 188928 ≤ 189184) (by norm_num : 189184 ≤ 189440), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 188928 ≤ 189184) (by norm_num : 189184 ≤ 189440), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 188928 ≤ 189184) (by norm_num : 189184 ≤ 189440), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 188928 ≤ 189184) (by norm_num : 189184 ≤ 189440), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_188416_189440 :
    (∑ n ∈ Ico 188416 189440, mobiusTreeValue 16 mobiusTable1200001 n) = (13 : ℤ) ∧
    (∑ n ∈ Ico 188416 189440, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (619 : ℕ) ∧
    (∑ n ∈ Ico 188416 189440, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (344372 : ℤ) ∧
    (∑ n ∈ Ico 188416 189440, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (6887815855832046300137595286 : ℤ) := by
  rcases cdemPrefixStats_188416_188928 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_188928_189440 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 188416 ≤ 188928) (by norm_num : 188928 ≤ 189440), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 188416 ≤ 188928) (by norm_num : 188928 ≤ 189440), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 188416 ≤ 188928) (by norm_num : 188928 ≤ 189440), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 188416 ≤ 188928) (by norm_num : 188928 ≤ 189440), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_189440_189504 :
    (∑ n ∈ Ico 189440 189504, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 189440 189504, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 189440 189504, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-26374 : ℤ) ∧
    (∑ n ∈ Ico 189440 189504, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-527506648496700510663685955 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_189504_189568 :
    (∑ n ∈ Ico 189504 189568, mobiusTreeValue 16 mobiusTable1200001 n) = (-4 : ℤ) ∧
    (∑ n ∈ Ico 189504 189568, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 189504 189568, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-105529 : ℤ) ∧
    (∑ n ∈ Ico 189504 189568, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-2110642560116804320486910131 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_189440_189568 :
    (∑ n ∈ Ico 189440 189568, mobiusTreeValue 16 mobiusTable1200001 n) = (-5 : ℤ) ∧
    (∑ n ∈ Ico 189440 189568, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (79 : ℕ) ∧
    (∑ n ∈ Ico 189440 189568, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-131903 : ℤ) ∧
    (∑ n ∈ Ico 189440 189568, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-2638149208613504831150596086 : ℤ) := by
  rcases cdemPrefixStats_189440_189504 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_189504_189568 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 189440 ≤ 189504) (by norm_num : 189504 ≤ 189568), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 189440 ≤ 189504) (by norm_num : 189504 ≤ 189568), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 189440 ≤ 189504) (by norm_num : 189504 ≤ 189568), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 189440 ≤ 189504) (by norm_num : 189504 ≤ 189568), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_189568_189632 :
    (∑ n ∈ Ico 189568 189632, mobiusTreeValue 16 mobiusTable1200001 n) = (-6 : ℤ) ∧
    (∑ n ∈ Ico 189568 189632, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 189568 189632, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-158197 : ℤ) ∧
    (∑ n ∈ Ico 189568 189632, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-3163970018526600352977103065 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_189632_189696 :
    (∑ n ∈ Ico 189632 189696, mobiusTreeValue 16 mobiusTable1200001 n) = (3 : ℤ) ∧
    (∑ n ∈ Ico 189632 189696, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 189632 189696, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (79108 : ℤ) ∧
    (∑ n ∈ Ico 189632 189696, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1582197717965938306922188942 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_189568_189696 :
    (∑ n ∈ Ico 189568 189696, mobiusTreeValue 16 mobiusTable1200001 n) = (-3 : ℤ) ∧
    (∑ n ∈ Ico 189568 189696, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (79 : ℕ) ∧
    (∑ n ∈ Ico 189568 189696, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-79089 : ℤ) ∧
    (∑ n ∈ Ico 189568 189696, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-1581772300560662046054914123 : ℤ) := by
  rcases cdemPrefixStats_189568_189632 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_189632_189696 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 189568 ≤ 189632) (by norm_num : 189632 ≤ 189696), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 189568 ≤ 189632) (by norm_num : 189632 ≤ 189696), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 189568 ≤ 189632) (by norm_num : 189632 ≤ 189696), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 189568 ≤ 189632) (by norm_num : 189632 ≤ 189696), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_189440_189696 :
    (∑ n ∈ Ico 189440 189696, mobiusTreeValue 16 mobiusTable1200001 n) = (-8 : ℤ) ∧
    (∑ n ∈ Ico 189440 189696, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (158 : ℕ) ∧
    (∑ n ∈ Ico 189440 189696, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-210992 : ℤ) ∧
    (∑ n ∈ Ico 189440 189696, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-4219921509174166877205510209 : ℤ) := by
  rcases cdemPrefixStats_189440_189568 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_189568_189696 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 189440 ≤ 189568) (by norm_num : 189568 ≤ 189696), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 189440 ≤ 189568) (by norm_num : 189568 ≤ 189696), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 189440 ≤ 189568) (by norm_num : 189568 ≤ 189696), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 189440 ≤ 189568) (by norm_num : 189568 ≤ 189696), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_189696_189760 :
    (∑ n ∈ Ico 189696 189760, mobiusTreeValue 16 mobiusTable1200001 n) = (-9 : ℤ) ∧
    (∑ n ∈ Ico 189696 189760, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 189696 189760, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-237173 : ℤ) ∧
    (∑ n ∈ Ico 189696 189760, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-4743566387006690760218062378 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_189760_189824 :
    (∑ n ∈ Ico 189760 189824, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 189760 189824, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 189760 189824, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-13 : ℤ) ∧
    (∑ n ∈ Ico 189760 189824, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-216538231149268522213988 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_189696_189824 :
    (∑ n ∈ Ico 189696 189824, mobiusTreeValue 16 mobiusTable1200001 n) = (-9 : ℤ) ∧
    (∑ n ∈ Ico 189696 189824, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (79 : ℕ) ∧
    (∑ n ∈ Ico 189696 189824, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-237186 : ℤ) ∧
    (∑ n ∈ Ico 189696 189824, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-4743782925237840028740276366 : ℤ) := by
  rcases cdemPrefixStats_189696_189760 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_189760_189824 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 189696 ≤ 189760) (by norm_num : 189760 ≤ 189824), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 189696 ≤ 189760) (by norm_num : 189760 ≤ 189824), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 189696 ≤ 189760) (by norm_num : 189760 ≤ 189824), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 189696 ≤ 189760) (by norm_num : 189760 ≤ 189824), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_189824_189888 :
    (∑ n ∈ Ico 189824 189888, mobiusTreeValue 16 mobiusTable1200001 n) = (-5 : ℤ) ∧
    (∑ n ∈ Ico 189824 189888, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 189824 189888, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-131662 : ℤ) ∧
    (∑ n ∈ Ico 189824 189888, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-2633264216913043734198367904 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_189888_189952 :
    (∑ n ∈ Ico 189888 189952, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 189888 189952, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 189888 189952, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (21 : ℤ) ∧
    (∑ n ∈ Ico 189888 189952, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (382578525699004083569748 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_189824_189952 :
    (∑ n ∈ Ico 189824 189952, mobiusTreeValue 16 mobiusTable1200001 n) = (-5 : ℤ) ∧
    (∑ n ∈ Ico 189824 189952, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 189824 189952, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-131641 : ℤ) ∧
    (∑ n ∈ Ico 189824 189952, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-2632881638387344730114798156 : ℤ) := by
  rcases cdemPrefixStats_189824_189888 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_189888_189952 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 189824 ≤ 189888) (by norm_num : 189888 ≤ 189952), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 189824 ≤ 189888) (by norm_num : 189888 ≤ 189952), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 189824 ≤ 189888) (by norm_num : 189888 ≤ 189952), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 189824 ≤ 189888) (by norm_num : 189888 ≤ 189952), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_189696_189952 :
    (∑ n ∈ Ico 189696 189952, mobiusTreeValue 16 mobiusTable1200001 n) = (-14 : ℤ) ∧
    (∑ n ∈ Ico 189696 189952, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (156 : ℕ) ∧
    (∑ n ∈ Ico 189696 189952, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-368827 : ℤ) ∧
    (∑ n ∈ Ico 189696 189952, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-7376664563625184758855074522 : ℤ) := by
  rcases cdemPrefixStats_189696_189824 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_189824_189952 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 189696 ≤ 189824) (by norm_num : 189824 ≤ 189952), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 189696 ≤ 189824) (by norm_num : 189824 ≤ 189952), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 189696 ≤ 189824) (by norm_num : 189824 ≤ 189952), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 189696 ≤ 189824) (by norm_num : 189824 ≤ 189952), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_189440_189952 :
    (∑ n ∈ Ico 189440 189952, mobiusTreeValue 16 mobiusTable1200001 n) = (-22 : ℤ) ∧
    (∑ n ∈ Ico 189440 189952, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (314 : ℕ) ∧
    (∑ n ∈ Ico 189440 189952, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-579819 : ℤ) ∧
    (∑ n ∈ Ico 189440 189952, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-11596586072799351636060584731 : ℤ) := by
  rcases cdemPrefixStats_189440_189696 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_189696_189952 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 189440 ≤ 189696) (by norm_num : 189696 ≤ 189952), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 189440 ≤ 189696) (by norm_num : 189696 ≤ 189952), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 189440 ≤ 189696) (by norm_num : 189696 ≤ 189952), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 189440 ≤ 189696) (by norm_num : 189696 ≤ 189952), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_189952_190016 :
    (∑ n ∈ Ico 189952 190016, mobiusTreeValue 16 mobiusTable1200001 n) = (8 : ℤ) ∧
    (∑ n ∈ Ico 189952 190016, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 189952 190016, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (210504 : ℤ) ∧
    (∑ n ∈ Ico 189952 190016, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (4210227128233935905741398180 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_190016_190080 :
    (∑ n ∈ Ico 190016 190080, mobiusTreeValue 16 mobiusTable1200001 n) = (3 : ℤ) ∧
    (∑ n ∈ Ico 190016 190080, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 190016 190080, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (78913 : ℤ) ∧
    (∑ n ∈ Ico 190016 190080, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1578266158520222925363229695 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_189952_190080 :
    (∑ n ∈ Ico 189952 190080, mobiusTreeValue 16 mobiusTable1200001 n) = (11 : ℤ) ∧
    (∑ n ∈ Ico 189952 190080, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (75 : ℕ) ∧
    (∑ n ∈ Ico 189952 190080, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (289417 : ℤ) ∧
    (∑ n ∈ Ico 189952 190080, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (5788493286754158831104627875 : ℤ) := by
  rcases cdemPrefixStats_189952_190016 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_190016_190080 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 189952 ≤ 190016) (by norm_num : 190016 ≤ 190080), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 189952 ≤ 190016) (by norm_num : 190016 ≤ 190080), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 189952 ≤ 190016) (by norm_num : 190016 ≤ 190080), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 189952 ≤ 190016) (by norm_num : 190016 ≤ 190080), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_190080_190144 :
    (∑ n ∈ Ico 190080 190144, mobiusTreeValue 16 mobiusTable1200001 n) = (-5 : ℤ) ∧
    (∑ n ∈ Ico 190080 190144, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 190080 190144, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-131504 : ℤ) ∧
    (∑ n ∈ Ico 190080 190144, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-2630103317969730635739820208 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_190144_190208 :
    (∑ n ∈ Ico 190144 190208, mobiusTreeValue 16 mobiusTable1200001 n) = (7 : ℤ) ∧
    (∑ n ∈ Ico 190144 190208, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 190144 190208, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (184015 : ℤ) ∧
    (∑ n ∈ Ico 190144 190208, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (3680372323775029488805315428 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_190080_190208 :
    (∑ n ∈ Ico 190080 190208, mobiusTreeValue 16 mobiusTable1200001 n) = (2 : ℤ) ∧
    (∑ n ∈ Ico 190080 190208, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (80 : ℕ) ∧
    (∑ n ∈ Ico 190080 190208, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (52511 : ℤ) ∧
    (∑ n ∈ Ico 190080 190208, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1050269005805298853065495220 : ℤ) := by
  rcases cdemPrefixStats_190080_190144 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_190144_190208 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 190080 ≤ 190144) (by norm_num : 190144 ≤ 190208), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 190080 ≤ 190144) (by norm_num : 190144 ≤ 190208), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 190080 ≤ 190144) (by norm_num : 190144 ≤ 190208), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 190080 ≤ 190144) (by norm_num : 190144 ≤ 190208), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_189952_190208 :
    (∑ n ∈ Ico 189952 190208, mobiusTreeValue 16 mobiusTable1200001 n) = (13 : ℤ) ∧
    (∑ n ∈ Ico 189952 190208, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (155 : ℕ) ∧
    (∑ n ∈ Ico 189952 190208, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (341928 : ℤ) ∧
    (∑ n ∈ Ico 189952 190208, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (6838762292559457684170123095 : ℤ) := by
  rcases cdemPrefixStats_189952_190080 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_190080_190208 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 189952 ≤ 190080) (by norm_num : 190080 ≤ 190208), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 189952 ≤ 190080) (by norm_num : 190080 ≤ 190208), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 189952 ≤ 190080) (by norm_num : 190080 ≤ 190208), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 189952 ≤ 190080) (by norm_num : 190080 ≤ 190208), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_190208_190272 :
    (∑ n ∈ Ico 190208 190272, mobiusTreeValue 16 mobiusTable1200001 n) = (8 : ℤ) ∧
    (∑ n ∈ Ico 190208 190272, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 190208 190272, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (210249 : ℤ) ∧
    (∑ n ∈ Ico 190208 190272, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (4205073598020525156844638771 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_190272_190336 :
    (∑ n ∈ Ico 190272 190336, mobiusTreeValue 16 mobiusTable1200001 n) = (-4 : ℤ) ∧
    (∑ n ∈ Ico 190272 190336, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 190272 190336, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-105089 : ℤ) ∧
    (∑ n ∈ Ico 190272 190336, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-2101831102937321266686313472 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_190208_190336 :
    (∑ n ∈ Ico 190208 190336, mobiusTreeValue 16 mobiusTable1200001 n) = (4 : ℤ) ∧
    (∑ n ∈ Ico 190208 190336, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (76 : ℕ) ∧
    (∑ n ∈ Ico 190208 190336, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (105160 : ℤ) ∧
    (∑ n ∈ Ico 190208 190336, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (2103242495083203890158325299 : ℤ) := by
  rcases cdemPrefixStats_190208_190272 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_190272_190336 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 190208 ≤ 190272) (by norm_num : 190272 ≤ 190336), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 190208 ≤ 190272) (by norm_num : 190272 ≤ 190336), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 190208 ≤ 190272) (by norm_num : 190272 ≤ 190336), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 190208 ≤ 190272) (by norm_num : 190272 ≤ 190336), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_190336_190400 :
    (∑ n ∈ Ico 190336 190400, mobiusTreeValue 16 mobiusTable1200001 n) = (-4 : ℤ) ∧
    (∑ n ∈ Ico 190336 190400, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 190336 190400, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-105072 : ℤ) ∧
    (∑ n ∈ Ico 190336 190400, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-2101513587780868094361256470 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_190400_190464 :
    (∑ n ∈ Ico 190400 190464, mobiusTreeValue 16 mobiusTable1200001 n) = (10 : ℤ) ∧
    (∑ n ∈ Ico 190400 190464, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (36 : ℕ) ∧
    (∑ n ∈ Ico 190400 190464, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (262530 : ℤ) ∧
    (∑ n ∈ Ico 190400 190464, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (5250735744089720703038041594 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_190336_190464 :
    (∑ n ∈ Ico 190336 190464, mobiusTreeValue 16 mobiusTable1200001 n) = (6 : ℤ) ∧
    (∑ n ∈ Ico 190336 190464, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (76 : ℕ) ∧
    (∑ n ∈ Ico 190336 190464, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (157458 : ℤ) ∧
    (∑ n ∈ Ico 190336 190464, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (3149222156308852608676785124 : ℤ) := by
  rcases cdemPrefixStats_190336_190400 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_190400_190464 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 190336 ≤ 190400) (by norm_num : 190400 ≤ 190464), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 190336 ≤ 190400) (by norm_num : 190400 ≤ 190464), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 190336 ≤ 190400) (by norm_num : 190400 ≤ 190464), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 190336 ≤ 190400) (by norm_num : 190400 ≤ 190464), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_190208_190464 :
    (∑ n ∈ Ico 190208 190464, mobiusTreeValue 16 mobiusTable1200001 n) = (10 : ℤ) ∧
    (∑ n ∈ Ico 190208 190464, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (152 : ℕ) ∧
    (∑ n ∈ Ico 190208 190464, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (262618 : ℤ) ∧
    (∑ n ∈ Ico 190208 190464, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (5252464651392056498835110423 : ℤ) := by
  rcases cdemPrefixStats_190208_190336 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_190336_190464 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 190208 ≤ 190336) (by norm_num : 190336 ≤ 190464), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 190208 ≤ 190336) (by norm_num : 190336 ≤ 190464), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 190208 ≤ 190336) (by norm_num : 190336 ≤ 190464), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 190208 ≤ 190336) (by norm_num : 190336 ≤ 190464), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_189952_190464 :
    (∑ n ∈ Ico 189952 190464, mobiusTreeValue 16 mobiusTable1200001 n) = (23 : ℤ) ∧
    (∑ n ∈ Ico 189952 190464, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (307 : ℕ) ∧
    (∑ n ∈ Ico 189952 190464, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (604546 : ℤ) ∧
    (∑ n ∈ Ico 189952 190464, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (12091226943951514183005233518 : ℤ) := by
  rcases cdemPrefixStats_189952_190208 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_190208_190464 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 189952 ≤ 190208) (by norm_num : 190208 ≤ 190464), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 189952 ≤ 190208) (by norm_num : 190208 ≤ 190464), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 189952 ≤ 190208) (by norm_num : 190208 ≤ 190464), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 189952 ≤ 190208) (by norm_num : 190208 ≤ 190464), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_189440_190464 :
    (∑ n ∈ Ico 189440 190464, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 189440 190464, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (621 : ℕ) ∧
    (∑ n ∈ Ico 189440 190464, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (24727 : ℤ) ∧
    (∑ n ∈ Ico 189440 190464, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (494640871152162546944648787 : ℤ) := by
  rcases cdemPrefixStats_189440_189952 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_189952_190464 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 189440 ≤ 189952) (by norm_num : 189952 ≤ 190464), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 189440 ≤ 189952) (by norm_num : 189952 ≤ 190464), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 189440 ≤ 189952) (by norm_num : 189952 ≤ 190464), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 189440 ≤ 189952) (by norm_num : 189952 ≤ 190464), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_188416_190464 :
    (∑ n ∈ Ico 188416 190464, mobiusTreeValue 16 mobiusTable1200001 n) = (14 : ℤ) ∧
    (∑ n ∈ Ico 188416 190464, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (1240 : ℕ) ∧
    (∑ n ∈ Ico 188416 190464, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (369099 : ℤ) ∧
    (∑ n ∈ Ico 188416 190464, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (7382456726984208847082244073 : ℤ) := by
  rcases cdemPrefixStats_188416_189440 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_189440_190464 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 188416 ≤ 189440) (by norm_num : 189440 ≤ 190464), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 188416 ≤ 189440) (by norm_num : 189440 ≤ 190464), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 188416 ≤ 189440) (by norm_num : 189440 ≤ 190464), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 188416 ≤ 189440) (by norm_num : 189440 ≤ 190464), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_190464_190528 :
    (∑ n ∈ Ico 190464 190528, mobiusTreeValue 16 mobiusTable1200001 n) = (13 : ℤ) ∧
    (∑ n ∈ Ico 190464 190528, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 190464 190528, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (341212 : ℤ) ∧
    (∑ n ∈ Ico 190464 190528, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (6824361933933795027742324108 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_190528_190592 :
    (∑ n ∈ Ico 190528 190592, mobiusTreeValue 16 mobiusTable1200001 n) = (-7 : ℤ) ∧
    (∑ n ∈ Ico 190528 190592, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 190528 190592, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-183657 : ℤ) ∧
    (∑ n ∈ Ico 190528 190592, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-3673168950935904582956402396 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_190464_190592 :
    (∑ n ∈ Ico 190464 190592, mobiusTreeValue 16 mobiusTable1200001 n) = (6 : ℤ) ∧
    (∑ n ∈ Ico 190464 190592, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (82 : ℕ) ∧
    (∑ n ∈ Ico 190464 190592, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (157555 : ℤ) ∧
    (∑ n ∈ Ico 190464 190592, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (3151192982997890444785921712 : ℤ) := by
  rcases cdemPrefixStats_190464_190528 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_190528_190592 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 190464 ≤ 190528) (by norm_num : 190528 ≤ 190592), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 190464 ≤ 190528) (by norm_num : 190528 ≤ 190592), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 190464 ≤ 190528) (by norm_num : 190528 ≤ 190592), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 190464 ≤ 190528) (by norm_num : 190528 ≤ 190592), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_190592_190656 :
    (∑ n ∈ Ico 190592 190656, mobiusTreeValue 16 mobiusTable1200001 n) = (3 : ℤ) ∧
    (∑ n ∈ Ico 190592 190656, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 190592 190656, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (78682 : ℤ) ∧
    (∑ n ∈ Ico 190592 190656, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1573698953936646578436537776 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_190656_190720 :
    (∑ n ∈ Ico 190656 190720, mobiusTreeValue 16 mobiusTable1200001 n) = (-4 : ℤ) ∧
    (∑ n ∈ Ico 190656 190720, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 190656 190720, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-104853 : ℤ) ∧
    (∑ n ∈ Ico 190656 190720, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-2097150448788901414945453801 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_190592_190720 :
    (∑ n ∈ Ico 190592 190720, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 190592 190720, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (79 : ℕ) ∧
    (∑ n ∈ Ico 190592 190720, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-26171 : ℤ) ∧
    (∑ n ∈ Ico 190592 190720, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-523451494852254836508916025 : ℤ) := by
  rcases cdemPrefixStats_190592_190656 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_190656_190720 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 190592 ≤ 190656) (by norm_num : 190656 ≤ 190720), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 190592 ≤ 190656) (by norm_num : 190656 ≤ 190720), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 190592 ≤ 190656) (by norm_num : 190656 ≤ 190720), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 190592 ≤ 190656) (by norm_num : 190656 ≤ 190720), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_190464_190720 :
    (∑ n ∈ Ico 190464 190720, mobiusTreeValue 16 mobiusTable1200001 n) = (5 : ℤ) ∧
    (∑ n ∈ Ico 190464 190720, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (161 : ℕ) ∧
    (∑ n ∈ Ico 190464 190720, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (131384 : ℤ) ∧
    (∑ n ∈ Ico 190464 190720, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (2627741488145635608277005687 : ℤ) := by
  rcases cdemPrefixStats_190464_190592 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_190592_190720 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 190464 ≤ 190592) (by norm_num : 190592 ≤ 190720), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 190464 ≤ 190592) (by norm_num : 190592 ≤ 190720), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 190464 ≤ 190592) (by norm_num : 190592 ≤ 190720), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 190464 ≤ 190592) (by norm_num : 190592 ≤ 190720), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_190720_190784 :
    (∑ n ∈ Ico 190720 190784, mobiusTreeValue 16 mobiusTable1200001 n) = (3 : ℤ) ∧
    (∑ n ∈ Ico 190720 190784, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 190720 190784, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (78632 : ℤ) ∧
    (∑ n ∈ Ico 190720 190784, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1572678722577486620149904116 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_190784_190848 :
    (∑ n ∈ Ico 190784 190848, mobiusTreeValue 16 mobiusTable1200001 n) = (-3 : ℤ) ∧
    (∑ n ∈ Ico 190784 190848, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 190784 190848, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-78630 : ℤ) ∧
    (∑ n ∈ Ico 190784 190848, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-1572576991850302026129906204 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_190720_190848 :
    (∑ n ∈ Ico 190720 190848, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 190720 190848, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 190720 190848, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (2 : ℤ) ∧
    (∑ n ∈ Ico 190720 190848, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (101730727184594019997912 : ℤ) := by
  rcases cdemPrefixStats_190720_190784 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_190784_190848 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 190720 ≤ 190784) (by norm_num : 190784 ≤ 190848), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 190720 ≤ 190784) (by norm_num : 190784 ≤ 190848), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 190720 ≤ 190784) (by norm_num : 190784 ≤ 190848), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 190720 ≤ 190784) (by norm_num : 190784 ≤ 190848), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_190848_190912 :
    (∑ n ∈ Ico 190848 190912, mobiusTreeValue 16 mobiusTable1200001 n) = (-3 : ℤ) ∧
    (∑ n ∈ Ico 190848 190912, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 190848 190912, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-78566 : ℤ) ∧
    (∑ n ∈ Ico 190848 190912, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-1571377173279295425406698483 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_190912_190976 :
    (∑ n ∈ Ico 190912 190976, mobiusTreeValue 16 mobiusTable1200001 n) = (14 : ℤ) ∧
    (∑ n ∈ Ico 190912 190976, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (36 : ℕ) ∧
    (∑ n ∈ Ico 190912 190976, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (366587 : ℤ) ∧
    (∑ n ∈ Ico 190912 190976, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (7331869264388959164283002243 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_190848_190976 :
    (∑ n ∈ Ico 190848 190976, mobiusTreeValue 16 mobiusTable1200001 n) = (11 : ℤ) ∧
    (∑ n ∈ Ico 190848 190976, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (75 : ℕ) ∧
    (∑ n ∈ Ico 190848 190976, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (288021 : ℤ) ∧
    (∑ n ∈ Ico 190848 190976, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (5760492091109663738876303760 : ℤ) := by
  rcases cdemPrefixStats_190848_190912 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_190912_190976 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 190848 ≤ 190912) (by norm_num : 190912 ≤ 190976), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 190848 ≤ 190912) (by norm_num : 190912 ≤ 190976), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 190848 ≤ 190912) (by norm_num : 190912 ≤ 190976), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 190848 ≤ 190912) (by norm_num : 190912 ≤ 190976), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_190720_190976 :
    (∑ n ∈ Ico 190720 190976, mobiusTreeValue 16 mobiusTable1200001 n) = (11 : ℤ) ∧
    (∑ n ∈ Ico 190720 190976, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (153 : ℕ) ∧
    (∑ n ∈ Ico 190720 190976, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (288023 : ℤ) ∧
    (∑ n ∈ Ico 190720 190976, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (5760593821836848332896301672 : ℤ) := by
  rcases cdemPrefixStats_190720_190848 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_190848_190976 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 190720 ≤ 190848) (by norm_num : 190848 ≤ 190976), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 190720 ≤ 190848) (by norm_num : 190848 ≤ 190976), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 190720 ≤ 190848) (by norm_num : 190848 ≤ 190976), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 190720 ≤ 190848) (by norm_num : 190848 ≤ 190976), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_190464_190976 :
    (∑ n ∈ Ico 190464 190976, mobiusTreeValue 16 mobiusTable1200001 n) = (16 : ℤ) ∧
    (∑ n ∈ Ico 190464 190976, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (314 : ℕ) ∧
    (∑ n ∈ Ico 190464 190976, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (419407 : ℤ) ∧
    (∑ n ∈ Ico 190464 190976, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (8388335309982483941173307359 : ℤ) := by
  rcases cdemPrefixStats_190464_190720 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_190720_190976 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 190464 ≤ 190720) (by norm_num : 190720 ≤ 190976), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 190464 ≤ 190720) (by norm_num : 190720 ≤ 190976), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 190464 ≤ 190720) (by norm_num : 190720 ≤ 190976), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 190464 ≤ 190720) (by norm_num : 190720 ≤ 190976), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_190976_191040 :
    (∑ n ∈ Ico 190976 191040, mobiusTreeValue 16 mobiusTable1200001 n) = (3 : ℤ) ∧
    (∑ n ∈ Ico 190976 191040, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 190976 191040, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (78563 : ℤ) ∧
    (∑ n ∈ Ico 190976 191040, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1571272664449060658293559639 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_191040_191104 :
    (∑ n ∈ Ico 191040 191104, mobiusTreeValue 16 mobiusTable1200001 n) = (3 : ℤ) ∧
    (∑ n ∈ Ico 191040 191104, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 191040 191104, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (78512 : ℤ) ∧
    (∑ n ∈ Ico 191040 191104, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1570233927809169273170912227 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_190976_191104 :
    (∑ n ∈ Ico 190976 191104, mobiusTreeValue 16 mobiusTable1200001 n) = (6 : ℤ) ∧
    (∑ n ∈ Ico 190976 191104, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (80 : ℕ) ∧
    (∑ n ∈ Ico 190976 191104, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (157075 : ℤ) ∧
    (∑ n ∈ Ico 190976 191104, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (3141506592258229931464471866 : ℤ) := by
  rcases cdemPrefixStats_190976_191040 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_191040_191104 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 190976 ≤ 191040) (by norm_num : 191040 ≤ 191104), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 190976 ≤ 191040) (by norm_num : 191040 ≤ 191104), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 190976 ≤ 191040) (by norm_num : 191040 ≤ 191104), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 190976 ≤ 191040) (by norm_num : 191040 ≤ 191104), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_191104_191168 :
    (∑ n ∈ Ico 191104 191168, mobiusTreeValue 16 mobiusTable1200001 n) = (3 : ℤ) ∧
    (∑ n ∈ Ico 191104 191168, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 191104 191168, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (78467 : ℤ) ∧
    (∑ n ∈ Ico 191104 191168, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1569365988400623398806642128 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_191168_191232 :
    (∑ n ∈ Ico 191168 191232, mobiusTreeValue 16 mobiusTable1200001 n) = (5 : ℤ) ∧
    (∑ n ∈ Ico 191168 191232, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 191168 191232, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (130758 : ℤ) ∧
    (∑ n ∈ Ico 191168 191232, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (2615297995867400746947957634 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_191104_191232 :
    (∑ n ∈ Ico 191104 191232, mobiusTreeValue 16 mobiusTable1200001 n) = (8 : ℤ) ∧
    (∑ n ∈ Ico 191104 191232, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 191104 191232, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (209225 : ℤ) ∧
    (∑ n ∈ Ico 191104 191232, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (4184663984268024145754599762 : ℤ) := by
  rcases cdemPrefixStats_191104_191168 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_191168_191232 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 191104 ≤ 191168) (by norm_num : 191168 ≤ 191232), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 191104 ≤ 191168) (by norm_num : 191168 ≤ 191232), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 191104 ≤ 191168) (by norm_num : 191168 ≤ 191232), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 191104 ≤ 191168) (by norm_num : 191168 ≤ 191232), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_190976_191232 :
    (∑ n ∈ Ico 190976 191232, mobiusTreeValue 16 mobiusTable1200001 n) = (14 : ℤ) ∧
    (∑ n ∈ Ico 190976 191232, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (158 : ℕ) ∧
    (∑ n ∈ Ico 190976 191232, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (366300 : ℤ) ∧
    (∑ n ∈ Ico 190976 191232, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (7326170576526254077219071628 : ℤ) := by
  rcases cdemPrefixStats_190976_191104 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_191104_191232 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 190976 ≤ 191104) (by norm_num : 191104 ≤ 191232), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 190976 ≤ 191104) (by norm_num : 191104 ≤ 191232), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 190976 ≤ 191104) (by norm_num : 191104 ≤ 191232), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 190976 ≤ 191104) (by norm_num : 191104 ≤ 191232), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_191232_191296 :
    (∑ n ∈ Ico 191232 191296, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 191232 191296, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 191232 191296, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (26118 : ℤ) ∧
    (∑ n ∈ Ico 191232 191296, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (522370053048944760329996106 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_191296_191360 :
    (∑ n ∈ Ico 191296 191360, mobiusTreeValue 16 mobiusTable1200001 n) = (-3 : ℤ) ∧
    (∑ n ∈ Ico 191296 191360, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 191296 191360, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-78403 : ℤ) ∧
    (∑ n ∈ Ico 191296 191360, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-1568031699295223606957659110 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_191232_191360 :
    (∑ n ∈ Ico 191232 191360, mobiusTreeValue 16 mobiusTable1200001 n) = (-2 : ℤ) ∧
    (∑ n ∈ Ico 191232 191360, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (76 : ℕ) ∧
    (∑ n ∈ Ico 191232 191360, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-52285 : ℤ) ∧
    (∑ n ∈ Ico 191232 191360, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-1045661646246278846627663004 : ℤ) := by
  rcases cdemPrefixStats_191232_191296 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_191296_191360 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 191232 ≤ 191296) (by norm_num : 191296 ≤ 191360), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 191232 ≤ 191296) (by norm_num : 191296 ≤ 191360), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 191232 ≤ 191296) (by norm_num : 191296 ≤ 191360), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 191232 ≤ 191296) (by norm_num : 191296 ≤ 191360), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_191360_191424 :
    (∑ n ∈ Ico 191360 191424, mobiusTreeValue 16 mobiusTable1200001 n) = (9 : ℤ) ∧
    (∑ n ∈ Ico 191360 191424, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 191360 191424, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (235102 : ℤ) ∧
    (∑ n ∈ Ico 191360 191424, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (4702082493021564051852331782 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_191424_191488 :
    (∑ n ∈ Ico 191424 191488, mobiusTreeValue 16 mobiusTable1200001 n) = (-6 : ℤ) ∧
    (∑ n ∈ Ico 191424 191488, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 191424 191488, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-156660 : ℤ) ∧
    (∑ n ∈ Ico 191424 191488, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-3133249114983403738656137067 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_191360_191488 :
    (∑ n ∈ Ico 191360 191488, mobiusTreeValue 16 mobiusTable1200001 n) = (3 : ℤ) ∧
    (∑ n ∈ Ico 191360 191488, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (79 : ℕ) ∧
    (∑ n ∈ Ico 191360 191488, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (78442 : ℤ) ∧
    (∑ n ∈ Ico 191360 191488, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1568833378038160313196194715 : ℤ) := by
  rcases cdemPrefixStats_191360_191424 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_191424_191488 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 191360 ≤ 191424) (by norm_num : 191424 ≤ 191488), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 191360 ≤ 191424) (by norm_num : 191424 ≤ 191488), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 191360 ≤ 191424) (by norm_num : 191424 ≤ 191488), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 191360 ≤ 191424) (by norm_num : 191424 ≤ 191488), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_191232_191488 :
    (∑ n ∈ Ico 191232 191488, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 191232 191488, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (155 : ℕ) ∧
    (∑ n ∈ Ico 191232 191488, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (26157 : ℤ) ∧
    (∑ n ∈ Ico 191232 191488, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (523171731791881466568531711 : ℤ) := by
  rcases cdemPrefixStats_191232_191360 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_191360_191488 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 191232 ≤ 191360) (by norm_num : 191360 ≤ 191488), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 191232 ≤ 191360) (by norm_num : 191360 ≤ 191488), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 191232 ≤ 191360) (by norm_num : 191360 ≤ 191488), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 191232 ≤ 191360) (by norm_num : 191360 ≤ 191488), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_190976_191488 :
    (∑ n ∈ Ico 190976 191488, mobiusTreeValue 16 mobiusTable1200001 n) = (15 : ℤ) ∧
    (∑ n ∈ Ico 190976 191488, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (313 : ℕ) ∧
    (∑ n ∈ Ico 190976 191488, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (392457 : ℤ) ∧
    (∑ n ∈ Ico 190976 191488, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (7849342308318135543787603339 : ℤ) := by
  rcases cdemPrefixStats_190976_191232 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_191232_191488 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 190976 ≤ 191232) (by norm_num : 191232 ≤ 191488), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 190976 ≤ 191232) (by norm_num : 191232 ≤ 191488), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 190976 ≤ 191232) (by norm_num : 191232 ≤ 191488), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 190976 ≤ 191232) (by norm_num : 191232 ≤ 191488), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_190464_191488 :
    (∑ n ∈ Ico 190464 191488, mobiusTreeValue 16 mobiusTable1200001 n) = (31 : ℤ) ∧
    (∑ n ∈ Ico 190464 191488, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (627 : ℕ) ∧
    (∑ n ∈ Ico 190464 191488, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (811864 : ℤ) ∧
    (∑ n ∈ Ico 190464 191488, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (16237677618300619484960910698 : ℤ) := by
  rcases cdemPrefixStats_190464_190976 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_190976_191488 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 190464 ≤ 190976) (by norm_num : 190976 ≤ 191488), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 190464 ≤ 190976) (by norm_num : 190976 ≤ 191488), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 190464 ≤ 190976) (by norm_num : 190976 ≤ 191488), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 190464 ≤ 190976) (by norm_num : 190976 ≤ 191488), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_191488_191552 :
    (∑ n ∈ Ico 191488 191552, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 191488 191552, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (36 : ℕ) ∧
    (∑ n ∈ Ico 191488 191552, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (17 : ℤ) ∧
    (∑ n ∈ Ico 191488 191552, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (359851973275924409649898 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_191552_191616 :
    (∑ n ∈ Ico 191552 191616, mobiusTreeValue 16 mobiusTable1200001 n) = (9 : ℤ) ∧
    (∑ n ∈ Ico 191552 191616, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 191552 191616, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (234882 : ℤ) ∧
    (∑ n ∈ Ico 191552 191616, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (4697768200573446161368695543 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_191488_191616 :
    (∑ n ∈ Ico 191488 191616, mobiusTreeValue 16 mobiusTable1200001 n) = (9 : ℤ) ∧
    (∑ n ∈ Ico 191488 191616, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (75 : ℕ) ∧
    (∑ n ∈ Ico 191488 191616, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (234899 : ℤ) ∧
    (∑ n ∈ Ico 191488 191616, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (4698128052546722085778345441 : ℤ) := by
  rcases cdemPrefixStats_191488_191552 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_191552_191616 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 191488 ≤ 191552) (by norm_num : 191552 ≤ 191616), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 191488 ≤ 191552) (by norm_num : 191552 ≤ 191616), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 191488 ≤ 191552) (by norm_num : 191552 ≤ 191616), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 191488 ≤ 191552) (by norm_num : 191552 ≤ 191616), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_191616_191680 :
    (∑ n ∈ Ico 191616 191680, mobiusTreeValue 16 mobiusTable1200001 n) = (-2 : ℤ) ∧
    (∑ n ∈ Ico 191616 191680, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 191616 191680, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-52145 : ℤ) ∧
    (∑ n ∈ Ico 191616 191680, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-1042929233678000871602466832 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_191680_191744 :
    (∑ n ∈ Ico 191680 191744, mobiusTreeValue 16 mobiusTable1200001 n) = (3 : ℤ) ∧
    (∑ n ∈ Ico 191680 191744, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 191680 191744, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (78241 : ℤ) ∧
    (∑ n ∈ Ico 191680 191744, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1564833694017200166008428024 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_191616_191744 :
    (∑ n ∈ Ico 191616 191744, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 191616 191744, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (79 : ℕ) ∧
    (∑ n ∈ Ico 191616 191744, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (26096 : ℤ) ∧
    (∑ n ∈ Ico 191616 191744, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (521904460339199294405961192 : ℤ) := by
  rcases cdemPrefixStats_191616_191680 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_191680_191744 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 191616 ≤ 191680) (by norm_num : 191680 ≤ 191744), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 191616 ≤ 191680) (by norm_num : 191680 ≤ 191744), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 191616 ≤ 191680) (by norm_num : 191680 ≤ 191744), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 191616 ≤ 191680) (by norm_num : 191680 ≤ 191744), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_191488_191744 :
    (∑ n ∈ Ico 191488 191744, mobiusTreeValue 16 mobiusTable1200001 n) = (10 : ℤ) ∧
    (∑ n ∈ Ico 191488 191744, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (154 : ℕ) ∧
    (∑ n ∈ Ico 191488 191744, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (260995 : ℤ) ∧
    (∑ n ∈ Ico 191488 191744, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (5220032512885921380184306633 : ℤ) := by
  rcases cdemPrefixStats_191488_191616 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_191616_191744 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 191488 ≤ 191616) (by norm_num : 191616 ≤ 191744), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 191488 ≤ 191616) (by norm_num : 191616 ≤ 191744), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 191488 ≤ 191616) (by norm_num : 191616 ≤ 191744), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 191488 ≤ 191616) (by norm_num : 191616 ≤ 191744), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_191744_191808 :
    (∑ n ∈ Ico 191744 191808, mobiusTreeValue 16 mobiusTable1200001 n) = (-2 : ℤ) ∧
    (∑ n ∈ Ico 191744 191808, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 191744 191808, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-52125 : ℤ) ∧
    (∑ n ∈ Ico 191744 191808, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-1042508149195038271085624611 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_191808_191872 :
    (∑ n ∈ Ico 191808 191872, mobiusTreeValue 16 mobiusTable1200001 n) = (3 : ℤ) ∧
    (∑ n ∈ Ico 191808 191872, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 191808 191872, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (78166 : ℤ) ∧
    (∑ n ∈ Ico 191808 191872, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1563286945220279271966871852 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_191744_191872 :
    (∑ n ∈ Ico 191744 191872, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 191744 191872, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 191744 191872, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (26041 : ℤ) ∧
    (∑ n ∈ Ico 191744 191872, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (520778796025241000881247241 : ℤ) := by
  rcases cdemPrefixStats_191744_191808 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_191808_191872 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 191744 ≤ 191808) (by norm_num : 191808 ≤ 191872), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 191744 ≤ 191808) (by norm_num : 191808 ≤ 191872), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 191744 ≤ 191808) (by norm_num : 191808 ≤ 191872), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 191744 ≤ 191808) (by norm_num : 191808 ≤ 191872), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_191872_191936 :
    (∑ n ∈ Ico 191872 191936, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 191872 191936, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 191872 191936, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (4 : ℤ) ∧
    (∑ n ∈ Ico 191872 191936, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (57040717175902889206931 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_191936_192000 :
    (∑ n ∈ Ico 191936 192000, mobiusTreeValue 16 mobiusTable1200001 n) = (-2 : ℤ) ∧
    (∑ n ∈ Ico 191936 192000, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 191936 192000, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-52103 : ℤ) ∧
    (∑ n ∈ Ico 191936 192000, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-1042103527793914492191596900 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_191872_192000 :
    (∑ n ∈ Ico 191872 192000, mobiusTreeValue 16 mobiusTable1200001 n) = (-2 : ℤ) ∧
    (∑ n ∈ Ico 191872 192000, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (80 : ℕ) ∧
    (∑ n ∈ Ico 191872 192000, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-52099 : ℤ) ∧
    (∑ n ∈ Ico 191872 192000, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-1042046487076738589302389969 : ℤ) := by
  rcases cdemPrefixStats_191872_191936 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_191936_192000 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 191872 ≤ 191936) (by norm_num : 191936 ≤ 192000), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 191872 ≤ 191936) (by norm_num : 191936 ≤ 192000), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 191872 ≤ 191936) (by norm_num : 191936 ≤ 192000), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 191872 ≤ 191936) (by norm_num : 191936 ≤ 192000), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_191744_192000 :
    (∑ n ∈ Ico 191744 192000, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 191744 192000, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (157 : ℕ) ∧
    (∑ n ∈ Ico 191744 192000, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-26058 : ℤ) ∧
    (∑ n ∈ Ico 191744 192000, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-521267691051497588421142728 : ℤ) := by
  rcases cdemPrefixStats_191744_191872 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_191872_192000 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 191744 ≤ 191872) (by norm_num : 191872 ≤ 192000), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 191744 ≤ 191872) (by norm_num : 191872 ≤ 192000), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 191744 ≤ 191872) (by norm_num : 191872 ≤ 192000), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 191744 ≤ 191872) (by norm_num : 191872 ≤ 192000), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_191488_192000 :
    (∑ n ∈ Ico 191488 192000, mobiusTreeValue 16 mobiusTable1200001 n) = (9 : ℤ) ∧
    (∑ n ∈ Ico 191488 192000, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (311 : ℕ) ∧
    (∑ n ∈ Ico 191488 192000, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (234937 : ℤ) ∧
    (∑ n ∈ Ico 191488 192000, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (4698764821834423791763163905 : ℤ) := by
  rcases cdemPrefixStats_191488_191744 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_191744_192000 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 191488 ≤ 191744) (by norm_num : 191744 ≤ 192000), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 191488 ≤ 191744) (by norm_num : 191744 ≤ 192000), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 191488 ≤ 191744) (by norm_num : 191744 ≤ 192000), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 191488 ≤ 191744) (by norm_num : 191744 ≤ 192000), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_192000_192064 :
    (∑ n ∈ Ico 192000 192064, mobiusTreeValue 16 mobiusTable1200001 n) = (-3 : ℤ) ∧
    (∑ n ∈ Ico 192000 192064, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 192000 192064, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-78096 : ℤ) ∧
    (∑ n ∈ Ico 192000 192064, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-1562017251620299662846349482 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_192064_192128 :
    (∑ n ∈ Ico 192064 192128, mobiusTreeValue 16 mobiusTable1200001 n) = (-12 : ℤ) ∧
    (∑ n ∈ Ico 192064 192128, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 192064 192128, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-312363 : ℤ) ∧
    (∑ n ∈ Ico 192064 192128, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-6247407784640125487370292766 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_192000_192128 :
    (∑ n ∈ Ico 192000 192128, mobiusTreeValue 16 mobiusTable1200001 n) = (-15 : ℤ) ∧
    (∑ n ∈ Ico 192000 192128, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (79 : ℕ) ∧
    (∑ n ∈ Ico 192000 192128, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-390459 : ℤ) ∧
    (∑ n ∈ Ico 192000 192128, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-7809425036260425150216642248 : ℤ) := by
  rcases cdemPrefixStats_192000_192064 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_192064_192128 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 192000 ≤ 192064) (by norm_num : 192064 ≤ 192128), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 192000 ≤ 192064) (by norm_num : 192064 ≤ 192128), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 192000 ≤ 192064) (by norm_num : 192064 ≤ 192128), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 192000 ≤ 192064) (by norm_num : 192064 ≤ 192128), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_192128_192192 :
    (∑ n ∈ Ico 192128 192192, mobiusTreeValue 16 mobiusTable1200001 n) = (-7 : ℤ) ∧
    (∑ n ∈ Ico 192128 192192, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 192128 192192, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-182140 : ℤ) ∧
    (∑ n ∈ Ico 192128 192192, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-3642857293157435050542915596 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_192192_192256 :
    (∑ n ∈ Ico 192192 192256, mobiusTreeValue 16 mobiusTable1200001 n) = (-11 : ℤ) ∧
    (∑ n ∈ Ico 192192 192256, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 192192 192256, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-286114 : ℤ) ∧
    (∑ n ∈ Ico 192192 192256, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-5722360539117343814885073550 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_192128_192256 :
    (∑ n ∈ Ico 192128 192256, mobiusTreeValue 16 mobiusTable1200001 n) = (-18 : ℤ) ∧
    (∑ n ∈ Ico 192128 192256, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (76 : ℕ) ∧
    (∑ n ∈ Ico 192128 192256, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-468254 : ℤ) ∧
    (∑ n ∈ Ico 192128 192256, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-9365217832274778865427989146 : ℤ) := by
  rcases cdemPrefixStats_192128_192192 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_192192_192256 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 192128 ≤ 192192) (by norm_num : 192192 ≤ 192256), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 192128 ≤ 192192) (by norm_num : 192192 ≤ 192256), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 192128 ≤ 192192) (by norm_num : 192192 ≤ 192256), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 192128 ≤ 192192) (by norm_num : 192192 ≤ 192256), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_192000_192256 :
    (∑ n ∈ Ico 192000 192256, mobiusTreeValue 16 mobiusTable1200001 n) = (-33 : ℤ) ∧
    (∑ n ∈ Ico 192000 192256, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (155 : ℕ) ∧
    (∑ n ∈ Ico 192000 192256, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-858713 : ℤ) ∧
    (∑ n ∈ Ico 192000 192256, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-17174642868535204015644631394 : ℤ) := by
  rcases cdemPrefixStats_192000_192128 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_192128_192256 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 192000 ≤ 192128) (by norm_num : 192128 ≤ 192256), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 192000 ≤ 192128) (by norm_num : 192128 ≤ 192256), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 192000 ≤ 192128) (by norm_num : 192128 ≤ 192256), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 192000 ≤ 192128) (by norm_num : 192128 ≤ 192256), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_192256_192320 :
    (∑ n ∈ Ico 192256 192320, mobiusTreeValue 16 mobiusTable1200001 n) = (-7 : ℤ) ∧
    (∑ n ∈ Ico 192256 192320, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 192256 192320, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-182002 : ℤ) ∧
    (∑ n ∈ Ico 192256 192320, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-3640105108134806700875217488 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_192320_192384 :
    (∑ n ∈ Ico 192320 192384, mobiusTreeValue 16 mobiusTable1200001 n) = (-2 : ℤ) ∧
    (∑ n ∈ Ico 192320 192384, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 192320 192384, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-51972 : ℤ) ∧
    (∑ n ∈ Ico 192320 192384, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-1039460465101668960681998187 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_192256_192384 :
    (∑ n ∈ Ico 192256 192384, mobiusTreeValue 16 mobiusTable1200001 n) = (-9 : ℤ) ∧
    (∑ n ∈ Ico 192256 192384, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (79 : ℕ) ∧
    (∑ n ∈ Ico 192256 192384, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-233974 : ℤ) ∧
    (∑ n ∈ Ico 192256 192384, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-4679565573236475661557215675 : ℤ) := by
  rcases cdemPrefixStats_192256_192320 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_192320_192384 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 192256 ≤ 192320) (by norm_num : 192320 ≤ 192384), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 192256 ≤ 192320) (by norm_num : 192320 ≤ 192384), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 192256 ≤ 192320) (by norm_num : 192320 ≤ 192384), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 192256 ≤ 192320) (by norm_num : 192320 ≤ 192384), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_192384_192448 :
    (∑ n ∈ Ico 192384 192448, mobiusTreeValue 16 mobiusTable1200001 n) = (6 : ℤ) ∧
    (∑ n ∈ Ico 192384 192448, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 192384 192448, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (155920 : ℤ) ∧
    (∑ n ∈ Ico 192384 192448, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (3118419376756017713255895104 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_192448_192512 :
    (∑ n ∈ Ico 192448 192512, mobiusTreeValue 16 mobiusTable1200001 n) = (3 : ℤ) ∧
    (∑ n ∈ Ico 192448 192512, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 192448 192512, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (77932 : ℤ) ∧
    (∑ n ∈ Ico 192448 192512, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1558754661475836458778461131 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_192384_192512 :
    (∑ n ∈ Ico 192384 192512, mobiusTreeValue 16 mobiusTable1200001 n) = (9 : ℤ) ∧
    (∑ n ∈ Ico 192384 192512, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 192384 192512, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (233852 : ℤ) ∧
    (∑ n ∈ Ico 192384 192512, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (4677174038231854172034356235 : ℤ) := by
  rcases cdemPrefixStats_192384_192448 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_192448_192512 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 192384 ≤ 192448) (by norm_num : 192448 ≤ 192512), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 192384 ≤ 192448) (by norm_num : 192448 ≤ 192512), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 192384 ≤ 192448) (by norm_num : 192448 ≤ 192512), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 192384 ≤ 192448) (by norm_num : 192448 ≤ 192512), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_192256_192512 :
    (∑ n ∈ Ico 192256 192512, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 192256 192512, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (156 : ℕ) ∧
    (∑ n ∈ Ico 192256 192512, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-122 : ℤ) ∧
    (∑ n ∈ Ico 192256 192512, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-2391535004621489522859440 : ℤ) := by
  rcases cdemPrefixStats_192256_192384 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_192384_192512 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 192256 ≤ 192384) (by norm_num : 192384 ≤ 192512), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 192256 ≤ 192384) (by norm_num : 192384 ≤ 192512), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 192256 ≤ 192384) (by norm_num : 192384 ≤ 192512), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 192256 ≤ 192384) (by norm_num : 192384 ≤ 192512), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_192000_192512 :
    (∑ n ∈ Ico 192000 192512, mobiusTreeValue 16 mobiusTable1200001 n) = (-33 : ℤ) ∧
    (∑ n ∈ Ico 192000 192512, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (311 : ℕ) ∧
    (∑ n ∈ Ico 192000 192512, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-858835 : ℤ) ∧
    (∑ n ∈ Ico 192000 192512, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-17177034403539825505167490834 : ℤ) := by
  rcases cdemPrefixStats_192000_192256 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_192256_192512 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 192000 ≤ 192256) (by norm_num : 192256 ≤ 192512), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 192000 ≤ 192256) (by norm_num : 192256 ≤ 192512), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 192000 ≤ 192256) (by norm_num : 192256 ≤ 192512), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 192000 ≤ 192256) (by norm_num : 192256 ≤ 192512), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_191488_192512 :
    (∑ n ∈ Ico 191488 192512, mobiusTreeValue 16 mobiusTable1200001 n) = (-24 : ℤ) ∧
    (∑ n ∈ Ico 191488 192512, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (622 : ℕ) ∧
    (∑ n ∈ Ico 191488 192512, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-623898 : ℤ) ∧
    (∑ n ∈ Ico 191488 192512, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-12478269581705401713404326929 : ℤ) := by
  rcases cdemPrefixStats_191488_192000 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_192000_192512 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 191488 ≤ 192000) (by norm_num : 192000 ≤ 192512), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 191488 ≤ 192000) (by norm_num : 192000 ≤ 192512), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 191488 ≤ 192000) (by norm_num : 192000 ≤ 192512), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 191488 ≤ 192000) (by norm_num : 192000 ≤ 192512), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_190464_192512 :
    (∑ n ∈ Ico 190464 192512, mobiusTreeValue 16 mobiusTable1200001 n) = (7 : ℤ) ∧
    (∑ n ∈ Ico 190464 192512, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (1249 : ℕ) ∧
    (∑ n ∈ Ico 190464 192512, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (187966 : ℤ) ∧
    (∑ n ∈ Ico 190464 192512, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (3759408036595217771556583769 : ℤ) := by
  rcases cdemPrefixStats_190464_191488 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_191488_192512 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 190464 ≤ 191488) (by norm_num : 191488 ≤ 192512), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 190464 ≤ 191488) (by norm_num : 191488 ≤ 192512), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 190464 ≤ 191488) (by norm_num : 191488 ≤ 192512), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 190464 ≤ 191488) (by norm_num : 191488 ≤ 192512), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_188416_192512 :
    (∑ n ∈ Ico 188416 192512, mobiusTreeValue 16 mobiusTable1200001 n) = (21 : ℤ) ∧
    (∑ n ∈ Ico 188416 192512, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (2489 : ℕ) ∧
    (∑ n ∈ Ico 188416 192512, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (557065 : ℤ) ∧
    (∑ n ∈ Ico 188416 192512, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (11141864763579426618638827842 : ℤ) := by
  rcases cdemPrefixStats_188416_190464 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_190464_192512 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 188416 ≤ 190464) (by norm_num : 190464 ≤ 192512), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 188416 ≤ 190464) (by norm_num : 190464 ≤ 192512), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 188416 ≤ 190464) (by norm_num : 190464 ≤ 192512), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 188416 ≤ 190464) (by norm_num : 190464 ≤ 192512), hR1, hR2] <;> norm_num

theorem cdemPrefixGroup046_checked_complete :
    (∑ n ∈ Ico 188416 192512, mobiusTreeValue 16 mobiusTable1200001 n) = (21 : ℤ) ∧
    (∑ n ∈ Ico 188416 192512, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (2489 : ℕ) ∧
    (∑ n ∈ Ico 188416 192512, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (557065 : ℤ) ∧
    (∑ n ∈ Ico 188416 192512, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (11141864763579426618638827842 : ℤ) := cdemPrefixStats_188416_192512
end Helfgott
#print axioms Helfgott.cdemPrefixGroup046_checked_complete

open Helfgott Finset
open scoped BigOperators

theorem solution :
    (∑ n ∈ Ico 188416 192512, mobiusTreeValue 16 mobiusTable1200001 n) = (21 : ℤ) ∧
    (∑ n ∈ Ico 188416 192512, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (2489 : ℕ) ∧
    (∑ n ∈ Ico 188416 192512, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (557065 : ℤ) ∧
    (∑ n ∈ Ico 188416 192512, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (11141864763579426618638827842 : ℤ) := Helfgott.cdemPrefixGroup046_checked_complete
#print axioms solution
