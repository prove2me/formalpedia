-- Prove2me | solution 1 for Helfgott.cdemPrefixGroup003_checked
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-09T01:17:16.911231+00:00
-- url     : https://prove2.me/submissions/69ea21c3-26ab-4143-8276-7f1b364af1c6

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
private theorem cdemPrefixStats_12288_12352 :
    (∑ n ∈ Ico 12288 12352, mobiusTreeValue 16 mobiusTable1200001 n) = (-6 : ℤ) ∧
    (∑ n ∈ Ico 12288 12352, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 12288 12352, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-2431575 : ℤ) ∧
    (∑ n ∈ Ico 12288 12352, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-48631595464321615704133261426 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_12352_12416 :
    (∑ n ∈ Ico 12352 12416, mobiusTreeValue 16 mobiusTable1200001 n) = (-3 : ℤ) ∧
    (∑ n ∈ Ico 12352 12416, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 12352 12416, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-1209187 : ℤ) ∧
    (∑ n ∈ Ico 12352 12416, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-24183756775223579448976474790 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_12288_12416 :
    (∑ n ∈ Ico 12288 12416, mobiusTreeValue 16 mobiusTable1200001 n) = (-9 : ℤ) ∧
    (∑ n ∈ Ico 12288 12416, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (79 : ℕ) ∧
    (∑ n ∈ Ico 12288 12416, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-3640762 : ℤ) ∧
    (∑ n ∈ Ico 12288 12416, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-72815352239545195153109736216 : ℤ) := by
  rcases cdemPrefixStats_12288_12352 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_12352_12416 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 12288 ≤ 12352) (by norm_num : 12352 ≤ 12416), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 12288 ≤ 12352) (by norm_num : 12352 ≤ 12416), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 12288 ≤ 12352) (by norm_num : 12352 ≤ 12416), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 12288 ≤ 12352) (by norm_num : 12352 ≤ 12416), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_12416_12480 :
    (∑ n ∈ Ico 12416 12480, mobiusTreeValue 16 mobiusTable1200001 n) = (3 : ℤ) ∧
    (∑ n ∈ Ico 12416 12480, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 12416 12480, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (1207239 : ℤ) ∧
    (∑ n ∈ Ico 12416 12480, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (24144823029700908312401831349 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_12480_12544 :
    (∑ n ∈ Ico 12480 12544, mobiusTreeValue 16 mobiusTable1200001 n) = (-8 : ℤ) ∧
    (∑ n ∈ Ico 12480 12544, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 12480 12544, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-3199716 : ℤ) ∧
    (∑ n ∈ Ico 12480 12544, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-63994376295571722451691165669 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_12416_12544 :
    (∑ n ∈ Ico 12416 12544, mobiusTreeValue 16 mobiusTable1200001 n) = (-5 : ℤ) ∧
    (∑ n ∈ Ico 12416 12544, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (75 : ℕ) ∧
    (∑ n ∈ Ico 12416 12544, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-1992477 : ℤ) ∧
    (∑ n ∈ Ico 12416 12544, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-39849553265870814139289334320 : ℤ) := by
  rcases cdemPrefixStats_12416_12480 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_12480_12544 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 12416 ≤ 12480) (by norm_num : 12480 ≤ 12544), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 12416 ≤ 12480) (by norm_num : 12480 ≤ 12544), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 12416 ≤ 12480) (by norm_num : 12480 ≤ 12544), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 12416 ≤ 12480) (by norm_num : 12480 ≤ 12544), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_12288_12544 :
    (∑ n ∈ Ico 12288 12544, mobiusTreeValue 16 mobiusTable1200001 n) = (-14 : ℤ) ∧
    (∑ n ∈ Ico 12288 12544, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (154 : ℕ) ∧
    (∑ n ∈ Ico 12288 12544, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-5633239 : ℤ) ∧
    (∑ n ∈ Ico 12288 12544, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-112664905505416009292399070536 : ℤ) := by
  rcases cdemPrefixStats_12288_12416 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_12416_12544 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 12288 ≤ 12416) (by norm_num : 12416 ≤ 12544), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 12288 ≤ 12416) (by norm_num : 12416 ≤ 12544), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 12288 ≤ 12416) (by norm_num : 12416 ≤ 12544), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 12288 ≤ 12416) (by norm_num : 12416 ≤ 12544), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_12544_12608 :
    (∑ n ∈ Ico 12544 12608, mobiusTreeValue 16 mobiusTable1200001 n) = (-4 : ℤ) ∧
    (∑ n ∈ Ico 12544 12608, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 12544 12608, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-1598518 : ℤ) ∧
    (∑ n ∈ Ico 12544 12608, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-31970350301631108787202737461 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_12608_12672 :
    (∑ n ∈ Ico 12608 12672, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 12608 12672, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 12608 12672, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-394668 : ℤ) ∧
    (∑ n ∈ Ico 12608 12672, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-7893325813696233894651151276 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_12544_12672 :
    (∑ n ∈ Ico 12544 12672, mobiusTreeValue 16 mobiusTable1200001 n) = (-5 : ℤ) ∧
    (∑ n ∈ Ico 12544 12672, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 12544 12672, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-1993186 : ℤ) ∧
    (∑ n ∈ Ico 12544 12672, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-39863676115327342681853888737 : ℤ) := by
  rcases cdemPrefixStats_12544_12608 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_12608_12672 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 12544 ≤ 12608) (by norm_num : 12608 ≤ 12672), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 12544 ≤ 12608) (by norm_num : 12608 ≤ 12672), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 12544 ≤ 12608) (by norm_num : 12608 ≤ 12672), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 12544 ≤ 12608) (by norm_num : 12608 ≤ 12672), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_12672_12736 :
    (∑ n ∈ Ico 12672 12736, mobiusTreeValue 16 mobiusTable1200001 n) = (8 : ℤ) ∧
    (∑ n ∈ Ico 12672 12736, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 12672 12736, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (3146448 : ℤ) ∧
    (∑ n ∈ Ico 12672 12736, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (62929052046687107573344650836 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_12736_12800 :
    (∑ n ∈ Ico 12736 12800, mobiusTreeValue 16 mobiusTable1200001 n) = (4 : ℤ) ∧
    (∑ n ∈ Ico 12736 12800, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 12736 12800, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (1564851 : ℤ) ∧
    (∑ n ∈ Ico 12736 12800, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (31297029750814597725655486188 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_12672_12800 :
    (∑ n ∈ Ico 12672 12800, mobiusTreeValue 16 mobiusTable1200001 n) = (12 : ℤ) ∧
    (∑ n ∈ Ico 12672 12800, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 12672 12800, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (4711299 : ℤ) ∧
    (∑ n ∈ Ico 12672 12800, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (94226081797501705299000137024 : ℤ) := by
  rcases cdemPrefixStats_12672_12736 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_12736_12800 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 12672 ≤ 12736) (by norm_num : 12736 ≤ 12800), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 12672 ≤ 12736) (by norm_num : 12736 ≤ 12800), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 12672 ≤ 12736) (by norm_num : 12736 ≤ 12800), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 12672 ≤ 12736) (by norm_num : 12736 ≤ 12800), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_12544_12800 :
    (∑ n ∈ Ico 12544 12800, mobiusTreeValue 16 mobiusTable1200001 n) = (7 : ℤ) ∧
    (∑ n ∈ Ico 12544 12800, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (155 : ℕ) ∧
    (∑ n ∈ Ico 12544 12800, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (2718113 : ℤ) ∧
    (∑ n ∈ Ico 12544 12800, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (54362405682174362617146248287 : ℤ) := by
  rcases cdemPrefixStats_12544_12672 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_12672_12800 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 12544 ≤ 12672) (by norm_num : 12672 ≤ 12800), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 12544 ≤ 12672) (by norm_num : 12672 ≤ 12800), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 12544 ≤ 12672) (by norm_num : 12672 ≤ 12800), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 12544 ≤ 12672) (by norm_num : 12672 ≤ 12800), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_12288_12800 :
    (∑ n ∈ Ico 12288 12800, mobiusTreeValue 16 mobiusTable1200001 n) = (-7 : ℤ) ∧
    (∑ n ∈ Ico 12288 12800, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (309 : ℕ) ∧
    (∑ n ∈ Ico 12288 12800, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-2915126 : ℤ) ∧
    (∑ n ∈ Ico 12288 12800, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-58302499823241646675252822249 : ℤ) := by
  rcases cdemPrefixStats_12288_12544 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_12544_12800 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 12288 ≤ 12544) (by norm_num : 12544 ≤ 12800), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 12288 ≤ 12544) (by norm_num : 12544 ≤ 12800), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 12288 ≤ 12544) (by norm_num : 12544 ≤ 12800), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 12288 ≤ 12544) (by norm_num : 12544 ≤ 12800), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_12800_12864 :
    (∑ n ∈ Ico 12800 12864, mobiusTreeValue 16 mobiusTable1200001 n) = (-10 : ℤ) ∧
    (∑ n ∈ Ico 12800 12864, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 12800 12864, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-3899435 : ℤ) ∧
    (∑ n ∈ Ico 12800 12864, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-77988786261800915744458967818 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_12864_12928 :
    (∑ n ∈ Ico 12864 12928, mobiusTreeValue 16 mobiusTable1200001 n) = (-10 : ℤ) ∧
    (∑ n ∈ Ico 12864 12928, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 12864 12928, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-3871223 : ℤ) ∧
    (∑ n ∈ Ico 12864 12928, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-77424604775116409935268217257 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_12800_12928 :
    (∑ n ∈ Ico 12800 12928, mobiusTreeValue 16 mobiusTable1200001 n) = (-20 : ℤ) ∧
    (∑ n ∈ Ico 12800 12928, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (80 : ℕ) ∧
    (∑ n ∈ Ico 12800 12928, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-7770658 : ℤ) ∧
    (∑ n ∈ Ico 12800 12928, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-155413391036917325679727185075 : ℤ) := by
  rcases cdemPrefixStats_12800_12864 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_12864_12928 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 12800 ≤ 12864) (by norm_num : 12864 ≤ 12928), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 12800 ≤ 12864) (by norm_num : 12864 ≤ 12928), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 12800 ≤ 12864) (by norm_num : 12864 ≤ 12928), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 12800 ≤ 12864) (by norm_num : 12864 ≤ 12928), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_12928_12992 :
    (∑ n ∈ Ico 12928 12992, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 12928 12992, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 12928 12992, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (386702 : ℤ) ∧
    (∑ n ∈ Ico 12928 12992, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (7734067239992219307314851138 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_12992_13056 :
    (∑ n ∈ Ico 12992 13056, mobiusTreeValue 16 mobiusTable1200001 n) = (-10 : ℤ) ∧
    (∑ n ∈ Ico 12992 13056, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 12992 13056, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-3842346 : ℤ) ∧
    (∑ n ∈ Ico 12992 13056, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-76847081045865922485708685330 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_12928_13056 :
    (∑ n ∈ Ico 12928 13056, mobiusTreeValue 16 mobiusTable1200001 n) = (-9 : ℤ) ∧
    (∑ n ∈ Ico 12928 13056, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 12928 13056, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-3455644 : ℤ) ∧
    (∑ n ∈ Ico 12928 13056, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-69113013805873703178393834192 : ℤ) := by
  rcases cdemPrefixStats_12928_12992 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_12992_13056 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 12928 ≤ 12992) (by norm_num : 12992 ≤ 13056), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 12928 ≤ 12992) (by norm_num : 12992 ≤ 13056), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 12928 ≤ 12992) (by norm_num : 12992 ≤ 13056), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 12928 ≤ 12992) (by norm_num : 12992 ≤ 13056), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_12800_13056 :
    (∑ n ∈ Ico 12800 13056, mobiusTreeValue 16 mobiusTable1200001 n) = (-29 : ℤ) ∧
    (∑ n ∈ Ico 12800 13056, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (157 : ℕ) ∧
    (∑ n ∈ Ico 12800 13056, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-11226302 : ℤ) ∧
    (∑ n ∈ Ico 12800 13056, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-224526404842791028858121019267 : ℤ) := by
  rcases cdemPrefixStats_12800_12928 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_12928_13056 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 12800 ≤ 12928) (by norm_num : 12928 ≤ 13056), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 12800 ≤ 12928) (by norm_num : 12928 ≤ 13056), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 12800 ≤ 12928) (by norm_num : 12928 ≤ 13056), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 12800 ≤ 12928) (by norm_num : 12928 ≤ 13056), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_13056_13120 :
    (∑ n ∈ Ico 13056 13120, mobiusTreeValue 16 mobiusTable1200001 n) = (3 : ℤ) ∧
    (∑ n ∈ Ico 13056 13120, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 13056 13120, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (1150529 : ℤ) ∧
    (∑ n ∈ Ico 13056 13120, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (23010609396284246565480161512 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_13120_13184 :
    (∑ n ∈ Ico 13120 13184, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 13120 13184, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 13120 13184, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (5430 : ℤ) ∧
    (∑ n ∈ Ico 13120 13184, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (108626841989372390884114409 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_13056_13184 :
    (∑ n ∈ Ico 13056 13184, mobiusTreeValue 16 mobiusTable1200001 n) = (3 : ℤ) ∧
    (∑ n ∈ Ico 13056 13184, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (79 : ℕ) ∧
    (∑ n ∈ Ico 13056 13184, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (1155959 : ℤ) ∧
    (∑ n ∈ Ico 13056 13184, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (23119236238273618956364275921 : ℤ) := by
  rcases cdemPrefixStats_13056_13120 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_13120_13184 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 13056 ≤ 13120) (by norm_num : 13120 ≤ 13184), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 13056 ≤ 13120) (by norm_num : 13120 ≤ 13184), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 13056 ≤ 13120) (by norm_num : 13120 ≤ 13184), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 13056 ≤ 13120) (by norm_num : 13120 ≤ 13184), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_13184_13248 :
    (∑ n ∈ Ico 13184 13248, mobiusTreeValue 16 mobiusTable1200001 n) = (-2 : ℤ) ∧
    (∑ n ∈ Ico 13184 13248, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 13184 13248, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-751797 : ℤ) ∧
    (∑ n ∈ Ico 13184 13248, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-15035970440519598185211297817 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_13248_13312 :
    (∑ n ∈ Ico 13248 13312, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 13248 13312, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 13248 13312, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-380674 : ℤ) ∧
    (∑ n ∈ Ico 13248 13312, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-7613540317095560892343356229 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_13184_13312 :
    (∑ n ∈ Ico 13184 13312, mobiusTreeValue 16 mobiusTable1200001 n) = (-3 : ℤ) ∧
    (∑ n ∈ Ico 13184 13312, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 13184 13312, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-1132471 : ℤ) ∧
    (∑ n ∈ Ico 13184 13312, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-22649510757615159077554654046 : ℤ) := by
  rcases cdemPrefixStats_13184_13248 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_13248_13312 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 13184 ≤ 13248) (by norm_num : 13248 ≤ 13312), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 13184 ≤ 13248) (by norm_num : 13248 ≤ 13312), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 13184 ≤ 13248) (by norm_num : 13248 ≤ 13312), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 13184 ≤ 13248) (by norm_num : 13248 ≤ 13312), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_13056_13312 :
    (∑ n ∈ Ico 13056 13312, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 13056 13312, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (156 : ℕ) ∧
    (∑ n ∈ Ico 13056 13312, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (23488 : ℤ) ∧
    (∑ n ∈ Ico 13056 13312, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (469725480658459878809621875 : ℤ) := by
  rcases cdemPrefixStats_13056_13184 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_13184_13312 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 13056 ≤ 13184) (by norm_num : 13184 ≤ 13312), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 13056 ≤ 13184) (by norm_num : 13184 ≤ 13312), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 13056 ≤ 13184) (by norm_num : 13184 ≤ 13312), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 13056 ≤ 13184) (by norm_num : 13184 ≤ 13312), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_12800_13312 :
    (∑ n ∈ Ico 12800 13312, mobiusTreeValue 16 mobiusTable1200001 n) = (-29 : ℤ) ∧
    (∑ n ∈ Ico 12800 13312, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (313 : ℕ) ∧
    (∑ n ∈ Ico 12800 13312, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-11202814 : ℤ) ∧
    (∑ n ∈ Ico 12800 13312, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-224056679362132568979311397392 : ℤ) := by
  rcases cdemPrefixStats_12800_13056 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_13056_13312 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 12800 ≤ 13056) (by norm_num : 13056 ≤ 13312), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 12800 ≤ 13056) (by norm_num : 13056 ≤ 13312), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 12800 ≤ 13056) (by norm_num : 13056 ≤ 13312), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 12800 ≤ 13056) (by norm_num : 13056 ≤ 13312), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_12288_13312 :
    (∑ n ∈ Ico 12288 13312, mobiusTreeValue 16 mobiusTable1200001 n) = (-36 : ℤ) ∧
    (∑ n ∈ Ico 12288 13312, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (622 : ℕ) ∧
    (∑ n ∈ Ico 12288 13312, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-14117940 : ℤ) ∧
    (∑ n ∈ Ico 12288 13312, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-282359179185374215654564219641 : ℤ) := by
  rcases cdemPrefixStats_12288_12800 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_12800_13312 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 12288 ≤ 12800) (by norm_num : 12800 ≤ 13312), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 12288 ≤ 12800) (by norm_num : 12800 ≤ 13312), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 12288 ≤ 12800) (by norm_num : 12800 ≤ 13312), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 12288 ≤ 12800) (by norm_num : 12800 ≤ 13312), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_13312_13376 :
    (∑ n ∈ Ico 13312 13376, mobiusTreeValue 16 mobiusTable1200001 n) = (6 : ℤ) ∧
    (∑ n ∈ Ico 13312 13376, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 13312 13376, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (2246661 : ℤ) ∧
    (∑ n ∈ Ico 13312 13376, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (44933284025796125652580654608 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_13376_13440 :
    (∑ n ∈ Ico 13376 13440, mobiusTreeValue 16 mobiusTable1200001 n) = (7 : ℤ) ∧
    (∑ n ∈ Ico 13376 13440, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 13376 13440, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (2612923 : ℤ) ∧
    (∑ n ∈ Ico 13376 13440, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (52258525927899305251479222335 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_13312_13440 :
    (∑ n ∈ Ico 13312 13440, mobiusTreeValue 16 mobiusTable1200001 n) = (13 : ℤ) ∧
    (∑ n ∈ Ico 13312 13440, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 13312 13440, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (4859584 : ℤ) ∧
    (∑ n ∈ Ico 13312 13440, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (97191809953695430904059876943 : ℤ) := by
  rcases cdemPrefixStats_13312_13376 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_13376_13440 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 13312 ≤ 13376) (by norm_num : 13376 ≤ 13440), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 13312 ≤ 13376) (by norm_num : 13376 ≤ 13440), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 13312 ≤ 13376) (by norm_num : 13376 ≤ 13440), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 13312 ≤ 13376) (by norm_num : 13376 ≤ 13440), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_13440_13504 :
    (∑ n ∈ Ico 13440 13504, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 13440 13504, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 13440 13504, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-369020 : ℤ) ∧
    (∑ n ∈ Ico 13440 13504, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-7380414799326264353893823598 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_13504_13568 :
    (∑ n ∈ Ico 13504 13568, mobiusTreeValue 16 mobiusTable1200001 n) = (8 : ℤ) ∧
    (∑ n ∈ Ico 13504 13568, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 13504 13568, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (2954889 : ℤ) ∧
    (∑ n ∈ Ico 13504 13568, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (59097905829572661658978614696 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_13440_13568 :
    (∑ n ∈ Ico 13440 13568, mobiusTreeValue 16 mobiusTable1200001 n) = (7 : ℤ) ∧
    (∑ n ∈ Ico 13440 13568, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (79 : ℕ) ∧
    (∑ n ∈ Ico 13440 13568, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (2585869 : ℤ) ∧
    (∑ n ∈ Ico 13440 13568, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (51717491030246397305084791098 : ℤ) := by
  rcases cdemPrefixStats_13440_13504 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_13504_13568 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 13440 ≤ 13504) (by norm_num : 13504 ≤ 13568), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 13440 ≤ 13504) (by norm_num : 13504 ≤ 13568), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 13440 ≤ 13504) (by norm_num : 13504 ≤ 13568), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 13440 ≤ 13504) (by norm_num : 13504 ≤ 13568), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_13312_13568 :
    (∑ n ∈ Ico 13312 13568, mobiusTreeValue 16 mobiusTable1200001 n) = (20 : ℤ) ∧
    (∑ n ∈ Ico 13312 13568, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (156 : ℕ) ∧
    (∑ n ∈ Ico 13312 13568, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (7445453 : ℤ) ∧
    (∑ n ∈ Ico 13312 13568, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (148909300983941828209144668041 : ℤ) := by
  rcases cdemPrefixStats_13312_13440 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_13440_13568 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 13312 ≤ 13440) (by norm_num : 13440 ≤ 13568), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 13312 ≤ 13440) (by norm_num : 13440 ≤ 13568), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 13312 ≤ 13440) (by norm_num : 13440 ≤ 13568), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 13312 ≤ 13440) (by norm_num : 13440 ≤ 13568), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_13568_13632 :
    (∑ n ∈ Ico 13568 13632, mobiusTreeValue 16 mobiusTable1200001 n) = (-2 : ℤ) ∧
    (∑ n ∈ Ico 13568 13632, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 13568 13632, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-731804 : ℤ) ∧
    (∑ n ∈ Ico 13568 13632, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-14635998311464182852502041480 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_13632_13696 :
    (∑ n ∈ Ico 13632 13696, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 13632 13696, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 13632 13696, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (369719 : ℤ) ∧
    (∑ n ∈ Ico 13632 13696, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (7394475215078733659567676615 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_13568_13696 :
    (∑ n ∈ Ico 13568 13696, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 13568 13696, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 13568 13696, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-362085 : ℤ) ∧
    (∑ n ∈ Ico 13568 13696, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-7241523096385449192934364865 : ℤ) := by
  rcases cdemPrefixStats_13568_13632 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_13632_13696 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 13568 ≤ 13632) (by norm_num : 13632 ≤ 13696), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 13568 ≤ 13632) (by norm_num : 13632 ≤ 13696), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 13568 ≤ 13632) (by norm_num : 13632 ≤ 13696), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 13568 ≤ 13632) (by norm_num : 13632 ≤ 13696), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_13696_13760 :
    (∑ n ∈ Ico 13696 13760, mobiusTreeValue 16 mobiusTable1200001 n) = (-4 : ℤ) ∧
    (∑ n ∈ Ico 13696 13760, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 13696 13760, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-1457537 : ℤ) ∧
    (∑ n ∈ Ico 13696 13760, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-29150791684510298136576110350 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_13760_13824 :
    (∑ n ∈ Ico 13760 13824, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 13760 13824, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 13760 13824, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (359009 : ℤ) ∧
    (∑ n ∈ Ico 13760 13824, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (7180227967576148800788866713 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_13696_13824 :
    (∑ n ∈ Ico 13696 13824, mobiusTreeValue 16 mobiusTable1200001 n) = (-3 : ℤ) ∧
    (∑ n ∈ Ico 13696 13824, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 13696 13824, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-1098528 : ℤ) ∧
    (∑ n ∈ Ico 13696 13824, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-21970563716934149335787243637 : ℤ) := by
  rcases cdemPrefixStats_13696_13760 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_13760_13824 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 13696 ≤ 13760) (by norm_num : 13760 ≤ 13824), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 13696 ≤ 13760) (by norm_num : 13760 ≤ 13824), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 13696 ≤ 13760) (by norm_num : 13760 ≤ 13824), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 13696 ≤ 13760) (by norm_num : 13760 ≤ 13824), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_13568_13824 :
    (∑ n ∈ Ico 13568 13824, mobiusTreeValue 16 mobiusTable1200001 n) = (-4 : ℤ) ∧
    (∑ n ∈ Ico 13568 13824, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (154 : ℕ) ∧
    (∑ n ∈ Ico 13568 13824, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-1460613 : ℤ) ∧
    (∑ n ∈ Ico 13568 13824, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-29212086813319598528721608502 : ℤ) := by
  rcases cdemPrefixStats_13568_13696 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_13696_13824 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 13568 ≤ 13696) (by norm_num : 13696 ≤ 13824), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 13568 ≤ 13696) (by norm_num : 13696 ≤ 13824), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 13568 ≤ 13696) (by norm_num : 13696 ≤ 13824), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 13568 ≤ 13696) (by norm_num : 13696 ≤ 13824), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_13312_13824 :
    (∑ n ∈ Ico 13312 13824, mobiusTreeValue 16 mobiusTable1200001 n) = (16 : ℤ) ∧
    (∑ n ∈ Ico 13312 13824, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (310 : ℕ) ∧
    (∑ n ∈ Ico 13312 13824, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (5984840 : ℤ) ∧
    (∑ n ∈ Ico 13312 13824, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (119697214170622229680423059539 : ℤ) := by
  rcases cdemPrefixStats_13312_13568 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_13568_13824 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 13312 ≤ 13568) (by norm_num : 13568 ≤ 13824), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 13312 ≤ 13568) (by norm_num : 13568 ≤ 13824), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 13312 ≤ 13568) (by norm_num : 13568 ≤ 13824), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 13312 ≤ 13568) (by norm_num : 13568 ≤ 13824), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_13824_13888 :
    (∑ n ∈ Ico 13824 13888, mobiusTreeValue 16 mobiusTable1200001 n) = (-7 : ℤ) ∧
    (∑ n ∈ Ico 13824 13888, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 13824 13888, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-2521064 : ℤ) ∧
    (∑ n ∈ Ico 13824 13888, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-50421361984962922541138428021 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_13888_13952 :
    (∑ n ∈ Ico 13888 13952, mobiusTreeValue 16 mobiusTable1200001 n) = (9 : ℤ) ∧
    (∑ n ∈ Ico 13888 13952, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 13888 13952, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (3230408 : ℤ) ∧
    (∑ n ∈ Ico 13888 13952, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (64608297773794357056077233728 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_13824_13952 :
    (∑ n ∈ Ico 13824 13952, mobiusTreeValue 16 mobiusTable1200001 n) = (2 : ℤ) ∧
    (∑ n ∈ Ico 13824 13952, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 13824 13952, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (709344 : ℤ) ∧
    (∑ n ∈ Ico 13824 13952, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (14186935788831434514938805707 : ℤ) := by
  rcases cdemPrefixStats_13824_13888 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_13888_13952 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 13824 ≤ 13888) (by norm_num : 13888 ≤ 13952), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 13824 ≤ 13888) (by norm_num : 13888 ≤ 13952), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 13824 ≤ 13888) (by norm_num : 13888 ≤ 13952), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 13824 ≤ 13888) (by norm_num : 13888 ≤ 13952), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_13952_14016 :
    (∑ n ∈ Ico 13952 14016, mobiusTreeValue 16 mobiusTable1200001 n) = (10 : ℤ) ∧
    (∑ n ∈ Ico 13952 14016, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 13952 14016, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (3580117 : ℤ) ∧
    (∑ n ∈ Ico 13952 14016, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (71602499723423930784776839103 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_14016_14080 :
    (∑ n ∈ Ico 14016 14080, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 14016 14080, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (36 : ℕ) ∧
    (∑ n ∈ Ico 14016 14080, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (3372 : ℤ) ∧
    (∑ n ∈ Ico 14016 14080, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (67488304002244273664197387 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_13952_14080 :
    (∑ n ∈ Ico 13952 14080, mobiusTreeValue 16 mobiusTable1200001 n) = (10 : ℤ) ∧
    (∑ n ∈ Ico 13952 14080, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (76 : ℕ) ∧
    (∑ n ∈ Ico 13952 14080, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (3583489 : ℤ) ∧
    (∑ n ∈ Ico 13952 14080, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (71669988027426175058441036490 : ℤ) := by
  rcases cdemPrefixStats_13952_14016 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_14016_14080 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 13952 ≤ 14016) (by norm_num : 14016 ≤ 14080), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 13952 ≤ 14016) (by norm_num : 14016 ≤ 14080), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 13952 ≤ 14016) (by norm_num : 14016 ≤ 14080), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 13952 ≤ 14016) (by norm_num : 14016 ≤ 14080), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_13824_14080 :
    (∑ n ∈ Ico 13824 14080, mobiusTreeValue 16 mobiusTable1200001 n) = (12 : ℤ) ∧
    (∑ n ∈ Ico 13824 14080, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (154 : ℕ) ∧
    (∑ n ∈ Ico 13824 14080, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (4292833 : ℤ) ∧
    (∑ n ∈ Ico 13824 14080, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (85856923816257609573379842197 : ℤ) := by
  rcases cdemPrefixStats_13824_13952 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_13952_14080 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 13824 ≤ 13952) (by norm_num : 13952 ≤ 14080), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 13824 ≤ 13952) (by norm_num : 13952 ≤ 14080), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 13824 ≤ 13952) (by norm_num : 13952 ≤ 14080), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 13824 ≤ 13952) (by norm_num : 13952 ≤ 14080), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_14080_14144 :
    (∑ n ∈ Ico 14080 14144, mobiusTreeValue 16 mobiusTable1200001 n) = (5 : ℤ) ∧
    (∑ n ∈ Ico 14080 14144, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 14080 14144, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (1771662 : ℤ) ∧
    (∑ n ∈ Ico 14080 14144, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (35433272436506914697402914481 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_14144_14208 :
    (∑ n ∈ Ico 14144 14208, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 14144 14208, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 14144 14208, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-354154 : ℤ) ∧
    (∑ n ∈ Ico 14144 14208, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-7083130564815129958238801581 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_14080_14208 :
    (∑ n ∈ Ico 14080 14208, mobiusTreeValue 16 mobiusTable1200001 n) = (4 : ℤ) ∧
    (∑ n ∈ Ico 14080 14208, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (82 : ℕ) ∧
    (∑ n ∈ Ico 14080 14208, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (1417508 : ℤ) ∧
    (∑ n ∈ Ico 14080 14208, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (28350141871691784739164112900 : ℤ) := by
  rcases cdemPrefixStats_14080_14144 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_14144_14208 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 14080 ≤ 14144) (by norm_num : 14144 ≤ 14208), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 14080 ≤ 14144) (by norm_num : 14144 ≤ 14208), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 14080 ≤ 14144) (by norm_num : 14144 ≤ 14208), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 14080 ≤ 14144) (by norm_num : 14144 ≤ 14208), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_14208_14272 :
    (∑ n ∈ Ico 14208 14272, mobiusTreeValue 16 mobiusTable1200001 n) = (5 : ℤ) ∧
    (∑ n ∈ Ico 14208 14272, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 14208 14272, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (1756116 : ℤ) ∧
    (∑ n ∈ Ico 14208 14272, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (35122318195939708464228285651 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_14272_14336 :
    (∑ n ∈ Ico 14272 14336, mobiusTreeValue 16 mobiusTable1200001 n) = (-11 : ℤ) ∧
    (∑ n ∈ Ico 14272 14336, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 14272 14336, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-3841757 : ℤ) ∧
    (∑ n ∈ Ico 14272 14336, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-76835214035237752356197276926 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_14208_14336 :
    (∑ n ∈ Ico 14208 14336, mobiusTreeValue 16 mobiusTable1200001 n) = (-6 : ℤ) ∧
    (∑ n ∈ Ico 14208 14336, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 14208 14336, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-2085641 : ℤ) ∧
    (∑ n ∈ Ico 14208 14336, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-41712895839298043891968991275 : ℤ) := by
  rcases cdemPrefixStats_14208_14272 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_14272_14336 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 14208 ≤ 14272) (by norm_num : 14272 ≤ 14336), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 14208 ≤ 14272) (by norm_num : 14272 ≤ 14336), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 14208 ≤ 14272) (by norm_num : 14272 ≤ 14336), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 14208 ≤ 14272) (by norm_num : 14272 ≤ 14336), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_14080_14336 :
    (∑ n ∈ Ico 14080 14336, mobiusTreeValue 16 mobiusTable1200001 n) = (-2 : ℤ) ∧
    (∑ n ∈ Ico 14080 14336, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (160 : ℕ) ∧
    (∑ n ∈ Ico 14080 14336, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-668133 : ℤ) ∧
    (∑ n ∈ Ico 14080 14336, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-13362753967606259152804878375 : ℤ) := by
  rcases cdemPrefixStats_14080_14208 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_14208_14336 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 14080 ≤ 14208) (by norm_num : 14208 ≤ 14336), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 14080 ≤ 14208) (by norm_num : 14208 ≤ 14336), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 14080 ≤ 14208) (by norm_num : 14208 ≤ 14336), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 14080 ≤ 14208) (by norm_num : 14208 ≤ 14336), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_13824_14336 :
    (∑ n ∈ Ico 13824 14336, mobiusTreeValue 16 mobiusTable1200001 n) = (10 : ℤ) ∧
    (∑ n ∈ Ico 13824 14336, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (314 : ℕ) ∧
    (∑ n ∈ Ico 13824 14336, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (3624700 : ℤ) ∧
    (∑ n ∈ Ico 13824 14336, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (72494169848651350420574963822 : ℤ) := by
  rcases cdemPrefixStats_13824_14080 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_14080_14336 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 13824 ≤ 14080) (by norm_num : 14080 ≤ 14336), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 13824 ≤ 14080) (by norm_num : 14080 ≤ 14336), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 13824 ≤ 14080) (by norm_num : 14080 ≤ 14336), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 13824 ≤ 14080) (by norm_num : 14080 ≤ 14336), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_13312_14336 :
    (∑ n ∈ Ico 13312 14336, mobiusTreeValue 16 mobiusTable1200001 n) = (26 : ℤ) ∧
    (∑ n ∈ Ico 13312 14336, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (624 : ℕ) ∧
    (∑ n ∈ Ico 13312 14336, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (9609540 : ℤ) ∧
    (∑ n ∈ Ico 13312 14336, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (192191384019273580100998023361 : ℤ) := by
  rcases cdemPrefixStats_13312_13824 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_13824_14336 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 13312 ≤ 13824) (by norm_num : 13824 ≤ 14336), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 13312 ≤ 13824) (by norm_num : 13824 ≤ 14336), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 13312 ≤ 13824) (by norm_num : 13824 ≤ 14336), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 13312 ≤ 13824) (by norm_num : 13824 ≤ 14336), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_12288_14336 :
    (∑ n ∈ Ico 12288 14336, mobiusTreeValue 16 mobiusTable1200001 n) = (-10 : ℤ) ∧
    (∑ n ∈ Ico 12288 14336, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (1246 : ℕ) ∧
    (∑ n ∈ Ico 12288 14336, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-4508400 : ℤ) ∧
    (∑ n ∈ Ico 12288 14336, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-90167795166100635553566196280 : ℤ) := by
  rcases cdemPrefixStats_12288_13312 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_13312_14336 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 12288 ≤ 13312) (by norm_num : 13312 ≤ 14336), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 12288 ≤ 13312) (by norm_num : 13312 ≤ 14336), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 12288 ≤ 13312) (by norm_num : 13312 ≤ 14336), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 12288 ≤ 13312) (by norm_num : 13312 ≤ 14336), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_14336_14400 :
    (∑ n ∈ Ico 14336 14400, mobiusTreeValue 16 mobiusTable1200001 n) = (7 : ℤ) ∧
    (∑ n ∈ Ico 14336 14400, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 14336 14400, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (2433059 : ℤ) ∧
    (∑ n ∈ Ico 14336 14400, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (48661204581099535868223704304 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_14400_14464 :
    (∑ n ∈ Ico 14400 14464, mobiusTreeValue 16 mobiusTable1200001 n) = (-3 : ℤ) ∧
    (∑ n ∈ Ico 14400 14464, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 14400 14464, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-1040395 : ℤ) ∧
    (∑ n ∈ Ico 14400 14464, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-20807880519160350286976881475 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_14336_14464 :
    (∑ n ∈ Ico 14336 14464, mobiusTreeValue 16 mobiusTable1200001 n) = (4 : ℤ) ∧
    (∑ n ∈ Ico 14336 14464, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (74 : ℕ) ∧
    (∑ n ∈ Ico 14336 14464, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (1392664 : ℤ) ∧
    (∑ n ∈ Ico 14336 14464, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (27853324061939185581246822829 : ℤ) := by
  rcases cdemPrefixStats_14336_14400 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_14400_14464 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 14336 ≤ 14400) (by norm_num : 14400 ≤ 14464), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 14336 ≤ 14400) (by norm_num : 14400 ≤ 14464), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 14336 ≤ 14400) (by norm_num : 14400 ≤ 14464), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 14336 ≤ 14400) (by norm_num : 14400 ≤ 14464), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_14464_14528 :
    (∑ n ∈ Ico 14464 14528, mobiusTreeValue 16 mobiusTable1200001 n) = (3 : ℤ) ∧
    (∑ n ∈ Ico 14464 14528, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 14464 14528, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (1034122 : ℤ) ∧
    (∑ n ∈ Ico 14464 14528, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (20682528929468735570464114985 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_14528_14592 :
    (∑ n ∈ Ico 14528 14592, mobiusTreeValue 16 mobiusTable1200001 n) = (-16 : ℤ) ∧
    (∑ n ∈ Ico 14528 14592, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 14528 14592, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-5499768 : ℤ) ∧
    (∑ n ∈ Ico 14528 14592, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-109995473137778004773623527680 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_14464_14592 :
    (∑ n ∈ Ico 14464 14592, mobiusTreeValue 16 mobiusTable1200001 n) = (-13 : ℤ) ∧
    (∑ n ∈ Ico 14464 14592, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (81 : ℕ) ∧
    (∑ n ∈ Ico 14464 14592, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-4465646 : ℤ) ∧
    (∑ n ∈ Ico 14464 14592, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-89312944208309269203159412695 : ℤ) := by
  rcases cdemPrefixStats_14464_14528 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_14528_14592 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 14464 ≤ 14528) (by norm_num : 14528 ≤ 14592), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 14464 ≤ 14528) (by norm_num : 14528 ≤ 14592), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 14464 ≤ 14528) (by norm_num : 14528 ≤ 14592), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 14464 ≤ 14528) (by norm_num : 14528 ≤ 14592), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_14336_14592 :
    (∑ n ∈ Ico 14336 14592, mobiusTreeValue 16 mobiusTable1200001 n) = (-9 : ℤ) ∧
    (∑ n ∈ Ico 14336 14592, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (155 : ℕ) ∧
    (∑ n ∈ Ico 14336 14592, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-3072982 : ℤ) ∧
    (∑ n ∈ Ico 14336 14592, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-61459620146370083621912589866 : ℤ) := by
  rcases cdemPrefixStats_14336_14464 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_14464_14592 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 14336 ≤ 14464) (by norm_num : 14464 ≤ 14592), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 14336 ≤ 14464) (by norm_num : 14464 ≤ 14592), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 14336 ≤ 14464) (by norm_num : 14464 ≤ 14592), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 14336 ≤ 14464) (by norm_num : 14464 ≤ 14592), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_14592_14656 :
    (∑ n ∈ Ico 14592 14656, mobiusTreeValue 16 mobiusTable1200001 n) = (-3 : ℤ) ∧
    (∑ n ∈ Ico 14592 14656, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 14592 14656, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-1020123 : ℤ) ∧
    (∑ n ∈ Ico 14592 14656, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-20402516089587941778862570158 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_14656_14720 :
    (∑ n ∈ Ico 14656 14720, mobiusTreeValue 16 mobiusTable1200001 n) = (6 : ℤ) ∧
    (∑ n ∈ Ico 14656 14720, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 14656 14720, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (2043270 : ℤ) ∧
    (∑ n ∈ Ico 14656 14720, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (40865469328193514472058006710 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_14592_14720 :
    (∑ n ∈ Ico 14592 14720, mobiusTreeValue 16 mobiusTable1200001 n) = (3 : ℤ) ∧
    (∑ n ∈ Ico 14592 14720, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (79 : ℕ) ∧
    (∑ n ∈ Ico 14592 14720, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (1023147 : ℤ) ∧
    (∑ n ∈ Ico 14592 14720, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (20462953238605572693195436552 : ℤ) := by
  rcases cdemPrefixStats_14592_14656 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_14656_14720 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 14592 ≤ 14656) (by norm_num : 14656 ≤ 14720), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 14592 ≤ 14656) (by norm_num : 14656 ≤ 14720), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 14592 ≤ 14656) (by norm_num : 14656 ≤ 14720), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 14592 ≤ 14656) (by norm_num : 14656 ≤ 14720), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_14720_14784 :
    (∑ n ∈ Ico 14720 14784, mobiusTreeValue 16 mobiusTable1200001 n) = (-15 : ℤ) ∧
    (∑ n ∈ Ico 14720 14784, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 14720 14784, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-5085235 : ℤ) ∧
    (∑ n ∈ Ico 14720 14784, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-101704797759895338631196116556 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_14784_14848 :
    (∑ n ∈ Ico 14784 14848, mobiusTreeValue 16 mobiusTable1200001 n) = (-5 : ℤ) ∧
    (∑ n ∈ Ico 14784 14848, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 14784 14848, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-1684426 : ℤ) ∧
    (∑ n ∈ Ico 14784 14848, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-33688534467313416794154144141 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_14720_14848 :
    (∑ n ∈ Ico 14720 14848, mobiusTreeValue 16 mobiusTable1200001 n) = (-20 : ℤ) ∧
    (∑ n ∈ Ico 14720 14848, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (76 : ℕ) ∧
    (∑ n ∈ Ico 14720 14848, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-6769661 : ℤ) ∧
    (∑ n ∈ Ico 14720 14848, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-135393332227208755425350260697 : ℤ) := by
  rcases cdemPrefixStats_14720_14784 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_14784_14848 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 14720 ≤ 14784) (by norm_num : 14784 ≤ 14848), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 14720 ≤ 14784) (by norm_num : 14784 ≤ 14848), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 14720 ≤ 14784) (by norm_num : 14784 ≤ 14848), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 14720 ≤ 14784) (by norm_num : 14784 ≤ 14848), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_14592_14848 :
    (∑ n ∈ Ico 14592 14848, mobiusTreeValue 16 mobiusTable1200001 n) = (-17 : ℤ) ∧
    (∑ n ∈ Ico 14592 14848, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (155 : ℕ) ∧
    (∑ n ∈ Ico 14592 14848, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-5746514 : ℤ) ∧
    (∑ n ∈ Ico 14592 14848, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-114930378988603182732154824145 : ℤ) := by
  rcases cdemPrefixStats_14592_14720 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_14720_14848 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 14592 ≤ 14720) (by norm_num : 14720 ≤ 14848), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 14592 ≤ 14720) (by norm_num : 14720 ≤ 14848), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 14592 ≤ 14720) (by norm_num : 14720 ≤ 14848), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 14592 ≤ 14720) (by norm_num : 14720 ≤ 14848), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_14336_14848 :
    (∑ n ∈ Ico 14336 14848, mobiusTreeValue 16 mobiusTable1200001 n) = (-26 : ℤ) ∧
    (∑ n ∈ Ico 14336 14848, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (310 : ℕ) ∧
    (∑ n ∈ Ico 14336 14848, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-8819496 : ℤ) ∧
    (∑ n ∈ Ico 14336 14848, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-176389999134973266354067414011 : ℤ) := by
  rcases cdemPrefixStats_14336_14592 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_14592_14848 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 14336 ≤ 14592) (by norm_num : 14592 ≤ 14848), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 14336 ≤ 14592) (by norm_num : 14592 ≤ 14848), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 14336 ≤ 14592) (by norm_num : 14592 ≤ 14848), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 14336 ≤ 14592) (by norm_num : 14592 ≤ 14848), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_14848_14912 :
    (∑ n ∈ Ico 14848 14912, mobiusTreeValue 16 mobiusTable1200001 n) = (-3 : ℤ) ∧
    (∑ n ∈ Ico 14848 14912, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 14848 14912, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-1006912 : ℤ) ∧
    (∑ n ∈ Ico 14848 14912, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-20138225874204101294758578702 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_14912_14976 :
    (∑ n ∈ Ico 14912 14976, mobiusTreeValue 16 mobiusTable1200001 n) = (2 : ℤ) ∧
    (∑ n ∈ Ico 14912 14976, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 14912 14976, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (667447 : ℤ) ∧
    (∑ n ∈ Ico 14912 14976, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (13348934690721613843734021672 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_14848_14976 :
    (∑ n ∈ Ico 14848 14976, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 14848 14976, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (79 : ℕ) ∧
    (∑ n ∈ Ico 14848 14976, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-339465 : ℤ) ∧
    (∑ n ∈ Ico 14848 14976, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-6789291183482487451024557030 : ℤ) := by
  rcases cdemPrefixStats_14848_14912 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_14912_14976 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 14848 ≤ 14912) (by norm_num : 14912 ≤ 14976), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 14848 ≤ 14912) (by norm_num : 14912 ≤ 14976), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 14848 ≤ 14912) (by norm_num : 14912 ≤ 14976), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 14848 ≤ 14912) (by norm_num : 14912 ≤ 14976), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_14976_15040 :
    (∑ n ∈ Ico 14976 15040, mobiusTreeValue 16 mobiusTable1200001 n) = (11 : ℤ) ∧
    (∑ n ∈ Ico 14976 15040, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 14976 15040, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (3667712 : ℤ) ∧
    (∑ n ∈ Ico 14976 15040, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (73354279225386540658944917617 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_15040_15104 :
    (∑ n ∈ Ico 15040 15104, mobiusTreeValue 16 mobiusTable1200001 n) = (7 : ℤ) ∧
    (∑ n ∈ Ico 15040 15104, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 15040 15104, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (2323906 : ℤ) ∧
    (∑ n ∈ Ico 15040 15104, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (46478207253699567929984460980 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_14976_15104 :
    (∑ n ∈ Ico 14976 15104, mobiusTreeValue 16 mobiusTable1200001 n) = (18 : ℤ) ∧
    (∑ n ∈ Ico 14976 15104, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (80 : ℕ) ∧
    (∑ n ∈ Ico 14976 15104, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (5991618 : ℤ) ∧
    (∑ n ∈ Ico 14976 15104, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (119832486479086108588929378597 : ℤ) := by
  rcases cdemPrefixStats_14976_15040 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_15040_15104 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 14976 ≤ 15040) (by norm_num : 15040 ≤ 15104), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 14976 ≤ 15040) (by norm_num : 15040 ≤ 15104), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 14976 ≤ 15040) (by norm_num : 15040 ≤ 15104), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 14976 ≤ 15040) (by norm_num : 15040 ≤ 15104), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_14848_15104 :
    (∑ n ∈ Ico 14848 15104, mobiusTreeValue 16 mobiusTable1200001 n) = (17 : ℤ) ∧
    (∑ n ∈ Ico 14848 15104, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (159 : ℕ) ∧
    (∑ n ∈ Ico 14848 15104, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (5652153 : ℤ) ∧
    (∑ n ∈ Ico 14848 15104, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (113043195295603621137904821567 : ℤ) := by
  rcases cdemPrefixStats_14848_14976 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_14976_15104 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 14848 ≤ 14976) (by norm_num : 14976 ≤ 15104), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 14848 ≤ 14976) (by norm_num : 14976 ≤ 15104), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 14848 ≤ 14976) (by norm_num : 14976 ≤ 15104), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 14848 ≤ 14976) (by norm_num : 14976 ≤ 15104), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_15104_15168 :
    (∑ n ∈ Ico 15104 15168, mobiusTreeValue 16 mobiusTable1200001 n) = (8 : ℤ) ∧
    (∑ n ∈ Ico 15104 15168, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 15104 15168, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (2642951 : ℤ) ∧
    (∑ n ∈ Ico 15104 15168, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (52859071355690377159815528912 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_15168_15232 :
    (∑ n ∈ Ico 15168 15232, mobiusTreeValue 16 mobiusTable1200001 n) = (-4 : ℤ) ∧
    (∑ n ∈ Ico 15168 15232, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 15168 15232, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-1316288 : ℤ) ∧
    (∑ n ∈ Ico 15168 15232, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-26325755700390901823983667856 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_15104_15232 :
    (∑ n ∈ Ico 15104 15232, mobiusTreeValue 16 mobiusTable1200001 n) = (4 : ℤ) ∧
    (∑ n ∈ Ico 15104 15232, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 15104 15232, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (1326663 : ℤ) ∧
    (∑ n ∈ Ico 15104 15232, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (26533315655299475335831861056 : ℤ) := by
  rcases cdemPrefixStats_15104_15168 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_15168_15232 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 15104 ≤ 15168) (by norm_num : 15168 ≤ 15232), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 15104 ≤ 15168) (by norm_num : 15168 ≤ 15232), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 15104 ≤ 15168) (by norm_num : 15168 ≤ 15232), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 15104 ≤ 15168) (by norm_num : 15168 ≤ 15232), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_15232_15296 :
    (∑ n ∈ Ico 15232 15296, mobiusTreeValue 16 mobiusTable1200001 n) = (-11 : ℤ) ∧
    (∑ n ∈ Ico 15232 15296, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 15232 15296, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-3602946 : ℤ) ∧
    (∑ n ∈ Ico 15232 15296, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-72059052680861345565237602038 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_15296_15360 :
    (∑ n ∈ Ico 15296 15360, mobiusTreeValue 16 mobiusTable1200001 n) = (-4 : ℤ) ∧
    (∑ n ∈ Ico 15296 15360, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 15296 15360, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-1306397 : ℤ) ∧
    (∑ n ∈ Ico 15296 15360, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-26127970410093425333788395210 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_15232_15360 :
    (∑ n ∈ Ico 15232 15360, mobiusTreeValue 16 mobiusTable1200001 n) = (-15 : ℤ) ∧
    (∑ n ∈ Ico 15232 15360, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 15232 15360, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-4909343 : ℤ) ∧
    (∑ n ∈ Ico 15232 15360, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-98187023090954770899025997248 : ℤ) := by
  rcases cdemPrefixStats_15232_15296 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_15296_15360 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 15232 ≤ 15296) (by norm_num : 15296 ≤ 15360), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 15232 ≤ 15296) (by norm_num : 15296 ≤ 15360), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 15232 ≤ 15296) (by norm_num : 15296 ≤ 15360), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 15232 ≤ 15296) (by norm_num : 15296 ≤ 15360), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_15104_15360 :
    (∑ n ∈ Ico 15104 15360, mobiusTreeValue 16 mobiusTable1200001 n) = (-11 : ℤ) ∧
    (∑ n ∈ Ico 15104 15360, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (155 : ℕ) ∧
    (∑ n ∈ Ico 15104 15360, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-3582680 : ℤ) ∧
    (∑ n ∈ Ico 15104 15360, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-71653707435655295563194136192 : ℤ) := by
  rcases cdemPrefixStats_15104_15232 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_15232_15360 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 15104 ≤ 15232) (by norm_num : 15232 ≤ 15360), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 15104 ≤ 15232) (by norm_num : 15232 ≤ 15360), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 15104 ≤ 15232) (by norm_num : 15232 ≤ 15360), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 15104 ≤ 15232) (by norm_num : 15232 ≤ 15360), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_14848_15360 :
    (∑ n ∈ Ico 14848 15360, mobiusTreeValue 16 mobiusTable1200001 n) = (6 : ℤ) ∧
    (∑ n ∈ Ico 14848 15360, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (314 : ℕ) ∧
    (∑ n ∈ Ico 14848 15360, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (2069473 : ℤ) ∧
    (∑ n ∈ Ico 14848 15360, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (41389487859948325574710685375 : ℤ) := by
  rcases cdemPrefixStats_14848_15104 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_15104_15360 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 14848 ≤ 15104) (by norm_num : 15104 ≤ 15360), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 14848 ≤ 15104) (by norm_num : 15104 ≤ 15360), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 14848 ≤ 15104) (by norm_num : 15104 ≤ 15360), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 14848 ≤ 15104) (by norm_num : 15104 ≤ 15360), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_14336_15360 :
    (∑ n ∈ Ico 14336 15360, mobiusTreeValue 16 mobiusTable1200001 n) = (-20 : ℤ) ∧
    (∑ n ∈ Ico 14336 15360, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (624 : ℕ) ∧
    (∑ n ∈ Ico 14336 15360, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-6750023 : ℤ) ∧
    (∑ n ∈ Ico 14336 15360, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-135000511275024940779356728636 : ℤ) := by
  rcases cdemPrefixStats_14336_14848 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_14848_15360 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 14336 ≤ 14848) (by norm_num : 14848 ≤ 15360), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 14336 ≤ 14848) (by norm_num : 14848 ≤ 15360), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 14336 ≤ 14848) (by norm_num : 14848 ≤ 15360), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 14336 ≤ 14848) (by norm_num : 14848 ≤ 15360), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_15360_15424 :
    (∑ n ∈ Ico 15360 15424, mobiusTreeValue 16 mobiusTable1200001 n) = (3 : ℤ) ∧
    (∑ n ∈ Ico 15360 15424, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 15360 15424, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (973751 : ℤ) ∧
    (∑ n ∈ Ico 15360 15424, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (19475037179332805434909679255 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_15424_15488 :
    (∑ n ∈ Ico 15424 15488, mobiusTreeValue 16 mobiusTable1200001 n) = (-3 : ℤ) ∧
    (∑ n ∈ Ico 15424 15488, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 15424 15488, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-971793 : ℤ) ∧
    (∑ n ∈ Ico 15424 15488, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-19435889676792215057661276232 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_15360_15488 :
    (∑ n ∈ Ico 15360 15488, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 15360 15488, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 15360 15488, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (1958 : ℤ) ∧
    (∑ n ∈ Ico 15360 15488, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (39147502540590377248403023 : ℤ) := by
  rcases cdemPrefixStats_15360_15424 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_15424_15488 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 15360 ≤ 15424) (by norm_num : 15424 ≤ 15488), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 15360 ≤ 15424) (by norm_num : 15424 ≤ 15488), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 15360 ≤ 15424) (by norm_num : 15424 ≤ 15488), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 15360 ≤ 15424) (by norm_num : 15424 ≤ 15488), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_15488_15552 :
    (∑ n ∈ Ico 15488 15552, mobiusTreeValue 16 mobiusTable1200001 n) = (-7 : ℤ) ∧
    (∑ n ∈ Ico 15488 15552, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 15488 15552, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-2254365 : ℤ) ∧
    (∑ n ∈ Ico 15488 15552, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-45087424676956054918395061094 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_15552_15616 :
    (∑ n ∈ Ico 15552 15616, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 15552 15616, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 15552 15616, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-320634 : ℤ) ∧
    (∑ n ∈ Ico 15552 15616, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-6412665021459494237816008257 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_15488_15616 :
    (∑ n ∈ Ico 15488 15616, mobiusTreeValue 16 mobiusTable1200001 n) = (-8 : ℤ) ∧
    (∑ n ∈ Ico 15488 15616, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 15488 15616, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-2574999 : ℤ) ∧
    (∑ n ∈ Ico 15488 15616, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-51500089698415549156211069351 : ℤ) := by
  rcases cdemPrefixStats_15488_15552 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_15552_15616 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 15488 ≤ 15552) (by norm_num : 15552 ≤ 15616), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 15488 ≤ 15552) (by norm_num : 15552 ≤ 15616), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 15488 ≤ 15552) (by norm_num : 15552 ≤ 15616), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 15488 ≤ 15552) (by norm_num : 15552 ≤ 15616), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_15360_15616 :
    (∑ n ∈ Ico 15360 15616, mobiusTreeValue 16 mobiusTable1200001 n) = (-8 : ℤ) ∧
    (∑ n ∈ Ico 15360 15616, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (156 : ℕ) ∧
    (∑ n ∈ Ico 15360 15616, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-2573041 : ℤ) ∧
    (∑ n ∈ Ico 15360 15616, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-51460942195874958778962666328 : ℤ) := by
  rcases cdemPrefixStats_15360_15488 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_15488_15616 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 15360 ≤ 15488) (by norm_num : 15488 ≤ 15616), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 15360 ≤ 15488) (by norm_num : 15488 ≤ 15616), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 15360 ≤ 15488) (by norm_num : 15488 ≤ 15616), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 15360 ≤ 15488) (by norm_num : 15488 ≤ 15616), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_15616_15680 :
    (∑ n ∈ Ico 15616 15680, mobiusTreeValue 16 mobiusTable1200001 n) = (-11 : ℤ) ∧
    (∑ n ∈ Ico 15616 15680, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 15616 15680, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-3514213 : ℤ) ∧
    (∑ n ∈ Ico 15616 15680, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-70284372839403278426640582213 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_15680_15744 :
    (∑ n ∈ Ico 15680 15744, mobiusTreeValue 16 mobiusTable1200001 n) = (3 : ℤ) ∧
    (∑ n ∈ Ico 15680 15744, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 15680 15744, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (961267 : ℤ) ∧
    (∑ n ∈ Ico 15680 15744, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (19225334965135415028680695059 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_15616_15744 :
    (∑ n ∈ Ico 15616 15744, mobiusTreeValue 16 mobiusTable1200001 n) = (-8 : ℤ) ∧
    (∑ n ∈ Ico 15616 15744, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 15616 15744, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-2552946 : ℤ) ∧
    (∑ n ∈ Ico 15616 15744, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-51059037874267863397959887154 : ℤ) := by
  rcases cdemPrefixStats_15616_15680 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_15680_15744 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 15616 ≤ 15680) (by norm_num : 15680 ≤ 15744), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 15616 ≤ 15680) (by norm_num : 15680 ≤ 15744), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 15616 ≤ 15680) (by norm_num : 15680 ≤ 15744), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 15616 ≤ 15680) (by norm_num : 15680 ≤ 15744), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_15744_15808 :
    (∑ n ∈ Ico 15744 15808, mobiusTreeValue 16 mobiusTable1200001 n) = (-7 : ℤ) ∧
    (∑ n ∈ Ico 15744 15808, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 15744 15808, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-2214346 : ℤ) ∧
    (∑ n ∈ Ico 15744 15808, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-44286976339150048329296077695 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_15808_15872 :
    (∑ n ∈ Ico 15808 15872, mobiusTreeValue 16 mobiusTable1200001 n) = (10 : ℤ) ∧
    (∑ n ∈ Ico 15808 15872, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (36 : ℕ) ∧
    (∑ n ∈ Ico 15808 15872, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (3153873 : ℤ) ∧
    (∑ n ∈ Ico 15808 15872, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (63077573841638900171076853643 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_15744_15872 :
    (∑ n ∈ Ico 15744 15872, mobiusTreeValue 16 mobiusTable1200001 n) = (3 : ℤ) ∧
    (∑ n ∈ Ico 15744 15872, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 15744 15872, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (939527 : ℤ) ∧
    (∑ n ∈ Ico 15744 15872, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (18790597502488851841780775948 : ℤ) := by
  rcases cdemPrefixStats_15744_15808 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_15808_15872 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 15744 ≤ 15808) (by norm_num : 15808 ≤ 15872), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 15744 ≤ 15808) (by norm_num : 15808 ≤ 15872), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 15744 ≤ 15808) (by norm_num : 15808 ≤ 15872), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 15744 ≤ 15808) (by norm_num : 15808 ≤ 15872), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_15616_15872 :
    (∑ n ∈ Ico 15616 15872, mobiusTreeValue 16 mobiusTable1200001 n) = (-5 : ℤ) ∧
    (∑ n ∈ Ico 15616 15872, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (155 : ℕ) ∧
    (∑ n ∈ Ico 15616 15872, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-1613419 : ℤ) ∧
    (∑ n ∈ Ico 15616 15872, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-32268440371779011556179111206 : ℤ) := by
  rcases cdemPrefixStats_15616_15744 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_15744_15872 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 15616 ≤ 15744) (by norm_num : 15744 ≤ 15872), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 15616 ≤ 15744) (by norm_num : 15744 ≤ 15872), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 15616 ≤ 15744) (by norm_num : 15744 ≤ 15872), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 15616 ≤ 15744) (by norm_num : 15744 ≤ 15872), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_15360_15872 :
    (∑ n ∈ Ico 15360 15872, mobiusTreeValue 16 mobiusTable1200001 n) = (-13 : ℤ) ∧
    (∑ n ∈ Ico 15360 15872, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (311 : ℕ) ∧
    (∑ n ∈ Ico 15360 15872, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-4186460 : ℤ) ∧
    (∑ n ∈ Ico 15360 15872, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-83729382567653970335141777534 : ℤ) := by
  rcases cdemPrefixStats_15360_15616 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_15616_15872 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 15360 ≤ 15616) (by norm_num : 15616 ≤ 15872), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 15360 ≤ 15616) (by norm_num : 15616 ≤ 15872), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 15360 ≤ 15616) (by norm_num : 15616 ≤ 15872), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 15360 ≤ 15616) (by norm_num : 15616 ≤ 15872), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_15872_15936 :
    (∑ n ∈ Ico 15872 15936, mobiusTreeValue 16 mobiusTable1200001 n) = (3 : ℤ) ∧
    (∑ n ∈ Ico 15872 15936, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 15872 15936, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (941890 : ℤ) ∧
    (∑ n ∈ Ico 15872 15936, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (18837878386660639750594770830 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_15936_16000 :
    (∑ n ∈ Ico 15936 16000, mobiusTreeValue 16 mobiusTable1200001 n) = (-9 : ℤ) ∧
    (∑ n ∈ Ico 15936 16000, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 15936 16000, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-2817861 : ℤ) ∧
    (∑ n ∈ Ico 15936 16000, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-56357293821125380998854492058 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_15872_16000 :
    (∑ n ∈ Ico 15872 16000, mobiusTreeValue 16 mobiusTable1200001 n) = (-6 : ℤ) ∧
    (∑ n ∈ Ico 15872 16000, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 15872 16000, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-1875971 : ℤ) ∧
    (∑ n ∈ Ico 15872 16000, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-37519415434464741248259721228 : ℤ) := by
  rcases cdemPrefixStats_15872_15936 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_15936_16000 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 15872 ≤ 15936) (by norm_num : 15936 ≤ 16000), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 15872 ≤ 15936) (by norm_num : 15936 ≤ 16000), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 15872 ≤ 15936) (by norm_num : 15936 ≤ 16000), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 15872 ≤ 15936) (by norm_num : 15936 ≤ 16000), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_16000_16064 :
    (∑ n ∈ Ico 16000 16064, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 16000 16064, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 16000 16064, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (314288 : ℤ) ∧
    (∑ n ∈ Ico 16000 16064, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (6285719668432614906091051363 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_16064_16128 :
    (∑ n ∈ Ico 16064 16128, mobiusTreeValue 16 mobiusTable1200001 n) = (-8 : ℤ) ∧
    (∑ n ∈ Ico 16064 16128, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 16064 16128, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-2486366 : ℤ) ∧
    (∑ n ∈ Ico 16064 16128, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-49727390884538098852838042414 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_16000_16128 :
    (∑ n ∈ Ico 16000 16128, mobiusTreeValue 16 mobiusTable1200001 n) = (-7 : ℤ) ∧
    (∑ n ∈ Ico 16000 16128, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 16000 16128, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-2172078 : ℤ) ∧
    (∑ n ∈ Ico 16000 16128, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-43441671216105483946746991051 : ℤ) := by
  rcases cdemPrefixStats_16000_16064 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_16064_16128 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 16000 ≤ 16064) (by norm_num : 16064 ≤ 16128), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 16000 ≤ 16064) (by norm_num : 16064 ≤ 16128), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 16000 ≤ 16064) (by norm_num : 16064 ≤ 16128), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 16000 ≤ 16064) (by norm_num : 16064 ≤ 16128), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_15872_16128 :
    (∑ n ∈ Ico 15872 16128, mobiusTreeValue 16 mobiusTable1200001 n) = (-13 : ℤ) ∧
    (∑ n ∈ Ico 15872 16128, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (155 : ℕ) ∧
    (∑ n ∈ Ico 15872 16128, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-4048049 : ℤ) ∧
    (∑ n ∈ Ico 15872 16128, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-80961086650570225195006712279 : ℤ) := by
  rcases cdemPrefixStats_15872_16000 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_16000_16128 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 15872 ≤ 16000) (by norm_num : 16000 ≤ 16128), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 15872 ≤ 16000) (by norm_num : 16000 ≤ 16128), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 15872 ≤ 16000) (by norm_num : 16000 ≤ 16128), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 15872 ≤ 16000) (by norm_num : 16000 ≤ 16128), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_16128_16192 :
    (∑ n ∈ Ico 16128 16192, mobiusTreeValue 16 mobiusTable1200001 n) = (-2 : ℤ) ∧
    (∑ n ∈ Ico 16128 16192, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 16128 16192, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-621687 : ℤ) ∧
    (∑ n ∈ Ico 16128 16192, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-12433769290310431650463609828 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_16192_16256 :
    (∑ n ∈ Ico 16192 16256, mobiusTreeValue 16 mobiusTable1200001 n) = (3 : ℤ) ∧
    (∑ n ∈ Ico 16192 16256, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 16192 16256, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (924498 : ℤ) ∧
    (∑ n ∈ Ico 16192 16256, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (18489996632181547834831694470 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_16128_16256 :
    (∑ n ∈ Ico 16128 16256, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 16128 16256, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 16128 16256, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (302811 : ℤ) ∧
    (∑ n ∈ Ico 16128 16256, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (6056227341871116184368084642 : ℤ) := by
  rcases cdemPrefixStats_16128_16192 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_16192_16256 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 16128 ≤ 16192) (by norm_num : 16192 ≤ 16256), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 16128 ≤ 16192) (by norm_num : 16192 ≤ 16256), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 16128 ≤ 16192) (by norm_num : 16192 ≤ 16256), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 16128 ≤ 16192) (by norm_num : 16192 ≤ 16256), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_16256_16320 :
    (∑ n ∈ Ico 16256 16320, mobiusTreeValue 16 mobiusTable1200001 n) = (-4 : ℤ) ∧
    (∑ n ∈ Ico 16256 16320, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (42 : ℕ) ∧
    (∑ n ∈ Ico 16256 16320, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-1227582 : ℤ) ∧
    (∑ n ∈ Ico 16256 16320, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-24551614322187029637707419439 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_16320_16384 :
    (∑ n ∈ Ico 16320 16384, mobiusTreeValue 16 mobiusTable1200001 n) = (6 : ℤ) ∧
    (∑ n ∈ Ico 16320 16384, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 16320 16384, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (1839574 : ℤ) ∧
    (∑ n ∈ Ico 16320 16384, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (36791552205802255970643813622 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_16256_16384 :
    (∑ n ∈ Ico 16256 16384, mobiusTreeValue 16 mobiusTable1200001 n) = (2 : ℤ) ∧
    (∑ n ∈ Ico 16256 16384, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (80 : ℕ) ∧
    (∑ n ∈ Ico 16256 16384, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (611992 : ℤ) ∧
    (∑ n ∈ Ico 16256 16384, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (12239937883615226332936394183 : ℤ) := by
  rcases cdemPrefixStats_16256_16320 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_16320_16384 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 16256 ≤ 16320) (by norm_num : 16320 ≤ 16384), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 16256 ≤ 16320) (by norm_num : 16320 ≤ 16384), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 16256 ≤ 16320) (by norm_num : 16320 ≤ 16384), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 16256 ≤ 16320) (by norm_num : 16320 ≤ 16384), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_16128_16384 :
    (∑ n ∈ Ico 16128 16384, mobiusTreeValue 16 mobiusTable1200001 n) = (3 : ℤ) ∧
    (∑ n ∈ Ico 16128 16384, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (157 : ℕ) ∧
    (∑ n ∈ Ico 16128 16384, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (914803 : ℤ) ∧
    (∑ n ∈ Ico 16128 16384, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (18296165225486342517304478825 : ℤ) := by
  rcases cdemPrefixStats_16128_16256 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_16256_16384 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 16128 ≤ 16256) (by norm_num : 16256 ≤ 16384), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 16128 ≤ 16256) (by norm_num : 16256 ≤ 16384), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 16128 ≤ 16256) (by norm_num : 16256 ≤ 16384), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 16128 ≤ 16256) (by norm_num : 16256 ≤ 16384), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_15872_16384 :
    (∑ n ∈ Ico 15872 16384, mobiusTreeValue 16 mobiusTable1200001 n) = (-10 : ℤ) ∧
    (∑ n ∈ Ico 15872 16384, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (312 : ℕ) ∧
    (∑ n ∈ Ico 15872 16384, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-3133246 : ℤ) ∧
    (∑ n ∈ Ico 15872 16384, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-62664921425083882677702233454 : ℤ) := by
  rcases cdemPrefixStats_15872_16128 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_16128_16384 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 15872 ≤ 16128) (by norm_num : 16128 ≤ 16384), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 15872 ≤ 16128) (by norm_num : 16128 ≤ 16384), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 15872 ≤ 16128) (by norm_num : 16128 ≤ 16384), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 15872 ≤ 16128) (by norm_num : 16128 ≤ 16384), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_15360_16384 :
    (∑ n ∈ Ico 15360 16384, mobiusTreeValue 16 mobiusTable1200001 n) = (-23 : ℤ) ∧
    (∑ n ∈ Ico 15360 16384, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (623 : ℕ) ∧
    (∑ n ∈ Ico 15360 16384, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-7319706 : ℤ) ∧
    (∑ n ∈ Ico 15360 16384, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-146394303992737853012844010988 : ℤ) := by
  rcases cdemPrefixStats_15360_15872 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_15872_16384 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 15360 ≤ 15872) (by norm_num : 15872 ≤ 16384), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 15360 ≤ 15872) (by norm_num : 15872 ≤ 16384), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 15360 ≤ 15872) (by norm_num : 15872 ≤ 16384), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 15360 ≤ 15872) (by norm_num : 15872 ≤ 16384), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_14336_16384 :
    (∑ n ∈ Ico 14336 16384, mobiusTreeValue 16 mobiusTable1200001 n) = (-43 : ℤ) ∧
    (∑ n ∈ Ico 14336 16384, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (1247 : ℕ) ∧
    (∑ n ∈ Ico 14336 16384, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-14069729 : ℤ) ∧
    (∑ n ∈ Ico 14336 16384, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-281394815267762793792200739624 : ℤ) := by
  rcases cdemPrefixStats_14336_15360 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_15360_16384 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 14336 ≤ 15360) (by norm_num : 15360 ≤ 16384), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 14336 ≤ 15360) (by norm_num : 15360 ≤ 16384), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 14336 ≤ 15360) (by norm_num : 15360 ≤ 16384), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 14336 ≤ 15360) (by norm_num : 15360 ≤ 16384), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_12288_16384 :
    (∑ n ∈ Ico 12288 16384, mobiusTreeValue 16 mobiusTable1200001 n) = (-53 : ℤ) ∧
    (∑ n ∈ Ico 12288 16384, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (2493 : ℕ) ∧
    (∑ n ∈ Ico 12288 16384, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-18578129 : ℤ) ∧
    (∑ n ∈ Ico 12288 16384, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-371562610433863429345766935904 : ℤ) := by
  rcases cdemPrefixStats_12288_14336 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_14336_16384 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 12288 ≤ 14336) (by norm_num : 14336 ≤ 16384), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 12288 ≤ 14336) (by norm_num : 14336 ≤ 16384), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 12288 ≤ 14336) (by norm_num : 14336 ≤ 16384), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 12288 ≤ 14336) (by norm_num : 14336 ≤ 16384), hR1, hR2] <;> norm_num

theorem cdemPrefixGroup003_checked_complete :
    (∑ n ∈ Ico 12288 16384, mobiusTreeValue 16 mobiusTable1200001 n) = (-53 : ℤ) ∧
    (∑ n ∈ Ico 12288 16384, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (2493 : ℕ) ∧
    (∑ n ∈ Ico 12288 16384, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-18578129 : ℤ) ∧
    (∑ n ∈ Ico 12288 16384, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-371562610433863429345766935904 : ℤ) := cdemPrefixStats_12288_16384
end Helfgott
#print axioms Helfgott.cdemPrefixGroup003_checked_complete

open Helfgott Finset
open scoped BigOperators

theorem solution :
    (∑ n ∈ Ico 12288 16384, mobiusTreeValue 16 mobiusTable1200001 n) = (-53 : ℤ) ∧
    (∑ n ∈ Ico 12288 16384, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (2493 : ℕ) ∧
    (∑ n ∈ Ico 12288 16384, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-18578129 : ℤ) ∧
    (∑ n ∈ Ico 12288 16384, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-371562610433863429345766935904 : ℤ) := Helfgott.cdemPrefixGroup003_checked_complete
#print axioms solution
