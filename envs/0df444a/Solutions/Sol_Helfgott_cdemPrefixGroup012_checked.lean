-- Prove2me | solution 1 for Helfgott.cdemPrefixGroup012_checked
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-09T01:38:26.550696+00:00
-- url     : https://prove2.me/submissions/8f77568b-d64b-4831-9c44-1f6319ed2368

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
private theorem cdemPrefixStats_49152_49216 :
    (∑ n ∈ Ico 49152 49216, mobiusTreeValue 16 mobiusTable1200001 n) = (-14 : ℤ) ∧
    (∑ n ∈ Ico 49152 49216, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 49152 49216, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-1423244 : ℤ) ∧
    (∑ n ∈ Ico 49152 49216, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-28465042262201320523766325439 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_49216_49280 :
    (∑ n ∈ Ico 49216 49280, mobiusTreeValue 16 mobiusTable1200001 n) = (2 : ℤ) ∧
    (∑ n ∈ Ico 49216 49280, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 49216 49280, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (203067 : ℤ) ∧
    (∑ n ∈ Ico 49216 49280, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (4061366982041220483721201268 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_49152_49280 :
    (∑ n ∈ Ico 49152 49280, mobiusTreeValue 16 mobiusTable1200001 n) = (-12 : ℤ) ∧
    (∑ n ∈ Ico 49152 49280, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 49152 49280, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-1220177 : ℤ) ∧
    (∑ n ∈ Ico 49152 49280, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-24403675280160100040045124171 : ℤ) := by
  rcases cdemPrefixStats_49152_49216 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_49216_49280 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 49152 ≤ 49216) (by norm_num : 49216 ≤ 49280), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 49152 ≤ 49216) (by norm_num : 49216 ≤ 49280), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 49152 ≤ 49216) (by norm_num : 49216 ≤ 49280), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 49152 ≤ 49216) (by norm_num : 49216 ≤ 49280), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_49280_49344 :
    (∑ n ∈ Ico 49280 49344, mobiusTreeValue 16 mobiusTable1200001 n) = (-3 : ℤ) ∧
    (∑ n ∈ Ico 49280 49344, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 49280 49344, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-304077 : ℤ) ∧
    (∑ n ∈ Ico 49280 49344, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-6081533111461088731850624757 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_49344_49408 :
    (∑ n ∈ Ico 49344 49408, mobiusTreeValue 16 mobiusTable1200001 n) = (-2 : ℤ) ∧
    (∑ n ∈ Ico 49344 49408, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 49344 49408, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-202223 : ℤ) ∧
    (∑ n ∈ Ico 49344 49408, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-4044398869051225940940523433 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_49280_49408 :
    (∑ n ∈ Ico 49280 49408, mobiusTreeValue 16 mobiusTable1200001 n) = (-5 : ℤ) ∧
    (∑ n ∈ Ico 49280 49408, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (79 : ℕ) ∧
    (∑ n ∈ Ico 49280 49408, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-506300 : ℤ) ∧
    (∑ n ∈ Ico 49280 49408, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-10125931980512314672791148190 : ℤ) := by
  rcases cdemPrefixStats_49280_49344 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_49344_49408 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 49280 ≤ 49344) (by norm_num : 49344 ≤ 49408), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 49280 ≤ 49344) (by norm_num : 49344 ≤ 49408), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 49280 ≤ 49344) (by norm_num : 49344 ≤ 49408), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 49280 ≤ 49344) (by norm_num : 49344 ≤ 49408), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_49152_49408 :
    (∑ n ∈ Ico 49152 49408, mobiusTreeValue 16 mobiusTable1200001 n) = (-17 : ℤ) ∧
    (∑ n ∈ Ico 49152 49408, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (157 : ℕ) ∧
    (∑ n ∈ Ico 49152 49408, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-1726477 : ℤ) ∧
    (∑ n ∈ Ico 49152 49408, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-34529607260672414712836272361 : ℤ) := by
  rcases cdemPrefixStats_49152_49280 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_49280_49408 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 49152 ≤ 49280) (by norm_num : 49280 ≤ 49408), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 49152 ≤ 49280) (by norm_num : 49280 ≤ 49408), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 49152 ≤ 49280) (by norm_num : 49280 ≤ 49408), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 49152 ≤ 49280) (by norm_num : 49280 ≤ 49408), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_49408_49472 :
    (∑ n ∈ Ico 49408 49472, mobiusTreeValue 16 mobiusTable1200001 n) = (-9 : ℤ) ∧
    (∑ n ∈ Ico 49408 49472, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 49408 49472, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-910073 : ℤ) ∧
    (∑ n ∈ Ico 49408 49472, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-18201514178743741554345260993 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_49472_49536 :
    (∑ n ∈ Ico 49472 49536, mobiusTreeValue 16 mobiusTable1200001 n) = (-5 : ℤ) ∧
    (∑ n ∈ Ico 49472 49536, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 49472 49536, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-505073 : ℤ) ∧
    (∑ n ∈ Ico 49472 49536, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-10101500599609705016765695751 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_49408_49536 :
    (∑ n ∈ Ico 49408 49536, mobiusTreeValue 16 mobiusTable1200001 n) = (-14 : ℤ) ∧
    (∑ n ∈ Ico 49408 49536, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (76 : ℕ) ∧
    (∑ n ∈ Ico 49408 49536, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-1415146 : ℤ) ∧
    (∑ n ∈ Ico 49408 49536, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-28303014778353446571110956744 : ℤ) := by
  rcases cdemPrefixStats_49408_49472 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_49472_49536 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 49408 ≤ 49472) (by norm_num : 49472 ≤ 49536), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 49408 ≤ 49472) (by norm_num : 49472 ≤ 49536), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 49408 ≤ 49472) (by norm_num : 49472 ≤ 49536), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 49408 ≤ 49472) (by norm_num : 49472 ≤ 49536), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_49536_49600 :
    (∑ n ∈ Ico 49536 49600, mobiusTreeValue 16 mobiusTable1200001 n) = (3 : ℤ) ∧
    (∑ n ∈ Ico 49536 49600, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 49536 49600, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (302461 : ℤ) ∧
    (∑ n ∈ Ico 49536 49600, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (6049280421415268454969042005 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_49600_49664 :
    (∑ n ∈ Ico 49600 49664, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 49600 49664, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 49600 49664, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-229 : ℤ) ∧
    (∑ n ∈ Ico 49600 49664, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-4547034602305230873512651 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_49536_49664 :
    (∑ n ∈ Ico 49536 49664, mobiusTreeValue 16 mobiusTable1200001 n) = (3 : ℤ) ∧
    (∑ n ∈ Ico 49536 49664, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 49536 49664, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (302232 : ℤ) ∧
    (∑ n ∈ Ico 49536 49664, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (6044733386812963224095529354 : ℤ) := by
  rcases cdemPrefixStats_49536_49600 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_49600_49664 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 49536 ≤ 49600) (by norm_num : 49600 ≤ 49664), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 49536 ≤ 49600) (by norm_num : 49600 ≤ 49664), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 49536 ≤ 49600) (by norm_num : 49600 ≤ 49664), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 49536 ≤ 49600) (by norm_num : 49600 ≤ 49664), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_49408_49664 :
    (∑ n ∈ Ico 49408 49664, mobiusTreeValue 16 mobiusTable1200001 n) = (-11 : ℤ) ∧
    (∑ n ∈ Ico 49408 49664, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (153 : ℕ) ∧
    (∑ n ∈ Ico 49408 49664, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-1112914 : ℤ) ∧
    (∑ n ∈ Ico 49408 49664, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-22258281391540483347015427390 : ℤ) := by
  rcases cdemPrefixStats_49408_49536 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_49536_49664 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 49408 ≤ 49536) (by norm_num : 49536 ≤ 49664), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 49408 ≤ 49536) (by norm_num : 49536 ≤ 49664), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 49408 ≤ 49536) (by norm_num : 49536 ≤ 49664), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 49408 ≤ 49536) (by norm_num : 49536 ≤ 49664), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_49152_49664 :
    (∑ n ∈ Ico 49152 49664, mobiusTreeValue 16 mobiusTable1200001 n) = (-28 : ℤ) ∧
    (∑ n ∈ Ico 49152 49664, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (310 : ℕ) ∧
    (∑ n ∈ Ico 49152 49664, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-2839391 : ℤ) ∧
    (∑ n ∈ Ico 49152 49664, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-56787888652212898059851699751 : ℤ) := by
  rcases cdemPrefixStats_49152_49408 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_49408_49664 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 49152 ≤ 49408) (by norm_num : 49408 ≤ 49664), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 49152 ≤ 49408) (by norm_num : 49408 ≤ 49664), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 49152 ≤ 49408) (by norm_num : 49408 ≤ 49664), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 49152 ≤ 49408) (by norm_num : 49408 ≤ 49664), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_49664_49728 :
    (∑ n ∈ Ico 49664 49728, mobiusTreeValue 16 mobiusTable1200001 n) = (-2 : ℤ) ∧
    (∑ n ∈ Ico 49664 49728, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 49664 49728, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-201684 : ℤ) ∧
    (∑ n ∈ Ico 49664 49728, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-4033743586358258097434024299 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_49728_49792 :
    (∑ n ∈ Ico 49728 49792, mobiusTreeValue 16 mobiusTable1200001 n) = (-10 : ℤ) ∧
    (∑ n ∈ Ico 49728 49792, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 49728 49792, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-1004815 : ℤ) ∧
    (∑ n ∈ Ico 49728 49792, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-20096426447817627538606357946 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_49664_49792 :
    (∑ n ∈ Ico 49664 49792, mobiusTreeValue 16 mobiusTable1200001 n) = (-12 : ℤ) ∧
    (∑ n ∈ Ico 49664 49792, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 49664 49792, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-1206499 : ℤ) ∧
    (∑ n ∈ Ico 49664 49792, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-24130170034175885636040382245 : ℤ) := by
  rcases cdemPrefixStats_49664_49728 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_49728_49792 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 49664 ≤ 49728) (by norm_num : 49728 ≤ 49792), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 49664 ≤ 49728) (by norm_num : 49728 ≤ 49792), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 49664 ≤ 49728) (by norm_num : 49728 ≤ 49792), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 49664 ≤ 49728) (by norm_num : 49728 ≤ 49792), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_49792_49856 :
    (∑ n ∈ Ico 49792 49856, mobiusTreeValue 16 mobiusTable1200001 n) = (-6 : ℤ) ∧
    (∑ n ∈ Ico 49792 49856, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 49792 49856, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-602323 : ℤ) ∧
    (∑ n ∈ Ico 49792 49856, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-12046499703996828491327172551 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_49856_49920 :
    (∑ n ∈ Ico 49856 49920, mobiusTreeValue 16 mobiusTable1200001 n) = (-5 : ℤ) ∧
    (∑ n ∈ Ico 49856 49920, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 49856 49920, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-500972 : ℤ) ∧
    (∑ n ∈ Ico 49856 49920, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-10019481533644173637828063803 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_49792_49920 :
    (∑ n ∈ Ico 49792 49920, mobiusTreeValue 16 mobiusTable1200001 n) = (-11 : ℤ) ∧
    (∑ n ∈ Ico 49792 49920, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (79 : ℕ) ∧
    (∑ n ∈ Ico 49792 49920, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-1103295 : ℤ) ∧
    (∑ n ∈ Ico 49792 49920, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-22065981237641002129155236354 : ℤ) := by
  rcases cdemPrefixStats_49792_49856 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_49856_49920 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 49792 ≤ 49856) (by norm_num : 49856 ≤ 49920), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 49792 ≤ 49856) (by norm_num : 49856 ≤ 49920), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 49792 ≤ 49856) (by norm_num : 49856 ≤ 49920), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 49792 ≤ 49856) (by norm_num : 49856 ≤ 49920), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_49664_49920 :
    (∑ n ∈ Ico 49664 49920, mobiusTreeValue 16 mobiusTable1200001 n) = (-23 : ℤ) ∧
    (∑ n ∈ Ico 49664 49920, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (157 : ℕ) ∧
    (∑ n ∈ Ico 49664 49920, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-2309794 : ℤ) ∧
    (∑ n ∈ Ico 49664 49920, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-46196151271816887765195618599 : ℤ) := by
  rcases cdemPrefixStats_49664_49792 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_49792_49920 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 49664 ≤ 49792) (by norm_num : 49792 ≤ 49920), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 49664 ≤ 49792) (by norm_num : 49792 ≤ 49920), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 49664 ≤ 49792) (by norm_num : 49792 ≤ 49920), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 49664 ≤ 49792) (by norm_num : 49792 ≤ 49920), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_49920_49984 :
    (∑ n ∈ Ico 49920 49984, mobiusTreeValue 16 mobiusTable1200001 n) = (3 : ℤ) ∧
    (∑ n ∈ Ico 49920 49984, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 49920 49984, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (299848 : ℤ) ∧
    (∑ n ∈ Ico 49920 49984, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (5996948017530537480480183349 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_49984_50048 :
    (∑ n ∈ Ico 49984 50048, mobiusTreeValue 16 mobiusTable1200001 n) = (-10 : ℤ) ∧
    (∑ n ∈ Ico 49984 50048, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 49984 50048, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-1000100 : ℤ) ∧
    (∑ n ∈ Ico 49984 50048, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-20002000913603796553999337796 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_49920_50048 :
    (∑ n ∈ Ico 49920 50048, mobiusTreeValue 16 mobiusTable1200001 n) = (-7 : ℤ) ∧
    (∑ n ∈ Ico 49920 50048, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (79 : ℕ) ∧
    (∑ n ∈ Ico 49920 50048, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-700252 : ℤ) ∧
    (∑ n ∈ Ico 49920 50048, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-14005052896073259073519154447 : ℤ) := by
  rcases cdemPrefixStats_49920_49984 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_49984_50048 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 49920 ≤ 49984) (by norm_num : 49984 ≤ 50048), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 49920 ≤ 49984) (by norm_num : 49984 ≤ 50048), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 49920 ≤ 49984) (by norm_num : 49984 ≤ 50048), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 49920 ≤ 49984) (by norm_num : 49984 ≤ 50048), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_50048_50112 :
    (∑ n ∈ Ico 50048 50112, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 50048 50112, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 50048 50112, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (100134 : ℤ) ∧
    (∑ n ∈ Ico 50048 50112, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (2002665945559167536413333373 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_50112_50176 :
    (∑ n ∈ Ico 50112 50176, mobiusTreeValue 16 mobiusTable1200001 n) = (-7 : ℤ) ∧
    (∑ n ∈ Ico 50112 50176, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 50112 50176, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-697993 : ℤ) ∧
    (∑ n ∈ Ico 50112 50176, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-13959954207476506977465279057 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_50048_50176 :
    (∑ n ∈ Ico 50048 50176, mobiusTreeValue 16 mobiusTable1200001 n) = (-6 : ℤ) ∧
    (∑ n ∈ Ico 50048 50176, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 50048 50176, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-597859 : ℤ) ∧
    (∑ n ∈ Ico 50048 50176, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-11957288261917339441051945684 : ℤ) := by
  rcases cdemPrefixStats_50048_50112 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_50112_50176 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 50048 ≤ 50112) (by norm_num : 50112 ≤ 50176), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 50048 ≤ 50112) (by norm_num : 50112 ≤ 50176), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 50048 ≤ 50112) (by norm_num : 50112 ≤ 50176), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 50048 ≤ 50112) (by norm_num : 50112 ≤ 50176), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_49920_50176 :
    (∑ n ∈ Ico 49920 50176, mobiusTreeValue 16 mobiusTable1200001 n) = (-13 : ℤ) ∧
    (∑ n ∈ Ico 49920 50176, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (157 : ℕ) ∧
    (∑ n ∈ Ico 49920 50176, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-1298111 : ℤ) ∧
    (∑ n ∈ Ico 49920 50176, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-25962341157990598514571100131 : ℤ) := by
  rcases cdemPrefixStats_49920_50048 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_50048_50176 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 49920 ≤ 50048) (by norm_num : 50048 ≤ 50176), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 49920 ≤ 50048) (by norm_num : 50048 ≤ 50176), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 49920 ≤ 50048) (by norm_num : 50048 ≤ 50176), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 49920 ≤ 50048) (by norm_num : 50048 ≤ 50176), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_49664_50176 :
    (∑ n ∈ Ico 49664 50176, mobiusTreeValue 16 mobiusTable1200001 n) = (-36 : ℤ) ∧
    (∑ n ∈ Ico 49664 50176, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (314 : ℕ) ∧
    (∑ n ∈ Ico 49664 50176, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-3607905 : ℤ) ∧
    (∑ n ∈ Ico 49664 50176, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-72158492429807486279766718730 : ℤ) := by
  rcases cdemPrefixStats_49664_49920 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_49920_50176 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 49664 ≤ 49920) (by norm_num : 49920 ≤ 50176), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 49664 ≤ 49920) (by norm_num : 49920 ≤ 50176), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 49664 ≤ 49920) (by norm_num : 49920 ≤ 50176), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 49664 ≤ 49920) (by norm_num : 49920 ≤ 50176), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_49152_50176 :
    (∑ n ∈ Ico 49152 50176, mobiusTreeValue 16 mobiusTable1200001 n) = (-64 : ℤ) ∧
    (∑ n ∈ Ico 49152 50176, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (624 : ℕ) ∧
    (∑ n ∈ Ico 49152 50176, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-6447296 : ℤ) ∧
    (∑ n ∈ Ico 49152 50176, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-128946381082020384339618418481 : ℤ) := by
  rcases cdemPrefixStats_49152_49664 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_49664_50176 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 49152 ≤ 49664) (by norm_num : 49664 ≤ 50176), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 49152 ≤ 49664) (by norm_num : 49664 ≤ 50176), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 49152 ≤ 49664) (by norm_num : 49664 ≤ 50176), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 49152 ≤ 49664) (by norm_num : 49664 ≤ 50176), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_50176_50240 :
    (∑ n ∈ Ico 50176 50240, mobiusTreeValue 16 mobiusTable1200001 n) = (-2 : ℤ) ∧
    (∑ n ∈ Ico 50176 50240, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 50176 50240, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-199591 : ℤ) ∧
    (∑ n ∈ Ico 50176 50240, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-3991838663074469804402950946 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_50240_50304 :
    (∑ n ∈ Ico 50240 50304, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 50240 50304, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 50240 50304, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-99306 : ℤ) ∧
    (∑ n ∈ Ico 50240 50304, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-1986169171280407291947156229 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_50176_50304 :
    (∑ n ∈ Ico 50176 50304, mobiusTreeValue 16 mobiusTable1200001 n) = (-3 : ℤ) ∧
    (∑ n ∈ Ico 50176 50304, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (79 : ℕ) ∧
    (∑ n ∈ Ico 50176 50304, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-298897 : ℤ) ∧
    (∑ n ∈ Ico 50176 50304, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-5978007834354877096350107175 : ℤ) := by
  rcases cdemPrefixStats_50176_50240 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_50240_50304 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 50176 ≤ 50240) (by norm_num : 50240 ≤ 50304), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 50176 ≤ 50240) (by norm_num : 50240 ≤ 50304), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 50176 ≤ 50240) (by norm_num : 50240 ≤ 50304), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 50176 ≤ 50240) (by norm_num : 50240 ≤ 50304), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_50304_50368 :
    (∑ n ∈ Ico 50304 50368, mobiusTreeValue 16 mobiusTable1200001 n) = (-5 : ℤ) ∧
    (∑ n ∈ Ico 50304 50368, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 50304 50368, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-496647 : ℤ) ∧
    (∑ n ∈ Ico 50304 50368, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-9932974023408987606747822365 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_50368_50432 :
    (∑ n ∈ Ico 50368 50432, mobiusTreeValue 16 mobiusTable1200001 n) = (-7 : ℤ) ∧
    (∑ n ∈ Ico 50368 50432, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 50368 50432, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-694471 : ℤ) ∧
    (∑ n ∈ Ico 50368 50432, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-13889482564268239216848849138 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_50304_50432 :
    (∑ n ∈ Ico 50304 50432, mobiusTreeValue 16 mobiusTable1200001 n) = (-12 : ℤ) ∧
    (∑ n ∈ Ico 50304 50432, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (76 : ℕ) ∧
    (∑ n ∈ Ico 50304 50432, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-1191118 : ℤ) ∧
    (∑ n ∈ Ico 50304 50432, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-23822456587677226823596671503 : ℤ) := by
  rcases cdemPrefixStats_50304_50368 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_50368_50432 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 50304 ≤ 50368) (by norm_num : 50368 ≤ 50432), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 50304 ≤ 50368) (by norm_num : 50368 ≤ 50432), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 50304 ≤ 50368) (by norm_num : 50368 ≤ 50432), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 50304 ≤ 50368) (by norm_num : 50368 ≤ 50432), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_50176_50432 :
    (∑ n ∈ Ico 50176 50432, mobiusTreeValue 16 mobiusTable1200001 n) = (-15 : ℤ) ∧
    (∑ n ∈ Ico 50176 50432, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (155 : ℕ) ∧
    (∑ n ∈ Ico 50176 50432, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-1490015 : ℤ) ∧
    (∑ n ∈ Ico 50176 50432, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-29800464422032103919946778678 : ℤ) := by
  rcases cdemPrefixStats_50176_50304 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_50304_50432 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 50176 ≤ 50304) (by norm_num : 50304 ≤ 50432), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 50176 ≤ 50304) (by norm_num : 50304 ≤ 50432), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 50176 ≤ 50304) (by norm_num : 50304 ≤ 50432), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 50176 ≤ 50304) (by norm_num : 50304 ≤ 50432), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_50432_50496 :
    (∑ n ∈ Ico 50432 50496, mobiusTreeValue 16 mobiusTable1200001 n) = (19 : ℤ) ∧
    (∑ n ∈ Ico 50432 50496, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 50432 50496, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (1882379 : ℤ) ∧
    (∑ n ∈ Ico 50432 50496, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (37647821104455762732043222099 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_50496_50560 :
    (∑ n ∈ Ico 50496 50560, mobiusTreeValue 16 mobiusTable1200001 n) = (-5 : ℤ) ∧
    (∑ n ∈ Ico 50496 50560, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 50496 50560, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-494648 : ℤ) ∧
    (∑ n ∈ Ico 50496 50560, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-9893037892140134003961073046 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_50432_50560 :
    (∑ n ∈ Ico 50432 50560, mobiusTreeValue 16 mobiusTable1200001 n) = (14 : ℤ) ∧
    (∑ n ∈ Ico 50432 50560, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 50432 50560, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (1387731 : ℤ) ∧
    (∑ n ∈ Ico 50432 50560, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (27754783212315628728082149053 : ℤ) := by
  rcases cdemPrefixStats_50432_50496 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_50496_50560 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 50432 ≤ 50496) (by norm_num : 50496 ≤ 50560), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 50432 ≤ 50496) (by norm_num : 50496 ≤ 50560), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 50432 ≤ 50496) (by norm_num : 50496 ≤ 50560), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 50432 ≤ 50496) (by norm_num : 50496 ≤ 50560), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_50560_50624 :
    (∑ n ∈ Ico 50560 50624, mobiusTreeValue 16 mobiusTable1200001 n) = (-12 : ℤ) ∧
    (∑ n ∈ Ico 50560 50624, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 50560 50624, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-1185903 : ℤ) ∧
    (∑ n ∈ Ico 50560 50624, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-23718189775640531206076175150 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_50624_50688 :
    (∑ n ∈ Ico 50624 50688, mobiusTreeValue 16 mobiusTable1200001 n) = (8 : ℤ) ∧
    (∑ n ∈ Ico 50624 50688, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 50624 50688, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (789702 : ℤ) ∧
    (∑ n ∈ Ico 50624 50688, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (15794124146272482410804752467 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_50560_50688 :
    (∑ n ∈ Ico 50560 50688, mobiusTreeValue 16 mobiusTable1200001 n) = (-4 : ℤ) ∧
    (∑ n ∈ Ico 50560 50688, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 50560 50688, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-396201 : ℤ) ∧
    (∑ n ∈ Ico 50560 50688, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-7924065629368048795271422683 : ℤ) := by
  rcases cdemPrefixStats_50560_50624 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_50624_50688 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 50560 ≤ 50624) (by norm_num : 50624 ≤ 50688), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 50560 ≤ 50624) (by norm_num : 50624 ≤ 50688), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 50560 ≤ 50624) (by norm_num : 50624 ≤ 50688), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 50560 ≤ 50624) (by norm_num : 50624 ≤ 50688), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_50432_50688 :
    (∑ n ∈ Ico 50432 50688, mobiusTreeValue 16 mobiusTable1200001 n) = (10 : ℤ) ∧
    (∑ n ∈ Ico 50432 50688, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (156 : ℕ) ∧
    (∑ n ∈ Ico 50432 50688, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (991530 : ℤ) ∧
    (∑ n ∈ Ico 50432 50688, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (19830717582947579932810726370 : ℤ) := by
  rcases cdemPrefixStats_50432_50560 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_50560_50688 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 50432 ≤ 50560) (by norm_num : 50560 ≤ 50688), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 50432 ≤ 50560) (by norm_num : 50560 ≤ 50688), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 50432 ≤ 50560) (by norm_num : 50560 ≤ 50688), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 50432 ≤ 50560) (by norm_num : 50560 ≤ 50688), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_50176_50688 :
    (∑ n ∈ Ico 50176 50688, mobiusTreeValue 16 mobiusTable1200001 n) = (-5 : ℤ) ∧
    (∑ n ∈ Ico 50176 50688, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (311 : ℕ) ∧
    (∑ n ∈ Ico 50176 50688, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-498485 : ℤ) ∧
    (∑ n ∈ Ico 50176 50688, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-9969746839084523987136052308 : ℤ) := by
  rcases cdemPrefixStats_50176_50432 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_50432_50688 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 50176 ≤ 50432) (by norm_num : 50432 ≤ 50688), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 50176 ≤ 50432) (by norm_num : 50432 ≤ 50688), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 50176 ≤ 50432) (by norm_num : 50432 ≤ 50688), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 50176 ≤ 50432) (by norm_num : 50432 ≤ 50688), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_50688_50752 :
    (∑ n ∈ Ico 50688 50752, mobiusTreeValue 16 mobiusTable1200001 n) = (7 : ℤ) ∧
    (∑ n ∈ Ico 50688 50752, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 50688 50752, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (690219 : ℤ) ∧
    (∑ n ∈ Ico 50688 50752, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (13804452576118869956655259155 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_50752_50816 :
    (∑ n ∈ Ico 50752 50816, mobiusTreeValue 16 mobiusTable1200001 n) = (2 : ℤ) ∧
    (∑ n ∈ Ico 50752 50816, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 50752 50816, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (196723 : ℤ) ∧
    (∑ n ∈ Ico 50752 50816, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (3934449495815800817844088904 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_50688_50816 :
    (∑ n ∈ Ico 50688 50816, mobiusTreeValue 16 mobiusTable1200001 n) = (9 : ℤ) ∧
    (∑ n ∈ Ico 50688 50816, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (79 : ℕ) ∧
    (∑ n ∈ Ico 50688 50816, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (886942 : ℤ) ∧
    (∑ n ∈ Ico 50688 50816, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (17738902071934670774499348059 : ℤ) := by
  rcases cdemPrefixStats_50688_50752 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_50752_50816 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 50688 ≤ 50752) (by norm_num : 50752 ≤ 50816), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 50688 ≤ 50752) (by norm_num : 50752 ≤ 50816), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 50688 ≤ 50752) (by norm_num : 50752 ≤ 50816), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 50688 ≤ 50752) (by norm_num : 50752 ≤ 50816), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_50816_50880 :
    (∑ n ∈ Ico 50816 50880, mobiusTreeValue 16 mobiusTable1200001 n) = (-3 : ℤ) ∧
    (∑ n ∈ Ico 50816 50880, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 50816 50880, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-294889 : ℤ) ∧
    (∑ n ∈ Ico 50816 50880, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-5897886631323716457908521847 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_50880_50944 :
    (∑ n ∈ Ico 50880 50944, mobiusTreeValue 16 mobiusTable1200001 n) = (8 : ℤ) ∧
    (∑ n ∈ Ico 50880 50944, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 50880 50944, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (785588 : ℤ) ∧
    (∑ n ∈ Ico 50880 50944, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (15711847571487503597307288042 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_50816_50944 :
    (∑ n ∈ Ico 50816 50944, mobiusTreeValue 16 mobiusTable1200001 n) = (5 : ℤ) ∧
    (∑ n ∈ Ico 50816 50944, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 50816 50944, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (490699 : ℤ) ∧
    (∑ n ∈ Ico 50816 50944, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (9813960940163787139398766195 : ℤ) := by
  rcases cdemPrefixStats_50816_50880 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_50880_50944 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 50816 ≤ 50880) (by norm_num : 50880 ≤ 50944), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 50816 ≤ 50880) (by norm_num : 50880 ≤ 50944), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 50816 ≤ 50880) (by norm_num : 50880 ≤ 50944), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 50816 ≤ 50880) (by norm_num : 50880 ≤ 50944), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_50688_50944 :
    (∑ n ∈ Ico 50688 50944, mobiusTreeValue 16 mobiusTable1200001 n) = (14 : ℤ) ∧
    (∑ n ∈ Ico 50688 50944, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (156 : ℕ) ∧
    (∑ n ∈ Ico 50688 50944, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (1377641 : ℤ) ∧
    (∑ n ∈ Ico 50688 50944, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (27552863012098457913898114254 : ℤ) := by
  rcases cdemPrefixStats_50688_50816 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_50816_50944 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 50688 ≤ 50816) (by norm_num : 50816 ≤ 50944), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 50688 ≤ 50816) (by norm_num : 50816 ≤ 50944), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 50688 ≤ 50816) (by norm_num : 50816 ≤ 50944), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 50688 ≤ 50816) (by norm_num : 50816 ≤ 50944), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_50944_51008 :
    (∑ n ∈ Ico 50944 51008, mobiusTreeValue 16 mobiusTable1200001 n) = (-3 : ℤ) ∧
    (∑ n ∈ Ico 50944 51008, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 50944 51008, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-294200 : ℤ) ∧
    (∑ n ∈ Ico 50944 51008, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-5884046750310164819485286859 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_51008_51072 :
    (∑ n ∈ Ico 51008 51072, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 51008 51072, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 51008 51072, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (98149 : ℤ) ∧
    (∑ n ∈ Ico 51008 51072, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1962970294670236483927166940 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_50944_51072 :
    (∑ n ∈ Ico 50944 51072, mobiusTreeValue 16 mobiusTable1200001 n) = (-2 : ℤ) ∧
    (∑ n ∈ Ico 50944 51072, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (76 : ℕ) ∧
    (∑ n ∈ Ico 50944 51072, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-196051 : ℤ) ∧
    (∑ n ∈ Ico 50944 51072, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-3921076455639928335558119919 : ℤ) := by
  rcases cdemPrefixStats_50944_51008 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_51008_51072 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 50944 ≤ 51008) (by norm_num : 51008 ≤ 51072), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 50944 ≤ 51008) (by norm_num : 51008 ≤ 51072), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 50944 ≤ 51008) (by norm_num : 51008 ≤ 51072), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 50944 ≤ 51008) (by norm_num : 51008 ≤ 51072), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_51072_51136 :
    (∑ n ∈ Ico 51072 51136, mobiusTreeValue 16 mobiusTable1200001 n) = (5 : ℤ) ∧
    (∑ n ∈ Ico 51072 51136, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 51072 51136, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (489753 : ℤ) ∧
    (∑ n ∈ Ico 51072 51136, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (9795075094908015636771242103 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_51136_51200 :
    (∑ n ∈ Ico 51136 51200, mobiusTreeValue 16 mobiusTable1200001 n) = (-4 : ℤ) ∧
    (∑ n ∈ Ico 51136 51200, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 51136 51200, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-390430 : ℤ) ∧
    (∑ n ∈ Ico 51136 51200, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-7808641929522616999949461056 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_51072_51200 :
    (∑ n ∈ Ico 51072 51200, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 51072 51200, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (81 : ℕ) ∧
    (∑ n ∈ Ico 51072 51200, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (99323 : ℤ) ∧
    (∑ n ∈ Ico 51072 51200, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1986433165385398636821781047 : ℤ) := by
  rcases cdemPrefixStats_51072_51136 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_51136_51200 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 51072 ≤ 51136) (by norm_num : 51136 ≤ 51200), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 51072 ≤ 51136) (by norm_num : 51136 ≤ 51200), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 51072 ≤ 51136) (by norm_num : 51136 ≤ 51200), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 51072 ≤ 51136) (by norm_num : 51136 ≤ 51200), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_50944_51200 :
    (∑ n ∈ Ico 50944 51200, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 50944 51200, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (157 : ℕ) ∧
    (∑ n ∈ Ico 50944 51200, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-96728 : ℤ) ∧
    (∑ n ∈ Ico 50944 51200, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-1934643290254529698736338872 : ℤ) := by
  rcases cdemPrefixStats_50944_51072 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_51072_51200 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 50944 ≤ 51072) (by norm_num : 51072 ≤ 51200), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 50944 ≤ 51072) (by norm_num : 51072 ≤ 51200), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 50944 ≤ 51072) (by norm_num : 51072 ≤ 51200), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 50944 ≤ 51072) (by norm_num : 51072 ≤ 51200), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_50688_51200 :
    (∑ n ∈ Ico 50688 51200, mobiusTreeValue 16 mobiusTable1200001 n) = (13 : ℤ) ∧
    (∑ n ∈ Ico 50688 51200, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (313 : ℕ) ∧
    (∑ n ∈ Ico 50688 51200, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (1280913 : ℤ) ∧
    (∑ n ∈ Ico 50688 51200, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (25618219721843928215161775382 : ℤ) := by
  rcases cdemPrefixStats_50688_50944 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_50944_51200 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 50688 ≤ 50944) (by norm_num : 50944 ≤ 51200), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 50688 ≤ 50944) (by norm_num : 50944 ≤ 51200), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 50688 ≤ 50944) (by norm_num : 50944 ≤ 51200), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 50688 ≤ 50944) (by norm_num : 50944 ≤ 51200), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_50176_51200 :
    (∑ n ∈ Ico 50176 51200, mobiusTreeValue 16 mobiusTable1200001 n) = (8 : ℤ) ∧
    (∑ n ∈ Ico 50176 51200, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (624 : ℕ) ∧
    (∑ n ∈ Ico 50176 51200, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (782428 : ℤ) ∧
    (∑ n ∈ Ico 50176 51200, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (15648472882759404228025723074 : ℤ) := by
  rcases cdemPrefixStats_50176_50688 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_50688_51200 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 50176 ≤ 50688) (by norm_num : 50688 ≤ 51200), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 50176 ≤ 50688) (by norm_num : 50688 ≤ 51200), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 50176 ≤ 50688) (by norm_num : 50688 ≤ 51200), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 50176 ≤ 50688) (by norm_num : 50688 ≤ 51200), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_49152_51200 :
    (∑ n ∈ Ico 49152 51200, mobiusTreeValue 16 mobiusTable1200001 n) = (-56 : ℤ) ∧
    (∑ n ∈ Ico 49152 51200, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (1248 : ℕ) ∧
    (∑ n ∈ Ico 49152 51200, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-5664868 : ℤ) ∧
    (∑ n ∈ Ico 49152 51200, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-113297908199260980111592695407 : ℤ) := by
  rcases cdemPrefixStats_49152_50176 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_50176_51200 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 49152 ≤ 50176) (by norm_num : 50176 ≤ 51200), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 49152 ≤ 50176) (by norm_num : 50176 ≤ 51200), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 49152 ≤ 50176) (by norm_num : 50176 ≤ 51200), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 49152 ≤ 50176) (by norm_num : 50176 ≤ 51200), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_51200_51264 :
    (∑ n ∈ Ico 51200 51264, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 51200 51264, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (36 : ℕ) ∧
    (∑ n ∈ Ico 51200 51264, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (163 : ℤ) ∧
    (∑ n ∈ Ico 51200 51264, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (3238036323847429169712785 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_51264_51328 :
    (∑ n ∈ Ico 51264 51328, mobiusTreeValue 16 mobiusTable1200001 n) = (11 : ℤ) ∧
    (∑ n ∈ Ico 51264 51328, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 51264 51328, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (1072324 : ℤ) ∧
    (∑ n ∈ Ico 51264 51328, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (21446639802873790101671860898 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_51200_51328 :
    (∑ n ∈ Ico 51200 51328, mobiusTreeValue 16 mobiusTable1200001 n) = (11 : ℤ) ∧
    (∑ n ∈ Ico 51200 51328, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (73 : ℕ) ∧
    (∑ n ∈ Ico 51200 51328, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (1072487 : ℤ) ∧
    (∑ n ∈ Ico 51200 51328, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (21449877839197637530841573683 : ℤ) := by
  rcases cdemPrefixStats_51200_51264 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_51264_51328 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 51200 ≤ 51264) (by norm_num : 51264 ≤ 51328), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 51200 ≤ 51264) (by norm_num : 51264 ≤ 51328), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 51200 ≤ 51264) (by norm_num : 51264 ≤ 51328), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 51200 ≤ 51264) (by norm_num : 51264 ≤ 51328), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_51328_51392 :
    (∑ n ∈ Ico 51328 51392, mobiusTreeValue 16 mobiusTable1200001 n) = (3 : ℤ) ∧
    (∑ n ∈ Ico 51328 51392, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 51328 51392, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (292059 : ℤ) ∧
    (∑ n ∈ Ico 51328 51392, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (5841195551970120632828320434 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_51392_51456 :
    (∑ n ∈ Ico 51392 51456, mobiusTreeValue 16 mobiusTable1200001 n) = (-7 : ℤ) ∧
    (∑ n ∈ Ico 51392 51456, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 51392 51456, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-680446 : ℤ) ∧
    (∑ n ∈ Ico 51392 51456, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-13608920371118928211447234315 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_51328_51456 :
    (∑ n ∈ Ico 51328 51456, mobiusTreeValue 16 mobiusTable1200001 n) = (-4 : ℤ) ∧
    (∑ n ∈ Ico 51328 51456, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (80 : ℕ) ∧
    (∑ n ∈ Ico 51328 51456, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-388387 : ℤ) ∧
    (∑ n ∈ Ico 51328 51456, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-7767724819148807578618913881 : ℤ) := by
  rcases cdemPrefixStats_51328_51392 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_51392_51456 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 51328 ≤ 51392) (by norm_num : 51392 ≤ 51456), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 51328 ≤ 51392) (by norm_num : 51392 ≤ 51456), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 51328 ≤ 51392) (by norm_num : 51392 ≤ 51456), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 51328 ≤ 51392) (by norm_num : 51392 ≤ 51456), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_51200_51456 :
    (∑ n ∈ Ico 51200 51456, mobiusTreeValue 16 mobiusTable1200001 n) = (7 : ℤ) ∧
    (∑ n ∈ Ico 51200 51456, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (153 : ℕ) ∧
    (∑ n ∈ Ico 51200 51456, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (684100 : ℤ) ∧
    (∑ n ∈ Ico 51200 51456, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (13682153020048829952222659802 : ℤ) := by
  rcases cdemPrefixStats_51200_51328 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_51328_51456 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 51200 ≤ 51328) (by norm_num : 51328 ≤ 51456), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 51200 ≤ 51328) (by norm_num : 51328 ≤ 51456), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 51200 ≤ 51328) (by norm_num : 51328 ≤ 51456), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 51200 ≤ 51328) (by norm_num : 51328 ≤ 51456), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_51456_51520 :
    (∑ n ∈ Ico 51456 51520, mobiusTreeValue 16 mobiusTable1200001 n) = (-4 : ℤ) ∧
    (∑ n ∈ Ico 51456 51520, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 51456 51520, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-388460 : ℤ) ∧
    (∑ n ∈ Ico 51456 51520, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-7769329174248306944009836582 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_51520_51584 :
    (∑ n ∈ Ico 51520 51584, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 51520 51584, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 51520 51584, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (96853 : ℤ) ∧
    (∑ n ∈ Ico 51520 51584, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1937041635430830068983350886 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_51456_51584 :
    (∑ n ∈ Ico 51456 51584, mobiusTreeValue 16 mobiusTable1200001 n) = (-3 : ℤ) ∧
    (∑ n ∈ Ico 51456 51584, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 51456 51584, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-291607 : ℤ) ∧
    (∑ n ∈ Ico 51456 51584, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-5832287538817476875026485696 : ℤ) := by
  rcases cdemPrefixStats_51456_51520 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_51520_51584 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 51456 ≤ 51520) (by norm_num : 51520 ≤ 51584), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 51456 ≤ 51520) (by norm_num : 51520 ≤ 51584), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 51456 ≤ 51520) (by norm_num : 51520 ≤ 51584), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 51456 ≤ 51520) (by norm_num : 51520 ≤ 51584), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_51584_51648 :
    (∑ n ∈ Ico 51584 51648, mobiusTreeValue 16 mobiusTable1200001 n) = (2 : ℤ) ∧
    (∑ n ∈ Ico 51584 51648, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 51584 51648, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (193758 : ℤ) ∧
    (∑ n ∈ Ico 51584 51648, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (3875256392293152215774207427 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_51648_51712 :
    (∑ n ∈ Ico 51648 51712, mobiusTreeValue 16 mobiusTable1200001 n) = (-5 : ℤ) ∧
    (∑ n ∈ Ico 51648 51712, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 51648 51712, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-483912 : ℤ) ∧
    (∑ n ∈ Ico 51648 51712, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-9678333195573677584421406100 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_51584_51712 :
    (∑ n ∈ Ico 51584 51712, mobiusTreeValue 16 mobiusTable1200001 n) = (-3 : ℤ) ∧
    (∑ n ∈ Ico 51584 51712, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (79 : ℕ) ∧
    (∑ n ∈ Ico 51584 51712, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-290154 : ℤ) ∧
    (∑ n ∈ Ico 51584 51712, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-5803076803280525368647198673 : ℤ) := by
  rcases cdemPrefixStats_51584_51648 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_51648_51712 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 51584 ≤ 51648) (by norm_num : 51648 ≤ 51712), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 51584 ≤ 51648) (by norm_num : 51648 ≤ 51712), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 51584 ≤ 51648) (by norm_num : 51648 ≤ 51712), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 51584 ≤ 51648) (by norm_num : 51648 ≤ 51712), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_51456_51712 :
    (∑ n ∈ Ico 51456 51712, mobiusTreeValue 16 mobiusTable1200001 n) = (-6 : ℤ) ∧
    (∑ n ∈ Ico 51456 51712, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (156 : ℕ) ∧
    (∑ n ∈ Ico 51456 51712, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-581761 : ℤ) ∧
    (∑ n ∈ Ico 51456 51712, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-11635364342098002243673684369 : ℤ) := by
  rcases cdemPrefixStats_51456_51584 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_51584_51712 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 51456 ≤ 51584) (by norm_num : 51584 ≤ 51712), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 51456 ≤ 51584) (by norm_num : 51584 ≤ 51712), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 51456 ≤ 51584) (by norm_num : 51584 ≤ 51712), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 51456 ≤ 51584) (by norm_num : 51584 ≤ 51712), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_51200_51712 :
    (∑ n ∈ Ico 51200 51712, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 51200 51712, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (309 : ℕ) ∧
    (∑ n ∈ Ico 51200 51712, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (102339 : ℤ) ∧
    (∑ n ∈ Ico 51200 51712, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (2046788677950827708548975433 : ℤ) := by
  rcases cdemPrefixStats_51200_51456 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_51456_51712 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 51200 ≤ 51456) (by norm_num : 51456 ≤ 51712), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 51200 ≤ 51456) (by norm_num : 51456 ≤ 51712), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 51200 ≤ 51456) (by norm_num : 51456 ≤ 51712), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 51200 ≤ 51456) (by norm_num : 51456 ≤ 51712), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_51712_51776 :
    (∑ n ∈ Ico 51712 51776, mobiusTreeValue 16 mobiusTable1200001 n) = (-6 : ℤ) ∧
    (∑ n ∈ Ico 51712 51776, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 51712 51776, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-579884 : ℤ) ∧
    (∑ n ∈ Ico 51712 51776, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-11597789246152450844009972002 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_51776_51840 :
    (∑ n ∈ Ico 51776 51840, mobiusTreeValue 16 mobiusTable1200001 n) = (-10 : ℤ) ∧
    (∑ n ∈ Ico 51776 51840, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 51776 51840, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-965119 : ℤ) ∧
    (∑ n ∈ Ico 51776 51840, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-19302486450597354967770340024 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_51712_51840 :
    (∑ n ∈ Ico 51712 51840, mobiusTreeValue 16 mobiusTable1200001 n) = (-16 : ℤ) ∧
    (∑ n ∈ Ico 51712 51840, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (80 : ℕ) ∧
    (∑ n ∈ Ico 51712 51840, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-1545003 : ℤ) ∧
    (∑ n ∈ Ico 51712 51840, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-30900275696749805811780312026 : ℤ) := by
  rcases cdemPrefixStats_51712_51776 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_51776_51840 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 51712 ≤ 51776) (by norm_num : 51776 ≤ 51840), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 51712 ≤ 51776) (by norm_num : 51776 ≤ 51840), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 51712 ≤ 51776) (by norm_num : 51776 ≤ 51840), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 51712 ≤ 51776) (by norm_num : 51776 ≤ 51840), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_51840_51904 :
    (∑ n ∈ Ico 51840 51904, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 51840 51904, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 51840 51904, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (96396 : ℤ) ∧
    (∑ n ∈ Ico 51840 51904, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1927933814984613946942539540 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_51904_51968 :
    (∑ n ∈ Ico 51904 51968, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 51904 51968, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 51904 51968, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-252 : ℤ) ∧
    (∑ n ∈ Ico 51904 51968, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-5004800602379385583381909 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_51840_51968 :
    (∑ n ∈ Ico 51840 51968, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 51840 51968, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 51840 51968, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (96144 : ℤ) ∧
    (∑ n ∈ Ico 51840 51968, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1922929014382234561359157631 : ℤ) := by
  rcases cdemPrefixStats_51840_51904 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_51904_51968 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 51840 ≤ 51904) (by norm_num : 51904 ≤ 51968), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 51840 ≤ 51904) (by norm_num : 51904 ≤ 51968), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 51840 ≤ 51904) (by norm_num : 51904 ≤ 51968), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 51840 ≤ 51904) (by norm_num : 51904 ≤ 51968), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_51712_51968 :
    (∑ n ∈ Ico 51712 51968, mobiusTreeValue 16 mobiusTable1200001 n) = (-15 : ℤ) ∧
    (∑ n ∈ Ico 51712 51968, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (157 : ℕ) ∧
    (∑ n ∈ Ico 51712 51968, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-1448859 : ℤ) ∧
    (∑ n ∈ Ico 51712 51968, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-28977346682367571250421154395 : ℤ) := by
  rcases cdemPrefixStats_51712_51840 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_51840_51968 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 51712 ≤ 51840) (by norm_num : 51840 ≤ 51968), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 51712 ≤ 51840) (by norm_num : 51840 ≤ 51968), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 51712 ≤ 51840) (by norm_num : 51840 ≤ 51968), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 51712 ≤ 51840) (by norm_num : 51840 ≤ 51968), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_51968_52032 :
    (∑ n ∈ Ico 51968 52032, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 51968 52032, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 51968 52032, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (96059 : ℤ) ∧
    (∑ n ∈ Ico 51968 52032, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1921224779574592735063176490 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_52032_52096 :
    (∑ n ∈ Ico 52032 52096, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 52032 52096, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 52032 52096, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-95861 : ℤ) ∧
    (∑ n ∈ Ico 52032 52096, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-1917206080673821183029143364 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_51968_52096 :
    (∑ n ∈ Ico 51968 52096, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 51968 52096, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 51968 52096, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (198 : ℤ) ∧
    (∑ n ∈ Ico 51968 52096, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (4018698900771552034033126 : ℤ) := by
  rcases cdemPrefixStats_51968_52032 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_52032_52096 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 51968 ≤ 52032) (by norm_num : 52032 ≤ 52096), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 51968 ≤ 52032) (by norm_num : 52032 ≤ 52096), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 51968 ≤ 52032) (by norm_num : 52032 ≤ 52096), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 51968 ≤ 52032) (by norm_num : 52032 ≤ 52096), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_52096_52160 :
    (∑ n ∈ Ico 52096 52160, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 52096 52160, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 52096 52160, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-96016 : ℤ) ∧
    (∑ n ∈ Ico 52096 52160, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-1920378134720939884897088902 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_52160_52224 :
    (∑ n ∈ Ico 52160 52224, mobiusTreeValue 16 mobiusTable1200001 n) = (-3 : ℤ) ∧
    (∑ n ∈ Ico 52160 52224, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 52160 52224, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-287518 : ℤ) ∧
    (∑ n ∈ Ico 52160 52224, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-5750392757440360543777895687 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_52096_52224 :
    (∑ n ∈ Ico 52096 52224, mobiusTreeValue 16 mobiusTable1200001 n) = (-4 : ℤ) ∧
    (∑ n ∈ Ico 52096 52224, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (76 : ℕ) ∧
    (∑ n ∈ Ico 52096 52224, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-383534 : ℤ) ∧
    (∑ n ∈ Ico 52096 52224, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-7670770892161300428674984589 : ℤ) := by
  rcases cdemPrefixStats_52096_52160 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_52160_52224 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 52096 ≤ 52160) (by norm_num : 52160 ≤ 52224), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 52096 ≤ 52160) (by norm_num : 52160 ≤ 52224), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 52096 ≤ 52160) (by norm_num : 52160 ≤ 52224), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 52096 ≤ 52160) (by norm_num : 52160 ≤ 52224), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_51968_52224 :
    (∑ n ∈ Ico 51968 52224, mobiusTreeValue 16 mobiusTable1200001 n) = (-4 : ℤ) ∧
    (∑ n ∈ Ico 51968 52224, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (154 : ℕ) ∧
    (∑ n ∈ Ico 51968 52224, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-383336 : ℤ) ∧
    (∑ n ∈ Ico 51968 52224, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-7666752193260528876640951463 : ℤ) := by
  rcases cdemPrefixStats_51968_52096 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_52096_52224 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 51968 ≤ 52096) (by norm_num : 52096 ≤ 52224), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 51968 ≤ 52096) (by norm_num : 52096 ≤ 52224), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 51968 ≤ 52096) (by norm_num : 52096 ≤ 52224), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 51968 ≤ 52096) (by norm_num : 52096 ≤ 52224), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_51712_52224 :
    (∑ n ∈ Ico 51712 52224, mobiusTreeValue 16 mobiusTable1200001 n) = (-19 : ℤ) ∧
    (∑ n ∈ Ico 51712 52224, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (311 : ℕ) ∧
    (∑ n ∈ Ico 51712 52224, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-1832195 : ℤ) ∧
    (∑ n ∈ Ico 51712 52224, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-36644098875628100127062105858 : ℤ) := by
  rcases cdemPrefixStats_51712_51968 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_51968_52224 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 51712 ≤ 51968) (by norm_num : 51968 ≤ 52224), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 51712 ≤ 51968) (by norm_num : 51968 ≤ 52224), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 51712 ≤ 51968) (by norm_num : 51968 ≤ 52224), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 51712 ≤ 51968) (by norm_num : 51968 ≤ 52224), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_51200_52224 :
    (∑ n ∈ Ico 51200 52224, mobiusTreeValue 16 mobiusTable1200001 n) = (-18 : ℤ) ∧
    (∑ n ∈ Ico 51200 52224, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (620 : ℕ) ∧
    (∑ n ∈ Ico 51200 52224, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-1729856 : ℤ) ∧
    (∑ n ∈ Ico 51200 52224, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-34597310197677272418513130425 : ℤ) := by
  rcases cdemPrefixStats_51200_51712 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_51712_52224 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 51200 ≤ 51712) (by norm_num : 51712 ≤ 52224), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 51200 ≤ 51712) (by norm_num : 51712 ≤ 52224), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 51200 ≤ 51712) (by norm_num : 51712 ≤ 52224), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 51200 ≤ 51712) (by norm_num : 51712 ≤ 52224), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_52224_52288 :
    (∑ n ∈ Ico 52224 52288, mobiusTreeValue 16 mobiusTable1200001 n) = (2 : ℤ) ∧
    (∑ n ∈ Ico 52224 52288, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 52224 52288, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (191340 : ℤ) ∧
    (∑ n ∈ Ico 52224 52288, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (3826836803338937166684196267 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_52288_52352 :
    (∑ n ∈ Ico 52288 52352, mobiusTreeValue 16 mobiusTable1200001 n) = (5 : ℤ) ∧
    (∑ n ∈ Ico 52288 52352, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 52288 52352, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (477591 : ℤ) ∧
    (∑ n ∈ Ico 52288 52352, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (9551826839745953747216909145 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_52224_52352 :
    (∑ n ∈ Ico 52224 52352, mobiusTreeValue 16 mobiusTable1200001 n) = (7 : ℤ) ∧
    (∑ n ∈ Ico 52224 52352, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 52224 52352, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (668931 : ℤ) ∧
    (∑ n ∈ Ico 52224 52352, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (13378663643084890913901105412 : ℤ) := by
  rcases cdemPrefixStats_52224_52288 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_52288_52352 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 52224 ≤ 52288) (by norm_num : 52288 ≤ 52352), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 52224 ≤ 52288) (by norm_num : 52288 ≤ 52352), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 52224 ≤ 52288) (by norm_num : 52288 ≤ 52352), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 52224 ≤ 52288) (by norm_num : 52288 ≤ 52352), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_52352_52416 :
    (∑ n ∈ Ico 52352 52416, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 52352 52416, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 52352 52416, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-320 : ℤ) ∧
    (∑ n ∈ Ico 52352 52416, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-6377161075607443108328945 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_52416_52480 :
    (∑ n ∈ Ico 52416 52480, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 52416 52480, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 52416 52480, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-252 : ℤ) ∧
    (∑ n ∈ Ico 52416 52480, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-5016640006059318252896995 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_52352_52480 :
    (∑ n ∈ Ico 52352 52480, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 52352 52480, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (76 : ℕ) ∧
    (∑ n ∈ Ico 52352 52480, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-572 : ℤ) ∧
    (∑ n ∈ Ico 52352 52480, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-11393801081666761361225940 : ℤ) := by
  rcases cdemPrefixStats_52352_52416 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_52416_52480 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 52352 ≤ 52416) (by norm_num : 52416 ≤ 52480), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 52352 ≤ 52416) (by norm_num : 52416 ≤ 52480), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 52352 ≤ 52416) (by norm_num : 52416 ≤ 52480), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 52352 ≤ 52416) (by norm_num : 52416 ≤ 52480), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_52224_52480 :
    (∑ n ∈ Ico 52224 52480, mobiusTreeValue 16 mobiusTable1200001 n) = (7 : ℤ) ∧
    (∑ n ∈ Ico 52224 52480, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (153 : ℕ) ∧
    (∑ n ∈ Ico 52224 52480, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (668359 : ℤ) ∧
    (∑ n ∈ Ico 52224 52480, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (13367269842003224152539879472 : ℤ) := by
  rcases cdemPrefixStats_52224_52352 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_52352_52480 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 52224 ≤ 52352) (by norm_num : 52352 ≤ 52480), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 52224 ≤ 52352) (by norm_num : 52352 ≤ 52480), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 52224 ≤ 52352) (by norm_num : 52352 ≤ 52480), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 52224 ≤ 52352) (by norm_num : 52352 ≤ 52480), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_52480_52544 :
    (∑ n ∈ Ico 52480 52544, mobiusTreeValue 16 mobiusTable1200001 n) = (9 : ℤ) ∧
    (∑ n ∈ Ico 52480 52544, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 52480 52544, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (857129 : ℤ) ∧
    (∑ n ∈ Ico 52480 52544, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (17142711366820425177119470243 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_52544_52608 :
    (∑ n ∈ Ico 52544 52608, mobiusTreeValue 16 mobiusTable1200001 n) = (-4 : ℤ) ∧
    (∑ n ∈ Ico 52544 52608, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 52544 52608, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-380509 : ℤ) ∧
    (∑ n ∈ Ico 52544 52608, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-7610239202702016279530581548 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_52480_52608 :
    (∑ n ∈ Ico 52480 52608, mobiusTreeValue 16 mobiusTable1200001 n) = (5 : ℤ) ∧
    (∑ n ∈ Ico 52480 52608, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (79 : ℕ) ∧
    (∑ n ∈ Ico 52480 52608, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (476620 : ℤ) ∧
    (∑ n ∈ Ico 52480 52608, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (9532472164118408897588888695 : ℤ) := by
  rcases cdemPrefixStats_52480_52544 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_52544_52608 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 52480 ≤ 52544) (by norm_num : 52544 ≤ 52608), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 52480 ≤ 52544) (by norm_num : 52544 ≤ 52608), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 52480 ≤ 52544) (by norm_num : 52544 ≤ 52608), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 52480 ≤ 52544) (by norm_num : 52544 ≤ 52608), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_52608_52672 :
    (∑ n ∈ Ico 52608 52672, mobiusTreeValue 16 mobiusTable1200001 n) = (6 : ℤ) ∧
    (∑ n ∈ Ico 52608 52672, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 52608 52672, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (569863 : ℤ) ∧
    (∑ n ∈ Ico 52608 52672, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (11397274602215012318880411663 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_52672_52736 :
    (∑ n ∈ Ico 52672 52736, mobiusTreeValue 16 mobiusTable1200001 n) = (-11 : ℤ) ∧
    (∑ n ∈ Ico 52672 52736, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 52672 52736, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-1043299 : ℤ) ∧
    (∑ n ∈ Ico 52672 52736, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-20866100022694943296885335228 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_52608_52736 :
    (∑ n ∈ Ico 52608 52736, mobiusTreeValue 16 mobiusTable1200001 n) = (-5 : ℤ) ∧
    (∑ n ∈ Ico 52608 52736, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (79 : ℕ) ∧
    (∑ n ∈ Ico 52608 52736, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-473436 : ℤ) ∧
    (∑ n ∈ Ico 52608 52736, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-9468825420479930978004923565 : ℤ) := by
  rcases cdemPrefixStats_52608_52672 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_52672_52736 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 52608 ≤ 52672) (by norm_num : 52672 ≤ 52736), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 52608 ≤ 52672) (by norm_num : 52672 ≤ 52736), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 52608 ≤ 52672) (by norm_num : 52672 ≤ 52736), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 52608 ≤ 52672) (by norm_num : 52672 ≤ 52736), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_52480_52736 :
    (∑ n ∈ Ico 52480 52736, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 52480 52736, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (158 : ℕ) ∧
    (∑ n ∈ Ico 52480 52736, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (3184 : ℤ) ∧
    (∑ n ∈ Ico 52480 52736, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (63646743638477919583965130 : ℤ) := by
  rcases cdemPrefixStats_52480_52608 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_52608_52736 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 52480 ≤ 52608) (by norm_num : 52608 ≤ 52736), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 52480 ≤ 52608) (by norm_num : 52608 ≤ 52736), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 52480 ≤ 52608) (by norm_num : 52608 ≤ 52736), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 52480 ≤ 52608) (by norm_num : 52608 ≤ 52736), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_52224_52736 :
    (∑ n ∈ Ico 52224 52736, mobiusTreeValue 16 mobiusTable1200001 n) = (7 : ℤ) ∧
    (∑ n ∈ Ico 52224 52736, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (311 : ℕ) ∧
    (∑ n ∈ Ico 52224 52736, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (671543 : ℤ) ∧
    (∑ n ∈ Ico 52224 52736, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (13430916585641702072123844602 : ℤ) := by
  rcases cdemPrefixStats_52224_52480 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_52480_52736 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 52224 ≤ 52480) (by norm_num : 52480 ≤ 52736), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 52224 ≤ 52480) (by norm_num : 52480 ≤ 52736), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 52224 ≤ 52480) (by norm_num : 52480 ≤ 52736), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 52224 ≤ 52480) (by norm_num : 52480 ≤ 52736), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_52736_52800 :
    (∑ n ∈ Ico 52736 52800, mobiusTreeValue 16 mobiusTable1200001 n) = (10 : ℤ) ∧
    (∑ n ∈ Ico 52736 52800, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 52736 52800, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (947433 : ℤ) ∧
    (∑ n ∈ Ico 52736 52800, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (18948693396280567291520360429 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_52800_52864 :
    (∑ n ∈ Ico 52800 52864, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 52800 52864, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 52800 52864, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (94318 : ℤ) ∧
    (∑ n ∈ Ico 52800 52864, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1886341535755494183934030848 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_52736_52864 :
    (∑ n ∈ Ico 52736 52864, mobiusTreeValue 16 mobiusTable1200001 n) = (11 : ℤ) ∧
    (∑ n ∈ Ico 52736 52864, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (79 : ℕ) ∧
    (∑ n ∈ Ico 52736 52864, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (1041751 : ℤ) ∧
    (∑ n ∈ Ico 52736 52864, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (20835034932036061475454391277 : ℤ) := by
  rcases cdemPrefixStats_52736_52800 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_52800_52864 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 52736 ≤ 52800) (by norm_num : 52800 ≤ 52864), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 52736 ≤ 52800) (by norm_num : 52800 ≤ 52864), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 52736 ≤ 52800) (by norm_num : 52800 ≤ 52864), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 52736 ≤ 52800) (by norm_num : 52800 ≤ 52864), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_52864_52928 :
    (∑ n ∈ Ico 52864 52928, mobiusTreeValue 16 mobiusTable1200001 n) = (-6 : ℤ) ∧
    (∑ n ∈ Ico 52864 52928, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 52864 52928, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-566910 : ℤ) ∧
    (∑ n ∈ Ico 52864 52928, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-11338223298171601316992151380 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_52928_52992 :
    (∑ n ∈ Ico 52928 52992, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 52928 52992, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 52928 52992, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (94466 : ℤ) ∧
    (∑ n ∈ Ico 52928 52992, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1889289565526174989383180361 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_52864_52992 :
    (∑ n ∈ Ico 52864 52992, mobiusTreeValue 16 mobiusTable1200001 n) = (-5 : ℤ) ∧
    (∑ n ∈ Ico 52864 52992, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 52864 52992, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-472444 : ℤ) ∧
    (∑ n ∈ Ico 52864 52992, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-9448933732645426327608971019 : ℤ) := by
  rcases cdemPrefixStats_52864_52928 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_52928_52992 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 52864 ≤ 52928) (by norm_num : 52928 ≤ 52992), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 52864 ≤ 52928) (by norm_num : 52928 ≤ 52992), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 52864 ≤ 52928) (by norm_num : 52928 ≤ 52992), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 52864 ≤ 52928) (by norm_num : 52928 ≤ 52992), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_52736_52992 :
    (∑ n ∈ Ico 52736 52992, mobiusTreeValue 16 mobiusTable1200001 n) = (6 : ℤ) ∧
    (∑ n ∈ Ico 52736 52992, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (156 : ℕ) ∧
    (∑ n ∈ Ico 52736 52992, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (569307 : ℤ) ∧
    (∑ n ∈ Ico 52736 52992, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (11386101199390635147845420258 : ℤ) := by
  rcases cdemPrefixStats_52736_52864 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_52864_52992 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 52736 ≤ 52864) (by norm_num : 52864 ≤ 52992), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 52736 ≤ 52864) (by norm_num : 52864 ≤ 52992), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 52736 ≤ 52864) (by norm_num : 52864 ≤ 52992), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 52736 ≤ 52864) (by norm_num : 52864 ≤ 52992), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_52992_53056 :
    (∑ n ∈ Ico 52992 53056, mobiusTreeValue 16 mobiusTable1200001 n) = (-3 : ℤ) ∧
    (∑ n ∈ Ico 52992 53056, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 52992 53056, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-282893 : ℤ) ∧
    (∑ n ∈ Ico 52992 53056, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-5657958421571737454790477222 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_53056_53120 :
    (∑ n ∈ Ico 53056 53120, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 53056 53120, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 53056 53120, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-94019 : ℤ) ∧
    (∑ n ∈ Ico 53056 53120, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-1880399170798463504355863117 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_52992_53120 :
    (∑ n ∈ Ico 52992 53120, mobiusTreeValue 16 mobiusTable1200001 n) = (-4 : ℤ) ∧
    (∑ n ∈ Ico 52992 53120, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (76 : ℕ) ∧
    (∑ n ∈ Ico 52992 53120, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-376912 : ℤ) ∧
    (∑ n ∈ Ico 52992 53120, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-7538357592370200959146340339 : ℤ) := by
  rcases cdemPrefixStats_52992_53056 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_53056_53120 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 52992 ≤ 53056) (by norm_num : 53056 ≤ 53120), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 52992 ≤ 53056) (by norm_num : 53056 ≤ 53120), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 52992 ≤ 53056) (by norm_num : 53056 ≤ 53120), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 52992 ≤ 53056) (by norm_num : 53056 ≤ 53120), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_53120_53184 :
    (∑ n ∈ Ico 53120 53184, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 53120 53184, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 53120 53184, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (223 : ℤ) ∧
    (∑ n ∈ Ico 53120 53184, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (4496339088837721724010395 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_53184_53248 :
    (∑ n ∈ Ico 53184 53248, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 53184 53248, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 53184 53248, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-93797 : ℤ) ∧
    (∑ n ∈ Ico 53184 53248, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-1875956061314634814156006828 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_53120_53248 :
    (∑ n ∈ Ico 53120 53248, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 53120 53248, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (79 : ℕ) ∧
    (∑ n ∈ Ico 53120 53248, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-93574 : ℤ) ∧
    (∑ n ∈ Ico 53120 53248, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-1871459722225797092431996433 : ℤ) := by
  rcases cdemPrefixStats_53120_53184 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_53184_53248 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 53120 ≤ 53184) (by norm_num : 53184 ≤ 53248), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 53120 ≤ 53184) (by norm_num : 53184 ≤ 53248), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 53120 ≤ 53184) (by norm_num : 53184 ≤ 53248), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 53120 ≤ 53184) (by norm_num : 53184 ≤ 53248), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_52992_53248 :
    (∑ n ∈ Ico 52992 53248, mobiusTreeValue 16 mobiusTable1200001 n) = (-5 : ℤ) ∧
    (∑ n ∈ Ico 52992 53248, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (155 : ℕ) ∧
    (∑ n ∈ Ico 52992 53248, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-470486 : ℤ) ∧
    (∑ n ∈ Ico 52992 53248, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-9409817314595998051578336772 : ℤ) := by
  rcases cdemPrefixStats_52992_53120 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_53120_53248 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 52992 ≤ 53120) (by norm_num : 53120 ≤ 53248), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 52992 ≤ 53120) (by norm_num : 53120 ≤ 53248), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 52992 ≤ 53120) (by norm_num : 53120 ≤ 53248), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 52992 ≤ 53120) (by norm_num : 53120 ≤ 53248), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_52736_53248 :
    (∑ n ∈ Ico 52736 53248, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 52736 53248, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (311 : ℕ) ∧
    (∑ n ∈ Ico 52736 53248, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (98821 : ℤ) ∧
    (∑ n ∈ Ico 52736 53248, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1976283884794637096267083486 : ℤ) := by
  rcases cdemPrefixStats_52736_52992 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_52992_53248 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 52736 ≤ 52992) (by norm_num : 52992 ≤ 53248), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 52736 ≤ 52992) (by norm_num : 52992 ≤ 53248), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 52736 ≤ 52992) (by norm_num : 52992 ≤ 53248), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 52736 ≤ 52992) (by norm_num : 52992 ≤ 53248), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_52224_53248 :
    (∑ n ∈ Ico 52224 53248, mobiusTreeValue 16 mobiusTable1200001 n) = (8 : ℤ) ∧
    (∑ n ∈ Ico 52224 53248, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (622 : ℕ) ∧
    (∑ n ∈ Ico 52224 53248, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (770364 : ℤ) ∧
    (∑ n ∈ Ico 52224 53248, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (15407200470436339168390928088 : ℤ) := by
  rcases cdemPrefixStats_52224_52736 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_52736_53248 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 52224 ≤ 52736) (by norm_num : 52736 ≤ 53248), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 52224 ≤ 52736) (by norm_num : 52736 ≤ 53248), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 52224 ≤ 52736) (by norm_num : 52736 ≤ 53248), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 52224 ≤ 52736) (by norm_num : 52736 ≤ 53248), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_51200_53248 :
    (∑ n ∈ Ico 51200 53248, mobiusTreeValue 16 mobiusTable1200001 n) = (-10 : ℤ) ∧
    (∑ n ∈ Ico 51200 53248, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (1242 : ℕ) ∧
    (∑ n ∈ Ico 51200 53248, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-959492 : ℤ) ∧
    (∑ n ∈ Ico 51200 53248, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-19190109727240933250122202337 : ℤ) := by
  rcases cdemPrefixStats_51200_52224 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_52224_53248 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 51200 ≤ 52224) (by norm_num : 52224 ≤ 53248), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 51200 ≤ 52224) (by norm_num : 52224 ≤ 53248), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 51200 ≤ 52224) (by norm_num : 52224 ≤ 53248), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 51200 ≤ 52224) (by norm_num : 52224 ≤ 53248), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_49152_53248 :
    (∑ n ∈ Ico 49152 53248, mobiusTreeValue 16 mobiusTable1200001 n) = (-66 : ℤ) ∧
    (∑ n ∈ Ico 49152 53248, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (2490 : ℕ) ∧
    (∑ n ∈ Ico 49152 53248, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-6624360 : ℤ) ∧
    (∑ n ∈ Ico 49152 53248, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-132488017926501913361714897744 : ℤ) := by
  rcases cdemPrefixStats_49152_51200 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_51200_53248 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 49152 ≤ 51200) (by norm_num : 51200 ≤ 53248), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 49152 ≤ 51200) (by norm_num : 51200 ≤ 53248), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 49152 ≤ 51200) (by norm_num : 51200 ≤ 53248), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 49152 ≤ 51200) (by norm_num : 51200 ≤ 53248), hR1, hR2] <;> norm_num

theorem cdemPrefixGroup012_checked_complete :
    (∑ n ∈ Ico 49152 53248, mobiusTreeValue 16 mobiusTable1200001 n) = (-66 : ℤ) ∧
    (∑ n ∈ Ico 49152 53248, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (2490 : ℕ) ∧
    (∑ n ∈ Ico 49152 53248, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-6624360 : ℤ) ∧
    (∑ n ∈ Ico 49152 53248, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-132488017926501913361714897744 : ℤ) := cdemPrefixStats_49152_53248
end Helfgott
#print axioms Helfgott.cdemPrefixGroup012_checked_complete

open Helfgott Finset
open scoped BigOperators

theorem solution :
    (∑ n ∈ Ico 49152 53248, mobiusTreeValue 16 mobiusTable1200001 n) = (-66 : ℤ) ∧
    (∑ n ∈ Ico 49152 53248, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (2490 : ℕ) ∧
    (∑ n ∈ Ico 49152 53248, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-6624360 : ℤ) ∧
    (∑ n ∈ Ico 49152 53248, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-132488017926501913361714897744 : ℤ) := Helfgott.cdemPrefixGroup012_checked_complete
#print axioms solution
