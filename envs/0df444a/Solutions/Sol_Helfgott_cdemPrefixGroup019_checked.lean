-- Prove2me | solution 1 for Helfgott.cdemPrefixGroup019_checked
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-09T01:52:11.207287+00:00
-- url     : https://prove2.me/submissions/06f82f6f-28aa-4fba-a344-10070bf43530

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
private theorem cdemPrefixStats_77824_77888 :
    (∑ n ∈ Ico 77824 77888, mobiusTreeValue 16 mobiusTable1200001 n) = (6 : ℤ) ∧
    (∑ n ∈ Ico 77824 77888, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 77824 77888, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (385432 : ℤ) ∧
    (∑ n ∈ Ico 77824 77888, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (7708647264229374210496522626 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_77888_77952 :
    (∑ n ∈ Ico 77888 77952, mobiusTreeValue 16 mobiusTable1200001 n) = (5 : ℤ) ∧
    (∑ n ∈ Ico 77888 77952, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 77888 77952, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (320635 : ℤ) ∧
    (∑ n ∈ Ico 77888 77952, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (6412785989467383865682109166 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_77824_77952 :
    (∑ n ∈ Ico 77824 77952, mobiusTreeValue 16 mobiusTable1200001 n) = (11 : ℤ) ∧
    (∑ n ∈ Ico 77824 77952, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (79 : ℕ) ∧
    (∑ n ∈ Ico 77824 77952, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (706067 : ℤ) ∧
    (∑ n ∈ Ico 77824 77952, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (14121433253696758076178631792 : ℤ) := by
  rcases cdemPrefixStats_77824_77888 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_77888_77952 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 77824 ≤ 77888) (by norm_num : 77888 ≤ 77952), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 77824 ≤ 77888) (by norm_num : 77888 ≤ 77952), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 77824 ≤ 77888) (by norm_num : 77888 ≤ 77952), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 77824 ≤ 77888) (by norm_num : 77888 ≤ 77952), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_77952_78016 :
    (∑ n ∈ Ico 77952 78016, mobiusTreeValue 16 mobiusTable1200001 n) = (-3 : ℤ) ∧
    (∑ n ∈ Ico 77952 78016, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 77952 78016, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-192397 : ℤ) ∧
    (∑ n ∈ Ico 77952 78016, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-3848012065464733727865409493 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_78016_78080 :
    (∑ n ∈ Ico 78016 78080, mobiusTreeValue 16 mobiusTable1200001 n) = (-9 : ℤ) ∧
    (∑ n ∈ Ico 78016 78080, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 78016 78080, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-576624 : ℤ) ∧
    (∑ n ∈ Ico 78016 78080, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-11532564787859102744195631267 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_77952_78080 :
    (∑ n ∈ Ico 77952 78080, mobiusTreeValue 16 mobiusTable1200001 n) = (-12 : ℤ) ∧
    (∑ n ∈ Ico 77952 78080, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 77952 78080, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-769021 : ℤ) ∧
    (∑ n ∈ Ico 77952 78080, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-15380576853323836472061040760 : ℤ) := by
  rcases cdemPrefixStats_77952_78016 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_78016_78080 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 77952 ≤ 78016) (by norm_num : 78016 ≤ 78080), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 77952 ≤ 78016) (by norm_num : 78016 ≤ 78080), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 77952 ≤ 78016) (by norm_num : 78016 ≤ 78080), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 77952 ≤ 78016) (by norm_num : 78016 ≤ 78080), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_77824_78080 :
    (∑ n ∈ Ico 77824 78080, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 77824 78080, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (157 : ℕ) ∧
    (∑ n ∈ Ico 77824 78080, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-62954 : ℤ) ∧
    (∑ n ∈ Ico 77824 78080, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-1259143599627078395882408968 : ℤ) := by
  rcases cdemPrefixStats_77824_77952 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_77952_78080 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 77824 ≤ 77952) (by norm_num : 77952 ≤ 78080), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 77824 ≤ 77952) (by norm_num : 77952 ≤ 78080), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 77824 ≤ 77952) (by norm_num : 77952 ≤ 78080), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 77824 ≤ 77952) (by norm_num : 77952 ≤ 78080), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_78080_78144 :
    (∑ n ∈ Ico 78080 78144, mobiusTreeValue 16 mobiusTable1200001 n) = (8 : ℤ) ∧
    (∑ n ∈ Ico 78080 78144, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 78080 78144, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (512210 : ℤ) ∧
    (∑ n ∈ Ico 78080 78144, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (10244310437012824921996252363 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_78144_78208 :
    (∑ n ∈ Ico 78144 78208, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 78144 78208, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 78144 78208, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (63947 : ℤ) ∧
    (∑ n ∈ Ico 78144 78208, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1278903360437837242928490697 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_78080_78208 :
    (∑ n ∈ Ico 78080 78208, mobiusTreeValue 16 mobiusTable1200001 n) = (9 : ℤ) ∧
    (∑ n ∈ Ico 78080 78208, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (79 : ℕ) ∧
    (∑ n ∈ Ico 78080 78208, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (576157 : ℤ) ∧
    (∑ n ∈ Ico 78080 78208, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (11523213797450662164924743060 : ℤ) := by
  rcases cdemPrefixStats_78080_78144 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_78144_78208 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 78080 ≤ 78144) (by norm_num : 78144 ≤ 78208), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 78080 ≤ 78144) (by norm_num : 78144 ≤ 78208), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 78080 ≤ 78144) (by norm_num : 78144 ≤ 78208), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 78080 ≤ 78144) (by norm_num : 78144 ≤ 78208), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_78208_78272 :
    (∑ n ∈ Ico 78208 78272, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 78208 78272, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 78208 78272, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (61 : ℤ) ∧
    (∑ n ∈ Ico 78208 78272, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1192866887083982263343798 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_78272_78336 :
    (∑ n ∈ Ico 78272 78336, mobiusTreeValue 16 mobiusTable1200001 n) = (-3 : ℤ) ∧
    (∑ n ∈ Ico 78272 78336, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 78272 78336, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-191704 : ℤ) ∧
    (∑ n ∈ Ico 78272 78336, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-3834059989646591863775322681 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_78208_78336 :
    (∑ n ∈ Ico 78208 78336, mobiusTreeValue 16 mobiusTable1200001 n) = (-3 : ℤ) ∧
    (∑ n ∈ Ico 78208 78336, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (75 : ℕ) ∧
    (∑ n ∈ Ico 78208 78336, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-191643 : ℤ) ∧
    (∑ n ∈ Ico 78208 78336, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-3832867122759507881511978883 : ℤ) := by
  rcases cdemPrefixStats_78208_78272 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_78272_78336 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 78208 ≤ 78272) (by norm_num : 78272 ≤ 78336), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 78208 ≤ 78272) (by norm_num : 78272 ≤ 78336), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 78208 ≤ 78272) (by norm_num : 78272 ≤ 78336), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 78208 ≤ 78272) (by norm_num : 78272 ≤ 78336), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_78080_78336 :
    (∑ n ∈ Ico 78080 78336, mobiusTreeValue 16 mobiusTable1200001 n) = (6 : ℤ) ∧
    (∑ n ∈ Ico 78080 78336, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (154 : ℕ) ∧
    (∑ n ∈ Ico 78080 78336, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (384514 : ℤ) ∧
    (∑ n ∈ Ico 78080 78336, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (7690346674691154283412764177 : ℤ) := by
  rcases cdemPrefixStats_78080_78208 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_78208_78336 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 78080 ≤ 78208) (by norm_num : 78208 ≤ 78336), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 78080 ≤ 78208) (by norm_num : 78208 ≤ 78336), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 78080 ≤ 78208) (by norm_num : 78208 ≤ 78336), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 78080 ≤ 78208) (by norm_num : 78208 ≤ 78336), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_77824_78336 :
    (∑ n ∈ Ico 77824 78336, mobiusTreeValue 16 mobiusTable1200001 n) = (5 : ℤ) ∧
    (∑ n ∈ Ico 77824 78336, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (311 : ℕ) ∧
    (∑ n ∈ Ico 77824 78336, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (321560 : ℤ) ∧
    (∑ n ∈ Ico 77824 78336, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (6431203075064075887530355209 : ℤ) := by
  rcases cdemPrefixStats_77824_78080 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_78080_78336 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 77824 ≤ 78080) (by norm_num : 78080 ≤ 78336), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 77824 ≤ 78080) (by norm_num : 78080 ≤ 78336), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 77824 ≤ 78080) (by norm_num : 78080 ≤ 78336), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 77824 ≤ 78080) (by norm_num : 78080 ≤ 78336), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_78336_78400 :
    (∑ n ∈ Ico 78336 78400, mobiusTreeValue 16 mobiusTable1200001 n) = (14 : ℤ) ∧
    (∑ n ∈ Ico 78336 78400, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 78336 78400, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (893181 : ℤ) ∧
    (∑ n ∈ Ico 78336 78400, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (17863735379744121137050517002 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_78400_78464 :
    (∑ n ∈ Ico 78400 78464, mobiusTreeValue 16 mobiusTable1200001 n) = (2 : ℤ) ∧
    (∑ n ∈ Ico 78400 78464, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 78400 78464, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (127355 : ℤ) ∧
    (∑ n ∈ Ico 78400 78464, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (2547134933179032135298200008 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_78336_78464 :
    (∑ n ∈ Ico 78336 78464, mobiusTreeValue 16 mobiusTable1200001 n) = (16 : ℤ) ∧
    (∑ n ∈ Ico 78336 78464, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 78336 78464, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (1020536 : ℤ) ∧
    (∑ n ∈ Ico 78336 78464, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (20410870312923153272348717010 : ℤ) := by
  rcases cdemPrefixStats_78336_78400 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_78400_78464 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 78336 ≤ 78400) (by norm_num : 78400 ≤ 78464), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 78336 ≤ 78400) (by norm_num : 78400 ≤ 78464), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 78336 ≤ 78400) (by norm_num : 78400 ≤ 78464), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 78336 ≤ 78400) (by norm_num : 78400 ≤ 78464), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_78464_78528 :
    (∑ n ∈ Ico 78464 78528, mobiusTreeValue 16 mobiusTable1200001 n) = (2 : ℤ) ∧
    (∑ n ∈ Ico 78464 78528, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (42 : ℕ) ∧
    (∑ n ∈ Ico 78464 78528, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (127406 : ℤ) ∧
    (∑ n ∈ Ico 78464 78528, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (2548144258564579264336490164 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_78528_78592 :
    (∑ n ∈ Ico 78528 78592, mobiusTreeValue 16 mobiusTable1200001 n) = (-12 : ℤ) ∧
    (∑ n ∈ Ico 78528 78592, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 78528 78592, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-763909 : ℤ) ∧
    (∑ n ∈ Ico 78528 78592, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-15278303598161571186856203061 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_78464_78592 :
    (∑ n ∈ Ico 78464 78592, mobiusTreeValue 16 mobiusTable1200001 n) = (-10 : ℤ) ∧
    (∑ n ∈ Ico 78464 78592, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (80 : ℕ) ∧
    (∑ n ∈ Ico 78464 78592, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-636503 : ℤ) ∧
    (∑ n ∈ Ico 78464 78592, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-12730159339596991922519712897 : ℤ) := by
  rcases cdemPrefixStats_78464_78528 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_78528_78592 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 78464 ≤ 78528) (by norm_num : 78528 ≤ 78592), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 78464 ≤ 78528) (by norm_num : 78528 ≤ 78592), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 78464 ≤ 78528) (by norm_num : 78528 ≤ 78592), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 78464 ≤ 78528) (by norm_num : 78528 ≤ 78592), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_78336_78592 :
    (∑ n ∈ Ico 78336 78592, mobiusTreeValue 16 mobiusTable1200001 n) = (6 : ℤ) ∧
    (∑ n ∈ Ico 78336 78592, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (158 : ℕ) ∧
    (∑ n ∈ Ico 78336 78592, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (384033 : ℤ) ∧
    (∑ n ∈ Ico 78336 78592, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (7680710973326161349829004113 : ℤ) := by
  rcases cdemPrefixStats_78336_78464 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_78464_78592 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 78336 ≤ 78464) (by norm_num : 78464 ≤ 78592), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 78336 ≤ 78464) (by norm_num : 78464 ≤ 78592), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 78336 ≤ 78464) (by norm_num : 78464 ≤ 78592), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 78336 ≤ 78464) (by norm_num : 78464 ≤ 78592), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_78592_78656 :
    (∑ n ∈ Ico 78592 78656, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 78592 78656, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 78592 78656, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-63588 : ℤ) ∧
    (∑ n ∈ Ico 78592 78656, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-1271747452158940898473196563 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_78656_78720 :
    (∑ n ∈ Ico 78656 78720, mobiusTreeValue 16 mobiusTable1200001 n) = (6 : ℤ) ∧
    (∑ n ∈ Ico 78656 78720, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 78656 78720, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (381124 : ℤ) ∧
    (∑ n ∈ Ico 78656 78720, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (7622596226239762231411697766 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_78592_78720 :
    (∑ n ∈ Ico 78592 78720, mobiusTreeValue 16 mobiusTable1200001 n) = (5 : ℤ) ∧
    (∑ n ∈ Ico 78592 78720, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (79 : ℕ) ∧
    (∑ n ∈ Ico 78592 78720, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (317536 : ℤ) ∧
    (∑ n ∈ Ico 78592 78720, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (6350848774080821332938501203 : ℤ) := by
  rcases cdemPrefixStats_78592_78656 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_78656_78720 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 78592 ≤ 78656) (by norm_num : 78656 ≤ 78720), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 78592 ≤ 78656) (by norm_num : 78656 ≤ 78720), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 78592 ≤ 78656) (by norm_num : 78656 ≤ 78720), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 78592 ≤ 78656) (by norm_num : 78656 ≤ 78720), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_78720_78784 :
    (∑ n ∈ Ico 78720 78784, mobiusTreeValue 16 mobiusTable1200001 n) = (8 : ℤ) ∧
    (∑ n ∈ Ico 78720 78784, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 78720 78784, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (507912 : ℤ) ∧
    (∑ n ∈ Ico 78720 78784, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (10158375170138132635716213854 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_78784_78848 :
    (∑ n ∈ Ico 78784 78848, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 78784 78848, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 78784 78848, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (63414 : ℤ) ∧
    (∑ n ∈ Ico 78784 78848, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1268294786701534340205859374 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_78720_78848 :
    (∑ n ∈ Ico 78720 78848, mobiusTreeValue 16 mobiusTable1200001 n) = (9 : ℤ) ∧
    (∑ n ∈ Ico 78720 78848, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 78720 78848, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (571326 : ℤ) ∧
    (∑ n ∈ Ico 78720 78848, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (11426669956839666975922073228 : ℤ) := by
  rcases cdemPrefixStats_78720_78784 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_78784_78848 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 78720 ≤ 78784) (by norm_num : 78784 ≤ 78848), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 78720 ≤ 78784) (by norm_num : 78784 ≤ 78848), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 78720 ≤ 78784) (by norm_num : 78784 ≤ 78848), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 78720 ≤ 78784) (by norm_num : 78784 ≤ 78848), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_78592_78848 :
    (∑ n ∈ Ico 78592 78848, mobiusTreeValue 16 mobiusTable1200001 n) = (14 : ℤ) ∧
    (∑ n ∈ Ico 78592 78848, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (156 : ℕ) ∧
    (∑ n ∈ Ico 78592 78848, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (888862 : ℤ) ∧
    (∑ n ∈ Ico 78592 78848, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (17777518730920488308860574431 : ℤ) := by
  rcases cdemPrefixStats_78592_78720 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_78720_78848 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 78592 ≤ 78720) (by norm_num : 78720 ≤ 78848), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 78592 ≤ 78720) (by norm_num : 78720 ≤ 78848), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 78592 ≤ 78720) (by norm_num : 78720 ≤ 78848), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 78592 ≤ 78720) (by norm_num : 78720 ≤ 78848), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_78336_78848 :
    (∑ n ∈ Ico 78336 78848, mobiusTreeValue 16 mobiusTable1200001 n) = (20 : ℤ) ∧
    (∑ n ∈ Ico 78336 78848, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (314 : ℕ) ∧
    (∑ n ∈ Ico 78336 78848, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (1272895 : ℤ) ∧
    (∑ n ∈ Ico 78336 78848, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (25458229704246649658689578544 : ℤ) := by
  rcases cdemPrefixStats_78336_78592 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_78592_78848 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 78336 ≤ 78592) (by norm_num : 78592 ≤ 78848), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 78336 ≤ 78592) (by norm_num : 78592 ≤ 78848), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 78336 ≤ 78592) (by norm_num : 78592 ≤ 78848), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 78336 ≤ 78592) (by norm_num : 78592 ≤ 78848), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_77824_78848 :
    (∑ n ∈ Ico 77824 78848, mobiusTreeValue 16 mobiusTable1200001 n) = (25 : ℤ) ∧
    (∑ n ∈ Ico 77824 78848, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (625 : ℕ) ∧
    (∑ n ∈ Ico 77824 78848, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (1594455 : ℤ) ∧
    (∑ n ∈ Ico 77824 78848, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (31889432779310725546219933753 : ℤ) := by
  rcases cdemPrefixStats_77824_78336 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_78336_78848 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 77824 ≤ 78336) (by norm_num : 78336 ≤ 78848), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 77824 ≤ 78336) (by norm_num : 78336 ≤ 78848), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 77824 ≤ 78336) (by norm_num : 78336 ≤ 78848), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 77824 ≤ 78336) (by norm_num : 78336 ≤ 78848), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_78848_78912 :
    (∑ n ∈ Ico 78848 78912, mobiusTreeValue 16 mobiusTable1200001 n) = (-8 : ℤ) ∧
    (∑ n ∈ Ico 78848 78912, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 78848 78912, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-507118 : ℤ) ∧
    (∑ n ∈ Ico 78848 78912, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-10142437986499069616874574929 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_78912_78976 :
    (∑ n ∈ Ico 78912 78976, mobiusTreeValue 16 mobiusTable1200001 n) = (8 : ℤ) ∧
    (∑ n ∈ Ico 78912 78976, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 78912 78976, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (506688 : ℤ) ∧
    (∑ n ∈ Ico 78912 78976, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (10133846176061284050981446778 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_78848_78976 :
    (∑ n ∈ Ico 78848 78976, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 78848 78976, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (76 : ℕ) ∧
    (∑ n ∈ Ico 78848 78976, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-430 : ℤ) ∧
    (∑ n ∈ Ico 78848 78976, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-8591810437785565893128151 : ℤ) := by
  rcases cdemPrefixStats_78848_78912 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_78912_78976 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 78848 ≤ 78912) (by norm_num : 78912 ≤ 78976), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 78848 ≤ 78912) (by norm_num : 78912 ≤ 78976), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 78848 ≤ 78912) (by norm_num : 78912 ≤ 78976), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 78848 ≤ 78912) (by norm_num : 78912 ≤ 78976), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_78976_79040 :
    (∑ n ∈ Ico 78976 79040, mobiusTreeValue 16 mobiusTable1200001 n) = (7 : ℤ) ∧
    (∑ n ∈ Ico 78976 79040, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 78976 79040, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (442856 : ℤ) ∧
    (∑ n ∈ Ico 78976 79040, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (8857154522088721302057719960 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_79040_79104 :
    (∑ n ∈ Ico 79040 79104, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 79040 79104, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 79040 79104, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (7 : ℤ) ∧
    (∑ n ∈ Ico 79040 79104, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (127906873588041206832625 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_78976_79104 :
    (∑ n ∈ Ico 78976 79104, mobiusTreeValue 16 mobiusTable1200001 n) = (7 : ℤ) ∧
    (∑ n ∈ Ico 78976 79104, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 78976 79104, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (442863 : ℤ) ∧
    (∑ n ∈ Ico 78976 79104, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (8857282428962309343264552585 : ℤ) := by
  rcases cdemPrefixStats_78976_79040 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_79040_79104 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 78976 ≤ 79040) (by norm_num : 79040 ≤ 79104), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 78976 ≤ 79040) (by norm_num : 79040 ≤ 79104), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 78976 ≤ 79040) (by norm_num : 79040 ≤ 79104), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 78976 ≤ 79040) (by norm_num : 79040 ≤ 79104), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_78848_79104 :
    (∑ n ∈ Ico 78848 79104, mobiusTreeValue 16 mobiusTable1200001 n) = (7 : ℤ) ∧
    (∑ n ∈ Ico 78848 79104, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (153 : ℕ) ∧
    (∑ n ∈ Ico 78848 79104, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (442433 : ℤ) ∧
    (∑ n ∈ Ico 78848 79104, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (8848690618524523777371424434 : ℤ) := by
  rcases cdemPrefixStats_78848_78976 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_78976_79104 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 78848 ≤ 78976) (by norm_num : 78976 ≤ 79104), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 78848 ≤ 78976) (by norm_num : 78976 ≤ 79104), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 78848 ≤ 78976) (by norm_num : 78976 ≤ 79104), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 78848 ≤ 78976) (by norm_num : 78976 ≤ 79104), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_79104_79168 :
    (∑ n ∈ Ico 79104 79168, mobiusTreeValue 16 mobiusTable1200001 n) = (-5 : ℤ) ∧
    (∑ n ∈ Ico 79104 79168, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 79104 79168, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-315829 : ℤ) ∧
    (∑ n ∈ Ico 79104 79168, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-6316593129383192297360647208 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_79168_79232 :
    (∑ n ∈ Ico 79168 79232, mobiusTreeValue 16 mobiusTable1200001 n) = (3 : ℤ) ∧
    (∑ n ∈ Ico 79168 79232, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 79168 79232, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (189451 : ℤ) ∧
    (∑ n ∈ Ico 79168 79232, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (3789058838065581047102650421 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_79104_79232 :
    (∑ n ∈ Ico 79104 79232, mobiusTreeValue 16 mobiusTable1200001 n) = (-2 : ℤ) ∧
    (∑ n ∈ Ico 79104 79232, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (76 : ℕ) ∧
    (∑ n ∈ Ico 79104 79232, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-126378 : ℤ) ∧
    (∑ n ∈ Ico 79104 79232, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-2527534291317611250257996787 : ℤ) := by
  rcases cdemPrefixStats_79104_79168 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_79168_79232 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 79104 ≤ 79168) (by norm_num : 79168 ≤ 79232), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 79104 ≤ 79168) (by norm_num : 79168 ≤ 79232), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 79104 ≤ 79168) (by norm_num : 79168 ≤ 79232), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 79104 ≤ 79168) (by norm_num : 79168 ≤ 79232), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_79232_79296 :
    (∑ n ∈ Ico 79232 79296, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 79232 79296, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 79232 79296, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (63098 : ℤ) ∧
    (∑ n ∈ Ico 79232 79296, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1262004793461023513774059934 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_79296_79360 :
    (∑ n ∈ Ico 79296 79360, mobiusTreeValue 16 mobiusTable1200001 n) = (-8 : ℤ) ∧
    (∑ n ∈ Ico 79296 79360, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 79296 79360, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-504186 : ℤ) ∧
    (∑ n ∈ Ico 79296 79360, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-10083854087686758402110217738 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_79232_79360 :
    (∑ n ∈ Ico 79232 79360, mobiusTreeValue 16 mobiusTable1200001 n) = (-7 : ℤ) ∧
    (∑ n ∈ Ico 79232 79360, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 79232 79360, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-441088 : ℤ) ∧
    (∑ n ∈ Ico 79232 79360, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-8821849294225734888336157804 : ℤ) := by
  rcases cdemPrefixStats_79232_79296 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_79296_79360 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 79232 ≤ 79296) (by norm_num : 79296 ≤ 79360), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 79232 ≤ 79296) (by norm_num : 79296 ≤ 79360), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 79232 ≤ 79296) (by norm_num : 79296 ≤ 79360), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 79232 ≤ 79296) (by norm_num : 79296 ≤ 79360), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_79104_79360 :
    (∑ n ∈ Ico 79104 79360, mobiusTreeValue 16 mobiusTable1200001 n) = (-9 : ℤ) ∧
    (∑ n ∈ Ico 79104 79360, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (153 : ℕ) ∧
    (∑ n ∈ Ico 79104 79360, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-567466 : ℤ) ∧
    (∑ n ∈ Ico 79104 79360, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-11349383585543346138594154591 : ℤ) := by
  rcases cdemPrefixStats_79104_79232 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_79232_79360 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 79104 ≤ 79232) (by norm_num : 79232 ≤ 79360), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 79104 ≤ 79232) (by norm_num : 79232 ≤ 79360), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 79104 ≤ 79232) (by norm_num : 79232 ≤ 79360), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 79104 ≤ 79232) (by norm_num : 79232 ≤ 79360), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_78848_79360 :
    (∑ n ∈ Ico 78848 79360, mobiusTreeValue 16 mobiusTable1200001 n) = (-2 : ℤ) ∧
    (∑ n ∈ Ico 78848 79360, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (306 : ℕ) ∧
    (∑ n ∈ Ico 78848 79360, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-125033 : ℤ) ∧
    (∑ n ∈ Ico 78848 79360, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-2500692967018822361222730157 : ℤ) := by
  rcases cdemPrefixStats_78848_79104 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_79104_79360 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 78848 ≤ 79104) (by norm_num : 79104 ≤ 79360), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 78848 ≤ 79104) (by norm_num : 79104 ≤ 79360), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 78848 ≤ 79104) (by norm_num : 79104 ≤ 79360), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 78848 ≤ 79104) (by norm_num : 79104 ≤ 79360), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_79360_79424 :
    (∑ n ∈ Ico 79360 79424, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 79360 79424, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 79360 79424, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-62921 : ℤ) ∧
    (∑ n ∈ Ico 79360 79424, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-1258462643078996753364171923 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_79424_79488 :
    (∑ n ∈ Ico 79424 79488, mobiusTreeValue 16 mobiusTable1200001 n) = (3 : ℤ) ∧
    (∑ n ∈ Ico 79424 79488, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 79424 79488, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (188753 : ℤ) ∧
    (∑ n ∈ Ico 79424 79488, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (3775104520968990111129037359 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_79360_79488 :
    (∑ n ∈ Ico 79360 79488, mobiusTreeValue 16 mobiusTable1200001 n) = (2 : ℤ) ∧
    (∑ n ∈ Ico 79360 79488, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 79360 79488, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (125832 : ℤ) ∧
    (∑ n ∈ Ico 79360 79488, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (2516641877889993357764865436 : ℤ) := by
  rcases cdemPrefixStats_79360_79424 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_79424_79488 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 79360 ≤ 79424) (by norm_num : 79424 ≤ 79488), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 79360 ≤ 79424) (by norm_num : 79424 ≤ 79488), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 79360 ≤ 79424) (by norm_num : 79424 ≤ 79488), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 79360 ≤ 79424) (by norm_num : 79424 ≤ 79488), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_79488_79552 :
    (∑ n ∈ Ico 79488 79552, mobiusTreeValue 16 mobiusTable1200001 n) = (-4 : ℤ) ∧
    (∑ n ∈ Ico 79488 79552, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 79488 79552, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-251453 : ℤ) ∧
    (∑ n ∈ Ico 79488 79552, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-5029153813031675239555926944 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_79552_79616 :
    (∑ n ∈ Ico 79552 79616, mobiusTreeValue 16 mobiusTable1200001 n) = (-9 : ℤ) ∧
    (∑ n ∈ Ico 79552 79616, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 79552 79616, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-565514 : ℤ) ∧
    (∑ n ∈ Ico 79552 79616, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-11310369475860459394567861532 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_79488_79616 :
    (∑ n ∈ Ico 79488 79616, mobiusTreeValue 16 mobiusTable1200001 n) = (-13 : ℤ) ∧
    (∑ n ∈ Ico 79488 79616, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (79 : ℕ) ∧
    (∑ n ∈ Ico 79488 79616, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-816967 : ℤ) ∧
    (∑ n ∈ Ico 79488 79616, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-16339523288892134634123788476 : ℤ) := by
  rcases cdemPrefixStats_79488_79552 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_79552_79616 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 79488 ≤ 79552) (by norm_num : 79552 ≤ 79616), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 79488 ≤ 79552) (by norm_num : 79552 ≤ 79616), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 79488 ≤ 79552) (by norm_num : 79552 ≤ 79616), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 79488 ≤ 79552) (by norm_num : 79552 ≤ 79616), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_79360_79616 :
    (∑ n ∈ Ico 79360 79616, mobiusTreeValue 16 mobiusTable1200001 n) = (-11 : ℤ) ∧
    (∑ n ∈ Ico 79360 79616, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (157 : ℕ) ∧
    (∑ n ∈ Ico 79360 79616, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-691135 : ℤ) ∧
    (∑ n ∈ Ico 79360 79616, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-13822881411002141276358923040 : ℤ) := by
  rcases cdemPrefixStats_79360_79488 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_79488_79616 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 79360 ≤ 79488) (by norm_num : 79488 ≤ 79616), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 79360 ≤ 79488) (by norm_num : 79488 ≤ 79616), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 79360 ≤ 79488) (by norm_num : 79488 ≤ 79616), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 79360 ≤ 79488) (by norm_num : 79488 ≤ 79616), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_79616_79680 :
    (∑ n ∈ Ico 79616 79680, mobiusTreeValue 16 mobiusTable1200001 n) = (-5 : ℤ) ∧
    (∑ n ∈ Ico 79616 79680, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 79616 79680, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-313910 : ℤ) ∧
    (∑ n ∈ Ico 79616 79680, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-6278220495771167885683884392 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_79680_79744 :
    (∑ n ∈ Ico 79680 79744, mobiusTreeValue 16 mobiusTable1200001 n) = (3 : ℤ) ∧
    (∑ n ∈ Ico 79680 79744, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 79680 79744, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (188175 : ℤ) ∧
    (∑ n ∈ Ico 79680 79744, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (3763533389722658582306462516 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_79616_79744 :
    (∑ n ∈ Ico 79616 79744, mobiusTreeValue 16 mobiusTable1200001 n) = (-2 : ℤ) ∧
    (∑ n ∈ Ico 79616 79744, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 79616 79744, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-125735 : ℤ) ∧
    (∑ n ∈ Ico 79616 79744, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-2514687106048509303377421876 : ℤ) := by
  rcases cdemPrefixStats_79616_79680 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_79680_79744 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 79616 ≤ 79680) (by norm_num : 79680 ≤ 79744), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 79616 ≤ 79680) (by norm_num : 79680 ≤ 79744), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 79616 ≤ 79680) (by norm_num : 79680 ≤ 79744), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 79616 ≤ 79680) (by norm_num : 79680 ≤ 79744), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_79744_79808 :
    (∑ n ∈ Ico 79744 79808, mobiusTreeValue 16 mobiusTable1200001 n) = (10 : ℤ) ∧
    (∑ n ∈ Ico 79744 79808, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 79744 79808, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (626757 : ℤ) ∧
    (∑ n ∈ Ico 79744 79808, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (12535208470733725011077455709 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_79808_79872 :
    (∑ n ∈ Ico 79808 79872, mobiusTreeValue 16 mobiusTable1200001 n) = (-6 : ℤ) ∧
    (∑ n ∈ Ico 79808 79872, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 79808 79872, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-375739 : ℤ) ∧
    (∑ n ∈ Ico 79808 79872, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-7514842697117943023474802985 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_79744_79872 :
    (∑ n ∈ Ico 79744 79872, mobiusTreeValue 16 mobiusTable1200001 n) = (4 : ℤ) ∧
    (∑ n ∈ Ico 79744 79872, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 79744 79872, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (251018 : ℤ) ∧
    (∑ n ∈ Ico 79744 79872, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (5020365773615781987602652724 : ℤ) := by
  rcases cdemPrefixStats_79744_79808 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_79808_79872 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 79744 ≤ 79808) (by norm_num : 79808 ≤ 79872), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 79744 ≤ 79808) (by norm_num : 79808 ≤ 79872), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 79744 ≤ 79808) (by norm_num : 79808 ≤ 79872), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 79744 ≤ 79808) (by norm_num : 79808 ≤ 79872), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_79616_79872 :
    (∑ n ∈ Ico 79616 79872, mobiusTreeValue 16 mobiusTable1200001 n) = (2 : ℤ) ∧
    (∑ n ∈ Ico 79616 79872, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (156 : ℕ) ∧
    (∑ n ∈ Ico 79616 79872, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (125283 : ℤ) ∧
    (∑ n ∈ Ico 79616 79872, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (2505678667567272684225230848 : ℤ) := by
  rcases cdemPrefixStats_79616_79744 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_79744_79872 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 79616 ≤ 79744) (by norm_num : 79744 ≤ 79872), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 79616 ≤ 79744) (by norm_num : 79744 ≤ 79872), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 79616 ≤ 79744) (by norm_num : 79744 ≤ 79872), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 79616 ≤ 79744) (by norm_num : 79744 ≤ 79872), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_79360_79872 :
    (∑ n ∈ Ico 79360 79872, mobiusTreeValue 16 mobiusTable1200001 n) = (-9 : ℤ) ∧
    (∑ n ∈ Ico 79360 79872, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (313 : ℕ) ∧
    (∑ n ∈ Ico 79360 79872, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-565852 : ℤ) ∧
    (∑ n ∈ Ico 79360 79872, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-11317202743434868592133692192 : ℤ) := by
  rcases cdemPrefixStats_79360_79616 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_79616_79872 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 79360 ≤ 79616) (by norm_num : 79616 ≤ 79872), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 79360 ≤ 79616) (by norm_num : 79616 ≤ 79872), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 79360 ≤ 79616) (by norm_num : 79616 ≤ 79872), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 79360 ≤ 79616) (by norm_num : 79616 ≤ 79872), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_78848_79872 :
    (∑ n ∈ Ico 78848 79872, mobiusTreeValue 16 mobiusTable1200001 n) = (-11 : ℤ) ∧
    (∑ n ∈ Ico 78848 79872, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (619 : ℕ) ∧
    (∑ n ∈ Ico 78848 79872, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-690885 : ℤ) ∧
    (∑ n ∈ Ico 78848 79872, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-13817895710453690953356422349 : ℤ) := by
  rcases cdemPrefixStats_78848_79360 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_79360_79872 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 78848 ≤ 79360) (by norm_num : 79360 ≤ 79872), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 78848 ≤ 79360) (by norm_num : 79360 ≤ 79872), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 78848 ≤ 79360) (by norm_num : 79360 ≤ 79872), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 78848 ≤ 79360) (by norm_num : 79360 ≤ 79872), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_77824_79872 :
    (∑ n ∈ Ico 77824 79872, mobiusTreeValue 16 mobiusTable1200001 n) = (14 : ℤ) ∧
    (∑ n ∈ Ico 77824 79872, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (1244 : ℕ) ∧
    (∑ n ∈ Ico 77824 79872, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (903570 : ℤ) ∧
    (∑ n ∈ Ico 77824 79872, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (18071537068857034592863511404 : ℤ) := by
  rcases cdemPrefixStats_77824_78848 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_78848_79872 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 77824 ≤ 78848) (by norm_num : 78848 ≤ 79872), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 77824 ≤ 78848) (by norm_num : 78848 ≤ 79872), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 77824 ≤ 78848) (by norm_num : 78848 ≤ 79872), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 77824 ≤ 78848) (by norm_num : 78848 ≤ 79872), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_79872_79936 :
    (∑ n ∈ Ico 79872 79936, mobiusTreeValue 16 mobiusTable1200001 n) = (-4 : ℤ) ∧
    (∑ n ∈ Ico 79872 79936, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 79872 79936, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-250323 : ℤ) ∧
    (∑ n ∈ Ico 79872 79936, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-5006587339301016440906826776 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_79936_80000 :
    (∑ n ∈ Ico 79936 80000, mobiusTreeValue 16 mobiusTable1200001 n) = (3 : ℤ) ∧
    (∑ n ∈ Ico 79936 80000, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 79936 80000, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (187562 : ℤ) ∧
    (∑ n ∈ Ico 79936 80000, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (3751219073827015864233602445 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_79872_80000 :
    (∑ n ∈ Ico 79872 80000, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 79872 80000, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 79872 80000, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-62761 : ℤ) ∧
    (∑ n ∈ Ico 79872 80000, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-1255368265474000576673224331 : ℤ) := by
  rcases cdemPrefixStats_79872_79936 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_79936_80000 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 79872 ≤ 79936) (by norm_num : 79936 ≤ 80000), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 79872 ≤ 79936) (by norm_num : 79936 ≤ 80000), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 79872 ≤ 79936) (by norm_num : 79936 ≤ 80000), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 79872 ≤ 79936) (by norm_num : 79936 ≤ 80000), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_80000_80064 :
    (∑ n ∈ Ico 80000 80064, mobiusTreeValue 16 mobiusTable1200001 n) = (3 : ℤ) ∧
    (∑ n ∈ Ico 80000 80064, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 80000 80064, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (187366 : ℤ) ∧
    (∑ n ∈ Ico 80000 80064, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (3747377018718955967840576899 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_80064_80128 :
    (∑ n ∈ Ico 80064 80128, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 80064 80128, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (35 : ℕ) ∧
    (∑ n ∈ Ico 80064 80128, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-62545 : ℤ) ∧
    (∑ n ∈ Ico 80064 80128, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-1250902426038439646250267988 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_80000_80128 :
    (∑ n ∈ Ico 80000 80128, mobiusTreeValue 16 mobiusTable1200001 n) = (2 : ℤ) ∧
    (∑ n ∈ Ico 80000 80128, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (72 : ℕ) ∧
    (∑ n ∈ Ico 80000 80128, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (124821 : ℤ) ∧
    (∑ n ∈ Ico 80000 80128, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (2496474592680516321590308911 : ℤ) := by
  rcases cdemPrefixStats_80000_80064 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_80064_80128 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 80000 ≤ 80064) (by norm_num : 80064 ≤ 80128), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 80000 ≤ 80064) (by norm_num : 80064 ≤ 80128), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 80000 ≤ 80064) (by norm_num : 80064 ≤ 80128), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 80000 ≤ 80064) (by norm_num : 80064 ≤ 80128), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_79872_80128 :
    (∑ n ∈ Ico 79872 80128, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 79872 80128, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (149 : ℕ) ∧
    (∑ n ∈ Ico 79872 80128, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (62060 : ℤ) ∧
    (∑ n ∈ Ico 79872 80128, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1241106327206515744917084580 : ℤ) := by
  rcases cdemPrefixStats_79872_80000 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_80000_80128 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 79872 ≤ 80000) (by norm_num : 80000 ≤ 80128), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 79872 ≤ 80000) (by norm_num : 80000 ≤ 80128), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 79872 ≤ 80000) (by norm_num : 80000 ≤ 80128), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 79872 ≤ 80000) (by norm_num : 80000 ≤ 80128), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_80128_80192 :
    (∑ n ∈ Ico 80128 80192, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 80128 80192, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 80128 80192, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (62479 : ℤ) ∧
    (∑ n ∈ Ico 80128 80192, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1249575269739867142018321497 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_80192_80256 :
    (∑ n ∈ Ico 80192 80256, mobiusTreeValue 16 mobiusTable1200001 n) = (-7 : ℤ) ∧
    (∑ n ∈ Ico 80192 80256, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 80192 80256, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-436274 : ℤ) ∧
    (∑ n ∈ Ico 80192 80256, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-8725522321130639413717436309 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_80128_80256 :
    (∑ n ∈ Ico 80128 80256, mobiusTreeValue 16 mobiusTable1200001 n) = (-6 : ℤ) ∧
    (∑ n ∈ Ico 80128 80256, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 80128 80256, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-373795 : ℤ) ∧
    (∑ n ∈ Ico 80128 80256, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-7475947051390772271699114812 : ℤ) := by
  rcases cdemPrefixStats_80128_80192 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_80192_80256 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 80128 ≤ 80192) (by norm_num : 80192 ≤ 80256), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 80128 ≤ 80192) (by norm_num : 80192 ≤ 80256), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 80128 ≤ 80192) (by norm_num : 80192 ≤ 80256), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 80128 ≤ 80192) (by norm_num : 80192 ≤ 80256), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_80256_80320 :
    (∑ n ∈ Ico 80256 80320, mobiusTreeValue 16 mobiusTable1200001 n) = (5 : ℤ) ∧
    (∑ n ∈ Ico 80256 80320, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 80256 80320, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (311424 : ℤ) ∧
    (∑ n ∈ Ico 80256 80320, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (6228557949701027424963058567 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_80320_80384 :
    (∑ n ∈ Ico 80320 80384, mobiusTreeValue 16 mobiusTable1200001 n) = (9 : ℤ) ∧
    (∑ n ∈ Ico 80320 80384, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 80320 80384, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (560053 : ℤ) ∧
    (∑ n ∈ Ico 80320 80384, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (11201135913917837108752215300 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_80256_80384 :
    (∑ n ∈ Ico 80256 80384, mobiusTreeValue 16 mobiusTable1200001 n) = (14 : ℤ) ∧
    (∑ n ∈ Ico 80256 80384, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (80 : ℕ) ∧
    (∑ n ∈ Ico 80256 80384, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (871477 : ℤ) ∧
    (∑ n ∈ Ico 80256 80384, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (17429693863618864533715273867 : ℤ) := by
  rcases cdemPrefixStats_80256_80320 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_80320_80384 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 80256 ≤ 80320) (by norm_num : 80320 ≤ 80384), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 80256 ≤ 80320) (by norm_num : 80320 ≤ 80384), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 80256 ≤ 80320) (by norm_num : 80320 ≤ 80384), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 80256 ≤ 80320) (by norm_num : 80320 ≤ 80384), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_80128_80384 :
    (∑ n ∈ Ico 80128 80384, mobiusTreeValue 16 mobiusTable1200001 n) = (8 : ℤ) ∧
    (∑ n ∈ Ico 80128 80384, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (158 : ℕ) ∧
    (∑ n ∈ Ico 80128 80384, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (497682 : ℤ) ∧
    (∑ n ∈ Ico 80128 80384, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (9953746812228092262016159055 : ℤ) := by
  rcases cdemPrefixStats_80128_80256 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_80256_80384 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 80128 ≤ 80256) (by norm_num : 80256 ≤ 80384), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 80128 ≤ 80256) (by norm_num : 80256 ≤ 80384), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 80128 ≤ 80256) (by norm_num : 80256 ≤ 80384), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 80128 ≤ 80256) (by norm_num : 80256 ≤ 80384), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_79872_80384 :
    (∑ n ∈ Ico 79872 80384, mobiusTreeValue 16 mobiusTable1200001 n) = (9 : ℤ) ∧
    (∑ n ∈ Ico 79872 80384, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (307 : ℕ) ∧
    (∑ n ∈ Ico 79872 80384, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (559742 : ℤ) ∧
    (∑ n ∈ Ico 79872 80384, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (11194853139434608006933243635 : ℤ) := by
  rcases cdemPrefixStats_79872_80128 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_80128_80384 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 79872 ≤ 80128) (by norm_num : 80128 ≤ 80384), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 79872 ≤ 80128) (by norm_num : 80128 ≤ 80384), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 79872 ≤ 80128) (by norm_num : 80128 ≤ 80384), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 79872 ≤ 80128) (by norm_num : 80128 ≤ 80384), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_80384_80448 :
    (∑ n ∈ Ico 80384 80448, mobiusTreeValue 16 mobiusTable1200001 n) = (-3 : ℤ) ∧
    (∑ n ∈ Ico 80384 80448, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 80384 80448, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-186588 : ℤ) ∧
    (∑ n ∈ Ico 80384 80448, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-3731791510499862411048132514 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_80448_80512 :
    (∑ n ∈ Ico 80448 80512, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 80448 80512, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 80448 80512, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (62199 : ℤ) ∧
    (∑ n ∈ Ico 80448 80512, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1243965124157298864949659504 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_80384_80512 :
    (∑ n ∈ Ico 80384 80512, mobiusTreeValue 16 mobiusTable1200001 n) = (-2 : ℤ) ∧
    (∑ n ∈ Ico 80384 80512, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 80384 80512, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-124389 : ℤ) ∧
    (∑ n ∈ Ico 80384 80512, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-2487826386342563546098473010 : ℤ) := by
  rcases cdemPrefixStats_80384_80448 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_80448_80512 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 80384 ≤ 80448) (by norm_num : 80448 ≤ 80512), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 80384 ≤ 80448) (by norm_num : 80448 ≤ 80512), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 80384 ≤ 80448) (by norm_num : 80448 ≤ 80512), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 80384 ≤ 80448) (by norm_num : 80448 ≤ 80512), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_80512_80576 :
    (∑ n ∈ Ico 80512 80576, mobiusTreeValue 16 mobiusTable1200001 n) = (5 : ℤ) ∧
    (∑ n ∈ Ico 80512 80576, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 80512 80576, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (310353 : ℤ) ∧
    (∑ n ∈ Ico 80512 80576, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (6207124636325051346495518380 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_80576_80640 :
    (∑ n ∈ Ico 80576 80640, mobiusTreeValue 16 mobiusTable1200001 n) = (-2 : ℤ) ∧
    (∑ n ∈ Ico 80576 80640, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 80576 80640, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-124126 : ℤ) ∧
    (∑ n ∈ Ico 80576 80640, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-2482527530149351613839500889 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_80512_80640 :
    (∑ n ∈ Ico 80512 80640, mobiusTreeValue 16 mobiusTable1200001 n) = (3 : ℤ) ∧
    (∑ n ∈ Ico 80512 80640, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (81 : ℕ) ∧
    (∑ n ∈ Ico 80512 80640, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (186227 : ℤ) ∧
    (∑ n ∈ Ico 80512 80640, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (3724597106175699732656017491 : ℤ) := by
  rcases cdemPrefixStats_80512_80576 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_80576_80640 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 80512 ≤ 80576) (by norm_num : 80576 ≤ 80640), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 80512 ≤ 80576) (by norm_num : 80576 ≤ 80640), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 80512 ≤ 80576) (by norm_num : 80576 ≤ 80640), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 80512 ≤ 80576) (by norm_num : 80576 ≤ 80640), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_80384_80640 :
    (∑ n ∈ Ico 80384 80640, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 80384 80640, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (159 : ℕ) ∧
    (∑ n ∈ Ico 80384 80640, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (61838 : ℤ) ∧
    (∑ n ∈ Ico 80384 80640, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1236770719833136186557544481 : ℤ) := by
  rcases cdemPrefixStats_80384_80512 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_80512_80640 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 80384 ≤ 80512) (by norm_num : 80512 ≤ 80640), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 80384 ≤ 80512) (by norm_num : 80512 ≤ 80640), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 80384 ≤ 80512) (by norm_num : 80512 ≤ 80640), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 80384 ≤ 80512) (by norm_num : 80512 ≤ 80640), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_80640_80704 :
    (∑ n ∈ Ico 80640 80704, mobiusTreeValue 16 mobiusTable1200001 n) = (-4 : ℤ) ∧
    (∑ n ∈ Ico 80640 80704, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 80640 80704, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-247828 : ℤ) ∧
    (∑ n ∈ Ico 80640 80704, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-4956567942465481111046481676 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_80704_80768 :
    (∑ n ∈ Ico 80704 80768, mobiusTreeValue 16 mobiusTable1200001 n) = (-6 : ℤ) ∧
    (∑ n ∈ Ico 80704 80768, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 80704 80768, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-371465 : ℤ) ∧
    (∑ n ∈ Ico 80704 80768, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-7429373777294023903718618793 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_80640_80768 :
    (∑ n ∈ Ico 80640 80768, mobiusTreeValue 16 mobiusTable1200001 n) = (-10 : ℤ) ∧
    (∑ n ∈ Ico 80640 80768, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 80640 80768, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-619293 : ℤ) ∧
    (∑ n ∈ Ico 80640 80768, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-12385941719759505014765100469 : ℤ) := by
  rcases cdemPrefixStats_80640_80704 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_80704_80768 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 80640 ≤ 80704) (by norm_num : 80704 ≤ 80768), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 80640 ≤ 80704) (by norm_num : 80704 ≤ 80768), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 80640 ≤ 80704) (by norm_num : 80704 ≤ 80768), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 80640 ≤ 80704) (by norm_num : 80704 ≤ 80768), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_80768_80832 :
    (∑ n ∈ Ico 80768 80832, mobiusTreeValue 16 mobiusTable1200001 n) = (-5 : ℤ) ∧
    (∑ n ∈ Ico 80768 80832, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 80768 80832, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-309429 : ℤ) ∧
    (∑ n ∈ Ico 80768 80832, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-6188685384239597316668384283 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_80832_80896 :
    (∑ n ∈ Ico 80832 80896, mobiusTreeValue 16 mobiusTable1200001 n) = (7 : ℤ) ∧
    (∑ n ∈ Ico 80832 80896, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 80832 80896, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (432932 : ℤ) ∧
    (∑ n ∈ Ico 80832 80896, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (8658742505412622731170796955 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_80768_80896 :
    (∑ n ∈ Ico 80768 80896, mobiusTreeValue 16 mobiusTable1200001 n) = (2 : ℤ) ∧
    (∑ n ∈ Ico 80768 80896, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (80 : ℕ) ∧
    (∑ n ∈ Ico 80768 80896, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (123503 : ℤ) ∧
    (∑ n ∈ Ico 80768 80896, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (2470057121173025414502412672 : ℤ) := by
  rcases cdemPrefixStats_80768_80832 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_80832_80896 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 80768 ≤ 80832) (by norm_num : 80832 ≤ 80896), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 80768 ≤ 80832) (by norm_num : 80832 ≤ 80896), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 80768 ≤ 80832) (by norm_num : 80832 ≤ 80896), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 80768 ≤ 80832) (by norm_num : 80832 ≤ 80896), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_80640_80896 :
    (∑ n ∈ Ico 80640 80896, mobiusTreeValue 16 mobiusTable1200001 n) = (-8 : ℤ) ∧
    (∑ n ∈ Ico 80640 80896, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (158 : ℕ) ∧
    (∑ n ∈ Ico 80640 80896, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-495790 : ℤ) ∧
    (∑ n ∈ Ico 80640 80896, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-9915884598586479600262687797 : ℤ) := by
  rcases cdemPrefixStats_80640_80768 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_80768_80896 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 80640 ≤ 80768) (by norm_num : 80768 ≤ 80896), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 80640 ≤ 80768) (by norm_num : 80768 ≤ 80896), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 80640 ≤ 80768) (by norm_num : 80768 ≤ 80896), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 80640 ≤ 80768) (by norm_num : 80768 ≤ 80896), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_80384_80896 :
    (∑ n ∈ Ico 80384 80896, mobiusTreeValue 16 mobiusTable1200001 n) = (-7 : ℤ) ∧
    (∑ n ∈ Ico 80384 80896, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (317 : ℕ) ∧
    (∑ n ∈ Ico 80384 80896, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-433952 : ℤ) ∧
    (∑ n ∈ Ico 80384 80896, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-8679113878753343413705143316 : ℤ) := by
  rcases cdemPrefixStats_80384_80640 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_80640_80896 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 80384 ≤ 80640) (by norm_num : 80640 ≤ 80896), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 80384 ≤ 80640) (by norm_num : 80640 ≤ 80896), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 80384 ≤ 80640) (by norm_num : 80640 ≤ 80896), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 80384 ≤ 80640) (by norm_num : 80640 ≤ 80896), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_79872_80896 :
    (∑ n ∈ Ico 79872 80896, mobiusTreeValue 16 mobiusTable1200001 n) = (2 : ℤ) ∧
    (∑ n ∈ Ico 79872 80896, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (624 : ℕ) ∧
    (∑ n ∈ Ico 79872 80896, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (125790 : ℤ) ∧
    (∑ n ∈ Ico 79872 80896, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (2515739260681264593228100319 : ℤ) := by
  rcases cdemPrefixStats_79872_80384 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_80384_80896 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 79872 ≤ 80384) (by norm_num : 80384 ≤ 80896), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 79872 ≤ 80384) (by norm_num : 80384 ≤ 80896), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 79872 ≤ 80384) (by norm_num : 80384 ≤ 80896), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 79872 ≤ 80384) (by norm_num : 80384 ≤ 80896), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_80896_80960 :
    (∑ n ∈ Ico 80896 80960, mobiusTreeValue 16 mobiusTable1200001 n) = (-7 : ℤ) ∧
    (∑ n ∈ Ico 80896 80960, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 80896 80960, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-432657 : ℤ) ∧
    (∑ n ∈ Ico 80896 80960, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-8653175704168570880859000738 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_80960_81024 :
    (∑ n ∈ Ico 80960 81024, mobiusTreeValue 16 mobiusTable1200001 n) = (-7 : ℤ) ∧
    (∑ n ∈ Ico 80960 81024, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 80960 81024, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-432021 : ℤ) ∧
    (∑ n ∈ Ico 80960 81024, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-8640527709089593482399365469 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_80896_81024 :
    (∑ n ∈ Ico 80896 81024, mobiusTreeValue 16 mobiusTable1200001 n) = (-14 : ℤ) ∧
    (∑ n ∈ Ico 80896 81024, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 80896 81024, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-864678 : ℤ) ∧
    (∑ n ∈ Ico 80896 81024, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-17293703413258164363258366207 : ℤ) := by
  rcases cdemPrefixStats_80896_80960 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_80960_81024 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 80896 ≤ 80960) (by norm_num : 80960 ≤ 81024), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 80896 ≤ 80960) (by norm_num : 80960 ≤ 81024), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 80896 ≤ 80960) (by norm_num : 80960 ≤ 81024), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 80896 ≤ 80960) (by norm_num : 80960 ≤ 81024), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_81024_81088 :
    (∑ n ∈ Ico 81024 81088, mobiusTreeValue 16 mobiusTable1200001 n) = (-6 : ℤ) ∧
    (∑ n ∈ Ico 81024 81088, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 81024 81088, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-370088 : ℤ) ∧
    (∑ n ∈ Ico 81024 81088, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-7401833839678940260301126601 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_81088_81152 :
    (∑ n ∈ Ico 81088 81152, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 81088 81152, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 81088 81152, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-61638 : ℤ) ∧
    (∑ n ∈ Ico 81088 81152, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-1232802046736678632861959788 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_81024_81152 :
    (∑ n ∈ Ico 81024 81152, mobiusTreeValue 16 mobiusTable1200001 n) = (-7 : ℤ) ∧
    (∑ n ∈ Ico 81024 81152, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 81024 81152, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-431726 : ℤ) ∧
    (∑ n ∈ Ico 81024 81152, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-8634635886415618893163086389 : ℤ) := by
  rcases cdemPrefixStats_81024_81088 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_81088_81152 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 81024 ≤ 81088) (by norm_num : 81088 ≤ 81152), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 81024 ≤ 81088) (by norm_num : 81088 ≤ 81152), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 81024 ≤ 81088) (by norm_num : 81088 ≤ 81152), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 81024 ≤ 81088) (by norm_num : 81088 ≤ 81152), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_80896_81152 :
    (∑ n ∈ Ico 80896 81152, mobiusTreeValue 16 mobiusTable1200001 n) = (-21 : ℤ) ∧
    (∑ n ∈ Ico 80896 81152, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (155 : ℕ) ∧
    (∑ n ∈ Ico 80896 81152, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-1296404 : ℤ) ∧
    (∑ n ∈ Ico 80896 81152, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-25928339299673783256421452596 : ℤ) := by
  rcases cdemPrefixStats_80896_81024 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_81024_81152 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 80896 ≤ 81024) (by norm_num : 81024 ≤ 81152), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 80896 ≤ 81024) (by norm_num : 81024 ≤ 81152), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 80896 ≤ 81024) (by norm_num : 81024 ≤ 81152), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 80896 ≤ 81024) (by norm_num : 81024 ≤ 81152), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_81152_81216 :
    (∑ n ∈ Ico 81152 81216, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 81152 81216, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 81152 81216, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (57 : ℤ) ∧
    (∑ n ∈ Ico 81152 81216, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1122594865402947317926381 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_81216_81280 :
    (∑ n ∈ Ico 81216 81280, mobiusTreeValue 16 mobiusTable1200001 n) = (9 : ℤ) ∧
    (∑ n ∈ Ico 81216 81280, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 81216 81280, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (553790 : ℤ) ∧
    (∑ n ∈ Ico 81216 81280, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (11075878330862852635480872437 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_81152_81280 :
    (∑ n ∈ Ico 81152 81280, mobiusTreeValue 16 mobiusTable1200001 n) = (9 : ℤ) ∧
    (∑ n ∈ Ico 81152 81280, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 81152 81280, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (553847 : ℤ) ∧
    (∑ n ∈ Ico 81152 81280, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (11077000925728255582798798818 : ℤ) := by
  rcases cdemPrefixStats_81152_81216 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_81216_81280 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 81152 ≤ 81216) (by norm_num : 81216 ≤ 81280), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 81152 ≤ 81216) (by norm_num : 81216 ≤ 81280), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 81152 ≤ 81216) (by norm_num : 81216 ≤ 81280), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 81152 ≤ 81216) (by norm_num : 81216 ≤ 81280), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_81280_81344 :
    (∑ n ∈ Ico 81280 81344, mobiusTreeValue 16 mobiusTable1200001 n) = (-2 : ℤ) ∧
    (∑ n ∈ Ico 81280 81344, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 81280 81344, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-123112 : ℤ) ∧
    (∑ n ∈ Ico 81280 81344, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-2462263729639093137722164848 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_81344_81408 :
    (∑ n ∈ Ico 81344 81408, mobiusTreeValue 16 mobiusTable1200001 n) = (-6 : ℤ) ∧
    (∑ n ∈ Ico 81344 81408, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 81344 81408, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-368832 : ℤ) ∧
    (∑ n ∈ Ico 81344 81408, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-7376715714708086129296922020 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_81280_81408 :
    (∑ n ∈ Ico 81280 81408, mobiusTreeValue 16 mobiusTable1200001 n) = (-8 : ℤ) ∧
    (∑ n ∈ Ico 81280 81408, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (80 : ℕ) ∧
    (∑ n ∈ Ico 81280 81408, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-491944 : ℤ) ∧
    (∑ n ∈ Ico 81280 81408, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-9838979444347179267019086868 : ℤ) := by
  rcases cdemPrefixStats_81280_81344 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_81344_81408 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 81280 ≤ 81344) (by norm_num : 81344 ≤ 81408), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 81280 ≤ 81344) (by norm_num : 81344 ≤ 81408), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 81280 ≤ 81344) (by norm_num : 81344 ≤ 81408), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 81280 ≤ 81344) (by norm_num : 81344 ≤ 81408), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_81152_81408 :
    (∑ n ∈ Ico 81152 81408, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 81152 81408, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (157 : ℕ) ∧
    (∑ n ∈ Ico 81152 81408, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (61903 : ℤ) ∧
    (∑ n ∈ Ico 81152 81408, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1238021481381076315779711950 : ℤ) := by
  rcases cdemPrefixStats_81152_81280 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_81280_81408 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 81152 ≤ 81280) (by norm_num : 81280 ≤ 81408), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 81152 ≤ 81280) (by norm_num : 81280 ≤ 81408), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 81152 ≤ 81280) (by norm_num : 81280 ≤ 81408), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 81152 ≤ 81280) (by norm_num : 81280 ≤ 81408), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_80896_81408 :
    (∑ n ∈ Ico 80896 81408, mobiusTreeValue 16 mobiusTable1200001 n) = (-20 : ℤ) ∧
    (∑ n ∈ Ico 80896 81408, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (312 : ℕ) ∧
    (∑ n ∈ Ico 80896 81408, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-1234501 : ℤ) ∧
    (∑ n ∈ Ico 80896 81408, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-24690317818292706940641740646 : ℤ) := by
  rcases cdemPrefixStats_80896_81152 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_81152_81408 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 80896 ≤ 81152) (by norm_num : 81152 ≤ 81408), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 80896 ≤ 81152) (by norm_num : 81152 ≤ 81408), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 80896 ≤ 81152) (by norm_num : 81152 ≤ 81408), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 80896 ≤ 81152) (by norm_num : 81152 ≤ 81408), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_81408_81472 :
    (∑ n ∈ Ico 81408 81472, mobiusTreeValue 16 mobiusTable1200001 n) = (-5 : ℤ) ∧
    (∑ n ∈ Ico 81408 81472, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 81408 81472, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-306877 : ℤ) ∧
    (∑ n ∈ Ico 81408 81472, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-6137559870317148685877295142 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_81472_81536 :
    (∑ n ∈ Ico 81472 81536, mobiusTreeValue 16 mobiusTable1200001 n) = (2 : ℤ) ∧
    (∑ n ∈ Ico 81472 81536, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 81472 81536, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (122716 : ℤ) ∧
    (∑ n ∈ Ico 81472 81536, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (2454303904504612224791755786 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_81408_81536 :
    (∑ n ∈ Ico 81408 81536, mobiusTreeValue 16 mobiusTable1200001 n) = (-3 : ℤ) ∧
    (∑ n ∈ Ico 81408 81536, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (75 : ℕ) ∧
    (∑ n ∈ Ico 81408 81536, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-184161 : ℤ) ∧
    (∑ n ∈ Ico 81408 81536, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-3683255965812536461085539356 : ℤ) := by
  rcases cdemPrefixStats_81408_81472 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_81472_81536 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 81408 ≤ 81472) (by norm_num : 81472 ≤ 81536), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 81408 ≤ 81472) (by norm_num : 81472 ≤ 81536), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 81408 ≤ 81472) (by norm_num : 81472 ≤ 81536), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 81408 ≤ 81472) (by norm_num : 81472 ≤ 81536), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_81536_81600 :
    (∑ n ∈ Ico 81536 81600, mobiusTreeValue 16 mobiusTable1200001 n) = (-4 : ℤ) ∧
    (∑ n ∈ Ico 81536 81600, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 81536 81600, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-245311 : ℤ) ∧
    (∑ n ∈ Ico 81536 81600, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-4906243060927229030770777408 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_81600_81664 :
    (∑ n ∈ Ico 81600 81664, mobiusTreeValue 16 mobiusTable1200001 n) = (-3 : ℤ) ∧
    (∑ n ∈ Ico 81600 81664, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 81600 81664, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-183795 : ℤ) ∧
    (∑ n ∈ Ico 81600 81664, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-3675839648935292280267150384 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_81536_81664 :
    (∑ n ∈ Ico 81536 81664, mobiusTreeValue 16 mobiusTable1200001 n) = (-7 : ℤ) ∧
    (∑ n ∈ Ico 81536 81664, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 81536 81664, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-429106 : ℤ) ∧
    (∑ n ∈ Ico 81536 81664, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-8582082709862521311037927792 : ℤ) := by
  rcases cdemPrefixStats_81536_81600 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_81600_81664 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 81536 ≤ 81600) (by norm_num : 81600 ≤ 81664), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 81536 ≤ 81600) (by norm_num : 81600 ≤ 81664), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 81536 ≤ 81600) (by norm_num : 81600 ≤ 81664), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 81536 ≤ 81600) (by norm_num : 81600 ≤ 81664), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_81408_81664 :
    (∑ n ∈ Ico 81408 81664, mobiusTreeValue 16 mobiusTable1200001 n) = (-10 : ℤ) ∧
    (∑ n ∈ Ico 81408 81664, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (152 : ℕ) ∧
    (∑ n ∈ Ico 81408 81664, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-613267 : ℤ) ∧
    (∑ n ∈ Ico 81408 81664, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-12265338675675057772123467148 : ℤ) := by
  rcases cdemPrefixStats_81408_81536 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_81536_81664 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 81408 ≤ 81536) (by norm_num : 81536 ≤ 81664), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 81408 ≤ 81536) (by norm_num : 81536 ≤ 81664), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 81408 ≤ 81536) (by norm_num : 81536 ≤ 81664), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 81408 ≤ 81536) (by norm_num : 81536 ≤ 81664), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_81664_81728 :
    (∑ n ∈ Ico 81664 81728, mobiusTreeValue 16 mobiusTable1200001 n) = (-6 : ℤ) ∧
    (∑ n ∈ Ico 81664 81728, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 81664 81728, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-367395 : ℤ) ∧
    (∑ n ∈ Ico 81664 81728, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-7347957099822395358153646922 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_81728_81792 :
    (∑ n ∈ Ico 81728 81792, mobiusTreeValue 16 mobiusTable1200001 n) = (-3 : ℤ) ∧
    (∑ n ∈ Ico 81728 81792, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 81728 81792, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-183390 : ℤ) ∧
    (∑ n ∈ Ico 81728 81792, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-3667869730449754345562809258 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_81664_81792 :
    (∑ n ∈ Ico 81664 81792, mobiusTreeValue 16 mobiusTable1200001 n) = (-9 : ℤ) ∧
    (∑ n ∈ Ico 81664 81792, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 81664 81792, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-550785 : ℤ) ∧
    (∑ n ∈ Ico 81664 81792, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-11015826830272149703716456180 : ℤ) := by
  rcases cdemPrefixStats_81664_81728 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_81728_81792 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 81664 ≤ 81728) (by norm_num : 81728 ≤ 81792), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 81664 ≤ 81728) (by norm_num : 81728 ≤ 81792), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 81664 ≤ 81728) (by norm_num : 81728 ≤ 81792), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 81664 ≤ 81728) (by norm_num : 81728 ≤ 81792), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_81792_81856 :
    (∑ n ∈ Ico 81792 81856, mobiusTreeValue 16 mobiusTable1200001 n) = (7 : ℤ) ∧
    (∑ n ∈ Ico 81792 81856, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 81792 81856, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (427806 : ℤ) ∧
    (∑ n ∈ Ico 81792 81856, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (8556217122277809427733349651 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_81856_81920 :
    (∑ n ∈ Ico 81856 81920, mobiusTreeValue 16 mobiusTable1200001 n) = (5 : ℤ) ∧
    (∑ n ∈ Ico 81856 81920, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 81856 81920, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (305378 : ℤ) ∧
    (∑ n ∈ Ico 81856 81920, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (6107571293469092041566069499 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_81792_81920 :
    (∑ n ∈ Ico 81792 81920, mobiusTreeValue 16 mobiusTable1200001 n) = (12 : ℤ) ∧
    (∑ n ∈ Ico 81792 81920, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 81792 81920, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (733184 : ℤ) ∧
    (∑ n ∈ Ico 81792 81920, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (14663788415746901469299419150 : ℤ) := by
  rcases cdemPrefixStats_81792_81856 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_81856_81920 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 81792 ≤ 81856) (by norm_num : 81856 ≤ 81920), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 81792 ≤ 81856) (by norm_num : 81856 ≤ 81920), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 81792 ≤ 81856) (by norm_num : 81856 ≤ 81920), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 81792 ≤ 81856) (by norm_num : 81856 ≤ 81920), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_81664_81920 :
    (∑ n ∈ Ico 81664 81920, mobiusTreeValue 16 mobiusTable1200001 n) = (3 : ℤ) ∧
    (∑ n ∈ Ico 81664 81920, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (155 : ℕ) ∧
    (∑ n ∈ Ico 81664 81920, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (182399 : ℤ) ∧
    (∑ n ∈ Ico 81664 81920, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (3647961585474751765582962970 : ℤ) := by
  rcases cdemPrefixStats_81664_81792 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_81792_81920 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 81664 ≤ 81792) (by norm_num : 81792 ≤ 81920), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 81664 ≤ 81792) (by norm_num : 81792 ≤ 81920), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 81664 ≤ 81792) (by norm_num : 81792 ≤ 81920), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 81664 ≤ 81792) (by norm_num : 81792 ≤ 81920), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_81408_81920 :
    (∑ n ∈ Ico 81408 81920, mobiusTreeValue 16 mobiusTable1200001 n) = (-7 : ℤ) ∧
    (∑ n ∈ Ico 81408 81920, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (307 : ℕ) ∧
    (∑ n ∈ Ico 81408 81920, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-430868 : ℤ) ∧
    (∑ n ∈ Ico 81408 81920, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-8617377090200306006540504178 : ℤ) := by
  rcases cdemPrefixStats_81408_81664 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_81664_81920 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 81408 ≤ 81664) (by norm_num : 81664 ≤ 81920), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 81408 ≤ 81664) (by norm_num : 81664 ≤ 81920), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 81408 ≤ 81664) (by norm_num : 81664 ≤ 81920), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 81408 ≤ 81664) (by norm_num : 81664 ≤ 81920), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_80896_81920 :
    (∑ n ∈ Ico 80896 81920, mobiusTreeValue 16 mobiusTable1200001 n) = (-27 : ℤ) ∧
    (∑ n ∈ Ico 80896 81920, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (619 : ℕ) ∧
    (∑ n ∈ Ico 80896 81920, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-1665369 : ℤ) ∧
    (∑ n ∈ Ico 80896 81920, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-33307694908493012947182244824 : ℤ) := by
  rcases cdemPrefixStats_80896_81408 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_81408_81920 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 80896 ≤ 81408) (by norm_num : 81408 ≤ 81920), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 80896 ≤ 81408) (by norm_num : 81408 ≤ 81920), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 80896 ≤ 81408) (by norm_num : 81408 ≤ 81920), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 80896 ≤ 81408) (by norm_num : 81408 ≤ 81920), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_79872_81920 :
    (∑ n ∈ Ico 79872 81920, mobiusTreeValue 16 mobiusTable1200001 n) = (-25 : ℤ) ∧
    (∑ n ∈ Ico 79872 81920, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (1243 : ℕ) ∧
    (∑ n ∈ Ico 79872 81920, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-1539579 : ℤ) ∧
    (∑ n ∈ Ico 79872 81920, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-30791955647811748353954144505 : ℤ) := by
  rcases cdemPrefixStats_79872_80896 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_80896_81920 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 79872 ≤ 80896) (by norm_num : 80896 ≤ 81920), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 79872 ≤ 80896) (by norm_num : 80896 ≤ 81920), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 79872 ≤ 80896) (by norm_num : 80896 ≤ 81920), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 79872 ≤ 80896) (by norm_num : 80896 ≤ 81920), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_77824_81920 :
    (∑ n ∈ Ico 77824 81920, mobiusTreeValue 16 mobiusTable1200001 n) = (-11 : ℤ) ∧
    (∑ n ∈ Ico 77824 81920, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (2487 : ℕ) ∧
    (∑ n ∈ Ico 77824 81920, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-636009 : ℤ) ∧
    (∑ n ∈ Ico 77824 81920, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-12720418578954713761090633101 : ℤ) := by
  rcases cdemPrefixStats_77824_79872 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_79872_81920 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 77824 ≤ 79872) (by norm_num : 79872 ≤ 81920), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 77824 ≤ 79872) (by norm_num : 79872 ≤ 81920), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 77824 ≤ 79872) (by norm_num : 79872 ≤ 81920), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 77824 ≤ 79872) (by norm_num : 79872 ≤ 81920), hR1, hR2] <;> norm_num

theorem cdemPrefixGroup019_checked_complete :
    (∑ n ∈ Ico 77824 81920, mobiusTreeValue 16 mobiusTable1200001 n) = (-11 : ℤ) ∧
    (∑ n ∈ Ico 77824 81920, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (2487 : ℕ) ∧
    (∑ n ∈ Ico 77824 81920, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-636009 : ℤ) ∧
    (∑ n ∈ Ico 77824 81920, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-12720418578954713761090633101 : ℤ) := cdemPrefixStats_77824_81920
end Helfgott
#print axioms Helfgott.cdemPrefixGroup019_checked_complete

open Helfgott Finset
open scoped BigOperators

theorem solution :
    (∑ n ∈ Ico 77824 81920, mobiusTreeValue 16 mobiusTable1200001 n) = (-11 : ℤ) ∧
    (∑ n ∈ Ico 77824 81920, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (2487 : ℕ) ∧
    (∑ n ∈ Ico 77824 81920, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-636009 : ℤ) ∧
    (∑ n ∈ Ico 77824 81920, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-12720418578954713761090633101 : ℤ) := Helfgott.cdemPrefixGroup019_checked_complete
#print axioms solution
