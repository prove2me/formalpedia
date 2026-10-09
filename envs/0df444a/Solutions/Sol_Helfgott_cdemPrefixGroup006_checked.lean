-- Prove2me | solution 1 for Helfgott.cdemPrefixGroup006_checked
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-09T01:24:36.362204+00:00
-- url     : https://prove2.me/submissions/ceac6db8-e8d1-4a19-8986-5b3895700a5b

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
private theorem cdemPrefixStats_24576_24640 :
    (∑ n ∈ Ico 24576 24640, mobiusTreeValue 16 mobiusTable1200001 n) = (3 : ℤ) ∧
    (∑ n ∈ Ico 24576 24640, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 24576 24640, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (611034 : ℤ) ∧
    (∑ n ∈ Ico 24576 24640, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (12220720314191606265389249658 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_24640_24704 :
    (∑ n ∈ Ico 24640 24704, mobiusTreeValue 16 mobiusTable1200001 n) = (12 : ℤ) ∧
    (∑ n ∈ Ico 24640 24704, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 24640 24704, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (2432608 : ℤ) ∧
    (∑ n ∈ Ico 24640 24704, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (48652310498609044944926870027 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_24576_24704 :
    (∑ n ∈ Ico 24576 24704, mobiusTreeValue 16 mobiusTable1200001 n) = (15 : ℤ) ∧
    (∑ n ∈ Ico 24576 24704, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (79 : ℕ) ∧
    (∑ n ∈ Ico 24576 24704, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (3043642 : ℤ) ∧
    (∑ n ∈ Ico 24576 24704, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (60873030812800651210316119685 : ℤ) := by
  rcases cdemPrefixStats_24576_24640 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_24640_24704 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 24576 ≤ 24640) (by norm_num : 24640 ≤ 24704), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 24576 ≤ 24640) (by norm_num : 24640 ≤ 24704), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 24576 ≤ 24640) (by norm_num : 24640 ≤ 24704), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 24576 ≤ 24640) (by norm_num : 24640 ≤ 24704), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_24704_24768 :
    (∑ n ∈ Ico 24704 24768, mobiusTreeValue 16 mobiusTable1200001 n) = (8 : ℤ) ∧
    (∑ n ∈ Ico 24704 24768, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 24704 24768, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (1617449 : ℤ) ∧
    (∑ n ∈ Ico 24704 24768, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (32349066941284783271612537892 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_24768_24832 :
    (∑ n ∈ Ico 24768 24832, mobiusTreeValue 16 mobiusTable1200001 n) = (2 : ℤ) ∧
    (∑ n ∈ Ico 24768 24832, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 24768 24832, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (402208 : ℤ) ∧
    (∑ n ∈ Ico 24768 24832, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (8044189255507685082842006302 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_24704_24832 :
    (∑ n ∈ Ico 24704 24832, mobiusTreeValue 16 mobiusTable1200001 n) = (10 : ℤ) ∧
    (∑ n ∈ Ico 24704 24832, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 24704 24832, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (2019657 : ℤ) ∧
    (∑ n ∈ Ico 24704 24832, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (40393256196792468354454544194 : ℤ) := by
  rcases cdemPrefixStats_24704_24768 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_24768_24832 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 24704 ≤ 24768) (by norm_num : 24768 ≤ 24832), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 24704 ≤ 24768) (by norm_num : 24768 ≤ 24832), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 24704 ≤ 24768) (by norm_num : 24768 ≤ 24832), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 24704 ≤ 24768) (by norm_num : 24768 ≤ 24832), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_24576_24832 :
    (∑ n ∈ Ico 24576 24832, mobiusTreeValue 16 mobiusTable1200001 n) = (25 : ℤ) ∧
    (∑ n ∈ Ico 24576 24832, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (157 : ℕ) ∧
    (∑ n ∈ Ico 24576 24832, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (5063299 : ℤ) ∧
    (∑ n ∈ Ico 24576 24832, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (101266287009593119564770663879 : ℤ) := by
  rcases cdemPrefixStats_24576_24704 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_24704_24832 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 24576 ≤ 24704) (by norm_num : 24704 ≤ 24832), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 24576 ≤ 24704) (by norm_num : 24704 ≤ 24832), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 24576 ≤ 24704) (by norm_num : 24704 ≤ 24832), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 24576 ≤ 24704) (by norm_num : 24704 ≤ 24832), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_24832_24896 :
    (∑ n ∈ Ico 24832 24896, mobiusTreeValue 16 mobiusTable1200001 n) = (4 : ℤ) ∧
    (∑ n ∈ Ico 24832 24896, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 24832 24896, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (804244 : ℤ) ∧
    (∑ n ∈ Ico 24832 24896, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (16084926583434521258095168931 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_24896_24960 :
    (∑ n ∈ Ico 24896 24960, mobiusTreeValue 16 mobiusTable1200001 n) = (4 : ℤ) ∧
    (∑ n ∈ Ico 24896 24960, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 24896 24960, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (802141 : ℤ) ∧
    (∑ n ∈ Ico 24896 24960, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (16042848822125367730387016605 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_24832_24960 :
    (∑ n ∈ Ico 24832 24960, mobiusTreeValue 16 mobiusTable1200001 n) = (8 : ℤ) ∧
    (∑ n ∈ Ico 24832 24960, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (76 : ℕ) ∧
    (∑ n ∈ Ico 24832 24960, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (1606385 : ℤ) ∧
    (∑ n ∈ Ico 24832 24960, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (32127775405559888988482185536 : ℤ) := by
  rcases cdemPrefixStats_24832_24896 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_24896_24960 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 24832 ≤ 24896) (by norm_num : 24896 ≤ 24960), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 24832 ≤ 24896) (by norm_num : 24896 ≤ 24960), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 24832 ≤ 24896) (by norm_num : 24896 ≤ 24960), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 24832 ≤ 24896) (by norm_num : 24896 ≤ 24960), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_24960_25024 :
    (∑ n ∈ Ico 24960 25024, mobiusTreeValue 16 mobiusTable1200001 n) = (5 : ℤ) ∧
    (∑ n ∈ Ico 24960 25024, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 24960 25024, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (999304 : ℤ) ∧
    (∑ n ∈ Ico 24960 25024, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (19986077526500745299145781526 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_25024_25088 :
    (∑ n ∈ Ico 25024 25088, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 25024 25088, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 25024 25088, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-565 : ℤ) ∧
    (∑ n ∈ Ico 25024 25088, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-11309682068427059539475625 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_24960_25088 :
    (∑ n ∈ Ico 24960 25088, mobiusTreeValue 16 mobiusTable1200001 n) = (5 : ℤ) ∧
    (∑ n ∈ Ico 24960 25088, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (79 : ℕ) ∧
    (∑ n ∈ Ico 24960 25088, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (998739 : ℤ) ∧
    (∑ n ∈ Ico 24960 25088, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (19974767844432318239606305901 : ℤ) := by
  rcases cdemPrefixStats_24960_25024 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_25024_25088 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 24960 ≤ 25024) (by norm_num : 25024 ≤ 25088), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 24960 ≤ 25024) (by norm_num : 25024 ≤ 25088), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 24960 ≤ 25024) (by norm_num : 25024 ≤ 25088), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 24960 ≤ 25024) (by norm_num : 25024 ≤ 25088), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_24832_25088 :
    (∑ n ∈ Ico 24832 25088, mobiusTreeValue 16 mobiusTable1200001 n) = (13 : ℤ) ∧
    (∑ n ∈ Ico 24832 25088, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (155 : ℕ) ∧
    (∑ n ∈ Ico 24832 25088, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (2605124 : ℤ) ∧
    (∑ n ∈ Ico 24832 25088, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (52102543249992207228088491437 : ℤ) := by
  rcases cdemPrefixStats_24832_24960 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_24960_25088 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 24832 ≤ 24960) (by norm_num : 24960 ≤ 25088), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 24832 ≤ 24960) (by norm_num : 24960 ≤ 25088), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 24832 ≤ 24960) (by norm_num : 24960 ≤ 25088), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 24832 ≤ 24960) (by norm_num : 24960 ≤ 25088), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_24576_25088 :
    (∑ n ∈ Ico 24576 25088, mobiusTreeValue 16 mobiusTable1200001 n) = (38 : ℤ) ∧
    (∑ n ∈ Ico 24576 25088, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (312 : ℕ) ∧
    (∑ n ∈ Ico 24576 25088, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (7668423 : ℤ) ∧
    (∑ n ∈ Ico 24576 25088, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (153368830259585326792859155316 : ℤ) := by
  rcases cdemPrefixStats_24576_24832 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_24832_25088 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 24576 ≤ 24832) (by norm_num : 24832 ≤ 25088), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 24576 ≤ 24832) (by norm_num : 24832 ≤ 25088), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 24576 ≤ 24832) (by norm_num : 24832 ≤ 25088), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 24576 ≤ 24832) (by norm_num : 24832 ≤ 25088), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_25088_25152 :
    (∑ n ∈ Ico 25088 25152, mobiusTreeValue 16 mobiusTable1200001 n) = (8 : ℤ) ∧
    (∑ n ∈ Ico 25088 25152, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 25088 25152, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (1594091 : ℤ) ∧
    (∑ n ∈ Ico 25088 25152, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (31881876509170743097972911721 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_25152_25216 :
    (∑ n ∈ Ico 25152 25216, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 25152 25216, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 25152 25216, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (1136 : ℤ) ∧
    (∑ n ∈ Ico 25152 25216, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (22705278647602184448638161 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_25088_25216 :
    (∑ n ∈ Ico 25088 25216, mobiusTreeValue 16 mobiusTable1200001 n) = (8 : ℤ) ∧
    (∑ n ∈ Ico 25088 25216, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 25088 25216, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (1595227 : ℤ) ∧
    (∑ n ∈ Ico 25088 25216, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (31904581787818345282421549882 : ℤ) := by
  rcases cdemPrefixStats_25088_25152 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_25152_25216 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 25088 ≤ 25152) (by norm_num : 25152 ≤ 25216), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 25088 ≤ 25152) (by norm_num : 25152 ≤ 25216), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 25088 ≤ 25152) (by norm_num : 25152 ≤ 25216), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 25088 ≤ 25152) (by norm_num : 25152 ≤ 25216), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_25216_25280 :
    (∑ n ∈ Ico 25216 25280, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 25216 25280, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 25216 25280, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (197781 : ℤ) ∧
    (∑ n ∈ Ico 25216 25280, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (3955712066850147035875664601 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_25280_25344 :
    (∑ n ∈ Ico 25280 25344, mobiusTreeValue 16 mobiusTable1200001 n) = (5 : ℤ) ∧
    (∑ n ∈ Ico 25280 25344, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 25280 25344, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (988149 : ℤ) ∧
    (∑ n ∈ Ico 25280 25344, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (19763021733286816627042829640 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_25216_25344 :
    (∑ n ∈ Ico 25216 25344, mobiusTreeValue 16 mobiusTable1200001 n) = (6 : ℤ) ∧
    (∑ n ∈ Ico 25216 25344, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (76 : ℕ) ∧
    (∑ n ∈ Ico 25216 25344, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (1185930 : ℤ) ∧
    (∑ n ∈ Ico 25216 25344, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (23718733800136963662918494241 : ℤ) := by
  rcases cdemPrefixStats_25216_25280 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_25280_25344 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 25216 ≤ 25280) (by norm_num : 25280 ≤ 25344), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 25216 ≤ 25280) (by norm_num : 25280 ≤ 25344), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 25216 ≤ 25280) (by norm_num : 25280 ≤ 25344), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 25216 ≤ 25280) (by norm_num : 25280 ≤ 25344), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_25088_25344 :
    (∑ n ∈ Ico 25088 25344, mobiusTreeValue 16 mobiusTable1200001 n) = (14 : ℤ) ∧
    (∑ n ∈ Ico 25088 25344, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (154 : ℕ) ∧
    (∑ n ∈ Ico 25088 25344, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (2781157 : ℤ) ∧
    (∑ n ∈ Ico 25088 25344, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (55623315587955308945340044123 : ℤ) := by
  rcases cdemPrefixStats_25088_25216 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_25216_25344 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 25088 ≤ 25216) (by norm_num : 25216 ≤ 25344), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 25088 ≤ 25216) (by norm_num : 25216 ≤ 25344), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 25088 ≤ 25216) (by norm_num : 25216 ≤ 25344), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 25088 ≤ 25216) (by norm_num : 25216 ≤ 25344), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_25344_25408 :
    (∑ n ∈ Ico 25344 25408, mobiusTreeValue 16 mobiusTable1200001 n) = (3 : ℤ) ∧
    (∑ n ∈ Ico 25344 25408, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 25344 25408, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (590092 : ℤ) ∧
    (∑ n ∈ Ico 25344 25408, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (11801857650462233196769811707 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_25408_25472 :
    (∑ n ∈ Ico 25408 25472, mobiusTreeValue 16 mobiusTable1200001 n) = (-10 : ℤ) ∧
    (∑ n ∈ Ico 25408 25472, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 25408 25472, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-1964433 : ℤ) ∧
    (∑ n ∈ Ico 25408 25472, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-39288744701009566782041695082 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_25344_25472 :
    (∑ n ∈ Ico 25344 25472, mobiusTreeValue 16 mobiusTable1200001 n) = (-7 : ℤ) ∧
    (∑ n ∈ Ico 25344 25472, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (79 : ℕ) ∧
    (∑ n ∈ Ico 25344 25472, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-1374341 : ℤ) ∧
    (∑ n ∈ Ico 25344 25472, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-27486887050547333585271883375 : ℤ) := by
  rcases cdemPrefixStats_25344_25408 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_25408_25472 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 25344 ≤ 25408) (by norm_num : 25408 ≤ 25472), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 25344 ≤ 25408) (by norm_num : 25408 ≤ 25472), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 25344 ≤ 25408) (by norm_num : 25408 ≤ 25472), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 25344 ≤ 25408) (by norm_num : 25408 ≤ 25472), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_25472_25536 :
    (∑ n ∈ Ico 25472 25536, mobiusTreeValue 16 mobiusTable1200001 n) = (2 : ℤ) ∧
    (∑ n ∈ Ico 25472 25536, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 25472 25536, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (393143 : ℤ) ∧
    (∑ n ∈ Ico 25472 25536, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (7862962374823394942089999795 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_25536_25600 :
    (∑ n ∈ Ico 25536 25600, mobiusTreeValue 16 mobiusTable1200001 n) = (-4 : ℤ) ∧
    (∑ n ∈ Ico 25536 25600, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 25536 25600, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-782825 : ℤ) ∧
    (∑ n ∈ Ico 25536 25600, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-15656490008017144753278841465 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_25472_25600 :
    (∑ n ∈ Ico 25472 25600, mobiusTreeValue 16 mobiusTable1200001 n) = (-2 : ℤ) ∧
    (∑ n ∈ Ico 25472 25600, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 25472 25600, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-389682 : ℤ) ∧
    (∑ n ∈ Ico 25472 25600, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-7793527633193749811188841670 : ℤ) := by
  rcases cdemPrefixStats_25472_25536 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_25536_25600 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 25472 ≤ 25536) (by norm_num : 25536 ≤ 25600), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 25472 ≤ 25536) (by norm_num : 25536 ≤ 25600), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 25472 ≤ 25536) (by norm_num : 25536 ≤ 25600), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 25472 ≤ 25536) (by norm_num : 25536 ≤ 25600), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_25344_25600 :
    (∑ n ∈ Ico 25344 25600, mobiusTreeValue 16 mobiusTable1200001 n) = (-9 : ℤ) ∧
    (∑ n ∈ Ico 25344 25600, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (157 : ℕ) ∧
    (∑ n ∈ Ico 25344 25600, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-1764023 : ℤ) ∧
    (∑ n ∈ Ico 25344 25600, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-35280414683741083396460725045 : ℤ) := by
  rcases cdemPrefixStats_25344_25472 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_25472_25600 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 25344 ≤ 25472) (by norm_num : 25472 ≤ 25600), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 25344 ≤ 25472) (by norm_num : 25472 ≤ 25600), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 25344 ≤ 25472) (by norm_num : 25472 ≤ 25600), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 25344 ≤ 25472) (by norm_num : 25472 ≤ 25600), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_25088_25600 :
    (∑ n ∈ Ico 25088 25600, mobiusTreeValue 16 mobiusTable1200001 n) = (5 : ℤ) ∧
    (∑ n ∈ Ico 25088 25600, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (311 : ℕ) ∧
    (∑ n ∈ Ico 25088 25600, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (1017134 : ℤ) ∧
    (∑ n ∈ Ico 25088 25600, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (20342900904214225548879319078 : ℤ) := by
  rcases cdemPrefixStats_25088_25344 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_25344_25600 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 25088 ≤ 25344) (by norm_num : 25344 ≤ 25600), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 25088 ≤ 25344) (by norm_num : 25344 ≤ 25600), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 25088 ≤ 25344) (by norm_num : 25344 ≤ 25600), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 25088 ≤ 25344) (by norm_num : 25344 ≤ 25600), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_24576_25600 :
    (∑ n ∈ Ico 24576 25600, mobiusTreeValue 16 mobiusTable1200001 n) = (43 : ℤ) ∧
    (∑ n ∈ Ico 24576 25600, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (623 : ℕ) ∧
    (∑ n ∈ Ico 24576 25600, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (8685557 : ℤ) ∧
    (∑ n ∈ Ico 24576 25600, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (173711731163799552341738474394 : ℤ) := by
  rcases cdemPrefixStats_24576_25088 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_25088_25600 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 24576 ≤ 25088) (by norm_num : 25088 ≤ 25600), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 24576 ≤ 25088) (by norm_num : 25088 ≤ 25600), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 24576 ≤ 25088) (by norm_num : 25088 ≤ 25600), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 24576 ≤ 25088) (by norm_num : 25088 ≤ 25600), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_25600_25664 :
    (∑ n ∈ Ico 25600 25664, mobiusTreeValue 16 mobiusTable1200001 n) = (-3 : ℤ) ∧
    (∑ n ∈ Ico 25600 25664, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 25600 25664, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-584707 : ℤ) ∧
    (∑ n ∈ Ico 25600 25664, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-11694222042846270386573023924 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_25664_25728 :
    (∑ n ∈ Ico 25664 25728, mobiusTreeValue 16 mobiusTable1200001 n) = (2 : ℤ) ∧
    (∑ n ∈ Ico 25664 25728, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 25664 25728, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (388013 : ℤ) ∧
    (∑ n ∈ Ico 25664 25728, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (7760293022699933036378775820 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_25600_25728 :
    (∑ n ∈ Ico 25600 25728, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 25600 25728, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (79 : ℕ) ∧
    (∑ n ∈ Ico 25600 25728, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-196694 : ℤ) ∧
    (∑ n ∈ Ico 25600 25728, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-3933929020146337350194248104 : ℤ) := by
  rcases cdemPrefixStats_25600_25664 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_25664_25728 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 25600 ≤ 25664) (by norm_num : 25664 ≤ 25728), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 25600 ≤ 25664) (by norm_num : 25664 ≤ 25728), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 25600 ≤ 25664) (by norm_num : 25664 ≤ 25728), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 25600 ≤ 25664) (by norm_num : 25664 ≤ 25728), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_25728_25792 :
    (∑ n ∈ Ico 25728 25792, mobiusTreeValue 16 mobiusTable1200001 n) = (-5 : ℤ) ∧
    (∑ n ∈ Ico 25728 25792, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 25728 25792, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-970481 : ℤ) ∧
    (∑ n ∈ Ico 25728 25792, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-19409639984643126293293947244 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_25792_25856 :
    (∑ n ∈ Ico 25792 25856, mobiusTreeValue 16 mobiusTable1200001 n) = (10 : ℤ) ∧
    (∑ n ∈ Ico 25792 25856, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 25792 25856, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (1935810 : ℤ) ∧
    (∑ n ∈ Ico 25792 25856, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (38716334202070956242165588305 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_25728_25856 :
    (∑ n ∈ Ico 25728 25856, mobiusTreeValue 16 mobiusTable1200001 n) = (5 : ℤ) ∧
    (∑ n ∈ Ico 25728 25856, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (79 : ℕ) ∧
    (∑ n ∈ Ico 25728 25856, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (965329 : ℤ) ∧
    (∑ n ∈ Ico 25728 25856, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (19306694217427829948871641061 : ℤ) := by
  rcases cdemPrefixStats_25728_25792 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_25792_25856 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 25728 ≤ 25792) (by norm_num : 25792 ≤ 25856), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 25728 ≤ 25792) (by norm_num : 25792 ≤ 25856), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 25728 ≤ 25792) (by norm_num : 25792 ≤ 25856), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 25728 ≤ 25792) (by norm_num : 25792 ≤ 25856), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_25600_25856 :
    (∑ n ∈ Ico 25600 25856, mobiusTreeValue 16 mobiusTable1200001 n) = (4 : ℤ) ∧
    (∑ n ∈ Ico 25600 25856, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (158 : ℕ) ∧
    (∑ n ∈ Ico 25600 25856, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (768635 : ℤ) ∧
    (∑ n ∈ Ico 25600 25856, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (15372765197281492598677392957 : ℤ) := by
  rcases cdemPrefixStats_25600_25728 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_25728_25856 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 25600 ≤ 25728) (by norm_num : 25728 ≤ 25856), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 25600 ≤ 25728) (by norm_num : 25728 ≤ 25856), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 25600 ≤ 25728) (by norm_num : 25728 ≤ 25856), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 25600 ≤ 25728) (by norm_num : 25728 ≤ 25856), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_25856_25920 :
    (∑ n ∈ Ico 25856 25920, mobiusTreeValue 16 mobiusTable1200001 n) = (2 : ℤ) ∧
    (∑ n ∈ Ico 25856 25920, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 25856 25920, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (386398 : ℤ) ∧
    (∑ n ∈ Ico 25856 25920, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (7727965082157205178818049211 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_25920_25984 :
    (∑ n ∈ Ico 25920 25984, mobiusTreeValue 16 mobiusTable1200001 n) = (-3 : ℤ) ∧
    (∑ n ∈ Ico 25920 25984, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 25920 25984, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-577446 : ℤ) ∧
    (∑ n ∈ Ico 25920 25984, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-11548973847014833278324700112 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_25856_25984 :
    (∑ n ∈ Ico 25856 25984, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 25856 25984, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 25856 25984, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-191048 : ℤ) ∧
    (∑ n ∈ Ico 25856 25984, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-3821008764857628099506650901 : ℤ) := by
  rcases cdemPrefixStats_25856_25920 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_25920_25984 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 25856 ≤ 25920) (by norm_num : 25920 ≤ 25984), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 25856 ≤ 25920) (by norm_num : 25920 ≤ 25984), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 25856 ≤ 25920) (by norm_num : 25920 ≤ 25984), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 25856 ≤ 25920) (by norm_num : 25920 ≤ 25984), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_25984_26048 :
    (∑ n ∈ Ico 25984 26048, mobiusTreeValue 16 mobiusTable1200001 n) = (4 : ℤ) ∧
    (∑ n ∈ Ico 25984 26048, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 25984 26048, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (769087 : ℤ) ∧
    (∑ n ∈ Ico 25984 26048, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (15381814496627395799054697620 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_26048_26112 :
    (∑ n ∈ Ico 26048 26112, mobiusTreeValue 16 mobiusTable1200001 n) = (8 : ℤ) ∧
    (∑ n ∈ Ico 26048 26112, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 26048 26112, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (1533750 : ℤ) ∧
    (∑ n ∈ Ico 26048 26112, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (30675137365432970238388485797 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_25984_26112 :
    (∑ n ∈ Ico 25984 26112, mobiusTreeValue 16 mobiusTable1200001 n) = (12 : ℤ) ∧
    (∑ n ∈ Ico 25984 26112, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 25984 26112, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (2302837 : ℤ) ∧
    (∑ n ∈ Ico 25984 26112, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (46056951862060366037443183417 : ℤ) := by
  rcases cdemPrefixStats_25984_26048 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_26048_26112 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 25984 ≤ 26048) (by norm_num : 26048 ≤ 26112), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 25984 ≤ 26048) (by norm_num : 26048 ≤ 26112), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 25984 ≤ 26048) (by norm_num : 26048 ≤ 26112), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 25984 ≤ 26048) (by norm_num : 26048 ≤ 26112), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_25856_26112 :
    (∑ n ∈ Ico 25856 26112, mobiusTreeValue 16 mobiusTable1200001 n) = (11 : ℤ) ∧
    (∑ n ∈ Ico 25856 26112, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (155 : ℕ) ∧
    (∑ n ∈ Ico 25856 26112, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (2111789 : ℤ) ∧
    (∑ n ∈ Ico 25856 26112, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (42235943097202737937936532516 : ℤ) := by
  rcases cdemPrefixStats_25856_25984 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_25984_26112 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 25856 ≤ 25984) (by norm_num : 25984 ≤ 26112), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 25856 ≤ 25984) (by norm_num : 25984 ≤ 26112), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 25856 ≤ 25984) (by norm_num : 25984 ≤ 26112), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 25856 ≤ 25984) (by norm_num : 25984 ≤ 26112), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_25600_26112 :
    (∑ n ∈ Ico 25600 26112, mobiusTreeValue 16 mobiusTable1200001 n) = (15 : ℤ) ∧
    (∑ n ∈ Ico 25600 26112, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (313 : ℕ) ∧
    (∑ n ∈ Ico 25600 26112, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (2880424 : ℤ) ∧
    (∑ n ∈ Ico 25600 26112, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (57608708294484230536613925473 : ℤ) := by
  rcases cdemPrefixStats_25600_25856 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_25856_26112 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 25600 ≤ 25856) (by norm_num : 25856 ≤ 26112), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 25600 ≤ 25856) (by norm_num : 25856 ≤ 26112), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 25600 ≤ 25856) (by norm_num : 25856 ≤ 26112), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 25600 ≤ 25856) (by norm_num : 25856 ≤ 26112), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_26112_26176 :
    (∑ n ∈ Ico 26112 26176, mobiusTreeValue 16 mobiusTable1200001 n) = (-4 : ℤ) ∧
    (∑ n ∈ Ico 26112 26176, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 26112 26176, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-765680 : ℤ) ∧
    (∑ n ∈ Ico 26112 26176, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-15313648114120441658730584424 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_26176_26240 :
    (∑ n ∈ Ico 26176 26240, mobiusTreeValue 16 mobiusTable1200001 n) = (5 : ℤ) ∧
    (∑ n ∈ Ico 26176 26240, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 26176 26240, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (953942 : ℤ) ∧
    (∑ n ∈ Ico 26176 26240, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (19078873381551974797540654983 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_26112_26240 :
    (∑ n ∈ Ico 26112 26240, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 26112 26240, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 26112 26240, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (188262 : ℤ) ∧
    (∑ n ∈ Ico 26112 26240, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (3765225267431533138810070559 : ℤ) := by
  rcases cdemPrefixStats_26112_26176 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_26176_26240 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 26112 ≤ 26176) (by norm_num : 26176 ≤ 26240), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 26112 ≤ 26176) (by norm_num : 26176 ≤ 26240), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 26112 ≤ 26176) (by norm_num : 26176 ≤ 26240), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 26112 ≤ 26176) (by norm_num : 26176 ≤ 26240), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_26240_26304 :
    (∑ n ∈ Ico 26240 26304, mobiusTreeValue 16 mobiusTable1200001 n) = (-3 : ℤ) ∧
    (∑ n ∈ Ico 26240 26304, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 26240 26304, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-572061 : ℤ) ∧
    (∑ n ∈ Ico 26240 26304, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-11441319829125788324511847088 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_26304_26368 :
    (∑ n ∈ Ico 26304 26368, mobiusTreeValue 16 mobiusTable1200001 n) = (5 : ℤ) ∧
    (∑ n ∈ Ico 26304 26368, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 26304 26368, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (947971 : ℤ) ∧
    (∑ n ∈ Ico 26304 26368, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (18959491562756859393425196130 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_26240_26368 :
    (∑ n ∈ Ico 26240 26368, mobiusTreeValue 16 mobiusTable1200001 n) = (2 : ℤ) ∧
    (∑ n ∈ Ico 26240 26368, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 26240 26368, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (375910 : ℤ) ∧
    (∑ n ∈ Ico 26240 26368, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (7518171733631071068913349042 : ℤ) := by
  rcases cdemPrefixStats_26240_26304 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_26304_26368 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 26240 ≤ 26304) (by norm_num : 26304 ≤ 26368), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 26240 ≤ 26304) (by norm_num : 26304 ≤ 26368), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 26240 ≤ 26304) (by norm_num : 26304 ≤ 26368), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 26240 ≤ 26304) (by norm_num : 26304 ≤ 26368), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_26112_26368 :
    (∑ n ∈ Ico 26112 26368, mobiusTreeValue 16 mobiusTable1200001 n) = (3 : ℤ) ∧
    (∑ n ∈ Ico 26112 26368, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (155 : ℕ) ∧
    (∑ n ∈ Ico 26112 26368, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (564172 : ℤ) ∧
    (∑ n ∈ Ico 26112 26368, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (11283397001062604207723419601 : ℤ) := by
  rcases cdemPrefixStats_26112_26240 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_26240_26368 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 26112 ≤ 26240) (by norm_num : 26240 ≤ 26368), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 26112 ≤ 26240) (by norm_num : 26240 ≤ 26368), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 26112 ≤ 26240) (by norm_num : 26240 ≤ 26368), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 26112 ≤ 26240) (by norm_num : 26240 ≤ 26368), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_26368_26432 :
    (∑ n ∈ Ico 26368 26432, mobiusTreeValue 16 mobiusTable1200001 n) = (-9 : ℤ) ∧
    (∑ n ∈ Ico 26368 26432, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 26368 26432, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-1704072 : ℤ) ∧
    (∑ n ∈ Ico 26368 26432, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-34081458160374917252512972259 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_26432_26496 :
    (∑ n ∈ Ico 26432 26496, mobiusTreeValue 16 mobiusTable1200001 n) = (8 : ℤ) ∧
    (∑ n ∈ Ico 26432 26496, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 26432 26496, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (1511191 : ℤ) ∧
    (∑ n ∈ Ico 26432 26496, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (30223902980693249679925509218 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_26368_26496 :
    (∑ n ∈ Ico 26368 26496, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 26368 26496, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (79 : ℕ) ∧
    (∑ n ∈ Ico 26368 26496, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-192881 : ℤ) ∧
    (∑ n ∈ Ico 26368 26496, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-3857555179681667572587463041 : ℤ) := by
  rcases cdemPrefixStats_26368_26432 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_26432_26496 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 26368 ≤ 26432) (by norm_num : 26432 ≤ 26496), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 26368 ≤ 26432) (by norm_num : 26432 ≤ 26496), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 26368 ≤ 26432) (by norm_num : 26432 ≤ 26496), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 26368 ≤ 26432) (by norm_num : 26432 ≤ 26496), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_26496_26560 :
    (∑ n ∈ Ico 26496 26560, mobiusTreeValue 16 mobiusTable1200001 n) = (5 : ℤ) ∧
    (∑ n ∈ Ico 26496 26560, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 26496 26560, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (943252 : ℤ) ∧
    (∑ n ∈ Ico 26496 26560, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (18865064151808208744970211185 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_26560_26624 :
    (∑ n ∈ Ico 26560 26624, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 26560 26624, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 26560 26624, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-455 : ℤ) ∧
    (∑ n ∈ Ico 26560 26624, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-9044703840459949263469620 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_26496_26624 :
    (∑ n ∈ Ico 26496 26624, mobiusTreeValue 16 mobiusTable1200001 n) = (5 : ℤ) ∧
    (∑ n ∈ Ico 26496 26624, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 26496 26624, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (942797 : ℤ) ∧
    (∑ n ∈ Ico 26496 26624, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (18856019447967748795706741565 : ℤ) := by
  rcases cdemPrefixStats_26496_26560 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_26560_26624 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 26496 ≤ 26560) (by norm_num : 26560 ≤ 26624), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 26496 ≤ 26560) (by norm_num : 26560 ≤ 26624), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 26496 ≤ 26560) (by norm_num : 26560 ≤ 26624), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 26496 ≤ 26560) (by norm_num : 26560 ≤ 26624), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_26368_26624 :
    (∑ n ∈ Ico 26368 26624, mobiusTreeValue 16 mobiusTable1200001 n) = (4 : ℤ) ∧
    (∑ n ∈ Ico 26368 26624, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (156 : ℕ) ∧
    (∑ n ∈ Ico 26368 26624, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (749916 : ℤ) ∧
    (∑ n ∈ Ico 26368 26624, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (14998464268286081223119278524 : ℤ) := by
  rcases cdemPrefixStats_26368_26496 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_26496_26624 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 26368 ≤ 26496) (by norm_num : 26496 ≤ 26624), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 26368 ≤ 26496) (by norm_num : 26496 ≤ 26624), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 26368 ≤ 26496) (by norm_num : 26496 ≤ 26624), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 26368 ≤ 26496) (by norm_num : 26496 ≤ 26624), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_26112_26624 :
    (∑ n ∈ Ico 26112 26624, mobiusTreeValue 16 mobiusTable1200001 n) = (7 : ℤ) ∧
    (∑ n ∈ Ico 26112 26624, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (311 : ℕ) ∧
    (∑ n ∈ Ico 26112 26624, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (1314088 : ℤ) ∧
    (∑ n ∈ Ico 26112 26624, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (26281861269348685430842698125 : ℤ) := by
  rcases cdemPrefixStats_26112_26368 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_26368_26624 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 26112 ≤ 26368) (by norm_num : 26368 ≤ 26624), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 26112 ≤ 26368) (by norm_num : 26368 ≤ 26624), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 26112 ≤ 26368) (by norm_num : 26368 ≤ 26624), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 26112 ≤ 26368) (by norm_num : 26368 ≤ 26624), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_25600_26624 :
    (∑ n ∈ Ico 25600 26624, mobiusTreeValue 16 mobiusTable1200001 n) = (22 : ℤ) ∧
    (∑ n ∈ Ico 25600 26624, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (624 : ℕ) ∧
    (∑ n ∈ Ico 25600 26624, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (4194512 : ℤ) ∧
    (∑ n ∈ Ico 25600 26624, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (83890569563832915967456623598 : ℤ) := by
  rcases cdemPrefixStats_25600_26112 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_26112_26624 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 25600 ≤ 26112) (by norm_num : 26112 ≤ 26624), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 25600 ≤ 26112) (by norm_num : 26112 ≤ 26624), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 25600 ≤ 26112) (by norm_num : 26112 ≤ 26624), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 25600 ≤ 26112) (by norm_num : 26112 ≤ 26624), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_24576_26624 :
    (∑ n ∈ Ico 24576 26624, mobiusTreeValue 16 mobiusTable1200001 n) = (65 : ℤ) ∧
    (∑ n ∈ Ico 24576 26624, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (1247 : ℕ) ∧
    (∑ n ∈ Ico 24576 26624, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (12880069 : ℤ) ∧
    (∑ n ∈ Ico 24576 26624, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (257602300727632468309195097992 : ℤ) := by
  rcases cdemPrefixStats_24576_25600 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_25600_26624 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 24576 ≤ 25600) (by norm_num : 25600 ≤ 26624), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 24576 ≤ 25600) (by norm_num : 25600 ≤ 26624), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 24576 ≤ 25600) (by norm_num : 25600 ≤ 26624), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 24576 ≤ 25600) (by norm_num : 25600 ≤ 26624), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_26624_26688 :
    (∑ n ∈ Ico 26624 26688, mobiusTreeValue 16 mobiusTable1200001 n) = (-7 : ℤ) ∧
    (∑ n ∈ Ico 26624 26688, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 26624 26688, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-1312623 : ℤ) ∧
    (∑ n ∈ Ico 26624 26688, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-26252506088510530230141103116 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_26688_26752 :
    (∑ n ∈ Ico 26688 26752, mobiusTreeValue 16 mobiusTable1200001 n) = (-11 : ℤ) ∧
    (∑ n ∈ Ico 26688 26752, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 26688 26752, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-2058639 : ℤ) ∧
    (∑ n ∈ Ico 26688 26752, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-41172996141755216460563916751 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_26624_26752 :
    (∑ n ∈ Ico 26624 26752, mobiusTreeValue 16 mobiusTable1200001 n) = (-18 : ℤ) ∧
    (∑ n ∈ Ico 26624 26752, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (76 : ℕ) ∧
    (∑ n ∈ Ico 26624 26752, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-3371262 : ℤ) ∧
    (∑ n ∈ Ico 26624 26752, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-67425502230265746690705019867 : ℤ) := by
  rcases cdemPrefixStats_26624_26688 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_26688_26752 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 26624 ≤ 26688) (by norm_num : 26688 ≤ 26752), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 26624 ≤ 26688) (by norm_num : 26688 ≤ 26752), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 26624 ≤ 26688) (by norm_num : 26688 ≤ 26752), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 26624 ≤ 26688) (by norm_num : 26688 ≤ 26752), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_26752_26816 :
    (∑ n ∈ Ico 26752 26816, mobiusTreeValue 16 mobiusTable1200001 n) = (-6 : ℤ) ∧
    (∑ n ∈ Ico 26752 26816, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 26752 26816, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-1119881 : ℤ) ∧
    (∑ n ∈ Ico 26752 26816, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-22397672117474479789562286304 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_26816_26880 :
    (∑ n ∈ Ico 26816 26880, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 26816 26880, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 26816 26880, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-184966 : ℤ) ∧
    (∑ n ∈ Ico 26816 26880, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-3699285980404738657788193932 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_26752_26880 :
    (∑ n ∈ Ico 26752 26880, mobiusTreeValue 16 mobiusTable1200001 n) = (-7 : ℤ) ∧
    (∑ n ∈ Ico 26752 26880, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 26752 26880, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-1304847 : ℤ) ∧
    (∑ n ∈ Ico 26752 26880, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-26096958097879218447350480236 : ℤ) := by
  rcases cdemPrefixStats_26752_26816 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_26816_26880 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 26752 ≤ 26816) (by norm_num : 26816 ≤ 26880), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 26752 ≤ 26816) (by norm_num : 26816 ≤ 26880), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 26752 ≤ 26816) (by norm_num : 26816 ≤ 26880), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 26752 ≤ 26816) (by norm_num : 26816 ≤ 26880), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_26624_26880 :
    (∑ n ∈ Ico 26624 26880, mobiusTreeValue 16 mobiusTable1200001 n) = (-25 : ℤ) ∧
    (∑ n ∈ Ico 26624 26880, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (153 : ℕ) ∧
    (∑ n ∈ Ico 26624 26880, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-4676109 : ℤ) ∧
    (∑ n ∈ Ico 26624 26880, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-93522460328144965138055500103 : ℤ) := by
  rcases cdemPrefixStats_26624_26752 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_26752_26880 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 26624 ≤ 26752) (by norm_num : 26752 ≤ 26880), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 26624 ≤ 26752) (by norm_num : 26752 ≤ 26880), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 26624 ≤ 26752) (by norm_num : 26752 ≤ 26880), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 26624 ≤ 26752) (by norm_num : 26752 ≤ 26880), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_26880_26944 :
    (∑ n ∈ Ico 26880 26944, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 26880 26944, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 26880 26944, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (185537 : ℤ) ∧
    (∑ n ∈ Ico 26880 26944, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (3710692391151526810704370984 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_26944_27008 :
    (∑ n ∈ Ico 26944 27008, mobiusTreeValue 16 mobiusTable1200001 n) = (2 : ℤ) ∧
    (∑ n ∈ Ico 26944 27008, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 26944 27008, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (369719 : ℤ) ∧
    (∑ n ∈ Ico 26944 27008, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (7394340154042562514328076989 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_26880_27008 :
    (∑ n ∈ Ico 26880 27008, mobiusTreeValue 16 mobiusTable1200001 n) = (3 : ℤ) ∧
    (∑ n ∈ Ico 26880 27008, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (79 : ℕ) ∧
    (∑ n ∈ Ico 26880 27008, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (555256 : ℤ) ∧
    (∑ n ∈ Ico 26880 27008, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (11105032545194089325032447973 : ℤ) := by
  rcases cdemPrefixStats_26880_26944 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_26944_27008 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 26880 ≤ 26944) (by norm_num : 26944 ≤ 27008), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 26880 ≤ 26944) (by norm_num : 26944 ≤ 27008), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 26880 ≤ 26944) (by norm_num : 26944 ≤ 27008), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 26880 ≤ 26944) (by norm_num : 26944 ≤ 27008), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_27008_27072 :
    (∑ n ∈ Ico 27008 27072, mobiusTreeValue 16 mobiusTable1200001 n) = (-8 : ℤ) ∧
    (∑ n ∈ Ico 27008 27072, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 27008 27072, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-1478432 : ℤ) ∧
    (∑ n ∈ Ico 27008 27072, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-29568731566933757547257748440 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_27072_27136 :
    (∑ n ∈ Ico 27072 27136, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 27072 27136, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 27072 27136, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (183447 : ℤ) ∧
    (∑ n ∈ Ico 27072 27136, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (3668944025436291530771803133 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_27008_27136 :
    (∑ n ∈ Ico 27008 27136, mobiusTreeValue 16 mobiusTable1200001 n) = (-7 : ℤ) ∧
    (∑ n ∈ Ico 27008 27136, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (79 : ℕ) ∧
    (∑ n ∈ Ico 27008 27136, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-1294985 : ℤ) ∧
    (∑ n ∈ Ico 27008 27136, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-25899787541497466016485945307 : ℤ) := by
  rcases cdemPrefixStats_27008_27072 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_27072_27136 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 27008 ≤ 27072) (by norm_num : 27072 ≤ 27136), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 27008 ≤ 27072) (by norm_num : 27072 ≤ 27136), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 27008 ≤ 27072) (by norm_num : 27072 ≤ 27136), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 27008 ≤ 27072) (by norm_num : 27072 ≤ 27136), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_26880_27136 :
    (∑ n ∈ Ico 26880 27136, mobiusTreeValue 16 mobiusTable1200001 n) = (-4 : ℤ) ∧
    (∑ n ∈ Ico 26880 27136, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (158 : ℕ) ∧
    (∑ n ∈ Ico 26880 27136, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-739729 : ℤ) ∧
    (∑ n ∈ Ico 26880 27136, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-14794754996303376691453497334 : ℤ) := by
  rcases cdemPrefixStats_26880_27008 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_27008_27136 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 26880 ≤ 27008) (by norm_num : 27008 ≤ 27136), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 26880 ≤ 27008) (by norm_num : 27008 ≤ 27136), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 26880 ≤ 27008) (by norm_num : 27008 ≤ 27136), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 26880 ≤ 27008) (by norm_num : 27008 ≤ 27136), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_26624_27136 :
    (∑ n ∈ Ico 26624 27136, mobiusTreeValue 16 mobiusTable1200001 n) = (-29 : ℤ) ∧
    (∑ n ∈ Ico 26624 27136, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (311 : ℕ) ∧
    (∑ n ∈ Ico 26624 27136, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-5415838 : ℤ) ∧
    (∑ n ∈ Ico 26624 27136, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-108317215324448341829508997437 : ℤ) := by
  rcases cdemPrefixStats_26624_26880 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_26880_27136 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 26624 ≤ 26880) (by norm_num : 26880 ≤ 27136), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 26624 ≤ 26880) (by norm_num : 26880 ≤ 27136), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 26624 ≤ 26880) (by norm_num : 26880 ≤ 27136), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 26624 ≤ 26880) (by norm_num : 26880 ≤ 27136), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_27136_27200 :
    (∑ n ∈ Ico 27136 27200, mobiusTreeValue 16 mobiusTable1200001 n) = (8 : ℤ) ∧
    (∑ n ∈ Ico 27136 27200, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 27136 27200, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (1471903 : ℤ) ∧
    (∑ n ∈ Ico 27136 27200, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (29438149836356265327313944922 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_27200_27264 :
    (∑ n ∈ Ico 27200 27264, mobiusTreeValue 16 mobiusTable1200001 n) = (5 : ℤ) ∧
    (∑ n ∈ Ico 27200 27264, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 27200 27264, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (918906 : ℤ) ∧
    (∑ n ∈ Ico 27200 27264, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (18378158229818022986638854725 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_27136_27264 :
    (∑ n ∈ Ico 27136 27264, mobiusTreeValue 16 mobiusTable1200001 n) = (13 : ℤ) ∧
    (∑ n ∈ Ico 27136 27264, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (79 : ℕ) ∧
    (∑ n ∈ Ico 27136 27264, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (2390809 : ℤ) ∧
    (∑ n ∈ Ico 27136 27264, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (47816308066174288313952799647 : ℤ) := by
  rcases cdemPrefixStats_27136_27200 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_27200_27264 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 27136 ≤ 27200) (by norm_num : 27200 ≤ 27264), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 27136 ≤ 27200) (by norm_num : 27200 ≤ 27264), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 27136 ≤ 27200) (by norm_num : 27200 ≤ 27264), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 27136 ≤ 27200) (by norm_num : 27200 ≤ 27264), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_27264_27328 :
    (∑ n ∈ Ico 27264 27328, mobiusTreeValue 16 mobiusTable1200001 n) = (-8 : ℤ) ∧
    (∑ n ∈ Ico 27264 27328, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 27264 27328, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-1466083 : ℤ) ∧
    (∑ n ∈ Ico 27264 27328, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-29321750733293811084716387214 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_27328_27392 :
    (∑ n ∈ Ico 27328 27392, mobiusTreeValue 16 mobiusTable1200001 n) = (8 : ℤ) ∧
    (∑ n ∈ Ico 27328 27392, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 27328 27392, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (1461455 : ℤ) ∧
    (∑ n ∈ Ico 27328 27392, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (29229096699306710003591064700 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_27264_27392 :
    (∑ n ∈ Ico 27264 27392, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 27264 27392, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 27264 27392, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-4628 : ℤ) ∧
    (∑ n ∈ Ico 27264 27392, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-92654033987101081125322514 : ℤ) := by
  rcases cdemPrefixStats_27264_27328 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_27328_27392 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 27264 ≤ 27328) (by norm_num : 27328 ≤ 27392), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 27264 ≤ 27328) (by norm_num : 27328 ≤ 27392), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 27264 ≤ 27328) (by norm_num : 27328 ≤ 27392), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 27264 ≤ 27328) (by norm_num : 27328 ≤ 27392), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_27136_27392 :
    (∑ n ∈ Ico 27136 27392, mobiusTreeValue 16 mobiusTable1200001 n) = (13 : ℤ) ∧
    (∑ n ∈ Ico 27136 27392, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (157 : ℕ) ∧
    (∑ n ∈ Ico 27136 27392, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (2386181 : ℤ) ∧
    (∑ n ∈ Ico 27136 27392, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (47723654032187187232827477133 : ℤ) := by
  rcases cdemPrefixStats_27136_27264 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_27264_27392 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 27136 ≤ 27264) (by norm_num : 27264 ≤ 27392), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 27136 ≤ 27264) (by norm_num : 27264 ≤ 27392), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 27136 ≤ 27264) (by norm_num : 27264 ≤ 27392), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 27136 ≤ 27264) (by norm_num : 27264 ≤ 27392), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_27392_27456 :
    (∑ n ∈ Ico 27392 27456, mobiusTreeValue 16 mobiusTable1200001 n) = (11 : ℤ) ∧
    (∑ n ∈ Ico 27392 27456, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 27392 27456, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (2004906 : ℤ) ∧
    (∑ n ∈ Ico 27392 27456, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (40098233644717704747486096673 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_27456_27520 :
    (∑ n ∈ Ico 27456 27520, mobiusTreeValue 16 mobiusTable1200001 n) = (6 : ℤ) ∧
    (∑ n ∈ Ico 27456 27520, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 27456 27520, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (1091471 : ℤ) ∧
    (∑ n ∈ Ico 27456 27520, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (21829450139012606552729964268 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_27392_27520 :
    (∑ n ∈ Ico 27392 27520, mobiusTreeValue 16 mobiusTable1200001 n) = (17 : ℤ) ∧
    (∑ n ∈ Ico 27392 27520, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (81 : ℕ) ∧
    (∑ n ∈ Ico 27392 27520, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (3096377 : ℤ) ∧
    (∑ n ∈ Ico 27392 27520, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (61927683783730311300216060941 : ℤ) := by
  rcases cdemPrefixStats_27392_27456 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_27456_27520 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 27392 ≤ 27456) (by norm_num : 27456 ≤ 27520), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 27392 ≤ 27456) (by norm_num : 27456 ≤ 27520), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 27392 ≤ 27456) (by norm_num : 27456 ≤ 27520), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 27392 ≤ 27456) (by norm_num : 27456 ≤ 27520), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_27520_27584 :
    (∑ n ∈ Ico 27520 27584, mobiusTreeValue 16 mobiusTable1200001 n) = (-2 : ℤ) ∧
    (∑ n ∈ Ico 27520 27584, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 27520 27584, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-363041 : ℤ) ∧
    (∑ n ∈ Ico 27520 27584, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-7260859112006752692184973685 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_27584_27648 :
    (∑ n ∈ Ico 27584 27648, mobiusTreeValue 16 mobiusTable1200001 n) = (8 : ℤ) ∧
    (∑ n ∈ Ico 27584 27648, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 27584 27648, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (1449298 : ℤ) ∧
    (∑ n ∈ Ico 27584 27648, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (28986026243040158437564444059 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_27520_27648 :
    (∑ n ∈ Ico 27520 27648, mobiusTreeValue 16 mobiusTable1200001 n) = (6 : ℤ) ∧
    (∑ n ∈ Ico 27520 27648, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 27520 27648, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (1086257 : ℤ) ∧
    (∑ n ∈ Ico 27520 27648, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (21725167131033405745379470374 : ℤ) := by
  rcases cdemPrefixStats_27520_27584 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_27584_27648 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 27520 ≤ 27584) (by norm_num : 27584 ≤ 27648), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 27520 ≤ 27584) (by norm_num : 27584 ≤ 27648), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 27520 ≤ 27584) (by norm_num : 27584 ≤ 27648), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 27520 ≤ 27584) (by norm_num : 27584 ≤ 27648), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_27392_27648 :
    (∑ n ∈ Ico 27392 27648, mobiusTreeValue 16 mobiusTable1200001 n) = (23 : ℤ) ∧
    (∑ n ∈ Ico 27392 27648, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (159 : ℕ) ∧
    (∑ n ∈ Ico 27392 27648, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (4182634 : ℤ) ∧
    (∑ n ∈ Ico 27392 27648, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (83652850914763717045595531315 : ℤ) := by
  rcases cdemPrefixStats_27392_27520 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_27520_27648 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 27392 ≤ 27520) (by norm_num : 27520 ≤ 27648), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 27392 ≤ 27520) (by norm_num : 27520 ≤ 27648), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 27392 ≤ 27520) (by norm_num : 27520 ≤ 27648), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 27392 ≤ 27520) (by norm_num : 27520 ≤ 27648), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_27136_27648 :
    (∑ n ∈ Ico 27136 27648, mobiusTreeValue 16 mobiusTable1200001 n) = (36 : ℤ) ∧
    (∑ n ∈ Ico 27136 27648, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (316 : ℕ) ∧
    (∑ n ∈ Ico 27136 27648, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (6568815 : ℤ) ∧
    (∑ n ∈ Ico 27136 27648, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (131376504946950904278423008448 : ℤ) := by
  rcases cdemPrefixStats_27136_27392 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_27392_27648 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 27136 ≤ 27392) (by norm_num : 27392 ≤ 27648), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 27136 ≤ 27392) (by norm_num : 27392 ≤ 27648), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 27136 ≤ 27392) (by norm_num : 27392 ≤ 27648), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 27136 ≤ 27392) (by norm_num : 27392 ≤ 27648), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_26624_27648 :
    (∑ n ∈ Ico 26624 27648, mobiusTreeValue 16 mobiusTable1200001 n) = (7 : ℤ) ∧
    (∑ n ∈ Ico 26624 27648, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (627 : ℕ) ∧
    (∑ n ∈ Ico 26624 27648, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (1152977 : ℤ) ∧
    (∑ n ∈ Ico 26624 27648, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (23059289622502562448914011011 : ℤ) := by
  rcases cdemPrefixStats_26624_27136 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_27136_27648 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 26624 ≤ 27136) (by norm_num : 27136 ≤ 27648), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 26624 ≤ 27136) (by norm_num : 27136 ≤ 27648), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 26624 ≤ 27136) (by norm_num : 27136 ≤ 27648), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 26624 ≤ 27136) (by norm_num : 27136 ≤ 27648), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_27648_27712 :
    (∑ n ∈ Ico 27648 27712, mobiusTreeValue 16 mobiusTable1200001 n) = (-5 : ℤ) ∧
    (∑ n ∈ Ico 27648 27712, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 27648 27712, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-901861 : ℤ) ∧
    (∑ n ∈ Ico 27648 27712, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-18037215590629319453265938438 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_27712_27776 :
    (∑ n ∈ Ico 27712 27776, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 27712 27776, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 27712 27776, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-179975 : ℤ) ∧
    (∑ n ∈ Ico 27712 27776, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-3599571727003225890988161997 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_27648_27776 :
    (∑ n ∈ Ico 27648 27776, mobiusTreeValue 16 mobiusTable1200001 n) = (-6 : ℤ) ∧
    (∑ n ∈ Ico 27648 27776, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (76 : ℕ) ∧
    (∑ n ∈ Ico 27648 27776, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-1081836 : ℤ) ∧
    (∑ n ∈ Ico 27648 27776, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-21636787317632545344254100435 : ℤ) := by
  rcases cdemPrefixStats_27648_27712 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_27712_27776 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 27648 ≤ 27712) (by norm_num : 27712 ≤ 27776), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 27648 ≤ 27712) (by norm_num : 27712 ≤ 27776), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 27648 ≤ 27712) (by norm_num : 27712 ≤ 27776), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 27648 ≤ 27712) (by norm_num : 27712 ≤ 27776), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_27776_27840 :
    (∑ n ∈ Ico 27776 27840, mobiusTreeValue 16 mobiusTable1200001 n) = (-4 : ℤ) ∧
    (∑ n ∈ Ico 27776 27840, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 27776 27840, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-718684 : ℤ) ∧
    (∑ n ∈ Ico 27776 27840, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-14373755181867438875570654395 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_27840_27904 :
    (∑ n ∈ Ico 27840 27904, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 27840 27904, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 27840 27904, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-177974 : ℤ) ∧
    (∑ n ∈ Ico 27840 27904, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-3559516870421435999473567951 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_27776_27904 :
    (∑ n ∈ Ico 27776 27904, mobiusTreeValue 16 mobiusTable1200001 n) = (-5 : ℤ) ∧
    (∑ n ∈ Ico 27776 27904, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 27776 27904, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-896658 : ℤ) ∧
    (∑ n ∈ Ico 27776 27904, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-17933272052288874875044222346 : ℤ) := by
  rcases cdemPrefixStats_27776_27840 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_27840_27904 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 27776 ≤ 27840) (by norm_num : 27840 ≤ 27904), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 27776 ≤ 27840) (by norm_num : 27840 ≤ 27904), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 27776 ≤ 27840) (by norm_num : 27840 ≤ 27904), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 27776 ≤ 27840) (by norm_num : 27840 ≤ 27904), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_27648_27904 :
    (∑ n ∈ Ico 27648 27904, mobiusTreeValue 16 mobiusTable1200001 n) = (-11 : ℤ) ∧
    (∑ n ∈ Ico 27648 27904, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (153 : ℕ) ∧
    (∑ n ∈ Ico 27648 27904, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-1978494 : ℤ) ∧
    (∑ n ∈ Ico 27648 27904, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-39570059369921420219298322781 : ℤ) := by
  rcases cdemPrefixStats_27648_27776 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_27776_27904 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 27648 ≤ 27776) (by norm_num : 27776 ≤ 27904), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 27648 ≤ 27776) (by norm_num : 27776 ≤ 27904), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 27648 ≤ 27776) (by norm_num : 27776 ≤ 27904), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 27648 ≤ 27776) (by norm_num : 27776 ≤ 27904), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_27904_27968 :
    (∑ n ∈ Ico 27904 27968, mobiusTreeValue 16 mobiusTable1200001 n) = (-10 : ℤ) ∧
    (∑ n ∈ Ico 27904 27968, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 27904 27968, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-1790800 : ℤ) ∧
    (∑ n ∈ Ico 27904 27968, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-35816103947452133625615881253 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_27968_28032 :
    (∑ n ∈ Ico 27968 28032, mobiusTreeValue 16 mobiusTable1200001 n) = (2 : ℤ) ∧
    (∑ n ∈ Ico 27968 28032, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 27968 28032, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (356951 : ℤ) ∧
    (∑ n ∈ Ico 27968 28032, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (7139028996648650481822699926 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_27904_28032 :
    (∑ n ∈ Ico 27904 28032, mobiusTreeValue 16 mobiusTable1200001 n) = (-8 : ℤ) ∧
    (∑ n ∈ Ico 27904 28032, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 27904 28032, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-1433849 : ℤ) ∧
    (∑ n ∈ Ico 27904 28032, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-28677074950803483143793181327 : ℤ) := by
  rcases cdemPrefixStats_27904_27968 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_27968_28032 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 27904 ≤ 27968) (by norm_num : 27968 ≤ 28032), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 27904 ≤ 27968) (by norm_num : 27968 ≤ 28032), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 27904 ≤ 27968) (by norm_num : 27968 ≤ 28032), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 27904 ≤ 27968) (by norm_num : 27968 ≤ 28032), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_28032_28096 :
    (∑ n ∈ Ico 28032 28096, mobiusTreeValue 16 mobiusTable1200001 n) = (-8 : ℤ) ∧
    (∑ n ∈ Ico 28032 28096, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (36 : ℕ) ∧
    (∑ n ∈ Ico 28032 28096, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-1425572 : ℤ) ∧
    (∑ n ∈ Ico 28032 28096, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-28511617638816762714302075487 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_28096_28160 :
    (∑ n ∈ Ico 28096 28160, mobiusTreeValue 16 mobiusTable1200001 n) = (10 : ℤ) ∧
    (∑ n ∈ Ico 28096 28160, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 28096 28160, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (1778285 : ℤ) ∧
    (∑ n ∈ Ico 28096 28160, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (35565800891140357991802704940 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_28032_28160 :
    (∑ n ∈ Ico 28032 28160, mobiusTreeValue 16 mobiusTable1200001 n) = (2 : ℤ) ∧
    (∑ n ∈ Ico 28032 28160, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (76 : ℕ) ∧
    (∑ n ∈ Ico 28032 28160, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (352713 : ℤ) ∧
    (∑ n ∈ Ico 28032 28160, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (7054183252323595277500629453 : ℤ) := by
  rcases cdemPrefixStats_28032_28096 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_28096_28160 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 28032 ≤ 28096) (by norm_num : 28096 ≤ 28160), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 28032 ≤ 28096) (by norm_num : 28096 ≤ 28160), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 28032 ≤ 28096) (by norm_num : 28096 ≤ 28160), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 28032 ≤ 28096) (by norm_num : 28096 ≤ 28160), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_27904_28160 :
    (∑ n ∈ Ico 27904 28160, mobiusTreeValue 16 mobiusTable1200001 n) = (-6 : ℤ) ∧
    (∑ n ∈ Ico 27904 28160, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (154 : ℕ) ∧
    (∑ n ∈ Ico 27904 28160, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-1081136 : ℤ) ∧
    (∑ n ∈ Ico 27904 28160, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-21622891698479887866292551874 : ℤ) := by
  rcases cdemPrefixStats_27904_28032 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_28032_28160 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 27904 ≤ 28032) (by norm_num : 28032 ≤ 28160), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 27904 ≤ 28032) (by norm_num : 28032 ≤ 28160), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 27904 ≤ 28032) (by norm_num : 28032 ≤ 28160), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 27904 ≤ 28032) (by norm_num : 28032 ≤ 28160), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_27648_28160 :
    (∑ n ∈ Ico 27648 28160, mobiusTreeValue 16 mobiusTable1200001 n) = (-17 : ℤ) ∧
    (∑ n ∈ Ico 27648 28160, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (307 : ℕ) ∧
    (∑ n ∈ Ico 27648 28160, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-3059630 : ℤ) ∧
    (∑ n ∈ Ico 27648 28160, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-61192951068401308085590874655 : ℤ) := by
  rcases cdemPrefixStats_27648_27904 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_27904_28160 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 27648 ≤ 27904) (by norm_num : 27904 ≤ 28160), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 27648 ≤ 27904) (by norm_num : 27904 ≤ 28160), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 27648 ≤ 27904) (by norm_num : 27904 ≤ 28160), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 27648 ≤ 27904) (by norm_num : 27904 ≤ 28160), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_28160_28224 :
    (∑ n ∈ Ico 28160 28224, mobiusTreeValue 16 mobiusTable1200001 n) = (-3 : ℤ) ∧
    (∑ n ∈ Ico 28160 28224, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 28160 28224, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-531644 : ℤ) ∧
    (∑ n ∈ Ico 28160 28224, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-10632900394783368544924289740 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_28224_28288 :
    (∑ n ∈ Ico 28224 28288, mobiusTreeValue 16 mobiusTable1200001 n) = (3 : ℤ) ∧
    (∑ n ∈ Ico 28224 28288, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 28224 28288, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (530733 : ℤ) ∧
    (∑ n ∈ Ico 28224 28288, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (10614698439255177974523398915 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_28160_28288 :
    (∑ n ∈ Ico 28160 28288, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 28160 28288, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (76 : ℕ) ∧
    (∑ n ∈ Ico 28160 28288, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-911 : ℤ) ∧
    (∑ n ∈ Ico 28160 28288, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-18201955528190570400890825 : ℤ) := by
  rcases cdemPrefixStats_28160_28224 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_28224_28288 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 28160 ≤ 28224) (by norm_num : 28224 ≤ 28288), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 28160 ≤ 28224) (by norm_num : 28224 ≤ 28288), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 28160 ≤ 28224) (by norm_num : 28224 ≤ 28288), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 28160 ≤ 28224) (by norm_num : 28224 ≤ 28288), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_28288_28352 :
    (∑ n ∈ Ico 28288 28352, mobiusTreeValue 16 mobiusTable1200001 n) = (5 : ℤ) ∧
    (∑ n ∈ Ico 28288 28352, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 28288 28352, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (883288 : ℤ) ∧
    (∑ n ∈ Ico 28288 28352, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (17665841679569391638035298412 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_28352_28416 :
    (∑ n ∈ Ico 28352 28416, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 28352 28416, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 28352 28416, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (176418 : ℤ) ∧
    (∑ n ∈ Ico 28352 28416, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (3528330730827430886619114838 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_28288_28416 :
    (∑ n ∈ Ico 28288 28416, mobiusTreeValue 16 mobiusTable1200001 n) = (6 : ℤ) ∧
    (∑ n ∈ Ico 28288 28416, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (82 : ℕ) ∧
    (∑ n ∈ Ico 28288 28416, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (1059706 : ℤ) ∧
    (∑ n ∈ Ico 28288 28416, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (21194172410396822524654413250 : ℤ) := by
  rcases cdemPrefixStats_28288_28352 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_28352_28416 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 28288 ≤ 28352) (by norm_num : 28352 ≤ 28416), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 28288 ≤ 28352) (by norm_num : 28352 ≤ 28416), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 28288 ≤ 28352) (by norm_num : 28352 ≤ 28416), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 28288 ≤ 28352) (by norm_num : 28352 ≤ 28416), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_28160_28416 :
    (∑ n ∈ Ico 28160 28416, mobiusTreeValue 16 mobiusTable1200001 n) = (6 : ℤ) ∧
    (∑ n ∈ Ico 28160 28416, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (158 : ℕ) ∧
    (∑ n ∈ Ico 28160 28416, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (1058795 : ℤ) ∧
    (∑ n ∈ Ico 28160 28416, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (21175970454868631954253522425 : ℤ) := by
  rcases cdemPrefixStats_28160_28288 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_28288_28416 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 28160 ≤ 28288) (by norm_num : 28288 ≤ 28416), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 28160 ≤ 28288) (by norm_num : 28288 ≤ 28416), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 28160 ≤ 28288) (by norm_num : 28288 ≤ 28416), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 28160 ≤ 28288) (by norm_num : 28288 ≤ 28416), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_28416_28480 :
    (∑ n ∈ Ico 28416 28480, mobiusTreeValue 16 mobiusTable1200001 n) = (-4 : ℤ) ∧
    (∑ n ∈ Ico 28416 28480, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 28416 28480, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-702511 : ℤ) ∧
    (∑ n ∈ Ico 28416 28480, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-14050249429658238420848755226 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_28480_28544 :
    (∑ n ∈ Ico 28480 28544, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 28480 28544, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 28480 28544, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-174000 : ℤ) ∧
    (∑ n ∈ Ico 28480 28544, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-3479986193159455791033246321 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_28416_28544 :
    (∑ n ∈ Ico 28416 28544, mobiusTreeValue 16 mobiusTable1200001 n) = (-5 : ℤ) ∧
    (∑ n ∈ Ico 28416 28544, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 28416 28544, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-876511 : ℤ) ∧
    (∑ n ∈ Ico 28416 28544, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-17530235622817694211882001547 : ℤ) := by
  rcases cdemPrefixStats_28416_28480 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_28480_28544 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 28416 ≤ 28480) (by norm_num : 28480 ≤ 28544), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 28416 ≤ 28480) (by norm_num : 28480 ≤ 28544), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 28416 ≤ 28480) (by norm_num : 28480 ≤ 28544), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 28416 ≤ 28480) (by norm_num : 28480 ≤ 28544), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_28544_28608 :
    (∑ n ∈ Ico 28544 28608, mobiusTreeValue 16 mobiusTable1200001 n) = (-8 : ℤ) ∧
    (∑ n ∈ Ico 28544 28608, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 28544 28608, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-1400091 : ℤ) ∧
    (∑ n ∈ Ico 28544 28608, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-28001902943649139153709361221 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_28608_28672 :
    (∑ n ∈ Ico 28608 28672, mobiusTreeValue 16 mobiusTable1200001 n) = (-5 : ℤ) ∧
    (∑ n ∈ Ico 28608 28672, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 28608 28672, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-873362 : ℤ) ∧
    (∑ n ∈ Ico 28608 28672, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-17467264595217859222387872274 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_28544_28672 :
    (∑ n ∈ Ico 28544 28672, mobiusTreeValue 16 mobiusTable1200001 n) = (-13 : ℤ) ∧
    (∑ n ∈ Ico 28544 28672, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (79 : ℕ) ∧
    (∑ n ∈ Ico 28544 28672, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-2273453 : ℤ) ∧
    (∑ n ∈ Ico 28544 28672, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-45469167538866998376097233495 : ℤ) := by
  rcases cdemPrefixStats_28544_28608 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_28608_28672 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 28544 ≤ 28608) (by norm_num : 28608 ≤ 28672), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 28544 ≤ 28608) (by norm_num : 28608 ≤ 28672), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 28544 ≤ 28608) (by norm_num : 28608 ≤ 28672), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 28544 ≤ 28608) (by norm_num : 28608 ≤ 28672), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_28416_28672 :
    (∑ n ∈ Ico 28416 28672, mobiusTreeValue 16 mobiusTable1200001 n) = (-18 : ℤ) ∧
    (∑ n ∈ Ico 28416 28672, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (156 : ℕ) ∧
    (∑ n ∈ Ico 28416 28672, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-3149964 : ℤ) ∧
    (∑ n ∈ Ico 28416 28672, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-62999403161684692587979235042 : ℤ) := by
  rcases cdemPrefixStats_28416_28544 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_28544_28672 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 28416 ≤ 28544) (by norm_num : 28544 ≤ 28672), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 28416 ≤ 28544) (by norm_num : 28544 ≤ 28672), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 28416 ≤ 28544) (by norm_num : 28544 ≤ 28672), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 28416 ≤ 28544) (by norm_num : 28544 ≤ 28672), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_28160_28672 :
    (∑ n ∈ Ico 28160 28672, mobiusTreeValue 16 mobiusTable1200001 n) = (-12 : ℤ) ∧
    (∑ n ∈ Ico 28160 28672, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (314 : ℕ) ∧
    (∑ n ∈ Ico 28160 28672, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-2091169 : ℤ) ∧
    (∑ n ∈ Ico 28160 28672, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-41823432706816060633725712617 : ℤ) := by
  rcases cdemPrefixStats_28160_28416 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_28416_28672 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 28160 ≤ 28416) (by norm_num : 28416 ≤ 28672), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 28160 ≤ 28416) (by norm_num : 28416 ≤ 28672), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 28160 ≤ 28416) (by norm_num : 28416 ≤ 28672), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 28160 ≤ 28416) (by norm_num : 28416 ≤ 28672), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_27648_28672 :
    (∑ n ∈ Ico 27648 28672, mobiusTreeValue 16 mobiusTable1200001 n) = (-29 : ℤ) ∧
    (∑ n ∈ Ico 27648 28672, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (621 : ℕ) ∧
    (∑ n ∈ Ico 27648 28672, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-5150799 : ℤ) ∧
    (∑ n ∈ Ico 27648 28672, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-103016383775217368719316587272 : ℤ) := by
  rcases cdemPrefixStats_27648_28160 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_28160_28672 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 27648 ≤ 28160) (by norm_num : 28160 ≤ 28672), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 27648 ≤ 28160) (by norm_num : 28160 ≤ 28672), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 27648 ≤ 28160) (by norm_num : 28160 ≤ 28672), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 27648 ≤ 28160) (by norm_num : 28160 ≤ 28672), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_26624_28672 :
    (∑ n ∈ Ico 26624 28672, mobiusTreeValue 16 mobiusTable1200001 n) = (-22 : ℤ) ∧
    (∑ n ∈ Ico 26624 28672, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (1248 : ℕ) ∧
    (∑ n ∈ Ico 26624 28672, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-3997822 : ℤ) ∧
    (∑ n ∈ Ico 26624 28672, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-79957094152714806270402576261 : ℤ) := by
  rcases cdemPrefixStats_26624_27648 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_27648_28672 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 26624 ≤ 27648) (by norm_num : 27648 ≤ 28672), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 26624 ≤ 27648) (by norm_num : 27648 ≤ 28672), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 26624 ≤ 27648) (by norm_num : 27648 ≤ 28672), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 26624 ≤ 27648) (by norm_num : 27648 ≤ 28672), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_24576_28672 :
    (∑ n ∈ Ico 24576 28672, mobiusTreeValue 16 mobiusTable1200001 n) = (43 : ℤ) ∧
    (∑ n ∈ Ico 24576 28672, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (2495 : ℕ) ∧
    (∑ n ∈ Ico 24576 28672, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (8882247 : ℤ) ∧
    (∑ n ∈ Ico 24576 28672, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (177645206574917662038792521731 : ℤ) := by
  rcases cdemPrefixStats_24576_26624 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_26624_28672 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 24576 ≤ 26624) (by norm_num : 26624 ≤ 28672), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 24576 ≤ 26624) (by norm_num : 26624 ≤ 28672), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 24576 ≤ 26624) (by norm_num : 26624 ≤ 28672), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 24576 ≤ 26624) (by norm_num : 26624 ≤ 28672), hR1, hR2] <;> norm_num

theorem cdemPrefixGroup006_checked_complete :
    (∑ n ∈ Ico 24576 28672, mobiusTreeValue 16 mobiusTable1200001 n) = (43 : ℤ) ∧
    (∑ n ∈ Ico 24576 28672, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (2495 : ℕ) ∧
    (∑ n ∈ Ico 24576 28672, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (8882247 : ℤ) ∧
    (∑ n ∈ Ico 24576 28672, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (177645206574917662038792521731 : ℤ) := cdemPrefixStats_24576_28672
end Helfgott
#print axioms Helfgott.cdemPrefixGroup006_checked_complete

open Helfgott Finset
open scoped BigOperators

theorem solution :
    (∑ n ∈ Ico 24576 28672, mobiusTreeValue 16 mobiusTable1200001 n) = (43 : ℤ) ∧
    (∑ n ∈ Ico 24576 28672, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (2495 : ℕ) ∧
    (∑ n ∈ Ico 24576 28672, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (8882247 : ℤ) ∧
    (∑ n ∈ Ico 24576 28672, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (177645206574917662038792521731 : ℤ) := Helfgott.cdemPrefixGroup006_checked_complete
#print axioms solution
