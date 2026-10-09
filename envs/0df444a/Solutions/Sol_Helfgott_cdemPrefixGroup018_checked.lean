-- Prove2me | solution 1 for Helfgott.cdemPrefixGroup018_checked
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-09T01:51:14.197496+00:00
-- url     : https://prove2.me/submissions/ca9cf831-624c-4bcb-af0f-0d123d6becf5

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
private theorem cdemPrefixStats_73728_73792 :
    (∑ n ∈ Ico 73728 73792, mobiusTreeValue 16 mobiusTable1200001 n) = (7 : ℤ) ∧
    (∑ n ∈ Ico 73728 73792, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 73728 73792, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (474651 : ℤ) ∧
    (∑ n ∈ Ico 73728 73792, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (9493143471895912549543656391 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_73792_73856 :
    (∑ n ∈ Ico 73792 73856, mobiusTreeValue 16 mobiusTable1200001 n) = (3 : ℤ) ∧
    (∑ n ∈ Ico 73792 73856, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 73792 73856, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (203207 : ℤ) ∧
    (∑ n ∈ Ico 73792 73856, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (4064160061360384077344167947 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_73728_73856 :
    (∑ n ∈ Ico 73728 73856, mobiusTreeValue 16 mobiusTable1200001 n) = (10 : ℤ) ∧
    (∑ n ∈ Ico 73728 73856, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (76 : ℕ) ∧
    (∑ n ∈ Ico 73728 73856, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (677858 : ℤ) ∧
    (∑ n ∈ Ico 73728 73856, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (13557303533256296626887824338 : ℤ) := by
  rcases cdemPrefixStats_73728_73792 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_73792_73856 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 73728 ≤ 73792) (by norm_num : 73792 ≤ 73856), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 73728 ≤ 73792) (by norm_num : 73792 ≤ 73856), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 73728 ≤ 73792) (by norm_num : 73792 ≤ 73856), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 73728 ≤ 73792) (by norm_num : 73792 ≤ 73856), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_73856_73920 :
    (∑ n ∈ Ico 73856 73920, mobiusTreeValue 16 mobiusTable1200001 n) = (12 : ℤ) ∧
    (∑ n ∈ Ico 73856 73920, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (42 : ℕ) ∧
    (∑ n ∈ Ico 73856 73920, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (811993 : ℤ) ∧
    (∑ n ∈ Ico 73856 73920, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (16239900390610921868922489253 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_73920_73984 :
    (∑ n ∈ Ico 73920 73984, mobiusTreeValue 16 mobiusTable1200001 n) = (-9 : ℤ) ∧
    (∑ n ∈ Ico 73920 73984, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 73920 73984, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-608623 : ℤ) ∧
    (∑ n ∈ Ico 73920 73984, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-12172506964318175542909156719 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_73856_73984 :
    (∑ n ∈ Ico 73856 73984, mobiusTreeValue 16 mobiusTable1200001 n) = (3 : ℤ) ∧
    (∑ n ∈ Ico 73856 73984, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (79 : ℕ) ∧
    (∑ n ∈ Ico 73856 73984, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (203370 : ℤ) ∧
    (∑ n ∈ Ico 73856 73984, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (4067393426292746326013332534 : ℤ) := by
  rcases cdemPrefixStats_73856_73920 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_73920_73984 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 73856 ≤ 73920) (by norm_num : 73920 ≤ 73984), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 73856 ≤ 73920) (by norm_num : 73920 ≤ 73984), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 73856 ≤ 73920) (by norm_num : 73920 ≤ 73984), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 73856 ≤ 73920) (by norm_num : 73920 ≤ 73984), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_73728_73984 :
    (∑ n ∈ Ico 73728 73984, mobiusTreeValue 16 mobiusTable1200001 n) = (13 : ℤ) ∧
    (∑ n ∈ Ico 73728 73984, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (155 : ℕ) ∧
    (∑ n ∈ Ico 73728 73984, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (881228 : ℤ) ∧
    (∑ n ∈ Ico 73728 73984, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (17624696959549042952901156872 : ℤ) := by
  rcases cdemPrefixStats_73728_73856 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_73856_73984 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 73728 ≤ 73856) (by norm_num : 73856 ≤ 73984), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 73728 ≤ 73856) (by norm_num : 73856 ≤ 73984), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 73728 ≤ 73856) (by norm_num : 73856 ≤ 73984), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 73728 ≤ 73856) (by norm_num : 73856 ≤ 73984), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_73984_74048 :
    (∑ n ∈ Ico 73984 74048, mobiusTreeValue 16 mobiusTable1200001 n) = (5 : ℤ) ∧
    (∑ n ∈ Ico 73984 74048, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 73984 74048, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (337793 : ℤ) ∧
    (∑ n ∈ Ico 73984 74048, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (6755898825701088489987458076 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_74048_74112 :
    (∑ n ∈ Ico 74048 74112, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 74048 74112, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 74048 74112, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-67592 : ℤ) ∧
    (∑ n ∈ Ico 74048 74112, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-1351787352038031432954706715 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_73984_74112 :
    (∑ n ∈ Ico 73984 74112, mobiusTreeValue 16 mobiusTable1200001 n) = (4 : ℤ) ∧
    (∑ n ∈ Ico 73984 74112, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 73984 74112, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (270201 : ℤ) ∧
    (∑ n ∈ Ico 73984 74112, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (5404111473663057057032751361 : ℤ) := by
  rcases cdemPrefixStats_73984_74048 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_74048_74112 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 73984 ≤ 74048) (by norm_num : 74048 ≤ 74112), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 73984 ≤ 74048) (by norm_num : 74048 ≤ 74112), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 73984 ≤ 74048) (by norm_num : 74048 ≤ 74112), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 73984 ≤ 74048) (by norm_num : 74048 ≤ 74112), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_74112_74176 :
    (∑ n ∈ Ico 74112 74176, mobiusTreeValue 16 mobiusTable1200001 n) = (-4 : ℤ) ∧
    (∑ n ∈ Ico 74112 74176, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 74112 74176, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-269673 : ℤ) ∧
    (∑ n ∈ Ico 74112 74176, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-5393524128466785112075781748 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_74176_74240 :
    (∑ n ∈ Ico 74176 74240, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 74176 74240, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 74176 74240, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-67466 : ℤ) ∧
    (∑ n ∈ Ico 74176 74240, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-1349270839478904558555482508 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_74112_74240 :
    (∑ n ∈ Ico 74112 74240, mobiusTreeValue 16 mobiusTable1200001 n) = (-5 : ℤ) ∧
    (∑ n ∈ Ico 74112 74240, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 74112 74240, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-337139 : ℤ) ∧
    (∑ n ∈ Ico 74112 74240, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-6742794967945689670631264256 : ℤ) := by
  rcases cdemPrefixStats_74112_74176 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_74176_74240 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 74112 ≤ 74176) (by norm_num : 74176 ≤ 74240), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 74112 ≤ 74176) (by norm_num : 74176 ≤ 74240), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 74112 ≤ 74176) (by norm_num : 74176 ≤ 74240), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 74112 ≤ 74176) (by norm_num : 74176 ≤ 74240), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_73984_74240 :
    (∑ n ∈ Ico 73984 74240, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 73984 74240, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (155 : ℕ) ∧
    (∑ n ∈ Ico 73984 74240, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-66938 : ℤ) ∧
    (∑ n ∈ Ico 73984 74240, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-1338683494282632613598512895 : ℤ) := by
  rcases cdemPrefixStats_73984_74112 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_74112_74240 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 73984 ≤ 74112) (by norm_num : 74112 ≤ 74240), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 73984 ≤ 74112) (by norm_num : 74112 ≤ 74240), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 73984 ≤ 74112) (by norm_num : 74112 ≤ 74240), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 73984 ≤ 74112) (by norm_num : 74112 ≤ 74240), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_73728_74240 :
    (∑ n ∈ Ico 73728 74240, mobiusTreeValue 16 mobiusTable1200001 n) = (12 : ℤ) ∧
    (∑ n ∈ Ico 73728 74240, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (310 : ℕ) ∧
    (∑ n ∈ Ico 73728 74240, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (814290 : ℤ) ∧
    (∑ n ∈ Ico 73728 74240, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (16286013465266410339302643977 : ℤ) := by
  rcases cdemPrefixStats_73728_73984 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_73984_74240 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 73728 ≤ 73984) (by norm_num : 73984 ≤ 74240), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 73728 ≤ 73984) (by norm_num : 73984 ≤ 74240), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 73728 ≤ 73984) (by norm_num : 73984 ≤ 74240), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 73728 ≤ 73984) (by norm_num : 73984 ≤ 74240), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_74240_74304 :
    (∑ n ∈ Ico 74240 74304, mobiusTreeValue 16 mobiusTable1200001 n) = (-8 : ℤ) ∧
    (∑ n ∈ Ico 74240 74304, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 74240 74304, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-538536 : ℤ) ∧
    (∑ n ∈ Ico 74240 74304, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-10770729835634815112310257562 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_74304_74368 :
    (∑ n ∈ Ico 74304 74368, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 74304 74368, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 74304 74368, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (48 : ℤ) ∧
    (∑ n ∈ Ico 74304 74368, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (976730001295328991718435 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_74240_74368 :
    (∑ n ∈ Ico 74240 74368, mobiusTreeValue 16 mobiusTable1200001 n) = (-8 : ℤ) ∧
    (∑ n ∈ Ico 74240 74368, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (76 : ℕ) ∧
    (∑ n ∈ Ico 74240 74368, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-538488 : ℤ) ∧
    (∑ n ∈ Ico 74240 74368, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-10769753105633519783318539127 : ℤ) := by
  rcases cdemPrefixStats_74240_74304 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_74304_74368 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 74240 ≤ 74304) (by norm_num : 74304 ≤ 74368), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 74240 ≤ 74304) (by norm_num : 74304 ≤ 74368), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 74240 ≤ 74304) (by norm_num : 74304 ≤ 74368), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 74240 ≤ 74304) (by norm_num : 74304 ≤ 74368), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_74368_74432 :
    (∑ n ∈ Ico 74368 74432, mobiusTreeValue 16 mobiusTable1200001 n) = (4 : ℤ) ∧
    (∑ n ∈ Ico 74368 74432, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 74368 74432, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (268751 : ℤ) ∧
    (∑ n ∈ Ico 74368 74432, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (5375025658599339198514127836 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_74432_74496 :
    (∑ n ∈ Ico 74432 74496, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 74432 74496, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (42 : ℕ) ∧
    (∑ n ∈ Ico 74432 74496, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (35 : ℤ) ∧
    (∑ n ∈ Ico 74432 74496, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (721594611748807291778677 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_74368_74496 :
    (∑ n ∈ Ico 74368 74496, mobiusTreeValue 16 mobiusTable1200001 n) = (4 : ℤ) ∧
    (∑ n ∈ Ico 74368 74496, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (80 : ℕ) ∧
    (∑ n ∈ Ico 74368 74496, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (268786 : ℤ) ∧
    (∑ n ∈ Ico 74368 74496, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (5375747253211088005805906513 : ℤ) := by
  rcases cdemPrefixStats_74368_74432 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_74432_74496 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 74368 ≤ 74432) (by norm_num : 74432 ≤ 74496), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 74368 ≤ 74432) (by norm_num : 74432 ≤ 74496), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 74368 ≤ 74432) (by norm_num : 74432 ≤ 74496), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 74368 ≤ 74432) (by norm_num : 74432 ≤ 74496), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_74240_74496 :
    (∑ n ∈ Ico 74240 74496, mobiusTreeValue 16 mobiusTable1200001 n) = (-4 : ℤ) ∧
    (∑ n ∈ Ico 74240 74496, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (156 : ℕ) ∧
    (∑ n ∈ Ico 74240 74496, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-269702 : ℤ) ∧
    (∑ n ∈ Ico 74240 74496, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-5394005852422431777512632614 : ℤ) := by
  rcases cdemPrefixStats_74240_74368 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_74368_74496 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 74240 ≤ 74368) (by norm_num : 74368 ≤ 74496), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 74240 ≤ 74368) (by norm_num : 74368 ≤ 74496), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 74240 ≤ 74368) (by norm_num : 74368 ≤ 74496), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 74240 ≤ 74368) (by norm_num : 74368 ≤ 74496), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_74496_74560 :
    (∑ n ∈ Ico 74496 74560, mobiusTreeValue 16 mobiusTable1200001 n) = (-4 : ℤ) ∧
    (∑ n ∈ Ico 74496 74560, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 74496 74560, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-268557 : ℤ) ∧
    (∑ n ∈ Ico 74496 74560, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-5371179865348476828398158893 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_74560_74624 :
    (∑ n ∈ Ico 74560 74624, mobiusTreeValue 16 mobiusTable1200001 n) = (-7 : ℤ) ∧
    (∑ n ∈ Ico 74560 74624, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 74560 74624, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-469198 : ℤ) ∧
    (∑ n ∈ Ico 74560 74624, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-9384025578181519265560827911 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_74496_74624 :
    (∑ n ∈ Ico 74496 74624, mobiusTreeValue 16 mobiusTable1200001 n) = (-11 : ℤ) ∧
    (∑ n ∈ Ico 74496 74624, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 74496 74624, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-737755 : ℤ) ∧
    (∑ n ∈ Ico 74496 74624, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-14755205443529996093958986804 : ℤ) := by
  rcases cdemPrefixStats_74496_74560 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_74560_74624 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 74496 ≤ 74560) (by norm_num : 74560 ≤ 74624), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 74496 ≤ 74560) (by norm_num : 74560 ≤ 74624), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 74496 ≤ 74560) (by norm_num : 74560 ≤ 74624), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 74496 ≤ 74560) (by norm_num : 74560 ≤ 74624), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_74624_74688 :
    (∑ n ∈ Ico 74624 74688, mobiusTreeValue 16 mobiusTable1200001 n) = (10 : ℤ) ∧
    (∑ n ∈ Ico 74624 74688, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 74624 74688, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (669910 : ℤ) ∧
    (∑ n ∈ Ico 74624 74688, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (13398270405258188498634434559 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_74688_74752 :
    (∑ n ∈ Ico 74688 74752, mobiusTreeValue 16 mobiusTable1200001 n) = (2 : ℤ) ∧
    (∑ n ∈ Ico 74688 74752, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 74688 74752, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (133725 : ℤ) ∧
    (∑ n ∈ Ico 74688 74752, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (2674564578765282136357852377 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_74624_74752 :
    (∑ n ∈ Ico 74624 74752, mobiusTreeValue 16 mobiusTable1200001 n) = (12 : ℤ) ∧
    (∑ n ∈ Ico 74624 74752, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 74624 74752, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (803635 : ℤ) ∧
    (∑ n ∈ Ico 74624 74752, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (16072834984023470634992286936 : ℤ) := by
  rcases cdemPrefixStats_74624_74688 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_74688_74752 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 74624 ≤ 74688) (by norm_num : 74688 ≤ 74752), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 74624 ≤ 74688) (by norm_num : 74688 ≤ 74752), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 74624 ≤ 74688) (by norm_num : 74688 ≤ 74752), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 74624 ≤ 74688) (by norm_num : 74688 ≤ 74752), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_74496_74752 :
    (∑ n ∈ Ico 74496 74752, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 74496 74752, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (155 : ℕ) ∧
    (∑ n ∈ Ico 74496 74752, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (65880 : ℤ) ∧
    (∑ n ∈ Ico 74496 74752, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1317629540493474541033300132 : ℤ) := by
  rcases cdemPrefixStats_74496_74624 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_74624_74752 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 74496 ≤ 74624) (by norm_num : 74624 ≤ 74752), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 74496 ≤ 74624) (by norm_num : 74624 ≤ 74752), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 74496 ≤ 74624) (by norm_num : 74624 ≤ 74752), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 74496 ≤ 74624) (by norm_num : 74624 ≤ 74752), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_74240_74752 :
    (∑ n ∈ Ico 74240 74752, mobiusTreeValue 16 mobiusTable1200001 n) = (-3 : ℤ) ∧
    (∑ n ∈ Ico 74240 74752, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (311 : ℕ) ∧
    (∑ n ∈ Ico 74240 74752, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-203822 : ℤ) ∧
    (∑ n ∈ Ico 74240 74752, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-4076376311928957236479332482 : ℤ) := by
  rcases cdemPrefixStats_74240_74496 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_74496_74752 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 74240 ≤ 74496) (by norm_num : 74496 ≤ 74752), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 74240 ≤ 74496) (by norm_num : 74496 ≤ 74752), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 74240 ≤ 74496) (by norm_num : 74496 ≤ 74752), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 74240 ≤ 74496) (by norm_num : 74496 ≤ 74752), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_73728_74752 :
    (∑ n ∈ Ico 73728 74752, mobiusTreeValue 16 mobiusTable1200001 n) = (9 : ℤ) ∧
    (∑ n ∈ Ico 73728 74752, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (621 : ℕ) ∧
    (∑ n ∈ Ico 73728 74752, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (610468 : ℤ) ∧
    (∑ n ∈ Ico 73728 74752, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (12209637153337453102823311495 : ℤ) := by
  rcases cdemPrefixStats_73728_74240 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_74240_74752 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 73728 ≤ 74240) (by norm_num : 74240 ≤ 74752), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 73728 ≤ 74240) (by norm_num : 74240 ≤ 74752), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 73728 ≤ 74240) (by norm_num : 74240 ≤ 74752), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 73728 ≤ 74240) (by norm_num : 74240 ≤ 74752), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_74752_74816 :
    (∑ n ∈ Ico 74752 74816, mobiusTreeValue 16 mobiusTable1200001 n) = (-12 : ℤ) ∧
    (∑ n ∈ Ico 74752 74816, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 74752 74816, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-802280 : ℤ) ∧
    (∑ n ∈ Ico 74752 74816, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-16045748681447883095885388362 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_74816_74880 :
    (∑ n ∈ Ico 74816 74880, mobiusTreeValue 16 mobiusTable1200001 n) = (-5 : ℤ) ∧
    (∑ n ∈ Ico 74816 74880, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (35 : ℕ) ∧
    (∑ n ∈ Ico 74816 74880, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-333742 : ℤ) ∧
    (∑ n ∈ Ico 74816 74880, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-6674886569982158025175431710 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_74752_74880 :
    (∑ n ∈ Ico 74752 74880, mobiusTreeValue 16 mobiusTable1200001 n) = (-17 : ℤ) ∧
    (∑ n ∈ Ico 74752 74880, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (75 : ℕ) ∧
    (∑ n ∈ Ico 74752 74880, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-1136022 : ℤ) ∧
    (∑ n ∈ Ico 74752 74880, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-22720635251430041121060820072 : ℤ) := by
  rcases cdemPrefixStats_74752_74816 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_74816_74880 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 74752 ≤ 74816) (by norm_num : 74816 ≤ 74880), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 74752 ≤ 74816) (by norm_num : 74816 ≤ 74880), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 74752 ≤ 74816) (by norm_num : 74816 ≤ 74880), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 74752 ≤ 74816) (by norm_num : 74816 ≤ 74880), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_74880_74944 :
    (∑ n ∈ Ico 74880 74944, mobiusTreeValue 16 mobiusTable1200001 n) = (-2 : ℤ) ∧
    (∑ n ∈ Ico 74880 74944, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 74880 74944, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-133576 : ℤ) ∧
    (∑ n ∈ Ico 74880 74944, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-2671510098755476278804754476 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_74944_75008 :
    (∑ n ∈ Ico 74944 75008, mobiusTreeValue 16 mobiusTable1200001 n) = (6 : ℤ) ∧
    (∑ n ∈ Ico 74944 75008, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 74944 75008, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (400147 : ℤ) ∧
    (∑ n ∈ Ico 74944 75008, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (8003023927431391937342800006 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_74880_75008 :
    (∑ n ∈ Ico 74880 75008, mobiusTreeValue 16 mobiusTable1200001 n) = (4 : ℤ) ∧
    (∑ n ∈ Ico 74880 75008, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (80 : ℕ) ∧
    (∑ n ∈ Ico 74880 75008, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (266571 : ℤ) ∧
    (∑ n ∈ Ico 74880 75008, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (5331513828675915658538045530 : ℤ) := by
  rcases cdemPrefixStats_74880_74944 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_74944_75008 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 74880 ≤ 74944) (by norm_num : 74944 ≤ 75008), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 74880 ≤ 74944) (by norm_num : 74944 ≤ 75008), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 74880 ≤ 74944) (by norm_num : 74944 ≤ 75008), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 74880 ≤ 74944) (by norm_num : 74944 ≤ 75008), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_74752_75008 :
    (∑ n ∈ Ico 74752 75008, mobiusTreeValue 16 mobiusTable1200001 n) = (-13 : ℤ) ∧
    (∑ n ∈ Ico 74752 75008, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (155 : ℕ) ∧
    (∑ n ∈ Ico 74752 75008, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-869451 : ℤ) ∧
    (∑ n ∈ Ico 74752 75008, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-17389121422754125462522774542 : ℤ) := by
  rcases cdemPrefixStats_74752_74880 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_74880_75008 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 74752 ≤ 74880) (by norm_num : 74880 ≤ 75008), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 74752 ≤ 74880) (by norm_num : 74880 ≤ 75008), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 74752 ≤ 74880) (by norm_num : 74880 ≤ 75008), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 74752 ≤ 74880) (by norm_num : 74880 ≤ 75008), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_75008_75072 :
    (∑ n ∈ Ico 75008 75072, mobiusTreeValue 16 mobiusTable1200001 n) = (-10 : ℤ) ∧
    (∑ n ∈ Ico 75008 75072, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 75008 75072, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-666426 : ℤ) ∧
    (∑ n ∈ Ico 75008 75072, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-13328641699056885452497166702 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_75072_75136 :
    (∑ n ∈ Ico 75072 75136, mobiusTreeValue 16 mobiusTable1200001 n) = (8 : ℤ) ∧
    (∑ n ∈ Ico 75072 75136, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 75072 75136, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (532587 : ℤ) ∧
    (∑ n ∈ Ico 75072 75136, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (10651825964088179992866981377 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_75008_75136 :
    (∑ n ∈ Ico 75008 75136, mobiusTreeValue 16 mobiusTable1200001 n) = (-2 : ℤ) ∧
    (∑ n ∈ Ico 75008 75136, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 75008 75136, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-133839 : ℤ) ∧
    (∑ n ∈ Ico 75008 75136, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-2676815734968705459630185325 : ℤ) := by
  rcases cdemPrefixStats_75008_75072 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_75072_75136 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 75008 ≤ 75072) (by norm_num : 75072 ≤ 75136), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 75008 ≤ 75072) (by norm_num : 75072 ≤ 75136), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 75008 ≤ 75072) (by norm_num : 75072 ≤ 75136), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 75008 ≤ 75072) (by norm_num : 75072 ≤ 75136), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_75136_75200 :
    (∑ n ∈ Ico 75136 75200, mobiusTreeValue 16 mobiusTable1200001 n) = (8 : ℤ) ∧
    (∑ n ∈ Ico 75136 75200, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 75136 75200, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (532230 : ℤ) ∧
    (∑ n ∈ Ico 75136 75200, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (10644616049349322533939396723 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_75200_75264 :
    (∑ n ∈ Ico 75200 75264, mobiusTreeValue 16 mobiusTable1200001 n) = (-12 : ℤ) ∧
    (∑ n ∈ Ico 75200 75264, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 75200 75264, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-797597 : ℤ) ∧
    (∑ n ∈ Ico 75200 75264, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-15952037950973162246645888728 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_75136_75264 :
    (∑ n ∈ Ico 75136 75264, mobiusTreeValue 16 mobiusTable1200001 n) = (-4 : ℤ) ∧
    (∑ n ∈ Ico 75136 75264, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 75136 75264, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-265367 : ℤ) ∧
    (∑ n ∈ Ico 75136 75264, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-5307421901623839712706492005 : ℤ) := by
  rcases cdemPrefixStats_75136_75200 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_75200_75264 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 75136 ≤ 75200) (by norm_num : 75200 ≤ 75264), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 75136 ≤ 75200) (by norm_num : 75200 ≤ 75264), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 75136 ≤ 75200) (by norm_num : 75200 ≤ 75264), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 75136 ≤ 75200) (by norm_num : 75200 ≤ 75264), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_75008_75264 :
    (∑ n ∈ Ico 75008 75264, mobiusTreeValue 16 mobiusTable1200001 n) = (-6 : ℤ) ∧
    (∑ n ∈ Ico 75008 75264, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (156 : ℕ) ∧
    (∑ n ∈ Ico 75008 75264, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-399206 : ℤ) ∧
    (∑ n ∈ Ico 75008 75264, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-7984237636592545172336677330 : ℤ) := by
  rcases cdemPrefixStats_75008_75136 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_75136_75264 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 75008 ≤ 75136) (by norm_num : 75136 ≤ 75264), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 75008 ≤ 75136) (by norm_num : 75136 ≤ 75264), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 75008 ≤ 75136) (by norm_num : 75136 ≤ 75264), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 75008 ≤ 75136) (by norm_num : 75136 ≤ 75264), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_74752_75264 :
    (∑ n ∈ Ico 74752 75264, mobiusTreeValue 16 mobiusTable1200001 n) = (-19 : ℤ) ∧
    (∑ n ∈ Ico 74752 75264, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (311 : ℕ) ∧
    (∑ n ∈ Ico 74752 75264, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-1268657 : ℤ) ∧
    (∑ n ∈ Ico 74752 75264, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-25373359059346670634859451872 : ℤ) := by
  rcases cdemPrefixStats_74752_75008 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_75008_75264 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 74752 ≤ 75008) (by norm_num : 75008 ≤ 75264), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 74752 ≤ 75008) (by norm_num : 75008 ≤ 75264), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 74752 ≤ 75008) (by norm_num : 75008 ≤ 75264), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 74752 ≤ 75008) (by norm_num : 75008 ≤ 75264), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_75264_75328 :
    (∑ n ∈ Ico 75264 75328, mobiusTreeValue 16 mobiusTable1200001 n) = (-3 : ℤ) ∧
    (∑ n ∈ Ico 75264 75328, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 75264 75328, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-199206 : ℤ) ∧
    (∑ n ∈ Ico 75264 75328, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-3984204800186965466674027180 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_75328_75392 :
    (∑ n ∈ Ico 75328 75392, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 75328 75392, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 75328 75392, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (66319 : ℤ) ∧
    (∑ n ∈ Ico 75328 75392, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1326364890178749456978844456 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_75264_75392 :
    (∑ n ∈ Ico 75264 75392, mobiusTreeValue 16 mobiusTable1200001 n) = (-2 : ℤ) ∧
    (∑ n ∈ Ico 75264 75392, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 75264 75392, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-132887 : ℤ) ∧
    (∑ n ∈ Ico 75264 75392, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-2657839910008216009695182724 : ℤ) := by
  rcases cdemPrefixStats_75264_75328 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_75328_75392 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 75264 ≤ 75328) (by norm_num : 75328 ≤ 75392), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 75264 ≤ 75328) (by norm_num : 75328 ≤ 75392), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 75264 ≤ 75328) (by norm_num : 75328 ≤ 75392), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 75264 ≤ 75328) (by norm_num : 75328 ≤ 75392), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_75392_75456 :
    (∑ n ∈ Ico 75392 75456, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 75392 75456, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 75392 75456, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (66246 : ℤ) ∧
    (∑ n ∈ Ico 75392 75456, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1324923830420325846799462882 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_75456_75520 :
    (∑ n ∈ Ico 75456 75520, mobiusTreeValue 16 mobiusTable1200001 n) = (-4 : ℤ) ∧
    (∑ n ∈ Ico 75456 75520, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 75456 75520, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-264886 : ℤ) ∧
    (∑ n ∈ Ico 75456 75520, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-5297768124133234110165922453 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_75392_75520 :
    (∑ n ∈ Ico 75392 75520, mobiusTreeValue 16 mobiusTable1200001 n) = (-3 : ℤ) ∧
    (∑ n ∈ Ico 75392 75520, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (79 : ℕ) ∧
    (∑ n ∈ Ico 75392 75520, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-198640 : ℤ) ∧
    (∑ n ∈ Ico 75392 75520, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-3972844293712908263366459571 : ℤ) := by
  rcases cdemPrefixStats_75392_75456 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_75456_75520 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 75392 ≤ 75456) (by norm_num : 75456 ≤ 75520), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 75392 ≤ 75456) (by norm_num : 75456 ≤ 75520), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 75392 ≤ 75456) (by norm_num : 75456 ≤ 75520), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 75392 ≤ 75456) (by norm_num : 75456 ≤ 75520), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_75264_75520 :
    (∑ n ∈ Ico 75264 75520, mobiusTreeValue 16 mobiusTable1200001 n) = (-5 : ℤ) ∧
    (∑ n ∈ Ico 75264 75520, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (157 : ℕ) ∧
    (∑ n ∈ Ico 75264 75520, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-331527 : ℤ) ∧
    (∑ n ∈ Ico 75264 75520, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-6630684203721124273061642295 : ℤ) := by
  rcases cdemPrefixStats_75264_75392 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_75392_75520 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 75264 ≤ 75392) (by norm_num : 75392 ≤ 75520), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 75264 ≤ 75392) (by norm_num : 75392 ≤ 75520), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 75264 ≤ 75392) (by norm_num : 75392 ≤ 75520), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 75264 ≤ 75392) (by norm_num : 75392 ≤ 75520), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_75520_75584 :
    (∑ n ∈ Ico 75520 75584, mobiusTreeValue 16 mobiusTable1200001 n) = (-8 : ℤ) ∧
    (∑ n ∈ Ico 75520 75584, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 75520 75584, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-529542 : ℤ) ∧
    (∑ n ∈ Ico 75520 75584, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-10590941352764940727302135116 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_75584_75648 :
    (∑ n ∈ Ico 75584 75648, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 75584 75648, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 75584 75648, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-66096 : ℤ) ∧
    (∑ n ∈ Ico 75584 75648, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-1321982112371168269121174457 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_75520_75648 :
    (∑ n ∈ Ico 75520 75648, mobiusTreeValue 16 mobiusTable1200001 n) = (-9 : ℤ) ∧
    (∑ n ∈ Ico 75520 75648, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 75520 75648, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-595638 : ℤ) ∧
    (∑ n ∈ Ico 75520 75648, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-11912923465136108996423309573 : ℤ) := by
  rcases cdemPrefixStats_75520_75584 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_75584_75648 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 75520 ≤ 75584) (by norm_num : 75584 ≤ 75648), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 75520 ≤ 75584) (by norm_num : 75584 ≤ 75648), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 75520 ≤ 75584) (by norm_num : 75584 ≤ 75648), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 75520 ≤ 75584) (by norm_num : 75584 ≤ 75648), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_75648_75712 :
    (∑ n ∈ Ico 75648 75712, mobiusTreeValue 16 mobiusTable1200001 n) = (-6 : ℤ) ∧
    (∑ n ∈ Ico 75648 75712, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 75648 75712, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-396409 : ℤ) ∧
    (∑ n ∈ Ico 75648 75712, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-7928240938431595771369678896 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_75712_75776 :
    (∑ n ∈ Ico 75712 75776, mobiusTreeValue 16 mobiusTable1200001 n) = (-4 : ℤ) ∧
    (∑ n ∈ Ico 75712 75776, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (36 : ℕ) ∧
    (∑ n ∈ Ico 75712 75776, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-264074 : ℤ) ∧
    (∑ n ∈ Ico 75712 75776, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-5281469959049094076192271289 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_75648_75776 :
    (∑ n ∈ Ico 75648 75776, mobiusTreeValue 16 mobiusTable1200001 n) = (-10 : ℤ) ∧
    (∑ n ∈ Ico 75648 75776, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (76 : ℕ) ∧
    (∑ n ∈ Ico 75648 75776, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-660483 : ℤ) ∧
    (∑ n ∈ Ico 75648 75776, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-13209710897480689847561950185 : ℤ) := by
  rcases cdemPrefixStats_75648_75712 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_75712_75776 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 75648 ≤ 75712) (by norm_num : 75712 ≤ 75776), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 75648 ≤ 75712) (by norm_num : 75712 ≤ 75776), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 75648 ≤ 75712) (by norm_num : 75712 ≤ 75776), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 75648 ≤ 75712) (by norm_num : 75712 ≤ 75776), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_75520_75776 :
    (∑ n ∈ Ico 75520 75776, mobiusTreeValue 16 mobiusTable1200001 n) = (-19 : ℤ) ∧
    (∑ n ∈ Ico 75520 75776, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (153 : ℕ) ∧
    (∑ n ∈ Ico 75520 75776, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-1256121 : ℤ) ∧
    (∑ n ∈ Ico 75520 75776, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-25122634362616798843985259758 : ℤ) := by
  rcases cdemPrefixStats_75520_75648 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_75648_75776 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 75520 ≤ 75648) (by norm_num : 75648 ≤ 75776), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 75520 ≤ 75648) (by norm_num : 75648 ≤ 75776), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 75520 ≤ 75648) (by norm_num : 75648 ≤ 75776), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 75520 ≤ 75648) (by norm_num : 75648 ≤ 75776), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_75264_75776 :
    (∑ n ∈ Ico 75264 75776, mobiusTreeValue 16 mobiusTable1200001 n) = (-24 : ℤ) ∧
    (∑ n ∈ Ico 75264 75776, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (310 : ℕ) ∧
    (∑ n ∈ Ico 75264 75776, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-1587648 : ℤ) ∧
    (∑ n ∈ Ico 75264 75776, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-31753318566337923117046902053 : ℤ) := by
  rcases cdemPrefixStats_75264_75520 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_75520_75776 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 75264 ≤ 75520) (by norm_num : 75520 ≤ 75776), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 75264 ≤ 75520) (by norm_num : 75520 ≤ 75776), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 75264 ≤ 75520) (by norm_num : 75520 ≤ 75776), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 75264 ≤ 75520) (by norm_num : 75520 ≤ 75776), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_74752_75776 :
    (∑ n ∈ Ico 74752 75776, mobiusTreeValue 16 mobiusTable1200001 n) = (-43 : ℤ) ∧
    (∑ n ∈ Ico 74752 75776, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (621 : ℕ) ∧
    (∑ n ∈ Ico 74752 75776, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-2856305 : ℤ) ∧
    (∑ n ∈ Ico 74752 75776, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-57126677625684593751906353925 : ℤ) := by
  rcases cdemPrefixStats_74752_75264 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_75264_75776 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 74752 ≤ 75264) (by norm_num : 75264 ≤ 75776), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 74752 ≤ 75264) (by norm_num : 75264 ≤ 75776), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 74752 ≤ 75264) (by norm_num : 75264 ≤ 75776), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 74752 ≤ 75264) (by norm_num : 75264 ≤ 75776), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_73728_75776 :
    (∑ n ∈ Ico 73728 75776, mobiusTreeValue 16 mobiusTable1200001 n) = (-34 : ℤ) ∧
    (∑ n ∈ Ico 73728 75776, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (1242 : ℕ) ∧
    (∑ n ∈ Ico 73728 75776, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-2245837 : ℤ) ∧
    (∑ n ∈ Ico 73728 75776, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-44917040472347140649083042430 : ℤ) := by
  rcases cdemPrefixStats_73728_74752 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_74752_75776 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 73728 ≤ 74752) (by norm_num : 74752 ≤ 75776), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 73728 ≤ 74752) (by norm_num : 74752 ≤ 75776), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 73728 ≤ 74752) (by norm_num : 74752 ≤ 75776), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 73728 ≤ 74752) (by norm_num : 74752 ≤ 75776), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_75776_75840 :
    (∑ n ∈ Ico 75776 75840, mobiusTreeValue 16 mobiusTable1200001 n) = (-9 : ℤ) ∧
    (∑ n ∈ Ico 75776 75840, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 75776 75840, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-593457 : ℤ) ∧
    (∑ n ∈ Ico 75776 75840, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-11869244808804460855370908547 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_75840_75904 :
    (∑ n ∈ Ico 75840 75904, mobiusTreeValue 16 mobiusTable1200001 n) = (-2 : ℤ) ∧
    (∑ n ∈ Ico 75840 75904, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 75840 75904, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-131685 : ℤ) ∧
    (∑ n ∈ Ico 75840 75904, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-2633759898690847356171963028 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_75776_75904 :
    (∑ n ∈ Ico 75776 75904, mobiusTreeValue 16 mobiusTable1200001 n) = (-11 : ℤ) ∧
    (∑ n ∈ Ico 75776 75904, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 75776 75904, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-725142 : ℤ) ∧
    (∑ n ∈ Ico 75776 75904, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-14503004707495308211542871575 : ℤ) := by
  rcases cdemPrefixStats_75776_75840 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_75840_75904 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 75776 ≤ 75840) (by norm_num : 75840 ≤ 75904), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 75776 ≤ 75840) (by norm_num : 75840 ≤ 75904), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 75776 ≤ 75840) (by norm_num : 75840 ≤ 75904), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 75776 ≤ 75840) (by norm_num : 75840 ≤ 75904), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_75904_75968 :
    (∑ n ∈ Ico 75904 75968, mobiusTreeValue 16 mobiusTable1200001 n) = (6 : ℤ) ∧
    (∑ n ∈ Ico 75904 75968, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 75904 75968, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (395101 : ℤ) ∧
    (∑ n ∈ Ico 75904 75968, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (7902102295669847244292386720 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_75968_76032 :
    (∑ n ∈ Ico 75968 76032, mobiusTreeValue 16 mobiusTable1200001 n) = (6 : ℤ) ∧
    (∑ n ∈ Ico 75968 76032, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 75968 76032, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (394772 : ℤ) ∧
    (∑ n ∈ Ico 75968 76032, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (7895464585055996262721885299 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_75904_76032 :
    (∑ n ∈ Ico 75904 76032, mobiusTreeValue 16 mobiusTable1200001 n) = (12 : ℤ) ∧
    (∑ n ∈ Ico 75904 76032, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 75904 76032, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (789873 : ℤ) ∧
    (∑ n ∈ Ico 75904 76032, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (15797566880725843507014272019 : ℤ) := by
  rcases cdemPrefixStats_75904_75968 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_75968_76032 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 75904 ≤ 75968) (by norm_num : 75968 ≤ 76032), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 75904 ≤ 75968) (by norm_num : 75968 ≤ 76032), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 75904 ≤ 75968) (by norm_num : 75968 ≤ 76032), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 75904 ≤ 75968) (by norm_num : 75968 ≤ 76032), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_75776_76032 :
    (∑ n ∈ Ico 75776 76032, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 75776 76032, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (155 : ℕ) ∧
    (∑ n ∈ Ico 75776 76032, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (64731 : ℤ) ∧
    (∑ n ∈ Ico 75776 76032, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1294562173230535295471400444 : ℤ) := by
  rcases cdemPrefixStats_75776_75904 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_75904_76032 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 75776 ≤ 75904) (by norm_num : 75904 ≤ 76032), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 75776 ≤ 75904) (by norm_num : 75904 ≤ 76032), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 75776 ≤ 75904) (by norm_num : 75904 ≤ 76032), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 75776 ≤ 75904) (by norm_num : 75904 ≤ 76032), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_76032_76096 :
    (∑ n ∈ Ico 76032 76096, mobiusTreeValue 16 mobiusTable1200001 n) = (3 : ℤ) ∧
    (∑ n ∈ Ico 76032 76096, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 76032 76096, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (197135 : ℤ) ∧
    (∑ n ∈ Ico 76032 76096, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (3942716377719461444079934987 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_76096_76160 :
    (∑ n ∈ Ico 76096 76160, mobiusTreeValue 16 mobiusTable1200001 n) = (-8 : ℤ) ∧
    (∑ n ∈ Ico 76096 76160, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 76096 76160, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-525450 : ℤ) ∧
    (∑ n ∈ Ico 76096 76160, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-10509100999110454947361011839 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_76032_76160 :
    (∑ n ∈ Ico 76032 76160, mobiusTreeValue 16 mobiusTable1200001 n) = (-5 : ℤ) ∧
    (∑ n ∈ Ico 76032 76160, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (79 : ℕ) ∧
    (∑ n ∈ Ico 76032 76160, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-328315 : ℤ) ∧
    (∑ n ∈ Ico 76032 76160, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-6566384621390993503281076852 : ℤ) := by
  rcases cdemPrefixStats_76032_76096 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_76096_76160 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 76032 ≤ 76096) (by norm_num : 76096 ≤ 76160), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 76032 ≤ 76096) (by norm_num : 76096 ≤ 76160), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 76032 ≤ 76096) (by norm_num : 76096 ≤ 76160), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 76032 ≤ 76096) (by norm_num : 76096 ≤ 76160), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_76160_76224 :
    (∑ n ∈ Ico 76160 76224, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 76160 76224, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 76160 76224, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-65595 : ℤ) ∧
    (∑ n ∈ Ico 76160 76224, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-1311922851296441420534957486 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_76224_76288 :
    (∑ n ∈ Ico 76224 76288, mobiusTreeValue 16 mobiusTable1200001 n) = (-7 : ℤ) ∧
    (∑ n ∈ Ico 76224 76288, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 76224 76288, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-458851 : ℤ) ∧
    (∑ n ∈ Ico 76224 76288, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-9177060708681070419170668410 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_76160_76288 :
    (∑ n ∈ Ico 76160 76288, mobiusTreeValue 16 mobiusTable1200001 n) = (-8 : ℤ) ∧
    (∑ n ∈ Ico 76160 76288, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (80 : ℕ) ∧
    (∑ n ∈ Ico 76160 76288, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-524446 : ℤ) ∧
    (∑ n ∈ Ico 76160 76288, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-10488983559977511839705625896 : ℤ) := by
  rcases cdemPrefixStats_76160_76224 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_76224_76288 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 76160 ≤ 76224) (by norm_num : 76224 ≤ 76288), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 76160 ≤ 76224) (by norm_num : 76224 ≤ 76288), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 76160 ≤ 76224) (by norm_num : 76224 ≤ 76288), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 76160 ≤ 76224) (by norm_num : 76224 ≤ 76288), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_76032_76288 :
    (∑ n ∈ Ico 76032 76288, mobiusTreeValue 16 mobiusTable1200001 n) = (-13 : ℤ) ∧
    (∑ n ∈ Ico 76032 76288, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (159 : ℕ) ∧
    (∑ n ∈ Ico 76032 76288, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-852761 : ℤ) ∧
    (∑ n ∈ Ico 76032 76288, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-17055368181368505342986702748 : ℤ) := by
  rcases cdemPrefixStats_76032_76160 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_76160_76288 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 76032 ≤ 76160) (by norm_num : 76160 ≤ 76288), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 76032 ≤ 76160) (by norm_num : 76160 ≤ 76288), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 76032 ≤ 76160) (by norm_num : 76160 ≤ 76288), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 76032 ≤ 76160) (by norm_num : 76160 ≤ 76288), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_75776_76288 :
    (∑ n ∈ Ico 75776 76288, mobiusTreeValue 16 mobiusTable1200001 n) = (-12 : ℤ) ∧
    (∑ n ∈ Ico 75776 76288, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (314 : ℕ) ∧
    (∑ n ∈ Ico 75776 76288, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-788030 : ℤ) ∧
    (∑ n ∈ Ico 75776 76288, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-15760806008137970047515302304 : ℤ) := by
  rcases cdemPrefixStats_75776_76032 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_76032_76288 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 75776 ≤ 76032) (by norm_num : 76032 ≤ 76288), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 75776 ≤ 76032) (by norm_num : 76032 ≤ 76288), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 75776 ≤ 76032) (by norm_num : 76032 ≤ 76288), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 75776 ≤ 76032) (by norm_num : 76032 ≤ 76288), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_76288_76352 :
    (∑ n ∈ Ico 76288 76352, mobiusTreeValue 16 mobiusTable1200001 n) = (7 : ℤ) ∧
    (∑ n ∈ Ico 76288 76352, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 76288 76352, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (458560 : ℤ) ∧
    (∑ n ∈ Ico 76288 76352, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (9171203833996323289902126925 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_76352_76416 :
    (∑ n ∈ Ico 76352 76416, mobiusTreeValue 16 mobiusTable1200001 n) = (13 : ℤ) ∧
    (∑ n ∈ Ico 76352 76416, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 76352 76416, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (850855 : ℤ) ∧
    (∑ n ∈ Ico 76352 76416, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (17017267117382702958024872062 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_76288_76416 :
    (∑ n ∈ Ico 76288 76416, mobiusTreeValue 16 mobiusTable1200001 n) = (20 : ℤ) ∧
    (∑ n ∈ Ico 76288 76416, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 76288 76416, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (1309415 : ℤ) ∧
    (∑ n ∈ Ico 76288 76416, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (26188470951379026247926998987 : ℤ) := by
  rcases cdemPrefixStats_76288_76352 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_76352_76416 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 76288 ≤ 76352) (by norm_num : 76352 ≤ 76416), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 76288 ≤ 76352) (by norm_num : 76352 ≤ 76416), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 76288 ≤ 76352) (by norm_num : 76352 ≤ 76416), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 76288 ≤ 76352) (by norm_num : 76352 ≤ 76416), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_76416_76480 :
    (∑ n ∈ Ico 76416 76480, mobiusTreeValue 16 mobiusTable1200001 n) = (6 : ℤ) ∧
    (∑ n ∈ Ico 76416 76480, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 76416 76480, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (392279 : ℤ) ∧
    (∑ n ∈ Ico 76416 76480, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (7845666824348342015665839637 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_76480_76544 :
    (∑ n ∈ Ico 76480 76544, mobiusTreeValue 16 mobiusTable1200001 n) = (-15 : ℤ) ∧
    (∑ n ∈ Ico 76480 76544, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 76480 76544, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-980276 : ℤ) ∧
    (∑ n ∈ Ico 76480 76544, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-19605623980257642198830865781 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_76416_76544 :
    (∑ n ∈ Ico 76416 76544, mobiusTreeValue 16 mobiusTable1200001 n) = (-9 : ℤ) ∧
    (∑ n ∈ Ico 76416 76544, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (79 : ℕ) ∧
    (∑ n ∈ Ico 76416 76544, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-587997 : ℤ) ∧
    (∑ n ∈ Ico 76416 76544, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-11759957155909300183165026144 : ℤ) := by
  rcases cdemPrefixStats_76416_76480 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_76480_76544 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 76416 ≤ 76480) (by norm_num : 76480 ≤ 76544), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 76416 ≤ 76480) (by norm_num : 76480 ≤ 76544), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 76416 ≤ 76480) (by norm_num : 76480 ≤ 76544), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 76416 ≤ 76480) (by norm_num : 76480 ≤ 76544), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_76288_76544 :
    (∑ n ∈ Ico 76288 76544, mobiusTreeValue 16 mobiusTable1200001 n) = (11 : ℤ) ∧
    (∑ n ∈ Ico 76288 76544, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (157 : ℕ) ∧
    (∑ n ∈ Ico 76288 76544, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (721418 : ℤ) ∧
    (∑ n ∈ Ico 76288 76544, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (14428513795469726064761972843 : ℤ) := by
  rcases cdemPrefixStats_76288_76416 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_76416_76544 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 76288 ≤ 76416) (by norm_num : 76416 ≤ 76544), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 76288 ≤ 76416) (by norm_num : 76416 ≤ 76544), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 76288 ≤ 76416) (by norm_num : 76416 ≤ 76544), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 76288 ≤ 76416) (by norm_num : 76416 ≤ 76544), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_76544_76608 :
    (∑ n ∈ Ico 76544 76608, mobiusTreeValue 16 mobiusTable1200001 n) = (5 : ℤ) ∧
    (∑ n ∈ Ico 76544 76608, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (35 : ℕ) ∧
    (∑ n ∈ Ico 76544 76608, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (326663 : ℤ) ∧
    (∑ n ∈ Ico 76544 76608, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (6533298391279000714734383737 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_76608_76672 :
    (∑ n ∈ Ico 76608 76672, mobiusTreeValue 16 mobiusTable1200001 n) = (15 : ℤ) ∧
    (∑ n ∈ Ico 76608 76672, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 76608 76672, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (978643 : ℤ) ∧
    (∑ n ∈ Ico 76608 76672, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (19573030683456095615300651612 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_76544_76672 :
    (∑ n ∈ Ico 76544 76672, mobiusTreeValue 16 mobiusTable1200001 n) = (20 : ℤ) ∧
    (∑ n ∈ Ico 76544 76672, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (74 : ℕ) ∧
    (∑ n ∈ Ico 76544 76672, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (1305306 : ℤ) ∧
    (∑ n ∈ Ico 76544 76672, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (26106329074735096330035035349 : ℤ) := by
  rcases cdemPrefixStats_76544_76608 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_76608_76672 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 76544 ≤ 76608) (by norm_num : 76608 ≤ 76672), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 76544 ≤ 76608) (by norm_num : 76608 ≤ 76672), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 76544 ≤ 76608) (by norm_num : 76608 ≤ 76672), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 76544 ≤ 76608) (by norm_num : 76608 ≤ 76672), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_76672_76736 :
    (∑ n ∈ Ico 76672 76736, mobiusTreeValue 16 mobiusTable1200001 n) = (-7 : ℤ) ∧
    (∑ n ∈ Ico 76672 76736, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 76672 76736, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-456338 : ℤ) ∧
    (∑ n ∈ Ico 76672 76736, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-9126824581421461815042541313 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_76736_76800 :
    (∑ n ∈ Ico 76736 76800, mobiusTreeValue 16 mobiusTable1200001 n) = (4 : ℤ) ∧
    (∑ n ∈ Ico 76736 76800, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 76736 76800, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (260491 : ℤ) ∧
    (∑ n ∈ Ico 76736 76800, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (5209861173210307731729724549 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_76672_76800 :
    (∑ n ∈ Ico 76672 76800, mobiusTreeValue 16 mobiusTable1200001 n) = (-3 : ℤ) ∧
    (∑ n ∈ Ico 76672 76800, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 76672 76800, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-195847 : ℤ) ∧
    (∑ n ∈ Ico 76672 76800, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-3916963408211154083312816764 : ℤ) := by
  rcases cdemPrefixStats_76672_76736 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_76736_76800 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 76672 ≤ 76736) (by norm_num : 76736 ≤ 76800), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 76672 ≤ 76736) (by norm_num : 76736 ≤ 76800), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 76672 ≤ 76736) (by norm_num : 76736 ≤ 76800), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 76672 ≤ 76736) (by norm_num : 76736 ≤ 76800), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_76544_76800 :
    (∑ n ∈ Ico 76544 76800, mobiusTreeValue 16 mobiusTable1200001 n) = (17 : ℤ) ∧
    (∑ n ∈ Ico 76544 76800, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (151 : ℕ) ∧
    (∑ n ∈ Ico 76544 76800, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (1109459 : ℤ) ∧
    (∑ n ∈ Ico 76544 76800, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (22189365666523942246722218585 : ℤ) := by
  rcases cdemPrefixStats_76544_76672 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_76672_76800 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 76544 ≤ 76672) (by norm_num : 76672 ≤ 76800), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 76544 ≤ 76672) (by norm_num : 76672 ≤ 76800), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 76544 ≤ 76672) (by norm_num : 76672 ≤ 76800), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 76544 ≤ 76672) (by norm_num : 76672 ≤ 76800), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_76288_76800 :
    (∑ n ∈ Ico 76288 76800, mobiusTreeValue 16 mobiusTable1200001 n) = (28 : ℤ) ∧
    (∑ n ∈ Ico 76288 76800, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (308 : ℕ) ∧
    (∑ n ∈ Ico 76288 76800, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (1830877 : ℤ) ∧
    (∑ n ∈ Ico 76288 76800, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (36617879461993668311484191428 : ℤ) := by
  rcases cdemPrefixStats_76288_76544 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_76544_76800 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 76288 ≤ 76544) (by norm_num : 76544 ≤ 76800), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 76288 ≤ 76544) (by norm_num : 76544 ≤ 76800), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 76288 ≤ 76544) (by norm_num : 76544 ≤ 76800), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 76288 ≤ 76544) (by norm_num : 76544 ≤ 76800), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_75776_76800 :
    (∑ n ∈ Ico 75776 76800, mobiusTreeValue 16 mobiusTable1200001 n) = (16 : ℤ) ∧
    (∑ n ∈ Ico 75776 76800, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (622 : ℕ) ∧
    (∑ n ∈ Ico 75776 76800, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (1042847 : ℤ) ∧
    (∑ n ∈ Ico 75776 76800, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (20857073453855698263968889124 : ℤ) := by
  rcases cdemPrefixStats_75776_76288 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_76288_76800 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 75776 ≤ 76288) (by norm_num : 76288 ≤ 76800), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 75776 ≤ 76288) (by norm_num : 76288 ≤ 76800), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 75776 ≤ 76288) (by norm_num : 76288 ≤ 76800), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 75776 ≤ 76288) (by norm_num : 76288 ≤ 76800), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_76800_76864 :
    (∑ n ∈ Ico 76800 76864, mobiusTreeValue 16 mobiusTable1200001 n) = (-6 : ℤ) ∧
    (∑ n ∈ Ico 76800 76864, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 76800 76864, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-390529 : ℤ) ∧
    (∑ n ∈ Ico 76800 76864, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-7810651600361621728757271791 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_76864_76928 :
    (∑ n ∈ Ico 76864 76928, mobiusTreeValue 16 mobiusTable1200001 n) = (4 : ℤ) ∧
    (∑ n ∈ Ico 76864 76928, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (36 : ℕ) ∧
    (∑ n ∈ Ico 76864 76928, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (260014 : ℤ) ∧
    (∑ n ∈ Ico 76864 76928, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (5200325751068110261063742211 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_76800_76928 :
    (∑ n ∈ Ico 76800 76928, mobiusTreeValue 16 mobiusTable1200001 n) = (-2 : ℤ) ∧
    (∑ n ∈ Ico 76800 76928, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (76 : ℕ) ∧
    (∑ n ∈ Ico 76800 76928, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-130515 : ℤ) ∧
    (∑ n ∈ Ico 76800 76928, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-2610325849293511467693529580 : ℤ) := by
  rcases cdemPrefixStats_76800_76864 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_76864_76928 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 76800 ≤ 76864) (by norm_num : 76864 ≤ 76928), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 76800 ≤ 76864) (by norm_num : 76864 ≤ 76928), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 76800 ≤ 76864) (by norm_num : 76864 ≤ 76928), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 76800 ≤ 76864) (by norm_num : 76864 ≤ 76928), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_76928_76992 :
    (∑ n ∈ Ico 76928 76992, mobiusTreeValue 16 mobiusTable1200001 n) = (-2 : ℤ) ∧
    (∑ n ∈ Ico 76928 76992, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 76928 76992, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-129773 : ℤ) ∧
    (∑ n ∈ Ico 76928 76992, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-2595527993765706438361428682 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_76992_77056 :
    (∑ n ∈ Ico 76992 77056, mobiusTreeValue 16 mobiusTable1200001 n) = (-5 : ℤ) ∧
    (∑ n ∈ Ico 76992 77056, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 76992 77056, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-324487 : ℤ) ∧
    (∑ n ∈ Ico 76992 77056, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-6489780634939444394764396975 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_76928_77056 :
    (∑ n ∈ Ico 76928 77056, mobiusTreeValue 16 mobiusTable1200001 n) = (-7 : ℤ) ∧
    (∑ n ∈ Ico 76928 77056, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (81 : ℕ) ∧
    (∑ n ∈ Ico 76928 77056, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-454260 : ℤ) ∧
    (∑ n ∈ Ico 76928 77056, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-9085308628705150833125825657 : ℤ) := by
  rcases cdemPrefixStats_76928_76992 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_76992_77056 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 76928 ≤ 76992) (by norm_num : 76992 ≤ 77056), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 76928 ≤ 76992) (by norm_num : 76992 ≤ 77056), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 76928 ≤ 76992) (by norm_num : 76992 ≤ 77056), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 76928 ≤ 76992) (by norm_num : 76992 ≤ 77056), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_76800_77056 :
    (∑ n ∈ Ico 76800 77056, mobiusTreeValue 16 mobiusTable1200001 n) = (-9 : ℤ) ∧
    (∑ n ∈ Ico 76800 77056, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (157 : ℕ) ∧
    (∑ n ∈ Ico 76800 77056, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-584775 : ℤ) ∧
    (∑ n ∈ Ico 76800 77056, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-11695634477998662300819355237 : ℤ) := by
  rcases cdemPrefixStats_76800_76928 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_76928_77056 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 76800 ≤ 76928) (by norm_num : 76928 ≤ 77056), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 76800 ≤ 76928) (by norm_num : 76928 ≤ 77056), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 76800 ≤ 76928) (by norm_num : 76928 ≤ 77056), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 76800 ≤ 76928) (by norm_num : 76928 ≤ 77056), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_77056_77120 :
    (∑ n ∈ Ico 77056 77120, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 77056 77120, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 77056 77120, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (64796 : ℤ) ∧
    (∑ n ∈ Ico 77056 77120, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1295889823671167063969291470 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_77120_77184 :
    (∑ n ∈ Ico 77120 77184, mobiusTreeValue 16 mobiusTable1200001 n) = (-4 : ℤ) ∧
    (∑ n ∈ Ico 77120 77184, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 77120 77184, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-259211 : ℤ) ∧
    (∑ n ∈ Ico 77120 77184, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-5184234109448266527152594486 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_77056_77184 :
    (∑ n ∈ Ico 77056 77184, mobiusTreeValue 16 mobiusTable1200001 n) = (-3 : ℤ) ∧
    (∑ n ∈ Ico 77056 77184, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (79 : ℕ) ∧
    (∑ n ∈ Ico 77056 77184, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-194415 : ℤ) ∧
    (∑ n ∈ Ico 77056 77184, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-3888344285777099463183303016 : ℤ) := by
  rcases cdemPrefixStats_77056_77120 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_77120_77184 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 77056 ≤ 77120) (by norm_num : 77120 ≤ 77184), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 77056 ≤ 77120) (by norm_num : 77120 ≤ 77184), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 77056 ≤ 77120) (by norm_num : 77120 ≤ 77184), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 77056 ≤ 77120) (by norm_num : 77120 ≤ 77184), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_77184_77248 :
    (∑ n ∈ Ico 77184 77248, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 77184 77248, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 77184 77248, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (12 : ℤ) ∧
    (∑ n ∈ Ico 77184 77248, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (233798372313613207064439 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_77248_77312 :
    (∑ n ∈ Ico 77248 77312, mobiusTreeValue 16 mobiusTable1200001 n) = (5 : ℤ) ∧
    (∑ n ∈ Ico 77248 77312, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 77248 77312, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (323390 : ℤ) ∧
    (∑ n ∈ Ico 77248 77312, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (6467886807118154139511414088 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_77184_77312 :
    (∑ n ∈ Ico 77184 77312, mobiusTreeValue 16 mobiusTable1200001 n) = (5 : ℤ) ∧
    (∑ n ∈ Ico 77184 77312, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 77184 77312, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (323402 : ℤ) ∧
    (∑ n ∈ Ico 77184 77312, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (6468120605490467752718478527 : ℤ) := by
  rcases cdemPrefixStats_77184_77248 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_77248_77312 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 77184 ≤ 77248) (by norm_num : 77248 ≤ 77312), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 77184 ≤ 77248) (by norm_num : 77248 ≤ 77312), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 77184 ≤ 77248) (by norm_num : 77248 ≤ 77312), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 77184 ≤ 77248) (by norm_num : 77248 ≤ 77312), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_77056_77312 :
    (∑ n ∈ Ico 77056 77312, mobiusTreeValue 16 mobiusTable1200001 n) = (2 : ℤ) ∧
    (∑ n ∈ Ico 77056 77312, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (156 : ℕ) ∧
    (∑ n ∈ Ico 77056 77312, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (128987 : ℤ) ∧
    (∑ n ∈ Ico 77056 77312, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (2579776319713368289535175511 : ℤ) := by
  rcases cdemPrefixStats_77056_77184 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_77184_77312 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 77056 ≤ 77184) (by norm_num : 77184 ≤ 77312), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 77056 ≤ 77184) (by norm_num : 77184 ≤ 77312), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 77056 ≤ 77184) (by norm_num : 77184 ≤ 77312), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 77056 ≤ 77184) (by norm_num : 77184 ≤ 77312), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_76800_77312 :
    (∑ n ∈ Ico 76800 77312, mobiusTreeValue 16 mobiusTable1200001 n) = (-7 : ℤ) ∧
    (∑ n ∈ Ico 76800 77312, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (313 : ℕ) ∧
    (∑ n ∈ Ico 76800 77312, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-455788 : ℤ) ∧
    (∑ n ∈ Ico 76800 77312, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-9115858158285294011284179726 : ℤ) := by
  rcases cdemPrefixStats_76800_77056 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_77056_77312 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 76800 ≤ 77056) (by norm_num : 77056 ≤ 77312), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 76800 ≤ 77056) (by norm_num : 77056 ≤ 77312), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 76800 ≤ 77056) (by norm_num : 77056 ≤ 77312), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 76800 ≤ 77056) (by norm_num : 77056 ≤ 77312), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_77312_77376 :
    (∑ n ∈ Ico 77312 77376, mobiusTreeValue 16 mobiusTable1200001 n) = (-4 : ℤ) ∧
    (∑ n ∈ Ico 77312 77376, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (36 : ℕ) ∧
    (∑ n ∈ Ico 77312 77376, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-258485 : ℤ) ∧
    (∑ n ∈ Ico 77312 77376, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-5169761546098051610941652497 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_77376_77440 :
    (∑ n ∈ Ico 77376 77440, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 77376 77440, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 77376 77440, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-64476 : ℤ) ∧
    (∑ n ∈ Ico 77376 77440, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-1289553680473282434593280418 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_77312_77440 :
    (∑ n ∈ Ico 77312 77440, mobiusTreeValue 16 mobiusTable1200001 n) = (-5 : ℤ) ∧
    (∑ n ∈ Ico 77312 77440, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 77312 77440, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-322961 : ℤ) ∧
    (∑ n ∈ Ico 77312 77440, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-6459315226571334045534932915 : ℤ) := by
  rcases cdemPrefixStats_77312_77376 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_77376_77440 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 77312 ≤ 77376) (by norm_num : 77376 ≤ 77440), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 77312 ≤ 77376) (by norm_num : 77376 ≤ 77440), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 77312 ≤ 77376) (by norm_num : 77376 ≤ 77440), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 77312 ≤ 77376) (by norm_num : 77376 ≤ 77440), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_77440_77504 :
    (∑ n ∈ Ico 77440 77504, mobiusTreeValue 16 mobiusTable1200001 n) = (5 : ℤ) ∧
    (∑ n ∈ Ico 77440 77504, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 77440 77504, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (322799 : ℤ) ∧
    (∑ n ∈ Ico 77440 77504, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (6456010915362515059091093559 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_77504_77568 :
    (∑ n ∈ Ico 77504 77568, mobiusTreeValue 16 mobiusTable1200001 n) = (-10 : ℤ) ∧
    (∑ n ∈ Ico 77504 77568, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 77504 77568, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-644898 : ℤ) ∧
    (∑ n ∈ Ico 77504 77568, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-12898067276632549511707933552 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_77440_77568 :
    (∑ n ∈ Ico 77440 77568, mobiusTreeValue 16 mobiusTable1200001 n) = (-5 : ℤ) ∧
    (∑ n ∈ Ico 77440 77568, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 77440 77568, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-322099 : ℤ) ∧
    (∑ n ∈ Ico 77440 77568, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-6442056361270034452616839993 : ℤ) := by
  rcases cdemPrefixStats_77440_77504 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_77504_77568 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 77440 ≤ 77504) (by norm_num : 77504 ≤ 77568), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 77440 ≤ 77504) (by norm_num : 77504 ≤ 77568), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 77440 ≤ 77504) (by norm_num : 77504 ≤ 77568), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 77440 ≤ 77504) (by norm_num : 77504 ≤ 77568), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_77312_77568 :
    (∑ n ∈ Ico 77312 77568, mobiusTreeValue 16 mobiusTable1200001 n) = (-10 : ℤ) ∧
    (∑ n ∈ Ico 77312 77568, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (154 : ℕ) ∧
    (∑ n ∈ Ico 77312 77568, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-645060 : ℤ) ∧
    (∑ n ∈ Ico 77312 77568, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-12901371587841368498151772908 : ℤ) := by
  rcases cdemPrefixStats_77312_77440 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_77440_77568 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 77312 ≤ 77440) (by norm_num : 77440 ≤ 77568), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 77312 ≤ 77440) (by norm_num : 77440 ≤ 77568), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 77312 ≤ 77440) (by norm_num : 77440 ≤ 77568), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 77312 ≤ 77440) (by norm_num : 77440 ≤ 77568), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_77568_77632 :
    (∑ n ∈ Ico 77568 77632, mobiusTreeValue 16 mobiusTable1200001 n) = (-2 : ℤ) ∧
    (∑ n ∈ Ico 77568 77632, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 77568 77632, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-128933 : ℤ) ∧
    (∑ n ∈ Ico 77568 77632, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-2578681840277150272321476189 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_77632_77696 :
    (∑ n ∈ Ico 77632 77696, mobiusTreeValue 16 mobiusTable1200001 n) = (2 : ℤ) ∧
    (∑ n ∈ Ico 77632 77696, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 77632 77696, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (128767 : ℤ) ∧
    (∑ n ∈ Ico 77632 77696, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (2575344910258460602997250276 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_77568_77696 :
    (∑ n ∈ Ico 77568 77696, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 77568 77696, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 77568 77696, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-166 : ℤ) ∧
    (∑ n ∈ Ico 77568 77696, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-3336930018689669324225913 : ℤ) := by
  rcases cdemPrefixStats_77568_77632 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_77632_77696 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 77568 ≤ 77632) (by norm_num : 77632 ≤ 77696), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 77568 ≤ 77632) (by norm_num : 77632 ≤ 77696), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 77568 ≤ 77632) (by norm_num : 77632 ≤ 77696), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 77568 ≤ 77632) (by norm_num : 77632 ≤ 77696), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_77696_77760 :
    (∑ n ∈ Ico 77696 77760, mobiusTreeValue 16 mobiusTable1200001 n) = (-8 : ℤ) ∧
    (∑ n ∈ Ico 77696 77760, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 77696 77760, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-514733 : ℤ) ∧
    (∑ n ∈ Ico 77696 77760, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-10294685118403256068048428648 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_77760_77824 :
    (∑ n ∈ Ico 77760 77824, mobiusTreeValue 16 mobiusTable1200001 n) = (-3 : ℤ) ∧
    (∑ n ∈ Ico 77760 77824, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 77760 77824, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-192927 : ℤ) ∧
    (∑ n ∈ Ico 77760 77824, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-3858602739189005607332352700 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_77696_77824 :
    (∑ n ∈ Ico 77696 77824, mobiusTreeValue 16 mobiusTable1200001 n) = (-11 : ℤ) ∧
    (∑ n ∈ Ico 77696 77824, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 77696 77824, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-707660 : ℤ) ∧
    (∑ n ∈ Ico 77696 77824, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-14153287857592261675380781348 : ℤ) := by
  rcases cdemPrefixStats_77696_77760 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_77760_77824 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 77696 ≤ 77760) (by norm_num : 77760 ≤ 77824), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 77696 ≤ 77760) (by norm_num : 77760 ≤ 77824), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 77696 ≤ 77760) (by norm_num : 77760 ≤ 77824), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 77696 ≤ 77760) (by norm_num : 77760 ≤ 77824), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_77568_77824 :
    (∑ n ∈ Ico 77568 77824, mobiusTreeValue 16 mobiusTable1200001 n) = (-11 : ℤ) ∧
    (∑ n ∈ Ico 77568 77824, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (155 : ℕ) ∧
    (∑ n ∈ Ico 77568 77824, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-707826 : ℤ) ∧
    (∑ n ∈ Ico 77568 77824, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-14156624787610951344705007261 : ℤ) := by
  rcases cdemPrefixStats_77568_77696 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_77696_77824 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 77568 ≤ 77696) (by norm_num : 77696 ≤ 77824), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 77568 ≤ 77696) (by norm_num : 77696 ≤ 77824), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 77568 ≤ 77696) (by norm_num : 77696 ≤ 77824), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 77568 ≤ 77696) (by norm_num : 77696 ≤ 77824), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_77312_77824 :
    (∑ n ∈ Ico 77312 77824, mobiusTreeValue 16 mobiusTable1200001 n) = (-21 : ℤ) ∧
    (∑ n ∈ Ico 77312 77824, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (309 : ℕ) ∧
    (∑ n ∈ Ico 77312 77824, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-1352886 : ℤ) ∧
    (∑ n ∈ Ico 77312 77824, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-27057996375452319842856780169 : ℤ) := by
  rcases cdemPrefixStats_77312_77568 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_77568_77824 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 77312 ≤ 77568) (by norm_num : 77568 ≤ 77824), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 77312 ≤ 77568) (by norm_num : 77568 ≤ 77824), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 77312 ≤ 77568) (by norm_num : 77568 ≤ 77824), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 77312 ≤ 77568) (by norm_num : 77568 ≤ 77824), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_76800_77824 :
    (∑ n ∈ Ico 76800 77824, mobiusTreeValue 16 mobiusTable1200001 n) = (-28 : ℤ) ∧
    (∑ n ∈ Ico 76800 77824, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (622 : ℕ) ∧
    (∑ n ∈ Ico 76800 77824, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-1808674 : ℤ) ∧
    (∑ n ∈ Ico 76800 77824, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-36173854533737613854140959895 : ℤ) := by
  rcases cdemPrefixStats_76800_77312 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_77312_77824 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 76800 ≤ 77312) (by norm_num : 77312 ≤ 77824), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 76800 ≤ 77312) (by norm_num : 77312 ≤ 77824), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 76800 ≤ 77312) (by norm_num : 77312 ≤ 77824), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 76800 ≤ 77312) (by norm_num : 77312 ≤ 77824), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_75776_77824 :
    (∑ n ∈ Ico 75776 77824, mobiusTreeValue 16 mobiusTable1200001 n) = (-12 : ℤ) ∧
    (∑ n ∈ Ico 75776 77824, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (1244 : ℕ) ∧
    (∑ n ∈ Ico 75776 77824, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-765827 : ℤ) ∧
    (∑ n ∈ Ico 75776 77824, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-15316781079881915590172070771 : ℤ) := by
  rcases cdemPrefixStats_75776_76800 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_76800_77824 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 75776 ≤ 76800) (by norm_num : 76800 ≤ 77824), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 75776 ≤ 76800) (by norm_num : 76800 ≤ 77824), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 75776 ≤ 76800) (by norm_num : 76800 ≤ 77824), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 75776 ≤ 76800) (by norm_num : 76800 ≤ 77824), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_73728_77824 :
    (∑ n ∈ Ico 73728 77824, mobiusTreeValue 16 mobiusTable1200001 n) = (-46 : ℤ) ∧
    (∑ n ∈ Ico 73728 77824, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (2486 : ℕ) ∧
    (∑ n ∈ Ico 73728 77824, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-3011664 : ℤ) ∧
    (∑ n ∈ Ico 73728 77824, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-60233821552229056239255113201 : ℤ) := by
  rcases cdemPrefixStats_73728_75776 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_75776_77824 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 73728 ≤ 75776) (by norm_num : 75776 ≤ 77824), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 73728 ≤ 75776) (by norm_num : 75776 ≤ 77824), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 73728 ≤ 75776) (by norm_num : 75776 ≤ 77824), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 73728 ≤ 75776) (by norm_num : 75776 ≤ 77824), hR1, hR2] <;> norm_num

theorem cdemPrefixGroup018_checked_complete :
    (∑ n ∈ Ico 73728 77824, mobiusTreeValue 16 mobiusTable1200001 n) = (-46 : ℤ) ∧
    (∑ n ∈ Ico 73728 77824, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (2486 : ℕ) ∧
    (∑ n ∈ Ico 73728 77824, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-3011664 : ℤ) ∧
    (∑ n ∈ Ico 73728 77824, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-60233821552229056239255113201 : ℤ) := cdemPrefixStats_73728_77824
end Helfgott
#print axioms Helfgott.cdemPrefixGroup018_checked_complete

open Helfgott Finset
open scoped BigOperators

theorem solution :
    (∑ n ∈ Ico 73728 77824, mobiusTreeValue 16 mobiusTable1200001 n) = (-46 : ℤ) ∧
    (∑ n ∈ Ico 73728 77824, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (2486 : ℕ) ∧
    (∑ n ∈ Ico 73728 77824, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-3011664 : ℤ) ∧
    (∑ n ∈ Ico 73728 77824, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-60233821552229056239255113201 : ℤ) := Helfgott.cdemPrefixGroup018_checked_complete
#print axioms solution
