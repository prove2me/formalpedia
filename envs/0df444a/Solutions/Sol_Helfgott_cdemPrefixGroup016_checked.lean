-- Prove2me | solution 1 for Helfgott.cdemPrefixGroup016_checked
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-09T01:46:29.451625+00:00
-- url     : https://prove2.me/submissions/705e828b-2de2-4429-bd21-d071e0fe6027

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
private theorem cdemPrefixStats_65536_65600 :
    (∑ n ∈ Ico 65536 65600, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 65536 65600, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 65536 65600, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-76428 : ℤ) ∧
    (∑ n ∈ Ico 65536 65600, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-1528601058859510272993188347 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_65600_65664 :
    (∑ n ∈ Ico 65600 65664, mobiusTreeValue 16 mobiusTable1200001 n) = (-8 : ℤ) ∧
    (∑ n ∈ Ico 65600 65664, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 65600 65664, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-609324 : ℤ) ∧
    (∑ n ∈ Ico 65600 65664, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-12186552906851207606138778889 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_65536_65664 :
    (∑ n ∈ Ico 65536 65664, mobiusTreeValue 16 mobiusTable1200001 n) = (-9 : ℤ) ∧
    (∑ n ∈ Ico 65536 65664, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (75 : ℕ) ∧
    (∑ n ∈ Ico 65536 65664, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-685752 : ℤ) ∧
    (∑ n ∈ Ico 65536 65664, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-13715153965710717879131967236 : ℤ) := by
  rcases cdemPrefixStats_65536_65600 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_65600_65664 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 65536 ≤ 65600) (by norm_num : 65600 ≤ 65664), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 65536 ≤ 65600) (by norm_num : 65600 ≤ 65664), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 65536 ≤ 65600) (by norm_num : 65600 ≤ 65664), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 65536 ≤ 65600) (by norm_num : 65600 ≤ 65664), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_65664_65728 :
    (∑ n ∈ Ico 65664 65728, mobiusTreeValue 16 mobiusTable1200001 n) = (-10 : ℤ) ∧
    (∑ n ∈ Ico 65664 65728, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 65664 65728, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-760850 : ℤ) ∧
    (∑ n ∈ Ico 65664 65728, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-15217063279529642466789398730 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_65728_65792 :
    (∑ n ∈ Ico 65728 65792, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 65728 65792, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 65728 65792, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (75933 : ℤ) ∧
    (∑ n ∈ Ico 65728 65792, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1518669336795263507741404282 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_65664_65792 :
    (∑ n ∈ Ico 65664 65792, mobiusTreeValue 16 mobiusTable1200001 n) = (-9 : ℤ) ∧
    (∑ n ∈ Ico 65664 65792, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 65664 65792, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-684917 : ℤ) ∧
    (∑ n ∈ Ico 65664 65792, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-13698393942734378959047994448 : ℤ) := by
  rcases cdemPrefixStats_65664_65728 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_65728_65792 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 65664 ≤ 65728) (by norm_num : 65728 ≤ 65792), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 65664 ≤ 65728) (by norm_num : 65728 ≤ 65792), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 65664 ≤ 65728) (by norm_num : 65728 ≤ 65792), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 65664 ≤ 65728) (by norm_num : 65728 ≤ 65792), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_65536_65792 :
    (∑ n ∈ Ico 65536 65792, mobiusTreeValue 16 mobiusTable1200001 n) = (-18 : ℤ) ∧
    (∑ n ∈ Ico 65536 65792, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (152 : ℕ) ∧
    (∑ n ∈ Ico 65536 65792, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-1370669 : ℤ) ∧
    (∑ n ∈ Ico 65536 65792, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-27413547908445096838179961684 : ℤ) := by
  rcases cdemPrefixStats_65536_65664 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_65664_65792 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 65536 ≤ 65664) (by norm_num : 65664 ≤ 65792), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 65536 ≤ 65664) (by norm_num : 65664 ≤ 65792), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 65536 ≤ 65664) (by norm_num : 65664 ≤ 65792), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 65536 ≤ 65664) (by norm_num : 65664 ≤ 65792), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_65792_65856 :
    (∑ n ∈ Ico 65792 65856, mobiusTreeValue 16 mobiusTable1200001 n) = (-2 : ℤ) ∧
    (∑ n ∈ Ico 65792 65856, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 65792 65856, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-151636 : ℤ) ∧
    (∑ n ∈ Ico 65792 65856, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-3032774289738243661061494239 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_65856_65920 :
    (∑ n ∈ Ico 65856 65920, mobiusTreeValue 16 mobiusTable1200001 n) = (9 : ℤ) ∧
    (∑ n ∈ Ico 65856 65920, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 65856 65920, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (682988 : ℤ) ∧
    (∑ n ∈ Ico 65856 65920, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (13659821263867147197007118414 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_65792_65920 :
    (∑ n ∈ Ico 65792 65920, mobiusTreeValue 16 mobiusTable1200001 n) = (7 : ℤ) ∧
    (∑ n ∈ Ico 65792 65920, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (79 : ℕ) ∧
    (∑ n ∈ Ico 65792 65920, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (531352 : ℤ) ∧
    (∑ n ∈ Ico 65792 65920, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (10627046974128903535945624175 : ℤ) := by
  rcases cdemPrefixStats_65792_65856 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_65856_65920 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 65792 ≤ 65856) (by norm_num : 65856 ≤ 65920), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 65792 ≤ 65856) (by norm_num : 65856 ≤ 65920), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 65792 ≤ 65856) (by norm_num : 65856 ≤ 65920), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 65792 ≤ 65856) (by norm_num : 65856 ≤ 65920), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_65920_65984 :
    (∑ n ∈ Ico 65920 65984, mobiusTreeValue 16 mobiusTable1200001 n) = (4 : ℤ) ∧
    (∑ n ∈ Ico 65920 65984, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 65920 65984, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (303207 : ℤ) ∧
    (∑ n ∈ Ico 65920 65984, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (6064188971603195370266080280 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_65984_66048 :
    (∑ n ∈ Ico 65984 66048, mobiusTreeValue 16 mobiusTable1200001 n) = (-3 : ℤ) ∧
    (∑ n ∈ Ico 65984 66048, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 65984 66048, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-227139 : ℤ) ∧
    (∑ n ∈ Ico 65984 66048, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-4542769883042828324750307185 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_65920_66048 :
    (∑ n ∈ Ico 65920 66048, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 65920 66048, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (79 : ℕ) ∧
    (∑ n ∈ Ico 65920 66048, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (76068 : ℤ) ∧
    (∑ n ∈ Ico 65920 66048, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1521419088560367045515773095 : ℤ) := by
  rcases cdemPrefixStats_65920_65984 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_65984_66048 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 65920 ≤ 65984) (by norm_num : 65984 ≤ 66048), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 65920 ≤ 65984) (by norm_num : 65984 ≤ 66048), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 65920 ≤ 65984) (by norm_num : 65984 ≤ 66048), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 65920 ≤ 65984) (by norm_num : 65984 ≤ 66048), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_65792_66048 :
    (∑ n ∈ Ico 65792 66048, mobiusTreeValue 16 mobiusTable1200001 n) = (8 : ℤ) ∧
    (∑ n ∈ Ico 65792 66048, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (158 : ℕ) ∧
    (∑ n ∈ Ico 65792 66048, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (607420 : ℤ) ∧
    (∑ n ∈ Ico 65792 66048, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (12148466062689270581461397270 : ℤ) := by
  rcases cdemPrefixStats_65792_65920 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_65920_66048 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 65792 ≤ 65920) (by norm_num : 65920 ≤ 66048), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 65792 ≤ 65920) (by norm_num : 65920 ≤ 66048), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 65792 ≤ 65920) (by norm_num : 65920 ≤ 66048), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 65792 ≤ 65920) (by norm_num : 65920 ≤ 66048), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_65536_66048 :
    (∑ n ∈ Ico 65536 66048, mobiusTreeValue 16 mobiusTable1200001 n) = (-10 : ℤ) ∧
    (∑ n ∈ Ico 65536 66048, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (310 : ℕ) ∧
    (∑ n ∈ Ico 65536 66048, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-763249 : ℤ) ∧
    (∑ n ∈ Ico 65536 66048, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-15265081845755826256718564414 : ℤ) := by
  rcases cdemPrefixStats_65536_65792 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_65792_66048 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 65536 ≤ 65792) (by norm_num : 65792 ≤ 66048), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 65536 ≤ 65792) (by norm_num : 65792 ≤ 66048), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 65536 ≤ 65792) (by norm_num : 65792 ≤ 66048), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 65536 ≤ 65792) (by norm_num : 65792 ≤ 66048), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_66048_66112 :
    (∑ n ∈ Ico 66048 66112, mobiusTreeValue 16 mobiusTable1200001 n) = (6 : ℤ) ∧
    (∑ n ∈ Ico 66048 66112, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (36 : ℕ) ∧
    (∑ n ∈ Ico 66048 66112, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (453997 : ℤ) ∧
    (∑ n ∈ Ico 66048 66112, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (9080018567361087852716549638 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_66112_66176 :
    (∑ n ∈ Ico 66112 66176, mobiusTreeValue 16 mobiusTable1200001 n) = (10 : ℤ) ∧
    (∑ n ∈ Ico 66112 66176, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 66112 66176, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (755950 : ℤ) ∧
    (∑ n ∈ Ico 66112 66176, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (15119124858180348393508501587 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_66048_66176 :
    (∑ n ∈ Ico 66048 66176, mobiusTreeValue 16 mobiusTable1200001 n) = (16 : ℤ) ∧
    (∑ n ∈ Ico 66048 66176, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (76 : ℕ) ∧
    (∑ n ∈ Ico 66048 66176, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (1209947 : ℤ) ∧
    (∑ n ∈ Ico 66048 66176, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (24199143425541436246225051225 : ℤ) := by
  rcases cdemPrefixStats_66048_66112 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_66112_66176 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 66048 ≤ 66112) (by norm_num : 66112 ≤ 66176), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 66048 ≤ 66112) (by norm_num : 66112 ≤ 66176), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 66048 ≤ 66112) (by norm_num : 66112 ≤ 66176), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 66048 ≤ 66112) (by norm_num : 66112 ≤ 66176), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_66176_66240 :
    (∑ n ∈ Ico 66176 66240, mobiusTreeValue 16 mobiusTable1200001 n) = (8 : ℤ) ∧
    (∑ n ∈ Ico 66176 66240, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 66176 66240, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (604050 : ℤ) ∧
    (∑ n ∈ Ico 66176 66240, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (12081033975479109949735635544 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_66240_66304 :
    (∑ n ∈ Ico 66240 66304, mobiusTreeValue 16 mobiusTable1200001 n) = (4 : ℤ) ∧
    (∑ n ∈ Ico 66240 66304, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 66240 66304, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (301721 : ℤ) ∧
    (∑ n ∈ Ico 66240 66304, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (6034457657076644421217738705 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_66176_66304 :
    (∑ n ∈ Ico 66176 66304, mobiusTreeValue 16 mobiusTable1200001 n) = (12 : ℤ) ∧
    (∑ n ∈ Ico 66176 66304, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (76 : ℕ) ∧
    (∑ n ∈ Ico 66176 66304, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (905771 : ℤ) ∧
    (∑ n ∈ Ico 66176 66304, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (18115491632555754370953374249 : ℤ) := by
  rcases cdemPrefixStats_66176_66240 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_66240_66304 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 66176 ≤ 66240) (by norm_num : 66240 ≤ 66304), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 66176 ≤ 66240) (by norm_num : 66240 ≤ 66304), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 66176 ≤ 66240) (by norm_num : 66240 ≤ 66304), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 66176 ≤ 66240) (by norm_num : 66240 ≤ 66304), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_66048_66304 :
    (∑ n ∈ Ico 66048 66304, mobiusTreeValue 16 mobiusTable1200001 n) = (28 : ℤ) ∧
    (∑ n ∈ Ico 66048 66304, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (152 : ℕ) ∧
    (∑ n ∈ Ico 66048 66304, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (2115718 : ℤ) ∧
    (∑ n ∈ Ico 66048 66304, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (42314635058097190617178425474 : ℤ) := by
  rcases cdemPrefixStats_66048_66176 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_66176_66304 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 66048 ≤ 66176) (by norm_num : 66176 ≤ 66304), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 66048 ≤ 66176) (by norm_num : 66176 ≤ 66304), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 66048 ≤ 66176) (by norm_num : 66176 ≤ 66304), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 66048 ≤ 66176) (by norm_num : 66176 ≤ 66304), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_66304_66368 :
    (∑ n ∈ Ico 66304 66368, mobiusTreeValue 16 mobiusTable1200001 n) = (-3 : ℤ) ∧
    (∑ n ∈ Ico 66304 66368, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 66304 66368, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-225820 : ℤ) ∧
    (∑ n ∈ Ico 66304 66368, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-4516409486260744313821842567 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_66368_66432 :
    (∑ n ∈ Ico 66368 66432, mobiusTreeValue 16 mobiusTable1200001 n) = (6 : ℤ) ∧
    (∑ n ∈ Ico 66368 66432, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 66368 66432, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (451954 : ℤ) ∧
    (∑ n ∈ Ico 66368 66432, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (9039160926409190916201992316 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_66304_66432 :
    (∑ n ∈ Ico 66304 66432, mobiusTreeValue 16 mobiusTable1200001 n) = (3 : ℤ) ∧
    (∑ n ∈ Ico 66304 66432, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (79 : ℕ) ∧
    (∑ n ∈ Ico 66304 66432, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (226134 : ℤ) ∧
    (∑ n ∈ Ico 66304 66432, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (4522751440148446602380149749 : ℤ) := by
  rcases cdemPrefixStats_66304_66368 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_66368_66432 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 66304 ≤ 66368) (by norm_num : 66368 ≤ 66432), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 66304 ≤ 66368) (by norm_num : 66368 ≤ 66432), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 66304 ≤ 66368) (by norm_num : 66368 ≤ 66432), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 66304 ≤ 66368) (by norm_num : 66368 ≤ 66432), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_66432_66496 :
    (∑ n ∈ Ico 66432 66496, mobiusTreeValue 16 mobiusTable1200001 n) = (2 : ℤ) ∧
    (∑ n ∈ Ico 66432 66496, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 66432 66496, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (150378 : ℤ) ∧
    (∑ n ∈ Ico 66432 66496, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (3007609043447119984598227472 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_66496_66560 :
    (∑ n ∈ Ico 66496 66560, mobiusTreeValue 16 mobiusTable1200001 n) = (-11 : ℤ) ∧
    (∑ n ∈ Ico 66496 66560, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 66496 66560, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-826745 : ℤ) ∧
    (∑ n ∈ Ico 66496 66560, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-16535003027528549745052965301 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_66432_66560 :
    (∑ n ∈ Ico 66432 66560, mobiusTreeValue 16 mobiusTable1200001 n) = (-9 : ℤ) ∧
    (∑ n ∈ Ico 66432 66560, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 66432 66560, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-676367 : ℤ) ∧
    (∑ n ∈ Ico 66432 66560, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-13527393984081429760454737829 : ℤ) := by
  rcases cdemPrefixStats_66432_66496 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_66496_66560 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 66432 ≤ 66496) (by norm_num : 66496 ≤ 66560), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 66432 ≤ 66496) (by norm_num : 66496 ≤ 66560), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 66432 ≤ 66496) (by norm_num : 66496 ≤ 66560), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 66432 ≤ 66496) (by norm_num : 66496 ≤ 66560), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_66304_66560 :
    (∑ n ∈ Ico 66304 66560, mobiusTreeValue 16 mobiusTable1200001 n) = (-6 : ℤ) ∧
    (∑ n ∈ Ico 66304 66560, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (156 : ℕ) ∧
    (∑ n ∈ Ico 66304 66560, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-450233 : ℤ) ∧
    (∑ n ∈ Ico 66304 66560, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-9004642543932983158074588080 : ℤ) := by
  rcases cdemPrefixStats_66304_66432 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_66432_66560 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 66304 ≤ 66432) (by norm_num : 66432 ≤ 66560), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 66304 ≤ 66432) (by norm_num : 66432 ≤ 66560), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 66304 ≤ 66432) (by norm_num : 66432 ≤ 66560), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 66304 ≤ 66432) (by norm_num : 66432 ≤ 66560), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_66048_66560 :
    (∑ n ∈ Ico 66048 66560, mobiusTreeValue 16 mobiusTable1200001 n) = (22 : ℤ) ∧
    (∑ n ∈ Ico 66048 66560, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (308 : ℕ) ∧
    (∑ n ∈ Ico 66048 66560, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (1665485 : ℤ) ∧
    (∑ n ∈ Ico 66048 66560, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (33309992514164207459103837394 : ℤ) := by
  rcases cdemPrefixStats_66048_66304 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_66304_66560 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 66048 ≤ 66304) (by norm_num : 66304 ≤ 66560), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 66048 ≤ 66304) (by norm_num : 66304 ≤ 66560), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 66048 ≤ 66304) (by norm_num : 66304 ≤ 66560), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 66048 ≤ 66304) (by norm_num : 66304 ≤ 66560), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_65536_66560 :
    (∑ n ∈ Ico 65536 66560, mobiusTreeValue 16 mobiusTable1200001 n) = (12 : ℤ) ∧
    (∑ n ∈ Ico 65536 66560, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (618 : ℕ) ∧
    (∑ n ∈ Ico 65536 66560, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (902236 : ℤ) ∧
    (∑ n ∈ Ico 65536 66560, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (18044910668408381202385272980 : ℤ) := by
  rcases cdemPrefixStats_65536_66048 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_66048_66560 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 65536 ≤ 66048) (by norm_num : 66048 ≤ 66560), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 65536 ≤ 66048) (by norm_num : 66048 ≤ 66560), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 65536 ≤ 66048) (by norm_num : 66048 ≤ 66560), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 65536 ≤ 66048) (by norm_num : 66048 ≤ 66560), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_66560_66624 :
    (∑ n ∈ Ico 66560 66624, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 66560 66624, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 66560 66624, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-42 : ℤ) ∧
    (∑ n ∈ Ico 66560 66624, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-880362257846079978781920 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_66624_66688 :
    (∑ n ∈ Ico 66624 66688, mobiusTreeValue 16 mobiusTable1200001 n) = (9 : ℤ) ∧
    (∑ n ∈ Ico 66624 66688, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 66624 66688, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (675058 : ℤ) ∧
    (∑ n ∈ Ico 66624 66688, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (13501239146910792847441686555 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_66560_66688 :
    (∑ n ∈ Ico 66560 66688, mobiusTreeValue 16 mobiusTable1200001 n) = (9 : ℤ) ∧
    (∑ n ∈ Ico 66560 66688, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (79 : ℕ) ∧
    (∑ n ∈ Ico 66560 66688, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (675016 : ℤ) ∧
    (∑ n ∈ Ico 66560 66688, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (13500358784652946767462904635 : ℤ) := by
  rcases cdemPrefixStats_66560_66624 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_66624_66688 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 66560 ≤ 66624) (by norm_num : 66624 ≤ 66688), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 66560 ≤ 66624) (by norm_num : 66624 ≤ 66688), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 66560 ≤ 66624) (by norm_num : 66624 ≤ 66688), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 66560 ≤ 66624) (by norm_num : 66624 ≤ 66688), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_66688_66752 :
    (∑ n ∈ Ico 66688 66752, mobiusTreeValue 16 mobiusTable1200001 n) = (-3 : ℤ) ∧
    (∑ n ∈ Ico 66688 66752, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 66688 66752, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-224646 : ℤ) ∧
    (∑ n ∈ Ico 66688 66752, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-4493011025655379557044069158 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_66752_66816 :
    (∑ n ∈ Ico 66752 66816, mobiusTreeValue 16 mobiusTable1200001 n) = (5 : ℤ) ∧
    (∑ n ∈ Ico 66752 66816, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 66752 66816, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (374445 : ℤ) ∧
    (∑ n ∈ Ico 66752 66816, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (7488953978452099076712532839 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_66688_66816 :
    (∑ n ∈ Ico 66688 66816, mobiusTreeValue 16 mobiusTable1200001 n) = (2 : ℤ) ∧
    (∑ n ∈ Ico 66688 66816, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (76 : ℕ) ∧
    (∑ n ∈ Ico 66688 66816, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (149799 : ℤ) ∧
    (∑ n ∈ Ico 66688 66816, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (2995942952796719519668463681 : ℤ) := by
  rcases cdemPrefixStats_66688_66752 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_66752_66816 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 66688 ≤ 66752) (by norm_num : 66752 ≤ 66816), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 66688 ≤ 66752) (by norm_num : 66752 ≤ 66816), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 66688 ≤ 66752) (by norm_num : 66752 ≤ 66816), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 66688 ≤ 66752) (by norm_num : 66752 ≤ 66816), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_66560_66816 :
    (∑ n ∈ Ico 66560 66816, mobiusTreeValue 16 mobiusTable1200001 n) = (11 : ℤ) ∧
    (∑ n ∈ Ico 66560 66816, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (155 : ℕ) ∧
    (∑ n ∈ Ico 66560 66816, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (824815 : ℤ) ∧
    (∑ n ∈ Ico 66560 66816, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (16496301737449666287131368316 : ℤ) := by
  rcases cdemPrefixStats_66560_66688 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_66688_66816 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 66560 ≤ 66688) (by norm_num : 66688 ≤ 66816), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 66560 ≤ 66688) (by norm_num : 66688 ≤ 66816), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 66560 ≤ 66688) (by norm_num : 66688 ≤ 66816), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 66560 ≤ 66688) (by norm_num : 66688 ≤ 66816), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_66816_66880 :
    (∑ n ∈ Ico 66816 66880, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 66816 66880, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 66816 66880, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (268 : ℤ) ∧
    (∑ n ∈ Ico 66816 66880, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (5304384711803607917425987 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_66880_66944 :
    (∑ n ∈ Ico 66880 66944, mobiusTreeValue 16 mobiusTable1200001 n) = (-7 : ℤ) ∧
    (∑ n ∈ Ico 66880 66944, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 66880 66944, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-522926 : ℤ) ∧
    (∑ n ∈ Ico 66880 66944, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-10458510416850967525260698552 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_66816_66944 :
    (∑ n ∈ Ico 66816 66944, mobiusTreeValue 16 mobiusTable1200001 n) = (-7 : ℤ) ∧
    (∑ n ∈ Ico 66816 66944, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (79 : ℕ) ∧
    (∑ n ∈ Ico 66816 66944, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-522658 : ℤ) ∧
    (∑ n ∈ Ico 66816 66944, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-10453206032139163917343272565 : ℤ) := by
  rcases cdemPrefixStats_66816_66880 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_66880_66944 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 66816 ≤ 66880) (by norm_num : 66880 ≤ 66944), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 66816 ≤ 66880) (by norm_num : 66880 ≤ 66944), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 66816 ≤ 66880) (by norm_num : 66880 ≤ 66944), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 66816 ≤ 66880) (by norm_num : 66880 ≤ 66944), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_66944_67008 :
    (∑ n ∈ Ico 66944 67008, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 66944 67008, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 66944 67008, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-243 : ℤ) ∧
    (∑ n ∈ Ico 66944 67008, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-4904783184871134320204696 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_67008_67072 :
    (∑ n ∈ Ico 67008 67072, mobiusTreeValue 16 mobiusTable1200001 n) = (3 : ℤ) ∧
    (∑ n ∈ Ico 67008 67072, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 67008 67072, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (223577 : ℤ) ∧
    (∑ n ∈ Ico 67008 67072, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (4471558812770964022292817573 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_66944_67072 :
    (∑ n ∈ Ico 66944 67072, mobiusTreeValue 16 mobiusTable1200001 n) = (3 : ℤ) ∧
    (∑ n ∈ Ico 66944 67072, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (81 : ℕ) ∧
    (∑ n ∈ Ico 66944 67072, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (223334 : ℤ) ∧
    (∑ n ∈ Ico 66944 67072, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (4466654029586092887972612877 : ℤ) := by
  rcases cdemPrefixStats_66944_67008 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_67008_67072 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 66944 ≤ 67008) (by norm_num : 67008 ≤ 67072), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 66944 ≤ 67008) (by norm_num : 67008 ≤ 67072), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 66944 ≤ 67008) (by norm_num : 67008 ≤ 67072), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 66944 ≤ 67008) (by norm_num : 67008 ≤ 67072), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_66816_67072 :
    (∑ n ∈ Ico 66816 67072, mobiusTreeValue 16 mobiusTable1200001 n) = (-4 : ℤ) ∧
    (∑ n ∈ Ico 66816 67072, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (160 : ℕ) ∧
    (∑ n ∈ Ico 66816 67072, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-299324 : ℤ) ∧
    (∑ n ∈ Ico 66816 67072, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-5986552002553071029370659688 : ℤ) := by
  rcases cdemPrefixStats_66816_66944 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_66944_67072 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 66816 ≤ 66944) (by norm_num : 66944 ≤ 67072), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 66816 ≤ 66944) (by norm_num : 66944 ≤ 67072), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 66816 ≤ 66944) (by norm_num : 66944 ≤ 67072), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 66816 ≤ 66944) (by norm_num : 66944 ≤ 67072), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_66560_67072 :
    (∑ n ∈ Ico 66560 67072, mobiusTreeValue 16 mobiusTable1200001 n) = (7 : ℤ) ∧
    (∑ n ∈ Ico 66560 67072, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (315 : ℕ) ∧
    (∑ n ∈ Ico 66560 67072, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (525491 : ℤ) ∧
    (∑ n ∈ Ico 66560 67072, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (10509749734896595257760708628 : ℤ) := by
  rcases cdemPrefixStats_66560_66816 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_66816_67072 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 66560 ≤ 66816) (by norm_num : 66816 ≤ 67072), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 66560 ≤ 66816) (by norm_num : 66816 ≤ 67072), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 66560 ≤ 66816) (by norm_num : 66816 ≤ 67072), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 66560 ≤ 66816) (by norm_num : 66816 ≤ 67072), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_67072_67136 :
    (∑ n ∈ Ico 67072 67136, mobiusTreeValue 16 mobiusTable1200001 n) = (3 : ℤ) ∧
    (∑ n ∈ Ico 67072 67136, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 67072 67136, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (223576 : ℤ) ∧
    (∑ n ∈ Ico 67072 67136, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (4471604205532430421912952860 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_67136_67200 :
    (∑ n ∈ Ico 67136 67200, mobiusTreeValue 16 mobiusTable1200001 n) = (-3 : ℤ) ∧
    (∑ n ∈ Ico 67136 67200, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 67136 67200, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-223166 : ℤ) ∧
    (∑ n ∈ Ico 67136 67200, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-4463288509535273458938359039 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_67072_67200 :
    (∑ n ∈ Ico 67072 67200, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 67072 67200, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (74 : ℕ) ∧
    (∑ n ∈ Ico 67072 67200, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (410 : ℤ) ∧
    (∑ n ∈ Ico 67072 67200, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (8315695997156962974593821 : ℤ) := by
  rcases cdemPrefixStats_67072_67136 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_67136_67200 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 67072 ≤ 67136) (by norm_num : 67136 ≤ 67200), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 67072 ≤ 67136) (by norm_num : 67136 ≤ 67200), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 67072 ≤ 67136) (by norm_num : 67136 ≤ 67200), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 67072 ≤ 67136) (by norm_num : 67136 ≤ 67200), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_67200_67264 :
    (∑ n ∈ Ico 67200 67264, mobiusTreeValue 16 mobiusTable1200001 n) = (4 : ℤ) ∧
    (∑ n ∈ Ico 67200 67264, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 67200 67264, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (297383 : ℤ) ∧
    (∑ n ∈ Ico 67200 67264, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (5947667414693495892764230499 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_67264_67328 :
    (∑ n ∈ Ico 67264 67328, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 67264 67328, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 67264 67328, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-74378 : ℤ) ∧
    (∑ n ∈ Ico 67264 67328, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-1487540339500101439983244239 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_67200_67328 :
    (∑ n ∈ Ico 67200 67328, mobiusTreeValue 16 mobiusTable1200001 n) = (3 : ℤ) ∧
    (∑ n ∈ Ico 67200 67328, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (79 : ℕ) ∧
    (∑ n ∈ Ico 67200 67328, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (223005 : ℤ) ∧
    (∑ n ∈ Ico 67200 67328, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (4460127075193394452780986260 : ℤ) := by
  rcases cdemPrefixStats_67200_67264 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_67264_67328 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 67200 ≤ 67264) (by norm_num : 67264 ≤ 67328), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 67200 ≤ 67264) (by norm_num : 67264 ≤ 67328), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 67200 ≤ 67264) (by norm_num : 67264 ≤ 67328), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 67200 ≤ 67264) (by norm_num : 67264 ≤ 67328), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_67072_67328 :
    (∑ n ∈ Ico 67072 67328, mobiusTreeValue 16 mobiusTable1200001 n) = (3 : ℤ) ∧
    (∑ n ∈ Ico 67072 67328, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (153 : ℕ) ∧
    (∑ n ∈ Ico 67072 67328, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (223415 : ℤ) ∧
    (∑ n ∈ Ico 67072 67328, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (4468442771190551415755580081 : ℤ) := by
  rcases cdemPrefixStats_67072_67200 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_67200_67328 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 67072 ≤ 67200) (by norm_num : 67200 ≤ 67328), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 67072 ≤ 67200) (by norm_num : 67200 ≤ 67328), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 67072 ≤ 67200) (by norm_num : 67200 ≤ 67328), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 67072 ≤ 67200) (by norm_num : 67200 ≤ 67328), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_67328_67392 :
    (∑ n ∈ Ico 67328 67392, mobiusTreeValue 16 mobiusTable1200001 n) = (-2 : ℤ) ∧
    (∑ n ∈ Ico 67328 67392, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 67328 67392, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-148445 : ℤ) ∧
    (∑ n ∈ Ico 67328 67392, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-2968834875028219976758220889 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_67392_67456 :
    (∑ n ∈ Ico 67392 67456, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 67392 67456, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 67392 67456, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-77 : ℤ) ∧
    (∑ n ∈ Ico 67392 67456, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-1517822913638814252093315 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_67328_67456 :
    (∑ n ∈ Ico 67328 67456, mobiusTreeValue 16 mobiusTable1200001 n) = (-2 : ℤ) ∧
    (∑ n ∈ Ico 67328 67456, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (76 : ℕ) ∧
    (∑ n ∈ Ico 67328 67456, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-148522 : ℤ) ∧
    (∑ n ∈ Ico 67328 67456, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-2970352697941858791010314204 : ℤ) := by
  rcases cdemPrefixStats_67328_67392 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_67392_67456 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 67328 ≤ 67392) (by norm_num : 67392 ≤ 67456), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 67328 ≤ 67392) (by norm_num : 67392 ≤ 67456), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 67328 ≤ 67392) (by norm_num : 67392 ≤ 67456), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 67328 ≤ 67392) (by norm_num : 67392 ≤ 67456), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_67456_67520 :
    (∑ n ∈ Ico 67456 67520, mobiusTreeValue 16 mobiusTable1200001 n) = (-3 : ℤ) ∧
    (∑ n ∈ Ico 67456 67520, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 67456 67520, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-222567 : ℤ) ∧
    (∑ n ∈ Ico 67456 67520, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-4451316134771412144759152169 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_67520_67584 :
    (∑ n ∈ Ico 67520 67584, mobiusTreeValue 16 mobiusTable1200001 n) = (-2 : ℤ) ∧
    (∑ n ∈ Ico 67520 67584, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 67520 67584, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-148221 : ℤ) ∧
    (∑ n ∈ Ico 67520 67584, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-2964429754400055858971892740 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_67456_67584 :
    (∑ n ∈ Ico 67456 67584, mobiusTreeValue 16 mobiusTable1200001 n) = (-5 : ℤ) ∧
    (∑ n ∈ Ico 67456 67584, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (79 : ℕ) ∧
    (∑ n ∈ Ico 67456 67584, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-370788 : ℤ) ∧
    (∑ n ∈ Ico 67456 67584, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-7415745889171468003731044909 : ℤ) := by
  rcases cdemPrefixStats_67456_67520 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_67520_67584 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 67456 ≤ 67520) (by norm_num : 67520 ≤ 67584), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 67456 ≤ 67520) (by norm_num : 67520 ≤ 67584), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 67456 ≤ 67520) (by norm_num : 67520 ≤ 67584), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 67456 ≤ 67520) (by norm_num : 67520 ≤ 67584), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_67328_67584 :
    (∑ n ∈ Ico 67328 67584, mobiusTreeValue 16 mobiusTable1200001 n) = (-7 : ℤ) ∧
    (∑ n ∈ Ico 67328 67584, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (155 : ℕ) ∧
    (∑ n ∈ Ico 67328 67584, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-519310 : ℤ) ∧
    (∑ n ∈ Ico 67328 67584, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-10386098587113326794741359113 : ℤ) := by
  rcases cdemPrefixStats_67328_67456 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_67456_67584 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 67328 ≤ 67456) (by norm_num : 67456 ≤ 67584), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 67328 ≤ 67456) (by norm_num : 67456 ≤ 67584), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 67328 ≤ 67456) (by norm_num : 67456 ≤ 67584), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 67328 ≤ 67456) (by norm_num : 67456 ≤ 67584), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_67072_67584 :
    (∑ n ∈ Ico 67072 67584, mobiusTreeValue 16 mobiusTable1200001 n) = (-4 : ℤ) ∧
    (∑ n ∈ Ico 67072 67584, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (308 : ℕ) ∧
    (∑ n ∈ Ico 67072 67584, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-295895 : ℤ) ∧
    (∑ n ∈ Ico 67072 67584, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-5917655815922775378985779032 : ℤ) := by
  rcases cdemPrefixStats_67072_67328 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_67328_67584 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 67072 ≤ 67328) (by norm_num : 67328 ≤ 67584), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 67072 ≤ 67328) (by norm_num : 67328 ≤ 67584), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 67072 ≤ 67328) (by norm_num : 67328 ≤ 67584), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 67072 ≤ 67328) (by norm_num : 67328 ≤ 67584), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_66560_67584 :
    (∑ n ∈ Ico 66560 67584, mobiusTreeValue 16 mobiusTable1200001 n) = (3 : ℤ) ∧
    (∑ n ∈ Ico 66560 67584, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (623 : ℕ) ∧
    (∑ n ∈ Ico 66560 67584, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (229596 : ℤ) ∧
    (∑ n ∈ Ico 66560 67584, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (4592093918973819878774929596 : ℤ) := by
  rcases cdemPrefixStats_66560_67072 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_67072_67584 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 66560 ≤ 67072) (by norm_num : 67072 ≤ 67584), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 66560 ≤ 67072) (by norm_num : 67072 ≤ 67584), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 66560 ≤ 67072) (by norm_num : 67072 ≤ 67584), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 66560 ≤ 67072) (by norm_num : 67072 ≤ 67584), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_65536_67584 :
    (∑ n ∈ Ico 65536 67584, mobiusTreeValue 16 mobiusTable1200001 n) = (15 : ℤ) ∧
    (∑ n ∈ Ico 65536 67584, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (1241 : ℕ) ∧
    (∑ n ∈ Ico 65536 67584, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (1131832 : ℤ) ∧
    (∑ n ∈ Ico 65536 67584, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (22637004587382201081160202576 : ℤ) := by
  rcases cdemPrefixStats_65536_66560 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_66560_67584 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 65536 ≤ 66560) (by norm_num : 66560 ≤ 67584), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 65536 ≤ 66560) (by norm_num : 66560 ≤ 67584), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 65536 ≤ 66560) (by norm_num : 66560 ≤ 67584), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 65536 ≤ 66560) (by norm_num : 66560 ≤ 67584), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_67584_67648 :
    (∑ n ∈ Ico 67584 67648, mobiusTreeValue 16 mobiusTable1200001 n) = (-5 : ℤ) ∧
    (∑ n ∈ Ico 67584 67648, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 67584 67648, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-369715 : ℤ) ∧
    (∑ n ∈ Ico 67584 67648, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-7394416813064574184265125245 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_67648_67712 :
    (∑ n ∈ Ico 67648 67712, mobiusTreeValue 16 mobiusTable1200001 n) = (3 : ℤ) ∧
    (∑ n ∈ Ico 67648 67712, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 67648 67712, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (221795 : ℤ) ∧
    (∑ n ∈ Ico 67648 67712, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (4435942029430318300769412738 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_67584_67712 :
    (∑ n ∈ Ico 67584 67712, mobiusTreeValue 16 mobiusTable1200001 n) = (-2 : ℤ) ∧
    (∑ n ∈ Ico 67584 67712, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (80 : ℕ) ∧
    (∑ n ∈ Ico 67584 67712, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-147920 : ℤ) ∧
    (∑ n ∈ Ico 67584 67712, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-2958474783634255883495712507 : ℤ) := by
  rcases cdemPrefixStats_67584_67648 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_67648_67712 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 67584 ≤ 67648) (by norm_num : 67648 ≤ 67712), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 67584 ≤ 67648) (by norm_num : 67648 ≤ 67712), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 67584 ≤ 67648) (by norm_num : 67648 ≤ 67712), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 67584 ≤ 67648) (by norm_num : 67648 ≤ 67712), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_67712_67776 :
    (∑ n ∈ Ico 67712 67776, mobiusTreeValue 16 mobiusTable1200001 n) = (-2 : ℤ) ∧
    (∑ n ∈ Ico 67712 67776, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 67712 67776, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-147492 : ℤ) ∧
    (∑ n ∈ Ico 67712 67776, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-2949893414043096251367675777 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_67776_67840 :
    (∑ n ∈ Ico 67776 67840, mobiusTreeValue 16 mobiusTable1200001 n) = (-8 : ℤ) ∧
    (∑ n ∈ Ico 67776 67840, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (42 : ℕ) ∧
    (∑ n ∈ Ico 67776 67840, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-590021 : ℤ) ∧
    (∑ n ∈ Ico 67776 67840, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-11800476446661439299309115507 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_67712_67840 :
    (∑ n ∈ Ico 67712 67840, mobiusTreeValue 16 mobiusTable1200001 n) = (-10 : ℤ) ∧
    (∑ n ∈ Ico 67712 67840, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (80 : ℕ) ∧
    (∑ n ∈ Ico 67712 67840, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-737513 : ℤ) ∧
    (∑ n ∈ Ico 67712 67840, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-14750369860704535550676791284 : ℤ) := by
  rcases cdemPrefixStats_67712_67776 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_67776_67840 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 67712 ≤ 67776) (by norm_num : 67776 ≤ 67840), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 67712 ≤ 67776) (by norm_num : 67776 ≤ 67840), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 67712 ≤ 67776) (by norm_num : 67776 ≤ 67840), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 67712 ≤ 67776) (by norm_num : 67776 ≤ 67840), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_67584_67840 :
    (∑ n ∈ Ico 67584 67840, mobiusTreeValue 16 mobiusTable1200001 n) = (-12 : ℤ) ∧
    (∑ n ∈ Ico 67584 67840, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (160 : ℕ) ∧
    (∑ n ∈ Ico 67584 67840, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-885433 : ℤ) ∧
    (∑ n ∈ Ico 67584 67840, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-17708844644338791434172503791 : ℤ) := by
  rcases cdemPrefixStats_67584_67712 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_67712_67840 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 67584 ≤ 67712) (by norm_num : 67712 ≤ 67840), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 67584 ≤ 67712) (by norm_num : 67712 ≤ 67840), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 67584 ≤ 67712) (by norm_num : 67712 ≤ 67840), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 67584 ≤ 67712) (by norm_num : 67712 ≤ 67840), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_67840_67904 :
    (∑ n ∈ Ico 67840 67904, mobiusTreeValue 16 mobiusTable1200001 n) = (3 : ℤ) ∧
    (∑ n ∈ Ico 67840 67904, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 67840 67904, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (221089 : ℤ) ∧
    (∑ n ∈ Ico 67840 67904, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (4421820873328291319202328760 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_67904_67968 :
    (∑ n ∈ Ico 67904 67968, mobiusTreeValue 16 mobiusTable1200001 n) = (-4 : ℤ) ∧
    (∑ n ∈ Ico 67904 67968, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 67904 67968, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-294340 : ℤ) ∧
    (∑ n ∈ Ico 67904 67968, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-5886833449178749359098757897 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_67840_67968 :
    (∑ n ∈ Ico 67840 67968, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 67840 67968, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 67840 67968, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-73251 : ℤ) ∧
    (∑ n ∈ Ico 67840 67968, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-1465012575850458039896429137 : ℤ) := by
  rcases cdemPrefixStats_67840_67904 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_67904_67968 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 67840 ≤ 67904) (by norm_num : 67904 ≤ 67968), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 67840 ≤ 67904) (by norm_num : 67904 ≤ 67968), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 67840 ≤ 67904) (by norm_num : 67904 ≤ 67968), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 67840 ≤ 67904) (by norm_num : 67904 ≤ 67968), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_67968_68032 :
    (∑ n ∈ Ico 67968 68032, mobiusTreeValue 16 mobiusTable1200001 n) = (5 : ℤ) ∧
    (∑ n ∈ Ico 67968 68032, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 67968 68032, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (367500 : ℤ) ∧
    (∑ n ∈ Ico 67968 68032, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (7350043257974047138833387085 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_68032_68096 :
    (∑ n ∈ Ico 68032 68096, mobiusTreeValue 16 mobiusTable1200001 n) = (8 : ℤ) ∧
    (∑ n ∈ Ico 68032 68096, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 68032 68096, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (587544 : ℤ) ∧
    (∑ n ∈ Ico 68032 68096, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (11750989447449919266503723175 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_67968_68096 :
    (∑ n ∈ Ico 67968 68096, mobiusTreeValue 16 mobiusTable1200001 n) = (13 : ℤ) ∧
    (∑ n ∈ Ico 67968 68096, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (79 : ℕ) ∧
    (∑ n ∈ Ico 67968 68096, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (955044 : ℤ) ∧
    (∑ n ∈ Ico 67968 68096, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (19101032705423966405337110260 : ℤ) := by
  rcases cdemPrefixStats_67968_68032 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_68032_68096 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 67968 ≤ 68032) (by norm_num : 68032 ≤ 68096), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 67968 ≤ 68032) (by norm_num : 68032 ≤ 68096), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 67968 ≤ 68032) (by norm_num : 68032 ≤ 68096), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 67968 ≤ 68032) (by norm_num : 68032 ≤ 68096), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_67840_68096 :
    (∑ n ∈ Ico 67840 68096, mobiusTreeValue 16 mobiusTable1200001 n) = (12 : ℤ) ∧
    (∑ n ∈ Ico 67840 68096, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (156 : ℕ) ∧
    (∑ n ∈ Ico 67840 68096, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (881793 : ℤ) ∧
    (∑ n ∈ Ico 67840 68096, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (17636020129573508365440681123 : ℤ) := by
  rcases cdemPrefixStats_67840_67968 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_67968_68096 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 67840 ≤ 67968) (by norm_num : 67968 ≤ 68096), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 67840 ≤ 67968) (by norm_num : 67968 ≤ 68096), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 67840 ≤ 67968) (by norm_num : 67968 ≤ 68096), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 67840 ≤ 67968) (by norm_num : 67968 ≤ 68096), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_67584_68096 :
    (∑ n ∈ Ico 67584 68096, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 67584 68096, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (316 : ℕ) ∧
    (∑ n ∈ Ico 67584 68096, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-3640 : ℤ) ∧
    (∑ n ∈ Ico 67584 68096, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-72824514765283068731822668 : ℤ) := by
  rcases cdemPrefixStats_67584_67840 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_67840_68096 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 67584 ≤ 67840) (by norm_num : 67840 ≤ 68096), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 67584 ≤ 67840) (by norm_num : 67840 ≤ 68096), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 67584 ≤ 67840) (by norm_num : 67840 ≤ 68096), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 67584 ≤ 67840) (by norm_num : 67840 ≤ 68096), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_68096_68160 :
    (∑ n ∈ Ico 68096 68160, mobiusTreeValue 16 mobiusTable1200001 n) = (-3 : ℤ) ∧
    (∑ n ∈ Ico 68096 68160, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 68096 68160, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-220320 : ℤ) ∧
    (∑ n ∈ Ico 68096 68160, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-4406450583424565205263381139 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_68160_68224 :
    (∑ n ∈ Ico 68160 68224, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 68160 68224, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (43 : ℕ) ∧
    (∑ n ∈ Ico 68160 68224, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (73403 : ℤ) ∧
    (∑ n ∈ Ico 68160 68224, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1468017722044423804360843049 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_68096_68224 :
    (∑ n ∈ Ico 68096 68224, mobiusTreeValue 16 mobiusTable1200001 n) = (-2 : ℤ) ∧
    (∑ n ∈ Ico 68096 68224, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (80 : ℕ) ∧
    (∑ n ∈ Ico 68096 68224, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-146917 : ℤ) ∧
    (∑ n ∈ Ico 68096 68224, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-2938432861380141400902538090 : ℤ) := by
  rcases cdemPrefixStats_68096_68160 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_68160_68224 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 68096 ≤ 68160) (by norm_num : 68160 ≤ 68224), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 68096 ≤ 68160) (by norm_num : 68160 ≤ 68224), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 68096 ≤ 68160) (by norm_num : 68160 ≤ 68224), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 68096 ≤ 68160) (by norm_num : 68160 ≤ 68224), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_68224_68288 :
    (∑ n ∈ Ico 68224 68288, mobiusTreeValue 16 mobiusTable1200001 n) = (2 : ℤ) ∧
    (∑ n ∈ Ico 68224 68288, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (36 : ℕ) ∧
    (∑ n ∈ Ico 68224 68288, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (146477 : ℤ) ∧
    (∑ n ∈ Ico 68224 68288, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (2929608238443311864678375376 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_68288_68352 :
    (∑ n ∈ Ico 68288 68352, mobiusTreeValue 16 mobiusTable1200001 n) = (10 : ℤ) ∧
    (∑ n ∈ Ico 68288 68352, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 68288 68352, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (731899 : ℤ) ∧
    (∑ n ∈ Ico 68288 68352, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (14638075106664568467382755547 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_68224_68352 :
    (∑ n ∈ Ico 68224 68352, mobiusTreeValue 16 mobiusTable1200001 n) = (12 : ℤ) ∧
    (∑ n ∈ Ico 68224 68352, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (76 : ℕ) ∧
    (∑ n ∈ Ico 68224 68352, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (878376 : ℤ) ∧
    (∑ n ∈ Ico 68224 68352, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (17567683345107880332061130923 : ℤ) := by
  rcases cdemPrefixStats_68224_68288 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_68288_68352 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 68224 ≤ 68288) (by norm_num : 68288 ≤ 68352), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 68224 ≤ 68288) (by norm_num : 68288 ≤ 68352), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 68224 ≤ 68288) (by norm_num : 68288 ≤ 68352), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 68224 ≤ 68288) (by norm_num : 68288 ≤ 68352), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_68096_68352 :
    (∑ n ∈ Ico 68096 68352, mobiusTreeValue 16 mobiusTable1200001 n) = (10 : ℤ) ∧
    (∑ n ∈ Ico 68096 68352, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (156 : ℕ) ∧
    (∑ n ∈ Ico 68096 68352, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (731459 : ℤ) ∧
    (∑ n ∈ Ico 68096 68352, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (14629250483727738931158592833 : ℤ) := by
  rcases cdemPrefixStats_68096_68224 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_68224_68352 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 68096 ≤ 68224) (by norm_num : 68224 ≤ 68352), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 68096 ≤ 68224) (by norm_num : 68224 ≤ 68352), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 68096 ≤ 68224) (by norm_num : 68224 ≤ 68352), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 68096 ≤ 68224) (by norm_num : 68224 ≤ 68352), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_68352_68416 :
    (∑ n ∈ Ico 68352 68416, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 68352 68416, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 68352 68416, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (73336 : ℤ) ∧
    (∑ n ∈ Ico 68352 68416, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1466693180525812721982792582 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_68416_68480 :
    (∑ n ∈ Ico 68416 68480, mobiusTreeValue 16 mobiusTable1200001 n) = (6 : ℤ) ∧
    (∑ n ∈ Ico 68416 68480, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 68416 68480, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (438431 : ℤ) ∧
    (∑ n ∈ Ico 68416 68480, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (8768661166059857367875220959 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_68352_68480 :
    (∑ n ∈ Ico 68352 68480, mobiusTreeValue 16 mobiusTable1200001 n) = (7 : ℤ) ∧
    (∑ n ∈ Ico 68352 68480, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 68352 68480, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (511767 : ℤ) ∧
    (∑ n ∈ Ico 68352 68480, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (10235354346585670089858013541 : ℤ) := by
  rcases cdemPrefixStats_68352_68416 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_68416_68480 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 68352 ≤ 68416) (by norm_num : 68416 ≤ 68480), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 68352 ≤ 68416) (by norm_num : 68416 ≤ 68480), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 68352 ≤ 68416) (by norm_num : 68416 ≤ 68480), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 68352 ≤ 68416) (by norm_num : 68416 ≤ 68480), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_68480_68544 :
    (∑ n ∈ Ico 68480 68544, mobiusTreeValue 16 mobiusTable1200001 n) = (-8 : ℤ) ∧
    (∑ n ∈ Ico 68480 68544, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 68480 68544, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-583915 : ℤ) ∧
    (∑ n ∈ Ico 68480 68544, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-11678449833380173988032426178 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_68544_68608 :
    (∑ n ∈ Ico 68544 68608, mobiusTreeValue 16 mobiusTable1200001 n) = (10 : ℤ) ∧
    (∑ n ∈ Ico 68544 68608, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 68544 68608, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (729086 : ℤ) ∧
    (∑ n ∈ Ico 68544 68608, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (14581852613298267970962003966 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_68480_68608 :
    (∑ n ∈ Ico 68480 68608, mobiusTreeValue 16 mobiusTable1200001 n) = (2 : ℤ) ∧
    (∑ n ∈ Ico 68480 68608, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (76 : ℕ) ∧
    (∑ n ∈ Ico 68480 68608, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (145171 : ℤ) ∧
    (∑ n ∈ Ico 68480 68608, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (2903402779918093982929577788 : ℤ) := by
  rcases cdemPrefixStats_68480_68544 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_68544_68608 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 68480 ≤ 68544) (by norm_num : 68544 ≤ 68608), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 68480 ≤ 68544) (by norm_num : 68544 ≤ 68608), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 68480 ≤ 68544) (by norm_num : 68544 ≤ 68608), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 68480 ≤ 68544) (by norm_num : 68544 ≤ 68608), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_68352_68608 :
    (∑ n ∈ Ico 68352 68608, mobiusTreeValue 16 mobiusTable1200001 n) = (9 : ℤ) ∧
    (∑ n ∈ Ico 68352 68608, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (153 : ℕ) ∧
    (∑ n ∈ Ico 68352 68608, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (656938 : ℤ) ∧
    (∑ n ∈ Ico 68352 68608, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (13138757126503764072787591329 : ℤ) := by
  rcases cdemPrefixStats_68352_68480 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_68480_68608 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 68352 ≤ 68480) (by norm_num : 68480 ≤ 68608), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 68352 ≤ 68480) (by norm_num : 68480 ≤ 68608), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 68352 ≤ 68480) (by norm_num : 68480 ≤ 68608), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 68352 ≤ 68480) (by norm_num : 68480 ≤ 68608), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_68096_68608 :
    (∑ n ∈ Ico 68096 68608, mobiusTreeValue 16 mobiusTable1200001 n) = (19 : ℤ) ∧
    (∑ n ∈ Ico 68096 68608, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (309 : ℕ) ∧
    (∑ n ∈ Ico 68096 68608, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (1388397 : ℤ) ∧
    (∑ n ∈ Ico 68096 68608, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (27768007610231503003946184162 : ℤ) := by
  rcases cdemPrefixStats_68096_68352 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_68352_68608 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 68096 ≤ 68352) (by norm_num : 68352 ≤ 68608), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 68096 ≤ 68352) (by norm_num : 68352 ≤ 68608), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 68096 ≤ 68352) (by norm_num : 68352 ≤ 68608), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 68096 ≤ 68352) (by norm_num : 68352 ≤ 68608), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_67584_68608 :
    (∑ n ∈ Ico 67584 68608, mobiusTreeValue 16 mobiusTable1200001 n) = (19 : ℤ) ∧
    (∑ n ∈ Ico 67584 68608, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (625 : ℕ) ∧
    (∑ n ∈ Ico 67584 68608, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (1384757 : ℤ) ∧
    (∑ n ∈ Ico 67584 68608, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (27695183095466219935214361494 : ℤ) := by
  rcases cdemPrefixStats_67584_68096 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_68096_68608 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 67584 ≤ 68096) (by norm_num : 68096 ≤ 68608), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 67584 ≤ 68096) (by norm_num : 68096 ≤ 68608), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 67584 ≤ 68096) (by norm_num : 68096 ≤ 68608), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 67584 ≤ 68096) (by norm_num : 68096 ≤ 68608), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_68608_68672 :
    (∑ n ∈ Ico 68608 68672, mobiusTreeValue 16 mobiusTable1200001 n) = (3 : ℤ) ∧
    (∑ n ∈ Ico 68608 68672, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 68608 68672, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (218592 : ℤ) ∧
    (∑ n ∈ Ico 68608 68672, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (4371923874831357921870117383 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_68672_68736 :
    (∑ n ∈ Ico 68672 68736, mobiusTreeValue 16 mobiusTable1200001 n) = (-3 : ℤ) ∧
    (∑ n ∈ Ico 68672 68736, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 68672 68736, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-218337 : ℤ) ∧
    (∑ n ∈ Ico 68672 68736, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-4366770583271695632437680954 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_68608_68736 :
    (∑ n ∈ Ico 68608 68736, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 68608 68736, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 68608 68736, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (255 : ℤ) ∧
    (∑ n ∈ Ico 68608 68736, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (5153291559662289432436429 : ℤ) := by
  rcases cdemPrefixStats_68608_68672 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_68672_68736 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 68608 ≤ 68672) (by norm_num : 68672 ≤ 68736), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 68608 ≤ 68672) (by norm_num : 68672 ≤ 68736), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 68608 ≤ 68672) (by norm_num : 68672 ≤ 68736), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 68608 ≤ 68672) (by norm_num : 68672 ≤ 68736), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_68736_68800 :
    (∑ n ∈ Ico 68736 68800, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 68736 68800, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 68736 68800, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (72659 : ℤ) ∧
    (∑ n ∈ Ico 68736 68800, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1453234193677554420513711479 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_68800_68864 :
    (∑ n ∈ Ico 68800 68864, mobiusTreeValue 16 mobiusTable1200001 n) = (3 : ℤ) ∧
    (∑ n ∈ Ico 68800 68864, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 68800 68864, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (217974 : ℤ) ∧
    (∑ n ∈ Ico 68800 68864, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (4359473049376204860105438883 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_68736_68864 :
    (∑ n ∈ Ico 68736 68864, mobiusTreeValue 16 mobiusTable1200001 n) = (4 : ℤ) ∧
    (∑ n ∈ Ico 68736 68864, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (76 : ℕ) ∧
    (∑ n ∈ Ico 68736 68864, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (290633 : ℤ) ∧
    (∑ n ∈ Ico 68736 68864, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (5812707243053759280619150362 : ℤ) := by
  rcases cdemPrefixStats_68736_68800 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_68800_68864 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 68736 ≤ 68800) (by norm_num : 68800 ≤ 68864), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 68736 ≤ 68800) (by norm_num : 68800 ≤ 68864), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 68736 ≤ 68800) (by norm_num : 68800 ≤ 68864), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 68736 ≤ 68800) (by norm_num : 68800 ≤ 68864), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_68608_68864 :
    (∑ n ∈ Ico 68608 68864, mobiusTreeValue 16 mobiusTable1200001 n) = (4 : ℤ) ∧
    (∑ n ∈ Ico 68608 68864, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (154 : ℕ) ∧
    (∑ n ∈ Ico 68608 68864, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (290888 : ℤ) ∧
    (∑ n ∈ Ico 68608 68864, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (5817860534613421570051586791 : ℤ) := by
  rcases cdemPrefixStats_68608_68736 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_68736_68864 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 68608 ≤ 68736) (by norm_num : 68736 ≤ 68864), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 68608 ≤ 68736) (by norm_num : 68736 ≤ 68864), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 68608 ≤ 68736) (by norm_num : 68736 ≤ 68864), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 68608 ≤ 68736) (by norm_num : 68736 ≤ 68864), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_68864_68928 :
    (∑ n ∈ Ico 68864 68928, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 68864 68928, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 68864 68928, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (7 : ℤ) ∧
    (∑ n ∈ Ico 68864 68928, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (126947119617545751879589 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_68928_68992 :
    (∑ n ∈ Ico 68928 68992, mobiusTreeValue 16 mobiusTable1200001 n) = (5 : ℤ) ∧
    (∑ n ∈ Ico 68928 68992, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 68928 68992, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (362436 : ℤ) ∧
    (∑ n ∈ Ico 68928 68992, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (7248835517985438275070323905 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_68864_68992 :
    (∑ n ∈ Ico 68864 68992, mobiusTreeValue 16 mobiusTable1200001 n) = (5 : ℤ) ∧
    (∑ n ∈ Ico 68864 68992, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (75 : ℕ) ∧
    (∑ n ∈ Ico 68864 68992, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (362443 : ℤ) ∧
    (∑ n ∈ Ico 68864 68992, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (7248962465105055820822203494 : ℤ) := by
  rcases cdemPrefixStats_68864_68928 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_68928_68992 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 68864 ≤ 68928) (by norm_num : 68928 ≤ 68992), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 68864 ≤ 68928) (by norm_num : 68928 ≤ 68992), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 68864 ≤ 68928) (by norm_num : 68928 ≤ 68992), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 68864 ≤ 68928) (by norm_num : 68928 ≤ 68992), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_68992_69056 :
    (∑ n ∈ Ico 68992 69056, mobiusTreeValue 16 mobiusTable1200001 n) = (8 : ℤ) ∧
    (∑ n ∈ Ico 68992 69056, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 68992 69056, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (579421 : ℤ) ∧
    (∑ n ∈ Ico 68992 69056, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (11588472335058264313047321276 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_69056_69120 :
    (∑ n ∈ Ico 69056 69120, mobiusTreeValue 16 mobiusTable1200001 n) = (-3 : ℤ) ∧
    (∑ n ∈ Ico 69056 69120, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 69056 69120, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-217027 : ℤ) ∧
    (∑ n ∈ Ico 69056 69120, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-4340487478271771874399377404 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_68992_69120 :
    (∑ n ∈ Ico 68992 69120, mobiusTreeValue 16 mobiusTable1200001 n) = (5 : ℤ) ∧
    (∑ n ∈ Ico 68992 69120, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (79 : ℕ) ∧
    (∑ n ∈ Ico 68992 69120, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (362394 : ℤ) ∧
    (∑ n ∈ Ico 68992 69120, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (7247984856786492438647943872 : ℤ) := by
  rcases cdemPrefixStats_68992_69056 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_69056_69120 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 68992 ≤ 69056) (by norm_num : 69056 ≤ 69120), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 68992 ≤ 69056) (by norm_num : 69056 ≤ 69120), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 68992 ≤ 69056) (by norm_num : 69056 ≤ 69120), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 68992 ≤ 69056) (by norm_num : 69056 ≤ 69120), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_68864_69120 :
    (∑ n ∈ Ico 68864 69120, mobiusTreeValue 16 mobiusTable1200001 n) = (10 : ℤ) ∧
    (∑ n ∈ Ico 68864 69120, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (154 : ℕ) ∧
    (∑ n ∈ Ico 68864 69120, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (724837 : ℤ) ∧
    (∑ n ∈ Ico 68864 69120, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (14496947321891548259470147366 : ℤ) := by
  rcases cdemPrefixStats_68864_68992 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_68992_69120 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 68864 ≤ 68992) (by norm_num : 68992 ≤ 69120), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 68864 ≤ 68992) (by norm_num : 68992 ≤ 69120), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 68864 ≤ 68992) (by norm_num : 68992 ≤ 69120), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 68864 ≤ 68992) (by norm_num : 68992 ≤ 69120), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_68608_69120 :
    (∑ n ∈ Ico 68608 69120, mobiusTreeValue 16 mobiusTable1200001 n) = (14 : ℤ) ∧
    (∑ n ∈ Ico 68608 69120, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (308 : ℕ) ∧
    (∑ n ∈ Ico 68608 69120, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (1015725 : ℤ) ∧
    (∑ n ∈ Ico 68608 69120, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (20314807856504969829521734157 : ℤ) := by
  rcases cdemPrefixStats_68608_68864 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_68864_69120 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 68608 ≤ 68864) (by norm_num : 68864 ≤ 69120), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 68608 ≤ 68864) (by norm_num : 68864 ≤ 69120), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 68608 ≤ 68864) (by norm_num : 68864 ≤ 69120), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 68608 ≤ 68864) (by norm_num : 68864 ≤ 69120), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_69120_69184 :
    (∑ n ∈ Ico 69120 69184, mobiusTreeValue 16 mobiusTable1200001 n) = (4 : ℤ) ∧
    (∑ n ∈ Ico 69120 69184, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (36 : ℕ) ∧
    (∑ n ∈ Ico 69120 69184, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (289296 : ℤ) ∧
    (∑ n ∈ Ico 69120 69184, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (5785928884958191245153579724 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_69184_69248 :
    (∑ n ∈ Ico 69184 69248, mobiusTreeValue 16 mobiusTable1200001 n) = (2 : ℤ) ∧
    (∑ n ∈ Ico 69184 69248, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (42 : ℕ) ∧
    (∑ n ∈ Ico 69184 69248, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (144579 : ℤ) ∧
    (∑ n ∈ Ico 69184 69248, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (2891591865457248737799279621 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_69120_69248 :
    (∑ n ∈ Ico 69120 69248, mobiusTreeValue 16 mobiusTable1200001 n) = (6 : ℤ) ∧
    (∑ n ∈ Ico 69120 69248, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 69120 69248, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (433875 : ℤ) ∧
    (∑ n ∈ Ico 69120 69248, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (8677520750415439982952859345 : ℤ) := by
  rcases cdemPrefixStats_69120_69184 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_69184_69248 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 69120 ≤ 69184) (by norm_num : 69184 ≤ 69248), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 69120 ≤ 69184) (by norm_num : 69184 ≤ 69248), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 69120 ≤ 69184) (by norm_num : 69184 ≤ 69248), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 69120 ≤ 69184) (by norm_num : 69184 ≤ 69248), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_69248_69312 :
    (∑ n ∈ Ico 69248 69312, mobiusTreeValue 16 mobiusTable1200001 n) = (3 : ℤ) ∧
    (∑ n ∈ Ico 69248 69312, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 69248 69312, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (216276 : ℤ) ∧
    (∑ n ∈ Ico 69248 69312, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (4325524354733750199961687551 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_69312_69376 :
    (∑ n ∈ Ico 69312 69376, mobiusTreeValue 16 mobiusTable1200001 n) = (6 : ℤ) ∧
    (∑ n ∈ Ico 69312 69376, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 69312 69376, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (432377 : ℤ) ∧
    (∑ n ∈ Ico 69312 69376, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (8647586473316519698071066032 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_69248_69376 :
    (∑ n ∈ Ico 69248 69376, mobiusTreeValue 16 mobiusTable1200001 n) = (9 : ℤ) ∧
    (∑ n ∈ Ico 69248 69376, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (75 : ℕ) ∧
    (∑ n ∈ Ico 69248 69376, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (648653 : ℤ) ∧
    (∑ n ∈ Ico 69248 69376, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (12973110828050269898032753583 : ℤ) := by
  rcases cdemPrefixStats_69248_69312 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_69312_69376 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 69248 ≤ 69312) (by norm_num : 69312 ≤ 69376), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 69248 ≤ 69312) (by norm_num : 69312 ≤ 69376), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 69248 ≤ 69312) (by norm_num : 69312 ≤ 69376), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 69248 ≤ 69312) (by norm_num : 69312 ≤ 69376), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_69120_69376 :
    (∑ n ∈ Ico 69120 69376, mobiusTreeValue 16 mobiusTable1200001 n) = (15 : ℤ) ∧
    (∑ n ∈ Ico 69120 69376, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (153 : ℕ) ∧
    (∑ n ∈ Ico 69120 69376, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (1082528 : ℤ) ∧
    (∑ n ∈ Ico 69120 69376, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (21650631578465709880985612928 : ℤ) := by
  rcases cdemPrefixStats_69120_69248 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_69248_69376 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 69120 ≤ 69248) (by norm_num : 69248 ≤ 69376), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 69120 ≤ 69248) (by norm_num : 69248 ≤ 69376), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 69120 ≤ 69248) (by norm_num : 69248 ≤ 69376), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 69120 ≤ 69248) (by norm_num : 69248 ≤ 69376), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_69376_69440 :
    (∑ n ∈ Ico 69376 69440, mobiusTreeValue 16 mobiusTable1200001 n) = (2 : ℤ) ∧
    (∑ n ∈ Ico 69376 69440, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 69376 69440, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (144101 : ℤ) ∧
    (∑ n ∈ Ico 69376 69440, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (2882051919380104017554372955 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_69440_69504 :
    (∑ n ∈ Ico 69440 69504, mobiusTreeValue 16 mobiusTable1200001 n) = (-2 : ℤ) ∧
    (∑ n ∈ Ico 69440 69504, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 69440 69504, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-144017 : ℤ) ∧
    (∑ n ∈ Ico 69440 69504, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-2880369974829518629843701734 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_69376_69504 :
    (∑ n ∈ Ico 69376 69504, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 69376 69504, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 69376 69504, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (84 : ℤ) ∧
    (∑ n ∈ Ico 69376 69504, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1681944550585387710671221 : ℤ) := by
  rcases cdemPrefixStats_69376_69440 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_69440_69504 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 69376 ≤ 69440) (by norm_num : 69440 ≤ 69504), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 69376 ≤ 69440) (by norm_num : 69440 ≤ 69504), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 69376 ≤ 69440) (by norm_num : 69440 ≤ 69504), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 69376 ≤ 69440) (by norm_num : 69440 ≤ 69504), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_69504_69568 :
    (∑ n ∈ Ico 69504 69568, mobiusTreeValue 16 mobiusTable1200001 n) = (11 : ℤ) ∧
    (∑ n ∈ Ico 69504 69568, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 69504 69568, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (791080 : ℤ) ∧
    (∑ n ∈ Ico 69504 69568, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (15821771439765194209214089420 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_69568_69632 :
    (∑ n ∈ Ico 69568 69632, mobiusTreeValue 16 mobiusTable1200001 n) = (4 : ℤ) ∧
    (∑ n ∈ Ico 69568 69632, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 69568 69632, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (287308 : ℤ) ∧
    (∑ n ∈ Ico 69568 69632, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (5746218281487015083933560672 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_69504_69632 :
    (∑ n ∈ Ico 69504 69632, mobiusTreeValue 16 mobiusTable1200001 n) = (15 : ℤ) ∧
    (∑ n ∈ Ico 69504 69632, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (81 : ℕ) ∧
    (∑ n ∈ Ico 69504 69632, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (1078388 : ℤ) ∧
    (∑ n ∈ Ico 69504 69632, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (21567989721252209293147650092 : ℤ) := by
  rcases cdemPrefixStats_69504_69568 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_69568_69632 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 69504 ≤ 69568) (by norm_num : 69568 ≤ 69632), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 69504 ≤ 69568) (by norm_num : 69568 ≤ 69632), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 69504 ≤ 69568) (by norm_num : 69568 ≤ 69632), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 69504 ≤ 69568) (by norm_num : 69568 ≤ 69632), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_69376_69632 :
    (∑ n ∈ Ico 69376 69632, mobiusTreeValue 16 mobiusTable1200001 n) = (15 : ℤ) ∧
    (∑ n ∈ Ico 69376 69632, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (159 : ℕ) ∧
    (∑ n ∈ Ico 69376 69632, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (1078472 : ℤ) ∧
    (∑ n ∈ Ico 69376 69632, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (21569671665802794680858321313 : ℤ) := by
  rcases cdemPrefixStats_69376_69504 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_69504_69632 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 69376 ≤ 69504) (by norm_num : 69504 ≤ 69632), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 69376 ≤ 69504) (by norm_num : 69504 ≤ 69632), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 69376 ≤ 69504) (by norm_num : 69504 ≤ 69632), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 69376 ≤ 69504) (by norm_num : 69504 ≤ 69632), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_69120_69632 :
    (∑ n ∈ Ico 69120 69632, mobiusTreeValue 16 mobiusTable1200001 n) = (30 : ℤ) ∧
    (∑ n ∈ Ico 69120 69632, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (312 : ℕ) ∧
    (∑ n ∈ Ico 69120 69632, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (2161000 : ℤ) ∧
    (∑ n ∈ Ico 69120 69632, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (43220303244268504561843934241 : ℤ) := by
  rcases cdemPrefixStats_69120_69376 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_69376_69632 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 69120 ≤ 69376) (by norm_num : 69376 ≤ 69632), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 69120 ≤ 69376) (by norm_num : 69376 ≤ 69632), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 69120 ≤ 69376) (by norm_num : 69376 ≤ 69632), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 69120 ≤ 69376) (by norm_num : 69376 ≤ 69632), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_68608_69632 :
    (∑ n ∈ Ico 68608 69632, mobiusTreeValue 16 mobiusTable1200001 n) = (44 : ℤ) ∧
    (∑ n ∈ Ico 68608 69632, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (620 : ℕ) ∧
    (∑ n ∈ Ico 68608 69632, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (3176725 : ℤ) ∧
    (∑ n ∈ Ico 68608 69632, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (63535111100773474391365668398 : ℤ) := by
  rcases cdemPrefixStats_68608_69120 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_69120_69632 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 68608 ≤ 69120) (by norm_num : 69120 ≤ 69632), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 68608 ≤ 69120) (by norm_num : 69120 ≤ 69632), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 68608 ≤ 69120) (by norm_num : 69120 ≤ 69632), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 68608 ≤ 69120) (by norm_num : 69120 ≤ 69632), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_67584_69632 :
    (∑ n ∈ Ico 67584 69632, mobiusTreeValue 16 mobiusTable1200001 n) = (63 : ℤ) ∧
    (∑ n ∈ Ico 67584 69632, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (1245 : ℕ) ∧
    (∑ n ∈ Ico 67584 69632, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (4561482 : ℤ) ∧
    (∑ n ∈ Ico 67584 69632, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (91230294196239694326580029892 : ℤ) := by
  rcases cdemPrefixStats_67584_68608 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_68608_69632 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 67584 ≤ 68608) (by norm_num : 68608 ≤ 69632), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 67584 ≤ 68608) (by norm_num : 68608 ≤ 69632), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 67584 ≤ 68608) (by norm_num : 68608 ≤ 69632), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 67584 ≤ 68608) (by norm_num : 68608 ≤ 69632), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_65536_69632 :
    (∑ n ∈ Ico 65536 69632, mobiusTreeValue 16 mobiusTable1200001 n) = (78 : ℤ) ∧
    (∑ n ∈ Ico 65536 69632, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (2486 : ℕ) ∧
    (∑ n ∈ Ico 65536 69632, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (5693314 : ℤ) ∧
    (∑ n ∈ Ico 65536 69632, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (113867298783621895407740232468 : ℤ) := by
  rcases cdemPrefixStats_65536_67584 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_67584_69632 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 65536 ≤ 67584) (by norm_num : 67584 ≤ 69632), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 65536 ≤ 67584) (by norm_num : 67584 ≤ 69632), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 65536 ≤ 67584) (by norm_num : 67584 ≤ 69632), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 65536 ≤ 67584) (by norm_num : 67584 ≤ 69632), hR1, hR2] <;> norm_num

theorem cdemPrefixGroup016_checked_complete :
    (∑ n ∈ Ico 65536 69632, mobiusTreeValue 16 mobiusTable1200001 n) = (78 : ℤ) ∧
    (∑ n ∈ Ico 65536 69632, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (2486 : ℕ) ∧
    (∑ n ∈ Ico 65536 69632, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (5693314 : ℤ) ∧
    (∑ n ∈ Ico 65536 69632, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (113867298783621895407740232468 : ℤ) := cdemPrefixStats_65536_69632
end Helfgott
#print axioms Helfgott.cdemPrefixGroup016_checked_complete

open Helfgott Finset
open scoped BigOperators

theorem solution :
    (∑ n ∈ Ico 65536 69632, mobiusTreeValue 16 mobiusTable1200001 n) = (78 : ℤ) ∧
    (∑ n ∈ Ico 65536 69632, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (2486 : ℕ) ∧
    (∑ n ∈ Ico 65536 69632, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (5693314 : ℤ) ∧
    (∑ n ∈ Ico 65536 69632, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (113867298783621895407740232468 : ℤ) := Helfgott.cdemPrefixGroup016_checked_complete
#print axioms solution
