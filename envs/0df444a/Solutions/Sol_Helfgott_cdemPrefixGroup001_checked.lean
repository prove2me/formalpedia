-- Prove2me | solution 1 for Helfgott.cdemPrefixGroup001_checked
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-09T01:17:23.784982+00:00
-- url     : https://prove2.me/submissions/87dfbf05-acdc-47d4-908c-d8981b1ec0d6

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
private theorem cdemPrefixStats_4096_4160 :
    (∑ n ∈ Ico 4096 4160, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 4096 4160, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 4096 4160, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (1273016 : ℤ) ∧
    (∑ n ∈ Ico 4096 4160, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (25460335204816792338784845063 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_4160_4224 :
    (∑ n ∈ Ico 4160 4224, mobiusTreeValue 16 mobiusTable1200001 n) = (7 : ℤ) ∧
    (∑ n ∈ Ico 4160 4224, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 4160 4224, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (8399803 : ℤ) ∧
    (∑ n ∈ Ico 4160 4224, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (167996102350314443602142042353 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_4096_4224 :
    (∑ n ∈ Ico 4096 4224, mobiusTreeValue 16 mobiusTable1200001 n) = (8 : ℤ) ∧
    (∑ n ∈ Ico 4096 4224, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 4096 4224, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (9672819 : ℤ) ∧
    (∑ n ∈ Ico 4096 4224, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (193456437555131235940926887416 : ℤ) := by
  rcases cdemPrefixStats_4096_4160 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_4160_4224 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 4096 ≤ 4160) (by norm_num : 4160 ≤ 4224), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 4096 ≤ 4160) (by norm_num : 4160 ≤ 4224), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 4096 ≤ 4160) (by norm_num : 4160 ≤ 4224), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 4096 ≤ 4160) (by norm_num : 4160 ≤ 4224), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_4224_4288 :
    (∑ n ∈ Ico 4224 4288, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 4224 4288, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 4224 4288, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (1109328 : ℤ) ∧
    (∑ n ∈ Ico 4224 4288, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (22186565095749910892428356416 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_4288_4352 :
    (∑ n ∈ Ico 4288 4352, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 4288 4352, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 4288 4352, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (1172259 : ℤ) ∧
    (∑ n ∈ Ico 4288 4352, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (23445201621505297493631300626 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_4224_4352 :
    (∑ n ∈ Ico 4224 4352, mobiusTreeValue 16 mobiusTable1200001 n) = (2 : ℤ) ∧
    (∑ n ∈ Ico 4224 4352, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 4224 4352, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (2281587 : ℤ) ∧
    (∑ n ∈ Ico 4224 4352, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (45631766717255208386059657042 : ℤ) := by
  rcases cdemPrefixStats_4224_4288 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_4288_4352 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 4224 ≤ 4288) (by norm_num : 4288 ≤ 4352), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 4224 ≤ 4288) (by norm_num : 4288 ≤ 4352), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 4224 ≤ 4288) (by norm_num : 4288 ≤ 4352), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 4224 ≤ 4288) (by norm_num : 4288 ≤ 4352), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_4096_4352 :
    (∑ n ∈ Ico 4096 4352, mobiusTreeValue 16 mobiusTable1200001 n) = (10 : ℤ) ∧
    (∑ n ∈ Ico 4096 4352, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (156 : ℕ) ∧
    (∑ n ∈ Ico 4096 4352, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (11954406 : ℤ) ∧
    (∑ n ∈ Ico 4096 4352, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (239088204272386444326986544458 : ℤ) := by
  rcases cdemPrefixStats_4096_4224 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_4224_4352 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 4096 ≤ 4224) (by norm_num : 4224 ≤ 4352), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 4096 ≤ 4224) (by norm_num : 4224 ≤ 4352), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 4096 ≤ 4224) (by norm_num : 4224 ≤ 4352), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 4096 ≤ 4224) (by norm_num : 4224 ≤ 4352), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_4352_4416 :
    (∑ n ∈ Ico 4352 4416, mobiusTreeValue 16 mobiusTable1200001 n) = (2 : ℤ) ∧
    (∑ n ∈ Ico 4352 4416, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 4352 4416, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (2256380 : ℤ) ∧
    (∑ n ∈ Ico 4352 4416, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (45127658505729477157075245538 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_4416_4480 :
    (∑ n ∈ Ico 4416 4480, mobiusTreeValue 16 mobiusTable1200001 n) = (3 : ℤ) ∧
    (∑ n ∈ Ico 4416 4480, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 4416 4480, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (3342239 : ℤ) ∧
    (∑ n ∈ Ico 4416 4480, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (66844744734625271649069319920 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_4352_4480 :
    (∑ n ∈ Ico 4352 4480, mobiusTreeValue 16 mobiusTable1200001 n) = (5 : ℤ) ∧
    (∑ n ∈ Ico 4352 4480, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 4352 4480, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (5598619 : ℤ) ∧
    (∑ n ∈ Ico 4352 4480, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (111972403240354748806144565458 : ℤ) := by
  rcases cdemPrefixStats_4352_4416 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_4416_4480 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 4352 ≤ 4416) (by norm_num : 4416 ≤ 4480), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 4352 ≤ 4416) (by norm_num : 4416 ≤ 4480), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 4352 ≤ 4416) (by norm_num : 4416 ≤ 4480), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 4352 ≤ 4416) (by norm_num : 4416 ≤ 4480), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_4480_4544 :
    (∑ n ∈ Ico 4480 4544, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 4480 4544, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 4480 4544, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (1086856 : ℤ) ∧
    (∑ n ∈ Ico 4480 4544, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (21737138313785924976354522576 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_4544_4608 :
    (∑ n ∈ Ico 4544 4608, mobiusTreeValue 16 mobiusTable1200001 n) = (3 : ℤ) ∧
    (∑ n ∈ Ico 4544 4608, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 4544 4608, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (3261752 : ℤ) ∧
    (∑ n ∈ Ico 4544 4608, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (65235062135438884515027401812 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_4480_4608 :
    (∑ n ∈ Ico 4480 4608, mobiusTreeValue 16 mobiusTable1200001 n) = (4 : ℤ) ∧
    (∑ n ∈ Ico 4480 4608, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 4480 4608, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (4348608 : ℤ) ∧
    (∑ n ∈ Ico 4480 4608, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (86972200449224809491381924388 : ℤ) := by
  rcases cdemPrefixStats_4480_4544 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_4544_4608 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 4480 ≤ 4544) (by norm_num : 4544 ≤ 4608), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 4480 ≤ 4544) (by norm_num : 4544 ≤ 4608), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 4480 ≤ 4544) (by norm_num : 4544 ≤ 4608), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 4480 ≤ 4544) (by norm_num : 4544 ≤ 4608), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_4352_4608 :
    (∑ n ∈ Ico 4352 4608, mobiusTreeValue 16 mobiusTable1200001 n) = (9 : ℤ) ∧
    (∑ n ∈ Ico 4352 4608, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (155 : ℕ) ∧
    (∑ n ∈ Ico 4352 4608, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (9947227 : ℤ) ∧
    (∑ n ∈ Ico 4352 4608, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (198944603689579558297526489846 : ℤ) := by
  rcases cdemPrefixStats_4352_4480 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_4480_4608 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 4352 ≤ 4480) (by norm_num : 4480 ≤ 4608), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 4352 ≤ 4480) (by norm_num : 4480 ≤ 4608), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 4352 ≤ 4480) (by norm_num : 4480 ≤ 4608), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 4352 ≤ 4480) (by norm_num : 4480 ≤ 4608), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_4096_4608 :
    (∑ n ∈ Ico 4096 4608, mobiusTreeValue 16 mobiusTable1200001 n) = (19 : ℤ) ∧
    (∑ n ∈ Ico 4096 4608, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (311 : ℕ) ∧
    (∑ n ∈ Ico 4096 4608, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (21901633 : ℤ) ∧
    (∑ n ∈ Ico 4096 4608, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (438032807961966002624513034304 : ℤ) := by
  rcases cdemPrefixStats_4096_4352 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_4352_4608 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 4096 ≤ 4352) (by norm_num : 4352 ≤ 4608), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 4096 ≤ 4352) (by norm_num : 4352 ≤ 4608), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 4096 ≤ 4352) (by norm_num : 4352 ≤ 4608), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 4096 ≤ 4352) (by norm_num : 4352 ≤ 4608), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_4608_4672 :
    (∑ n ∈ Ico 4608 4672, mobiusTreeValue 16 mobiusTable1200001 n) = (-7 : ℤ) ∧
    (∑ n ∈ Ico 4608 4672, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 4608 4672, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-7526485 : ℤ) ∧
    (∑ n ∈ Ico 4608 4672, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-150529798918917421209703237804 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_4672_4736 :
    (∑ n ∈ Ico 4672 4736, mobiusTreeValue 16 mobiusTable1200001 n) = (6 : ℤ) ∧
    (∑ n ∈ Ico 4672 4736, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 4672 4736, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (6414200 : ℤ) ∧
    (∑ n ∈ Ico 4672 4736, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (128284067906218237217901108973 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_4608_4736 :
    (∑ n ∈ Ico 4608 4736, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 4608 4736, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (79 : ℕ) ∧
    (∑ n ∈ Ico 4608 4736, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-1112285 : ℤ) ∧
    (∑ n ∈ Ico 4608 4736, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-22245731012699183991802128831 : ℤ) := by
  rcases cdemPrefixStats_4608_4672 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_4672_4736 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 4608 ≤ 4672) (by norm_num : 4672 ≤ 4736), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 4608 ≤ 4672) (by norm_num : 4672 ≤ 4736), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 4608 ≤ 4672) (by norm_num : 4672 ≤ 4736), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 4608 ≤ 4672) (by norm_num : 4672 ≤ 4736), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_4736_4800 :
    (∑ n ∈ Ico 4736 4800, mobiusTreeValue 16 mobiusTable1200001 n) = (10 : ℤ) ∧
    (∑ n ∈ Ico 4736 4800, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 4736 4800, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (10520978 : ℤ) ∧
    (∑ n ∈ Ico 4736 4800, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (210419686581046905922395968104 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_4800_4864 :
    (∑ n ∈ Ico 4800 4864, mobiusTreeValue 16 mobiusTable1200001 n) = (11 : ℤ) ∧
    (∑ n ∈ Ico 4800 4864, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 4800 4864, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (11341657 : ℤ) ∧
    (∑ n ∈ Ico 4800 4864, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (226833203766895162537365330125 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_4736_4864 :
    (∑ n ∈ Ico 4736 4864, mobiusTreeValue 16 mobiusTable1200001 n) = (21 : ℤ) ∧
    (∑ n ∈ Ico 4736 4864, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (79 : ℕ) ∧
    (∑ n ∈ Ico 4736 4864, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (21862635 : ℤ) ∧
    (∑ n ∈ Ico 4736 4864, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (437252890347942068459761298229 : ℤ) := by
  rcases cdemPrefixStats_4736_4800 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_4800_4864 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 4736 ≤ 4800) (by norm_num : 4800 ≤ 4864), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 4736 ≤ 4800) (by norm_num : 4800 ≤ 4864), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 4736 ≤ 4800) (by norm_num : 4800 ≤ 4864), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 4736 ≤ 4800) (by norm_num : 4800 ≤ 4864), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_4608_4864 :
    (∑ n ∈ Ico 4608 4864, mobiusTreeValue 16 mobiusTable1200001 n) = (20 : ℤ) ∧
    (∑ n ∈ Ico 4608 4864, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (158 : ℕ) ∧
    (∑ n ∈ Ico 4608 4864, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (20750350 : ℤ) ∧
    (∑ n ∈ Ico 4608 4864, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (415007159335242884467959169398 : ℤ) := by
  rcases cdemPrefixStats_4608_4736 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_4736_4864 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 4608 ≤ 4736) (by norm_num : 4736 ≤ 4864), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 4608 ≤ 4736) (by norm_num : 4736 ≤ 4864), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 4608 ≤ 4736) (by norm_num : 4736 ≤ 4864), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 4608 ≤ 4736) (by norm_num : 4736 ≤ 4864), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_4864_4928 :
    (∑ n ∈ Ico 4864 4928, mobiusTreeValue 16 mobiusTable1200001 n) = (-4 : ℤ) ∧
    (∑ n ∈ Ico 4864 4928, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 4864 4928, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-4076746 : ℤ) ∧
    (∑ n ∈ Ico 4864 4928, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-81534907086218723215814664563 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_4928_4992 :
    (∑ n ∈ Ico 4928 4992, mobiusTreeValue 16 mobiusTable1200001 n) = (-12 : ℤ) ∧
    (∑ n ∈ Ico 4928 4992, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 4928 4992, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-12096925 : ℤ) ∧
    (∑ n ∈ Ico 4928 4992, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-241938583098076831576326331712 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_4864_4992 :
    (∑ n ∈ Ico 4864 4992, mobiusTreeValue 16 mobiusTable1200001 n) = (-16 : ℤ) ∧
    (∑ n ∈ Ico 4864 4992, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 4864 4992, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-16173671 : ℤ) ∧
    (∑ n ∈ Ico 4864 4992, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-323473490184295554792140996275 : ℤ) := by
  rcases cdemPrefixStats_4864_4928 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_4928_4992 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 4864 ≤ 4928) (by norm_num : 4928 ≤ 4992), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 4864 ≤ 4928) (by norm_num : 4928 ≤ 4992), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 4864 ≤ 4928) (by norm_num : 4928 ≤ 4992), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 4864 ≤ 4928) (by norm_num : 4928 ≤ 4992), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_4992_5056 :
    (∑ n ∈ Ico 4992 5056, mobiusTreeValue 16 mobiusTable1200001 n) = (-9 : ℤ) ∧
    (∑ n ∈ Ico 4992 5056, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (35 : ℕ) ∧
    (∑ n ∈ Ico 4992 5056, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-8961453 : ℤ) ∧
    (∑ n ∈ Ico 4992 5056, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-179229185624508154883492940121 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_5056_5120 :
    (∑ n ∈ Ico 5056 5120, mobiusTreeValue 16 mobiusTable1200001 n) = (4 : ℤ) ∧
    (∑ n ∈ Ico 5056 5120, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 5056 5120, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (3936608 : ℤ) ∧
    (∑ n ∈ Ico 5056 5120, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (78732265306641294843541391662 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_4992_5120 :
    (∑ n ∈ Ico 4992 5120, mobiusTreeValue 16 mobiusTable1200001 n) = (-5 : ℤ) ∧
    (∑ n ∈ Ico 4992 5120, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (75 : ℕ) ∧
    (∑ n ∈ Ico 4992 5120, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-5024845 : ℤ) ∧
    (∑ n ∈ Ico 4992 5120, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-100496920317866860039951548459 : ℤ) := by
  rcases cdemPrefixStats_4992_5056 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_5056_5120 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 4992 ≤ 5056) (by norm_num : 5056 ≤ 5120), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 4992 ≤ 5056) (by norm_num : 5056 ≤ 5120), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 4992 ≤ 5056) (by norm_num : 5056 ≤ 5120), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 4992 ≤ 5056) (by norm_num : 5056 ≤ 5120), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_4864_5120 :
    (∑ n ∈ Ico 4864 5120, mobiusTreeValue 16 mobiusTable1200001 n) = (-21 : ℤ) ∧
    (∑ n ∈ Ico 4864 5120, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (153 : ℕ) ∧
    (∑ n ∈ Ico 4864 5120, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-21198516 : ℤ) ∧
    (∑ n ∈ Ico 4864 5120, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-423970410502162414832092544734 : ℤ) := by
  rcases cdemPrefixStats_4864_4992 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_4992_5120 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 4864 ≤ 4992) (by norm_num : 4992 ≤ 5120), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 4864 ≤ 4992) (by norm_num : 4992 ≤ 5120), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 4864 ≤ 4992) (by norm_num : 4992 ≤ 5120), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 4864 ≤ 4992) (by norm_num : 4992 ≤ 5120), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_4608_5120 :
    (∑ n ∈ Ico 4608 5120, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 4608 5120, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (311 : ℕ) ∧
    (∑ n ∈ Ico 4608 5120, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-448166 : ℤ) ∧
    (∑ n ∈ Ico 4608 5120, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-8963251166919530364133375336 : ℤ) := by
  rcases cdemPrefixStats_4608_4864 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_4864_5120 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 4608 ≤ 4864) (by norm_num : 4864 ≤ 5120), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 4608 ≤ 4864) (by norm_num : 4864 ≤ 5120), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 4608 ≤ 4864) (by norm_num : 4864 ≤ 5120), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 4608 ≤ 4864) (by norm_num : 4864 ≤ 5120), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_4096_5120 :
    (∑ n ∈ Ico 4096 5120, mobiusTreeValue 16 mobiusTable1200001 n) = (18 : ℤ) ∧
    (∑ n ∈ Ico 4096 5120, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (622 : ℕ) ∧
    (∑ n ∈ Ico 4096 5120, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (21453467 : ℤ) ∧
    (∑ n ∈ Ico 4096 5120, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (429069556795046472260379658968 : ℤ) := by
  rcases cdemPrefixStats_4096_4608 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_4608_5120 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 4096 ≤ 4608) (by norm_num : 4608 ≤ 5120), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 4096 ≤ 4608) (by norm_num : 4608 ≤ 5120), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 4096 ≤ 4608) (by norm_num : 4608 ≤ 5120), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 4096 ≤ 4608) (by norm_num : 4608 ≤ 5120), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_5120_5184 :
    (∑ n ∈ Ico 5120 5184, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 5120 5184, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 5120 5184, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-977261 : ℤ) ∧
    (∑ n ∈ Ico 5120 5184, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-19545239016896290259446439736 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_5184_5248 :
    (∑ n ∈ Ico 5184 5248, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 5184 5248, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 5184 5248, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (968932 : ℤ) ∧
    (∑ n ∈ Ico 5184 5248, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (19378666398280756314440604130 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_5120_5248 :
    (∑ n ∈ Ico 5120 5248, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 5120 5248, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (76 : ℕ) ∧
    (∑ n ∈ Ico 5120 5248, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-8329 : ℤ) ∧
    (∑ n ∈ Ico 5120 5248, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-166572618615533945005835606 : ℤ) := by
  rcases cdemPrefixStats_5120_5184 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_5184_5248 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 5120 ≤ 5184) (by norm_num : 5184 ≤ 5248), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 5120 ≤ 5184) (by norm_num : 5184 ≤ 5248), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 5120 ≤ 5184) (by norm_num : 5184 ≤ 5248), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 5120 ≤ 5184) (by norm_num : 5184 ≤ 5248), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_5248_5312 :
    (∑ n ∈ Ico 5248 5312, mobiusTreeValue 16 mobiusTable1200001 n) = (-4 : ℤ) ∧
    (∑ n ∈ Ico 5248 5312, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 5248 5312, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-3757041 : ℤ) ∧
    (∑ n ∈ Ico 5248 5312, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-75140887728790871594857956638 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_5312_5376 :
    (∑ n ∈ Ico 5312 5376, mobiusTreeValue 16 mobiusTable1200001 n) = (16 : ℤ) ∧
    (∑ n ∈ Ico 5312 5376, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 5312 5376, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (14973462 : ℤ) ∧
    (∑ n ∈ Ico 5312 5376, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (299469406192186532008770555583 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_5248_5376 :
    (∑ n ∈ Ico 5248 5376, mobiusTreeValue 16 mobiusTable1200001 n) = (12 : ℤ) ∧
    (∑ n ∈ Ico 5248 5376, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 5248 5376, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (11216421 : ℤ) ∧
    (∑ n ∈ Ico 5248 5376, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (224328518463395660413912598945 : ℤ) := by
  rcases cdemPrefixStats_5248_5312 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_5312_5376 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 5248 ≤ 5312) (by norm_num : 5312 ≤ 5376), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 5248 ≤ 5312) (by norm_num : 5312 ≤ 5376), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 5248 ≤ 5312) (by norm_num : 5312 ≤ 5376), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 5248 ≤ 5312) (by norm_num : 5312 ≤ 5376), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_5120_5376 :
    (∑ n ∈ Ico 5120 5376, mobiusTreeValue 16 mobiusTable1200001 n) = (12 : ℤ) ∧
    (∑ n ∈ Ico 5120 5376, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (154 : ℕ) ∧
    (∑ n ∈ Ico 5120 5376, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (11208092 : ℤ) ∧
    (∑ n ∈ Ico 5120 5376, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (224161945844780126468906763339 : ℤ) := by
  rcases cdemPrefixStats_5120_5248 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_5248_5376 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 5120 ≤ 5248) (by norm_num : 5248 ≤ 5376), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 5120 ≤ 5248) (by norm_num : 5248 ≤ 5376), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 5120 ≤ 5248) (by norm_num : 5248 ≤ 5376), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 5120 ≤ 5248) (by norm_num : 5248 ≤ 5376), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_5376_5440 :
    (∑ n ∈ Ico 5376 5440, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 5376 5440, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 5376 5440, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (911310 : ℤ) ∧
    (∑ n ∈ Ico 5376 5440, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (18226284193923660543214272681 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_5440_5504 :
    (∑ n ∈ Ico 5440 5504, mobiusTreeValue 16 mobiusTable1200001 n) = (-3 : ℤ) ∧
    (∑ n ∈ Ico 5440 5504, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 5440 5504, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-2758370 : ℤ) ∧
    (∑ n ∈ Ico 5440 5504, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-55167438509295271089927141256 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_5376_5504 :
    (∑ n ∈ Ico 5376 5504, mobiusTreeValue 16 mobiusTable1200001 n) = (-2 : ℤ) ∧
    (∑ n ∈ Ico 5376 5504, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 5376 5504, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-1847060 : ℤ) ∧
    (∑ n ∈ Ico 5376 5504, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-36941154315371610546712868575 : ℤ) := by
  rcases cdemPrefixStats_5376_5440 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_5440_5504 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 5376 ≤ 5440) (by norm_num : 5440 ≤ 5504), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 5376 ≤ 5440) (by norm_num : 5440 ≤ 5504), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 5376 ≤ 5440) (by norm_num : 5440 ≤ 5504), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 5376 ≤ 5440) (by norm_num : 5440 ≤ 5504), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_5504_5568 :
    (∑ n ∈ Ico 5504 5568, mobiusTreeValue 16 mobiusTable1200001 n) = (-2 : ℤ) ∧
    (∑ n ∈ Ico 5504 5568, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 5504 5568, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-1817148 : ℤ) ∧
    (∑ n ∈ Ico 5504 5568, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-36342973427142339475470921310 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_5568_5632 :
    (∑ n ∈ Ico 5568 5632, mobiusTreeValue 16 mobiusTable1200001 n) = (7 : ℤ) ∧
    (∑ n ∈ Ico 5568 5632, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 5568 5632, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (6240393 : ℤ) ∧
    (∑ n ∈ Ico 5568 5632, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (124807966291266687021371305764 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_5504_5632 :
    (∑ n ∈ Ico 5504 5632, mobiusTreeValue 16 mobiusTable1200001 n) = (5 : ℤ) ∧
    (∑ n ∈ Ico 5504 5632, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 5504 5632, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (4423245 : ℤ) ∧
    (∑ n ∈ Ico 5504 5632, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (88464992864124347545900384454 : ℤ) := by
  rcases cdemPrefixStats_5504_5568 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_5568_5632 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 5504 ≤ 5568) (by norm_num : 5568 ≤ 5632), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 5504 ≤ 5568) (by norm_num : 5568 ≤ 5632), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 5504 ≤ 5568) (by norm_num : 5568 ≤ 5632), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 5504 ≤ 5568) (by norm_num : 5568 ≤ 5632), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_5376_5632 :
    (∑ n ∈ Ico 5376 5632, mobiusTreeValue 16 mobiusTable1200001 n) = (3 : ℤ) ∧
    (∑ n ∈ Ico 5376 5632, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (155 : ℕ) ∧
    (∑ n ∈ Ico 5376 5632, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (2576185 : ℤ) ∧
    (∑ n ∈ Ico 5376 5632, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (51523838548752736999187515879 : ℤ) := by
  rcases cdemPrefixStats_5376_5504 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_5504_5632 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 5376 ≤ 5504) (by norm_num : 5504 ≤ 5632), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 5376 ≤ 5504) (by norm_num : 5504 ≤ 5632), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 5376 ≤ 5504) (by norm_num : 5504 ≤ 5632), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 5376 ≤ 5504) (by norm_num : 5504 ≤ 5632), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_5120_5632 :
    (∑ n ∈ Ico 5120 5632, mobiusTreeValue 16 mobiusTable1200001 n) = (15 : ℤ) ∧
    (∑ n ∈ Ico 5120 5632, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (309 : ℕ) ∧
    (∑ n ∈ Ico 5120 5632, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (13784277 : ℤ) ∧
    (∑ n ∈ Ico 5120 5632, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (275685784393532863468094279218 : ℤ) := by
  rcases cdemPrefixStats_5120_5376 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_5376_5632 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 5120 ≤ 5376) (by norm_num : 5376 ≤ 5632), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 5120 ≤ 5376) (by norm_num : 5376 ≤ 5632), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 5120 ≤ 5376) (by norm_num : 5376 ≤ 5632), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 5120 ≤ 5376) (by norm_num : 5376 ≤ 5632), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_5632_5696 :
    (∑ n ∈ Ico 5632 5696, mobiusTreeValue 16 mobiusTable1200001 n) = (-9 : ℤ) ∧
    (∑ n ∈ Ico 5632 5696, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 5632 5696, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-7921613 : ℤ) ∧
    (∑ n ∈ Ico 5632 5696, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-158432356314965015323504272274 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_5696_5760 :
    (∑ n ∈ Ico 5696 5760, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 5696 5760, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 5696 5760, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (871934 : ℤ) ∧
    (∑ n ∈ Ico 5696 5760, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (17438695524902999580441110826 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_5632_5760 :
    (∑ n ∈ Ico 5632 5760, mobiusTreeValue 16 mobiusTable1200001 n) = (-8 : ℤ) ∧
    (∑ n ∈ Ico 5632 5760, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 5632 5760, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-7049679 : ℤ) ∧
    (∑ n ∈ Ico 5632 5760, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-140993660790062015743063161448 : ℤ) := by
  rcases cdemPrefixStats_5632_5696 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_5696_5760 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 5632 ≤ 5696) (by norm_num : 5696 ≤ 5760), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 5632 ≤ 5696) (by norm_num : 5696 ≤ 5760), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 5632 ≤ 5696) (by norm_num : 5696 ≤ 5760), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 5632 ≤ 5696) (by norm_num : 5696 ≤ 5760), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_5760_5824 :
    (∑ n ∈ Ico 5760 5824, mobiusTreeValue 16 mobiusTable1200001 n) = (-2 : ℤ) ∧
    (∑ n ∈ Ico 5760 5824, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 5760 5824, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-1713714 : ℤ) ∧
    (∑ n ∈ Ico 5760 5824, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-34274261747820798068858471079 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_5824_5888 :
    (∑ n ∈ Ico 5824 5888, mobiusTreeValue 16 mobiusTable1200001 n) = (-13 : ℤ) ∧
    (∑ n ∈ Ico 5824 5888, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 5824 5888, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-11087150 : ℤ) ∧
    (∑ n ∈ Ico 5824 5888, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-221743094416362842717755285346 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_5760_5888 :
    (∑ n ∈ Ico 5760 5888, mobiusTreeValue 16 mobiusTable1200001 n) = (-15 : ℤ) ∧
    (∑ n ∈ Ico 5760 5888, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 5760 5888, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-12800864 : ℤ) ∧
    (∑ n ∈ Ico 5760 5888, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-256017356164183640786613756425 : ℤ) := by
  rcases cdemPrefixStats_5760_5824 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_5824_5888 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 5760 ≤ 5824) (by norm_num : 5824 ≤ 5888), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 5760 ≤ 5824) (by norm_num : 5824 ≤ 5888), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 5760 ≤ 5824) (by norm_num : 5824 ≤ 5888), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 5760 ≤ 5824) (by norm_num : 5824 ≤ 5888), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_5632_5888 :
    (∑ n ∈ Ico 5632 5888, mobiusTreeValue 16 mobiusTable1200001 n) = (-23 : ℤ) ∧
    (∑ n ∈ Ico 5632 5888, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (155 : ℕ) ∧
    (∑ n ∈ Ico 5632 5888, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-19850543 : ℤ) ∧
    (∑ n ∈ Ico 5632 5888, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-397011016954245656529676917873 : ℤ) := by
  rcases cdemPrefixStats_5632_5760 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_5760_5888 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 5632 ≤ 5760) (by norm_num : 5760 ≤ 5888), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 5632 ≤ 5760) (by norm_num : 5760 ≤ 5888), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 5632 ≤ 5760) (by norm_num : 5760 ≤ 5888), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 5632 ≤ 5760) (by norm_num : 5760 ≤ 5888), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_5888_5952 :
    (∑ n ∈ Ico 5888 5952, mobiusTreeValue 16 mobiusTable1200001 n) = (7 : ℤ) ∧
    (∑ n ∈ Ico 5888 5952, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 5888 5952, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (5902633 : ℤ) ∧
    (∑ n ∈ Ico 5888 5952, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (118052734735051658213400656125 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_5952_6016 :
    (∑ n ∈ Ico 5952 6016, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 5952 6016, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 5952 6016, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (831023 : ℤ) ∧
    (∑ n ∈ Ico 5952 6016, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (16620446758409596295178924744 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_5888_6016 :
    (∑ n ∈ Ico 5888 6016, mobiusTreeValue 16 mobiusTable1200001 n) = (8 : ℤ) ∧
    (∑ n ∈ Ico 5888 6016, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (80 : ℕ) ∧
    (∑ n ∈ Ico 5888 6016, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (6733656 : ℤ) ∧
    (∑ n ∈ Ico 5888 6016, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (134673181493461254508579580869 : ℤ) := by
  rcases cdemPrefixStats_5888_5952 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_5952_6016 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 5888 ≤ 5952) (by norm_num : 5952 ≤ 6016), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 5888 ≤ 5952) (by norm_num : 5952 ≤ 6016), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 5888 ≤ 5952) (by norm_num : 5952 ≤ 6016), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 5888 ≤ 5952) (by norm_num : 5952 ≤ 6016), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_6016_6080 :
    (∑ n ∈ Ico 6016 6080, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 6016 6080, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 6016 6080, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (27786 : ℤ) ∧
    (∑ n ∈ Ico 6016 6080, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (555749550391651961930673054 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_6080_6144 :
    (∑ n ∈ Ico 6080 6144, mobiusTreeValue 16 mobiusTable1200001 n) = (-5 : ℤ) ∧
    (∑ n ∈ Ico 6080 6144, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 6080 6144, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-4081693 : ℤ) ∧
    (∑ n ∈ Ico 6080 6144, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-81633879963576295264028627481 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_6016_6144 :
    (∑ n ∈ Ico 6016 6144, mobiusTreeValue 16 mobiusTable1200001 n) = (-5 : ℤ) ∧
    (∑ n ∈ Ico 6016 6144, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (79 : ℕ) ∧
    (∑ n ∈ Ico 6016 6144, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-4053907 : ℤ) ∧
    (∑ n ∈ Ico 6016 6144, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-81078130413184643302097954427 : ℤ) := by
  rcases cdemPrefixStats_6016_6080 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_6080_6144 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 6016 ≤ 6080) (by norm_num : 6080 ≤ 6144), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 6016 ≤ 6080) (by norm_num : 6080 ≤ 6144), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 6016 ≤ 6080) (by norm_num : 6080 ≤ 6144), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 6016 ≤ 6080) (by norm_num : 6080 ≤ 6144), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_5888_6144 :
    (∑ n ∈ Ico 5888 6144, mobiusTreeValue 16 mobiusTable1200001 n) = (3 : ℤ) ∧
    (∑ n ∈ Ico 5888 6144, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (159 : ℕ) ∧
    (∑ n ∈ Ico 5888 6144, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (2679749 : ℤ) ∧
    (∑ n ∈ Ico 5888 6144, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (53595051080276611206481626442 : ℤ) := by
  rcases cdemPrefixStats_5888_6016 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_6016_6144 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 5888 ≤ 6016) (by norm_num : 6016 ≤ 6144), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 5888 ≤ 6016) (by norm_num : 6016 ≤ 6144), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 5888 ≤ 6016) (by norm_num : 6016 ≤ 6144), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 5888 ≤ 6016) (by norm_num : 6016 ≤ 6144), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_5632_6144 :
    (∑ n ∈ Ico 5632 6144, mobiusTreeValue 16 mobiusTable1200001 n) = (-20 : ℤ) ∧
    (∑ n ∈ Ico 5632 6144, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (314 : ℕ) ∧
    (∑ n ∈ Ico 5632 6144, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-17170794 : ℤ) ∧
    (∑ n ∈ Ico 5632 6144, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-343415965873969045323195291431 : ℤ) := by
  rcases cdemPrefixStats_5632_5888 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_5888_6144 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 5632 ≤ 5888) (by norm_num : 5888 ≤ 6144), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 5632 ≤ 5888) (by norm_num : 5888 ≤ 6144), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 5632 ≤ 5888) (by norm_num : 5888 ≤ 6144), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 5632 ≤ 5888) (by norm_num : 5888 ≤ 6144), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_5120_6144 :
    (∑ n ∈ Ico 5120 6144, mobiusTreeValue 16 mobiusTable1200001 n) = (-5 : ℤ) ∧
    (∑ n ∈ Ico 5120 6144, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (623 : ℕ) ∧
    (∑ n ∈ Ico 5120 6144, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-3386517 : ℤ) ∧
    (∑ n ∈ Ico 5120 6144, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-67730181480436181855101012213 : ℤ) := by
  rcases cdemPrefixStats_5120_5632 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_5632_6144 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 5120 ≤ 5632) (by norm_num : 5632 ≤ 6144), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 5120 ≤ 5632) (by norm_num : 5632 ≤ 6144), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 5120 ≤ 5632) (by norm_num : 5632 ≤ 6144), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 5120 ≤ 5632) (by norm_num : 5632 ≤ 6144), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_4096_6144 :
    (∑ n ∈ Ico 4096 6144, mobiusTreeValue 16 mobiusTable1200001 n) = (13 : ℤ) ∧
    (∑ n ∈ Ico 4096 6144, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (1245 : ℕ) ∧
    (∑ n ∈ Ico 4096 6144, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (18066950 : ℤ) ∧
    (∑ n ∈ Ico 4096 6144, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (361339375314610290405278646755 : ℤ) := by
  rcases cdemPrefixStats_4096_5120 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_5120_6144 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 4096 ≤ 5120) (by norm_num : 5120 ≤ 6144), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 4096 ≤ 5120) (by norm_num : 5120 ≤ 6144), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 4096 ≤ 5120) (by norm_num : 5120 ≤ 6144), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 4096 ≤ 5120) (by norm_num : 5120 ≤ 6144), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_6144_6208 :
    (∑ n ∈ Ico 6144 6208, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 6144 6208, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 6144 6208, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (14872 : ℤ) ∧
    (∑ n ∈ Ico 6144 6208, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (297408140098278580951972066 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_6208_6272 :
    (∑ n ∈ Ico 6208 6272, mobiusTreeValue 16 mobiusTable1200001 n) = (-6 : ℤ) ∧
    (∑ n ∈ Ico 6208 6272, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 6208 6272, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-4802547 : ℤ) ∧
    (∑ n ∈ Ico 6208 6272, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-96050943473012871058470759282 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_6144_6272 :
    (∑ n ∈ Ico 6144 6272, mobiusTreeValue 16 mobiusTable1200001 n) = (-6 : ℤ) ∧
    (∑ n ∈ Ico 6144 6272, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 6144 6272, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-4787675 : ℤ) ∧
    (∑ n ∈ Ico 6144 6272, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-95753535332914592477518787216 : ℤ) := by
  rcases cdemPrefixStats_6144_6208 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_6208_6272 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 6144 ≤ 6208) (by norm_num : 6208 ≤ 6272), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 6144 ≤ 6208) (by norm_num : 6208 ≤ 6272), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 6144 ≤ 6208) (by norm_num : 6208 ≤ 6272), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 6144 ≤ 6208) (by norm_num : 6208 ≤ 6272), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_6272_6336 :
    (∑ n ∈ Ico 6272 6336, mobiusTreeValue 16 mobiusTable1200001 n) = (-7 : ℤ) ∧
    (∑ n ∈ Ico 6272 6336, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 6272 6336, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-5556140 : ℤ) ∧
    (∑ n ∈ Ico 6272 6336, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-111122952474557423744288396261 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_6336_6400 :
    (∑ n ∈ Ico 6336 6400, mobiusTreeValue 16 mobiusTable1200001 n) = (-6 : ℤ) ∧
    (∑ n ∈ Ico 6336 6400, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 6336 6400, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-4706005 : ℤ) ∧
    (∑ n ∈ Ico 6336 6400, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-94120165220651554646143480308 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_6272_6400 :
    (∑ n ∈ Ico 6272 6400, mobiusTreeValue 16 mobiusTable1200001 n) = (-13 : ℤ) ∧
    (∑ n ∈ Ico 6272 6400, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 6272 6400, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-10262145 : ℤ) ∧
    (∑ n ∈ Ico 6272 6400, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-205243117695208978390431876569 : ℤ) := by
  rcases cdemPrefixStats_6272_6336 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_6336_6400 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 6272 ≤ 6336) (by norm_num : 6336 ≤ 6400), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 6272 ≤ 6336) (by norm_num : 6336 ≤ 6400), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 6272 ≤ 6336) (by norm_num : 6336 ≤ 6400), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 6272 ≤ 6336) (by norm_num : 6336 ≤ 6400), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_6144_6400 :
    (∑ n ∈ Ico 6144 6400, mobiusTreeValue 16 mobiusTable1200001 n) = (-19 : ℤ) ∧
    (∑ n ∈ Ico 6144 6400, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (155 : ℕ) ∧
    (∑ n ∈ Ico 6144 6400, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-15049820 : ℤ) ∧
    (∑ n ∈ Ico 6144 6400, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-300996653028123570867950663785 : ℤ) := by
  rcases cdemPrefixStats_6144_6272 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_6272_6400 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 6144 ≤ 6272) (by norm_num : 6272 ≤ 6400), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 6144 ≤ 6272) (by norm_num : 6272 ≤ 6400), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 6144 ≤ 6272) (by norm_num : 6272 ≤ 6400), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 6144 ≤ 6272) (by norm_num : 6272 ≤ 6400), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_6400_6464 :
    (∑ n ∈ Ico 6400 6464, mobiusTreeValue 16 mobiusTable1200001 n) = (12 : ℤ) ∧
    (∑ n ∈ Ico 6400 6464, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 6400 6464, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (9339341 : ℤ) ∧
    (∑ n ∈ Ico 6400 6464, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (186786897709610888142562336968 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_6464_6528 :
    (∑ n ∈ Ico 6464 6528, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 6464 6528, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 6464 6528, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (749980 : ℤ) ∧
    (∑ n ∈ Ico 6464 6528, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (14999572915517211892364058922 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_6400_6528 :
    (∑ n ∈ Ico 6400 6528, mobiusTreeValue 16 mobiusTable1200001 n) = (13 : ℤ) ∧
    (∑ n ∈ Ico 6400 6528, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (79 : ℕ) ∧
    (∑ n ∈ Ico 6400 6528, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (10089321 : ℤ) ∧
    (∑ n ∈ Ico 6400 6528, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (201786470625128100034926395890 : ℤ) := by
  rcases cdemPrefixStats_6400_6464 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_6464_6528 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 6400 ≤ 6464) (by norm_num : 6464 ≤ 6528), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 6400 ≤ 6464) (by norm_num : 6464 ≤ 6528), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 6400 ≤ 6464) (by norm_num : 6464 ≤ 6528), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 6400 ≤ 6464) (by norm_num : 6464 ≤ 6528), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_6528_6592 :
    (∑ n ∈ Ico 6528 6592, mobiusTreeValue 16 mobiusTable1200001 n) = (-11 : ℤ) ∧
    (∑ n ∈ Ico 6528 6592, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 6528 6592, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-8373607 : ℤ) ∧
    (∑ n ∈ Ico 6528 6592, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-167472249997695077583185464241 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_6592_6656 :
    (∑ n ∈ Ico 6592 6656, mobiusTreeValue 16 mobiusTable1200001 n) = (9 : ℤ) ∧
    (∑ n ∈ Ico 6592 6656, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 6592 6656, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (6806956 : ℤ) ∧
    (∑ n ∈ Ico 6592 6656, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (136139166357653711588599946536 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_6528_6656 :
    (∑ n ∈ Ico 6528 6656, mobiusTreeValue 16 mobiusTable1200001 n) = (-2 : ℤ) ∧
    (∑ n ∈ Ico 6528 6656, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (76 : ℕ) ∧
    (∑ n ∈ Ico 6528 6656, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-1566651 : ℤ) ∧
    (∑ n ∈ Ico 6528 6656, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-31333083640041365994585517705 : ℤ) := by
  rcases cdemPrefixStats_6528_6592 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_6592_6656 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 6528 ≤ 6592) (by norm_num : 6592 ≤ 6656), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 6528 ≤ 6592) (by norm_num : 6592 ≤ 6656), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 6528 ≤ 6592) (by norm_num : 6592 ≤ 6656), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 6528 ≤ 6592) (by norm_num : 6592 ≤ 6656), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_6400_6656 :
    (∑ n ∈ Ico 6400 6656, mobiusTreeValue 16 mobiusTable1200001 n) = (11 : ℤ) ∧
    (∑ n ∈ Ico 6400 6656, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (155 : ℕ) ∧
    (∑ n ∈ Ico 6400 6656, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (8522670 : ℤ) ∧
    (∑ n ∈ Ico 6400 6656, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (170453386985086734040340878185 : ℤ) := by
  rcases cdemPrefixStats_6400_6528 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_6528_6656 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 6400 ≤ 6528) (by norm_num : 6528 ≤ 6656), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 6400 ≤ 6528) (by norm_num : 6528 ≤ 6656), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 6400 ≤ 6528) (by norm_num : 6528 ≤ 6656), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 6400 ≤ 6528) (by norm_num : 6528 ≤ 6656), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_6144_6656 :
    (∑ n ∈ Ico 6144 6656, mobiusTreeValue 16 mobiusTable1200001 n) = (-8 : ℤ) ∧
    (∑ n ∈ Ico 6144 6656, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (310 : ℕ) ∧
    (∑ n ∈ Ico 6144 6656, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-6527150 : ℤ) ∧
    (∑ n ∈ Ico 6144 6656, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-130543266043036836827609785600 : ℤ) := by
  rcases cdemPrefixStats_6144_6400 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_6400_6656 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 6144 ≤ 6400) (by norm_num : 6400 ≤ 6656), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 6144 ≤ 6400) (by norm_num : 6400 ≤ 6656), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 6144 ≤ 6400) (by norm_num : 6400 ≤ 6656), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 6144 ≤ 6400) (by norm_num : 6400 ≤ 6656), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_6656_6720 :
    (∑ n ∈ Ico 6656 6720, mobiusTreeValue 16 mobiusTable1200001 n) = (-3 : ℤ) ∧
    (∑ n ∈ Ico 6656 6720, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 6656 6720, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-2239796 : ℤ) ∧
    (∑ n ∈ Ico 6656 6720, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-44795976101664736245373154766 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_6720_6784 :
    (∑ n ∈ Ico 6720 6784, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 6720 6784, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 6720 6784, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (743937 : ℤ) ∧
    (∑ n ∈ Ico 6720 6784, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (14878806802777924000216374541 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_6656_6784 :
    (∑ n ∈ Ico 6656 6784, mobiusTreeValue 16 mobiusTable1200001 n) = (-2 : ℤ) ∧
    (∑ n ∈ Ico 6656 6784, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (80 : ℕ) ∧
    (∑ n ∈ Ico 6656 6784, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-1495859 : ℤ) ∧
    (∑ n ∈ Ico 6656 6784, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-29917169298886812245156780225 : ℤ) := by
  rcases cdemPrefixStats_6656_6720 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_6720_6784 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 6656 ≤ 6720) (by norm_num : 6720 ≤ 6784), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 6656 ≤ 6720) (by norm_num : 6720 ≤ 6784), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 6656 ≤ 6720) (by norm_num : 6720 ≤ 6784), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 6656 ≤ 6720) (by norm_num : 6720 ≤ 6784), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_6784_6848 :
    (∑ n ∈ Ico 6784 6848, mobiusTreeValue 16 mobiusTable1200001 n) = (2 : ℤ) ∧
    (∑ n ∈ Ico 6784 6848, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 6784 6848, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (1465417 : ℤ) ∧
    (∑ n ∈ Ico 6784 6848, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (29308311076754456170669150033 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_6848_6912 :
    (∑ n ∈ Ico 6848 6912, mobiusTreeValue 16 mobiusTable1200001 n) = (-5 : ℤ) ∧
    (∑ n ∈ Ico 6848 6912, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (35 : ℕ) ∧
    (∑ n ∈ Ico 6848 6912, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-3645839 : ℤ) ∧
    (∑ n ∈ Ico 6848 6912, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-72916794979471552501794074465 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_6784_6912 :
    (∑ n ∈ Ico 6784 6912, mobiusTreeValue 16 mobiusTable1200001 n) = (-3 : ℤ) ∧
    (∑ n ∈ Ico 6784 6912, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (75 : ℕ) ∧
    (∑ n ∈ Ico 6784 6912, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-2180422 : ℤ) ∧
    (∑ n ∈ Ico 6784 6912, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-43608483902717096331124924432 : ℤ) := by
  rcases cdemPrefixStats_6784_6848 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_6848_6912 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 6784 ≤ 6848) (by norm_num : 6848 ≤ 6912), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 6784 ≤ 6848) (by norm_num : 6848 ≤ 6912), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 6784 ≤ 6848) (by norm_num : 6848 ≤ 6912), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 6784 ≤ 6848) (by norm_num : 6848 ≤ 6912), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_6656_6912 :
    (∑ n ∈ Ico 6656 6912, mobiusTreeValue 16 mobiusTable1200001 n) = (-5 : ℤ) ∧
    (∑ n ∈ Ico 6656 6912, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (155 : ℕ) ∧
    (∑ n ∈ Ico 6656 6912, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-3676281 : ℤ) ∧
    (∑ n ∈ Ico 6656 6912, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-73525653201603908576281704657 : ℤ) := by
  rcases cdemPrefixStats_6656_6784 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_6784_6912 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 6656 ≤ 6784) (by norm_num : 6784 ≤ 6912), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 6656 ≤ 6784) (by norm_num : 6784 ≤ 6912), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 6656 ≤ 6784) (by norm_num : 6784 ≤ 6912), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 6656 ≤ 6784) (by norm_num : 6784 ≤ 6912), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_6912_6976 :
    (∑ n ∈ Ico 6912 6976, mobiusTreeValue 16 mobiusTable1200001 n) = (-3 : ℤ) ∧
    (∑ n ∈ Ico 6912 6976, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 6912 6976, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-2142963 : ℤ) ∧
    (∑ n ∈ Ico 6912 6976, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-42859264403061489879878837295 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_6976_7040 :
    (∑ n ∈ Ico 6976 7040, mobiusTreeValue 16 mobiusTable1200001 n) = (-2 : ℤ) ∧
    (∑ n ∈ Ico 6976 7040, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 6976 7040, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-1446796 : ℤ) ∧
    (∑ n ∈ Ico 6976 7040, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-28935971508579692280475498858 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_6912_7040 :
    (∑ n ∈ Ico 6912 7040, mobiusTreeValue 16 mobiusTable1200001 n) = (-5 : ℤ) ∧
    (∑ n ∈ Ico 6912 7040, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 6912 7040, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-3589759 : ℤ) ∧
    (∑ n ∈ Ico 6912 7040, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-71795235911641182160354336153 : ℤ) := by
  rcases cdemPrefixStats_6912_6976 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_6976_7040 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 6912 ≤ 6976) (by norm_num : 6976 ≤ 7040), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 6912 ≤ 6976) (by norm_num : 6976 ≤ 7040), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 6912 ≤ 6976) (by norm_num : 6976 ≤ 7040), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 6912 ≤ 6976) (by norm_num : 6976 ≤ 7040), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_7040_7104 :
    (∑ n ∈ Ico 7040 7104, mobiusTreeValue 16 mobiusTable1200001 n) = (8 : ℤ) ∧
    (∑ n ∈ Ico 7040 7104, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 7040 7104, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (5653610 : ℤ) ∧
    (∑ n ∈ Ico 7040 7104, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (113072308980137389316450930105 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_7104_7168 :
    (∑ n ∈ Ico 7104 7168, mobiusTreeValue 16 mobiusTable1200001 n) = (14 : ℤ) ∧
    (∑ n ∈ Ico 7104 7168, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 7104 7168, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (9803197 : ℤ) ∧
    (∑ n ∈ Ico 7104 7168, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (196064014403923115721614621644 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_7040_7168 :
    (∑ n ∈ Ico 7040 7168, mobiusTreeValue 16 mobiusTable1200001 n) = (22 : ℤ) ∧
    (∑ n ∈ Ico 7040 7168, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 7040 7168, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (15456807 : ℤ) ∧
    (∑ n ∈ Ico 7040 7168, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (309136323384060505038065551749 : ℤ) := by
  rcases cdemPrefixStats_7040_7104 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_7104_7168 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 7040 ≤ 7104) (by norm_num : 7104 ≤ 7168), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 7040 ≤ 7104) (by norm_num : 7104 ≤ 7168), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 7040 ≤ 7104) (by norm_num : 7104 ≤ 7168), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 7040 ≤ 7104) (by norm_num : 7104 ≤ 7168), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_6912_7168 :
    (∑ n ∈ Ico 6912 7168, mobiusTreeValue 16 mobiusTable1200001 n) = (17 : ℤ) ∧
    (∑ n ∈ Ico 6912 7168, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (155 : ℕ) ∧
    (∑ n ∈ Ico 6912 7168, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (11867048 : ℤ) ∧
    (∑ n ∈ Ico 6912 7168, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (237341087472419322877711215596 : ℤ) := by
  rcases cdemPrefixStats_6912_7040 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_7040_7168 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 6912 ≤ 7040) (by norm_num : 7040 ≤ 7168), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 6912 ≤ 7040) (by norm_num : 7040 ≤ 7168), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 6912 ≤ 7040) (by norm_num : 7040 ≤ 7168), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 6912 ≤ 7040) (by norm_num : 7040 ≤ 7168), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_6656_7168 :
    (∑ n ∈ Ico 6656 7168, mobiusTreeValue 16 mobiusTable1200001 n) = (12 : ℤ) ∧
    (∑ n ∈ Ico 6656 7168, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (310 : ℕ) ∧
    (∑ n ∈ Ico 6656 7168, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (8190767 : ℤ) ∧
    (∑ n ∈ Ico 6656 7168, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (163815434270815414301429510939 : ℤ) := by
  rcases cdemPrefixStats_6656_6912 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_6912_7168 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 6656 ≤ 6912) (by norm_num : 6912 ≤ 7168), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 6656 ≤ 6912) (by norm_num : 6912 ≤ 7168), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 6656 ≤ 6912) (by norm_num : 6912 ≤ 7168), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 6656 ≤ 6912) (by norm_num : 6912 ≤ 7168), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_6144_7168 :
    (∑ n ∈ Ico 6144 7168, mobiusTreeValue 16 mobiusTable1200001 n) = (4 : ℤ) ∧
    (∑ n ∈ Ico 6144 7168, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (620 : ℕ) ∧
    (∑ n ∈ Ico 6144 7168, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (1663617 : ℤ) ∧
    (∑ n ∈ Ico 6144 7168, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (33272168227778577473819725339 : ℤ) := by
  rcases cdemPrefixStats_6144_6656 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_6656_7168 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 6144 ≤ 6656) (by norm_num : 6656 ≤ 7168), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 6144 ≤ 6656) (by norm_num : 6656 ≤ 7168), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 6144 ≤ 6656) (by norm_num : 6656 ≤ 7168), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 6144 ≤ 6656) (by norm_num : 6656 ≤ 7168), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_7168_7232 :
    (∑ n ∈ Ico 7168 7232, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 7168 7232, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 7168 7232, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (695931 : ℤ) ∧
    (∑ n ∈ Ico 7168 7232, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (13918641475528731497162139930 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_7232_7296 :
    (∑ n ∈ Ico 7232 7296, mobiusTreeValue 16 mobiusTable1200001 n) = (10 : ℤ) ∧
    (∑ n ∈ Ico 7232 7296, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 7232 7296, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (6886820 : ℤ) ∧
    (∑ n ∈ Ico 7232 7296, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (137736467602200236955051189046 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_7168_7296 :
    (∑ n ∈ Ico 7168 7296, mobiusTreeValue 16 mobiusTable1200001 n) = (11 : ℤ) ∧
    (∑ n ∈ Ico 7168 7296, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (79 : ℕ) ∧
    (∑ n ∈ Ico 7168 7296, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (7582751 : ℤ) ∧
    (∑ n ∈ Ico 7168 7296, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (151655109077728968452213328976 : ℤ) := by
  rcases cdemPrefixStats_7168_7232 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_7232_7296 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 7168 ≤ 7232) (by norm_num : 7232 ≤ 7296), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 7168 ≤ 7232) (by norm_num : 7232 ≤ 7296), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 7168 ≤ 7232) (by norm_num : 7232 ≤ 7296), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 7168 ≤ 7232) (by norm_num : 7232 ≤ 7296), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_7296_7360 :
    (∑ n ∈ Ico 7296 7360, mobiusTreeValue 16 mobiusTable1200001 n) = (-4 : ℤ) ∧
    (∑ n ∈ Ico 7296 7360, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 7296 7360, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-2732461 : ℤ) ∧
    (∑ n ∈ Ico 7296 7360, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-54649196498816029319212531045 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_7360_7424 :
    (∑ n ∈ Ico 7360 7424, mobiusTreeValue 16 mobiusTable1200001 n) = (9 : ℤ) ∧
    (∑ n ∈ Ico 7360 7424, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 7360 7424, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (6087330 : ℤ) ∧
    (∑ n ∈ Ico 7360 7424, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (121746658731553980198079820736 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_7296_7424 :
    (∑ n ∈ Ico 7296 7424, mobiusTreeValue 16 mobiusTable1200001 n) = (5 : ℤ) ∧
    (∑ n ∈ Ico 7296 7424, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (79 : ℕ) ∧
    (∑ n ∈ Ico 7296 7424, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (3354869 : ℤ) ∧
    (∑ n ∈ Ico 7296 7424, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (67097462232737950878867289691 : ℤ) := by
  rcases cdemPrefixStats_7296_7360 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_7360_7424 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 7296 ≤ 7360) (by norm_num : 7360 ≤ 7424), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 7296 ≤ 7360) (by norm_num : 7360 ≤ 7424), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 7296 ≤ 7360) (by norm_num : 7360 ≤ 7424), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 7296 ≤ 7360) (by norm_num : 7360 ≤ 7424), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_7168_7424 :
    (∑ n ∈ Ico 7168 7424, mobiusTreeValue 16 mobiusTable1200001 n) = (16 : ℤ) ∧
    (∑ n ∈ Ico 7168 7424, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (158 : ℕ) ∧
    (∑ n ∈ Ico 7168 7424, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (10937620 : ℤ) ∧
    (∑ n ∈ Ico 7168 7424, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (218752571310466919331080618667 : ℤ) := by
  rcases cdemPrefixStats_7168_7296 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_7296_7424 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 7168 ≤ 7296) (by norm_num : 7296 ≤ 7424), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 7168 ≤ 7296) (by norm_num : 7296 ≤ 7424), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 7168 ≤ 7296) (by norm_num : 7296 ≤ 7424), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 7168 ≤ 7296) (by norm_num : 7296 ≤ 7424), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_7424_7488 :
    (∑ n ∈ Ico 7424 7488, mobiusTreeValue 16 mobiusTable1200001 n) = (3 : ℤ) ∧
    (∑ n ∈ Ico 7424 7488, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 7424 7488, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (2020674 : ℤ) ∧
    (∑ n ∈ Ico 7424 7488, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (40413532123761444204916403552 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_7488_7552 :
    (∑ n ∈ Ico 7488 7552, mobiusTreeValue 16 mobiusTable1200001 n) = (-9 : ℤ) ∧
    (∑ n ∈ Ico 7488 7552, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 7488 7552, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-5981696 : ℤ) ∧
    (∑ n ∈ Ico 7488 7552, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-119634021991030832736239813904 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_7424_7552 :
    (∑ n ∈ Ico 7424 7552, mobiusTreeValue 16 mobiusTable1200001 n) = (-6 : ℤ) ∧
    (∑ n ∈ Ico 7424 7552, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (76 : ℕ) ∧
    (∑ n ∈ Ico 7424 7552, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-3961022 : ℤ) ∧
    (∑ n ∈ Ico 7424 7552, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-79220489867269388531323410352 : ℤ) := by
  rcases cdemPrefixStats_7424_7488 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_7488_7552 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 7424 ≤ 7488) (by norm_num : 7488 ≤ 7552), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 7424 ≤ 7488) (by norm_num : 7488 ≤ 7552), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 7424 ≤ 7488) (by norm_num : 7488 ≤ 7552), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 7424 ≤ 7488) (by norm_num : 7488 ≤ 7552), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_7552_7616 :
    (∑ n ∈ Ico 7552 7616, mobiusTreeValue 16 mobiusTable1200001 n) = (-10 : ℤ) ∧
    (∑ n ∈ Ico 7552 7616, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 7552 7616, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-6607621 : ℤ) ∧
    (∑ n ∈ Ico 7552 7616, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-132152536916470976753548989686 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_7616_7680 :
    (∑ n ∈ Ico 7616 7680, mobiusTreeValue 16 mobiusTable1200001 n) = (5 : ℤ) ∧
    (∑ n ∈ Ico 7616 7680, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 7616 7680, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (3275846 : ℤ) ∧
    (∑ n ∈ Ico 7616 7680, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (65516995241681423072103979122 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_7552_7680 :
    (∑ n ∈ Ico 7552 7680, mobiusTreeValue 16 mobiusTable1200001 n) = (-5 : ℤ) ∧
    (∑ n ∈ Ico 7552 7680, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (81 : ℕ) ∧
    (∑ n ∈ Ico 7552 7680, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-3331775 : ℤ) ∧
    (∑ n ∈ Ico 7552 7680, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-66635541674789553681445010564 : ℤ) := by
  rcases cdemPrefixStats_7552_7616 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_7616_7680 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 7552 ≤ 7616) (by norm_num : 7616 ≤ 7680), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 7552 ≤ 7616) (by norm_num : 7616 ≤ 7680), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 7552 ≤ 7616) (by norm_num : 7616 ≤ 7680), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 7552 ≤ 7616) (by norm_num : 7616 ≤ 7680), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_7424_7680 :
    (∑ n ∈ Ico 7424 7680, mobiusTreeValue 16 mobiusTable1200001 n) = (-11 : ℤ) ∧
    (∑ n ∈ Ico 7424 7680, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (157 : ℕ) ∧
    (∑ n ∈ Ico 7424 7680, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-7292797 : ℤ) ∧
    (∑ n ∈ Ico 7424 7680, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-145856031542058942212768420916 : ℤ) := by
  rcases cdemPrefixStats_7424_7552 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_7552_7680 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 7424 ≤ 7552) (by norm_num : 7552 ≤ 7680), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 7424 ≤ 7552) (by norm_num : 7552 ≤ 7680), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 7424 ≤ 7552) (by norm_num : 7552 ≤ 7680), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 7424 ≤ 7552) (by norm_num : 7552 ≤ 7680), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_7168_7680 :
    (∑ n ∈ Ico 7168 7680, mobiusTreeValue 16 mobiusTable1200001 n) = (5 : ℤ) ∧
    (∑ n ∈ Ico 7168 7680, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (315 : ℕ) ∧
    (∑ n ∈ Ico 7168 7680, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (3644823 : ℤ) ∧
    (∑ n ∈ Ico 7168 7680, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (72896539768407977118312197751 : ℤ) := by
  rcases cdemPrefixStats_7168_7424 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_7424_7680 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 7168 ≤ 7424) (by norm_num : 7424 ≤ 7680), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 7168 ≤ 7424) (by norm_num : 7424 ≤ 7680), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 7168 ≤ 7424) (by norm_num : 7424 ≤ 7680), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 7168 ≤ 7424) (by norm_num : 7424 ≤ 7680), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_7680_7744 :
    (∑ n ∈ Ico 7680 7744, mobiusTreeValue 16 mobiusTable1200001 n) = (-10 : ℤ) ∧
    (∑ n ∈ Ico 7680 7744, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 7680 7744, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-6495326 : ℤ) ∧
    (∑ n ∈ Ico 7680 7744, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-129906691090241807624980877570 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_7744_7808 :
    (∑ n ∈ Ico 7744 7808, mobiusTreeValue 16 mobiusTable1200001 n) = (4 : ℤ) ∧
    (∑ n ∈ Ico 7744 7808, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 7744 7808, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (2579956 : ℤ) ∧
    (∑ n ∈ Ico 7744 7808, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (51599187735935231281516705679 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_7680_7808 :
    (∑ n ∈ Ico 7680 7808, mobiusTreeValue 16 mobiusTable1200001 n) = (-6 : ℤ) ∧
    (∑ n ∈ Ico 7680 7808, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 7680 7808, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-3915370 : ℤ) ∧
    (∑ n ∈ Ico 7680 7808, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-78307503354306576343464171891 : ℤ) := by
  rcases cdemPrefixStats_7680_7744 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_7744_7808 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 7680 ≤ 7744) (by norm_num : 7744 ≤ 7808), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 7680 ≤ 7744) (by norm_num : 7744 ≤ 7808), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 7680 ≤ 7744) (by norm_num : 7744 ≤ 7808), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 7680 ≤ 7744) (by norm_num : 7744 ≤ 7808), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_7808_7872 :
    (∑ n ∈ Ico 7808 7872, mobiusTreeValue 16 mobiusTable1200001 n) = (6 : ℤ) ∧
    (∑ n ∈ Ico 7808 7872, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 7808 7872, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (3828419 : ℤ) ∧
    (∑ n ∈ Ico 7808 7872, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (76568450109773475340168520896 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_7872_7936 :
    (∑ n ∈ Ico 7872 7936, mobiusTreeValue 16 mobiusTable1200001 n) = (-5 : ℤ) ∧
    (∑ n ∈ Ico 7872 7936, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 7872 7936, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-3166210 : ℤ) ∧
    (∑ n ∈ Ico 7872 7936, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-63324259635057721464669738387 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_7808_7936 :
    (∑ n ∈ Ico 7808 7936, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 7808 7936, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (79 : ℕ) ∧
    (∑ n ∈ Ico 7808 7936, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (662209 : ℤ) ∧
    (∑ n ∈ Ico 7808 7936, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (13244190474715753875498782509 : ℤ) := by
  rcases cdemPrefixStats_7808_7872 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_7872_7936 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 7808 ≤ 7872) (by norm_num : 7872 ≤ 7936), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 7808 ≤ 7872) (by norm_num : 7872 ≤ 7936), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 7808 ≤ 7872) (by norm_num : 7872 ≤ 7936), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 7808 ≤ 7872) (by norm_num : 7872 ≤ 7936), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_7680_7936 :
    (∑ n ∈ Ico 7680 7936, mobiusTreeValue 16 mobiusTable1200001 n) = (-5 : ℤ) ∧
    (∑ n ∈ Ico 7680 7936, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (157 : ℕ) ∧
    (∑ n ∈ Ico 7680 7936, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-3253161 : ℤ) ∧
    (∑ n ∈ Ico 7680 7936, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-65063312879590822467965389382 : ℤ) := by
  rcases cdemPrefixStats_7680_7808 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_7808_7936 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 7680 ≤ 7808) (by norm_num : 7808 ≤ 7936), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 7680 ≤ 7808) (by norm_num : 7808 ≤ 7936), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 7680 ≤ 7808) (by norm_num : 7808 ≤ 7936), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 7680 ≤ 7808) (by norm_num : 7808 ≤ 7936), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_7936_8000 :
    (∑ n ∈ Ico 7936 8000, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 7936 8000, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 7936 8000, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (605010 : ℤ) ∧
    (∑ n ∈ Ico 7936 8000, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (12100202266687792778179144693 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_8000_8064 :
    (∑ n ∈ Ico 8000 8064, mobiusTreeValue 16 mobiusTable1200001 n) = (14 : ℤ) ∧
    (∑ n ∈ Ico 8000 8064, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 8000 8064, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (8712153 : ℤ) ∧
    (∑ n ∈ Ico 8000 8064, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (174243174435423239918065317217 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_7936_8064 :
    (∑ n ∈ Ico 7936 8064, mobiusTreeValue 16 mobiusTable1200001 n) = (15 : ℤ) ∧
    (∑ n ∈ Ico 7936 8064, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 7936 8064, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (9317163 : ℤ) ∧
    (∑ n ∈ Ico 7936 8064, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (186343376702111032696244461910 : ℤ) := by
  rcases cdemPrefixStats_7936_8000 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_8000_8064 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 7936 ≤ 8000) (by norm_num : 8000 ≤ 8064), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 7936 ≤ 8000) (by norm_num : 8000 ≤ 8064), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 7936 ≤ 8000) (by norm_num : 8000 ≤ 8064), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 7936 ≤ 8000) (by norm_num : 8000 ≤ 8064), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_8064_8128 :
    (∑ n ∈ Ico 8064 8128, mobiusTreeValue 16 mobiusTable1200001 n) = (-4 : ℤ) ∧
    (∑ n ∈ Ico 8064 8128, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 8064 8128, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-2462277 : ℤ) ∧
    (∑ n ∈ Ico 8064 8128, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-49245620156637491461467424931 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_8128_8192 :
    (∑ n ∈ Ico 8128 8192, mobiusTreeValue 16 mobiusTable1200001 n) = (13 : ℤ) ∧
    (∑ n ∈ Ico 8128 8192, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 8128 8192, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (7980396 : ℤ) ∧
    (∑ n ∈ Ico 8128 8192, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (159607985344573492997664568665 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_8064_8192 :
    (∑ n ∈ Ico 8064 8192, mobiusTreeValue 16 mobiusTable1200001 n) = (9 : ℤ) ∧
    (∑ n ∈ Ico 8064 8192, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 8064 8192, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (5518119 : ℤ) ∧
    (∑ n ∈ Ico 8064 8192, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (110362365187936001536197143734 : ℤ) := by
  rcases cdemPrefixStats_8064_8128 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_8128_8192 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 8064 ≤ 8128) (by norm_num : 8128 ≤ 8192), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 8064 ≤ 8128) (by norm_num : 8128 ≤ 8192), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 8064 ≤ 8128) (by norm_num : 8128 ≤ 8192), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 8064 ≤ 8128) (by norm_num : 8128 ≤ 8192), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_7936_8192 :
    (∑ n ∈ Ico 7936 8192, mobiusTreeValue 16 mobiusTable1200001 n) = (24 : ℤ) ∧
    (∑ n ∈ Ico 7936 8192, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (154 : ℕ) ∧
    (∑ n ∈ Ico 7936 8192, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (14835282 : ℤ) ∧
    (∑ n ∈ Ico 7936 8192, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (296705741890047034232441605644 : ℤ) := by
  rcases cdemPrefixStats_7936_8064 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_8064_8192 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 7936 ≤ 8064) (by norm_num : 8064 ≤ 8192), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 7936 ≤ 8064) (by norm_num : 8064 ≤ 8192), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 7936 ≤ 8064) (by norm_num : 8064 ≤ 8192), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 7936 ≤ 8064) (by norm_num : 8064 ≤ 8192), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_7680_8192 :
    (∑ n ∈ Ico 7680 8192, mobiusTreeValue 16 mobiusTable1200001 n) = (19 : ℤ) ∧
    (∑ n ∈ Ico 7680 8192, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (311 : ℕ) ∧
    (∑ n ∈ Ico 7680 8192, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (11582121 : ℤ) ∧
    (∑ n ∈ Ico 7680 8192, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (231642429010456211764476216262 : ℤ) := by
  rcases cdemPrefixStats_7680_7936 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_7936_8192 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 7680 ≤ 7936) (by norm_num : 7936 ≤ 8192), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 7680 ≤ 7936) (by norm_num : 7936 ≤ 8192), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 7680 ≤ 7936) (by norm_num : 7936 ≤ 8192), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 7680 ≤ 7936) (by norm_num : 7936 ≤ 8192), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_7168_8192 :
    (∑ n ∈ Ico 7168 8192, mobiusTreeValue 16 mobiusTable1200001 n) = (24 : ℤ) ∧
    (∑ n ∈ Ico 7168 8192, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (626 : ℕ) ∧
    (∑ n ∈ Ico 7168 8192, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (15226944 : ℤ) ∧
    (∑ n ∈ Ico 7168 8192, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (304538968778864188882788414013 : ℤ) := by
  rcases cdemPrefixStats_7168_7680 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_7680_8192 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 7168 ≤ 7680) (by norm_num : 7680 ≤ 8192), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 7168 ≤ 7680) (by norm_num : 7680 ≤ 8192), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 7168 ≤ 7680) (by norm_num : 7680 ≤ 8192), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 7168 ≤ 7680) (by norm_num : 7680 ≤ 8192), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_6144_8192 :
    (∑ n ∈ Ico 6144 8192, mobiusTreeValue 16 mobiusTable1200001 n) = (28 : ℤ) ∧
    (∑ n ∈ Ico 6144 8192, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (1246 : ℕ) ∧
    (∑ n ∈ Ico 6144 8192, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (16890561 : ℤ) ∧
    (∑ n ∈ Ico 6144 8192, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (337811137006642766356608139352 : ℤ) := by
  rcases cdemPrefixStats_6144_7168 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_7168_8192 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 6144 ≤ 7168) (by norm_num : 7168 ≤ 8192), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 6144 ≤ 7168) (by norm_num : 7168 ≤ 8192), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 6144 ≤ 7168) (by norm_num : 7168 ≤ 8192), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 6144 ≤ 7168) (by norm_num : 7168 ≤ 8192), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_4096_8192 :
    (∑ n ∈ Ico 4096 8192, mobiusTreeValue 16 mobiusTable1200001 n) = (41 : ℤ) ∧
    (∑ n ∈ Ico 4096 8192, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (2491 : ℕ) ∧
    (∑ n ∈ Ico 4096 8192, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (34957511 : ℤ) ∧
    (∑ n ∈ Ico 4096 8192, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (699150512321253056761886786107 : ℤ) := by
  rcases cdemPrefixStats_4096_6144 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_6144_8192 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 4096 ≤ 6144) (by norm_num : 6144 ≤ 8192), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 4096 ≤ 6144) (by norm_num : 6144 ≤ 8192), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 4096 ≤ 6144) (by norm_num : 6144 ≤ 8192), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 4096 ≤ 6144) (by norm_num : 6144 ≤ 8192), hR1, hR2] <;> norm_num

theorem cdemPrefixGroup001_checked_complete :
    (∑ n ∈ Ico 4096 8192, mobiusTreeValue 16 mobiusTable1200001 n) = (41 : ℤ) ∧
    (∑ n ∈ Ico 4096 8192, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (2491 : ℕ) ∧
    (∑ n ∈ Ico 4096 8192, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (34957511 : ℤ) ∧
    (∑ n ∈ Ico 4096 8192, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (699150512321253056761886786107 : ℤ) := cdemPrefixStats_4096_8192
end Helfgott
#print axioms Helfgott.cdemPrefixGroup001_checked_complete

open Helfgott Finset
open scoped BigOperators

theorem solution :
    (∑ n ∈ Ico 4096 8192, mobiusTreeValue 16 mobiusTable1200001 n) = (41 : ℤ) ∧
    (∑ n ∈ Ico 4096 8192, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (2491 : ℕ) ∧
    (∑ n ∈ Ico 4096 8192, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (34957511 : ℤ) ∧
    (∑ n ∈ Ico 4096 8192, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (699150512321253056761886786107 : ℤ) := Helfgott.cdemPrefixGroup001_checked_complete
#print axioms solution
