-- Prove2me | solution 1 for Helfgott.cdemPrefixGroup036_checked
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-09T02:34:19.282095+00:00
-- url     : https://prove2.me/submissions/fc38dcc6-c30a-41bc-a26d-8736d283fab4

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
private theorem cdemPrefixStats_147456_147520 :
    (∑ n ∈ Ico 147456 147520, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 147456 147520, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 147456 147520, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-33894 : ℤ) ∧
    (∑ n ∈ Ico 147456 147520, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-677947669608272199409319550 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_147520_147584 :
    (∑ n ∈ Ico 147520 147584, mobiusTreeValue 16 mobiusTable1200001 n) = (-5 : ℤ) ∧
    (∑ n ∈ Ico 147520 147584, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 147520 147584, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-169403 : ℤ) ∧
    (∑ n ∈ Ico 147520 147584, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-3388148940536313716842455728 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_147456_147584 :
    (∑ n ∈ Ico 147456 147584, mobiusTreeValue 16 mobiusTable1200001 n) = (-6 : ℤ) ∧
    (∑ n ∈ Ico 147456 147584, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 147456 147584, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-203297 : ℤ) ∧
    (∑ n ∈ Ico 147456 147584, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-4066096610144585916251775278 : ℤ) := by
  rcases cdemPrefixStats_147456_147520 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_147520_147584 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 147456 ≤ 147520) (by norm_num : 147520 ≤ 147584), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 147456 ≤ 147520) (by norm_num : 147520 ≤ 147584), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 147456 ≤ 147520) (by norm_num : 147520 ≤ 147584), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 147456 ≤ 147520) (by norm_num : 147520 ≤ 147584), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_147584_147648 :
    (∑ n ∈ Ico 147584 147648, mobiusTreeValue 16 mobiusTable1200001 n) = (5 : ℤ) ∧
    (∑ n ∈ Ico 147584 147648, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 147584 147648, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (169351 : ℤ) ∧
    (∑ n ∈ Ico 147584 147648, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (3387084148161583108604240003 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_147648_147712 :
    (∑ n ∈ Ico 147648 147712, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 147648 147712, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 147648 147712, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-33860 : ℤ) ∧
    (∑ n ∈ Ico 147648 147712, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-677176454956568075908368584 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_147584_147712 :
    (∑ n ∈ Ico 147584 147712, mobiusTreeValue 16 mobiusTable1200001 n) = (4 : ℤ) ∧
    (∑ n ∈ Ico 147584 147712, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 147584 147712, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (135491 : ℤ) ∧
    (∑ n ∈ Ico 147584 147712, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (2709907693205015032695871419 : ℤ) := by
  rcases cdemPrefixStats_147584_147648 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_147648_147712 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 147584 ≤ 147648) (by norm_num : 147648 ≤ 147712), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 147584 ≤ 147648) (by norm_num : 147648 ≤ 147712), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 147584 ≤ 147648) (by norm_num : 147648 ≤ 147712), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 147584 ≤ 147648) (by norm_num : 147648 ≤ 147712), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_147456_147712 :
    (∑ n ∈ Ico 147456 147712, mobiusTreeValue 16 mobiusTable1200001 n) = (-2 : ℤ) ∧
    (∑ n ∈ Ico 147456 147712, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (156 : ℕ) ∧
    (∑ n ∈ Ico 147456 147712, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-67806 : ℤ) ∧
    (∑ n ∈ Ico 147456 147712, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-1356188916939570883555903859 : ℤ) := by
  rcases cdemPrefixStats_147456_147584 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_147584_147712 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 147456 ≤ 147584) (by norm_num : 147584 ≤ 147712), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 147456 ≤ 147584) (by norm_num : 147584 ≤ 147712), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 147456 ≤ 147584) (by norm_num : 147584 ≤ 147712), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 147456 ≤ 147584) (by norm_num : 147584 ≤ 147712), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_147712_147776 :
    (∑ n ∈ Ico 147712 147776, mobiusTreeValue 16 mobiusTable1200001 n) = (-2 : ℤ) ∧
    (∑ n ∈ Ico 147712 147776, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 147712 147776, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-67705 : ℤ) ∧
    (∑ n ∈ Ico 147712 147776, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-1354128080559672680127038156 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_147776_147840 :
    (∑ n ∈ Ico 147776 147840, mobiusTreeValue 16 mobiusTable1200001 n) = (-8 : ℤ) ∧
    (∑ n ∈ Ico 147776 147840, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (42 : ℕ) ∧
    (∑ n ∈ Ico 147776 147840, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-270626 : ℤ) ∧
    (∑ n ∈ Ico 147776 147840, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-5412600971831459636852152789 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_147712_147840 :
    (∑ n ∈ Ico 147712 147840, mobiusTreeValue 16 mobiusTable1200001 n) = (-10 : ℤ) ∧
    (∑ n ∈ Ico 147712 147840, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (80 : ℕ) ∧
    (∑ n ∈ Ico 147712 147840, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-338331 : ℤ) ∧
    (∑ n ∈ Ico 147712 147840, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-6766729052391132316979190945 : ℤ) := by
  rcases cdemPrefixStats_147712_147776 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_147776_147840 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 147712 ≤ 147776) (by norm_num : 147776 ≤ 147840), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 147712 ≤ 147776) (by norm_num : 147776 ≤ 147840), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 147712 ≤ 147776) (by norm_num : 147776 ≤ 147840), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 147712 ≤ 147776) (by norm_num : 147776 ≤ 147840), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_147840_147904 :
    (∑ n ∈ Ico 147840 147904, mobiusTreeValue 16 mobiusTable1200001 n) = (4 : ℤ) ∧
    (∑ n ∈ Ico 147840 147904, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 147840 147904, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (135274 : ℤ) ∧
    (∑ n ∈ Ico 147840 147904, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (2705531622288899460377101322 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_147904_147968 :
    (∑ n ∈ Ico 147904 147968, mobiusTreeValue 16 mobiusTable1200001 n) = (2 : ℤ) ∧
    (∑ n ∈ Ico 147904 147968, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 147904 147968, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (67640 : ℤ) ∧
    (∑ n ∈ Ico 147904 147968, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1352836127288954764196377040 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_147840_147968 :
    (∑ n ∈ Ico 147840 147968, mobiusTreeValue 16 mobiusTable1200001 n) = (6 : ℤ) ∧
    (∑ n ∈ Ico 147840 147968, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 147840 147968, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (202914 : ℤ) ∧
    (∑ n ∈ Ico 147840 147968, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (4058367749577854224573478362 : ℤ) := by
  rcases cdemPrefixStats_147840_147904 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_147904_147968 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 147840 ≤ 147904) (by norm_num : 147904 ≤ 147968), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 147840 ≤ 147904) (by norm_num : 147904 ≤ 147968), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 147840 ≤ 147904) (by norm_num : 147904 ≤ 147968), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 147840 ≤ 147904) (by norm_num : 147904 ≤ 147968), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_147712_147968 :
    (∑ n ∈ Ico 147712 147968, mobiusTreeValue 16 mobiusTable1200001 n) = (-4 : ℤ) ∧
    (∑ n ∈ Ico 147712 147968, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (158 : ℕ) ∧
    (∑ n ∈ Ico 147712 147968, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-135417 : ℤ) ∧
    (∑ n ∈ Ico 147712 147968, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-2708361302813278092405712583 : ℤ) := by
  rcases cdemPrefixStats_147712_147840 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_147840_147968 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 147712 ≤ 147840) (by norm_num : 147840 ≤ 147968), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 147712 ≤ 147840) (by norm_num : 147840 ≤ 147968), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 147712 ≤ 147840) (by norm_num : 147840 ≤ 147968), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 147712 ≤ 147840) (by norm_num : 147840 ≤ 147968), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_147456_147968 :
    (∑ n ∈ Ico 147456 147968, mobiusTreeValue 16 mobiusTable1200001 n) = (-6 : ℤ) ∧
    (∑ n ∈ Ico 147456 147968, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (314 : ℕ) ∧
    (∑ n ∈ Ico 147456 147968, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-203223 : ℤ) ∧
    (∑ n ∈ Ico 147456 147968, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-4064550219752848975961616442 : ℤ) := by
  rcases cdemPrefixStats_147456_147712 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_147712_147968 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 147456 ≤ 147712) (by norm_num : 147712 ≤ 147968), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 147456 ≤ 147712) (by norm_num : 147712 ≤ 147968), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 147456 ≤ 147712) (by norm_num : 147712 ≤ 147968), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 147456 ≤ 147712) (by norm_num : 147712 ≤ 147968), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_147968_148032 :
    (∑ n ∈ Ico 147968 148032, mobiusTreeValue 16 mobiusTable1200001 n) = (3 : ℤ) ∧
    (∑ n ∈ Ico 147968 148032, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (35 : ℕ) ∧
    (∑ n ∈ Ico 147968 148032, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (101346 : ℤ) ∧
    (∑ n ∈ Ico 147968 148032, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (2026940257637426333219374896 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_148032_148096 :
    (∑ n ∈ Ico 148032 148096, mobiusTreeValue 16 mobiusTable1200001 n) = (-2 : ℤ) ∧
    (∑ n ∈ Ico 148032 148096, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 148032 148096, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-67513 : ℤ) ∧
    (∑ n ∈ Ico 148032 148096, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-1350351976759089138564937634 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_147968_148096 :
    (∑ n ∈ Ico 147968 148096, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 147968 148096, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (75 : ℕ) ∧
    (∑ n ∈ Ico 147968 148096, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (33833 : ℤ) ∧
    (∑ n ∈ Ico 147968 148096, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (676588280878337194654437262 : ℤ) := by
  rcases cdemPrefixStats_147968_148032 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_148032_148096 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 147968 ≤ 148032) (by norm_num : 148032 ≤ 148096), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 147968 ≤ 148032) (by norm_num : 148032 ≤ 148096), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 147968 ≤ 148032) (by norm_num : 148032 ≤ 148096), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 147968 ≤ 148032) (by norm_num : 148032 ≤ 148096), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_148096_148160 :
    (∑ n ∈ Ico 148096 148160, mobiusTreeValue 16 mobiusTable1200001 n) = (3 : ℤ) ∧
    (∑ n ∈ Ico 148096 148160, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 148096 148160, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (101289 : ℤ) ∧
    (∑ n ∈ Ico 148096 148160, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (2025795021064981775784895898 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_148160_148224 :
    (∑ n ∈ Ico 148160 148224, mobiusTreeValue 16 mobiusTable1200001 n) = (-3 : ℤ) ∧
    (∑ n ∈ Ico 148160 148224, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 148160 148224, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-101196 : ℤ) ∧
    (∑ n ∈ Ico 148160 148224, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-2023972684723955119945716998 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_148096_148224 :
    (∑ n ∈ Ico 148096 148224, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 148096 148224, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (80 : ℕ) ∧
    (∑ n ∈ Ico 148096 148224, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (93 : ℤ) ∧
    (∑ n ∈ Ico 148096 148224, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1822336341026655839178900 : ℤ) := by
  rcases cdemPrefixStats_148096_148160 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_148160_148224 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 148096 ≤ 148160) (by norm_num : 148160 ≤ 148224), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 148096 ≤ 148160) (by norm_num : 148160 ≤ 148224), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 148096 ≤ 148160) (by norm_num : 148160 ≤ 148224), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 148096 ≤ 148160) (by norm_num : 148160 ≤ 148224), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_147968_148224 :
    (∑ n ∈ Ico 147968 148224, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 147968 148224, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (155 : ℕ) ∧
    (∑ n ∈ Ico 147968 148224, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (33926 : ℤ) ∧
    (∑ n ∈ Ico 147968 148224, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (678410617219363850493616162 : ℤ) := by
  rcases cdemPrefixStats_147968_148096 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_148096_148224 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 147968 ≤ 148096) (by norm_num : 148096 ≤ 148224), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 147968 ≤ 148096) (by norm_num : 148096 ≤ 148224), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 147968 ≤ 148096) (by norm_num : 148096 ≤ 148224), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 147968 ≤ 148096) (by norm_num : 148096 ≤ 148224), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_148224_148288 :
    (∑ n ∈ Ico 148224 148288, mobiusTreeValue 16 mobiusTable1200001 n) = (4 : ℤ) ∧
    (∑ n ∈ Ico 148224 148288, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 148224 148288, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (134888 : ℤ) ∧
    (∑ n ∈ Ico 148224 148288, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (2697781121087287504680157488 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_148288_148352 :
    (∑ n ∈ Ico 148288 148352, mobiusTreeValue 16 mobiusTable1200001 n) = (8 : ℤ) ∧
    (∑ n ∈ Ico 148288 148352, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 148288 148352, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (269698 : ℤ) ∧
    (∑ n ∈ Ico 148288 148352, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (5394034331502727765459946105 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_148224_148352 :
    (∑ n ∈ Ico 148224 148352, mobiusTreeValue 16 mobiusTable1200001 n) = (12 : ℤ) ∧
    (∑ n ∈ Ico 148224 148352, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 148224 148352, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (404586 : ℤ) ∧
    (∑ n ∈ Ico 148224 148352, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (8091815452590015270140103593 : ℤ) := by
  rcases cdemPrefixStats_148224_148288 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_148288_148352 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 148224 ≤ 148288) (by norm_num : 148288 ≤ 148352), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 148224 ≤ 148288) (by norm_num : 148288 ≤ 148352), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 148224 ≤ 148288) (by norm_num : 148288 ≤ 148352), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 148224 ≤ 148288) (by norm_num : 148288 ≤ 148352), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_148352_148416 :
    (∑ n ∈ Ico 148352 148416, mobiusTreeValue 16 mobiusTable1200001 n) = (4 : ℤ) ∧
    (∑ n ∈ Ico 148352 148416, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 148352 148416, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (134809 : ℤ) ∧
    (∑ n ∈ Ico 148352 148416, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (2696230754636149759700098129 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_148416_148480 :
    (∑ n ∈ Ico 148416 148480, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 148416 148480, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 148416 148480, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-33658 : ℤ) ∧
    (∑ n ∈ Ico 148416 148480, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-673200917180094425197607655 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_148352_148480 :
    (∑ n ∈ Ico 148352 148480, mobiusTreeValue 16 mobiusTable1200001 n) = (3 : ℤ) ∧
    (∑ n ∈ Ico 148352 148480, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 148352 148480, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (101151 : ℤ) ∧
    (∑ n ∈ Ico 148352 148480, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (2023029837456055334502490474 : ℤ) := by
  rcases cdemPrefixStats_148352_148416 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_148416_148480 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 148352 ≤ 148416) (by norm_num : 148416 ≤ 148480), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 148352 ≤ 148416) (by norm_num : 148416 ≤ 148480), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 148352 ≤ 148416) (by norm_num : 148416 ≤ 148480), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 148352 ≤ 148416) (by norm_num : 148416 ≤ 148480), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_148224_148480 :
    (∑ n ∈ Ico 148224 148480, mobiusTreeValue 16 mobiusTable1200001 n) = (15 : ℤ) ∧
    (∑ n ∈ Ico 148224 148480, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (155 : ℕ) ∧
    (∑ n ∈ Ico 148224 148480, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (505737 : ℤ) ∧
    (∑ n ∈ Ico 148224 148480, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (10114845290046070604642594067 : ℤ) := by
  rcases cdemPrefixStats_148224_148352 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_148352_148480 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 148224 ≤ 148352) (by norm_num : 148352 ≤ 148480), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 148224 ≤ 148352) (by norm_num : 148352 ≤ 148480), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 148224 ≤ 148352) (by norm_num : 148352 ≤ 148480), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 148224 ≤ 148352) (by norm_num : 148352 ≤ 148480), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_147968_148480 :
    (∑ n ∈ Ico 147968 148480, mobiusTreeValue 16 mobiusTable1200001 n) = (16 : ℤ) ∧
    (∑ n ∈ Ico 147968 148480, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (310 : ℕ) ∧
    (∑ n ∈ Ico 147968 148480, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (539663 : ℤ) ∧
    (∑ n ∈ Ico 147968 148480, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (10793255907265434455136210229 : ℤ) := by
  rcases cdemPrefixStats_147968_148224 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_148224_148480 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 147968 ≤ 148224) (by norm_num : 148224 ≤ 148480), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 147968 ≤ 148224) (by norm_num : 148224 ≤ 148480), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 147968 ≤ 148224) (by norm_num : 148224 ≤ 148480), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 147968 ≤ 148224) (by norm_num : 148224 ≤ 148480), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_147456_148480 :
    (∑ n ∈ Ico 147456 148480, mobiusTreeValue 16 mobiusTable1200001 n) = (10 : ℤ) ∧
    (∑ n ∈ Ico 147456 148480, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (624 : ℕ) ∧
    (∑ n ∈ Ico 147456 148480, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (336440 : ℤ) ∧
    (∑ n ∈ Ico 147456 148480, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (6728705687512585479174593787 : ℤ) := by
  rcases cdemPrefixStats_147456_147968 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_147968_148480 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 147456 ≤ 147968) (by norm_num : 147968 ≤ 148480), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 147456 ≤ 147968) (by norm_num : 147968 ≤ 148480), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 147456 ≤ 147968) (by norm_num : 147968 ≤ 148480), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 147456 ≤ 147968) (by norm_num : 147968 ≤ 148480), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_148480_148544 :
    (∑ n ∈ Ico 148480 148544, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 148480 148544, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 148480 148544, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-6 : ℤ) ∧
    (∑ n ∈ Ico 148480 148544, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-86045105356211287346769 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_148544_148608 :
    (∑ n ∈ Ico 148544 148608, mobiusTreeValue 16 mobiusTable1200001 n) = (6 : ℤ) ∧
    (∑ n ∈ Ico 148544 148608, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 148544 148608, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (201908 : ℤ) ∧
    (∑ n ∈ Ico 148544 148608, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (4038219553101158202285120004 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_148480_148608 :
    (∑ n ∈ Ico 148480 148608, mobiusTreeValue 16 mobiusTable1200001 n) = (6 : ℤ) ∧
    (∑ n ∈ Ico 148480 148608, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 148480 148608, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (201902 : ℤ) ∧
    (∑ n ∈ Ico 148480 148608, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (4038133507995801990997773235 : ℤ) := by
  rcases cdemPrefixStats_148480_148544 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_148544_148608 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 148480 ≤ 148544) (by norm_num : 148544 ≤ 148608), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 148480 ≤ 148544) (by norm_num : 148544 ≤ 148608), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 148480 ≤ 148544) (by norm_num : 148544 ≤ 148608), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 148480 ≤ 148544) (by norm_num : 148544 ≤ 148608), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_148608_148672 :
    (∑ n ∈ Ico 148608 148672, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 148608 148672, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 148608 148672, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (15 : ℤ) ∧
    (∑ n ∈ Ico 148608 148672, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (361966522851977129606193 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_148672_148736 :
    (∑ n ∈ Ico 148672 148736, mobiusTreeValue 16 mobiusTable1200001 n) = (-2 : ℤ) ∧
    (∑ n ∈ Ico 148672 148736, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 148672 148736, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-67255 : ℤ) ∧
    (∑ n ∈ Ico 148672 148736, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-1345107570052166778496299891 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_148608_148736 :
    (∑ n ∈ Ico 148608 148736, mobiusTreeValue 16 mobiusTable1200001 n) = (-2 : ℤ) ∧
    (∑ n ∈ Ico 148608 148736, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 148608 148736, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-67240 : ℤ) ∧
    (∑ n ∈ Ico 148608 148736, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-1344745603529314801366693698 : ℤ) := by
  rcases cdemPrefixStats_148608_148672 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_148672_148736 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 148608 ≤ 148672) (by norm_num : 148672 ≤ 148736), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 148608 ≤ 148672) (by norm_num : 148672 ≤ 148736), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 148608 ≤ 148672) (by norm_num : 148672 ≤ 148736), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 148608 ≤ 148672) (by norm_num : 148672 ≤ 148736), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_148480_148736 :
    (∑ n ∈ Ico 148480 148736, mobiusTreeValue 16 mobiusTable1200001 n) = (4 : ℤ) ∧
    (∑ n ∈ Ico 148480 148736, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (156 : ℕ) ∧
    (∑ n ∈ Ico 148480 148736, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (134662 : ℤ) ∧
    (∑ n ∈ Ico 148480 148736, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (2693387904466487189631079537 : ℤ) := by
  rcases cdemPrefixStats_148480_148608 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_148608_148736 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 148480 ≤ 148608) (by norm_num : 148608 ≤ 148736), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 148480 ≤ 148608) (by norm_num : 148608 ≤ 148736), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 148480 ≤ 148608) (by norm_num : 148608 ≤ 148736), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 148480 ≤ 148608) (by norm_num : 148608 ≤ 148736), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_148736_148800 :
    (∑ n ∈ Ico 148736 148800, mobiusTreeValue 16 mobiusTable1200001 n) = (-7 : ℤ) ∧
    (∑ n ∈ Ico 148736 148800, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 148736 148800, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-235258 : ℤ) ∧
    (∑ n ∈ Ico 148736 148800, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-4705245318947568771555654106 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_148800_148864 :
    (∑ n ∈ Ico 148800 148864, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 148800 148864, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (35 : ℕ) ∧
    (∑ n ∈ Ico 148800 148864, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (33637 : ℤ) ∧
    (∑ n ∈ Ico 148800 148864, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (672684009537650805743979223 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_148736_148864 :
    (∑ n ∈ Ico 148736 148864, mobiusTreeValue 16 mobiusTable1200001 n) = (-6 : ℤ) ∧
    (∑ n ∈ Ico 148736 148864, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (76 : ℕ) ∧
    (∑ n ∈ Ico 148736 148864, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-201621 : ℤ) ∧
    (∑ n ∈ Ico 148736 148864, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-4032561309409917965811674883 : ℤ) := by
  rcases cdemPrefixStats_148736_148800 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_148800_148864 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 148736 ≤ 148800) (by norm_num : 148800 ≤ 148864), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 148736 ≤ 148800) (by norm_num : 148800 ≤ 148864), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 148736 ≤ 148800) (by norm_num : 148800 ≤ 148864), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 148736 ≤ 148800) (by norm_num : 148800 ≤ 148864), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_148864_148928 :
    (∑ n ∈ Ico 148864 148928, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 148864 148928, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 148864 148928, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-33569 : ℤ) ∧
    (∑ n ∈ Ico 148864 148928, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-671442873751063809444057026 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_148928_148992 :
    (∑ n ∈ Ico 148928 148992, mobiusTreeValue 16 mobiusTable1200001 n) = (-2 : ℤ) ∧
    (∑ n ∈ Ico 148928 148992, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 148928 148992, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-67143 : ℤ) ∧
    (∑ n ∈ Ico 148928 148992, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-1342903710945812815116225166 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_148864_148992 :
    (∑ n ∈ Ico 148864 148992, mobiusTreeValue 16 mobiusTable1200001 n) = (-3 : ℤ) ∧
    (∑ n ∈ Ico 148864 148992, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 148864 148992, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-100712 : ℤ) ∧
    (∑ n ∈ Ico 148864 148992, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-2014346584696876624560282192 : ℤ) := by
  rcases cdemPrefixStats_148864_148928 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_148928_148992 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 148864 ≤ 148928) (by norm_num : 148928 ≤ 148992), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 148864 ≤ 148928) (by norm_num : 148928 ≤ 148992), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 148864 ≤ 148928) (by norm_num : 148928 ≤ 148992), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 148864 ≤ 148928) (by norm_num : 148928 ≤ 148992), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_148736_148992 :
    (∑ n ∈ Ico 148736 148992, mobiusTreeValue 16 mobiusTable1200001 n) = (-9 : ℤ) ∧
    (∑ n ∈ Ico 148736 148992, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (153 : ℕ) ∧
    (∑ n ∈ Ico 148736 148992, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-302333 : ℤ) ∧
    (∑ n ∈ Ico 148736 148992, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-6046907894106794590371957075 : ℤ) := by
  rcases cdemPrefixStats_148736_148864 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_148864_148992 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 148736 ≤ 148864) (by norm_num : 148864 ≤ 148992), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 148736 ≤ 148864) (by norm_num : 148864 ≤ 148992), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 148736 ≤ 148864) (by norm_num : 148864 ≤ 148992), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 148736 ≤ 148864) (by norm_num : 148864 ≤ 148992), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_148480_148992 :
    (∑ n ∈ Ico 148480 148992, mobiusTreeValue 16 mobiusTable1200001 n) = (-5 : ℤ) ∧
    (∑ n ∈ Ico 148480 148992, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (309 : ℕ) ∧
    (∑ n ∈ Ico 148480 148992, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-167671 : ℤ) ∧
    (∑ n ∈ Ico 148480 148992, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-3353519989640307400740877538 : ℤ) := by
  rcases cdemPrefixStats_148480_148736 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_148736_148992 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 148480 ≤ 148736) (by norm_num : 148736 ≤ 148992), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 148480 ≤ 148736) (by norm_num : 148736 ≤ 148992), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 148480 ≤ 148736) (by norm_num : 148736 ≤ 148992), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 148480 ≤ 148736) (by norm_num : 148736 ≤ 148992), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_148992_149056 :
    (∑ n ∈ Ico 148992 149056, mobiusTreeValue 16 mobiusTable1200001 n) = (6 : ℤ) ∧
    (∑ n ∈ Ico 148992 149056, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 148992 149056, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (201331 : ℤ) ∧
    (∑ n ∈ Ico 148992 149056, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (4026692528012445541335860992 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_149056_149120 :
    (∑ n ∈ Ico 149056 149120, mobiusTreeValue 16 mobiusTable1200001 n) = (-10 : ℤ) ∧
    (∑ n ∈ Ico 149056 149120, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 149056 149120, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-335347 : ℤ) ∧
    (∑ n ∈ Ico 149056 149120, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-6706998220368817369102071823 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_148992_149120 :
    (∑ n ∈ Ico 148992 149120, mobiusTreeValue 16 mobiusTable1200001 n) = (-4 : ℤ) ∧
    (∑ n ∈ Ico 148992 149120, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (80 : ℕ) ∧
    (∑ n ∈ Ico 148992 149120, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-134016 : ℤ) ∧
    (∑ n ∈ Ico 148992 149120, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-2680305692356371827766210831 : ℤ) := by
  rcases cdemPrefixStats_148992_149056 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_149056_149120 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 148992 ≤ 149056) (by norm_num : 149056 ≤ 149120), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 148992 ≤ 149056) (by norm_num : 149056 ≤ 149120), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 148992 ≤ 149056) (by norm_num : 149056 ≤ 149120), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 148992 ≤ 149056) (by norm_num : 149056 ≤ 149120), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_149120_149184 :
    (∑ n ∈ Ico 149120 149184, mobiusTreeValue 16 mobiusTable1200001 n) = (-7 : ℤ) ∧
    (∑ n ∈ Ico 149120 149184, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 149120 149184, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-234642 : ℤ) ∧
    (∑ n ∈ Ico 149120 149184, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-4692897723435505709321296386 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_149184_149248 :
    (∑ n ∈ Ico 149184 149248, mobiusTreeValue 16 mobiusTable1200001 n) = (7 : ℤ) ∧
    (∑ n ∈ Ico 149184 149248, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 149184 149248, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (234544 : ℤ) ∧
    (∑ n ∈ Ico 149184 149248, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (4690956943078554748953404486 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_149120_149248 :
    (∑ n ∈ Ico 149120 149248, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 149120 149248, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (76 : ℕ) ∧
    (∑ n ∈ Ico 149120 149248, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-98 : ℤ) ∧
    (∑ n ∈ Ico 149120 149248, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-1940780356950960367891900 : ℤ) := by
  rcases cdemPrefixStats_149120_149184 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_149184_149248 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 149120 ≤ 149184) (by norm_num : 149184 ≤ 149248), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 149120 ≤ 149184) (by norm_num : 149184 ≤ 149248), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 149120 ≤ 149184) (by norm_num : 149184 ≤ 149248), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 149120 ≤ 149184) (by norm_num : 149184 ≤ 149248), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_148992_149248 :
    (∑ n ∈ Ico 148992 149248, mobiusTreeValue 16 mobiusTable1200001 n) = (-4 : ℤ) ∧
    (∑ n ∈ Ico 148992 149248, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (156 : ℕ) ∧
    (∑ n ∈ Ico 148992 149248, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-134114 : ℤ) ∧
    (∑ n ∈ Ico 148992 149248, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-2682246472713322788134102731 : ℤ) := by
  rcases cdemPrefixStats_148992_149120 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_149120_149248 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 148992 ≤ 149120) (by norm_num : 149120 ≤ 149248), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 148992 ≤ 149120) (by norm_num : 149120 ≤ 149248), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 148992 ≤ 149120) (by norm_num : 149120 ≤ 149248), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 148992 ≤ 149120) (by norm_num : 149120 ≤ 149248), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_149248_149312 :
    (∑ n ∈ Ico 149248 149312, mobiusTreeValue 16 mobiusTable1200001 n) = (-7 : ℤ) ∧
    (∑ n ∈ Ico 149248 149312, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 149248 149312, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-234463 : ℤ) ∧
    (∑ n ∈ Ico 149248 149312, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-4689340807655762551257060495 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_149312_149376 :
    (∑ n ∈ Ico 149312 149376, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 149312 149376, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 149312 149376, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-33506 : ℤ) ∧
    (∑ n ∈ Ico 149312 149376, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-670142044847775256278672257 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_149248_149376 :
    (∑ n ∈ Ico 149248 149376, mobiusTreeValue 16 mobiusTable1200001 n) = (-8 : ℤ) ∧
    (∑ n ∈ Ico 149248 149376, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 149248 149376, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-267969 : ℤ) ∧
    (∑ n ∈ Ico 149248 149376, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-5359482852503537807535732752 : ℤ) := by
  rcases cdemPrefixStats_149248_149312 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_149312_149376 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 149248 ≤ 149312) (by norm_num : 149312 ≤ 149376), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 149248 ≤ 149312) (by norm_num : 149312 ≤ 149376), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 149248 ≤ 149312) (by norm_num : 149312 ≤ 149376), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 149248 ≤ 149312) (by norm_num : 149312 ≤ 149376), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_149376_149440 :
    (∑ n ∈ Ico 149376 149440, mobiusTreeValue 16 mobiusTable1200001 n) = (5 : ℤ) ∧
    (∑ n ∈ Ico 149376 149440, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 149376 149440, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (167297 : ℤ) ∧
    (∑ n ∈ Ico 149376 149440, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (3346007943819991423026759045 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_149440_149504 :
    (∑ n ∈ Ico 149440 149504, mobiusTreeValue 16 mobiusTable1200001 n) = (-10 : ℤ) ∧
    (∑ n ∈ Ico 149440 149504, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 149440 149504, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-334491 : ℤ) ∧
    (∑ n ∈ Ico 149440 149504, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-6689988152737001107601906076 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_149376_149504 :
    (∑ n ∈ Ico 149376 149504, mobiusTreeValue 16 mobiusTable1200001 n) = (-5 : ℤ) ∧
    (∑ n ∈ Ico 149376 149504, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (79 : ℕ) ∧
    (∑ n ∈ Ico 149376 149504, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-167194 : ℤ) ∧
    (∑ n ∈ Ico 149376 149504, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-3343980208917009684575147031 : ℤ) := by
  rcases cdemPrefixStats_149376_149440 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_149440_149504 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 149376 ≤ 149440) (by norm_num : 149440 ≤ 149504), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 149376 ≤ 149440) (by norm_num : 149440 ≤ 149504), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 149376 ≤ 149440) (by norm_num : 149440 ≤ 149504), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 149376 ≤ 149440) (by norm_num : 149440 ≤ 149504), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_149248_149504 :
    (∑ n ∈ Ico 149248 149504, mobiusTreeValue 16 mobiusTable1200001 n) = (-13 : ℤ) ∧
    (∑ n ∈ Ico 149248 149504, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (157 : ℕ) ∧
    (∑ n ∈ Ico 149248 149504, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-435163 : ℤ) ∧
    (∑ n ∈ Ico 149248 149504, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-8703463061420547492110879783 : ℤ) := by
  rcases cdemPrefixStats_149248_149376 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_149376_149504 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 149248 ≤ 149376) (by norm_num : 149376 ≤ 149504), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 149248 ≤ 149376) (by norm_num : 149376 ≤ 149504), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 149248 ≤ 149376) (by norm_num : 149376 ≤ 149504), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 149248 ≤ 149376) (by norm_num : 149376 ≤ 149504), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_148992_149504 :
    (∑ n ∈ Ico 148992 149504, mobiusTreeValue 16 mobiusTable1200001 n) = (-17 : ℤ) ∧
    (∑ n ∈ Ico 148992 149504, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (313 : ℕ) ∧
    (∑ n ∈ Ico 148992 149504, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-569277 : ℤ) ∧
    (∑ n ∈ Ico 148992 149504, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-11385709534133870280244982514 : ℤ) := by
  rcases cdemPrefixStats_148992_149248 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_149248_149504 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 148992 ≤ 149248) (by norm_num : 149248 ≤ 149504), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 148992 ≤ 149248) (by norm_num : 149248 ≤ 149504), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 148992 ≤ 149248) (by norm_num : 149248 ≤ 149504), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 148992 ≤ 149248) (by norm_num : 149248 ≤ 149504), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_148480_149504 :
    (∑ n ∈ Ico 148480 149504, mobiusTreeValue 16 mobiusTable1200001 n) = (-22 : ℤ) ∧
    (∑ n ∈ Ico 148480 149504, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (622 : ℕ) ∧
    (∑ n ∈ Ico 148480 149504, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-736948 : ℤ) ∧
    (∑ n ∈ Ico 148480 149504, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-14739229523774177680985860052 : ℤ) := by
  rcases cdemPrefixStats_148480_148992 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_148992_149504 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 148480 ≤ 148992) (by norm_num : 148992 ≤ 149504), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 148480 ≤ 148992) (by norm_num : 148992 ≤ 149504), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 148480 ≤ 148992) (by norm_num : 148992 ≤ 149504), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 148480 ≤ 148992) (by norm_num : 148992 ≤ 149504), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_147456_149504 :
    (∑ n ∈ Ico 147456 149504, mobiusTreeValue 16 mobiusTable1200001 n) = (-12 : ℤ) ∧
    (∑ n ∈ Ico 147456 149504, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (1246 : ℕ) ∧
    (∑ n ∈ Ico 147456 149504, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-400508 : ℤ) ∧
    (∑ n ∈ Ico 147456 149504, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-8010523836261592201811266265 : ℤ) := by
  rcases cdemPrefixStats_147456_148480 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_148480_149504 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 147456 ≤ 148480) (by norm_num : 148480 ≤ 149504), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 147456 ≤ 148480) (by norm_num : 148480 ≤ 149504), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 147456 ≤ 148480) (by norm_num : 148480 ≤ 149504), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 147456 ≤ 148480) (by norm_num : 148480 ≤ 149504), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_149504_149568 :
    (∑ n ∈ Ico 149504 149568, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 149504 149568, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 149504 149568, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (8 : ℤ) ∧
    (∑ n ∈ Ico 149504 149568, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (147650254601106880825696 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_149568_149632 :
    (∑ n ∈ Ico 149568 149632, mobiusTreeValue 16 mobiusTable1200001 n) = (2 : ℤ) ∧
    (∑ n ∈ Ico 149568 149632, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 149568 149632, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (66862 : ℤ) ∧
    (∑ n ∈ Ico 149568 149632, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1337278169730590200225625041 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_149504_149632 :
    (∑ n ∈ Ico 149504 149632, mobiusTreeValue 16 mobiusTable1200001 n) = (2 : ℤ) ∧
    (∑ n ∈ Ico 149504 149632, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (80 : ℕ) ∧
    (∑ n ∈ Ico 149504 149632, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (66870 : ℤ) ∧
    (∑ n ∈ Ico 149504 149632, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1337425819985191307106450737 : ℤ) := by
  rcases cdemPrefixStats_149504_149568 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_149568_149632 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 149504 ≤ 149568) (by norm_num : 149568 ≤ 149632), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 149504 ≤ 149568) (by norm_num : 149568 ≤ 149632), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 149504 ≤ 149568) (by norm_num : 149568 ≤ 149632), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 149504 ≤ 149568) (by norm_num : 149568 ≤ 149632), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_149632_149696 :
    (∑ n ∈ Ico 149632 149696, mobiusTreeValue 16 mobiusTable1200001 n) = (6 : ℤ) ∧
    (∑ n ∈ Ico 149632 149696, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (36 : ℕ) ∧
    (∑ n ∈ Ico 149632 149696, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (200456 : ℤ) ∧
    (∑ n ∈ Ico 149632 149696, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (4009167669410142771292834772 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_149696_149760 :
    (∑ n ∈ Ico 149696 149760, mobiusTreeValue 16 mobiusTable1200001 n) = (2 : ℤ) ∧
    (∑ n ∈ Ico 149696 149760, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (36 : ℕ) ∧
    (∑ n ∈ Ico 149696 149760, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (66745 : ℤ) ∧
    (∑ n ∈ Ico 149696 149760, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1334979347807094798985063841 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_149632_149760 :
    (∑ n ∈ Ico 149632 149760, mobiusTreeValue 16 mobiusTable1200001 n) = (8 : ℤ) ∧
    (∑ n ∈ Ico 149632 149760, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (72 : ℕ) ∧
    (∑ n ∈ Ico 149632 149760, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (267201 : ℤ) ∧
    (∑ n ∈ Ico 149632 149760, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (5344147017217237570277898613 : ℤ) := by
  rcases cdemPrefixStats_149632_149696 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_149696_149760 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 149632 ≤ 149696) (by norm_num : 149696 ≤ 149760), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 149632 ≤ 149696) (by norm_num : 149696 ≤ 149760), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 149632 ≤ 149696) (by norm_num : 149696 ≤ 149760), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 149632 ≤ 149696) (by norm_num : 149696 ≤ 149760), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_149504_149760 :
    (∑ n ∈ Ico 149504 149760, mobiusTreeValue 16 mobiusTable1200001 n) = (10 : ℤ) ∧
    (∑ n ∈ Ico 149504 149760, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (152 : ℕ) ∧
    (∑ n ∈ Ico 149504 149760, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (334071 : ℤ) ∧
    (∑ n ∈ Ico 149504 149760, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (6681572837202428877384349350 : ℤ) := by
  rcases cdemPrefixStats_149504_149632 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_149632_149760 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 149504 ≤ 149632) (by norm_num : 149632 ≤ 149760), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 149504 ≤ 149632) (by norm_num : 149632 ≤ 149760), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 149504 ≤ 149632) (by norm_num : 149632 ≤ 149760), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 149504 ≤ 149632) (by norm_num : 149632 ≤ 149760), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_149760_149824 :
    (∑ n ∈ Ico 149760 149824, mobiusTreeValue 16 mobiusTable1200001 n) = (16 : ℤ) ∧
    (∑ n ∈ Ico 149760 149824, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 149760 149824, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (534075 : ℤ) ∧
    (∑ n ∈ Ico 149760 149824, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (10681670051165510214504938062 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_149824_149888 :
    (∑ n ∈ Ico 149824 149888, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 149824 149888, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 149824 149888, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-26 : ℤ) ∧
    (∑ n ∈ Ico 149824 149888, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-556682762137426466481228 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_149760_149888 :
    (∑ n ∈ Ico 149760 149888, mobiusTreeValue 16 mobiusTable1200001 n) = (16 : ℤ) ∧
    (∑ n ∈ Ico 149760 149888, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 149760 149888, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (534049 : ℤ) ∧
    (∑ n ∈ Ico 149760 149888, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (10681113368403372788038456834 : ℤ) := by
  rcases cdemPrefixStats_149760_149824 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_149824_149888 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 149760 ≤ 149824) (by norm_num : 149824 ≤ 149888), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 149760 ≤ 149824) (by norm_num : 149824 ≤ 149888), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 149760 ≤ 149824) (by norm_num : 149824 ≤ 149888), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 149760 ≤ 149824) (by norm_num : 149824 ≤ 149888), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_149888_149952 :
    (∑ n ∈ Ico 149888 149952, mobiusTreeValue 16 mobiusTable1200001 n) = (-12 : ℤ) ∧
    (∑ n ∈ Ico 149888 149952, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 149888 149952, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-400245 : ℤ) ∧
    (∑ n ∈ Ico 149888 149952, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-8004980908598750119899068154 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_149952_150016 :
    (∑ n ∈ Ico 149952 150016, mobiusTreeValue 16 mobiusTable1200001 n) = (2 : ℤ) ∧
    (∑ n ∈ Ico 149952 150016, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 149952 150016, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (66697 : ℤ) ∧
    (∑ n ∈ Ico 149952 150016, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1333840075922145597377713479 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_149888_150016 :
    (∑ n ∈ Ico 149888 150016, mobiusTreeValue 16 mobiusTable1200001 n) = (-10 : ℤ) ∧
    (∑ n ∈ Ico 149888 150016, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 149888 150016, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-333548 : ℤ) ∧
    (∑ n ∈ Ico 149888 150016, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-6671140832676604522521354675 : ℤ) := by
  rcases cdemPrefixStats_149888_149952 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_149952_150016 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 149888 ≤ 149952) (by norm_num : 149952 ≤ 150016), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 149888 ≤ 149952) (by norm_num : 149952 ≤ 150016), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 149888 ≤ 149952) (by norm_num : 149952 ≤ 150016), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 149888 ≤ 149952) (by norm_num : 149952 ≤ 150016), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_149760_150016 :
    (∑ n ∈ Ico 149760 150016, mobiusTreeValue 16 mobiusTable1200001 n) = (6 : ℤ) ∧
    (∑ n ∈ Ico 149760 150016, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (156 : ℕ) ∧
    (∑ n ∈ Ico 149760 150016, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (200501 : ℤ) ∧
    (∑ n ∈ Ico 149760 150016, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (4009972535726768265517102159 : ℤ) := by
  rcases cdemPrefixStats_149760_149888 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_149888_150016 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 149760 ≤ 149888) (by norm_num : 149888 ≤ 150016), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 149760 ≤ 149888) (by norm_num : 149888 ≤ 150016), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 149760 ≤ 149888) (by norm_num : 149888 ≤ 150016), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 149760 ≤ 149888) (by norm_num : 149888 ≤ 150016), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_149504_150016 :
    (∑ n ∈ Ico 149504 150016, mobiusTreeValue 16 mobiusTable1200001 n) = (16 : ℤ) ∧
    (∑ n ∈ Ico 149504 150016, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (308 : ℕ) ∧
    (∑ n ∈ Ico 149504 150016, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (534572 : ℤ) ∧
    (∑ n ∈ Ico 149504 150016, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (10691545372929197142901451509 : ℤ) := by
  rcases cdemPrefixStats_149504_149760 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_149760_150016 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 149504 ≤ 149760) (by norm_num : 149760 ≤ 150016), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 149504 ≤ 149760) (by norm_num : 149760 ≤ 150016), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 149504 ≤ 149760) (by norm_num : 149760 ≤ 150016), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 149504 ≤ 149760) (by norm_num : 149760 ≤ 150016), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_150016_150080 :
    (∑ n ∈ Ico 150016 150080, mobiusTreeValue 16 mobiusTable1200001 n) = (9 : ℤ) ∧
    (∑ n ∈ Ico 150016 150080, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 150016 150080, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (299909 : ℤ) ∧
    (∑ n ∈ Ico 150016 150080, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (5998262781175284156520934681 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_150080_150144 :
    (∑ n ∈ Ico 150080 150144, mobiusTreeValue 16 mobiusTable1200001 n) = (-9 : ℤ) ∧
    (∑ n ∈ Ico 150080 150144, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 150080 150144, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-299775 : ℤ) ∧
    (∑ n ∈ Ico 150080 150144, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-5995607792823534350750935514 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_150016_150144 :
    (∑ n ∈ Ico 150016 150144, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 150016 150144, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (80 : ℕ) ∧
    (∑ n ∈ Ico 150016 150144, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (134 : ℤ) ∧
    (∑ n ∈ Ico 150016 150144, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (2654988351749805769999167 : ℤ) := by
  rcases cdemPrefixStats_150016_150080 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_150080_150144 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 150016 ≤ 150080) (by norm_num : 150080 ≤ 150144), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 150016 ≤ 150080) (by norm_num : 150080 ≤ 150144), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 150016 ≤ 150080) (by norm_num : 150080 ≤ 150144), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 150016 ≤ 150080) (by norm_num : 150080 ≤ 150144), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_150144_150208 :
    (∑ n ∈ Ico 150144 150208, mobiusTreeValue 16 mobiusTable1200001 n) = (-3 : ℤ) ∧
    (∑ n ∈ Ico 150144 150208, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 150144 150208, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-99845 : ℤ) ∧
    (∑ n ∈ Ico 150144 150208, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-1996951146677645249988634620 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_150208_150272 :
    (∑ n ∈ Ico 150208 150272, mobiusTreeValue 16 mobiusTable1200001 n) = (-5 : ℤ) ∧
    (∑ n ∈ Ico 150208 150272, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 150208 150272, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-166415 : ℤ) ∧
    (∑ n ∈ Ico 150208 150272, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-3328376280672664796080672788 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_150144_150272 :
    (∑ n ∈ Ico 150144 150272, mobiusTreeValue 16 mobiusTable1200001 n) = (-8 : ℤ) ∧
    (∑ n ∈ Ico 150144 150272, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 150144 150272, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-266260 : ℤ) ∧
    (∑ n ∈ Ico 150144 150272, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-5325327427350310046069307408 : ℤ) := by
  rcases cdemPrefixStats_150144_150208 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_150208_150272 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 150144 ≤ 150208) (by norm_num : 150208 ≤ 150272), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 150144 ≤ 150208) (by norm_num : 150208 ≤ 150272), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 150144 ≤ 150208) (by norm_num : 150208 ≤ 150272), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 150144 ≤ 150208) (by norm_num : 150208 ≤ 150272), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_150016_150272 :
    (∑ n ∈ Ico 150016 150272, mobiusTreeValue 16 mobiusTable1200001 n) = (-8 : ℤ) ∧
    (∑ n ∈ Ico 150016 150272, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (158 : ℕ) ∧
    (∑ n ∈ Ico 150016 150272, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-266126 : ℤ) ∧
    (∑ n ∈ Ico 150016 150272, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-5322672438998560240299308241 : ℤ) := by
  rcases cdemPrefixStats_150016_150144 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_150144_150272 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 150016 ≤ 150144) (by norm_num : 150144 ≤ 150272), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 150016 ≤ 150144) (by norm_num : 150144 ≤ 150272), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 150016 ≤ 150144) (by norm_num : 150144 ≤ 150272), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 150016 ≤ 150144) (by norm_num : 150144 ≤ 150272), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_150272_150336 :
    (∑ n ∈ Ico 150272 150336, mobiusTreeValue 16 mobiusTable1200001 n) = (-5 : ℤ) ∧
    (∑ n ∈ Ico 150272 150336, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 150272 150336, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-166312 : ℤ) ∧
    (∑ n ∈ Ico 150272 150336, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-3326303736623931696396861047 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_150336_150400 :
    (∑ n ∈ Ico 150336 150400, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 150336 150400, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 150336 150400, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-2 : ℤ) ∧
    (∑ n ∈ Ico 150336 150400, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-31072347439985772335530 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_150272_150400 :
    (∑ n ∈ Ico 150272 150400, mobiusTreeValue 16 mobiusTable1200001 n) = (-5 : ℤ) ∧
    (∑ n ∈ Ico 150272 150400, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (79 : ℕ) ∧
    (∑ n ∈ Ico 150272 150400, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-166314 : ℤ) ∧
    (∑ n ∈ Ico 150272 150400, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-3326334808971371682169196577 : ℤ) := by
  rcases cdemPrefixStats_150272_150336 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_150336_150400 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 150272 ≤ 150336) (by norm_num : 150336 ≤ 150400), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 150272 ≤ 150336) (by norm_num : 150336 ≤ 150400), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 150272 ≤ 150336) (by norm_num : 150336 ≤ 150400), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 150272 ≤ 150336) (by norm_num : 150336 ≤ 150400), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_150400_150464 :
    (∑ n ∈ Ico 150400 150464, mobiusTreeValue 16 mobiusTable1200001 n) = (8 : ℤ) ∧
    (∑ n ∈ Ico 150400 150464, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 150400 150464, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (265835 : ℤ) ∧
    (∑ n ∈ Ico 150400 150464, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (5316793523738226014632901972 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_150464_150528 :
    (∑ n ∈ Ico 150464 150528, mobiusTreeValue 16 mobiusTable1200001 n) = (6 : ℤ) ∧
    (∑ n ∈ Ico 150464 150528, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 150464 150528, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (199364 : ℤ) ∧
    (∑ n ∈ Ico 150464 150528, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (3987324697703956139844304376 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_150400_150528 :
    (∑ n ∈ Ico 150400 150528, mobiusTreeValue 16 mobiusTable1200001 n) = (14 : ℤ) ∧
    (∑ n ∈ Ico 150400 150528, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 150400 150528, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (465199 : ℤ) ∧
    (∑ n ∈ Ico 150400 150528, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (9304118221442182154477206348 : ℤ) := by
  rcases cdemPrefixStats_150400_150464 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_150464_150528 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 150400 ≤ 150464) (by norm_num : 150464 ≤ 150528), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 150400 ≤ 150464) (by norm_num : 150464 ≤ 150528), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 150400 ≤ 150464) (by norm_num : 150464 ≤ 150528), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 150400 ≤ 150464) (by norm_num : 150464 ≤ 150528), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_150272_150528 :
    (∑ n ∈ Ico 150272 150528, mobiusTreeValue 16 mobiusTable1200001 n) = (9 : ℤ) ∧
    (∑ n ∈ Ico 150272 150528, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (157 : ℕ) ∧
    (∑ n ∈ Ico 150272 150528, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (298885 : ℤ) ∧
    (∑ n ∈ Ico 150272 150528, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (5977783412470810472308009771 : ℤ) := by
  rcases cdemPrefixStats_150272_150400 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_150400_150528 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 150272 ≤ 150400) (by norm_num : 150400 ≤ 150528), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 150272 ≤ 150400) (by norm_num : 150400 ≤ 150528), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 150272 ≤ 150400) (by norm_num : 150400 ≤ 150528), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 150272 ≤ 150400) (by norm_num : 150400 ≤ 150528), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_150016_150528 :
    (∑ n ∈ Ico 150016 150528, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 150016 150528, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (315 : ℕ) ∧
    (∑ n ∈ Ico 150016 150528, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (32759 : ℤ) ∧
    (∑ n ∈ Ico 150016 150528, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (655110973472250232008701530 : ℤ) := by
  rcases cdemPrefixStats_150016_150272 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_150272_150528 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 150016 ≤ 150272) (by norm_num : 150272 ≤ 150528), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 150016 ≤ 150272) (by norm_num : 150272 ≤ 150528), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 150016 ≤ 150272) (by norm_num : 150272 ≤ 150528), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 150016 ≤ 150272) (by norm_num : 150272 ≤ 150528), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_149504_150528 :
    (∑ n ∈ Ico 149504 150528, mobiusTreeValue 16 mobiusTable1200001 n) = (17 : ℤ) ∧
    (∑ n ∈ Ico 149504 150528, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (623 : ℕ) ∧
    (∑ n ∈ Ico 149504 150528, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (567331 : ℤ) ∧
    (∑ n ∈ Ico 149504 150528, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (11346656346401447374910153039 : ℤ) := by
  rcases cdemPrefixStats_149504_150016 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_150016_150528 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 149504 ≤ 150016) (by norm_num : 150016 ≤ 150528), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 149504 ≤ 150016) (by norm_num : 150016 ≤ 150528), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 149504 ≤ 150016) (by norm_num : 150016 ≤ 150528), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 149504 ≤ 150016) (by norm_num : 150016 ≤ 150528), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_150528_150592 :
    (∑ n ∈ Ico 150528 150592, mobiusTreeValue 16 mobiusTable1200001 n) = (-4 : ℤ) ∧
    (∑ n ∈ Ico 150528 150592, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (36 : ℕ) ∧
    (∑ n ∈ Ico 150528 150592, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-132806 : ℤ) ∧
    (∑ n ∈ Ico 150528 150592, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-2656201141466704134275770807 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_150592_150656 :
    (∑ n ∈ Ico 150592 150656, mobiusTreeValue 16 mobiusTable1200001 n) = (8 : ℤ) ∧
    (∑ n ∈ Ico 150592 150656, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 150592 150656, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (265578 : ℤ) ∧
    (∑ n ∈ Ico 150592 150656, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (5311635365456522777802847064 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_150528_150656 :
    (∑ n ∈ Ico 150528 150656, mobiusTreeValue 16 mobiusTable1200001 n) = (4 : ℤ) ∧
    (∑ n ∈ Ico 150528 150656, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (74 : ℕ) ∧
    (∑ n ∈ Ico 150528 150656, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (132772 : ℤ) ∧
    (∑ n ∈ Ico 150528 150656, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (2655434223989818643527076257 : ℤ) := by
  rcases cdemPrefixStats_150528_150592 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_150592_150656 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 150528 ≤ 150592) (by norm_num : 150592 ≤ 150656), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 150528 ≤ 150592) (by norm_num : 150592 ≤ 150656), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 150528 ≤ 150592) (by norm_num : 150592 ≤ 150656), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 150528 ≤ 150592) (by norm_num : 150592 ≤ 150656), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_150656_150720 :
    (∑ n ∈ Ico 150656 150720, mobiusTreeValue 16 mobiusTable1200001 n) = (10 : ℤ) ∧
    (∑ n ∈ Ico 150656 150720, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (42 : ℕ) ∧
    (∑ n ∈ Ico 150656 150720, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (331824 : ℤ) ∧
    (∑ n ∈ Ico 150656 150720, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (6636572018931258200427999636 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_150720_150784 :
    (∑ n ∈ Ico 150720 150784, mobiusTreeValue 16 mobiusTable1200001 n) = (-2 : ℤ) ∧
    (∑ n ∈ Ico 150720 150784, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 150720 150784, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-66365 : ℤ) ∧
    (∑ n ∈ Ico 150720 150784, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-1327324690084928542212987285 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_150656_150784 :
    (∑ n ∈ Ico 150656 150784, mobiusTreeValue 16 mobiusTable1200001 n) = (8 : ℤ) ∧
    (∑ n ∈ Ico 150656 150784, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (80 : ℕ) ∧
    (∑ n ∈ Ico 150656 150784, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (265459 : ℤ) ∧
    (∑ n ∈ Ico 150656 150784, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (5309247328846329658215012351 : ℤ) := by
  rcases cdemPrefixStats_150656_150720 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_150720_150784 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 150656 ≤ 150720) (by norm_num : 150720 ≤ 150784), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 150656 ≤ 150720) (by norm_num : 150720 ≤ 150784), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 150656 ≤ 150720) (by norm_num : 150720 ≤ 150784), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 150656 ≤ 150720) (by norm_num : 150720 ≤ 150784), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_150528_150784 :
    (∑ n ∈ Ico 150528 150784, mobiusTreeValue 16 mobiusTable1200001 n) = (12 : ℤ) ∧
    (∑ n ∈ Ico 150528 150784, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (154 : ℕ) ∧
    (∑ n ∈ Ico 150528 150784, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (398231 : ℤ) ∧
    (∑ n ∈ Ico 150528 150784, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (7964681552836148301742088608 : ℤ) := by
  rcases cdemPrefixStats_150528_150656 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_150656_150784 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 150528 ≤ 150656) (by norm_num : 150656 ≤ 150784), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 150528 ≤ 150656) (by norm_num : 150656 ≤ 150784), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 150528 ≤ 150656) (by norm_num : 150656 ≤ 150784), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 150528 ≤ 150656) (by norm_num : 150656 ≤ 150784), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_150784_150848 :
    (∑ n ∈ Ico 150784 150848, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 150784 150848, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (42 : ℕ) ∧
    (∑ n ∈ Ico 150784 150848, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (34 : ℤ) ∧
    (∑ n ∈ Ico 150784 150848, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (668204424474403496466320 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_150848_150912 :
    (∑ n ∈ Ico 150848 150912, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 150848 150912, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (36 : ℕ) ∧
    (∑ n ∈ Ico 150848 150912, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (26 : ℤ) ∧
    (∑ n ∈ Ico 150848 150912, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (509635418004089051371177 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_150784_150912 :
    (∑ n ∈ Ico 150784 150912, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 150784 150912, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 150784 150912, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (60 : ℤ) ∧
    (∑ n ∈ Ico 150784 150912, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1177839842478492547837497 : ℤ) := by
  rcases cdemPrefixStats_150784_150848 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_150848_150912 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 150784 ≤ 150848) (by norm_num : 150848 ≤ 150912), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 150784 ≤ 150848) (by norm_num : 150848 ≤ 150912), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 150784 ≤ 150848) (by norm_num : 150848 ≤ 150912), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 150784 ≤ 150848) (by norm_num : 150848 ≤ 150912), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_150912_150976 :
    (∑ n ∈ Ico 150912 150976, mobiusTreeValue 16 mobiusTable1200001 n) = (6 : ℤ) ∧
    (∑ n ∈ Ico 150912 150976, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 150912 150976, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (198702 : ℤ) ∧
    (∑ n ∈ Ico 150912 150976, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (3974180931549581278519478865 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_150976_151040 :
    (∑ n ∈ Ico 150976 151040, mobiusTreeValue 16 mobiusTable1200001 n) = (-3 : ℤ) ∧
    (∑ n ∈ Ico 150976 151040, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 150976 151040, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-99387 : ℤ) ∧
    (∑ n ∈ Ico 150976 151040, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-1987833763406430147350126451 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_150912_151040 :
    (∑ n ∈ Ico 150912 151040, mobiusTreeValue 16 mobiusTable1200001 n) = (3 : ℤ) ∧
    (∑ n ∈ Ico 150912 151040, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (79 : ℕ) ∧
    (∑ n ∈ Ico 150912 151040, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (99315 : ℤ) ∧
    (∑ n ∈ Ico 150912 151040, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1986347168143151131169352414 : ℤ) := by
  rcases cdemPrefixStats_150912_150976 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_150976_151040 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 150912 ≤ 150976) (by norm_num : 150976 ≤ 151040), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 150912 ≤ 150976) (by norm_num : 150976 ≤ 151040), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 150912 ≤ 150976) (by norm_num : 150976 ≤ 151040), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 150912 ≤ 150976) (by norm_num : 150976 ≤ 151040), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_150784_151040 :
    (∑ n ∈ Ico 150784 151040, mobiusTreeValue 16 mobiusTable1200001 n) = (3 : ℤ) ∧
    (∑ n ∈ Ico 150784 151040, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (157 : ℕ) ∧
    (∑ n ∈ Ico 150784 151040, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (99375 : ℤ) ∧
    (∑ n ∈ Ico 150784 151040, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1987525007985629623717189911 : ℤ) := by
  rcases cdemPrefixStats_150784_150912 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_150912_151040 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 150784 ≤ 150912) (by norm_num : 150912 ≤ 151040), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 150784 ≤ 150912) (by norm_num : 150912 ≤ 151040), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 150784 ≤ 150912) (by norm_num : 150912 ≤ 151040), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 150784 ≤ 150912) (by norm_num : 150912 ≤ 151040), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_150528_151040 :
    (∑ n ∈ Ico 150528 151040, mobiusTreeValue 16 mobiusTable1200001 n) = (15 : ℤ) ∧
    (∑ n ∈ Ico 150528 151040, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (311 : ℕ) ∧
    (∑ n ∈ Ico 150528 151040, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (497606 : ℤ) ∧
    (∑ n ∈ Ico 150528 151040, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (9952206560821777925459278519 : ℤ) := by
  rcases cdemPrefixStats_150528_150784 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_150784_151040 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 150528 ≤ 150784) (by norm_num : 150784 ≤ 151040), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 150528 ≤ 150784) (by norm_num : 150784 ≤ 151040), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 150528 ≤ 150784) (by norm_num : 150784 ≤ 151040), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 150528 ≤ 150784) (by norm_num : 150784 ≤ 151040), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_151040_151104 :
    (∑ n ∈ Ico 151040 151104, mobiusTreeValue 16 mobiusTable1200001 n) = (7 : ℤ) ∧
    (∑ n ∈ Ico 151040 151104, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 151040 151104, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (231647 : ℤ) ∧
    (∑ n ∈ Ico 151040 151104, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (4632965152890130543684989136 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_151104_151168 :
    (∑ n ∈ Ico 151104 151168, mobiusTreeValue 16 mobiusTable1200001 n) = (6 : ℤ) ∧
    (∑ n ∈ Ico 151104 151168, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 151104 151168, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (198522 : ℤ) ∧
    (∑ n ∈ Ico 151104 151168, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (3970577974011003748814016353 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_151040_151168 :
    (∑ n ∈ Ico 151040 151168, mobiusTreeValue 16 mobiusTable1200001 n) = (13 : ℤ) ∧
    (∑ n ∈ Ico 151040 151168, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 151040 151168, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (430169 : ℤ) ∧
    (∑ n ∈ Ico 151040 151168, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (8603543126901134292499005489 : ℤ) := by
  rcases cdemPrefixStats_151040_151104 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_151104_151168 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 151040 ≤ 151104) (by norm_num : 151104 ≤ 151168), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 151040 ≤ 151104) (by norm_num : 151104 ≤ 151168), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 151040 ≤ 151104) (by norm_num : 151104 ≤ 151168), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 151040 ≤ 151104) (by norm_num : 151104 ≤ 151168), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_151168_151232 :
    (∑ n ∈ Ico 151168 151232, mobiusTreeValue 16 mobiusTable1200001 n) = (-2 : ℤ) ∧
    (∑ n ∈ Ico 151168 151232, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 151168 151232, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-66172 : ℤ) ∧
    (∑ n ∈ Ico 151168 151232, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-1323459947191564187843308593 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_151232_151296 :
    (∑ n ∈ Ico 151232 151296, mobiusTreeValue 16 mobiusTable1200001 n) = (2 : ℤ) ∧
    (∑ n ∈ Ico 151232 151296, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 151232 151296, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (66103 : ℤ) ∧
    (∑ n ∈ Ico 151232 151296, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1322051830442659632773178462 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_151168_151296 :
    (∑ n ∈ Ico 151168 151296, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 151168 151296, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (76 : ℕ) ∧
    (∑ n ∈ Ico 151168 151296, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-69 : ℤ) ∧
    (∑ n ∈ Ico 151168 151296, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-1408116748904555070130131 : ℤ) := by
  rcases cdemPrefixStats_151168_151232 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_151232_151296 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 151168 ≤ 151232) (by norm_num : 151232 ≤ 151296), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 151168 ≤ 151232) (by norm_num : 151232 ≤ 151296), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 151168 ≤ 151232) (by norm_num : 151232 ≤ 151296), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 151168 ≤ 151232) (by norm_num : 151232 ≤ 151296), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_151040_151296 :
    (∑ n ∈ Ico 151040 151296, mobiusTreeValue 16 mobiusTable1200001 n) = (13 : ℤ) ∧
    (∑ n ∈ Ico 151040 151296, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (153 : ℕ) ∧
    (∑ n ∈ Ico 151040 151296, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (430100 : ℤ) ∧
    (∑ n ∈ Ico 151040 151296, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (8602135010152229737428875358 : ℤ) := by
  rcases cdemPrefixStats_151040_151168 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_151168_151296 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 151040 ≤ 151168) (by norm_num : 151168 ≤ 151296), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 151040 ≤ 151168) (by norm_num : 151168 ≤ 151296), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 151040 ≤ 151168) (by norm_num : 151168 ≤ 151296), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 151040 ≤ 151168) (by norm_num : 151168 ≤ 151296), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_151296_151360 :
    (∑ n ∈ Ico 151296 151360, mobiusTreeValue 16 mobiusTable1200001 n) = (-2 : ℤ) ∧
    (∑ n ∈ Ico 151296 151360, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 151296 151360, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-66053 : ℤ) ∧
    (∑ n ∈ Ico 151296 151360, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-1321125898851875998543338777 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_151360_151424 :
    (∑ n ∈ Ico 151360 151424, mobiusTreeValue 16 mobiusTable1200001 n) = (-4 : ℤ) ∧
    (∑ n ∈ Ico 151360 151424, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 151360 151424, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-132065 : ℤ) ∧
    (∑ n ∈ Ico 151360 151424, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-2641349141268588893548741267 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_151296_151424 :
    (∑ n ∈ Ico 151296 151424, mobiusTreeValue 16 mobiusTable1200001 n) = (-6 : ℤ) ∧
    (∑ n ∈ Ico 151296 151424, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (80 : ℕ) ∧
    (∑ n ∈ Ico 151296 151424, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-198118 : ℤ) ∧
    (∑ n ∈ Ico 151296 151424, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-3962475040120464892092080044 : ℤ) := by
  rcases cdemPrefixStats_151296_151360 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_151360_151424 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 151296 ≤ 151360) (by norm_num : 151360 ≤ 151424), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 151296 ≤ 151360) (by norm_num : 151360 ≤ 151424), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 151296 ≤ 151360) (by norm_num : 151360 ≤ 151424), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 151296 ≤ 151360) (by norm_num : 151360 ≤ 151424), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_151424_151488 :
    (∑ n ∈ Ico 151424 151488, mobiusTreeValue 16 mobiusTable1200001 n) = (-3 : ℤ) ∧
    (∑ n ∈ Ico 151424 151488, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 151424 151488, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-99019 : ℤ) ∧
    (∑ n ∈ Ico 151424 151488, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-1980424597190702792510170893 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_151488_151552 :
    (∑ n ∈ Ico 151488 151552, mobiusTreeValue 16 mobiusTable1200001 n) = (-4 : ℤ) ∧
    (∑ n ∈ Ico 151488 151552, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 151488 151552, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-132014 : ℤ) ∧
    (∑ n ∈ Ico 151488 151552, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-2640285832864406135394323132 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_151424_151552 :
    (∑ n ∈ Ico 151424 151552, mobiusTreeValue 16 mobiusTable1200001 n) = (-7 : ℤ) ∧
    (∑ n ∈ Ico 151424 151552, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (79 : ℕ) ∧
    (∑ n ∈ Ico 151424 151552, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-231033 : ℤ) ∧
    (∑ n ∈ Ico 151424 151552, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-4620710430055108927904494025 : ℤ) := by
  rcases cdemPrefixStats_151424_151488 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_151488_151552 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 151424 ≤ 151488) (by norm_num : 151488 ≤ 151552), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 151424 ≤ 151488) (by norm_num : 151488 ≤ 151552), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 151424 ≤ 151488) (by norm_num : 151488 ≤ 151552), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 151424 ≤ 151488) (by norm_num : 151488 ≤ 151552), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_151296_151552 :
    (∑ n ∈ Ico 151296 151552, mobiusTreeValue 16 mobiusTable1200001 n) = (-13 : ℤ) ∧
    (∑ n ∈ Ico 151296 151552, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (159 : ℕ) ∧
    (∑ n ∈ Ico 151296 151552, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-429151 : ℤ) ∧
    (∑ n ∈ Ico 151296 151552, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-8583185470175573819996574069 : ℤ) := by
  rcases cdemPrefixStats_151296_151424 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_151424_151552 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 151296 ≤ 151424) (by norm_num : 151424 ≤ 151552), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 151296 ≤ 151424) (by norm_num : 151424 ≤ 151552), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 151296 ≤ 151424) (by norm_num : 151424 ≤ 151552), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 151296 ≤ 151424) (by norm_num : 151424 ≤ 151552), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_151040_151552 :
    (∑ n ∈ Ico 151040 151552, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 151040 151552, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (312 : ℕ) ∧
    (∑ n ∈ Ico 151040 151552, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (949 : ℤ) ∧
    (∑ n ∈ Ico 151040 151552, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (18949539976655917432301289 : ℤ) := by
  rcases cdemPrefixStats_151040_151296 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_151296_151552 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 151040 ≤ 151296) (by norm_num : 151296 ≤ 151552), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 151040 ≤ 151296) (by norm_num : 151296 ≤ 151552), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 151040 ≤ 151296) (by norm_num : 151296 ≤ 151552), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 151040 ≤ 151296) (by norm_num : 151296 ≤ 151552), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_150528_151552 :
    (∑ n ∈ Ico 150528 151552, mobiusTreeValue 16 mobiusTable1200001 n) = (15 : ℤ) ∧
    (∑ n ∈ Ico 150528 151552, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (623 : ℕ) ∧
    (∑ n ∈ Ico 150528 151552, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (498555 : ℤ) ∧
    (∑ n ∈ Ico 150528 151552, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (9971156100798433842891579808 : ℤ) := by
  rcases cdemPrefixStats_150528_151040 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_151040_151552 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 150528 ≤ 151040) (by norm_num : 151040 ≤ 151552), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 150528 ≤ 151040) (by norm_num : 151040 ≤ 151552), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 150528 ≤ 151040) (by norm_num : 151040 ≤ 151552), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 150528 ≤ 151040) (by norm_num : 151040 ≤ 151552), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_149504_151552 :
    (∑ n ∈ Ico 149504 151552, mobiusTreeValue 16 mobiusTable1200001 n) = (32 : ℤ) ∧
    (∑ n ∈ Ico 149504 151552, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (1246 : ℕ) ∧
    (∑ n ∈ Ico 149504 151552, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (1065886 : ℤ) ∧
    (∑ n ∈ Ico 149504 151552, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (21317812447199881217801732847 : ℤ) := by
  rcases cdemPrefixStats_149504_150528 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_150528_151552 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 149504 ≤ 150528) (by norm_num : 150528 ≤ 151552), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 149504 ≤ 150528) (by norm_num : 150528 ≤ 151552), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 149504 ≤ 150528) (by norm_num : 150528 ≤ 151552), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 149504 ≤ 150528) (by norm_num : 150528 ≤ 151552), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_147456_151552 :
    (∑ n ∈ Ico 147456 151552, mobiusTreeValue 16 mobiusTable1200001 n) = (20 : ℤ) ∧
    (∑ n ∈ Ico 147456 151552, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (2492 : ℕ) ∧
    (∑ n ∈ Ico 147456 151552, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (665378 : ℤ) ∧
    (∑ n ∈ Ico 147456 151552, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (13307288610938289015990466582 : ℤ) := by
  rcases cdemPrefixStats_147456_149504 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_149504_151552 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 147456 ≤ 149504) (by norm_num : 149504 ≤ 151552), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 147456 ≤ 149504) (by norm_num : 149504 ≤ 151552), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 147456 ≤ 149504) (by norm_num : 149504 ≤ 151552), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 147456 ≤ 149504) (by norm_num : 149504 ≤ 151552), hR1, hR2] <;> norm_num

theorem cdemPrefixGroup036_checked_complete :
    (∑ n ∈ Ico 147456 151552, mobiusTreeValue 16 mobiusTable1200001 n) = (20 : ℤ) ∧
    (∑ n ∈ Ico 147456 151552, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (2492 : ℕ) ∧
    (∑ n ∈ Ico 147456 151552, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (665378 : ℤ) ∧
    (∑ n ∈ Ico 147456 151552, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (13307288610938289015990466582 : ℤ) := cdemPrefixStats_147456_151552
end Helfgott
#print axioms Helfgott.cdemPrefixGroup036_checked_complete

open Helfgott Finset
open scoped BigOperators

theorem solution :
    (∑ n ∈ Ico 147456 151552, mobiusTreeValue 16 mobiusTable1200001 n) = (20 : ℤ) ∧
    (∑ n ∈ Ico 147456 151552, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (2492 : ℕ) ∧
    (∑ n ∈ Ico 147456 151552, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (665378 : ℤ) ∧
    (∑ n ∈ Ico 147456 151552, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (13307288610938289015990466582 : ℤ) := Helfgott.cdemPrefixGroup036_checked_complete
#print axioms solution
