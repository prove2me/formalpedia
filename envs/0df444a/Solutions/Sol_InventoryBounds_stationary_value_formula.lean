-- Prove2me | solution 1 for InventoryBounds.stationary_value_formula
-- status  : ACCEPTED   (prove)
-- author  : @visuddhi
-- created : 2026-10-08T16:24:40.633743+00:00
-- url     : https://prove2.me/submissions/7c352ade-5429-4f95-bec2-ad40858d54e1

import Definitions.Def_InventoryBounds_StationaryValuation
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

set_option autoImplicit false
open scoped BigOperators

namespace InventoryBounds.FormulaAudit

theorem one_period_cost (ρ y : ℝ) (hy : 0 ≤ y) :
    ρ * stageCost 1 1 y 0 + (1 - ρ) * stageCost 1 1 y 1 =
      if y ≤ 1 then (1 - ρ) + (2 * ρ - 1) * y else y - (1 - ρ) := by
  simp only [stageCost, one_mul, sub_zero, zero_sub]
  rw [max_eq_left hy, max_eq_right (neg_nonpos.mpr hy)]
  by_cases h : y ≤ 1
  · rw [if_pos h, max_eq_right (sub_nonpos.mpr h), max_eq_left (sub_nonneg.mpr h)]
    ring
  · have h' : 1 ≤ y := le_of_lt (lt_of_not_ge h)
    rw [if_neg h, max_eq_left (sub_nonneg.mpr h'), max_eq_right (sub_nonpos.mpr h')]
    ring

theorem one_period_cost_mono (ρ y z : ℝ) (hρ : 1 / 2 ≤ ρ)
    (hy : 0 ≤ y) (hyz : y ≤ z) :
    ρ * stageCost 1 1 y 0 + (1 - ρ) * stageCost 1 1 y 1 ≤
      ρ * stageCost 1 1 z 0 + (1 - ρ) * stageCost 1 1 z 1 := by
  rw [one_period_cost ρ y hy, one_period_cost ρ z (hy.trans hyz)]
  have hs : 0 ≤ 2 * ρ - 1 := by linarith
  split_ifs <;> nlinarith

theorem continuation_objective_mono (v : ℝ → ℝ) (hv : Monotone v)
    (ρ y z : ℝ) (hρ : 1 / 2 ≤ ρ) (hρ1 : ρ ≤ 1)
    (hy : 0 ≤ y) (hyz : y ≤ z) :
    ρ * (stageCost 1 1 y 0 + v y) + (1 - ρ) * (stageCost 1 1 y 1 + v (y - 1)) ≤
      ρ * (stageCost 1 1 z 0 + v z) + (1 - ρ) * (stageCost 1 1 z 1 + v (z - 1)) := by
  have hg := one_period_cost_mono ρ y z hρ hy hyz
  have h0 := mul_le_mul_of_nonneg_left (hv hyz) (show 0 ≤ ρ by linarith)
  have h1 := mul_le_mul_of_nonneg_left (hv (sub_le_sub_right hyz 1)) (sub_nonneg.mpr hρ1)
  nlinarith

theorem zero_value_monotone (T : ℕ) (ρ : ℝ) (hρ : 1 / 2 ≤ ρ) (hρ1 : ρ ≤ 1) :
    Monotone (zeroBaseStockValue T ρ) := by
  induction T with
  | zero => intro x z hxz; simp [zeroBaseStockValue]
  | succ n ih =>
    intro x z hxz
    exact continuation_objective_mono (zeroBaseStockValue n ρ) ih
      ρ (max x 0) (max z 0) hρ hρ1 (le_max_right x 0)
      (max_le_max hxz le_rfl)

theorem zero_base_stock_optimal (T : ℕ) (ρ x : ℝ)
    (hρ : 1 / 2 ≤ ρ) (hρ1 : ρ ≤ 1) :
    bernoulliDP T ρ x = zeroBaseStockValue T ρ x := by
  induction T generalizing x with
  | zero => rfl
  | succ n ih =>
    let a : ℝ := max x 0
    let f : ℝ → ℝ := fun y =>
      ρ * (stageCost 1 1 y 0 + zeroBaseStockValue n ρ y) +
      (1 - ρ) * (stageCost 1 1 y 1 + zeroBaseStockValue n ρ (y - 1))
    have hmin : ∀ y, a ≤ y → f a ≤ f y := by
      intro y hy
      exact continuation_objective_mono (zeroBaseStockValue n ρ)
        (zero_value_monotone n ρ hρ hρ1) ρ a y hρ hρ1 (le_max_right x 0) hy
    have hmem : f a ∈ f '' Set.Ici a := ⟨a, Set.mem_Ici.mpr (le_refl a), rfl⟩
    have hne : (f '' Set.Ici a).Nonempty := ⟨f a, hmem⟩
    have hbound : ∀ z ∈ f '' Set.Ici a, f a ≤ z := by
      rintro z ⟨y, hy, rfl⟩
      exact hmin y hy
    have hbdd : BddBelow (f '' Set.Ici a) := ⟨f a, hbound⟩
    simp only [bernoulliDP, zeroBaseStockValue, ih]
    change sInf (f '' Set.Ici a) = f a
    exact le_antisymm (csInf_le hbdd hmem) (le_csInf hne hbound)

theorem zero_value_nonpositive (T : ℕ) (ρ x : ℝ) (hx : x ≤ 0) :
    zeroBaseStockValue T ρ x = zeroBaseStockValue T ρ 0 := by
  cases T with
  | zero => rfl
  | succ n => simp only [zeroBaseStockValue, max_eq_right hx, max_self]

theorem zero_value_at_zero (T : ℕ) (ρ : ℝ) :
    zeroBaseStockValue T ρ 0 = (T : ℝ) * (1 - ρ) := by
  induction T with
  | zero => simp [zeroBaseStockValue]
  | succ n ih =>
    rw [zeroBaseStockValue]
    norm_num [stageCost]
    rw [zero_value_nonpositive n ρ (-1) (by norm_num), ih]
    ring

theorem zero_value_at_one (T : ℕ) (ρ : ℝ) :
    zeroBaseStockValue T ρ 1 = valueFormula T ρ := by
  induction T with
  | zero => simp [zeroBaseStockValue, valueFormula]
  | succ n ih =>
    rw [zeroBaseStockValue]
    norm_num [stageCost]
    rw [ih, zero_value_at_zero]
    simp only [valueFormula, Finset.sum_range_succ', pow_succ,
      ← Finset.sum_mul,
      Nat.cast_add, Nat.cast_one, pow_zero]
    ring

theorem stationary_value_formula (T : ℕ) (ρ : ℝ)
    (hρ : 1 / 2 < ρ) (hρ1 : ρ ≤ 1) :
    bernoulliDP T ρ 1 = valueFormula T ρ := by
  rw [zero_base_stock_optimal T ρ 1 (le_of_lt hρ) hρ1]
  exact zero_value_at_one T ρ

end InventoryBounds.FormulaAudit

#print axioms InventoryBounds.FormulaAudit.zero_base_stock_optimal
#print axioms InventoryBounds.FormulaAudit.stationary_value_formula

open InventoryBounds

theorem solution (T : ℕ) (ρ : ℝ)
    (hρ : 1 / 2 < ρ) (hρ1 : ρ ≤ 1) :
    bernoulliDP T ρ 1 = valueFormula T ρ := by
  exact InventoryBounds.FormulaAudit.stationary_value_formula T ρ hρ hρ1

#print axioms solution
