-- Prove2me | solution 1 for NarrowDNF.Weighted.select_two_budgets
-- status  : ACCEPTED   (prove)
-- author  : @chenghua.liu
-- created : 2026-11-13T08:23:38.325208+00:00
-- url     : https://prove2.me/submissions/fd40cecc-e5f2-4b92-9ac9-6ac6677f74e1

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Theorems.Thm_NarrowDNF_Weighted_exists_le_mean

namespace NarrowDNF
end NarrowDNF

namespace NarrowDNF.Weighted
end NarrowDNF.Weighted


open NarrowDNF
open NarrowDNF
open NarrowDNF.Weighted
open scoped BigOperators
variable {α : Type*} [Fintype α]
/-- Simultaneously select small error and cost by one weighted average.
This is the full finite averaging step of Theorem 3.5, including zero budget. -/
theorem solution [Nonempty α] (weights : α → ℝ)
    (hw : ∀ x, 0 < weights x) (hs : ∑ x, weights x = 1)
    (err cost : α → ℝ) (herr : ∀ x, 0 ≤ err x) (hcost : ∀ x, 0 ≤ cost x)
    (e B τ : ℝ) (hB : 0 ≤ B) (hτ : 0 < τ)
    (he : (∑ x, weights x * err x) ≤ e)
    (hM : (∑ x, weights x * cost x) ≤ B) :
    ∃ x, err x ≤ e + τ ∧ cost x ≤ B * (1 + e / τ) := by
  classical
  by_cases hB0 : B = 0
  · obtain ⟨x, hx⟩ := exists_le_mean weights hw hs err
    refine ⟨x, by linarith, ?_⟩
    have hterm : weights x * cost x ≤ ∑ y, weights y * cost y :=
      Finset.single_le_sum (fun y _ => mul_nonneg (hw y).le (hcost y)) (Finset.mem_univ x)
    have hc : cost x ≤ 0 := by nlinarith [hw x]
    simp only [hB0, zero_mul]
    exact hc
  · have hBp : 0 < B := lt_of_le_of_ne hB (Ne.symm hB0)
    obtain ⟨x, hx⟩ := exists_le_mean weights hw hs (fun x => err x + (τ / B) * cost x)
    have hsum : (∑ x, weights x * (err x + (τ / B) * cost x)) ≤ e + τ := by
      calc
        _ = (∑ x, weights x * err x) + (τ / B) * (∑ x, weights x * cost x) := by
          simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
          congr 1
          apply Finset.sum_congr rfl
          intro i _
          ring
        _ ≤ e + (τ / B) * B := add_le_add he
          (mul_le_mul_of_nonneg_left hM (div_nonneg hτ.le hB))
        _ = e + τ := by rw [div_mul_cancel₀ τ hB0]
    have hchoice : err x + (τ / B) * cost x ≤ e + τ := hx.trans hsum
    refine ⟨x, ?_, ?_⟩
    · have := mul_nonneg (div_nonneg hτ.le hB) (hcost x)
      linarith
    · have hc : (τ * cost x) / B ≤ e + τ := by
        rw [← div_mul_eq_mul_div]
        linarith [herr x]
      have hc' := (div_le_iff₀ hBp).mp hc
      have hbound : cost x ≤ ((e + τ) * B) / τ := by
        apply (le_div_iff₀ hτ).mpr
        nlinarith
      have hident : ((e + τ) * B) / τ = B * (1 + e / τ) := by
        calc
          ((e + τ) * B) / τ = B * (e / τ + τ / τ) := by ring
          _ = B * (1 + e / τ) := by rw [div_self hτ.ne']; ring
      simpa only [hident] using hbound
