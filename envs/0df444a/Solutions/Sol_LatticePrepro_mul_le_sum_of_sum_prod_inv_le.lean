-- Prove2me | solution 1 for LatticePrepro.mul_le_sum_of_sum_prod_inv_le
-- status  : ACCEPTED   (prove)
-- author  : @WizardOfMenlo
-- created : 2026-11-16T22:11:22.18374+00:00
-- url     : https://prove2.me/submissions/53ffeb46-2661-4156-b7cb-372e4da0e04b

import Mathlib


namespace LatticePrepro

open Finset

/-- For positive reals `x_1, …, x_q`, `q + 1 ≤ ∑_j x_j + ∏_j x_j⁻¹` (the AM–GM inequality for the
`q + 1` numbers `x_1, …, x_q, (∏_j x_j)⁻¹`, whose product is `1`). -/
lemma add_one_le_sum_add_prod_inv {q : ℕ} (x : Fin q → ℝ) (hx : ∀ j, 0 < x j) :
    (q : ℝ) + 1 ≤ ∑ j, x j + ∏ j, (x j)⁻¹ := by
  have hP : 0 < ∏ j, (x j)⁻¹ := prod_pos fun j _ => inv_pos.mpr (hx j)
  have h1 : ∑ j, (Real.log (x j) + 1) ≤ ∑ j, x j :=
    sum_le_sum fun j _ => by linarith [Real.log_le_sub_one_of_pos (hx j)]
  have h2 : Real.log (∏ j, (x j)⁻¹) + 1 ≤ ∏ j, (x j)⁻¹ := by
    linarith [Real.log_le_sub_one_of_pos hP]
  have h3 : Real.log (∏ j, (x j)⁻¹) = -∑ j, Real.log (x j) := by
    rw [Real.log_prod fun j _ => (inv_pos.mpr (hx j)).ne']
    simp only [Real.log_inv, sum_neg_distrib]
  rw [sum_add_distrib, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one] at h1
  linarith

/-- If the sum over `r` of `∏_j λ_{r,j}⁻¹` is at most `|R| / t^q`, then the sum of all
`λ_{r,j}` is at least `|R| · q · t` (equation (31)). -/
private theorem mul_le_sum_of_sum_prod_inv_le {R : Type*} [Fintype R] {q : ℕ} (lam : R → Fin q → ℝ)
    (hlam : ∀ r j, 0 < lam r j) {t : ℝ} (ht : 0 < t)
    (h : (∑ r, ∏ j, (lam r j)⁻¹) * t ^ q ≤ Fintype.card R) :
    (Fintype.card R : ℝ) * q * t ≤ ∑ r, ∑ j, lam r j := by
  have h1 : ∀ r, (q : ℝ) + 1 ≤ (∑ j, lam r j) / t + t ^ q * ∏ j, (lam r j)⁻¹ := by
    intro r
    have h0 := add_one_le_sum_add_prod_inv (fun j => lam r j / t) fun j => div_pos (hlam r j) ht
    have e1 : ∑ j, lam r j / t = (∑ j, lam r j) / t := (sum_div _ _ _).symm
    have e2 : ∏ j, (lam r j / t)⁻¹ = t ^ q * ∏ j, (lam r j)⁻¹ := by
      have e : ∀ j, (lam r j / t)⁻¹ = t * (lam r j)⁻¹ := fun j => by
        rw [inv_div, div_eq_mul_inv]
      simp only [e, prod_mul_distrib, prod_const, card_univ, Fintype.card_fin]
    rwa [e1, e2] at h0
  have h2 : ∑ _r : R, ((q : ℝ) + 1) ≤
      ∑ r, ((∑ j, lam r j) / t + t ^ q * ∏ j, (lam r j)⁻¹) := sum_le_sum fun r _ => h1 r
  rw [sum_const, card_univ, nsmul_eq_mul, sum_add_distrib, ← sum_div, ← mul_sum] at h2
  have h3 : (Fintype.card R : ℝ) * q ≤ (∑ r, ∑ j, lam r j) / t := by linarith
  exact (le_div_iff₀ ht).mp h3

end LatticePrepro

open Finset
theorem solution {R : Type*} [Fintype R] {q : ℕ} (lam : R → Fin q → ℝ)
    (hlam : ∀ r j, 0 < lam r j) {t : ℝ} (ht : 0 < t)
    (h : (∑ r, ∏ j, (lam r j)⁻¹) * t ^ q ≤ Fintype.card R) :
    (Fintype.card R : ℝ) * q * t ≤ ∑ r, ∑ j, lam r j :=
  @LatticePrepro.mul_le_sum_of_sum_prod_inv_le R _ q lam hlam t ht h
