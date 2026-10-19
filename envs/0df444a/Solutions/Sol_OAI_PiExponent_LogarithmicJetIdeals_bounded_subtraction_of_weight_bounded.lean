-- Prove2me | solution 1 for OAI.PiExponent.LogarithmicJetIdeals.bounded_subtraction_of_weight_bounded
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T23:12:29.934541+00:00
-- url     : https://prove2.me/submissions/62a22938-b3f3-4b0e-9948-a2fead0cc9e5

import Mathlib
import Mathlib.RingTheory.MvPolynomial.MonomialOrder
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.Data.Complex.Basic

open scoped BigOperators
theorem h41_bsub (m : ℕ) (w : Fin (m + 1) → ℝ) (D : ℝ) (N : Fin (m + 1) → ℕ) (o : MonomialOrder (Fin (m + 1))) (ho : ∀ i b, (∑ j, w j * (b j : ℝ) ≤ D) → o.toSyn b < o.toSyn (Finsupp.single i (N i))) (i : Fin (m + 1)) (Q : MvPolynomial (Fin (m + 1)) ℂ) (hQ : ∀ b ∈ Q.support, ∑ j, w j * (b j : ℝ) ≤ D) : (o.leadingCoeff (MvPolynomial.monomial (Finsupp.single i (N i)) (1 : ℂ) - Q) = 1) ∧ (o.degree (MvPolynomial.monomial (Finsupp.single i (N i)) (1 : ℂ) - Q) = Finsupp.single i (N i)) := by
  classical
  have hdm : o.degree (MvPolynomial.monomial (Finsupp.single i (N i)) (1 : ℂ)) = Finsupp.single i (N i) := by
    rw [o.degree_monomial]; simp
  have hlm : o.leadingCoeff (MvPolynomial.monomial (Finsupp.single i (N i)) (1 : ℂ)) = 1 := by
    rw [o.leadingCoeff_monomial]
  by_cases hQ0 : Q = 0
  · subst hQ0; simp only [sub_zero]; exact ⟨hlm, hdm⟩
  have hlt : o.toSyn (o.degree Q) < o.toSyn (o.degree (MvPolynomial.monomial (Finsupp.single i (N i)) (1 : ℂ))) := by
    rw [hdm]
    exact ho i _ (hQ _ (o.degree_mem_support hQ0))
  exact ⟨(o.leadingCoeff_sub_of_lt hlt).trans hlm, (o.degree_sub_of_lt hlt).trans hdm⟩

theorem solution (m : ℕ) (w : Fin (m + 1) → ℝ) (D : ℝ) (N : Fin (m + 1) → ℕ) (o : MonomialOrder (Fin (m + 1))) (hN : ∀ i, D < (N i : ℝ) * w i) (ho : ∀ i b, (∑ j, w j * (b j : ℝ) ≤ D) → o.toSyn b < o.toSyn (Finsupp.single i (N i))) (i : Fin (m + 1)) (Q : MvPolynomial (Fin (m + 1)) ℂ) (hQ : ∀ b ∈ Q.support, ∑ j, w j * (b j : ℝ) ≤ D) : (o.leadingCoeff (MvPolynomial.monomial (Finsupp.single i (N i)) (1 : ℂ) - Q) = 1) ∧ (o.degree (MvPolynomial.monomial (Finsupp.single i (N i)) (1 : ℂ) - Q) = Finsupp.single i (N i)) := by
  exact h41_bsub m w D N o ho i Q hQ

