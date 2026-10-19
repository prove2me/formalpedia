-- Prove2me | solution 1 for OAI.PiExponent.LogarithmicJetIdeals.extract_pure_leading_relations
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T23:12:37.167934+00:00
-- url     : https://prove2.me/submissions/fdaa4ed6-99e4-4483-9d9f-a7ad253cec92

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

theorem solution (m : ℕ) (w : Fin (m + 1) → ℝ) (D : ℝ) (I : Ideal (MvPolynomial (Fin (m + 1)) ℂ)) (N : Fin (m + 1) → ℕ) (o : MonomialOrder (Fin (m + 1))) (hN : ∀ i, D < (N i : ℝ) * w i) (ho : ∀ i b, (∑ j, w j * (b j : ℝ) ≤ D) → o.toSyn b < o.toSyn (Finsupp.single i (N i))) (hrep : ∀ P : MvPolynomial (Fin (m + 1)) ℂ, ∃ Q : MvPolynomial (Fin (m + 1)) ℂ, P - Q ∈ I ∧ ∀ b ∈ Q.support, ∑ i, w i * (b i : ℝ) ≤ D) : ∃ f : Fin (m + 1) → MvPolynomial (Fin (m + 1)) ℂ, (∀ i, f i ∈ I) ∧ (∀ i, o.leadingCoeff (f i) = 1) ∧ (∀ i, o.degree (f i) = Finsupp.single i (N i)) := by
  classical
  have h := fun i => hrep (MvPolynomial.monomial (Finsupp.single i (N i)) (1 : ℂ))
  choose Q hQI hQw using h
  refine ⟨fun i => MvPolynomial.monomial (Finsupp.single i (N i)) (1 : ℂ) - Q i, hQI, fun i => ?_, fun i => ?_⟩
  · exact (h41_bsub m w D N o ho i (Q i) (hQw i)).1
  · exact (h41_bsub m w D N o ho i (Q i) (hQw i)).2

