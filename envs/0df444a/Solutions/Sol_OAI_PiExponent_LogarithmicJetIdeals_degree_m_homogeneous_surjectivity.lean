-- Prove2me | solution 1 for OAI.PiExponent.LogarithmicJetIdeals.degree_m_homogeneous_surjectivity
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-15T06:38:12.24906+00:00
-- url     : https://prove2.me/submissions/f90192a3-5325-4c57-92f9-6df239c51d88

import Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_exists_degree_index_finset
import Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_finite_homogeneous_sum_coeff

import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.MvPowerSeries.Equiv

open scoped BigOperators

theorem solution
    {n : Nat}
    (phi : Fin n → MvPowerSeries (Fin n) Complex)
    (N : Nat)
    (hbelow : ∀ d e : Fin n → Nat,
      (∑ k, d k) ≤ N → (∑ k, e k) ≤ N →
      (∑ k, e k) < (∑ k, d k) →
      MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm e)
        (MvPolynomial.aeval phi
          (MvPolynomial.monomial (Finsupp.equivFunOnFinite.symm d) (1 : Complex))) = 0)
    (hsame : ∀ d e : Fin n → Nat,
      (∑ k, d k) ≤ N → (∑ k, e k) ≤ N →
      (∑ k, e k) = (∑ k, d k) →
      MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm e)
        (MvPolynomial.aeval phi
          (MvPolynomial.monomial (Finsupp.equivFunOnFinite.symm d) (1 : Complex))) =
            (if d = e then 1 else 0))
    (value : (Fin n → Nat) → Complex)
    (m : Nat)
    (hm : m ≤ N) :
    ∃ R : MvPolynomial (Fin n) Complex,
      (∀ e : Fin n → Nat, (∑ k, e k) < m →
        MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm e)
          (MvPolynomial.aeval phi R) = 0) ∧
      (∀ e : Fin n → Nat, (∑ k, e k) = m →
        MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm e)
          (MvPolynomial.aeval phi R) = value e) := by
  obtain ⟨S, hS⟩ :=
    OAI.PiExponent.LogarithmicJetIdeals.exists_degree_index_finset (n := n) m
  let R : MvPolynomial (Fin n) Complex :=
    ∑ d ∈ S, MvPolynomial.monomial (Finsupp.equivFunOnFinite.symm d) (value d)
  refine ⟨R, ?_, ?_⟩
  · intro e he
    have hc :=
      OAI.PiExponent.LogarithmicJetIdeals.finite_homogeneous_sum_coeff
        phi N hbelow hsame value m hm S hS e (Nat.le_of_lt he)
    simpa [R, Nat.ne_of_lt he] using hc
  · intro e he
    have hc :=
      OAI.PiExponent.LogarithmicJetIdeals.finite_homogeneous_sum_coeff
        phi N hbelow hsame value m hm S hS e (le_of_eq he)
    simpa [R, he] using hc