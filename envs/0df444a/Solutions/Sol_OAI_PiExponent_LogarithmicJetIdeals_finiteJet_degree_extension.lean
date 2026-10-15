-- Prove2me | solution 1 for OAI.PiExponent.LogarithmicJetIdeals.finiteJet_degree_extension
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-15T06:30:23.054433+00:00
-- url     : https://prove2.me/submissions/739dc720-3459-4e71-8f67-145b0353c62c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.MvPowerSeries.Equiv
import Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_degree_m_correction

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
    (Q : MvPolynomial (Fin n) Complex)
    (hQ : ∀ e : Fin n → Nat, (∑ k, e k) < m →
      MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm e)
        (MvPolynomial.aeval phi Q) = value e)
    (hm : m ≤ N) :
    ∃ Q' : MvPolynomial (Fin n) Complex,
      ∀ e : Fin n → Nat, (∑ k, e k) < m + 1 →
        MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm e)
          (MvPolynomial.aeval phi Q') = value e := by
  obtain ⟨R, hlow, hdegree⟩ :=
    OAI.PiExponent.LogarithmicJetIdeals.degree_m_correction
      phi N hbelow hsame value m Q hm
  refine ⟨Q + R, ?_⟩
  intro e he
  by_cases hlt : (∑ k, e k) < m
  · rw [hlow e hlt]
    exact hQ e hlt
  · have heq : (∑ k, e k) = m := by omega
    exact hdegree e heq