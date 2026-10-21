-- Prove2me | solution 1 for OAI.PiExponent.LogarithmicJetIdeals.finiteJet_interpolation_from_triangular
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-15T06:26:15.288494+00:00
-- url     : https://prove2.me/submissions/e7851db1-ef04-4cde-bbf6-956531ee5f63

import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.MvPowerSeries.Equiv
import Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_finiteJet_degree_extension
import Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_finite_induction_of_extend

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
    (value : (Fin n → Nat) → Complex) :
    ∃ Q : MvPolynomial (Fin n) Complex,
      (e : Fin n → Nat) →
        (∑ k, e k) ≤ N →
          MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm e)
            (MvPolynomial.aeval phi Q) = value e := by
  let Good : MvPolynomial (Fin n) Complex → Nat → Prop :=
    fun Q m => ∀ e : Fin n → Nat, (∑ k, e k) < m →
      MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm e)
        (MvPolynomial.aeval phi Q) = value e
  have hbase : ∃ Q : MvPolynomial (Fin n) Complex, Good Q 0 := by
    refine ⟨0, ?_⟩
    intro e he
    exact False.elim (Nat.not_lt_zero _ he)
  have hstep : ∀ m : Nat, m ≤ N →
      ∀ Q : MvPolynomial (Fin n) Complex, Good Q m →
        ∃ Q' : MvPolynomial (Fin n) Complex, Good Q' (m + 1) := by
    intro m hm Q hQ
    exact OAI.PiExponent.LogarithmicJetIdeals.finiteJet_degree_extension
      phi N hbelow hsame value m Q hQ hm
  obtain ⟨Q, hQ⟩ :=
    OAI.PiExponent.LogarithmicJetIdeals.finite_induction_of_extend
      (α := MvPolynomial (Fin n) Complex) N Good hbase hstep
  refine ⟨Q, ?_⟩
  intro e he
  exact hQ e (Nat.lt_succ_of_le he)
