-- Prove2me | solution 1 for OAI.PiExponent.LogarithmicJetIdeals.finiteJet_monomial_coefficients
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-15T06:25:49.384994+00:00
-- url     : https://prove2.me/submissions/68f5c10c-65cd-4b89-bfe5-8fe7189d97b6

import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.MvPowerSeries.Equiv
import Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_homogeneous_substitution_coefficients

open scoped BigOperators

theorem solution
    {n : Nat}
    (phi : Fin n → MvPowerSeries (Fin n) Complex)
    (hzero : ∀ i, MvPowerSeries.coeff 0 (phi i) = 0)
    (hlinear : ∀ i j, MvPowerSeries.coeff (Finsupp.single j 1) (phi i) =
      (if i = j then 1 else 0))
    (d e : Fin n → Nat) :
    ((∑ k, e k) < (∑ k, d k) →
      MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm e)
        (MvPolynomial.aeval phi
          (MvPolynomial.monomial (Finsupp.equivFunOnFinite.symm d) (1 : Complex))) = 0) ∧
    ((∑ k, e k) = (∑ k, d k) →
      MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm e)
        (MvPolynomial.aeval phi
          (MvPolynomial.monomial (Finsupp.equivFunOnFinite.symm d) (1 : Complex))) =
            (if d = e then 1 else 0)) := by
  classical
  let md : Fin n →₀ Nat := Finsupp.equivFunOnFinite.symm d
  let me : Fin n →₀ Nat := Finsupp.equivFunOnFinite.symm e
  have hhom : ∀ m ∈ (MvPolynomial.monomial md (1 : Complex)).support,
      (∑ i, m i) = ∑ i, d i := by
    intro m hm
    have hm' : m = md := by
      simpa [md, MvPolynomial.support_monomial] using hm
    rw [hm']
    simp [md]
  have hc :=
    OAI.PiExponent.LogarithmicJetIdeals.homogeneous_substitution_coefficients
      phi hzero hlinear (MvPolynomial.monomial md (1 : Complex))
      (∑ i, d i) hhom e
  constructor
  · intro he
    exact hc.1 he
  · intro he
    simpa [md, me, MvPolynomial.coeff_monomial] using hc.2 he