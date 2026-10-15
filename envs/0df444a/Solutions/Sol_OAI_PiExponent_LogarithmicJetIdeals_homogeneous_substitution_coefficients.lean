-- Prove2me | solution 1 for OAI.PiExponent.LogarithmicJetIdeals.homogeneous_substitution_coefficients
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-15T06:28:26.100675+00:00
-- url     : https://prove2.me/submissions/86553382-42ae-428b-bf4e-614ffb5a4198

import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.MvPowerSeries.Equiv
import Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_homogeneous_substitution_coefficients_monomial
import Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_homogeneous_substitution_coefficients_of_terms

open scoped BigOperators

theorem solution
    {n : Nat}
    (phi : Fin n → MvPowerSeries (Fin n) Complex)
    (hzero : ∀ i, MvPowerSeries.coeff 0 (phi i) = 0)
    (hlinear : ∀ i j, MvPowerSeries.coeff (Finsupp.single j 1) (phi i) =
      (if i = j then 1 else 0))
    (P : MvPolynomial (Fin n) Complex)
    (D : Nat)
    (hhom : ∀ m ∈ P.support, (∑ i, m i) = D)
    (e : Fin n → Nat) :
    ((∑ i, e i) < D →
      MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm e)
        (MvPolynomial.aeval phi P) = 0) ∧
    ((∑ i, e i) = D →
      MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm e)
        (MvPolynomial.aeval phi P) =
          MvPolynomial.coeff (Finsupp.equivFunOnFinite.symm e) P) := by
  exact OAI.PiExponent.LogarithmicJetIdeals.homogeneous_substitution_coefficients_of_terms
    phi P D e hhom (fun m hm => by
      have hd : (∑ i, m i) = D := hhom m hm
      exact OAI.PiExponent.LogarithmicJetIdeals.homogeneous_substitution_coefficients_monomial
        phi hzero hlinear m (MvPolynomial.coeff m P) D e hd)