-- Prove2me | solution 1 for OAI.PiExponent.LogarithmicJetIdeals.homogeneous_substitution_coefficients_monomial
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-15T06:31:02.529269+00:00
-- url     : https://prove2.me/submissions/487eaba7-fd4c-4778-b779-b855440e82f9

import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.MvPowerSeries.Equiv
import Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_coefficients_scaled_product_identity_linear

open scoped BigOperators

theorem solution
    {n : Nat}
    (phi : Fin n → MvPowerSeries (Fin n) Complex)
    (hzero : ∀ i, MvPowerSeries.coeff 0 (phi i) = 0)
    (hlinear : ∀ i j, MvPowerSeries.coeff (Finsupp.single j 1) (phi i) =
      (if i = j then 1 else 0))
    (m : Fin n →₀ Nat)
    (c : Complex)
    (D : Nat)
    (e : Fin n → Nat)
    (hdeg : (∑ i, m i) = D) :
    ((∑ i, e i) < D →
      MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm e)
        (MvPolynomial.aeval phi (MvPolynomial.monomial m c)) = 0) ∧
    ((∑ i, e i) = D →
      MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm e)
        (MvPolynomial.aeval phi (MvPolynomial.monomial m c)) =
          MvPolynomial.coeff (Finsupp.equivFunOnFinite.symm e)
            (MvPolynomial.monomial m c)) := by
  simpa only [MvPolynomial.aeval_monomial] using
    OAI.PiExponent.LogarithmicJetIdeals.coefficients_scaled_product_identity_linear
      phi hzero hlinear m c D e hdeg