-- Prove2me | solution 1 for OAI.PiExponent.LogarithmicJetIdeals.homogeneous_aeval_coeff_of_linear_part
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-20T17:37:21.374638+00:00
-- url     : https://prove2.me/submissions/d5bbe66d-b1d9-4b20-8358-7b465c44316a

import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_aeval_monomial_coeff_of_linear_part
import Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_coeff_aeval_eq_coeff_of_monomial_coeff

open scoped BigOperators
open OAI.PiExponent.AdmissibleFormalInterpolation

theorem solution
    {m : Nat}
    (R : Fin (m + 1) -> MvPowerSeries (Fin (m + 1)) Complex)
    (n : Nat)
    (Q : MvPolynomial (Fin (m + 1)) Complex)
    (hhom : ∀ a : Finsupp (Fin (m + 1)) Nat,
      a ∈ Q.support -> (∑ k : Fin (m + 1), a k) = n)
    (hR : ∀ (i : Fin (m + 1)) (d : Fin (m + 1) -> Nat),
      (∑ k : Fin (m + 1), d k) <= 1 ->
        MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm d) (R i) =
          MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm d) (MvPowerSeries.X i))
    (e : Fin (m + 1) -> Nat)
    (he : (∑ k : Fin (m + 1), e k) <= n) :
    MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm e)
      (MvPolynomial.aeval R Q) =
      MvPolynomial.coeff (Finsupp.equivFunOnFinite.symm e) Q := by
  apply OAI.PiExponent.LogarithmicJetIdeals.coeff_aeval_eq_coeff_of_monomial_coeff
  intro a ha
  have hae : (∑ k : Fin (m + 1), e k) <= (∑ k : Fin (m + 1), a k) := by
    rw [hhom a ha]
    exact he
  exact OAI.PiExponent.LogarithmicJetIdeals.aeval_monomial_coeff_of_linear_part
    R a hR e hae