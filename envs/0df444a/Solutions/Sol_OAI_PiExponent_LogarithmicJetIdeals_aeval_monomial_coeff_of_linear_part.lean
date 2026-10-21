-- Prove2me | solution 1 for OAI.PiExponent.LogarithmicJetIdeals.aeval_monomial_coeff_of_linear_part
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-20T17:42:16.458127+00:00
-- url     : https://prove2.me/submissions/b2b20b5c-dbff-40fa-bfef-697c964e41c1

import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_coeff_finsupp_prod_of_linear_part

open scoped BigOperators

theorem solution
    {m : Nat}
    (R : Fin (m + 1) -> MvPowerSeries (Fin (m + 1)) Complex)
    (a : Finsupp (Fin (m + 1)) Nat)
    (hR : ∀ (i : Fin (m + 1)) (d : Fin (m + 1) -> Nat),
      (∑ k : Fin (m + 1), d k) <= 1 ->
        MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm d) (R i) =
          MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm d) (MvPowerSeries.X i))
    (e : Fin (m + 1) -> Nat)
    (he : (∑ k : Fin (m + 1), e k) <= (∑ k : Fin (m + 1), a k)) :
    MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm e)
      (MvPolynomial.aeval R (MvPolynomial.monomial a (1 : Complex))) =
      MvPolynomial.coeff (Finsupp.equivFunOnFinite.symm e)
        (MvPolynomial.monomial a (1 : Complex)) := by
  rw [MvPolynomial.aeval_monomial]
  simpa using
    OAI.PiExponent.LogarithmicJetIdeals.coeff_finsupp_prod_of_linear_part R a hR e he