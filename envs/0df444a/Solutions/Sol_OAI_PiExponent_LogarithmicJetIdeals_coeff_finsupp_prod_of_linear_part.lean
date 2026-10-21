-- Prove2me | solution 1 for OAI.PiExponent.LogarithmicJetIdeals.coeff_finsupp_prod_of_linear_part
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-20T17:53:06.274823+00:00
-- url     : https://prove2.me/submissions/37908539-d4f5-4c0d-8d94-e44fe5ff657f

import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_coeff_finsupp_prod_below_degree
import Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_coeff_finsupp_prod_at_boundary

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
      (a.prod fun i k => R i ^ k) =
      MvPolynomial.coeff (Finsupp.equivFunOnFinite.symm e)
        (MvPolynomial.monomial a (1 : Complex)) := by
  by_cases hEq : (∑ k : Fin (m + 1), e k) = (∑ k : Fin (m + 1), a k)
  · exact OAI.PiExponent.LogarithmicJetIdeals.coeff_finsupp_prod_at_boundary
      R a hR e hEq
  · have hlt : (∑ k : Fin (m + 1), e k) < (∑ k : Fin (m + 1), a k) := by omega
    exact OAI.PiExponent.LogarithmicJetIdeals.coeff_finsupp_prod_below_degree
      R a hR e hlt