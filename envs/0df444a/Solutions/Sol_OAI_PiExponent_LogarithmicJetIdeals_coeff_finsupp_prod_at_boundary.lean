-- Prove2me | solution 1 for OAI.PiExponent.LogarithmicJetIdeals.coeff_finsupp_prod_at_boundary
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-20T17:59:17.292729+00:00
-- url     : https://prove2.me/submissions/954d31d3-f140-49c9-a182-b4a79aa25c65

import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_coeff_finsupp_prod_linear_part
import Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_coeff_X_prod_eq_monomial

open scoped BigOperators

theorem solution
    {ι : Type} [Fintype ι] [DecidableEq ι]
    {K : Type} [CommSemiring K]
    (R : ι -> MvPowerSeries ι K)
    (a : Finsupp ι Nat)
    (hR : ∀ (i : ι) (d : ι -> Nat),
      (∑ k : ι, d k) <= 1 ->
        MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm d) (R i) =
          MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm d) (MvPowerSeries.X i))
    (e : ι -> Nat)
    (he : (∑ k : ι, e k) = (∑ k : ι, a k)) :
    MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm e)
      (a.prod fun i k => R i ^ k) =
      MvPolynomial.coeff (Finsupp.equivFunOnFinite.symm e)
        (MvPolynomial.monomial a (1 : K)) := by
  calc
    MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm e)
        (a.prod fun i k => R i ^ k) =
        MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm e)
          (a.prod fun i k => MvPowerSeries.X i ^ k) :=
      OAI.PiExponent.LogarithmicJetIdeals.coeff_finsupp_prod_linear_part
        R a hR e he
    _ = MvPolynomial.coeff (Finsupp.equivFunOnFinite.symm e)
        (MvPolynomial.monomial a (1 : K)) :=
      OAI.PiExponent.LogarithmicJetIdeals.coeff_X_prod_eq_monomial a e