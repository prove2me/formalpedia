-- Prove2me | solution 1 for OAI.PiExponent.LogarithmicJetIdeals.coeff_X_prod_eq_monomial
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-20T18:19:08.139584+00:00
-- url     : https://prove2.me/submissions/933de0ff-cd85-4544-b572-c969f786edbb

import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation

open scoped BigOperators

theorem solution
    {ι : Type} [Fintype ι] [DecidableEq ι]
    {K : Type} [CommSemiring K]
    (a : Finsupp ι Nat)
    (e : ι -> Nat) :
    MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm e)
      (a.prod fun i k => MvPowerSeries.X i ^ k) =
    MvPolynomial.coeff (Finsupp.equivFunOnFinite.symm e)
      (MvPolynomial.monomial a (1 : K)) := by
  classical
  rw [← MvPowerSeries.monomial_one_eq a]
  simp [MvPowerSeries.coeff_monomial, MvPolynomial.coeff_monomial, eq_comm]