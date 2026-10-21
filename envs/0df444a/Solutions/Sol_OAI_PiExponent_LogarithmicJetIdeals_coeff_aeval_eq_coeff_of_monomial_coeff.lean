-- Prove2me | solution 1 for OAI.PiExponent.LogarithmicJetIdeals.coeff_aeval_eq_coeff_of_monomial_coeff
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-20T17:55:41.534998+00:00
-- url     : https://prove2.me/submissions/7a999115-a839-4603-aa6b-39d494ffe8ec

import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation

open scoped BigOperators

theorem solution
    {m : Nat}
    (R : Fin (m + 1) -> MvPowerSeries (Fin (m + 1)) Complex)
    (Q : MvPolynomial (Fin (m + 1)) Complex)
    (e : Fin (m + 1) -> Nat)
    (hmono : ∀ a : Finsupp (Fin (m + 1)) Nat, a ∈ Q.support ->
      MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm e)
        (MvPolynomial.aeval R (MvPolynomial.monomial a (1 : Complex))) =
      MvPolynomial.coeff (Finsupp.equivFunOnFinite.symm e)
        (MvPolynomial.monomial a (1 : Complex))) :
    MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm e)
      (MvPolynomial.aeval R Q) =
    MvPolynomial.coeff (Finsupp.equivFunOnFinite.symm e) Q := by
  classical
  let k := Finsupp.equivFunOnFinite.symm e
  have hterm (a : Finsupp (Fin (m + 1)) Nat) (ha : a ∈ Q.support)
      (c : Complex) :
      MvPowerSeries.coeff k (MvPolynomial.aeval R (MvPolynomial.monomial a c)) =
        MvPolynomial.coeff k (MvPolynomial.monomial a c) := by
    have hscaled : MvPolynomial.monomial a c = c • MvPolynomial.monomial a (1 : Complex) := by
      simp only [MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
    rw [hscaled, map_smul, MvPowerSeries.coeff_smul, MvPolynomial.coeff_smul,
      smul_eq_mul]
    exact congrArg (fun z : Complex => c * z) (hmono a ha)
  rw [MvPolynomial.as_sum Q]
  simp only [map_sum, MvPolynomial.coeff_sum]
  apply Finset.sum_congr rfl
  intro a ha
  exact hterm a ha (MvPolynomial.coeff a Q)