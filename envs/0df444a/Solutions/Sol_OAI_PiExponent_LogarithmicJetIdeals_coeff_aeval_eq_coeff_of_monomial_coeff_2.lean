-- Prove2me | solution 2 for OAI.PiExponent.LogarithmicJetIdeals.coeff_aeval_eq_coeff_of_monomial_coeff
-- status  : ACCEPTED   (prove)
-- author  : @polylog
-- created : 2026-10-20T18:09:39.43533+00:00
-- url     : https://prove2.me/submissions/ded56740-5388-4bea-b620-cf0139f081c3

import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation

open scoped BigOperators

theorem solution {m : Nat}
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
  set e' := Finsupp.equivFunOnFinite.symm e
  have hL : MvPowerSeries.coeff e' (MvPolynomial.aeval R Q) =
      ∑ v ∈ Q.support, Q.coeff v *
        MvPowerSeries.coeff e' (MvPolynomial.aeval R (MvPolynomial.monomial v (1 : Complex))) := by
    conv_lhs => rw [MvPolynomial.as_sum Q]
    rw [map_sum]
    rw [map_sum]
    refine Finset.sum_congr rfl ?_
    intro v hv
    have h : MvPolynomial.aeval R (MvPolynomial.monomial v (Q.coeff v)) =
        MvPowerSeries.C (Q.coeff v) *
          MvPolynomial.aeval R (MvPolynomial.monomial v (1 : Complex)) := by
      rw [MvPolynomial.aeval_monomial, MvPolynomial.aeval_monomial, map_one, one_mul,
        MvPowerSeries.c_eq_algebraMap]
    rw [h, MvPowerSeries.coeff_C_mul]
  have hR : MvPolynomial.coeff e' Q =
      ∑ v ∈ Q.support, Q.coeff v *
        MvPolynomial.coeff e' (MvPolynomial.monomial v (1 : Complex)) := by
    conv_lhs => rw [MvPolynomial.as_sum Q]
    simp only [MvPolynomial.coeff_sum]
    refine Finset.sum_congr rfl ?_
    intro v hv
    rw [MvPolynomial.coeff_monomial]
    by_cases h : e' = v <;> simp [h, MvPolynomial.coeff_monomial]
  rw [hL, hR]
  refine Finset.sum_congr rfl ?_
  intro v hv
  exact congrArg (fun x => MvPolynomial.coeff v Q * x) (hmono v hv)
