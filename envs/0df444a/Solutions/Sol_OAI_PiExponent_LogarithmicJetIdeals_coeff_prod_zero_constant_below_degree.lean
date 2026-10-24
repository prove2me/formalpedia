-- Prove2me | solution 1 for OAI.PiExponent.LogarithmicJetIdeals.coeff_prod_zero_constant_below_degree
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T03:16:57.896017+00:00
-- url     : https://prove2.me/submissions/97c42cf7-3c28-4eb6-9708-5347d948d48b

import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation

open scoped BigOperators

theorem solution
    {ι : Type} [Fintype ι] [DecidableEq ι]
    {K : Type} [CommSemiring K]
    (R : ι -> MvPowerSeries ι K)
    (a : Finsupp ι Nat)
    (hzero : ∀ i, MvPowerSeries.coeff 0 (R i) = 0)
    (e : ι -> Nat)
    (he : (∑ k : ι, e k) < (∑ k : ι, a k)) :
    MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm e)
      (a.prod fun i k => R i ^ k) = 0 := by
  apply MvPowerSeries.coeff_of_lt_order
  have h1 : ((∑ k : ι, a k : ℕ) : ℕ∞) ≤ (a.prod fun i k => R i ^ k).order := by
    unfold Finsupp.prod
    refine le_trans ?_ (MvPowerSeries.le_order_prod _ _)
    rw [← Finsupp.sum_fintype a (fun _ k => k) (by simp)]
    unfold Finsupp.sum
    push_cast
    refine Finset.sum_le_sum fun i _ => ?_
    exact MvPowerSeries.le_order_pow_of_constantCoeff_eq_zero _ (hzero i)
  refine lt_of_lt_of_le ?_ h1
  rw [Finsupp.degree_eq_sum]
  simp only [Finsupp.coe_equivFunOnFinite_symm]
  exact_mod_cast he
