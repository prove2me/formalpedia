-- Prove2me | solution 1 for OAI.PiExponent.LogarithmicJetIdeals.coeff_finsupp_prod_linear_part
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-20T18:27:16.582895+00:00
-- url     : https://prove2.me/submissions/c832362d-5fd6-42c4-a9e2-4a9a1a6317e6

import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_coeff_finsupp_prod_linear_part_finite

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
    MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm e)
      (a.prod fun i k => MvPowerSeries.X i ^ k) := by
  classical
  let σ := Σ i : ι, Fin (a i)
  let f : σ -> MvPowerSeries ι K := fun x => R x.1
  let v : σ -> ι := fun x => x.1
  have hlin : ∀ (x : σ) (d : ι -> Nat), (∑ k : ι, d k) <= 1 ->
      MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm d) (f x) =
        MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm d) (MvPowerSeries.X (v x)) := by
    intro x d hd
    exact hR x.1 d hd
  have hdeg : (∑ k : ι, e k) = Fintype.card σ := by
    simpa [σ, Fintype.card_sigma] using he
  have h := OAI.PiExponent.LogarithmicJetIdeals.coeff_finsupp_prod_linear_part_finite
    (R := f) (v := v) hlin e hdeg
  rw [Finsupp.prod_pow, Finsupp.prod_pow]
  simpa [σ, f, v, Fintype.prod_sigma] using h