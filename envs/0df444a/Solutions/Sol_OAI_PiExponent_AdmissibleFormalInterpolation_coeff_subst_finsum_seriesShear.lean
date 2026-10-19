-- Prove2me | solution 1 for OAI.PiExponent.AdmissibleFormalInterpolation.coeff_subst_finsum_seriesShear
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-18T07:41:42.368095+00:00
-- url     : https://prove2.me/submissions/30735ece-0eed-4059-905f-fd282ad1d6b6

import Definitions.Def_OAI_PiExponent_WeightedJetShear
import Mathlib.RingTheory.MvPowerSeries.Substitution

open OAI.PiExponent OAI.PiExponent.AdmissibleFormalInterpolation
open scoped BigOperators

theorem solution
    {m : ℕ} (D : Fin m → PowerSeries ℂ)
    (hD0 : ∀ i, PowerSeries.coeff 0 (D i) = 0)
    (G : MvPowerSeries (Fin (m + 1)) ℂ)
    (b : Fin (m + 1) → ℕ) :
    MvPowerSeries.coeff (InterpolationMatrix.exponentVector b)
        (MvPowerSeries.subst
          (Fin.cases (MvPowerSeries.X 0)
            (fun i => MvPowerSeries.X i.succ + liftLogSeries m (D i))) G) =
      ∑ᶠ a : Fin (m + 1) → ℕ,
        MvPowerSeries.coeff (InterpolationMatrix.exponentVector a) G *
          MvPowerSeries.coeff (InterpolationMatrix.exponentVector b)
            (seriesShear D
              (MvPolynomial.monomial (InterpolationMatrix.exponentVector a) 1)) := by
  classical
  let s : Fin (m + 1) → MvPowerSeries (Fin (m + 1)) ℂ :=
    Fin.cases (MvPowerSeries.X 0)
      (fun i => MvPowerSeries.X i.succ + liftLogSeries m (D i))
  have hLift (j : Fin m) :
      MvPowerSeries.constantCoeff (liftLogSeries m (D j)) = 0 := by
    rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
    have h := MvPowerSeries.coeff_coeff_finSuccEquiv
      (p := liftLogSeries m (D j)) (k := 0) (x := 0)
    simpa [liftLogSeries, PowerSeries.coeff_map, hD0 j] using h.symm
  have hs : ∀ i, MvPowerSeries.constantCoeff (s i) = 0 := by
    intro i
    refine Fin.cases ?_ ?_ i
    · simp [s]
    · simp [s, hLift]
  have hsubst : MvPowerSeries.HasSubst s :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero hs
  rw [MvPowerSeries.coeff_subst hsubst G (InterpolationMatrix.exponentVector b)]
  rw [← finsum_comp_equiv
    (Finsupp.equivFunOnFinite (α := Fin (m + 1)) (M := ℕ)).symm]
  apply finsum_congr
  intro a
  simp [s, InterpolationMatrix.exponentVector, seriesShear,
    MvPolynomial.aeval_monomial]
