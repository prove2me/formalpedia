-- Prove2me | solution 1 for OAI.PiExponent.AdmissibleFormalInterpolation.seriesShear_coeff_subst_eq_sum_of_weight_nondecreasing
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-18T07:10:38.900401+00:00
-- url     : https://prove2.me/submissions/16dd339c-5ae4-45a8-aa21-f5770c01f15d

import Definitions.Def_OAI_PiExponent_WeightedJetShear
import Mathlib.RingTheory.MvPowerSeries.Substitution
import Theorems.Thm_OAI_PiExponent_AdmissibleFormalInterpolation_coeff_subst_finsum_seriesShear
import Theorems.Thm_OAI_PiExponent_AdmissibleFormalInterpolation_weighted_finsum_cutoff

open OAI.PiExponent OAI.PiExponent.AdmissibleFormalInterpolation
open scoped BigOperators

theorem solution
    {m : ℕ} (v0 : ℝ) (u : Fin m → ℝ) (H : ℝ)
    (D : Fin m → PowerSeries ℂ)
    (hv0 : 0 < v0) (hu : ∀ i, 0 < u i) (hH : 0 < H)
    (hD0 : ∀ i, PowerSeries.coeff 0 (D i) = 0)
    (htri : ∀ (a b : Fin (m + 1) → ℕ),
      (∑ i, Fin.cases v0 u i * (b i : ℝ)) <
        (∑ i, Fin.cases v0 u i * (a i : ℝ)) →
      MvPowerSeries.coeff (InterpolationMatrix.exponentVector b)
        (seriesShear D
          (MvPolynomial.monomial (InterpolationMatrix.exponentVector a) 1)) = 0)
    (G : MvPowerSeries (Fin (m + 1)) ℂ)
    (b : ↥(strictWeightedSimplex (Fin.cases v0 u) H)) :
    (∑ a : ↥(strictWeightedSimplex (Fin.cases v0 u) H),
      MvPowerSeries.coeff (InterpolationMatrix.exponentVector a.val) G *
        MvPowerSeries.coeff (InterpolationMatrix.exponentVector b.val)
          (seriesShear D
            (MvPolynomial.monomial (InterpolationMatrix.exponentVector a.val) 1))) =
      MvPowerSeries.coeff (InterpolationMatrix.exponentVector b.val)
        (MvPowerSeries.subst
          (Fin.cases (MvPowerSeries.X 0)
            (fun i => MvPowerSeries.X i.succ + liftLogSeries m (D i))) G) := by
  calc
    (∑ a : ↥(strictWeightedSimplex (Fin.cases v0 u) H),
        MvPowerSeries.coeff (InterpolationMatrix.exponentVector a.val) G *
          MvPowerSeries.coeff (InterpolationMatrix.exponentVector b.val)
            (seriesShear D
              (MvPolynomial.monomial (InterpolationMatrix.exponentVector a.val) 1))) =
        ∑ᶠ a : Fin (m + 1) → ℕ,
          MvPowerSeries.coeff (InterpolationMatrix.exponentVector a) G *
            MvPowerSeries.coeff (InterpolationMatrix.exponentVector b.val)
              (seriesShear D
                (MvPolynomial.monomial (InterpolationMatrix.exponentVector a) 1)) := by
      exact (OAI.PiExponent.AdmissibleFormalInterpolation.weighted_finsum_cutoff
        v0 u H D hv0 hu hH hD0 htri G b).symm
    _ = MvPowerSeries.coeff (InterpolationMatrix.exponentVector b.val)
          (MvPowerSeries.subst
            (Fin.cases (MvPowerSeries.X 0)
              (fun i => MvPowerSeries.X i.succ + liftLogSeries m (D i))) G) := by
      exact (OAI.PiExponent.AdmissibleFormalInterpolation.coeff_subst_finsum_seriesShear
        D hD0 G b.val).symm
