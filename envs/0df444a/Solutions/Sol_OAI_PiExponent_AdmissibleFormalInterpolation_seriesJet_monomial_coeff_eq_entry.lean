-- Prove2me | solution 1 for OAI.PiExponent.AdmissibleFormalInterpolation.seriesJet_monomial_coeff_eq_entry
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-16T16:35:49.142285+00:00
-- url     : https://prove2.me/submissions/bfacd5f9-1ad8-435d-baca-5f99ca0f2c7c

import Theorems.Thm_OAI_PiExponent_AdmissibleFormalInterpolation_seriesJet_monomial_eq_explicitProduct
import Theorems.Thm_OAI_PiExponent_AdmissibleFormalInterpolation_explicitProduct_coeff_eq_entry

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.AdmissibleFormalInterpolation

theorem solution
    {m : ℕ} (j s : ℕ) (r : Fin m → ℂ) (G : Fin m → Polynomial ℂ)
    (h : ℕ) (a b : Fin m → ℕ) :
  MvPowerSeries.coeff (InterpolationMatrix.exponentVector (Fin.cases s b))
      (seriesJet (fun i => (j : ℂ) * r i) (fun i => (G i : PowerSeries ℂ))
        (MvPolynomial.monomial (InterpolationMatrix.exponentVector (Fin.cases h a)) 1)) =
    InterpolationMatrix.entry r G j s b h a := by
  rw [OAI.PiExponent.AdmissibleFormalInterpolation.seriesJet_monomial_eq_explicitProduct,
    OAI.PiExponent.AdmissibleFormalInterpolation.explicitProduct_coeff_eq_entry]