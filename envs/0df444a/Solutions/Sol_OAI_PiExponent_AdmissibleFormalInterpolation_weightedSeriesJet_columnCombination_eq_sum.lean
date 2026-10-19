-- Prove2me | solution 1 for OAI.PiExponent.AdmissibleFormalInterpolation.weightedSeriesJet_columnCombination_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-16T13:10:19.453148+00:00
-- url     : https://prove2.me/submissions/864c723b-a6e5-463e-9507-1658b584a9c1

import Definitions.Def_OAI_PiExponent_ColumnCombination

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.AdmissibleFormalInterpolation

theorem solution
    {m : ℕ} (K : ℕ) (w0 v0 theta : ℝ) (w : Fin m → ℝ) (H : ℝ)
    (r : Fin m → ℂ) (G : Fin m → Polynomial ℂ)
    (x : InterpolationMatrix.Column w0 w H → ℂ)
    (rho : InterpolationMatrix.Row K v0 theta w H) :
  weightedSeriesJet v0 (fun i => w i / theta) H
      (fun i => (rho.1.val : ℂ) * r i) (fun i => (G i : PowerSeries ℂ))
      (columnCombination w0 w H x) rho.2 =
    ∑ c : InterpolationMatrix.Column w0 w H,
      x c * weightedSeriesJet v0 (fun i => w i / theta) H
        (fun i => (rho.1.val : ℂ) * r i) (fun i => (G i : PowerSeries ℂ))
        (columnMonomial w0 w H c) rho.2 := by
  classical
  simp [weightedSeriesJet, seriesJet, columnCombination,
    MvPowerSeries.algebraMap_apply, MvPowerSeries.coeff_C_mul]