-- Prove2me | solution 1 for OAI.PiExponent.AdmissibleFormalInterpolation.weightedSeriesJet_columnMonomial_eq_matrix_entry
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-16T13:14:37.554203+00:00
-- url     : https://prove2.me/submissions/f12ee91e-8649-41ef-9ef8-4f0680d1c963
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_OAI_PiExponent_ColumnCombination
import Theorems.Thm_OAI_PiExponent_AdmissibleFormalInterpolation_seriesJet_monomial_coeff_eq_entry

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.AdmissibleFormalInterpolation

theorem solution
    {m : ℕ} (K : ℕ) (w0 v0 theta : ℝ) (w : Fin m → ℝ) (H : ℝ)
    (r : Fin m → ℂ) (G : Fin m → Polynomial ℂ)
    (x : InterpolationMatrix.Column w0 w H → ℂ)
    (rho : InterpolationMatrix.Row K v0 theta w H)
    (c : InterpolationMatrix.Column w0 w H) :
  weightedSeriesJet v0 (fun i => w i / theta) H
      (fun i => (rho.1.val : ℂ) * r i) (fun i => (G i : PowerSeries ℂ))
      (columnMonomial w0 w H c) rho.2 =
    InterpolationMatrix.matrix K w0 v0 theta w H r G rho c := by
  change MvPowerSeries.coeff (InterpolationMatrix.exponentVector rho.2.1)
      (seriesJet (fun i => (rho.1.val : ℂ) * r i)
        (fun i => (G i : PowerSeries ℂ))
        (MvPolynomial.monomial (InterpolationMatrix.exponentVector c.1) 1)) =
    InterpolationMatrix.entry r G rho.1.val (rho.2.1 0)
      (fun i => rho.2.1 i.succ) (c.1 0) (fun i => c.1 i.succ)
  have hr : rho.2.1 = Fin.cases (rho.2.1 0) (fun i => rho.2.1 i.succ) := by
    funext i
    exact Fin.cases (by rfl) (fun j => by rfl) i
  have hc : c.1 = Fin.cases (c.1 0) (fun i => c.1 i.succ) := by
    funext i
    exact Fin.cases (by rfl) (fun j => by rfl) i
  simpa only [← hr, ← hc] using
    (OAI.PiExponent.AdmissibleFormalInterpolation.seriesJet_monomial_coeff_eq_entry
      (m := m) rho.1.val (rho.2.1 0) r G (c.1 0)
      (fun i => c.1 i.succ) (fun i => rho.2.1 i.succ))
