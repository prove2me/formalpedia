-- Prove2me | solution 1 for HunterPDE.Harmonic.sphereAverage_radial_eq_ball_laplacian
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-08T22:51:53.004903+00:00
-- url     : https://prove2.me/submissions/f5a6449f-425c-4de9-975c-dd38fd11d631

import Theorems.Thm_MeasureTheory_average_covector_flux_ball
import Mathlib.Analysis.InnerProductSpace.Harmonic.Basic

open MeasureTheory Set

theorem solution {n : ℕ} (hn : 0 < n)
    {u : EuclideanSpace ℝ (Fin n) → ℝ} {x : EuclideanSpace ℝ (Fin n)}
    {r : ℝ} (hr : 0 < r)
    (hu : ∀ y ∈ Metric.closedBall x r, ContDiffAt ℝ 2 u y) :
    (⨍ ω : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
      fderiv ℝ u (x + r • ω.1) ω.1 ∂(volume.toSphere)) =
      (r / (n : ℝ)) *
        (⨍ y in Metric.ball x r, Laplacian.laplacian u y) := by
  have hDu : ∀ y ∈ Metric.closedBall x r, ContDiffAt ℝ 1 (fderiv ℝ u) y := by
    intro y hy
    exact (hu y hy).fderiv_right (by norm_num)
  have hflux := MeasureTheory.average_covector_flux_ball hn hr hDu
  simpa only [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis u
      (EuclideanSpace.basisFun (Fin n) ℝ), iteratedFDeriv_two_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one] using hflux
