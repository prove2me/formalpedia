-- Prove2me | solution 1 for HunterPDE.Harmonic.hasDerivAt_sphereAverage_zero
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-08T19:16:25.713485+00:00
-- url     : https://prove2.me/submissions/be6062e6-3d9c-4287-a653-55b623403f63

import Theorems.Thm_HunterPDE_Harmonic_hasDerivAt_sphereAverage_radial
import Theorems.Thm_HunterPDE_Harmonic_sphereAverage_radial_eq_ball_laplacian
import Mathlib.Tactic.NormNum

open MeasureTheory Set
open HunterPDE.Harmonic

theorem solution {n : ℕ} (hn : 0 < n) {u : EuclideanSpace ℝ (Fin n) → ℝ}
    {x : EuclideanSpace ℝ (Fin n)} {r : ℝ} (hr : 0 < r)
    (hu : InnerProductSpace.HarmonicOnNhd u (Metric.closedBall x r)) :
    HasDerivAt (sphereAverage u x) 0 r := by
  have hC2 : ∀ y ∈ Metric.closedBall x r, ContDiffAt ℝ 2 u y :=
    fun y hy => (hu y hy).1
  have hC1 : ∀ y ∈ Metric.closedBall x r, ContDiffAt ℝ 1 u y := by
    intro y hy
    exact (hC2 y hy).of_le (by norm_num)
  have hLap : ∀ y ∈ Metric.ball x r, Laplacian.laplacian u y = 0 := by
    intro y hy
    exact (hu y (Metric.ball_subset_closedBall hy)).2.eq_of_nhds
  have hAvg : (⨍ y in Metric.ball x r, Laplacian.laplacian u y) = 0 := by
    calc
      (⨍ y in Metric.ball x r, Laplacian.laplacian u y) =
          (⨍ _y in Metric.ball x r, (0 : ℝ)) := by
            apply average_congr
            exact (ae_restrict_iff' measurableSet_ball).2 (Filter.Eventually.of_forall hLap)
      _ = 0 := average_zero _
  have hFlux := sphereAverage_radial_eq_ball_laplacian hn hr hC2
  rw [hAvg, mul_zero] at hFlux
  simpa only [hFlux] using hasDerivAt_sphereAverage_radial hn hr hC1
