-- Prove2me | solution 1 for HunterPDE.Harmonic.sphereAverage_mono_of_laplacian_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-09T14:25:29.063621+00:00
-- url     : https://prove2.me/submissions/f70de806-dfab-4ea9-9cb3-df58c6bfe09d

import Theorems.Thm_HunterPDE_Harmonic_sphereAverage_continuousOn
import Theorems.Thm_HunterPDE_Harmonic_hasDerivAt_sphereAverage_radial
import Theorems.Thm_HunterPDE_Harmonic_sphereAverage_radial_eq_ball_laplacian
import Mathlib.Analysis.Calculus.Deriv.MeanValue

open MeasureTheory Set HunterPDE.Harmonic
set_option autoImplicit false

theorem solution {n : ℕ} (hn : 0 < n) {u : EuclideanSpace ℝ (Fin n) → ℝ}
    {x : EuclideanSpace ℝ (Fin n)} {r : ℝ} (hr : 0 < r)
    (hu : ∀ y ∈ Metric.closedBall x r, ContDiffAt ℝ 2 u y)
    (hΔ : ∀ y ∈ Metric.ball x r, 0 ≤ Laplacian.laplacian u y) :
    MonotoneOn (sphereAverage u x) (Icc 0 r) := by
  have hc : ContinuousOn u (Metric.closedBall x r) :=
    fun y hy => (hu y hy).continuousAt.continuousWithinAt
  have hd : ∀ t ∈ Ioo 0 r, HasDerivAt (sphereAverage u x)
      ((t / (n : ℝ)) * (⨍ y in Metric.ball x t, Laplacian.laplacian u y)) t := by
    intro t ht
    have hsub : Metric.closedBall x t ⊆ Metric.closedBall x r :=
      Metric.closedBall_subset_closedBall ht.2.le
    have htC : ∀ y ∈ Metric.closedBall x t, ContDiffAt ℝ 2 u y :=
      fun y hy => hu y (hsub hy)
    have hh := hasDerivAt_sphereAverage_radial hn ht.1
      (fun y hy => (htC y hy).of_le (by norm_num))
    rw [sphereAverage_radial_eq_ball_laplacian hn ht.1 htC] at hh
    exact hh
  apply monotoneOn_of_deriv_nonneg (convex_Icc 0 r)
    (sphereAverage_continuousOn hr.le hc)
  · intro t ht
    rw [interior_Icc] at ht
    exact (hd t ht).differentiableAt.differentiableWithinAt
  · intro t ht
    rw [interior_Icc] at ht
    rw [(hd t ht).deriv, setAverage_eq, smul_eq_mul]
    apply mul_nonneg (div_nonneg ht.1.le (Nat.cast_nonneg n))
    apply mul_nonneg (inv_nonneg.mpr measureReal_nonneg)
    exact setIntegral_nonneg measurableSet_ball
      (fun y hy => hΔ y ((Metric.ball_subset_ball ht.2.le) hy))
