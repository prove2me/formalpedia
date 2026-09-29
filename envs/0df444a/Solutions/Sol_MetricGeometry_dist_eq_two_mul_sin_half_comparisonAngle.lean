-- Prove2me | solution 1 for MetricGeometry.dist_eq_two_mul_sin_half_comparisonAngle
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-28T00:08:20.633397+00:00
-- url     : https://prove2.me/submissions/6822d795-a5c4-448d-9748-b6148203982a

import Definitions.Def_metric_geodesic_angle
import Theorems.Thm_MetricGeometry_comparisonAngle_mem_Icc
import Theorems.Thm_MetricGeometry_dist_sq_law_of_cosines

open MetricGeometry

theorem solution {X : Type*} [PseudoMetricSpace X] (p x y : X) (L : ℝ)
    (hx : dist p x = L) (hy : dist p y = L) :
    dist x y = 2 * L * Real.sin (comparisonAngle p x y / 2) := by
  have hL : 0 ≤ L := hx ▸ dist_nonneg
  have hrange := MetricGeometry.comparisonAngle_mem_Icc p x y
  have hhalf : 0 ≤ comparisonAngle p x y / 2 := by linarith [hrange.1]
  have hhalf2 : comparisonAngle p x y / 2 ≤ Real.pi := by
    linarith [hrange.2, Real.pi_pos]
  have hsin : 0 ≤ Real.sin (comparisonAngle p x y / 2) := Real.sin_nonneg_of_nonneg_of_le_pi hhalf hhalf2
  have hcos : Real.cos (comparisonAngle p x y)
      = 1 - 2 * Real.sin (comparisonAngle p x y / 2) ^ 2 := by
    have hgen : ∀ t : ℝ, Real.cos (2 * t) = 1 - 2 * Real.sin t ^ 2 := by
      intro t; rw [Real.cos_two_mul']; nlinarith [Real.sin_sq_add_cos_sq t]
    have := hgen (comparisonAngle p x y / 2)
    rwa [show 2 * (comparisonAngle p x y / 2) = comparisonAngle p x y from by ring] at this
  have hsq : dist x y ^ 2 = (2 * L * Real.sin (comparisonAngle p x y / 2)) ^ 2 := by
    rw [MetricGeometry.dist_sq_law_of_cosines p x y, hx, hy, hcos]; ring
  have h1 : 0 ≤ dist x y := dist_nonneg
  have h2 : 0 ≤ 2 * L * Real.sin (comparisonAngle p x y / 2) := by positivity
  nlinarith [hsq, h1, h2]
