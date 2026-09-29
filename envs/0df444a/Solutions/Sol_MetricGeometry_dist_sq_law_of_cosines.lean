-- Prove2me | solution 1 for MetricGeometry.dist_sq_law_of_cosines
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-28T00:08:19.183568+00:00
-- url     : https://prove2.me/submissions/a463b9b8-8945-4337-a2e9-b1d5bbcfa449

import Definitions.Def_metric_geodesic_angle
import Theorems.Thm_MetricGeometry_cos_comparisonAngle

open MetricGeometry

theorem solution {X : Type*} [PseudoMetricSpace X] (p x y : X) :
    dist x y ^ 2 = dist p x ^ 2 + dist p y ^ 2
      - 2 * dist p x * dist p y * Real.cos (comparisonAngle p x y) := by
  rcases eq_or_ne (dist p x) 0 with hx | hx
  · have h1 : dist x y = dist p y := by
      refine le_antisymm ?_ ?_
      · calc dist x y ≤ dist x p + dist p y := dist_triangle _ _ _
          _ = dist p y := by rw [dist_comm x p, hx, zero_add]
      · calc dist p y ≤ dist p x + dist x y := dist_triangle _ _ _
          _ = dist x y := by rw [hx, zero_add]
    rw [h1, hx]; ring
  rcases eq_or_ne (dist p y) 0 with hy | hy
  · have h1 : dist x y = dist p x := by
      refine le_antisymm ?_ ?_
      · calc dist x y ≤ dist x p + dist p y := dist_triangle _ _ _
          _ = dist p x := by rw [dist_comm x p, hy, add_zero]
      · calc dist p x ≤ dist p y + dist y x := dist_triangle _ _ _
          _ = dist x y := by rw [hy, zero_add, dist_comm y x]
    rw [h1, hy]; ring
  rw [MetricGeometry.cos_comparisonAngle p x y hx hy]
  field_simp
  ring
