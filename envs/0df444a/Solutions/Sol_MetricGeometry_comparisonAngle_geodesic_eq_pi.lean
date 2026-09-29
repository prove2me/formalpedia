-- Prove2me | solution 1 for MetricGeometry.comparisonAngle_geodesic_eq_pi
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-27T21:27:19.391058+00:00
-- url     : https://prove2.me/submissions/b6d187c5-bba9-466a-8fa8-14409cdb8f9d

import Definitions.Def_metric_geodesic_angle

open MetricGeometry

theorem solution {X : Type*} [MetricSpace X] (g : ℝ → X) (x y : X)
    (h : IsGeodesicSegment g x y) (hxy : x ≠ y) (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1) :
    comparisonAngle (g t) x y = Real.pi := by
  obtain ⟨h0, h1, hd⟩ := h
  have hD : 0 < dist x y := dist_pos.mpr hxy
  have e1 : dist (g t) x = t * dist x y := by
    have := hd t ⟨le_of_lt ht0, le_of_lt ht1⟩ 0 (by norm_num)
    rw [h0] at this
    rw [this, abs_of_nonneg (by linarith)]; ring
  have e2 : dist (g t) y = (1 - t) * dist x y := by
    have := hd t ⟨le_of_lt ht0, le_of_lt ht1⟩ 1 (by norm_num)
    rw [h1] at this
    rw [this, abs_of_nonpos (by linarith)]; ring
  unfold comparisonAngle
  rw [e1, e2]
  have hne : (2 : ℝ) * (t * dist x y) * ((1 - t) * dist x y) ≠ 0 := by positivity
  rw [show ((t * dist x y) ^ 2 + ((1 - t) * dist x y) ^ 2 - dist x y ^ 2)
      = -(2 * (t * dist x y) * ((1 - t) * dist x y)) from by ring]
  rw [neg_div, div_self hne, Real.arccos_neg_one]
