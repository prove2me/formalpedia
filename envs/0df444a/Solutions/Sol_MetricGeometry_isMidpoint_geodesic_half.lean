-- Prove2me | solution 1 for MetricGeometry.isMidpoint_geodesic_half
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-27T21:27:18.837769+00:00
-- url     : https://prove2.me/submissions/75ebb5e0-af85-4509-a09a-6c6c2f75d1f4

import Definitions.Def_metric_geodesic_angle

open MetricGeometry

theorem solution {X : Type*} [PseudoMetricSpace X] (g : ℝ → X) (x y : X)
    (h : IsGeodesicSegment g x y) : IsMidpoint (g (1 / 2)) x y := by
  obtain ⟨h0, h1, hd⟩ := h
  constructor
  · have := hd 0 (by norm_num) (1 / 2) (by norm_num)
    rw [h0] at this
    rw [this]; norm_num; ring
  · have := hd (1 / 2) (by norm_num) 1 (by norm_num)
    rw [h1] at this
    rw [this]; norm_num; ring
