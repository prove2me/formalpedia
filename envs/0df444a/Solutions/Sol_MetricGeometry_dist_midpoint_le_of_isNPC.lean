-- Prove2me | solution 1 for MetricGeometry.dist_midpoint_le_of_isNPC
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-27T20:55:25.212249+00:00
-- url     : https://prove2.me/submissions/b0182eff-695c-46da-b79c-fa91d731eb2d

import Definitions.Def_metric_npc_cone

open MetricGeometry

-- midpoint convexity of the distance function
theorem solution {X : Type*} [PseudoMetricSpace X] (h : IsNPC X) (x y m z : X)
    (hm : IsMidpoint m x y) :
    dist m z ≤ (dist x z + dist y z) / 2 := by
  have hcn := h x y m z hm
  have htri : |dist x z - dist y z| ≤ dist x y := abs_dist_sub_le x y z
  have hsq : (dist x z - dist y z) ^ 2 ≤ dist x y ^ 2 := by
    have h1 : |dist x z - dist y z| ^ 2 = (dist x z - dist y z) ^ 2 := sq_abs _
    nlinarith [abs_nonneg (dist x z - dist y z), dist_nonneg (x := x) (y := y), htri, h1]
  have hmz : (0 : ℝ) ≤ dist m z := dist_nonneg
  have hxz : (0 : ℝ) ≤ dist x z := dist_nonneg
  have hyz : (0 : ℝ) ≤ dist y z := dist_nonneg
  nlinarith [hcn, hsq, hmz, hxz, hyz, sq_nonneg (dist m z - (dist x z + dist y z) / 2)]
