-- Prove2me | solution 1 for MetricGeometry.eq_of_isMidpoint_of_isNPC
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-27T18:32:30.883864+00:00
-- url     : https://prove2.me/submissions/8928e3d3-3935-4d61-a73f-1de84eae8a67

import Definitions.Def_metric_npc_cone

open MetricGeometry

theorem solution {X : Type*} [MetricSpace X] (h : IsNPC X)
    (m m' x y : X) (hm : IsMidpoint m x y) (hm' : IsMidpoint m' x y) :
    m = m' := by
  have hcn := h x y m m' hm
  obtain ⟨ha, hb⟩ := hm'
  have hy : dist y m' = dist x y / 2 := by rw [dist_comm]; exact hb
  rw [ha, hy] at hcn
  have hd : (0 : ℝ) ≤ dist m m' := dist_nonneg
  have hzero : dist m m' = 0 := by nlinarith [hcn, hd]
  exact dist_eq_zero.mp hzero
