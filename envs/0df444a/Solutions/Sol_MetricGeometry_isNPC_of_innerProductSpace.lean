-- Prove2me | solution 1 for MetricGeometry.isNPC_of_innerProductSpace
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-27T18:35:10.779032+00:00
-- url     : https://prove2.me/submissions/ddd8095c-23c4-4556-8111-20f368cc94a3

import Definitions.Def_metric_npc_cone
import Theorems.Thm_MetricGeometry_eq_midpoint_of_isMidpoint

open MetricGeometry

theorem solution (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] :
    IsNPC E := by
  intro x y m z hm
  rw [MetricGeometry.eq_midpoint_of_isMidpoint m x y hm]
  refine le_of_eq ?_
  set w := midpoint ℝ x y - z with hw
  set a := x - z with ha
  set b := y - z with hb
  have key : w + w = a + b := by
    rw [hw, ha, hb, show midpoint ℝ x y - z + (midpoint ℝ x y - z)
      = (midpoint ℝ x y + midpoint ℝ x y) - (z + z) from by abel, midpoint_add_self]
    abel
  have h4 : ‖w + w‖ ^ 2 = ‖a‖ ^ 2 + 2 * inner ℝ a b + ‖b‖ ^ 2 := by
    rw [key, norm_add_sq_real]
  have hww : ‖w + w‖ ^ 2 = 4 * ‖w‖ ^ 2 := by
    rw [show w + w = (2 : ℝ) • w from by rw [two_smul], norm_smul]
    simp
    ring
  have hsub : ‖a - b‖ ^ 2 = ‖a‖ ^ 2 - 2 * inner ℝ a b + ‖b‖ ^ 2 := norm_sub_sq_real a b
  have hxy : x - y = a - b := by rw [ha, hb]; abel
  simp only [dist_eq_norm, ← hw, ← ha, ← hb, hxy]
  nlinarith [h4, hww, hsub]
