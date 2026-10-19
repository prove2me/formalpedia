-- Prove2me | solution 1 for MetricCodes.MRRW.interior_boundary_weight_gt_distance
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:30.949776+00:00
-- url     : https://prove2.me/submissions/eb06a94d-6c14-4760-8a11-91620f1ffd05

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Johnson_zero_fibre_boundary_variance

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open MetricCodes
open MetricCodes.MRRW
noncomputable section
set_option autoImplicit false
open Filter Topology
open scoped Topology
namespace MetricCodes.MRRW
theorem _root_.solution {δ a u : ℝ}
    (hδ : 0 < δ)
    (hu : 0 < u) (hua : u < a) (ha : a < (1 : ℝ) / 2)
    (hboundary :
      MetricCodes.Johnson.spectralLimit a 0 0 u =
        MetricCodes.Johnson.asymptoticThreshold δ a) :
    δ / 2 < a := by
  have ha0 : 0 < a := lt_trans hu hua
  have huone : 0 < 1 - u := by linarith
  have hs : 0 < Real.sqrt (u * (1 - u)) :=
    Real.sqrt_pos.mpr (mul_pos hu huone)
  have hvariance := MetricCodes.Johnson.zero_fibre_boundary_variance
    hu hua ha hboundary
  have hcross : 0 < δ * (2 * Real.sqrt (u * (1 - u))) := by
    positivity
  nlinarith [sq_nonneg (2 * Real.sqrt (u * (1 - u))),
    sq_pos_of_pos ha0]
end MetricCodes.MRRW
