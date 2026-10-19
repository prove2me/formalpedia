-- Prove2me | solution 1 for MetricCodes.MRRW.interior_boundary_delta_relation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:30.949776+00:00
-- url     : https://prove2.me/submissions/2817fb8c-df9e-4fff-a58d-3eda360107e7

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
    (hu : 0 < u) (hua : u < a) (ha : a < (1 : ℝ) / 2)
    (hboundary :
      MetricCodes.Johnson.spectralLimit a 0 0 u =
        MetricCodes.Johnson.asymptoticThreshold δ a) :
    δ * (1 + 2 * Real.sqrt (u * (1 - u))) =
      2 * (a * (1 - a) - u * (1 - u)) := by
  have huone : 0 < 1 - u := by linarith
  have hsquare := Real.sq_sqrt (mul_pos hu huone).le
  have hvariance := MetricCodes.Johnson.zero_fibre_boundary_variance
    hu hua ha hboundary
  nlinarith
end MetricCodes.MRRW
