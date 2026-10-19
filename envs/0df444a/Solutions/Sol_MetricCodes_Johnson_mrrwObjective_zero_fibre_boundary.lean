-- Prove2me | solution 1 for MetricCodes.Johnson.mrrwObjective_zero_fibre_boundary
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:30.299848+00:00
-- url     : https://prove2.me/submissions/da81d4dc-ca1a-4449-a540-4b6349be7fce

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Johnson_mrrwG_variance
import Theorems.Thm_MetricCodes_Johnson_zero_fibre_boundary_variance

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open MetricCodes
open MetricCodes.Johnson
noncomputable section
open scoped BigOperators InnerProductSpace Matrix
namespace MetricCodes.Johnson
theorem _root_.solution {δ α u : ℝ}
    (hu : 0 < u) (hua : u < α)
    (ha : α < (1 : ℝ) / 2)
    (hboundary :
      spectralLimit α 0 0 u = asymptoticThreshold δ α) :
    mrrwObjective δ (2 * Real.sqrt (u * (1 - u))) =
      shellRate α 0 0 u := by
  have huone : 0 < 1 - u := by linarith
  have hsquare := Real.sq_sqrt (mul_pos hu huone).le
  have hvariance :
      (2 * Real.sqrt (u * (1 - u))) ^ 2 =
        4 * u * (1 - u) := by
    nlinarith [hsquare]
  have hboundary' :=
    zero_fibre_boundary_variance hu hua ha hboundary
  have hargument :
      4 * u * (1 - u) +
        2 * δ * (2 * Real.sqrt (u * (1 - u))) + 2 * δ =
        4 * α * (1 - α) := by
    nlinarith [hboundary', hvariance]
  unfold mrrwObjective
  rw [hvariance, hargument,
    mrrwG_variance (by linarith : u ≤ (1 : ℝ) / 2),
    mrrwG_variance ha.le, shellRate_zero_fibre]
  ring
end MetricCodes.Johnson
