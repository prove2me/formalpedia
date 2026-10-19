-- Prove2me | solution 1 for MetricCodes.MRRW.hasDerivAt_mrrwObjective_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:30.949776+00:00
-- url     : https://prove2.me/submissions/7e740ad0-d94e-4892-8235-e9577892262e

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_MRRW_hasDerivAt_mrrwG_sq_zero
import Theorems.Thm_MetricCodes_MRRW_hasDerivAt_mrrwG_boundary_quadratic_zero

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open MetricCodes
open MetricCodes.MRRW
noncomputable section
set_option autoImplicit false
open Filter Topology
open scoped Topology
namespace MetricCodes.MRRW
theorem _root_.solution
    {δ : ℝ} (hδ : 0 < δ) (hhalf : δ < (1 : ℝ) / 2) :
    HasDerivAt (MetricCodes.Johnson.mrrwObjective δ)
      (-lowerEndpointDerivative δ) 0 := by
  unfold MetricCodes.Johnson.mrrwObjective
  change
    HasDerivAt
      (((fun _ : ℝ => (1 : ℝ)) +
        (fun r : ℝ => MetricCodes.Johnson.mrrwG (r ^ 2))) -
        (fun r : ℝ =>
          MetricCodes.Johnson.mrrwG (r ^ 2 + 2 * δ * r + 2 * δ)))
      (-lowerEndpointDerivative δ) 0
  simpa using
    ((hasDerivAt_const (x := (0 : ℝ)) (1 : ℝ)).add
      hasDerivAt_mrrwG_sq_zero).sub
        (hasDerivAt_mrrwG_boundary_quadratic_zero hδ hhalf)
end MetricCodes.MRRW
