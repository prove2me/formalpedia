-- Prove2me | solution 1 for MetricCodes.MRRW.lowerEndpointRoot_lt_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:30.949776+00:00
-- url     : https://prove2.me/submissions/a6040651-e531-48da-aaba-9871edcec87d

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open MetricCodes
open MetricCodes.MRRW
noncomputable section
set_option autoImplicit false
open Filter Topology
open scoped Topology
namespace MetricCodes.MRRW
theorem _root_.solution {δ : ℝ}
    (hδ : 0 < δ) :
    lowerEndpointRoot δ < 1 := by
  unfold lowerEndpointRoot
  apply (Real.sqrt_lt' (by norm_num : (0 : ℝ) < 1)).2
  linarith
end MetricCodes.MRRW
