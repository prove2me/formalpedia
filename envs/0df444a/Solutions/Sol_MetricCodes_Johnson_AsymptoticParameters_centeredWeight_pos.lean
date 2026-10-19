-- Prove2me | solution 1 for MetricCodes.Johnson.AsymptoticParameters.centeredWeight_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:30.299848+00:00
-- url     : https://prove2.me/submissions/ce68f2b2-1f04-43a8-bebd-66f377c1d3d2

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open MetricCodes
open MetricCodes.Johnson
noncomputable section
open scoped BigOperators InnerProductSpace Matrix
open MetricCodes.Johnson.AsymptoticParameters
variable {δ α β γ u : ℝ}
namespace MetricCodes.Johnson.AsymptoticParameters
theorem _root_.solution
    (h : AsymptoticParameters δ α β γ u) :
    0 < centeredWeight α := by
  unfold centeredWeight
  nlinarith [h.weight_lt_half]
end MetricCodes.Johnson.AsymptoticParameters
