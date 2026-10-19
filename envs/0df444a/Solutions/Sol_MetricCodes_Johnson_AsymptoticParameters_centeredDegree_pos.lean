-- Prove2me | solution 1 for MetricCodes.Johnson.AsymptoticParameters.centeredDegree_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:29.660979+00:00
-- url     : https://prove2.me/submissions/c46212c0-adad-4751-a06e-e65b2c58a392

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
    0 < centeredDegree u := by
  unfold centeredDegree
  nlinarith [h.degree_lt_weight, h.weight_lt_half]
end MetricCodes.Johnson.AsymptoticParameters
