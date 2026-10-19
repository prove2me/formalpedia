-- Prove2me | solution 1 for MetricCodes.Johnson.AsymptoticParameters.neg_degree_lt_centeredEta
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:30.299848+00:00
-- url     : https://prove2.me/submissions/a2488e97-1762-431a-a759-8aa711703c61

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
    -centeredDegree u < centeredEta α β γ := by
  unfold centeredEta centeredDegree
  nlinarith [h.degree_lt_right]
end MetricCodes.Johnson.AsymptoticParameters
