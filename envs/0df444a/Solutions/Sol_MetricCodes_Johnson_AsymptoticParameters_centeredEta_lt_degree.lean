-- Prove2me | solution 1 for MetricCodes.Johnson.AsymptoticParameters.centeredEta_lt_degree
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:30.299848+00:00
-- url     : https://prove2.me/submissions/dc326240-918d-4682-973d-9d7fa8099d08

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
    centeredEta α β γ < centeredDegree u := by
  unfold centeredEta centeredDegree
  nlinarith [h.degree_lt_left]
end MetricCodes.Johnson.AsymptoticParameters
