-- Prove2me | solution 1 for MetricCodes.Johnson.AsymptoticParameters.centeredSigma_gt_degree
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:30.299848+00:00
-- url     : https://prove2.me/submissions/7ab39d1f-b015-4353-a661-774333e394ad

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
    centeredDegree u < centeredSigma β γ := by
  unfold centeredDegree centeredSigma
  nlinarith [h.first_lt_degree]
end MetricCodes.Johnson.AsymptoticParameters
