-- Prove2me | solution 1 for MetricCodes.Johnson.AsymptoticParameters.sigma_sq_sub_degree_sq_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:30.299848+00:00
-- url     : https://prove2.me/submissions/55e8c47b-3deb-43af-956c-cb670a6aef65

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Johnson_AsymptoticParameters_centeredDegree_pos
import Theorems.Thm_MetricCodes_Johnson_AsymptoticParameters_centeredSigma_gt_degree
import Theorems.Thm_MetricCodes_Johnson_AsymptoticParameters_centeredSigma_pos

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
    0 < centeredSigma β γ ^ 2 - centeredDegree u ^ 2 := by
  have hleft : 0 < centeredSigma β γ - centeredDegree u :=
    sub_pos.mpr h.centeredSigma_gt_degree
  have hright : 0 < centeredSigma β γ + centeredDegree u :=
    add_pos h.centeredSigma_pos h.centeredDegree_pos
  nlinarith [mul_pos hleft hright]
end MetricCodes.Johnson.AsymptoticParameters
