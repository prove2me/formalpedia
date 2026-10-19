-- Prove2me | solution 1 for MetricCodes.Johnson.AsymptoticParameters.degree_sq_sub_eta_sq_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:30.299848+00:00
-- url     : https://prove2.me/submissions/7604f034-86c4-4a38-b9c2-b7f53bbf6345

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Johnson_AsymptoticParameters_centeredEta_lt_degree
import Theorems.Thm_MetricCodes_Johnson_AsymptoticParameters_neg_degree_lt_centeredEta

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
    0 < centeredDegree u ^ 2 - centeredEta α β γ ^ 2 := by
  have hleft : 0 < centeredDegree u - centeredEta α β γ :=
    sub_pos.mpr h.centeredEta_lt_degree
  have hright : 0 < centeredDegree u + centeredEta α β γ := by
    linarith [h.neg_degree_lt_centeredEta]
  nlinarith [mul_pos hleft hright]
end MetricCodes.Johnson.AsymptoticParameters
