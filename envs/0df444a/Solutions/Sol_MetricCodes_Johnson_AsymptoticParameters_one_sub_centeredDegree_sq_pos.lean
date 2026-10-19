-- Prove2me | solution 1 for MetricCodes.Johnson.AsymptoticParameters.one_sub_centeredDegree_sq_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:30.299848+00:00
-- url     : https://prove2.me/submissions/53ce79f9-b9e6-49b1-955b-baa683b0ea86

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Johnson_AsymptoticParameters_degree_pos

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
    0 < 1 - centeredDegree u ^ 2 := by
  have huone : 0 < 1 - u := by
    nlinarith [h.degree_lt_weight, h.weight_lt_half]
  have hprod : 0 < u * (1 - u) := mul_pos h.degree_pos huone
  unfold centeredDegree
  nlinarith
end MetricCodes.Johnson.AsymptoticParameters
