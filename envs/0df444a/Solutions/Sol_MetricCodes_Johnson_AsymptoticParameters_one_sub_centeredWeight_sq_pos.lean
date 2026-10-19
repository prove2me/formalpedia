-- Prove2me | solution 1 for MetricCodes.Johnson.AsymptoticParameters.one_sub_centeredWeight_sq_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:30.299848+00:00
-- url     : https://prove2.me/submissions/87ceaffb-4ba0-4b95-9d57-e26e96c75269

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Johnson_AsymptoticParameters_weight_complement_pos

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
    0 < 1 - centeredWeight α ^ 2 := by
  have hprod : 0 < α * (1 - α) :=
    mul_pos h.weight_pos h.weight_complement_pos
  unfold centeredWeight
  nlinarith
end MetricCodes.Johnson.AsymptoticParameters
