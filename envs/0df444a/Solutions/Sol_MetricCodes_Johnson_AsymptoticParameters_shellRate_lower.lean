-- Prove2me | solution 1 for MetricCodes.Johnson.AsymptoticParameters.shellRate_lower
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:30.299848+00:00
-- url     : https://prove2.me/submissions/abac9d8f-1441-435a-b53e-59cd20617596

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_binaryEntropy_nonneg
import Theorems.Thm_MetricCodes_Hamming_binaryEntropy_le_one
import Theorems.Thm_MetricCodes_Johnson_binaryEntropy_le_one
import Theorems.Thm_MetricCodes_Johnson_AsymptoticParameters_degree_pos
import Theorems.Thm_MetricCodes_Johnson_AsymptoticParameters_rankPenalty_le_one

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
    -1 ≤ shellRate α β γ u := by
  have hαentropy := binaryEntropy_le_one α
  have huone : u ≤ 1 := by
    nlinarith [h.degree_lt_weight, h.weight_lt_half]
  have huentropy := MetricCodes.binaryEntropy_nonneg h.degree_pos.le huone
  unfold shellRate
  nlinarith [h.rankPenalty_le_one]
end MetricCodes.Johnson.AsymptoticParameters
