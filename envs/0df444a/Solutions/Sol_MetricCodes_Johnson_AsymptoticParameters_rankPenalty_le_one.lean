-- Prove2me | solution 1 for MetricCodes.Johnson.AsymptoticParameters.rankPenalty_le_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:30.299848+00:00
-- url     : https://prove2.me/submissions/65239996-837b-4577-954e-b5124a214378

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Hamming_binaryEntropy_le_one
import Theorems.Thm_MetricCodes_Johnson_binaryEntropy_le_one
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
    rankPenalty α β γ ≤ 1 := by
  have hsupport := mul_le_mul_of_nonneg_left
    (binaryEntropy_le_one (β / α)) h.weight_pos.le
  have hcomplement := mul_le_mul_of_nonneg_left
    (binaryEntropy_le_one (γ / (1 - α)))
    h.weight_complement_pos.le
  unfold rankPenalty
  nlinarith
end MetricCodes.Johnson.AsymptoticParameters
