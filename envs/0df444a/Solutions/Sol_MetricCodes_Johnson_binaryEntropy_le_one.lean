-- Prove2me | solution 1 for MetricCodes.Johnson.binaryEntropy_le_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:29.660979+00:00
-- url     : https://prove2.me/submissions/543ae803-4573-4f6f-b929-256ea01146c0

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open MetricCodes
open MetricCodes.Johnson
noncomputable section
open scoped BigOperators InnerProductSpace Matrix
namespace MetricCodes.Johnson
theorem _root_.solution (u : ℝ) :
    MetricCodes.binaryEntropy u ≤ 1 := by
  rw [binaryEntropy_eq_binEntropy_div_log]
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  apply (div_le_iff₀ hlog).mpr
  simpa using (Real.binEntropy_le_log_two (p := u))
end MetricCodes.Johnson
