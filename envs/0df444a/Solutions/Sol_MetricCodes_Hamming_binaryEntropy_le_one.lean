-- Prove2me | solution 1 for MetricCodes.Hamming.binaryEntropy_le_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:28.340887+00:00
-- url     : https://prove2.me/submissions/667a0c86-afb9-4634-9fda-e34908336647

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open MetricCodes
noncomputable section
set_option autoImplicit false
open Filter Metric Topology
open scoped BigOperators InnerProductSpace Topology
open MetricCodes.Hamming
namespace MetricCodes.Hamming
theorem _root_.solution (u : ℝ) :
    MetricCodes.binaryEntropy u ≤ 1 := by
  rw [binaryEntropy_eq_binEntropy_div_log]
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  apply (div_le_iff₀ hlog).2
  simpa using (Real.binEntropy_le_log_two (p := u))
end MetricCodes.Hamming
