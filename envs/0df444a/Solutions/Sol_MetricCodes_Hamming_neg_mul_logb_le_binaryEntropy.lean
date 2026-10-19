-- Prove2me | solution 1 for MetricCodes.Hamming.neg_mul_logb_le_binaryEntropy
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:28.946406+00:00
-- url     : https://prove2.me/submissions/522ee5b8-f039-4551-8db7-1d86c7b5896c

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
theorem _root_.solution {b : ℝ}
    (hb : 0 ≤ b) (hb' : b ≤ 1) :
    b * (-Real.logb 2 b) ≤ MetricCodes.binaryEntropy b := by
  have hlog : Real.logb 2 (1 - b) ≤ 0 :=
    Real.logb_nonpos (by norm_num) (by linarith) (by linarith)
  have hterm : (1 - b) * Real.logb 2 (1 - b) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by linarith) hlog
  unfold MetricCodes.binaryEntropy
  nlinarith
end MetricCodes.Hamming
