-- Prove2me | solution 1 for MetricCodes.Hamming.improvementSlope_gt_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:28.946406+00:00
-- url     : https://prove2.me/submissions/149159a2-5d7f-46f5-977e-ee49bd1737a2

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
theorem _root_.solution {a : ℝ} (ha : a < (1 : ℝ) / 2) :
    1 < improvementSlope a := by
  have hden : 0 < 1 - 2 * a := by linarith
  have hfrac : 0 < 2 / (1 - 2 * a) := by positivity
  unfold improvementSlope
  linarith
end MetricCodes.Hamming
