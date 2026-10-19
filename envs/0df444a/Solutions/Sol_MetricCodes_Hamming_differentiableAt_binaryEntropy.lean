-- Prove2me | solution 1 for MetricCodes.Hamming.differentiableAt_binaryEntropy
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:28.946406+00:00
-- url     : https://prove2.me/submissions/7fd9bdb0-7964-456e-a9ff-aaf6c3eddadc

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
theorem _root_.solution {a : ℝ}
    (ha : 0 < a) (ha' : a < 1) :
    DifferentiableAt ℝ MetricCodes.binaryEntropy a := by
  have hfun : MetricCodes.binaryEntropy =
      (fun u : ℝ => Real.binEntropy u / Real.log 2) :=
    funext binaryEntropy_eq_binEntropy_div_log
  rw [hfun]
  exact
    (Real.differentiableAt_binEntropy ha.ne' (ne_of_lt ha')).div_const
      (Real.log 2)
end MetricCodes.Hamming
