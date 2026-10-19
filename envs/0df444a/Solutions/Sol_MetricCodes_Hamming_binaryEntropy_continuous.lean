-- Prove2me | solution 1 for MetricCodes.Hamming.binaryEntropy_continuous
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:28.340887+00:00
-- url     : https://prove2.me/submissions/11d656c7-5ca4-4b7c-9792-b158b792959e

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
theorem _root_.solution : Continuous MetricCodes.binaryEntropy := by
  have hfun : MetricCodes.binaryEntropy =
      (fun u : ℝ => Real.binEntropy u / Real.log 2) :=
    funext binaryEntropy_eq_binEntropy_div_log
  rw [hfun]
  exact Real.binEntropy_continuous.div_const (Real.log 2)
end MetricCodes.Hamming
