-- Prove2me | solution 1 for MetricCodes.Hamming.spectralMarginPolynomial_continuous
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:28.946406+00:00
-- url     : https://prove2.me/submissions/ec5613cf-070a-45b5-941e-2aa00231069e

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
theorem _root_.solution (a c : ℝ) :
    Continuous (spectralMarginPolynomial a c) := by
  unfold spectralMarginPolynomial
  fun_prop
end MetricCodes.Hamming
