-- Prove2me | solution 1 for MetricCodes.Hamming.spectralMarginPolynomial_improvement_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:28.946406+00:00
-- url     : https://prove2.me/submissions/4a57adf5-5165-4dc8-93b0-798e6e8704ae

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
    (ha : a < (1 : ℝ) / 2) :
    spectralMarginPolynomial a (improvementSlope a) 0 =
      a * (1 - a) * (1 - 2 * a) := by
  have hden : 1 - 2 * a ≠ 0 := by linarith
  have hden' : 1 - a * 2 ≠ 0 := by
    simpa [mul_comm] using hden
  unfold spectralMarginPolynomial improvementSlope
  field_simp [hden, hden']
  ; ring
end MetricCodes.Hamming
