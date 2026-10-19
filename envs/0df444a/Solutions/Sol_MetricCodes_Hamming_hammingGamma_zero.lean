-- Prove2me | solution 1 for MetricCodes.Hamming.hammingGamma_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:28.946406+00:00
-- url     : https://prove2.me/submissions/e914431f-0aed-47cb-91ef-a77c6e02fd2d

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
theorem _root_.solution {a : ℝ} (ha : 0 < a) (ha' : a < 1) :
    MetricCodes.hammingGamma a 0 = 2 * Real.sqrt (a * (1 - a)) := by
  have hrad : 0 < a * (1 - a) := mul_pos ha (sub_pos.mpr ha')
  have hsqrt : Real.sqrt (a * (1 - a)) ≠ 0 :=
    (Real.sqrt_pos.2 hrad).ne'
  have hsquare := Real.sq_sqrt hrad.le
  unfold MetricCodes.hammingGamma
  simp only [sub_zero]
  field_simp [hsqrt]
  nlinarith
end MetricCodes.Hamming
