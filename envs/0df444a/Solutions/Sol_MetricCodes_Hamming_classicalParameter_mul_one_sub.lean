-- Prove2me | solution 1 for MetricCodes.Hamming.classicalParameter_mul_one_sub
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:28.946406+00:00
-- url     : https://prove2.me/submissions/39d8d857-da59-43fd-a6b9-e62eecac6185

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
theorem _root_.solution {δ : ℝ}
    (hδ : 0 < δ) (hδ' : δ < (1 : ℝ) / 2) :
    classicalParameter δ * (1 - classicalParameter δ) =
      ((1 : ℝ) / 2 - δ) ^ 2 := by
  have hrad : 0 ≤ δ * (1 - δ) :=
    (mul_pos hδ (by linarith)).le
  have hsqrt := Real.sq_sqrt hrad
  unfold classicalParameter
  nlinarith
end MetricCodes.Hamming
