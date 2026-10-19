-- Prove2me | solution 1 for MetricCodes.Hamming.classicalParameter_lt_half
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:28.340887+00:00
-- url     : https://prove2.me/submissions/e8ab4235-f218-4e6b-ab5d-666a1dd81a06

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
    classicalParameter δ < (1 : ℝ) / 2 := by
  have hrad : 0 < δ * (1 - δ) := mul_pos hδ (by linarith)
  unfold classicalParameter
  have hsqrt := Real.sqrt_pos.2 hrad
  linarith
end MetricCodes.Hamming
