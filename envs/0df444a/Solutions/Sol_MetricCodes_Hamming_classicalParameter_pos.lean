-- Prove2me | solution 1 for MetricCodes.Hamming.classicalParameter_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:28.340887+00:00
-- url     : https://prove2.me/submissions/772fc0c1-0f3e-494f-8c7b-fef0be7873f2

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
    0 < classicalParameter δ := by
  have hsquare : 0 < (δ - (1 : ℝ) / 2) ^ 2 :=
    sq_pos_of_ne_zero (by linarith)
  have hrad : 0 < δ * (1 - δ) := mul_pos hδ (by linarith)
  have hrad_lt : δ * (1 - δ) < ((1 : ℝ) / 2) ^ 2 := by
    nlinarith
  have hroot : Real.sqrt (δ * (1 - δ)) < (1 : ℝ) / 2 := by
    exact (Real.sqrt_lt' (by norm_num)).2 hrad_lt
  unfold classicalParameter
  linarith
end MetricCodes.Hamming
