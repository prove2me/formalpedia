-- Prove2me | solution 1 for Kyprianou.Ch01.stableAlphaOneCosineEndpointInfinity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T09:06:18.270411+00:00
-- url     : https://prove2.me/submissions/fc07cef8-c736-4d8d-b86b-2e88780f3bdf

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Real
open scoped Topology
set_option autoImplicit false
/-! The upper integration-by-parts boundary term vanishes as r tends to infinity. -/
theorem solution :
    Tendsto (fun r : ℝ => (1 - Real.cos r) / r)
    atTop (𝓝 (0 : ℝ)) := by
  have ht : Tendsto (fun r : ℝ => 2 / r) atTop (𝓝 (0 : ℝ)) := by
    simpa only [div_eq_mul_inv, mul_zero] using
      ((tendsto_const_nhds : Tendsto (fun _ : ℝ => (2 : ℝ)) atTop (𝓝 2)).mul
        (tendsto_inv_atTop_zero : Tendsto (fun r : ℝ => r⁻¹) atTop (𝓝 0)))
  refine Filter.Tendsto.squeeze' tendsto_const_nhds ht ?_ ?_
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
    exact div_nonneg (sub_nonneg.mpr (Real.cos_le_one r)) hr.le
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
    exact (div_le_div_of_nonneg_right (by linarith [Real.neg_one_le_cos r]) hr.le)
