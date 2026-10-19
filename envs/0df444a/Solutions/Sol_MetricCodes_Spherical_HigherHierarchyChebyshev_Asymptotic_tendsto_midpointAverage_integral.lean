-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchyChebyshev.Asymptotic.tendsto_midpointAverage_integral
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:34.162962+00:00
-- url     : https://prove2.me/submissions/10243555-70a0-4097-9961-cd1ce5fe3129

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchyChebyshev_Asymptotic_midpointAverage_integral_error_le

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option autoImplicit false
open MetricCodes
open MetricCodes.Spherical
noncomputable section
open Filter
open scoped Topology BigOperators Interval
open MetricCodes.Spherical.HigherHierarchyChebyshev MetricCodes.Spherical.HigherHierarchyChebyshev.Asymptotic
namespace MetricCodes.Spherical.HigherHierarchyChebyshev.Asymptotic
theorem _root_.solution
    {f : ℝ → ℝ} (hf : AntitoneOn f (Set.Icc (0 : ℝ) 1)) :
    Tendsto (midpointAverage f) atTop (𝓝 (∫ x in (0 : ℝ)..1, f x)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  simp only [Real.norm_eq_abs]
  refine squeeze_zero' (g := fun N : ℕ => (f 0 - f 1) / N)
    (Eventually.of_forall fun _ => abs_nonneg _) ?_ ?_
  · filter_upwards [eventually_gt_atTop (0 : ℕ)] with N hN
    exact midpointAverage_integral_error_le hf hN
  · exact (tendsto_const_div_atTop_nhds_zero_nat (f 0 - f 1))
end MetricCodes.Spherical.HigherHierarchyChebyshev.Asymptotic
