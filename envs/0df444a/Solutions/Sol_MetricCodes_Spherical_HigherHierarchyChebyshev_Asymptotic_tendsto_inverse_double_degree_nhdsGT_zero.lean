-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchyChebyshev.Asymptotic.tendsto_inverse_double_degree_nhdsGT_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:34.162962+00:00
-- url     : https://prove2.me/submissions/8c52b4e7-a0ba-4396-954a-00f4b127f108

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes

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
theorem _root_.solution :
    Tendsto (fun a : ℝ => 1 / (1 + 2 * a)) atTop (𝓝[>] 0) := by
  have hlinear : Tendsto (fun a : ℝ => 1 + 2 * a) atTop atTop :=
    tendsto_atTop_add_const_left atTop 1
      (tendsto_id.const_mul_atTop (by norm_num : (0 : ℝ) < 2))
  have hzero : Tendsto (fun a : ℝ => 1 / (1 + 2 * a)) atTop (𝓝 0) := by
    convert tendsto_inv_atTop_zero.comp hlinear using 1
    ext a
    simp [one_div]
  rw [tendsto_nhdsWithin_iff]
  refine ⟨hzero, ?_⟩
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with a ha
  change 0 < 1 / (1 + 2 * a)
  positivity
end MetricCodes.Spherical.HigherHierarchyChebyshev.Asymptotic
