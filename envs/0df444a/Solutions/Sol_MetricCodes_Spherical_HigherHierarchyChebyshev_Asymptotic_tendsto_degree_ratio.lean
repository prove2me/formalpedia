-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchyChebyshev.Asymptotic.tendsto_degree_ratio
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:34.162962+00:00
-- url     : https://prove2.me/submissions/af54d106-3de0-44df-917b-c16dcc90b4ce

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
    Tendsto (fun a : ℝ => (1 + 2 * a) / (1 + a)) atTop (𝓝 2) := by
  have hinv : Tendsto (fun a : ℝ => a⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero
  have hratio :
      Tendsto (fun a : ℝ => (a⁻¹ + 2) / (a⁻¹ + 1)) atTop (𝓝 2) := by
    convert (hinv.add_const 2).div (hinv.add_const 1)
      (by norm_num : (0 : ℝ) + 1 ≠ 0) using 1
    · ext a
      rfl
    · norm_num
  apply hratio.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with a ha
  field_simp
end MetricCodes.Spherical.HigherHierarchyChebyshev.Asymptotic
