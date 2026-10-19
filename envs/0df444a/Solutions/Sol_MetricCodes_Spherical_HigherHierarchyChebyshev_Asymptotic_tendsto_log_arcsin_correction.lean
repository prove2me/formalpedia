-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchyChebyshev.Asymptotic.tendsto_log_arcsin_correction
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:34.162962+00:00
-- url     : https://prove2.me/submissions/5b4865c3-3282-4892-a6a7-228bfe6a9e52

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchyChebyshev_Asymptotic_tendsto_arcsin_div_self_nhdsGT_zero
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchyChebyshev_Asymptotic_tendsto_inverse_double_degree_nhdsGT_zero

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
    Tendsto (fun a : ℝ =>
      Real.log (Real.arcsin (1 / (1 + 2 * a)) /
        (1 / (1 + 2 * a)))) atTop (𝓝 0) := by
  have hratio := tendsto_arcsin_div_self_nhdsGT_zero.comp
    tendsto_inverse_double_degree_nhdsGT_zero
  convert (Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto.comp
    hratio using 1
  · ext a
    rfl
  · norm_num
end MetricCodes.Spherical.HigherHierarchyChebyshev.Asymptotic
