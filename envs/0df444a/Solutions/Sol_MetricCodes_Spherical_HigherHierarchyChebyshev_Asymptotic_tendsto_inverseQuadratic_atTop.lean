-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchyChebyshev.Asymptotic.tendsto_inverseQuadratic_atTop
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:34.162962+00:00
-- url     : https://prove2.me/submissions/a4207f84-fcd9-4924-8ed9-b91833326676

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
    Tendsto inverseQuadratic atTop atTop := by
  unfold inverseQuadratic
  have hlinear : Tendsto (fun R : ℝ => 1 + 4 * R) atTop atTop := by
    exact tendsto_atTop_add_const_left atTop 1
      (tendsto_id.const_mul_atTop (by norm_num : (0 : ℝ) < 4))
  have hroot : Tendsto (fun R : ℝ => Real.sqrt (1 + 4 * R)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp hlinear
  have hsub : Tendsto (fun R : ℝ => Real.sqrt (1 + 4 * R) + (-1))
      atTop atTop := tendsto_atTop_add_const_right atTop (-1) hroot
  simpa [sub_eq_add_neg] using
    hsub.atTop_div_const (by norm_num : (0 : ℝ) < 2)
end MetricCodes.Spherical.HigherHierarchyChebyshev.Asymptotic
