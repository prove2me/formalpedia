-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchyChebyshev.Asymptotic.radiusNormalizer_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:34.162962+00:00
-- url     : https://prove2.me/submissions/51dbf676-686a-4511-9446-ccbe2ae2244d

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
theorem _root_.solution {R : ℝ} (hR : 0 ≤ R) :
    0 < radiusNormalizer R := by
  unfold radiusNormalizer
  apply mul_pos (div_pos (by norm_num) Real.pi_pos)
  exact Real.arcsin_pos.mpr
    (div_pos (by norm_num) (Real.sqrt_pos.mpr (by nlinarith)))
end MetricCodes.Spherical.HigherHierarchyChebyshev.Asymptotic
