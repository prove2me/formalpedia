-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchyChebyshev.Asymptotic.integral_angularAtom_eq_radiusGamma
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:34.744009+00:00
-- url     : https://prove2.me/submissions/b4828753-5f37-4bdc-bf0a-13d1628c0346

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchyChebyshev_integral_angularAtom_eq_formula

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open scoped Interval
open Filter
open scoped Topology BigOperators
open MetricCodes MetricCodes.Spherical MetricCodes.Spherical.HigherHierarchyChebyshev MetricCodes.Spherical.HigherHierarchyChebyshev.Asymptotic
namespace MetricCodes.Spherical.HigherHierarchyChebyshev.Asymptotic
theorem _root_.solution
    {R : ℝ} (hR : 0 < R) :
    (∫ t in (0 : ℝ)..1, angularAtom R t) = radiusGamma R := by
  rw [integral_angularAtom_eq_formula hR]
  rfl
end MetricCodes.Spherical.HigherHierarchyChebyshev.Asymptotic
