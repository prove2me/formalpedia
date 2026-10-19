-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchyChebyshev.sqrt_angularQuadratic
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:34.162962+00:00
-- url     : https://prove2.me/submissions/a4e6177b-b80c-49ec-86b8-03d7e5224808

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchyChebyshev_angularQuadratic_eq_cos_half_sq
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchyChebyshev_angular_cos_nonneg

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open scoped Interval
open MetricCodes MetricCodes.Spherical MetricCodes.Spherical.HigherHierarchyChebyshev
namespace MetricCodes.Spherical.HigherHierarchyChebyshev
theorem _root_.solution {R : ℝ} (hR : 0 < R)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    Real.sqrt (angularQuadratic R t) =
      Real.sqrt R * Real.cos (Real.pi * t / 2) := by
  rw [angularQuadratic_eq_cos_half_sq,
    Real.sqrt_mul hR.le, Real.sqrt_sq (angular_cos_nonneg ht)]
end MetricCodes.Spherical.HigherHierarchyChebyshev
