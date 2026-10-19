-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchyChebyshev.Asymptotic.log_two_mul_sphericalEntropy
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:34.162962+00:00
-- url     : https://prove2.me/submissions/8a33e478-b2ed-469b-8201-2ed1d15b005d

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_sphericalEntropy_eq_log_add

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
theorem _root_.solution {a : ℝ} (ha : 0 < a) :
    Real.log 2 * MetricCodes.sphericalEntropy a =
      Real.log (1 + a) + a * Real.log (1 + 1 / a) := by
  rw [MetricCodes.sphericalEntropy_eq_log_add ha]
  have hlog : Real.log (2 : ℝ) ≠ 0 :=
    (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne'
  have hratio : (1 + a) / a = 1 + 1 / a := by
    field_simp
    ring
  unfold Real.logb
  rw [hratio]
  field_simp
end MetricCodes.Spherical.HigherHierarchyChebyshev.Asymptotic
