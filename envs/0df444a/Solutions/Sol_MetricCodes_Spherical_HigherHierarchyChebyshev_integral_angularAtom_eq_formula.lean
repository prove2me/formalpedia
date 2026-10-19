-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchyChebyshev.integral_angularAtom_eq_formula
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:34.744009+00:00
-- url     : https://prove2.me/submissions/082e3568-9813-42cc-9d0a-219effd99a5f

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchyChebyshev_integral_angularAtom_eq_arcsin
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchyChebyshev_arcsin_angularAmplitude_eq

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open scoped Interval
open MetricCodes MetricCodes.Spherical MetricCodes.Spherical.HigherHierarchyChebyshev
namespace MetricCodes.Spherical.HigherHierarchyChebyshev
theorem _root_.solution {R : ℝ} (hR : 0 < R) :
    (∫ t in (0 : ℝ)..1, angularAtom R t) =
      (1 - (2 / Real.pi) *
        Real.arcsin (1 / Real.sqrt (4 * R + 1))) / 2 := by
  rw [integral_angularAtom_eq_arcsin hR,
    arcsin_angularAmplitude_eq hR]
  have hpi : Real.pi ≠ 0 := Real.pi_pos.ne'
  have hrad : 1 + 4 * R = 4 * R + 1 := by ring
  rw [hrad]
  field_simp
end MetricCodes.Spherical.HigherHierarchyChebyshev
