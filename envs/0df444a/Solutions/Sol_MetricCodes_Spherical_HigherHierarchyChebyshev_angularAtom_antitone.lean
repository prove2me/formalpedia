-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchyChebyshev.angularAtom_antitone
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:34.744009+00:00
-- url     : https://prove2.me/submissions/e7872886-2c48-42da-8496-0dec9bc0eb12

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchyChebyshev_spectralAtom_inverseQuadratic_half
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchyChebyshev_angularQuadratic_nonneg

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open scoped Interval
open MetricCodes MetricCodes.Spherical MetricCodes.Spherical.HigherHierarchyChebyshev
namespace MetricCodes.Spherical.HigherHierarchyChebyshev
theorem _root_.solution {R : ℝ} (hR : 0 < R) :
    AntitoneOn (angularAtom R) (Set.Icc (0 : ℝ) 1) := by
  intro x hx y hy hxy
  have hangles : Real.pi * x ≤ Real.pi * y :=
    mul_le_mul_of_nonneg_left hxy Real.pi_pos.le
  have hcos : Real.cos (Real.pi * y) ≤ Real.cos (Real.pi * x) :=
    Real.cos_le_cos_of_nonneg_of_le_pi
      (mul_nonneg Real.pi_pos.le hx.1)
      (by nlinarith [Real.pi_pos, hy.2]) hangles
  have hquadratic : angularQuadratic R y ≤ angularQuadratic R x := by
    unfold angularQuadratic
    exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have hxquad := angularQuadratic_nonneg hR.le x
  have hyquad := angularQuadratic_nonneg hR.le y
  unfold angularAtom
  rw [spectralAtom_inverseQuadratic_half hxquad,
    spectralAtom_inverseQuadratic_half hyquad]
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply Real.sqrt_le_sqrt
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  nlinarith
end MetricCodes.Spherical.HigherHierarchyChebyshev
