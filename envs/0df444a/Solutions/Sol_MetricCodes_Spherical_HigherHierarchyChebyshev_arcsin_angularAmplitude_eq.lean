-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchyChebyshev.arcsin_angularAmplitude_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:34.744009+00:00
-- url     : https://prove2.me/submissions/ae3da462-47f2-4cb7-aa64-aa5c1121c77f

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchyChebyshev_angularAmplitude_pos

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open scoped Interval
open MetricCodes MetricCodes.Spherical MetricCodes.Spherical.HigherHierarchyChebyshev
namespace MetricCodes.Spherical.HigherHierarchyChebyshev
theorem _root_.solution {R : ℝ} (hR : 0 < R) :
    Real.arcsin (angularAmplitude R) =
      Real.pi / 2 - Real.arcsin (1 / Real.sqrt (1 + 4 * R)) := by
  have hD : 0 < 1 + 4 * R := by positivity
  have hroot := Real.sqrt_pos.mpr hD
  have hroot_sq := Real.sq_sqrt hD.le
  have hRroot_sq := Real.sq_sqrt hR.le
  have hcomplement :
      Real.sqrt (1 - (1 / Real.sqrt (1 + 4 * R)) ^ 2) =
        angularAmplitude R := by
    have hsquare :
        1 - (1 / Real.sqrt (1 + 4 * R)) ^ 2 =
          (angularAmplitude R) ^ 2 := by
      unfold angularAmplitude
      field_simp
      nlinarith
    rw [hsquare, Real.sqrt_sq (angularAmplitude_pos hR).le]
  calc
    Real.arcsin (angularAmplitude R) =
        Real.arccos (1 / Real.sqrt (1 + 4 * R)) := by
          symm
          rw [Real.arccos_eq_arcsin (by positivity), hcomplement]
    _ = Real.pi / 2 - Real.arcsin (1 / Real.sqrt (1 + 4 * R)) :=
      Real.arccos_eq_pi_div_two_sub_arcsin _
end MetricCodes.Spherical.HigherHierarchyChebyshev
