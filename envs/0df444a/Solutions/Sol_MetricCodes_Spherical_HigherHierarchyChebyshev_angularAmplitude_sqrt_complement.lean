-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchyChebyshev.angularAmplitude_sqrt_complement
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:34.744009+00:00
-- url     : https://prove2.me/submissions/2cd360b3-b9c0-4003-8d1e-23d8868bf01f

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open scoped Interval
open MetricCodes MetricCodes.Spherical MetricCodes.Spherical.HigherHierarchyChebyshev
namespace MetricCodes.Spherical.HigherHierarchyChebyshev
theorem _root_.solution {R : ℝ} (hR : 0 < R)
    (t : ℝ) :
    Real.sqrt
        (1 - (angularAmplitude R * Real.sin (Real.pi * t / 2)) ^ 2) =
      Real.sqrt (1 + 4 * R * Real.cos (Real.pi * t / 2) ^ 2) /
        Real.sqrt (1 + 4 * R) := by
  have hD : 0 < 1 + 4 * R := by positivity
  have hroot : 0 < Real.sqrt (1 + 4 * R) := Real.sqrt_pos.mpr hD
  have hroot_sq := Real.sq_sqrt hD.le
  have hRroot_sq := Real.sq_sqrt hR.le
  have htrig := Real.sin_sq_add_cos_sq (Real.pi * t / 2)
  have hins :
      1 - (angularAmplitude R * Real.sin (Real.pi * t / 2)) ^ 2 =
        (1 + 4 * R * Real.cos (Real.pi * t / 2) ^ 2) /
          (1 + 4 * R) := by
    unfold angularAmplitude
    field_simp
    rw [hroot_sq, hRroot_sq]
    linear_combination -(4 * R * (1 + 4 * R)) * htrig
  rw [hins, Real.sqrt_div (by positivity :
    0 ≤ 1 + 4 * R * Real.cos (Real.pi * t / 2) ^ 2)]
end MetricCodes.Spherical.HigherHierarchyChebyshev
