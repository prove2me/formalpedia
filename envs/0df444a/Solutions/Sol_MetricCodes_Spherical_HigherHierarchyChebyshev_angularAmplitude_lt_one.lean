-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchyChebyshev.angularAmplitude_lt_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:34.162962+00:00
-- url     : https://prove2.me/submissions/f0373805-3ee9-424e-969f-c2162b8a3548

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
theorem _root_.solution {R : ℝ} (hR : 0 < R) :
    angularAmplitude R < 1 := by
  have hden : 0 < Real.sqrt (1 + 4 * R) := by positivity
  have hroot := Real.sqrt_pos.2 hR
  have hroot_sq := Real.sq_sqrt hR.le
  have hden_sq := Real.sq_sqrt (by positivity : 0 ≤ 1 + 4 * R)
  unfold angularAmplitude
  apply (div_lt_iff₀ hden).2
  nlinarith [sq_nonneg (Real.sqrt (1 + 4 * R) - 2 * Real.sqrt R)]
end MetricCodes.Spherical.HigherHierarchyChebyshev
