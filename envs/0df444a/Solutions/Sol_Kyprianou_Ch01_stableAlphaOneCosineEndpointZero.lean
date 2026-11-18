-- Prove2me | solution 1 for Kyprianou.Ch01.stableAlphaOneCosineEndpointZero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T09:02:05.039426+00:00
-- url     : https://prove2.me/submissions/dc977f37-ee51-49c1-8b9d-ed02ab54ef2c

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Real
open scoped Topology
set_option autoImplicit false
/-! The integration-by-parts boundary term vanishes at the positive origin. -/
theorem solution :
    Tendsto (fun r : ℝ => (1 - Real.cos r) / r)
    (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
  have hderiv : HasDerivAt
      (fun r : ℝ => 1 - Real.cos r) 0 0 := by
    simpa [Real.sin_zero] using (Real.hasDerivAt_cos 0).const_sub 1
  have h := hderiv.tendsto_slope_zero_right
  simpa [Real.cos_zero, div_eq_inv_mul, smul_eq_mul,
    mul_comm, add_zero] using h
