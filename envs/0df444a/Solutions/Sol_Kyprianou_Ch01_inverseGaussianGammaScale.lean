-- Prove2me | solution 1 for Kyprianou.Ch01.inverseGaussianGammaScale
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T17:43:01.694505+00:00
-- url     : https://prove2.me/submissions/29c6b47a-c2c3-4fa9-be77-5d64d1ab821d

import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Theorems.Thm_Kyprianou_Ch01_inverseGaussianGammaNegativeHalf
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Complex Real Set
set_option autoImplicit false

theorem solution :
    Real.Gamma (-(1 / 2 : ℝ)) /
      Real.sqrt (2 * Real.pi) = -Real.sqrt 2 := by
  rw [Kyprianou.Ch01.inverseGaussianGammaNegativeHalf]
  have hs : Real.sqrt (2 * Real.pi) =
      Real.sqrt 2 * Real.sqrt Real.pi :=
    Real.sqrt_mul (by norm_num : 0 ≤ (2 : ℝ)) _
  rw [hs]
  have hs2 : 0 < Real.sqrt 2 := by positivity
  have hsp : 0 < Real.sqrt Real.pi := Real.sqrt_pos.2 Real.pi_pos
  apply (div_eq_iff (mul_ne_zero (ne_of_gt hs2) (ne_of_gt hsp))).2
  calc
    -2 * Real.sqrt Real.pi =
      -(Real.sqrt 2 * Real.sqrt 2) * Real.sqrt Real.pi := by
        rw [Real.mul_self_sqrt (by norm_num : 0 ≤ (2 : ℝ))]
    _ = -Real.sqrt 2 * (Real.sqrt 2 * Real.sqrt Real.pi) := by ring
