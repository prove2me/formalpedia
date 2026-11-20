-- Prove2me | solution 1 for Kyprianou.Ch01.inverseGaussianPassageDensityPower
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T19:07:23.477467+00:00
-- url     : https://prove2.me/submissions/c6ad3a8f-b373-423c-b121-2955603f3d44

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Theorems.Thm_Kyprianou_Ch01_inverseGaussianDensityPowerIdentity
open Real
set_option autoImplicit false

theorem solution
    (s x : ℝ) (hx : 0 < x) :
    s / Real.sqrt (2 * Real.pi * x ^ 3) =
      (s / Real.sqrt (2 * Real.pi)) *
        x ^ (-(3 / 2 : ℝ)) := by
  have h := Kyprianou.Ch01.inverseGaussianDensityPowerIdentity x hx
  calc
    s / Real.sqrt (2 * Real.pi * x ^ 3) =
      s * (1 / Real.sqrt (2 * Real.pi * x ^ 3)) := by ring
    _ = s * ((1 / Real.sqrt (2 * Real.pi)) *
      x ^ (-(3 / 2 : ℝ))) := by rw [h]
    _ = (s / Real.sqrt (2 * Real.pi)) *
      x ^ (-(3 / 2 : ℝ)) := by ring
