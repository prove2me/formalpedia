-- Prove2me | solution 1 for Kyprianou.Ch01.stableAboveOneCompensatedTailPointwise
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T22:30:18.773908+00:00
-- url     : https://prove2.me/submissions/e698a69d-d9a8-4731-964a-273296746c8f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Theorems.Thm_Kyprianou_Ch01_stableBelowOneCompensatedPositivePointwise
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Real Complex Set
set_option autoImplicit false

theorem solution
    (alpha c xi r : ℝ) (hr : 0 < r) :
    (c * r ^ (-alpha - 1)) •
      ProbabilityTheory.levyCompensatedIntegrand xi r =
      (c : ℂ) *
        ((Complex.exp ((Complex.I * (xi : ℂ)) * (r : ℂ)) - 1 -
            Complex.I * (xi : ℂ) * (r : ℂ)) *
          (((r ^ (-alpha - 1) : ℝ) : ℂ))) +
      (Complex.I * ((c * xi : ℝ) : ℂ)) *
        (if r < 1 then (0 : ℂ) else
          (((r ^ (-alpha) : ℝ) : ℂ))) := by
  have hsource :=
    Kyprianou.Ch01.stableBelowOneCompensatedPositivePointwise
      alpha c xi r hr
  have hpow : r ^ (-alpha - 1) * r = r ^ (-alpha) := by
    simpa only [sub_add_cancel] using
      (Real.rpow_add_one hr.ne' (-alpha - 1)).symm
  have hcpow :
      (((r ^ (-alpha - 1) : ℝ) : ℂ)) * (r : ℂ) =
        (((r ^ (-alpha) : ℝ) : ℂ)) := by
    exact_mod_cast hpow
  rw [hsource]
  by_cases h : r < 1
  · simp only [if_pos h, mul_zero, add_zero]
    rw [← hcpow]
    push_cast
    ring
  · simp only [if_neg h, mul_zero, sub_zero]
    rw [← hcpow]
    push_cast
    ring
