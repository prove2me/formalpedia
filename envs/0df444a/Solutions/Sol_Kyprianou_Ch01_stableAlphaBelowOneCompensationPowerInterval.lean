-- Prove2me | solution 1 for Kyprianou.Ch01.stableAlphaBelowOneCompensationPowerInterval
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T19:53:32.143838+00:00
-- url     : https://prove2.me/submissions/bca5df2f-2203-4263-af7a-1ae9ba0cfd0a

import Mathlib
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 intervalIntegral Real
set_option autoImplicit false

theorem solution
    (alpha : ℝ) (ha0 : 0 < alpha) (ha1 : alpha < 1) :
    (∫ r in (0 : ℝ)..1, r ^ (-alpha)) = 1 / (1 - alpha) := by
  have hpow :=
    integral_rpow
      (a := (0 : ℝ)) (b := (1 : ℝ))
      (r := -alpha) (Or.inl (by linarith : -1 < -alpha))
  rw [hpow]
  have h : 1 - alpha ≠ 0 := by linarith
  simp only [Real.one_rpow,
    Real.zero_rpow (by linarith : -alpha + 1 ≠ 0),
    sub_zero]
  congr 1 <;> ring
