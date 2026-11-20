-- Prove2me | solution 1 for Kyprianou.Ch01.stableAboveOneUntruncatedPositiveGammaValue
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T23:45:48.685266+00:00
-- url     : https://prove2.me/submissions/b6bbc173-75f8-4fbb-9f76-74a57808cda4

import Mathlib
import Theorems.Thm_Kyprianou_Ch01_stableAboveOnePositiveFrequencyKernelScale
import Theorems.Thm_Kyprianou_Ch01_stableAlphaAboveOneKernelValue
import Theorems.Thm_Kyprianou_Ch01_stableGammaPositiveFrequencyPhase
open MeasureTheory Set Real Complex
set_option autoImplicit false

theorem solution
    (alpha xi : ℝ) (ha1 : 1 < alpha) (ha2 : alpha < 2)
    (hxi : 0 < xi) :
    (∫ r in Set.Ioi (0 : ℝ),
      (Complex.exp (Complex.I * (((xi * r : ℝ) : ℂ))) - 1 -
        Complex.I * (((xi * r : ℝ) : ℂ))) /
        (((r ^ (alpha + 1) : ℝ) : ℂ)) ∂volume) =
      (((Real.Gamma (-alpha) : ℝ) : ℂ)) *
        Complex.exp ((alpha : ℂ) *
          Complex.log (-(Complex.I * (xi : ℂ)))) := by
  have hscale :=
    Kyprianou.Ch01.stableAboveOnePositiveFrequencyKernelScale
      alpha xi ha1 hxi
  have hunit :=
    Kyprianou.Ch01.stableAlphaAboveOneKernelValue
      alpha ha1 ha2
  have hphase :=
    Kyprianou.Ch01.stableGammaPositiveFrequencyPhase alpha xi hxi
  rw [hscale, hunit, hphase]
  push_cast
  ring
