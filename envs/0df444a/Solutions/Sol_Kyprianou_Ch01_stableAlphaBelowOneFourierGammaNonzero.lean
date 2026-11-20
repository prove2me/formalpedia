-- Prove2me | solution 1 for Kyprianou.Ch01.stableAlphaBelowOneFourierGammaNonzero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T19:23:12.749203+00:00
-- url     : https://prove2.me/submissions/ac594a6c-c4f1-4e17-aedc-091676dbe9b5

import Mathlib
import Theorems.Thm_Kyprianou_Ch01_stableGammaComplexDeficitValue
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Complex Set
set_option autoImplicit false

theorem solution
    (alpha xi : ℝ) (ha0 : 0 < alpha) (ha1 : alpha < 1)
    (hxi : xi ≠ 0) :
    (∫ r in Set.Ioi (0 : ℝ),
       (Complex.exp ((Complex.I * (xi : ℂ)) * (r : ℂ)) - 1) *
         ((r ^ (-alpha - 1) : ℝ) : ℂ) ∂volume) =
      ((Real.Gamma (-alpha) : ℝ) : ℂ) *
        Complex.exp ((alpha : ℂ) *
          Complex.log (-(Complex.I * (xi : ℂ)))) := by
  let w : ℂ := Complex.I * (xi : ℂ)
  have hw : w ≠ 0 := by
    exact mul_ne_zero Complex.I_ne_zero (Complex.ofReal_ne_zero.mpr hxi)
  have hwre : w.re ≤ 0 := by
    simp [w]
  exact Kyprianou.Ch01.stableGammaComplexDeficitValue
    alpha ha0 ha1 w hw hwre
