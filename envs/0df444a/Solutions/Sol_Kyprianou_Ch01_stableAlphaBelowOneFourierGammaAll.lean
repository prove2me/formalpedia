-- Prove2me | solution 1 for Kyprianou.Ch01.stableAlphaBelowOneFourierGammaAll
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T19:30:12.829307+00:00
-- url     : https://prove2.me/submissions/e64435f5-d201-4663-a0d0-1d857fe18bca

import Mathlib
import Theorems.Thm_Kyprianou_Ch01_stableAlphaBelowOneFourierGammaNonzero
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Complex Set
set_option autoImplicit false

theorem solution
    (alpha xi : ℝ) (ha0 : 0 < alpha) (ha1 : alpha < 1) :
    (∫ r in Set.Ioi (0 : ℝ),
       (Complex.exp ((Complex.I * (xi : ℂ)) * (r : ℂ)) - 1) *
         ((r ^ (-alpha - 1) : ℝ) : ℂ) ∂volume) =
      if xi = 0 then 0 else
        ((Real.Gamma (-alpha) : ℝ) : ℂ) *
          Complex.exp ((alpha : ℂ) *
            Complex.log (-(Complex.I * (xi : ℂ)))) := by
  by_cases hxi : xi = 0
  · subst xi
    simp
  · simpa only [if_neg hxi] using
      (Kyprianou.Ch01.stableAlphaBelowOneFourierGammaNonzero
        alpha xi ha0 ha1 hxi)
