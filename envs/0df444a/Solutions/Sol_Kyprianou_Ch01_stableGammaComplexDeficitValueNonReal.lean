-- Prove2me | solution 1 for Kyprianou.Ch01.stableGammaComplexDeficitValueNonReal
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T23:12:57.247219+00:00
-- url     : https://prove2.me/submissions/35c6e1cc-d37e-4eb3-b4c1-5f935560ca95

import Mathlib
import Theorems.Thm_Kyprianou_Ch01_stableGammaComplexDeficitValueStrictLeft
import Theorems.Thm_Kyprianou_Ch01_stableGammaComplexDeficitValueImaginary
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Complex Real Filter
set_option autoImplicit false

theorem solution
    (alpha : ℝ) (h0 : 0 < alpha) (h1 : alpha < 1)
    (w : ℂ) (hw : w ≠ 0) (hwre : w.re ≤ 0)
    (hwim : w.im ≠ 0) :
    (∫ r in Set.Ioi (0 : ℝ),
      (Complex.exp (w * (r : ℂ)) - 1) *
        ((r ^ (-alpha - 1) : ℝ) : ℂ) ∂volume) =
      ((Real.Gamma (-alpha) : ℝ) : ℂ) *
        Complex.exp ((alpha : ℂ) * Complex.log (-w)) := by
  rcases lt_or_eq_of_le hwre with hstrict | hboundary
  · exact Kyprianou.Ch01.stableGammaComplexDeficitValueStrictLeft
      alpha h0 h1 w hw hstrict
  · exact Kyprianou.Ch01.stableGammaComplexDeficitValueImaginary
      alpha h0 h1 w hw hboundary hwim
