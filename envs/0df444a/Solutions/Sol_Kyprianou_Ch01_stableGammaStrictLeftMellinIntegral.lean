-- Prove2me | solution 1 for Kyprianou.Ch01.stableGammaStrictLeftMellinIntegral
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T13:06:24.199814+00:00
-- url     : https://prove2.me/submissions/e6e57f4b-d589-42e9-8189-0afbfc4ca285

import Mathlib
import Definitions.Def_Kyprianou_Ch01_ExplicitLevyExamples
import Theorems.Thm_Kyprianou_Ch01_stableGammaStrictLeftMellinHolomorphic
import Theorems.Thm_Kyprianou_Ch01_stableGammaStrictLeftMellinUniqueness
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Complex Real Set Filter Kyprianou.Ch01
set_option autoImplicit false

theorem solution
    (alpha : ℝ) (h0 : 0 < alpha) (h1 : alpha < 1)
    (w : ℂ) (hwre : w.re < 0) :
    (∫ r in Set.Ioi (0 : ℝ),
      Complex.exp (w * (r : ℂ)) *
        ((r ^ (-alpha) : ℝ) : ℂ) ∂volume) =
      ((Real.Gamma (1 - alpha) : ℝ) : ℂ) *
        Complex.exp (((alpha - 1 : ℝ) : ℂ) * Complex.log (-w)) := by
  exact Kyprianou.Ch01.stableGammaStrictLeftMellinUniqueness
    alpha h0 h1
    (Kyprianou.Ch01.stableGammaStrictLeftMellinHolomorphic alpha h0 h1)
    w hwre
