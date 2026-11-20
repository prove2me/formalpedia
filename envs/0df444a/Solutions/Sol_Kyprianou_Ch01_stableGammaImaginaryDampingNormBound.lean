-- Prove2me | solution 1 for Kyprianou.Ch01.stableGammaImaginaryDampingNormBound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T08:12:55.366184+00:00
-- url     : https://prove2.me/submissions/c85c82f8-f4ab-4ea2-a5c8-85a064cf5649

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.SetSemiring
import Theorems.Thm_Kyprianou_Ch01_stableGammaImaginaryDampingNormNearZero
import Theorems.Thm_Kyprianou_Ch01_stableGammaImaginaryDampingNormTail
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Complex Real Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    (alpha : ℝ) (h0 : 0 < alpha) (h1 : alpha < 1)
    (w : ℂ) (hwre : w.re = 0) (epsilon x : ℝ)
    (he0 : 0 ≤ epsilon) (he1 : epsilon ≤ 1) (hx : 0 < x) :
    ‖(Complex.exp ((w - (epsilon : ℂ)) * (x : ℂ)) - 1) *
        (((x ^ (-alpha - 1) : ℝ)) : ℂ)‖ ≤
      (‖w‖ + 2) *
        (if x ≤ 1 then x ^ (-alpha)
          else x ^ (-alpha - 1)) := by
  by_cases hx1 : x ≤ 1
  · simpa only [if_pos hx1] using
      Kyprianou.Ch01.stableGammaImaginaryDampingNormNearZero
        alpha h0 h1 w hwre epsilon x he0 he1 hx hx1
  · have htail : 1 < x := lt_of_not_ge hx1
    simpa only [if_neg hx1] using
      Kyprianou.Ch01.stableGammaImaginaryDampingNormTail
        alpha h0 h1 w hwre epsilon x he0 he1 hx htail
