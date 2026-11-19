-- Prove2me | solution 1 for Kyprianou.Ch01.stableAlphaAboveOneKernelEnvelopeBound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T00:20:09.908551+00:00
-- url     : https://prove2.me/submissions/8e2ed022-a9f3-4202-8e37-7995a31ca4cf

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.SetSemiring
import Theorems.Thm_Kyprianou_Ch01_stableAlphaAboveOneNearZeroPointwiseBound
import Theorems.Thm_Kyprianou_Ch01_stableAlphaAboveOneTailPointwiseBound
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Complex Real Filter
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Quadratic near-zero and linear tail envelope for compensated Fourier kernels. -/
theorem solution (alpha r : ℝ) (hr : 0 < r) :
    ‖(Complex.exp (Complex.I * (r : ℂ)) - 1 -
        Complex.I * (r : ℂ)) /
          (((r ^ (alpha + 1) : ℝ)) : ℂ)‖ ≤
      (if r ≤ 1 then r ^ (1 - alpha)
        else 2 * r ^ (-alpha)) := by
  by_cases hsmall : r ≤ 1
  · simpa only [if_pos hsmall] using
      Kyprianou.Ch01.stableAlphaAboveOneNearZeroPointwiseBound
        alpha r hr hsmall
  · have hlarge : 1 < r := lt_of_not_ge hsmall
    simpa only [if_neg hsmall] using
      Kyprianou.Ch01.stableAlphaAboveOneTailPointwiseBound
        alpha r hlarge
