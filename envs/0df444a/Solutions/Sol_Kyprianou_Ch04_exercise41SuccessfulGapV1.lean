-- Prove2me | solution 1 for Kyprianou.Ch04.exercise41SuccessfulGapV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T00:43:18.300796+00:00
-- url     : https://prove2.me/submissions/a15cb92a-7a45-4289-80cb-e9e5158e8594

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_smallTimeDriftLimit
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
set_option autoImplicit false

open Kyprianou.Ch04

/-- If two real values have absolute value less than d*h/8, their difference cannot dominate d*dt/2 for dt at least h. -/
theorem solution
    (d h x y dt : ℝ) (hd : 0 < d) (hh : 0 < h)
    (hx : |x| < d * h / 8) (hy : |y| < d * h / 8)
    (hslope : d / 2 * dt ≤ y - x) : dt < h := by
  by_contra! hdt
  have hxL := (abs_lt.mp hx).1
  have hyU := (abs_lt.mp hy).2
  have hm := mul_le_mul_of_nonneg_left hdt (by positivity : 0 ≤ d / 2)
  have hdh : 0 < d * h := mul_pos hd hh
  linarith
