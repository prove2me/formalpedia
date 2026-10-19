-- Prove2me | solution 1 for HlawkaGaussian.dbg_int
-- status  : ACCEPTED   (prove)
-- author  : @Winningatmath
-- created : 2026-10-16T21:06:24.733498+00:00
-- url     : https://prove2.me/submissions/acb1f8c7-8720-494d-ab91-5dec92dba5b9

import Mathlib
open MeasureTheory ProbabilityTheory

theorem solution : ∫ (t : ℝ), t ∂(ProbabilityTheory.gaussianReal 0 1) = 0 := by
  norm_num
