-- Prove2me | solution 1 for MarkovProcess.measurable_laplaceDensity
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T00:55:41.43999+00:00
-- url     : https://prove2.me/submissions/4e3e084e-ca5c-45af-825e-4d1a89eb9e38

import Mathlib

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
theorem solution (lam : ℝ) :
    Measurable fun t : ℝ ↦ ENNReal.ofReal (Real.exp (-lam * t)) := by
  fun_prop
