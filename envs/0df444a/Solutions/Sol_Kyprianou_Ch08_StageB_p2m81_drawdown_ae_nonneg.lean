-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.p2m81_drawdown_ae_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @yuzhou
-- created : 2026-11-22T03:22:23.383441+00:00
-- url     : https://prove2.me/submissions/f34fc1bd-31fd-470c-ba95-8193742f69ee

import Mathlib
open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hsupp : μ (Iio (0 : ℝ)) = 0) :
    ∀ᵐ y ∂μ, 0 ≤ y := by
  rw [ae_iff]
  simpa only [not_le, Set.Iio] using hsupp
