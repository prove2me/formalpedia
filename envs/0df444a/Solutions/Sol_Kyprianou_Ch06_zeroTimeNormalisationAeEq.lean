-- Prove2me | solution 1 for Kyprianou.Ch06.zeroTimeNormalisationAeEq
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T21:07:29.017195+00:00
-- url     : https://prove2.me/submissions/c7c195a6-c5ae-4457-b7f7-4118da8af601

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

set_option autoImplicit false
open MeasureTheory
open scoped NNReal

/-- The pointwise-zero modification of a real process agrees with the source
process simultaneously at all nonnegative times, almost surely. -/
theorem solution
    {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) (X : NNReal → Ω → Real)
    (hzero : ∀ᵐ ω ∂P, X 0 ω = 0) :
    ∀ᵐ ω ∂P, ∀ t : NNReal,
      (if t = 0 then (0 : Real) else X t ω) = X t ω := by
  filter_upwards [hzero] with ω hω
  intro t
  by_cases ht : t = 0
  · subst t
    simp [hω]
  · simp [ht]
