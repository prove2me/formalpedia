-- Prove2me | solution 1 for Kyprianou.Ch04.stationaryEventFubiniV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T23:28:35.306405+00:00
-- url     : https://prove2.me/submissions/019ce0a3-a6a7-4fdc-ac79-bc56d4ed6be2

import Mathlib.MeasureTheory.Measure.Prod
open MeasureTheory Filter Set
open scoped ENNReal NNReal
set_option autoImplicit false

/-- A full-time-measure event with stationary path law holds at the origin. -/
theorem solution {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Q : Measure ℝ) [SigmaFinite Q]
    (hQ : NeBot (ae Q))
    (A : ℝ → Ω → Prop)
    (hm : MeasurableSet {z : ℝ × Ω | A z.1 z.2})
    (ha : ∀ᵐ ω ∂P, ∀ᵐ s ∂Q, A s ω)
    (hs : ∀ s : ℝ, (∀ᵐ ω ∂P, A s ω) → ∀ᵐ ω ∂P, A 0 ω) :
    ∀ᵐ ω ∂P, A 0 ω := by
  have h := (Measure.ae_ae_comm hm).2 ha
  letI := hQ
  obtain ⟨s, hₛ⟩ := h.exists
  exact hs s hₛ
