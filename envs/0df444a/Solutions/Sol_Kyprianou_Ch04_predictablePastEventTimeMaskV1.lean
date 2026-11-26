-- Prove2me | solution 1 for Kyprianou.Ch04.predictablePastEventTimeMaskV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T09:18:52.742254+00:00
-- url     : https://prove2.me/submissions/7a8c38da-bbe7-4a98-a53f-8157e3a1400e

import Mathlib
open MeasureTheory Filter Set
open scoped NNReal
set_option autoImplicit false

/-- Restricting a predictable marked kernel to a future time interval and a past event preserves predictability. -/
theorem solution {Ω : Type} [MeasurableSpace Ω]
    (F : Filtration NNReal inferInstance) (s t : NNReal)
    (A : Set Ω) (hA : MeasurableSet[F s] A)
    (g : (NNReal × Ω) × ℝ → ℝ)
    (hg : Measurable[F.predictable.prod inferInstance] g) :
    Measurable[F.predictable.prod inferInstance]
      (((Ioc s t ×ˢ A) ×ˢ (univ : Set ℝ)).indicator g) := by
  letI : MeasurableSpace (NNReal × Ω) := F.predictable
  exact hg.indicator ((measurableSet_predictable_Ioc_prod (𝓕 := F) s t hA).prod MeasurableSet.univ)
