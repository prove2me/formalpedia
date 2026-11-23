-- Prove2me | solution 1 for Kyprianou.Ch02.integerValuedFiniteSupportV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T09:34:26.244691+00:00
-- url     : https://prove2.me/submissions/271999cf-3329-4af5-add6-b3f9783f46cd

import Mathlib
import Definitions.Def_LevyStochCalc_Probability_IntegerValuedMeasure_F003

open MeasureTheory
open scoped ENNReal
set_option autoImplicit false

theorem solution
    {α : Type} [MeasurableSpace α]
    [MeasurableSpace.CountablySeparated α]
    (μ : Measure α)
    (hint : LevyStochCalc.Probability.IsIntegerValued μ) :
    ∃ s : Finset α, ∀ᵐ a ∂μ, a ∈ s := by
  exact LevyStochCalc.Probability.exists_finset_ae_mem hint
