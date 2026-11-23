-- Prove2me | solution 1 for Kyprianou.Ch02.integerValuedFiniteDiracV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T10:18:54.032134+00:00
-- url     : https://prove2.me/submissions/a5e0ccf0-4355-44fd-bada-98c017f074e5

import Mathlib
import Definitions.Def_LevyStochCalc_Probability_IntegerValuedMeasure_F003
import Theorems.Thm_Kyprianou_Ch02_integerValuedFiniteSupportV1
open MeasureTheory
open scoped ENNReal
set_option autoImplicit false

theorem solution
    {α : Type} [MeasurableSpace α]
    [MeasurableSpace.CountablySeparated α]
    (μ : Measure α)
    (hint : LevyStochCalc.Probability.IsIntegerValued μ) :
    ∃ s : Finset α, μ = ∑ a ∈ s, μ {a} • Measure.dirac a := by
  haveI : MeasurableSingletonClass α :=
    MeasurableSpace.measurableSingletonClass_of_countablySeparated
  obtain ⟨s, hs⟩ :=
    Kyprianou.Ch02.integerValuedFiniteSupportV1 μ hint
  exact ⟨s, Measure.ae_mem_finset_iff.mp hs⟩
