-- Prove2me | solution 1 for MeasureTheory.IsUniversallyNull.mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T07:21:50.858805+00:00
-- url     : https://prove2.me/submissions/1d8da61a-ce53-417e-98b2-52c442cfbf04

module
public import Definitions.Def_AddUN_IdealInvariant
public import Mathlib.MeasureTheory.MeasurableSpace.Card
public import Mathlib.Probability.Distributions.Uniform
public import Mathlib.Probability.ProductMeasure
public import Definitions.Def_AddUN_UniversallyNull

set_option autoImplicit false
@[expose] public section
public section
open Set Filter Topology Cardinal IdealInvariant
open scoped ENNReal
open MeasureTheory
variable {X : Type*} [MeasurableSpace X] {A B : Set X}
namespace MeasureTheory
namespace IsUniversallyNull
theorem _root_.solution (hB : IsUniversallyNull B) (h : A ⊆ B) : IsUniversallyNull A :=
  fun μ _ _ ↦ measure_mono_null h (hB μ)
end IsUniversallyNull
end MeasureTheory
