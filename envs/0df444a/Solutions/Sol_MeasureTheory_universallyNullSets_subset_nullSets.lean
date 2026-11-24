-- Prove2me | solution 1 for MeasureTheory.universallyNullSets_subset_nullSets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T07:33:57.053398+00:00
-- url     : https://prove2.me/submissions/19701f3a-97bd-4dc7-927d-d544fd866a3b

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
theorem _root_.solution (μ : Measure X) [IsFiniteMeasure μ]
    [NullSingletonClass μ] : universallyNullSets X ⊆ μ.nullSets :=
  fun _ h ↦ h μ
end MeasureTheory
