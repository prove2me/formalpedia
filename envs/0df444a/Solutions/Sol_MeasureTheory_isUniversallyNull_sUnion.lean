-- Prove2me | solution 1 for MeasureTheory.isUniversallyNull_sUnion
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T07:33:46.436338+00:00
-- url     : https://prove2.me/submissions/694253b4-8a69-4d44-8d6c-3e90ffda7cbd

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
theorem _root_.solution {𝒜 : Set (Set X)} (h𝒜 : 𝒜.Countable)
    (h : ∀ A ∈ 𝒜, IsUniversallyNull A) : IsUniversallyNull (⋃₀ 𝒜) :=
  fun μ _ _ ↦ (measure_sUnion_null_iff h𝒜).2 fun A hA ↦ h A hA μ
end MeasureTheory
