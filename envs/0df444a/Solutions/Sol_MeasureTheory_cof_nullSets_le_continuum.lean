-- Prove2me | solution 1 for MeasureTheory.cof_nullSets_le_continuum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T07:34:54.137704+00:00
-- url     : https://prove2.me/submissions/8043be68-684e-4163-b766-c7ec50707a26

module
public import Definitions.Def_AddUN_IdealInvariant
public import Mathlib.MeasureTheory.MeasurableSpace.Card
public import Mathlib.Probability.Distributions.Uniform
public import Mathlib.Probability.ProductMeasure
public import Definitions.Def_AddUN_UniversallyNull
public import Theorems.Thm_IdealInvariant_cof_le


set_option autoImplicit false
@[expose] public section
public section
open Set Filter Topology Cardinal IdealInvariant
open scoped ENNReal
open MeasureTheory
variable {X : Type*} [MeasurableSpace X] {A B : Set X}
namespace MeasureTheory
theorem _root_.solution [MeasurableSpace.CountablyGenerated X] (μ : Measure X) :
    cof μ.nullSets ≤ 𝔠 := by
  have hsub : {B | MeasurableSet B ∧ μ B = 0} ⊆ μ.nullSets := fun B hB ↦ hB.2
  have hcof : ∀ A ∈ μ.nullSets, ∃ B ∈ {B | MeasurableSet B ∧ μ B = 0}, A ⊆ B := fun A hA ↦
    ⟨toMeasurable μ A, ⟨measurableSet_toMeasurable μ A, (measure_toMeasurable A).trans hA⟩,
      subset_toMeasurable μ A⟩
  refine (cof_le hsub hcof).trans ((mk_le_mk_of_subset fun B hB ↦ hB.1).trans ?_)
  obtain ⟨b, hbc, rfl⟩ := MeasurableSpace.CountablyGenerated.isCountablyGenerated (α := X)
  exact MeasurableSpace.cardinal_measurableSet_le_continuum
    ((le_aleph0_iff_set_countable.2 hbc).trans aleph0_le_continuum)
end MeasureTheory
