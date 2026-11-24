-- Prove2me | solution 1 for MeasureTheory.aleph0_lt_add_universallyNullSets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T07:35:14.366848+00:00
-- url     : https://prove2.me/submissions/1f8098f1-b20b-4e96-a77a-144d9190d6a6

module
public import Definitions.Def_AddUN_IdealInvariant
public import Mathlib.MeasureTheory.MeasurableSpace.Card
public import Mathlib.Probability.Distributions.Uniform
public import Mathlib.Probability.ProductMeasure
public import Definitions.Def_AddUN_UniversallyNull
public import Theorems.Thm_Set_Countable_isUniversallyNull
public import Theorems.Thm_MeasureTheory_isUniversallyNull_sUnion
public import Theorems.Thm_IdealInvariant_aleph0_lt_add


set_option autoImplicit false
@[expose] public section
public section
open Set Filter Topology Cardinal IdealInvariant
open scoped ENNReal
open MeasureTheory
variable {X : Type*} [MeasurableSpace X] {A B : Set X}
namespace MeasureTheory
theorem _root_.solution (h : ¬ IsUniversallyNull (Set.univ : Set X)) :
    ℵ₀ < add (universallyNullSets X) := by
  refine aleph0_lt_add (fun 𝒜 h𝒜 hc ↦ isUniversallyNull_sUnion hc fun A hA ↦ h𝒜 hA)
    ⟨range fun x ↦ ({x} : Set X), ?_, ?_⟩
  · rintro _ ⟨x, rfl⟩
    exact (countable_singleton x).isUniversallyNull
  · have hU : ⋃₀ (range fun x ↦ ({x} : Set X)) = Set.univ := by
      ext
      simp
    simpa [hU] using h
end MeasureTheory
