-- Prove2me | solution 1 for MeasureTheory.aleph0_lt_add_nullSets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T07:34:09.061936+00:00
-- url     : https://prove2.me/submissions/01f638dd-36da-4d71-93e6-941abb520d56

module
public import Definitions.Def_AddUN_IdealInvariant
public import Mathlib.MeasureTheory.MeasurableSpace.Card
public import Mathlib.Probability.Distributions.Uniform
public import Mathlib.Probability.ProductMeasure
public import Definitions.Def_AddUN_UniversallyNull
public import Theorems.Thm_IdealInvariant_aleph0_lt_add


set_option autoImplicit false
@[expose] public section
public section
open Set Filter Topology Cardinal IdealInvariant
open scoped ENNReal
open MeasureTheory
variable {X : Type*} [MeasurableSpace X] {A B : Set X}
namespace MeasureTheory
theorem _root_.solution (μ : Measure X) [NullSingletonClass μ] [NeZero μ] :
    ℵ₀ < add μ.nullSets := by
  refine aleph0_lt_add (fun 𝒜 h𝒜 hc ↦ (measure_sUnion_null_iff hc).2 fun A hA ↦ h𝒜 hA)
    ⟨range fun x ↦ ({x} : Set X), ?_, ?_⟩
  · rintro _ ⟨x, rfl⟩
    exact measure_singleton x
  · have h : ⋃₀ (range fun x ↦ ({x} : Set X)) = Set.univ := by
      ext
      simp
    simpa [h] using NeZero.ne μ
end MeasureTheory
