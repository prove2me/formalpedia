-- Prove2me | solution 1 for MeasureTheory.IsUniversallyNull.of_injOn
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T07:22:32.754027+00:00
-- url     : https://prove2.me/submissions/076241b2-7a9e-49e4-b008-3ca0db47428a

module
public import Definitions.Def_AddUN_UniversallyNull
public import Definitions.Def_AddUN_Transfer
public import Theorems.Thm_MeasureTheory_IsUniversallyNull_mono


set_option autoImplicit false
@[expose] public section
public section
open Set
open MeasureTheory
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSingletonClass Y]
namespace MeasureTheory
namespace IsUniversallyNull
theorem _root_.solution {P : Set Y} (hP : IsUniversallyNull P) {φ : X → Y}
    (hφ : Measurable φ) {A : Set X} (hinj : InjOn φ A) (himg : φ '' A ⊆ P) :
    IsUniversallyNull A := by
  intro μ _ _
  -- The atoms of the image measure form a countable set.
  have hAt : {c : Y | 0 < μ.map φ {c}}.Countable :=
    Measure.countable_meas_pos_of_disjoint_iUnion (μ := μ.map φ)
      (As := fun c : Y ↦ ({c} : Set Y)) (fun c ↦ measurableSet_singleton c)
      (fun a b hab ↦ by simpa [Function.onFun] using hab)
  set At : Set Y := {c : Y | 0 < μ.map φ {c}} with hAtdef
  have hAtm : MeasurableSet At := hAt.measurableSet
  -- Removing the atoms gives a finite measure that vanishes on singletons.
  have hsing : NullSingletonClass ((μ.map φ).restrict Atᶜ) := ⟨fun c ↦ by
    rw [Measure.restrict_apply (measurableSet_singleton c)]
    by_cases hc : c ∈ At
    · have h : ({c} : Set Y) ∩ Atᶜ = ∅ := by
        ext y
        simp only [mem_inter_iff, mem_singleton_iff, mem_compl_iff, mem_empty_iff_false,
          iff_false, not_and, not_not]
        rintro rfl
        exact hc
      rw [h, measure_empty]
    · exact le_antisymm ((measure_mono inter_subset_left).trans (not_lt.1 hc)) zero_le⟩
  have h0 : μ.map φ (P ∩ Atᶜ) = 0 := by
    have := hP ((μ.map φ).restrict Atᶜ)
    rwa [Measure.restrict_apply' hAtm.compl] at this
  have h1 : μ (φ ⁻¹' (P ∩ Atᶜ)) = 0 :=
    le_antisymm ((Measure.le_map_apply hφ.aemeasurable _).trans h0.le) zero_le
  -- The points of `A` that are sent to atoms form a countable set.
  have h2 : (A ∩ φ ⁻¹' At).Countable :=
    countable_of_injective_of_countable_image (hinj.mono inter_subset_left)
      (hAt.mono (image_subset_iff.2 inter_subset_right))
  refine measure_mono_null (t := φ ⁻¹' (P ∩ Atᶜ) ∪ A ∩ φ ⁻¹' At) (fun x hx ↦ ?_)
    (measure_union_null h1 (h2.measure_zero μ))
  by_cases hxa : φ x ∈ At
  · exact Or.inr ⟨hx, hxa⟩
  · exact Or.inl ⟨himg ⟨x, hx, rfl⟩, hxa⟩
end IsUniversallyNull
end MeasureTheory
