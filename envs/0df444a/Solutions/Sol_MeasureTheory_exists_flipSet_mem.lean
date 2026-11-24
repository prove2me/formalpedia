-- Prove2me | solution 1 for MeasureTheory.exists_flipSet_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T07:44:22.995224+00:00
-- url     : https://prove2.me/submissions/eedd33e3-fb81-4ae0-b37b-6329c4527ce7

module
public import Definitions.Def_AddUN_InitialCylinder
public import Definitions.Def_AddUN_ZeroOne
public import Theorems.Thm_MeasureTheory_measurableSet_saturation
public import Theorems.Thm_MeasureTheory_measure_saturation_eq_one

set_option autoImplicit false
@[expose] public section
public section
open Set
open MeasureTheory
namespace MeasureTheory
theorem _root_.solution {X E : Set (ℕ → Bool)} (hX : cantorMeasure X ≠ 0)
    (hE : MeasurableSet E) (hpos : cantorMeasure E ≠ 0) :
    ∃ x ∈ X, ∃ s : Finset ℕ, flipSet s x ∈ E := by
  by_contra hno
  refine hX (measure_mono_null (t := (saturation E)ᶜ) (fun x hx hsat ↦ ?_) ?_)
  · obtain ⟨s, hs⟩ := mem_iUnion.1 hsat
    exact hno ⟨x, hx, s, hs⟩
  · rw [measure_compl (measurableSet_saturation hE) (measure_ne_top _ _), measure_univ,
      measure_saturation_eq_one hE hpos, tsub_self]
end MeasureTheory
