-- Prove2me | solution 1 for MeasureTheory.flipSet_preimage_saturation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T07:42:14.507967+00:00
-- url     : https://prove2.me/submissions/c5fade99-25e6-46f5-a2c8-e429226a6b3e

module
public import Definitions.Def_AddUN_InitialCylinder
public import Definitions.Def_AddUN_ZeroOne
public import Theorems.Thm_MeasureTheory_flipSet_flipSet
public import Theorems.Thm_MeasureTheory_flip_apply_self
public import Theorems.Thm_MeasureTheory_flip_flip
attribute [local simp] MeasureTheory.flip_apply_self
attribute [local simp] MeasureTheory.flip_flip



set_option autoImplicit false
@[expose] public section
public section
open Set
open MeasureTheory
namespace MeasureTheory
theorem _root_.solution (E : Set (ℕ → Bool)) (t : Finset ℕ) :
    flipSet t ⁻¹' saturation E = saturation E := by
  ext w
  simp only [saturation, mem_preimage, mem_iUnion]
  constructor
  · rintro ⟨s, hs⟩
    exact ⟨symmDiff s t, by rwa [← flipSet_flipSet]⟩
  · rintro ⟨s, hs⟩
    exact ⟨symmDiff s t, by rwa [flipSet_flipSet, symmDiff_symmDiff_cancel_right]⟩
end MeasureTheory
