-- Prove2me | solution 1 for MeasureTheory.subset_saturation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T07:41:20.331929+00:00
-- url     : https://prove2.me/submissions/80ded037-5c9a-4d28-9ddc-4387d3b4ea56

module
public import Definitions.Def_AddUN_InitialCylinder
public import Definitions.Def_AddUN_ZeroOne
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
theorem _root_.solution (E : Set (ℕ → Bool)) : E ⊆ saturation E := fun w hw ↦
  mem_iUnion.2 ⟨∅, by
    have h : flipSet ∅ w = w := by
      ext j
      simp [flipSet]
    rwa [mem_preimage, h]⟩
end MeasureTheory
