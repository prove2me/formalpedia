-- Prove2me | solution 1 for MeasureTheory.flipSet_flipSet
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T07:40:56.210772+00:00
-- url     : https://prove2.me/submissions/74ab765f-fd47-47f4-ae03-d16d3d768344

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
theorem _root_.solution (s t : Finset ℕ) (w : ℕ → Bool) :
    flipSet s (flipSet t w) = flipSet (symmDiff s t) w := by
  ext j
  by_cases hs : j ∈ s <;> by_cases ht : j ∈ t <;> simp [flipSet, Finset.mem_symmDiff, hs, ht]
end MeasureTheory
