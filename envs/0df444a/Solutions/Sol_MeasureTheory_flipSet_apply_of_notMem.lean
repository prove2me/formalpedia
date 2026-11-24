-- Prove2me | solution 1 for MeasureTheory.flipSet_apply_of_notMem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T07:31:56.599601+00:00
-- url     : https://prove2.me/submissions/1fb0a78c-6462-4c8b-8dc1-29e891b80170

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
theorem _root_.solution {s : Finset ℕ} {j : ℕ} (h : j ∉ s) (w : ℕ → Bool) :
    flipSet s w j = w j := by
  simp [flipSet, h]
end MeasureTheory
