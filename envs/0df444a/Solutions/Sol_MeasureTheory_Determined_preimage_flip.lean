-- Prove2me | solution 1 for MeasureTheory.Determined.preimage_flip
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T07:36:07.701926+00:00
-- url     : https://prove2.me/submissions/f6fdbbd1-3e36-4c18-b4a4-d0ae0a7f047a

module
public import Definitions.Def_AddUN_UniversallyNull
public import Mathlib.MeasureTheory.Measure.Regular
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.Topology.ClopenBox
public import Definitions.Def_AddUN_CantorMeasure
public import Theorems.Thm_MeasureTheory_flip_apply_self
public import Theorems.Thm_MeasureTheory_flip_apply_of_ne
public import Theorems.Thm_MeasureTheory_flip_flip
public import Theorems.Thm_MeasureTheory_Determined_mem_iff
attribute [local simp] MeasureTheory.flip_apply_self
attribute [local simp] MeasureTheory.flip_flip

set_option autoImplicit false
@[expose] public section
public section
open Set Filter Topology TopologicalSpace
open scoped ENNReal
open MeasureTheory
open MeasureTheory.Determined
variable {s t : Set ℕ} {E F : Set (ℕ → Bool)}
namespace MeasureTheory.Determined
theorem _root_.solution {i : ℕ} (hE : Determined s E) (hi : i ∉ s) : flip i ⁻¹' E = E := by
  ext w
  exact hE.mem_iff fun j hj ↦ flip_apply_of_ne (by rintro rfl; exact hi hj) w
end MeasureTheory.Determined
