-- Prove2me | solution 1 for MeasureTheory.cylinderOn_eq_biInter
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T07:34:47.312636+00:00
-- url     : https://prove2.me/submissions/f51d107c-5121-433b-a569-bb139860055e

module
public import Definitions.Def_AddUN_UniversallyNull
public import Mathlib.MeasureTheory.Measure.Regular
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.Topology.ClopenBox
public import Definitions.Def_AddUN_CantorMeasure
public import Theorems.Thm_MeasureTheory_flip_apply_self
public import Theorems.Thm_MeasureTheory_flip_flip
attribute [local simp] MeasureTheory.flip_apply_self
attribute [local simp] MeasureTheory.flip_flip

set_option autoImplicit false
@[expose] public section
public section
open Set Filter Topology TopologicalSpace
open scoped ENNReal
open MeasureTheory
namespace MeasureTheory
theorem _root_.solution (B : Finset ℕ) (v : ℕ → Bool) :
    cylinderOn B v = ⋂ i ∈ B, (fun w : ℕ → Bool ↦ w i) ⁻¹' {v i} := by
  ext w
  simp [cylinderOn]
end MeasureTheory
