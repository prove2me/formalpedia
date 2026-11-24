-- Prove2me | solution 1 for MeasureTheory.cylinderOn_insert
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T07:34:52.434255+00:00
-- url     : https://prove2.me/submissions/8c7408c3-e75e-4cec-b62c-2b3bb80b566f

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
theorem _root_.solution {B : Finset ℕ} {i : ℕ} (v : ℕ → Bool) :
    cylinderOn (insert i B) v = cylinderOn B v ∩ {w | w i = v i} := by
  ext w
  simp [cylinderOn, and_comm]
end MeasureTheory
