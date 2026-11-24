-- Prove2me | solution 1 for MeasureTheory.determined_cylinderOn
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T07:22:55.327893+00:00
-- url     : https://prove2.me/submissions/57757855-ca64-4c12-bdd3-30e56b60a0aa

module
public import Definitions.Def_AddUN_UniversallyNull
public import Mathlib.MeasureTheory.Measure.Regular
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.Topology.ClopenBox
public import Definitions.Def_AddUN_CantorMeasure

set_option autoImplicit false
@[expose] public section
public section
open Set Filter Topology TopologicalSpace
open scoped ENNReal
open MeasureTheory
namespace MeasureTheory
theorem _root_.solution (B : Finset ℕ) (v : ℕ → Bool) {s : Set ℕ} (h : ↑B ⊆ s) :
    Determined s (cylinderOn B v) :=
  fun _ _ hw hE i hi ↦ (hw i (h hi)).symm.trans (hE i hi)
end MeasureTheory
