-- Prove2me | solution 1 for MeasureTheory.Determined.compl
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T07:23:13.388089+00:00
-- url     : https://prove2.me/submissions/12ee089c-011b-403c-8902-d27a52f0d452

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
open MeasureTheory.Determined
variable {s t : Set ℕ} {E F : Set (ℕ → Bool)}
namespace MeasureTheory.Determined
theorem _root_.solution (hE : Determined s E) : Determined s Eᶜ :=
  fun _ _ hw h h' ↦ h (hE (fun i hi ↦ (hw i hi).symm) h')
end MeasureTheory.Determined
