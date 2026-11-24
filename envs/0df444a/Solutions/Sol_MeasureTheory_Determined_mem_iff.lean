-- Prove2me | solution 1 for MeasureTheory.Determined.mem_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T07:34:40.18881+00:00
-- url     : https://prove2.me/submissions/93703503-cafb-440f-a5cd-e4d6f9012153

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
theorem _root_.solution (h : Determined s E) {w w' : ℕ → Bool} (hw : ∀ i ∈ s, w i = w' i) :
    w ∈ E ↔ w' ∈ E :=
  ⟨fun hE ↦ h hw hE, fun hE ↦ h (fun i hi ↦ (hw i hi).symm) hE⟩
end MeasureTheory.Determined
