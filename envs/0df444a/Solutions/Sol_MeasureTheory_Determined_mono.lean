-- Prove2me | solution 1 for MeasureTheory.Determined.mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T07:22:53.76581+00:00
-- url     : https://prove2.me/submissions/05720e2f-4afc-4374-8886-926c40dbb446

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
theorem _root_.solution (h : Determined s E) (hst : s ⊆ t) : Determined t E :=
  fun _ _ hw hE ↦ h (fun i hi ↦ hw i (hst hi)) hE
end MeasureTheory.Determined
