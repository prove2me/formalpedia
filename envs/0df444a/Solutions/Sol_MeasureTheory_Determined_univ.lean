-- Prove2me | solution 1 for MeasureTheory.Determined.univ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T07:22:12.816458+00:00
-- url     : https://prove2.me/submissions/54037f90-f2f0-41fc-883d-afa245d41fd2

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
theorem _root_.solution : Determined s (Set.univ : Set (ℕ → Bool)) := fun _ _ _ _ ↦ trivial
end MeasureTheory.Determined
