-- Prove2me | solution 1 for MeasureTheory.Determined.inter
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T07:22:18.532378+00:00
-- url     : https://prove2.me/submissions/1f91a64a-e6cb-4af1-a312-30f16e150665

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
theorem _root_.solution (hE : Determined s E) (hF : Determined s F) : Determined s (E ∩ F) :=
  fun _ _ hw h ↦ ⟨hE hw h.1, hF hw h.2⟩
end MeasureTheory.Determined
