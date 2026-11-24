-- Prove2me | solution 1 for MeasureTheory.mem_cylinderOn
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T07:23:16.371468+00:00
-- url     : https://prove2.me/submissions/15894789-f88a-4d36-8f6f-bae94b35373a

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
theorem _root_.solution {B : Finset ℕ} {v w : ℕ → Bool} : w ∈ cylinderOn B v ↔ ∀ i ∈ B, w i = v i :=
  Iff.rfl
end MeasureTheory
