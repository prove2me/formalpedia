-- Prove2me | solution 1 for MeasureTheory.flip_apply_self
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T07:22:02.743207+00:00
-- url     : https://prove2.me/submissions/52bec9cf-fa4f-4e52-8dbc-434b92d77cf0

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
theorem _root_.solution (i : ℕ) (w : ℕ → Bool) : flip i w i = !w i := by simp [flip]
end MeasureTheory
