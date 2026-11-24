-- Prove2me | solution 1 for MeasureTheory.flip_apply_of_ne
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T07:34:18.953234+00:00
-- url     : https://prove2.me/submissions/a0e37171-2134-41bc-bf69-325c7e33d6e6

module
public import Definitions.Def_AddUN_UniversallyNull
public import Mathlib.MeasureTheory.Measure.Regular
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.Topology.ClopenBox
public import Definitions.Def_AddUN_CantorMeasure
public import Theorems.Thm_MeasureTheory_flip_apply_self
attribute [local simp] MeasureTheory.flip_apply_self

set_option autoImplicit false
@[expose] public section
public section
open Set Filter Topology TopologicalSpace
open scoped ENNReal
open MeasureTheory
namespace MeasureTheory
theorem _root_.solution {i j : ℕ} (h : j ≠ i) (w : ℕ → Bool) : flip i w j = w j := by
  simp [flip, h]
end MeasureTheory
