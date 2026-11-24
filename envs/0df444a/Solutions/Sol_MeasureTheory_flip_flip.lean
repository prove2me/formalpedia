-- Prove2me | solution 1 for MeasureTheory.flip_flip
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T07:22:39.982215+00:00
-- url     : https://prove2.me/submissions/6180d4ca-02ab-4db2-beec-fcb5e1e6cd42

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
theorem _root_.solution (i : ℕ) (w : ℕ → Bool) : flip i (flip i w) = w := by
  ext j
  by_cases h : j = i <;> simp [flip, h]
end MeasureTheory
