-- Prove2me | solution 1 for MeasureTheory.cantorMeasure_cylinderOn
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T07:38:12.910998+00:00
-- url     : https://prove2.me/submissions/23aa03de-20aa-4172-ada0-2f4418230d1a

module
public import Definitions.Def_AddUN_UniversallyNull
public import Mathlib.MeasureTheory.Measure.Regular
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.Topology.ClopenBox
public import Definitions.Def_AddUN_CantorMeasure
public import Theorems.Thm_MeasureTheory_flip_apply_self
public import Theorems.Thm_MeasureTheory_flip_flip
public import Theorems.Thm_MeasureTheory_Determined_univ
public import Theorems.Thm_MeasureTheory_cantorMeasure_inter_cylinder
attribute [local simp] MeasureTheory.flip_apply_self
attribute [local simp] MeasureTheory.flip_flip

set_option autoImplicit false
@[expose] public section
public section
open Set Filter Topology TopologicalSpace
open scoped ENNReal
open MeasureTheory
namespace MeasureTheory
theorem _root_.solution (B : Finset ℕ) (v : ℕ → Bool) :
    cantorMeasure (cylinderOn B v) = 2⁻¹ ^ B.card := by
  simpa using cantorMeasure_inter_cylinder B v (E := Set.univ) Determined.univ
end MeasureTheory
