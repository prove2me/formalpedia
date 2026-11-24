-- Prove2me | solution 1 for MeasureTheory.measurableSet_cylinderOn
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T07:37:21.606455+00:00
-- url     : https://prove2.me/submissions/3c8a57e7-c317-4289-90bd-09d6233e5a30

module
public import Definitions.Def_AddUN_UniversallyNull
public import Mathlib.MeasureTheory.Measure.Regular
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.Topology.ClopenBox
public import Definitions.Def_AddUN_CantorMeasure
public import Theorems.Thm_MeasureTheory_isClopen_cylinderOn

set_option autoImplicit false
@[expose] public section
public section
open Set Filter Topology TopologicalSpace
open scoped ENNReal
open MeasureTheory
namespace MeasureTheory
theorem _root_.solution (B : Finset ℕ) (v : ℕ → Bool) : MeasurableSet (cylinderOn B v) :=
  (isClopen_cylinderOn B v).isClosed.measurableSet
end MeasureTheory
