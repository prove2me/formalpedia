-- Prove2me | solution 1 for MeasureTheory.isClopen_cylinderOn
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T07:36:03.899609+00:00
-- url     : https://prove2.me/submissions/dbbffeb9-6734-40e5-a6f5-315227bdc856

module
public import Definitions.Def_AddUN_UniversallyNull
public import Mathlib.MeasureTheory.Measure.Regular
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.Topology.ClopenBox
public import Definitions.Def_AddUN_CantorMeasure
public import Theorems.Thm_MeasureTheory_cylinderOn_eq_biInter

set_option autoImplicit false
@[expose] public section
public section
open Set Filter Topology TopologicalSpace
open scoped ENNReal
open MeasureTheory
namespace MeasureTheory
theorem _root_.solution (B : Finset ℕ) (v : ℕ → Bool) : IsClopen (cylinderOn B v) := by
  rw [cylinderOn_eq_biInter]
  exact B.finite_toSet.isClopen_biInter fun i _ ↦
    (isClopen_discrete {v i}).preimage (continuous_apply i)
end MeasureTheory
