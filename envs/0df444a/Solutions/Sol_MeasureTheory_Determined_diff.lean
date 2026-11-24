-- Prove2me | solution 1 for MeasureTheory.Determined.diff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T07:23:58.952157+00:00
-- url     : https://prove2.me/submissions/ec9cb77c-2573-44c6-8b46-8ab7b89c9480

module
public import Definitions.Def_AddUN_UniversallyNull
public import Mathlib.MeasureTheory.Measure.Regular
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.Topology.ClopenBox
public import Definitions.Def_AddUN_CantorMeasure
public import Theorems.Thm_MeasureTheory_Determined_inter
public import Theorems.Thm_MeasureTheory_Determined_compl

set_option autoImplicit false
@[expose] public section
public section
open Set Filter Topology TopologicalSpace
open scoped ENNReal
open MeasureTheory
open MeasureTheory.Determined
variable {s t : Set ℕ} {E F : Set (ℕ → Bool)}
namespace MeasureTheory.Determined
theorem _root_.solution (hE : Determined s E) (hF : Determined s F) : Determined s (E \ F) :=
  hE.inter hF.compl
end MeasureTheory.Determined
