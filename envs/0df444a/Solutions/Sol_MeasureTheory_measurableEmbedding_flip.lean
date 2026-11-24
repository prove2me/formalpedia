-- Prove2me | solution 1 for MeasureTheory.measurableEmbedding_flip
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T07:34:29.579536+00:00
-- url     : https://prove2.me/submissions/642ea4a3-7222-4d43-ae93-1a10c562de8f

module
public import Definitions.Def_AddUN_UniversallyNull
public import Mathlib.MeasureTheory.Measure.Regular
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.Topology.ClopenBox
public import Definitions.Def_AddUN_CantorMeasure
public import Theorems.Thm_MeasureTheory_flip_flip
public import Theorems.Thm_MeasureTheory_measurePreserving_flip
attribute [local simp] MeasureTheory.flip_flip

set_option autoImplicit false
@[expose] public section
public section
open Set Filter Topology TopologicalSpace
open scoped ENNReal
open MeasureTheory
namespace MeasureTheory
theorem _root_.solution (i : ℕ) : MeasurableEmbedding (flip i) :=
  MeasurableEquiv.measurableEmbedding
    { toFun := flip i
      invFun := flip i
      left_inv := flip_flip i
      right_inv := flip_flip i
      measurable_toFun := (measurePreserving_flip i).measurable
      measurable_invFun := (measurePreserving_flip i).measurable }
end MeasureTheory
