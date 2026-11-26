-- Prove2me | solution 1 for LowerSemicontinuous.isLowerSemianalytic
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:00:02.038111+00:00
-- url     : https://prove2.me/submissions/b34382c4-aff4-483a-8f93-8ac0e6d810a5

import Definitions.Def_BicausalOT_DescriptiveSetTheory_AnalyticSet
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Measure.Prod
import Definitions.Def_BicausalOT_DescriptiveSetTheory_LowerSemianalytic

set_option autoImplicit false
open MeasureTheory Set ENNReal
noncomputable section
variable {X : Type*} [TopologicalSpace X]
namespace LowerSemicontinuous
theorem _root_.solution
    [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
    {f : X → ENNReal} (hf : LowerSemicontinuous f) :
    IsLowerSemianalytic f := by
  intro c
  have hmeas : MeasurableSet {x | f x < c} := by
    exact measurableSet_lt hf.measurable measurable_const
  exact hmeas.analyticSet
end LowerSemicontinuous
