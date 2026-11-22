-- Prove2me | solution 1 for NemytskiiLebesgue.IsCaratheodory.neg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:38:32.869368+00:00
-- url     : https://prove2.me/submissions/a13f4e61-56a9-45af-ba45-86239793952a

module
public import Definitions.Def_LeanPool_NemytskiiLebesgue_Caratheodory
public import Definitions.Def_LeanPool_NemytskiiLebesgue_Closure

set_option autoImplicit true
@[expose] public section
public section
open NemytskiiLebesgue
open scoped NemytskiiLebesgue
open MeasureTheory _root_.Filter
namespace NemytskiiLebesgue
namespace IsCaratheodory
theorem _root_.solution
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {D : Type*} [TopologicalSpace D]
    {F : Type*} [TopologicalSpace F]
    [Neg F] [ContinuousNeg F]
    {f : Ω → D → F} (hf : IsCaratheodory f μ) :
    IsCaratheodory (-f) μ where
  isStronglyMeasurable x :=
    (hf.isStronglyMeasurable x).neg
  ae_continuous := by
    filter_upwards [hf.ae_continuous] with ω hω
    exact hω.neg
end IsCaratheodory
end NemytskiiLebesgue
