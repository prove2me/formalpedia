-- Prove2me | solution 1 for NemytskiiLebesgue.IsCaratheodory.const
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:38:21.668808+00:00
-- url     : https://prove2.me/submissions/0f970382-62bd-48f4-aeb7-f9da99851b6f

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
    (c : F) :
    IsCaratheodory (fun _ : Ω => fun _ : D => c) μ where
  isStronglyMeasurable _ := stronglyMeasurable_const
  ae_continuous := Eventually.of_forall ↓continuous_const
end IsCaratheodory
end NemytskiiLebesgue
