-- Prove2me | solution 1 for NemytskiiLebesgue.IsCaratheodory.of_continuous
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:38:25.128012+00:00
-- url     : https://prove2.me/submissions/8946253d-a89a-4087-b810-4eb4efdc16e7

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
    {f : D → F} (hf : Continuous f) :
    IsCaratheodory (fun _ : Ω => fun x : D => f x) μ where
  isStronglyMeasurable _ := stronglyMeasurable_const
  ae_continuous := Eventually.of_forall ↓hf
end IsCaratheodory
end NemytskiiLebesgue
