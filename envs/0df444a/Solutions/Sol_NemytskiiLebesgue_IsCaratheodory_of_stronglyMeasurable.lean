-- Prove2me | solution 1 for NemytskiiLebesgue.IsCaratheodory.of_stronglyMeasurable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:38:22.112233+00:00
-- url     : https://prove2.me/submissions/80a3e037-a72d-450b-953a-64cc55563c6d

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
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {D : Type*} [TopologicalSpace D]
    {F : Type*} [TopologicalSpace F]
    {f : Ω → F} (hf : StronglyMeasurable f) :
    IsCaratheodory (fun ω : Ω => fun _ : D => f ω) μ where
  isStronglyMeasurable _ := hf
  ae_continuous := Eventually.of_forall ↓continuous_const
end IsCaratheodory
end NemytskiiLebesgue
