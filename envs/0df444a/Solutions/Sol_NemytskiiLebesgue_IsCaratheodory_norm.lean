-- Prove2me | solution 1 for NemytskiiLebesgue.IsCaratheodory.norm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:36:51.624931+00:00
-- url     : https://prove2.me/submissions/6188617b-5f41-4b40-a41d-58e3b6e072b4

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
    {F : Type*} [NormedAddCommGroup F]
    {f : Ω → D → F} (hf : IsCaratheodory f μ) :
    IsCaratheodory (‖f · ·‖) μ where
  isStronglyMeasurable x :=
    (hf.isStronglyMeasurable x).norm
  ae_continuous := by
    filter_upwards [hf.ae_continuous] with ω hω
    exact hω.norm
end IsCaratheodory
end NemytskiiLebesgue
