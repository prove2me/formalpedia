-- Prove2me | solution 1 for NemytskiiLebesgue.IsCaratheodory.nnnorm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:39:09.668525+00:00
-- url     : https://prove2.me/submissions/c9567237-22d2-4302-b6c1-da2527922c37

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
    IsCaratheodory (‖f · ·‖₊) μ where
  isStronglyMeasurable x :=
    (hf.isStronglyMeasurable x).nnnorm
  ae_continuous := by
    filter_upwards [hf.ae_continuous] with ω hω
    exact hω.nnnorm
end IsCaratheodory
end NemytskiiLebesgue
