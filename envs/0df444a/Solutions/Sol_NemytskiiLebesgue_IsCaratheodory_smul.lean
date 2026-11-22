-- Prove2me | solution 1 for NemytskiiLebesgue.IsCaratheodory.smul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:38:44.655384+00:00
-- url     : https://prove2.me/submissions/52323bbf-2abe-46b7-838f-90d0696b39d3

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
    {D : Type*} [TopologicalSpace D] {M : Type*} [TopologicalSpace M]
    {F : Type*} [TopologicalSpace F]
    [SMul M F] [ContinuousSMul M F]
    {f : Ω → D → M} (hf : IsCaratheodory f μ)
    {g : Ω → D → F} (hg : IsCaratheodory g μ) :
    IsCaratheodory (f • g) μ where
  isStronglyMeasurable x :=
    (hf.isStronglyMeasurable x).smul (hg.isStronglyMeasurable x)
  ae_continuous := by
    filter_upwards [hf.ae_continuous, hg.ae_continuous] with ω hfω hgω
    exact hfω.smul hgω
end IsCaratheodory
end NemytskiiLebesgue
