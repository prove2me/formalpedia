-- Prove2me | solution 1 for NemytskiiLebesgue.IsCaratheodory.prod
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:39:13.759267+00:00
-- url     : https://prove2.me/submissions/a1d9a8a9-51bc-47fe-baa7-b76ed0123642

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
    {G : Type*} [TopologicalSpace G]
    {f : Ω → D → F} (hf : IsCaratheodory f μ)
    {g : Ω → D → G} (hg : IsCaratheodory g μ) :
    IsCaratheodory (fun ω : Ω => fun x : D => (f ω x, g ω x)) μ where
  isStronglyMeasurable x :=
    StronglyMeasurable.prodMk
      (hf.isStronglyMeasurable x)
      (hg.isStronglyMeasurable x)
  ae_continuous := by
    filter_upwards [hf.ae_continuous, hg.ae_continuous] with ω hfω hgω
    exact Continuous.prodMk hfω hgω
end IsCaratheodory
end NemytskiiLebesgue
