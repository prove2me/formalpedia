-- Prove2me | solution 1 for NemytskiiLebesgue.IsCaratheodory.mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:36:39.650186+00:00
-- url     : https://prove2.me/submissions/a076c2dc-8ad9-4477-b462-33f992b97ae3

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
    [Mul F] [ContinuousMul F]
    {f : Ω → D → F} (hf : IsCaratheodory f μ)
    {g : Ω → D → F} (hg : IsCaratheodory g μ) :
    IsCaratheodory (f * g) μ where
  isStronglyMeasurable x :=
    (hf.isStronglyMeasurable x).mul (hg.isStronglyMeasurable x)
  ae_continuous := by
    filter_upwards [hf.ae_continuous, hg.ae_continuous] with ω hfω hgω
    exact hfω.mul hgω
end IsCaratheodory
end NemytskiiLebesgue
