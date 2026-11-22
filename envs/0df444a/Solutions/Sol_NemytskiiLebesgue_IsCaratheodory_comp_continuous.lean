-- Prove2me | solution 1 for NemytskiiLebesgue.IsCaratheodory.comp_continuous
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:33:58.366255+00:00
-- url     : https://prove2.me/submissions/5165677c-3784-4e82-a101-7108a0aef27a

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
    {g : F → G} (hg : Continuous g) :
    IsCaratheodory (g <| f · ·) μ where
  isStronglyMeasurable x :=
    hg.comp_stronglyMeasurable (hf.isStronglyMeasurable x)
  ae_continuous := by
    filter_upwards [hf.ae_continuous] with ω hω
    exact hg.comp hω
end IsCaratheodory
end NemytskiiLebesgue
