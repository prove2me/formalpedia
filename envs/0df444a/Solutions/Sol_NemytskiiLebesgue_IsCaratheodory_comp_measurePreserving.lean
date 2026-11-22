-- Prove2me | solution 1 for NemytskiiLebesgue.IsCaratheodory.comp_measurePreserving
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:39:05.759756+00:00
-- url     : https://prove2.me/submissions/ef25b656-87fa-4194-bf35-457192129f72

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
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {μ : Measure Ω} {μ' : Measure Ω'}
    {D : Type*} [TopologicalSpace D]
    {F : Type*} [TopologicalSpace F]
    {f : Ω → D → F} (hf : IsCaratheodory f μ)
    {g : Ω' → Ω} (hg : MeasurePreserving g μ' μ) :
    IsCaratheodory (f ∘ g) μ' where
  isStronglyMeasurable x :=
    (hf.isStronglyMeasurable x).comp_measurable hg.measurable
  ae_continuous :=
    hg.quasiMeasurePreserving.ae hf.ae_continuous
end IsCaratheodory
end NemytskiiLebesgue
