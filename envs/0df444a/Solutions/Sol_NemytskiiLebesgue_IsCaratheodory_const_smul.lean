-- Prove2me | solution 1 for NemytskiiLebesgue.IsCaratheodory.const_smul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:38:46.432472+00:00
-- url     : https://prove2.me/submissions/ed15fa97-e044-4c05-a423-696dc43a8247

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
    {D : Type*} [TopologicalSpace D] {M : Type*}
    {F : Type*} [TopologicalSpace F]
    [SMul M F] [ContinuousConstSMul M F]
    {f : Ω → D → F} (hf : IsCaratheodory f μ) (c : M) :
    IsCaratheodory (c • f) μ where
  isStronglyMeasurable x :=
    (hf.isStronglyMeasurable x).const_smul c
  ae_continuous := by
    filter_upwards [hf.ae_continuous] with ω hω
    exact hω.const_smul c
end IsCaratheodory
end NemytskiiLebesgue
