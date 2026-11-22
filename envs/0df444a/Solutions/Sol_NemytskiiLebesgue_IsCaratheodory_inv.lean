-- Prove2me | solution 1 for NemytskiiLebesgue.IsCaratheodory.inv
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:38:46.874158+00:00
-- url     : https://prove2.me/submissions/94caaae0-4c8f-4442-95b2-51e0294309c7

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
    [Inv F] [ContinuousInv F]
    {f : Ω → D → F} (hf : IsCaratheodory f μ) :
    IsCaratheodory (f⁻¹) μ where
  isStronglyMeasurable x :=
    (hf.isStronglyMeasurable x).inv
  ae_continuous := by
    filter_upwards [hf.ae_continuous] with ω hω
    exact hω.inv
end IsCaratheodory
end NemytskiiLebesgue
