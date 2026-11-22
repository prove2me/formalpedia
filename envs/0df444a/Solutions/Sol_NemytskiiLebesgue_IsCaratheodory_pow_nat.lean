-- Prove2me | solution 1 for NemytskiiLebesgue.IsCaratheodory.pow_nat
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:36:45.564398+00:00
-- url     : https://prove2.me/submissions/a197b52c-04e0-48d4-804a-558b1bfe4876

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
    [Monoid F] [ContinuousMul F]
    {f : Ω → D → F} (hf : IsCaratheodory f μ) (n : ℕ) :
    IsCaratheodory (f ^ n) μ where
  isStronglyMeasurable x :=
    (hf.isStronglyMeasurable x).pow n
  ae_continuous := by
    filter_upwards [hf.ae_continuous] with ω hω
    exact hω.pow n
end IsCaratheodory
end NemytskiiLebesgue
