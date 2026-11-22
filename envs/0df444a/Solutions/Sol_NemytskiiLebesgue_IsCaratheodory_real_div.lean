-- Prove2me | solution 1 for NemytskiiLebesgue.IsCaratheodory.real_div
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:38:58.906155+00:00
-- url     : https://prove2.me/submissions/cbd10e40-bbc2-44b6-89df-0230ed07d93b

module
public import Definitions.Def_LeanPool_NemytskiiLebesgue_Caratheodory
public import Definitions.Def_LeanPool_NemytskiiLebesgue_Closure
public import Theorems.Thm_NemytskiiLebesgue_IsCaratheodory_div

set_option autoImplicit true
@[expose] public section
public section
open NemytskiiLebesgue
open scoped NemytskiiLebesgue
open MeasureTheory _root_.Filter
namespace NemytskiiLebesgue
namespace IsCaratheodory
theorem _root_.solution
    {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω}
    {m : ℕ} {D : Set ℝ^m}
    {f : Ω → D → ℝ} (hf : IsCaratheodory f μ)
    {g : Ω → D → ℝ} (hg : IsCaratheodory g μ)
    (hg0 : ∀ᵐ ω ∂μ, ∀ x : D, g ω x ≠ 0) :
    IsCaratheodory (f / g) μ where
  isStronglyMeasurable x :=
    ((hf.isStronglyMeasurable x).measurable.div
      (hg.isStronglyMeasurable x).measurable).stronglyMeasurable
  ae_continuous := by
    filter_upwards [hf.ae_continuous, hg.ae_continuous, hg0] with ω hcf hcg hne
    exact hcf.div hcg hne
end IsCaratheodory
end NemytskiiLebesgue
