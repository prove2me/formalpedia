-- Prove2me | solution 2 for OAI.EntropyRateDimension.MeasureEntropy.integral_finite_observation
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T06:22:46.942262+00:00
-- url     : https://prove2.me/submissions/585bd5fc-465e-4fca-a2bc-757218668a52

-- Generated from openai/math@1581d4c lean/OAI/MeasureTheory/SelfSimilar/RandomGrid.lean:L144-L161
-- (upload_full_project.md Phase 4): solution for node OAI.EntropyRateDimension.MeasureEntropy.integral_finite_observation. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_SelfSimilar
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_Basic
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_FiniteEntropy
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_FiniteDistribution
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_MeasureEntropy
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_RandomGrid

-- ---- from OAI.MeasureTheory.SelfSimilar.RandomGrid ----
namespace OAI

universe uα uβ uγ

section
open scoped BigOperators ENNReal
open MeasureTheory
namespace EntropyRateDimension
namespace FiniteDistribution

attribute [local instance] Classical.propDecidable

end FiniteDistribution
namespace RandomGrid

attribute [local instance] OAI.EntropyRateDimension.RandomGrid.unitCircleProbability
end RandomGrid

namespace MeasureEntropy

theorem integral_finite_observation {α : Type uα} {β : Type uβ} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSingletonClass β] (μ : Measure α) [IsFiniteMeasure μ]
    (f : α → β) (hf : Measurable f) (s : Finset β) (hs : ∀ᵐ x ∂μ, f x ∈ s)
    (F : β → ℝ) : ∫ x, F (f x) ∂μ = ∑ b ∈ s, mass μ f b*F b := by
  classical
  have he : (fun x => F (f x)) =ᵐ[μ]
      fun x => ∑ b ∈ s, ({x | f x=b} : Set α).indicator (fun _ => F b) x := by
    filter_upwards [hs] with x hx
    simp only [Set.indicator_apply,Set.mem_ofPred]
    simp [Finset.sum_ite_eq,hx]
  rw [integral_congr_ae he, integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro b _
    change (∫ a, (f ⁻¹' {b}).indicator (fun _ => F b) a ∂μ) = _
    rw [integral_indicator_const _ ((measurableSet_singleton b).preimage hf)]
    rfl
  · intro b _
    exact (integrable_const _).indicator ((measurableSet_singleton b).preimage hf)

end MeasureEntropy

end EntropyRateDimension
end

end OAI

-- ---- platform node ----
open OAI OAI.EntropyRateDimension OAI.EntropyRateDimension.MeasureEntropy
open scoped BigOperators ENNReal
open MeasureTheory


theorem solution.{uα,uβ} : type_of% @_root_.OAI.EntropyRateDimension.MeasureEntropy.integral_finite_observation.{uα,uβ} := @_root_.OAI.EntropyRateDimension.MeasureEntropy.integral_finite_observation.{uα,uβ}
