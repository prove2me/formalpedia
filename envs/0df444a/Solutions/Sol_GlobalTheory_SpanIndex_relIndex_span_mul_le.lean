-- Prove2me | solution 1 for GlobalTheory.SpanIndex.relIndex_span_mul_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:53:34.853404+00:00
-- url     : https://prove2.me/submissions/8ba42b65-ef42-4705-afb0-157997afdd33

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_CuspidalExponentialDecay
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_RelIndexSupMulRelIndexInfSame
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_SpanImageInfSpanImageOfLinearIndependent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_RelIndexSpanNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_RelIndexIntegralSpanSupermultiplicative
import Theorems.Thm_GlobalTheory_SpanIndex_relIndex_mul_le_of_le
import Theorems.Thm_GlobalTheory_SpanIndex_span_le_inf_span
import Theorems.Thm_GlobalTheory_SpanIndex_relIndex_span_ne_zero
import Theorems.Thm_GlobalTheory_span_inf_sup_overlapping_parts


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up MeasureTheory Topology
open scoped ComplexOrder ENNReal Matrix
open GlobalTheory GlobalTheory.SpanIndex
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
namespace GlobalTheory.SpanIndex
theorem _root_.solution : (∀ (r : ℕ) (X : Data E r) (α β γ : Type) [Fintype α] [Fintype β] [Fintype γ] [DecidableEq α] [DecidableEq β] [DecidableEq γ] (w : α ⊕ β ⊕ γ → Fin r → E), LinearIndependent E w → (∀ a, w a ∈ X.Λ) → ((Submodule.span (𝓞 E) (Set.range (w ∘ (Sum.map id Sum.inl : α ⊕ β → α ⊕ β ⊕ γ)))).toAddSubgroup.relIndex (X.Λ.toAddSubgroup ⊓ (Submodule.span E (Set.range (w ∘ (Sum.map id Sum.inl : α ⊕ β → α ⊕ β ⊕ γ)))).toAddSubgroup)) * ((Submodule.span (𝓞 E) (Set.range (w ∘ (Sum.map id Sum.inr : α ⊕ γ → α ⊕ β ⊕ γ)))).toAddSubgroup.relIndex (X.Λ.toAddSubgroup ⊓ (Submodule.span E (Set.range (w ∘ (Sum.map id Sum.inr : α ⊕ γ → α ⊕ β ⊕ γ)))).toAddSubgroup)) ≤ ((Submodule.span (𝓞 E) (Set.range (w ∘ (Sum.inl : α → α ⊕ β ⊕ γ)))).toAddSubgroup.relIndex (X.Λ.toAddSubgroup ⊓ (Submodule.span E (Set.range (w ∘ (Sum.inl : α → α ⊕ β ⊕ γ)))).toAddSubgroup)) * ((Submodule.span (𝓞 E) (Set.range w)).toAddSubgroup.relIndex (X.Λ.toAddSubgroup ⊓ (Submodule.span E (Set.range w)).toAddSubgroup))) := by
  intro r X α β γ _ _ _ _ _ _ w hw hΛ
  have hw' : LinearIndependent (𝓞 E) w := hw.restrict_scalars' (𝓞 E)
  obtain ⟨i₁, s₁⟩ := GlobalTheory.span_inf_sup_overlapping_parts (𝓞 E) _ α β γ w hw'
  obtain ⟨i₂, s₂⟩ := GlobalTheory.span_inf_sup_overlapping_parts E _ α β γ w hw
  have hne := relIndex_span_ne_zero r X _ w hw hΛ
  rw [← s₁, ← s₂, Submodule.sup_toAddSubgroup, Submodule.sup_toAddSubgroup] at hne
  have key := relIndex_mul_le_of_le _ _ _ _ _
    (span_le_inf_span X.Λ (w ∘ (Sum.map id Sum.inl : α ⊕ β → α ⊕ β ⊕ γ)) fun a => hΛ _)
    (span_le_inf_span X.Λ (w ∘ (Sum.map id Sum.inr : α ⊕ γ → α ⊕ β ⊕ γ)) fun a => hΛ _) hne
  rw [← i₁, ← i₂, ← s₁, ← s₂, Submodule.sup_toAddSubgroup, Submodule.sup_toAddSubgroup]
  exact key
end GlobalTheory.SpanIndex
