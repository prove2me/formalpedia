-- Prove2me | solution 1 for GlobalTheory.FlagFlowCheck.scaled_maj_flow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:44:58.214511+00:00
-- url     : https://prove2.me/submissions/51dc85a0-1e78-4202-87ac-f6c9e3579beb

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FlowDomainCriterionHolds
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_MajPos
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_IsIntegralCc
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_UpperHalfSurvey_FirstMinimumRankZero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_flowDomainCriterion_holds


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.FlagFlowCheck
open NumberField Complex ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
namespace GlobalTheory.FlagFlowCheck
theorem _root_.solution {x : Frame X.Ψ r} (hx : x ∈ X.dom) {ξ : Fin r → E} (hξ : X.IsIso ξ)
    (s : X.Ψ → ℂ) (hs : X.flow ξ s x ∈ X.dom) (τ : X.Ψ) :
    X.c τ * X.maj (X.flow ξ s x) τ (Data.emb τ.1 ξ) = 1 / (X.tt ξ x τ + (s τ).im) := by
  have he : X.IsIsoV (fun τ => Data.emb τ.1 ξ) := by
    intro σ
    refine ⟨?_, fun h => hξ.2.2 ?_⟩
    · have h0 := congrArg σ.1 hξ.2.1
      simpa [herm, hermC, Data.emb, emb_cc] using h0
    · funext a
      exact (map_eq_zero_iff σ.1 σ.1.injective).1 (congrFun h a)
  have h := (flowDomainCriterion_holds r X _ he x hx s).2 hs τ
  have h' : X.tt ξ (X.flow ξ s x) τ = X.tt ξ x τ + (s τ).im := h
  rw [← h']
  simp [Data.tt]
end GlobalTheory.FlagFlowCheck
