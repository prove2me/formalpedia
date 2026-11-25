-- Prove2me | solution 1 for GlobalTheory.FlagFlowCheck.first_minimum_rank_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:44:45.628465+00:00
-- url     : https://prove2.me/submissions/47a9426c-1dc6-41a7-bb7c-6b7054ca5e06

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FlowDomainCriterionHolds
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_MajPos
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_IsIntegralCc
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_UpperHalfSurvey_FirstMinimumRankZero

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
theorem _root_.solution (Y : Data E 0) (x : Frame Y.Ψ 0) : Y.la1 x = 0 := by
  have : {t | ∃ v ∈ Y.Λ, v ≠ 0 ∧ t = ∑ τ, Y.c τ * Y.maj x τ (Data.emb τ.1 v)} = (∅ : Set ℝ) := by
    ext t
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
    rintro ⟨v, -, hv, -⟩
    exact hv (Subsingleton.elim _ _)
  unfold Data.la1 Data.firstMinimumSq
  rw [this]
  simp
end GlobalTheory.FlagFlowCheck
