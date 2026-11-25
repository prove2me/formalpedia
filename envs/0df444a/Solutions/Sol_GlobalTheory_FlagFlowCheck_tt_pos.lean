-- Prove2me | solution 1 for GlobalTheory.FlagFlowCheck.tt_pos
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:43:34.334939+00:00
-- url     : https://prove2.me/submissions/d4061370-f641-4a67-910b-cb24d2a1c870

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FlowDomainCriterionHolds
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_MajPos
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_IsIntegralCc
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_UpperHalfSurvey_FirstMinimumRankZero
import Theorems.Thm_GlobalTheory_FlagFlowCheck_c_pos
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_Data_maj_pos
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_MajorantFamilyNorms_c_pos


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
theorem _root_.solution {x : Frame X.Ψ r} (hx : x ∈ X.dom) {ξ : Fin r → E} (hξ : ξ ≠ 0) (τ : X.Ψ) :
    0 < X.tt ξ x τ := by
  have hv : Data.emb τ.1 ξ ≠ 0 := by
    intro h
    apply hξ
    funext a
    exact (map_eq_zero_iff τ.1 τ.1.injective).1 (congrFun h a)
  have := X.maj_pos hx τ hv
  have := c_pos X τ
  unfold Data.tt
  positivity
end GlobalTheory.FlagFlowCheck
