-- Prove2me | solution 1 for GlobalTheory.ThetaSumBound.firstMinimum_sq_mul_iInf_height_le_card
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T13:53:13.537245+00:00
-- url     : https://prove2.me/submissions/4c8072cb-1918-4808-a281-3eabe799bcd7

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TorusAtData
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainPointBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_ModerateCoefficientPositivity
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TorusAtPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TorusAtDataPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SplitC
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExistsThetaRunParametersUniformTorusStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_FirstMinimumSqMulIInfHeightLeCard
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_Data_maj_pos
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_add
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_cc
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_eq_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_intCast
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_inv
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_natCast
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_neg
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_one
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_sub
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_actE_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_add
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_cc
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_eq_zero
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_intCast
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_inv
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_mul
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_natCast
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_neg
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_one
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_sub
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_zero
attribute [local simp] ReciprocityTheory.ChartRestriction.G.I2.actE_apply



set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.I2
open GlobalTheory GlobalTheory.ThetaSumBound
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
namespace GlobalTheory.ThetaSumBound
theorem _root_.solution (X : Data E r) {x : Frame X.Ψ r} (hx : x ∈ X.dom) {ξ : Fin r → E}
    (hξ : ξ ∈ X.Λ) (h0 : ξ ≠ 0) : X.la1 x ^ 2 * ⨅ τ, X.tt ξ x τ ≤ Fintype.card X.Ψ := by
  have hc : ∀ τ : X.Ψ, 0 < X.c τ := fun τ => by
    unfold Data.c
    have : τ.1 X.ξ0 ≠ 0 := (map_ne_zero _).2 X.ξ0_ne
    positivity
  have hpos : ∀ v : Fin r → E, v ≠ 0 → ∀ τ : X.Ψ, 0 < X.c τ * X.maj x τ (Data.emb τ.1 v) := by
    intro v hv0 τ
    have hne : Data.emb τ.1 v ≠ 0 := by
      obtain ⟨a, ha⟩ := Function.ne_iff.1 hv0
      intro h
      exact (map_ne_zero τ.1).2 ha (congrFun h a)
    exact mul_pos (hc τ) (X.maj_pos hx τ hne)
  have hlb : ∀ t ∈ {t | ∃ v ∈ X.Λ, v ≠ 0 ∧ t = ∑ τ, X.c τ * X.maj x τ (Data.emb τ.1 v)}, 0 ≤ t := by
    rintro _ ⟨v, -, hv, rfl⟩
    exact Finset.sum_nonneg fun τ _ => (hpos v hv τ).le
  have h1 : X.la1 x ^ 2 ≤ ∑ τ, X.c τ * X.maj x τ (Data.emb τ.1 ξ) := by
    unfold Data.la1 Data.firstMinimumSq
    rw [Real.sq_sqrt (Real.sInf_nonneg hlb)]
    exact csInf_le ⟨0, hlb⟩ ⟨ξ, hξ, h0, rfl⟩
  have ht0 : 0 ≤ ⨅ τ, X.tt ξ x τ := Real.iInf_nonneg fun τ => (one_div_pos.2 (hpos ξ h0 τ)).le
  refine (mul_le_mul_of_nonneg_right h1 ht0).trans ?_
  rw [Finset.sum_mul]
  calc _ ≤ ∑ _τ : X.Ψ, (1 : ℝ) := by
        refine Finset.sum_le_sum fun τ _ => ?_
        have h2 : ⨅ τ, X.tt ξ x τ ≤ X.tt ξ x τ := ciInf_le (Set.finite_range _).bddBelow τ
        refine (mul_le_mul_of_nonneg_left h2 (hpos ξ h0 τ).le).trans (le_of_eq ?_)
        exact mul_one_div_cancel (hpos ξ h0 τ).ne'
    _ = _ := by simp
end GlobalTheory.ThetaSumBound
