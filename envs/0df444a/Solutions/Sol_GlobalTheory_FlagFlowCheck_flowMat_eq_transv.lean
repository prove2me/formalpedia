-- Prove2me | solution 1 for GlobalTheory.FlagFlowCheck.flowMat_eq_transv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:44:51.395809+00:00
-- url     : https://prove2.me/submissions/7cc3ca76-768a-4d84-856d-756d5fb03b05

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FlowDomainCriterionHolds
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_MajPos
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_IsIntegralCc
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_UpperHalfSurvey_FirstMinimumRankZero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_cc_mul


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
theorem _root_.solution (ξ : Fin r → E) (τ : X.Ψ) (s : E) :
    X.flowMat ξ τ (τ.1 s) = (transvMat X.Gm ξ (s * X.κ0)).map τ.1 := by
  have hcc : cc X.κ0 = -X.κ0 := by
    rcases X.κ0_xi with h | h
    · rw [h, cc_mul, X.ξ0_im]; have : cc (2 : E) = 2 := map_ofNat _ 2
      rw [this]; ring
    · have e : -(2 * X.ξ0) = 0 - 2 * X.ξ0 := by ring
      rw [h, e, cc_sub, cc_zero, cc_mul, X.ξ0_im]; have : cc (2 : E) = 2 := map_ofNat _ 2
      rw [this]; ring
  have hre : (τ.1 X.κ0).re = 0 := by
    have h1 : conj (τ.1 X.κ0) = -(τ.1 X.κ0) := by rw [← emb_cc, hcc, map_neg]
    have h2 := congrArg Complex.re h1
    simp only [Complex.conj_re, Complex.neg_re] at h2
    linarith
  have hn : ‖τ.1 X.κ0‖ = X.c τ := by
    unfold Data.c
    rcases X.κ0_xi with h | h <;> simp [h, map_ofNat]
  have hk : τ.1 X.κ0 = -(I * X.c τ) := by
    have h3 : ‖τ.1 X.κ0‖ = |(τ.1 X.κ0).im| := (Complex.abs_im_eq_norm.2 hre).symm
    rw [abs_of_neg (X.κ0_sign τ)] at h3
    apply Complex.ext <;> simp [hre]
    linarith
  ext a b
  have h1 : τ.1 (if a = b then 1 else 0) = if a = b then 1 else 0 := by split_ifs <;> simp
  simp only [Data.flowMat, transvMat, Matrix.of_apply, Matrix.map_apply, map_add, map_mul, map_sum,
    h1, hk, emb_cc]
  ring
end GlobalTheory.FlagFlowCheck
