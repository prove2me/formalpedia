-- Prove2me | solution 1 for GlobalTheory.ThetaSumBound.finsum_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T05:52:13.489434+00:00
-- url     : https://prove2.me/submissions/a8c3338f-42bf-48b9-a3f7-5719b344251e

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TorusAtData
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainPointBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_ModerateCoefficientPositivity
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TorusAtPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TorusAtDataPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SplitC
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExistsThetaRunParametersUniformTorusStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_FirstMinimumSqMulIInfHeightLeCard
import Theorems.Thm_GlobalTheory_ThetaSumBound_finsum_mem_le_card_mul
import Theorems.Thm_GlobalTheory_ThetaSumBound_exists_coords
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
omit [IsCMField E]
namespace GlobalTheory.ThetaSumBound
theorem _root_.solution (T : PT E) (S : Set (Fin T.r → Vsp T.dim))
    (hS : ∀ a ∈ S, (∀ j, a j ∈ ZSpan.fundamentalDomain T.b) ∧ ∀ j, ((5 : ℂ) ^ 2) • a j ∈ T.L)
    (f : (Fin T.r → Vsp T.dim) → ℝ) (M : ℝ) (hM : 0 ≤ M) (hf : ∀ a ∈ S, f a ≤ M) :
    ∑ᶠ (a) (_ : a ∈ S), f a ≤ (25 : ℝ) ^ (2 * (Module.finrank ℚ E * T.r) * T.r) * M := by
  have h := finsum_mem_le_card_mul
    (fun (k : Fin T.r → Fin (2 * Fintype.card (Idx T.dim)) → Fin 25) (j : Fin T.r) =>
      ∑ i, (((k j i : ℕ) : ℝ) / 25) • T.b i) S (fun a ha => by
        choose k hk using fun j => exists_coords T.b (a j) ((hS a ha).1 j) ((hS a ha).2 j)
        exact ⟨k, funext hk⟩) f M hM hf
  refine h.trans (mul_le_mul_of_nonneg_right ?_ hM)
  have hN : Fintype.card (Idx T.dim) ≤ Module.finrank ℚ E * T.r := by
    rw [Fintype.card_sigma, ← NumberField.Embeddings.card E ℂ]
    calc _ ≤ ∑ _τ : E →+* ℂ, T.r := Finset.sum_le_sum fun τ _ => by
          have := T.dim_conj τ
          simp only [Fintype.card_fin]; omega
      _ = _ := by simp
  simp only [Fintype.card_fun, Fintype.card_fin]
  push_cast
  rw [← pow_mul]
  exact pow_le_pow_right₀ (by norm_num) (Nat.mul_le_mul_right _ (by omega))
end GlobalTheory.ThetaSumBound
