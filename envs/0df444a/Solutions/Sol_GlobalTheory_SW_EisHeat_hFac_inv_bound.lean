-- Prove2me | solution 1 for GlobalTheory.SW.EisHeat.hFac_inv_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:19:43.39969+00:00
-- url     : https://prove2.me/submissions/01f9815b-211f-422d-ad2c-f446b3e3c423

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SchwartzBruhatInnerProductSelfNonnegBoundsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_PosSemidefSubMulConjTranspose
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HermitianThetaEisensteinConvergeBoundedStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_EisAutomorphyLinear
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_DerivDerivConstMulCexpBilinearAtZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExhaustStatementPfA
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_EisensteinSeriesOfSchwartzIsHolomorphic
import Theorems.Thm_GlobalTheory_SW_Base_I_mem_Hn
import Theorems.Thm_GlobalTheory_SW_EisTrans_entry_bound
import Theorems.Thm_GlobalTheory_SW_EisTrans_hFac_zero
import Theorems.Thm_GlobalTheory_SW_HAct_map_mem
import Theorems.Thm_GlobalTheory_SW_HermComp_row_rel
import Theorems.Thm_GlobalTheory_SW_Model_I_mem_Hn
import Theorems.Thm_GlobalTheory_SW_norm_det_denom_compare
import Theorems.Thm_GlobalTheory_SW_rowEmb_apply
import Theorems.Thm_GlobalTheory_SW_unitary_act_halfSpace
import Theorems.Thm_GlobalTheory_spanCovol_bot
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.SW.rowEmb_apply
attribute [local simp] GlobalTheory.spanCovol_bot



set_option autoImplicit false
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.EisHeat
variable {E : Type} [Field E] (Ψ : Finset (E →+* ℂ)) {n N : ℕ}
variable [NumberField E] [IsCMField E]
namespace GlobalTheory.SW.EisHeat
theorem _root_.solution (n N : ℕ) {δ : ℝ} (hδ : 0 < δ) (B : ℝ) :
    ∃ K : ℝ, ∀ γ ∈ UU E N, ∀ Z ∈ Hn Ψ N, Z ∈ HnGe Ψ N δ → ∀ z z' : CM Ψ n N,
      (∀ τ a b, ‖Z τ a b‖ ≤ B) → (∀ τ a b, ‖z τ a b‖ ≤ B) → (∀ τ a b, ‖z' τ a b‖ ≤ B) →
      ‖(hFac Ψ γ Z z z')⁻¹‖ ≤
        K * ‖(hFac Ψ γ (fun _ => I • (1 : Matrix (Fin N) (Fin N) ℂ)) (0 : CM Ψ n N) 0)⁻¹‖ := by
  obtain ⟨c, hc, hcmp⟩ := norm_det_denom_compare N δ (B + B) hδ
  refine ⟨∏ _τ : Ψ, (c ^ n)⁻¹ *
    Real.exp (‖2 * (π : ℂ) * I‖ * ∑ _k : Fin n, ∑ _a : Fin N, B * ∑ _b : Fin N, δ⁻¹ * B),
    fun γ hγ Z hZ hZ' z z' hB hz hz' => ?_⟩
  rw [EisTrans.hFac_zero, hFac, ← Finset.prod_inv_distrib, ← Finset.prod_inv_distrib, norm_prod,
    norm_prod, ← Finset.prod_mul_distrib]
  refine Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun τ _ => ?_
  have hr := (HermComp.row_rel _ (HAct.map_mem τ.1 hγ)).2
  have hd := (((unitary_act_halfSpace E Ψ N γ hγ).2 Z hZ).1 τ).1
  have hd0 := (((unitary_act_halfSpace E Ψ N γ hγ).2 _ (Base.I_mem_Hn Ψ)).1 τ).1
  rw [mul_inv, norm_mul, mul_right_comm (c ^ n)⁻¹]
  refine mul_le_mul ?_ ?_ (norm_nonneg _) (by positivity)
  · unfold hDen at hd hd0 ⊢
    change γ.toBlocks₂₂.map τ.1 * (γ.toBlocks₂₁.map τ.1)ᴴ =
      γ.toBlocks₂₁.map τ.1 * (γ.toBlocks₂₂.map τ.1)ᴴ at hr
    generalize γ.toBlocks₂₁.map τ.1 = C at *
    generalize γ.toBlocks₂₂.map τ.1 = D at *
    have h1 : (C * Dᴴ).IsHermitian := by
      unfold IsHermitian
      rw [conjTranspose_mul, conjTranspose_conjTranspose, hr]
    have h2 : (C * Cᴴ + D * Dᴴ).PosDef := by
      have e : C * Cᴴ + D * Dᴴ = (C * (I • (1 : Matrix (Fin N) (Fin N) ℂ)) + D) *
          (C * (I • (1 : Matrix (Fin N) (Fin N) ℂ)) + D)ᴴ := by
        simp only [Matrix.mul_smul, Matrix.mul_one, conjTranspose_add, conjTranspose_smul,
          Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, hr, Complex.star_def, Complex.conj_I,
          smul_add, smul_smul, neg_smul, Matrix.mul_neg, smul_neg, I_mul_I, neg_neg, one_smul]
        abel
      rw [e]
      exact PosDef.mul_conjTranspose_self _
        (Matrix.vecMul_injective_of_isUnit ((isUnit_iff_isUnit_det _).2 (Ne.isUnit hd0)))
    have h3 := (hcmp C D (Z τ) h1 h2 (hZ' τ) fun a b => (norm_add_le _ _).trans
      (add_le_add (hB τ a b) (by simpa using hB τ b a))).1
    rw [norm_inv, norm_inv, norm_pow, norm_pow, ← mul_inv, ← mul_pow]
    have h4 := norm_pos_iff.2 hd0
    exact inv_anti₀ (by positivity) (pow_le_pow_left₀ (by positivity) h3 n)
  · rw [← Complex.exp_neg]
    refine (Complex.norm_exp_le_exp_norm _).trans (Real.exp_le_exp.2 ?_)
    rw [norm_neg, norm_mul]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    have hb := EisTrans.entry_bound hδ hr hd (hZ' τ)
    refine norm_sum_le_of_le _ fun k _ => norm_sum_le_of_le _ fun a _ => ?_
    rw [norm_mul]
    refine mul_le_mul (hz' τ k a) ?_ (norm_nonneg _) ((norm_nonneg _).trans (hz' τ k a))
    rw [Matrix.mulVec, dotProduct]
    refine norm_sum_le_of_le _ fun b _ => ?_
    rw [norm_mul]
    exact mul_le_mul (hb a b) (hz τ k b) (norm_nonneg _) (by positivity)
end GlobalTheory.SW.EisHeat
