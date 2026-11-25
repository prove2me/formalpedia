-- Prove2me | solution 1 for GlobalTheory.SW.EisConv.det_gram_bot
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:29:30.700122+00:00
-- url     : https://prove2.me/submissions/ef79c046-42db-499a-905e-caf4160de096

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_UnitaryActHalfSpace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_PosSemidefSubMulConjTranspose
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsLinearIndependentOfRatIndependent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SummableEisMajorant
import Theorems.Thm_GlobalTheory_SW_HAct_blocks
import Theorems.Thm_GlobalTheory_SW_HAct_group_part
import Theorems.Thm_GlobalTheory_SW_HAct_map_blocks
import Theorems.Thm_GlobalTheory_SW_HAct_map_ccT
import Theorems.Thm_GlobalTheory_SW_HAct_map_mem
import Theorems.Thm_GlobalTheory_SW_denom_mul_conjTranspose
import Theorems.Thm_GlobalTheory_SW_norm_det_mul_conjTranspose
import Theorems.Thm_GlobalTheory_SW_rowEmb_apply
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
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.EisConv
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {N : ℕ}
namespace GlobalTheory.SW.EisConv
theorem _root_.solution {γ : M2 E N} (h : γ ∈ UU E N) (τ : E →+* ℂ) :
    ((γ.submatrix Sum.inr id).map τ * ((γ.submatrix Sum.inr id).map τ)ᴴ).det.re =
      ‖(γ.toBlocks₂₁.map τ * (I • (1 : Matrix (Fin N) (Fin N) ℂ)) + γ.toBlocks₂₂.map τ).det‖ ^ 2 := by
  have e : (γ.submatrix Sum.inr id).map τ * ((γ.submatrix Sum.inr id).map τ)ᴴ =
      γ.toBlocks₂₁.map τ * (γ.toBlocks₂₁.map τ)ᴴ + γ.toBlocks₂₂.map τ * (γ.toBlocks₂₂.map τ)ᴴ := by
    ext i j
    simp [mul_apply, Fintype.sum_sum_type, toBlocks₂₁, toBlocks₂₂]
  have h1 := HAct.map_mem τ (HAct.group_part h).2.2.1
  rw [HAct.map_ccT, HAct.map_blocks τ γ, fromBlocks_conjTranspose] at h1
  have h2 := (HAct.blocks h1).2.2.2
  simp only [conjTranspose_conjTranspose] at h2
  have h3 : (γ.toBlocks₂₁.map τ * (γ.toBlocks₂₂.map τ)ᴴ).IsHermitian := by
    rw [IsHermitian, conjTranspose_mul, conjTranspose_conjTranspose, h2]
  have h4 := denom_mul_conjTranspose _ _ 0 h3 isHermitian_zero 1
  rw [e]
  have h5 := norm_det_mul_conjTranspose
    (γ.toBlocks₂₁.map τ * (I • (1 : Matrix (Fin N) (Fin N) ℂ)) + γ.toBlocks₂₂.map τ)
  simp only [ofReal_one, mul_one, zero_add, Matrix.mul_zero, one_pow, one_smul] at h4
  rw [h4, add_comm] at h5
  rw [h5, ofReal_re]
end GlobalTheory.SW.EisConv
