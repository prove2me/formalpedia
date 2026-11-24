-- Prove2me | solution 1 for GlobalTheory.SW.HeisH.transH_heisH
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:13:34.59788+00:00
-- url     : https://prove2.me/submissions/bac24810-3bc7-47cb-8cde-62b5541e0b44

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ThHEqThSDictionary
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_UnitaryActHalfSpace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HermitianWeilActionUnitaryGroupTestFunctionsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HermitianHeisenbergOperatorLaws
import Theorems.Thm_GlobalTheory_SW_HeisH_expo_key
import Theorems.Thm_GlobalTheory_SW_HeisH_lin_key
import Theorems.Thm_GlobalTheory_SW_HeisH_of_mulVec
import Theorems.Thm_GlobalTheory_SW_HeisH_of_vecMul
import Theorems.Thm_GlobalTheory_SW_HeisH_sum_rows
import Theorems.Thm_GlobalTheory_SW_HeisH_shift_transpose
import Theorems.Thm_GlobalTheory_SW_HeisH_pairT_eq
import Theorems.Thm_GlobalTheory_SW_HeisH_thH_heisH
import Theorems.Thm_GlobalTheory_SW_Base_expo_eq_trace
import Theorems.Thm_GlobalTheory_SW_HAct_blocks
import Theorems.Thm_GlobalTheory_SW_HAct_det_ne
import Theorems.Thm_GlobalTheory_SW_HAct_group_part
import Theorems.Thm_GlobalTheory_SW_HAct_map_blocks
import Theorems.Thm_GlobalTheory_SW_HAct_map_ccT
import Theorems.Thm_GlobalTheory_SW_HAct_map_mem
import Theorems.Thm_GlobalTheory_SW_TransComp_blocks


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.HeisH
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Ψ : Finset (E →+* ℂ)} {n N : ℕ}
namespace GlobalTheory.SW.HeisH
theorem _root_.solution (hΨ : IsType Ψ) {γ : M2 E N} (hγ : γ ∈ UU E N)
    (d' b' : Matrix (Fin n) (Fin N) E) {φ ψ : Matrix (Fin n) (Fin N) E → ℂ}
    (H : TransH Ψ γ φ ψ) :
    TransH Ψ γ (heisH (d' * γ.toBlocks₁₁ + b' * γ.toBlocks₂₁)
      (d' * γ.toBlocks₁₂ + b' * γ.toBlocks₂₂) φ) (heisH d' b' ψ) := by
  intro Z hZ z z'
  have hb := fun τ : Ψ => HAct.blocks (HAct.map_blocks τ.1 γ ▸ HAct.map_mem τ.1 hγ)
  have hQ : ∀ τ, (hDen Ψ γ Z τ).det ≠ 0 := fun τ =>
    HAct.det_ne (hb τ).1 (hb τ).2.1 (hb τ).2.2.1 (hb τ).2.2.2 (hZ τ)
  have h5 : ∀ τ : Ψ, γ.toBlocks₂₁.map τ.1 * (γ.toBlocks₂₂.map τ.1)ᴴ =
      γ.toBlocks₂₂.map τ.1 * (γ.toBlocks₂₁.map τ.1)ᴴ := fun τ => by
    have h := HAct.map_mem τ.1 (HAct.group_part hγ).2.2.1
    rw [HAct.map_ccT, HAct.map_blocks τ.1 γ, fromBlocks_conjTranspose] at h
    simpa using (HAct.blocks h).2.2.2
  set d := d' * γ.toBlocks₁₁ + b' * γ.toBlocks₂₁ with hd
  set b := d' * γ.toBlocks₁₂ + b' * γ.toBlocks₂₂ with hbb
  have md : ∀ τ : Ψ, d.map τ.1 = d'.map τ.1 * γ.toBlocks₁₁.map τ.1 +
      b'.map τ.1 * γ.toBlocks₂₁.map τ.1 := fun τ => by
    rw [hd, Matrix.map_add _ (map_add τ.1), Matrix.map_mul, Matrix.map_mul]
  have mb : ∀ τ : Ψ, b.map τ.1 = d'.map τ.1 * γ.toBlocks₁₂.map τ.1 +
      b'.map τ.1 * γ.toBlocks₂₂.map τ.1 := fun τ => by
    rw [hbb, Matrix.map_add _ (map_add τ.1), Matrix.map_mul, Matrix.map_mul]
  have L : ∀ τ : Ψ,
      (b.map τ.1 + d.map τ.1 * Z τ) * (hDen Ψ γ Z τ)⁻¹ = b'.map τ.1 + d'.map τ.1 * hAct Ψ γ Z τ ∧
      (hDen' Ψ γ Z τ)⁻¹ * ((b.map τ.1)ᴴ + Z τ * (d.map τ.1)ᴴ) =
        (b'.map τ.1)ᴴ + hAct Ψ γ Z τ * (d'.map τ.1)ᴴ ∧
      (b.map τ.1 + d.map τ.1 * Z τ) * ((hDen Ψ γ Z τ)⁻¹ * γ.toBlocks₂₁.map τ.1) =
        d.map τ.1 - d'.map τ.1 * (hDen' Ψ γ Z τ)⁻¹ ∧
      ((hDen Ψ γ Z τ)⁻¹ * γ.toBlocks₂₁.map τ.1) * ((b.map τ.1)ᴴ + Z τ * (d.map τ.1)ᴴ) =
        (d.map τ.1)ᴴ - (hDen Ψ γ Z τ)⁻¹ * (d'.map τ.1)ᴴ := fun τ => by
    rw [md, mb]
    exact lin_key _ _ (hb τ).1 (hb τ).2.1 (hb τ).2.2.1 (hb τ).2.2.2 (h5 τ) (hQ τ)
  have H1 := H Z hZ (fun τ => z τ + (b.map τ.1).map conj + (d.map τ.1).map conj * (Z τ)ᵀ)
    (fun τ => z' τ + b.map τ.1 + d.map τ.1 * Z τ)
  rw [thH_heisH hΨ, thH_heisH hΨ, ← mul_assoc]
  have a1 : (fun τ : Ψ => (Matrix.of fun k => (hDen' Ψ γ Z τ)⁻¹ *ᵥ z τ k) +
      (b'.map τ.1).map conj + (d'.map τ.1).map conj * (hAct Ψ γ Z τ)ᵀ) =
      fun τ : Ψ => Matrix.of fun k => (hDen' Ψ γ Z τ)⁻¹ *ᵥ
        (z τ + (b.map τ.1).map conj + (d.map τ.1).map conj * (Z τ)ᵀ) k := by
    funext τ
    apply transpose_injective
    rw [shift_transpose, of_mulVec, of_mulVec, transpose_transpose, transpose_transpose,
      shift_transpose, add_assoc, add_assoc, Matrix.mul_add, (L τ).2.1]
  have a2 : (fun τ : Ψ => (Matrix.of fun k => z' τ k ᵥ* (hDen Ψ γ Z τ)⁻¹) +
      b'.map τ.1 + d'.map τ.1 * hAct Ψ γ Z τ) =
      fun τ : Ψ => Matrix.of fun k => (z' τ + b.map τ.1 + d.map τ.1 * Z τ) k ᵥ*
        (hDen Ψ γ Z τ)⁻¹ := by
    funext τ
    rw [of_vecMul, of_vecMul, add_assoc, add_assoc, Matrix.add_mul, (L τ).1]
  rw [a1, a2, H1, ← mul_assoc]
  congr 1
  unfold hFac
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, ← Complex.exp_sum, ← Complex.exp_sum,
    mul_left_comm, mul_assoc (∏ τ, (hDen Ψ γ Z τ).det ^ n), ← Complex.exp_add, ← Complex.exp_add]
  congr 2
  simp only [Base.expo_eq_trace, pairT_eq hΨ, sum_rows, shift_transpose, of_mulVec, of_vecMul,
    transpose_transpose, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun τ _ => ?_
  have := expo_key (w := z' τ) (u := (z τ)ᵀ) (L τ).1 (L τ).2.1
    (L τ).2.2.1 (L τ).2.2.2
  linear_combination π * I * this
end GlobalTheory.SW.HeisH
