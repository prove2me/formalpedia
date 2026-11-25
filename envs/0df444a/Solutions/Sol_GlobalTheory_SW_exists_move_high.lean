-- Prove2me | solution 1 for GlobalTheory.SW.exists_move_high
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T07:32:28.69251+00:00
-- url     : https://prove2.me/submissions/942b14d9-a867-4cf2-9ff3-0877ad2ca741

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_UnitaryActHalfSpace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsNearlyPrimitive
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsUnitaryExt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsShortIso
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ShortIsotropicVectorsExistenceSuccOfVeryShortSteStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsUnitaryMoveHermitianHalfSpaceHigh
import Theorems.Thm_GlobalTheory_SW_Reduct_le_trace
import Theorems.Thm_GlobalTheory_SW_Reduct_ge_of_inv_le
import Theorems.Thm_GlobalTheory_SW_Reduct_exists_rows
import Theorems.Thm_GlobalTheory_SW_Base_ccT_mul
import Theorems.Thm_GlobalTheory_SW_HAct_ccT_mul
import Theorems.Thm_GlobalTheory_SW_MinkowskiProductBounds_ccT_mul
import Theorems.Thm_GlobalTheory_SW_NearPrim_exists_rows
import Theorems.Thm_GlobalTheory_SW_RowExt_exists_unitary_ext
import Theorems.Thm_GlobalTheory_SW_exists_nearly_primitive
import Theorems.Thm_GlobalTheory_SW_unitary_act_halfSpace
import Theorems.Thm_GlobalTheory_spanCovol_bot
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.spanCovol_bot



set_option autoImplicit false
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real
open GlobalTheory.SW.Reduct
namespace GlobalTheory.SW
theorem _root_.solution : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Finset (E →+* ℂ)), IsType Ψ → ∀ N : ℕ, ∃ (c : ℕ) (δ : ℝ), 0 < c ∧ 0 < δ ∧ ∀ Z ∈ Hn Ψ N, ∃ γ ∈ UU E N, Den c γ ∧ hAct Ψ γ Z ∈ HnGe Ψ N δ := by
  intro E _ _ _ Ψ hΨ N
  obtain ⟨B, hB0, hB⟩ := exists_rows hΨ N
  obtain ⟨c, C, hc, hprim⟩ := GlobalTheory.SW.exists_nearly_primitive E N
  obtain ⟨c', hc', hext⟩ := GlobalTheory.SW.RowExt.exists_unitary_ext E N c hc
  have hT : 0 < B * (N * (N * C ^ 2)) + 1 := by positivity
  refine ⟨c', (B * (N * (N * C ^ 2)) + 1)⁻¹, hc', inv_pos.2 hT, fun Z hZ => ?_⟩
  obtain ⟨W, w1, w2, w3, w4⟩ := hB Z hZ
  obtain ⟨a, a1, a2, a3, a4⟩ := hprim _ W w1 w2
  have hli : LinearIndependent E fun i => (a * W) i := by
    refine Matrix.vecMul_injective_iff.1 fun x y hxy => ?_
    simp only [← Matrix.vecMul_vecMul] at hxy
    exact Matrix.vecMul_injective_iff_isUnit.2 ((Matrix.isUnit_iff_isUnit_det a).2 (Ne.isUnit a1))
      (Matrix.vecMul_injective_iff.2 w2 hxy)
  obtain ⟨γ, hγ, hden, hrow⟩ := hext (a * W) a3 hli (by
    rw [Base.ccT_mul, Matrix.mul_assoc a, Matrix.mul_assoc a, ← Matrix.mul_assoc _ (ccT W), w3]
    simp) a4
  refine ⟨γ, hγ, hden, fun τ => ?_⟩
  obtain ⟨h1, h2, -⟩ := (GlobalTheory.SW.unitary_act_halfSpace E Ψ N γ hγ).2 Z hZ
  obtain ⟨hQ, -, -, hI⟩ := h1 τ
  have hQe : hDen Ψ γ Z τ =
      a.map τ.1 * (W.map τ.1 * fromRows (Z τ) (1 : Matrix (Fin N) (Fin N) ℂ)) := by
    have : fromCols (γ.toBlocks₂₁.map τ.1) (γ.toBlocks₂₂.map τ.1) = a.map τ.1 * W.map τ.1 := by
      rw [← Matrix.map_mul]
      ext i (j | j) <;> simp [← hrow, Matrix.toBlocks₂₁, Matrix.toBlocks₂₂]
    rw [← Matrix.mul_assoc, ← this, fromCols_mul_fromRows, Matrix.mul_one, hDen]
  have hY := hZ τ
  have hM := w4 τ
  have hY' := h2 τ
  rw [show ∀ (V : Matrix (Fin N) (Fin N ⊕ Fin N) ℂ) (P : Matrix (Fin N ⊕ Fin N) (Fin N) ℂ)
      (Y : Matrix (Fin N) (Fin N) ℂ), V * (P * Y * Pᴴ) * Vᴴ = V * P * Y * (V * P)ᴴ from
    fun V P Y => by simp only [conjTranspose_mul, Matrix.mul_assoc]] at hM
  have ha : ∀ i j, ‖a.map τ.1 i j‖ ≤ C := a2 τ.1
  generalize W.map τ.1 * fromRows (Z τ) (1 : Matrix (Fin N) (Fin N) ℂ) = R at hQe hM
  generalize a.map τ.1 = A at hQe ha
  generalize hDen Ψ γ Z τ = Q at hQ hI hQe
  generalize imH (hAct Ψ γ Z τ) = Y' at hI hY' ⊢
  generalize imH (Z τ) = Y at hI hY hM
  have hu : IsUnit Y.det := (Matrix.isUnit_iff_isUnit_det _).1 hY.isUnit
  have hinv : Y' * (Q * Y⁻¹ * Qᴴ) = 1 := by
    have e : Y⁻¹ * (Qᴴ * Y' * Q) = 1 := by rw [hI]; exact nonsing_inv_mul _ hu
    rw [← Matrix.mul_assoc] at e
    have e' := mul_eq_one_comm.1 e
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc] at e'
    exact mul_eq_one_comm.1 e'
  refine ge_of_inv_le hY'.posSemidef (hY.inv.posSemidef.mul_mul_conjTranspose_same Q).1 hinv hT ?_
  have p1 := (le_trace (hY.inv.posSemidef.mul_mul_conjTranspose_same R) hM).mul_mul_conjTranspose_same A
  have htr : (A * Aᴴ).trace.re ≤ N * (N * C ^ 2) := by
    rw [Matrix.trace, Complex.re_sum]
    refine (Finset.sum_le_card_nsmul _ _ (N * C ^ 2) fun i _ => ?_).trans (by simp)
    rw [Matrix.diag_apply, Matrix.mul_apply, Complex.re_sum]
    refine (Finset.sum_le_card_nsmul _ _ (C ^ 2) fun j _ => ?_).trans (by simp)
    rw [conjTranspose_apply, Complex.star_def, Complex.mul_conj', ← Complex.ofReal_pow,
      Complex.ofReal_re]
    exact pow_le_pow_left₀ (norm_nonneg _) (ha i j) 2
  have p2 := (le_trace (posSemidef_self_mul_conjTranspose A) htr).smul (a := (B : ℂ))
    (by exact_mod_cast hB0)
  refine (congrArg Matrix.PosSemidef ?_).mp ((p1.add p2).add Matrix.PosSemidef.one)
  subst hQe
  simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
    conjTranspose_mul, Matrix.mul_assoc]
  push_cast
  module
end GlobalTheory.SW
