-- Prove2me | solution 1 for GlobalTheory.SW.Parab.trans_parabolic
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T03:11:56.620373+00:00
-- url     : https://prove2.me/submissions/91d6ccdd-2ccb-4fc4-b50a-2b00f28590c6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IMemSiegel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_RationalSchwartzBruhatAlgebraIntegralLinearStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SchwartzBruhatInvariantIntegralMatrixMulStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SiegelThetaTransformationSiegelParabolic
import Theorems.Thm_GlobalTheory_SW_Parab_parChar_mul_conj
import Theorems.Thm_GlobalTheory_SW_Parab_isSB_parChar_mul
import Theorems.Thm_GlobalTheory_SW_Parab_qv_row_mul
import Theorems.Thm_GlobalTheory_SW_Parab_qv_bilin
import Theorems.Thm_P2M_GlobalTheory_SW_Parab_qm_mul__cae64bfa856c
import Theorems.Thm_GlobalTheory_SW_LinChange_haar_mul
import Theorems.Thm_GlobalTheory_SW_isSB_algebra_haar_linear

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Matrix Complex GlobalTheory.SW
open scoped ComplexConjugate Real
namespace GlobalTheory.SW.Parab
open Matrix Complex in
open scoped ComplexConjugate Real in
private lemma parabolic_exponent_term_eq {ι : Type} [Fintype ι] (A B : Matrix ι ι ℚ) (τ : Matrix ι ι ℂ)
    (v : ι → ℚ) (z : ι → ℂ) :
    _root_.GlobalTheory.SW.qv v ⬝ᵥ ((_root_.GlobalTheory.SW.qm A * τ + _root_.GlobalTheory.SW.qm B) *
        _root_.GlobalTheory.SW.qm Aᵀ) *ᵥ _root_.GlobalTheory.SW.qv v +
      2 * _root_.GlobalTheory.SW.qv v ⬝ᵥ (z ᵥ* _root_.GlobalTheory.SW.qm Aᵀ) =
    (_root_.GlobalTheory.SW.qv v ᵥ* _root_.GlobalTheory.SW.qm A) ⬝ᵥ τ *ᵥ
        (_root_.GlobalTheory.SW.qv v ᵥ* _root_.GlobalTheory.SW.qm A) +
      2 * (_root_.GlobalTheory.SW.qv v ᵥ* _root_.GlobalTheory.SW.qm A) ⬝ᵥ z +
      ((v ⬝ᵥ (B * Aᵀ) *ᵥ v : ℚ) : ℂ) := by
  rw [_root_.GlobalTheory.SW.Parab.qv_bilin, _root_.GlobalTheory.SW.Parab.qm_mul']
  have hT : _root_.GlobalTheory.SW.qm Aᵀ = (_root_.GlobalTheory.SW.qm A)ᵀ := by
    ext i j
    simp [_root_.GlobalTheory.SW.qm]
  rw [hT, add_mul, add_mulVec, dotProduct_add, ← mulVec_mulVec, ← mulVec_mulVec, mulVec_transpose,
    dotProduct_mulVec, vecMul_transpose, dotProduct_mulVec _ (_root_.GlobalTheory.SW.qm A) z]
  ring
end GlobalTheory.SW.Parab
end

set_option autoImplicit false
open Matrix Complex GlobalTheory.SW
open scoped ComplexConjugate Real
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.Parab
open Matrix Complex
open scoped ComplexConjugate Real
namespace GlobalTheory.SW.Parab
namespace _root_.GlobalTheory.SW.Parab
theorem _root_.solution : ∀ (κ ι : Type) [Fintype κ] [Fintype ι] [DecidableEq ι]
    (σ : Matrix (ι ⊕ ι) (ι ⊕ ι) ℚ), Even (Fintype.card κ) → σ ∈ Matrix.symplecticGroup ι ℚ →
    σ.toBlocks₂₁ = 0 → ∃ ω : (Matrix κ ι ℚ → ℂ) → (Matrix κ ι ℚ → ℂ), ∀ φ, _root_.GlobalTheory.SW.IsSB φ →
    _root_.GlobalTheory.SW.IsSB (ω φ) ∧ _root_.GlobalTheory.SW.TransS σ φ (ω φ) ∧
    ∀ φ', _root_.GlobalTheory.SW.IsSB φ' → _root_.GlobalTheory.SW.ip (ω φ) (ω φ') =
      _root_.GlobalTheory.SW.ip φ φ' := by
  intro κ ι _ _ _ σ hev hσ hC
  classical
  have hDA : σ.toBlocks₂₂ * σ.toBlocks₁₁ᵀ = 1 := by
    have h := hσ
    rw [SymplecticGroup.mem_iff, ← fromBlocks_toBlocks σ, hC] at h
    simp only [J, fromBlocks_transpose, fromBlocks_multiply, fromBlocks_inj] at h
    simpa using h.2.2.1
  set A := σ.toBlocks₁₁ with hA
  set B := σ.toBlocks₁₂ with hB
  set D := σ.toBlocks₂₂ with hD
  have hAD : Aᵀ * D = 1 := mul_eq_one_comm.mp hDA
  have hDtA : Dᵀ * A = 1 := by simpa [Matrix.transpose_mul] using congrArg Matrix.transpose hAD
  have hADt : A * Dᵀ = 1 := mul_eq_one_comm.mp hDtA
  have hdet : D.det * A.det = 1 := by
    have h := congrArg Matrix.det hDA
    rwa [det_mul, det_transpose, det_one] at h
  have hdetA : A.det ≠ 0 := fun h => by simp [h] at hdet
  let e : Matrix κ ι ℚ ≃ Matrix κ ι ℚ :=
    { toFun := fun x => x * A
      invFun := fun x => x * Dᵀ
      left_inv := fun x => by simp [Matrix.mul_assoc, hADt]
      right_inv := fun x => by simp [Matrix.mul_assoc, hDtA] }
  let c : ℂ := (_root_.GlobalTheory.SW.qm D).det ^ (Fintype.card κ / 2)
  refine ⟨fun φ => c • fun x => _root_.GlobalTheory.SW.Parab.parChar (B * Aᵀ) x * φ (x * A), fun φ hφ => ?_⟩
  have hφA := (_root_.GlobalTheory.SW.LinChange.haar_mul ℚ κ ι φ hφ).1 A hdetA
  have hf := _root_.GlobalTheory.SW.Parab.isSB_parChar_mul (B * Aᵀ) _ hφA.1
  refine ⟨(_root_.GlobalTheory.SW.isSB_algebra_haar_linear ℚ κ ι _ _ hf hf).2.1 c, ?_, ?_⟩
  · intro τ hτ ζ
    have hqD : (_root_.GlobalTheory.SW.qm D)⁻¹ = _root_.GlobalTheory.SW.qm Aᵀ := by
      refine Matrix.inv_eq_right_inv ?_
      rw [← _root_.GlobalTheory.SW.Parab.qm_mul', hDA]
      ext i j
      by_cases hij : i = j <;> simp [_root_.GlobalTheory.SW.qm, one_apply, hij]
    have h0 : _root_.GlobalTheory.SW.qm σ.toBlocks₂₁ = 0 := by
      rw [hC]
      ext i j
      simp [_root_.GlobalTheory.SW.qm]
    unfold _root_.GlobalTheory.SW.thS _root_.GlobalTheory.SW.spAct _root_.GlobalTheory.SW.spDen
    rw [h0, ← hA, ← hB, ← hD]
    simp only [zero_mul, zero_add, Matrix.mul_zero, zero_mulVec, dotProduct_zero, Finset.sum_const_zero,
      mul_zero, Complex.exp_zero, mul_one, hqD, Pi.smul_apply, smul_eq_mul]
    conv_rhs => rw [← e.tsum_eq, ← tsum_mul_left]
    congr 1
    funext x
    simp only [e, Equiv.coe_fn_mk, _root_.GlobalTheory.SW.Parab.qv_row_mul, parabolic_exponent_term_eq,
      Finset.sum_add_distrib]
    unfold _root_.GlobalTheory.SW.Parab.parChar
    rw [Rat.cast_sum, mul_add, Complex.exp_add, Complex.exp_neg]
    field_simp
    exact mul_comm _ _
  · intro φ' hφ'
    have hconj := (_root_.GlobalTheory.SW.isSB_algebra_haar_linear ℚ κ ι φ' φ' hφ' hφ').2.2.2.1
    have hg : _root_.GlobalTheory.SW.IsSB fun x => φ x * conj (φ' x) :=
      (_root_.GlobalTheory.SW.isSB_algebra_haar_linear ℚ κ ι _ _ hφ hconj).2.2.1
    have hgA := (_root_.GlobalTheory.SW.LinChange.haar_mul ℚ κ ι _ hg).1 A hdetA
    have hgA' := (_root_.GlobalTheory.SW.isSB_algebra_haar_linear ℚ κ ι _ _ hgA.1 hgA.1).2.2.2.2.2.1
    unfold _root_.GlobalTheory.SW.ip
    have hpt : (fun x => (c • fun x => _root_.GlobalTheory.SW.Parab.parChar (B * Aᵀ) x * φ (x * A)) x *
        conj ((c • fun x => _root_.GlobalTheory.SW.Parab.parChar (B * Aᵀ) x * φ' (x * A)) x)) =
        (c * conj c) • fun x => φ (x * A) * conj (φ' (x * A)) := by
      funext x
      simp only [Pi.smul_apply, smul_eq_mul, map_mul]
      linear_combination (c * conj c * φ (x * A) * conj (φ' (x * A))) *
        _root_.GlobalTheory.SW.Parab.parChar_mul_conj (B * Aᵀ) x
    rw [hpt, hgA', hgA.2, ← mul_assoc]
    have hdetD : (_root_.GlobalTheory.SW.qm D).det = (D.det : ℂ) := by
      rw [_root_.GlobalTheory.SW.qm]
      exact ((Rat.castHom ℂ).map_det D).symm
    obtain ⟨r, hr⟩ := hev
    have hn : Fintype.card κ / 2 = r := by omega
    have hq : (D.det ^ r * D.det ^ r * |A.det| ^ (r + r) : ℚ) = 1 := by
      rw [Even.pow_abs ⟨r, rfl⟩, ← pow_add, ← mul_pow, hdet, one_pow]
    have hconst : ∀ N : ℚ, N = A.det → c * conj c * ((|N| : ℚ) : ℂ) ^ Fintype.card κ = 1 := by
      rintro N rfl
      simp only [c, hdetD, hn, map_pow, map_ratCast]
      rw [hr]
      exact_mod_cast hq
    rw [hconst _ ?_, one_mul]
    exact congrFun (congrArg DFunLike.coe (Algebra.norm_self ℚ)) A.det
end _root_.GlobalTheory.SW.Parab
end GlobalTheory.SW.Parab
