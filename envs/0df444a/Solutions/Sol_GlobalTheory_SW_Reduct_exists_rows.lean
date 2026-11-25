-- Prove2me | solution 1 for GlobalTheory.SW.Reduct.exists_rows
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T07:03:29.966839+00:00
-- url     : https://prove2.me/submissions/1bbd9285-5a7f-4b03-9e72-50775e376146

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_UnitaryActHalfSpace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsNearlyPrimitive
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsUnitaryExt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsShortIso
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ShortIsotropicVectorsExistenceSuccOfVeryShortSteStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsUnitaryMoveHermitianHalfSpaceHigh
import Theorems.Thm_GlobalTheory_SW_Reduct_exists_maj
import Theorems.Thm_GlobalTheory_SW_Reduct_shortIso_all
import Theorems.Thm_GlobalTheory_SW_Reduct_exists_imag
import Theorems.Thm_GlobalTheory_SW_Reduct_den_smul_J
import Theorems.Thm_GlobalTheory_SW_Reduct_map_J
import Theorems.Thm_GlobalTheory_SW_Reduct_li_submatrix
import Theorems.Thm_GlobalTheory_SW_Reduct_hval_eq
import Theorems.Thm_GlobalTheory_SW_Base_ccT_J
import Theorems.Thm_GlobalTheory_SW_Base_ccT_map
import Theorems.Thm_GlobalTheory_SW_Base_map_cc
import Theorems.Thm_GlobalTheory_SW_MinkowskiProductBounds_hval_eq
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
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.Reduct
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
namespace GlobalTheory.SW.Reduct
theorem _root_.solution {Ψ : Finset (E →+* ℂ)} (hΨ : IsType Ψ) (N : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ Z ∈ Hn Ψ N, ∃ W : Matrix (Fin N) (Fin N ⊕ Fin N) E, IntM W ∧
      LinearIndependent E (fun i => W i) ∧ W * Matrix.J (Fin N) E * ccT W = 0 ∧
      ∀ τ : Ψ, (W.map τ.1 * (fromRows (Z τ) (1 : Matrix (Fin N) (Fin N) ℂ) * (imH (Z τ))⁻¹ *
        (fromRows (Z τ) (1 : Matrix (Fin N) (Fin N) ℂ))ᴴ) * (W.map τ.1)ᴴ).trace.re ≤ B := by
  obtain ⟨ξ, D, hξ, hc, hD, hi, hi'⟩ := exists_imag (E := E)
  obtain ⟨C, hC⟩ := shortIso_all hΨ N D hD
  let e : Fin (2 * N) ≃ Fin N ⊕ Fin N := (finCongr (two_mul N)).trans finSumFinEquiv.symm
  have ht : ∀ τ : E →+* ℂ, τ ξ = ((τ ξ).im : ℂ) * I := fun τ => by
    have h1 := Base.map_cc τ ξ
    rw [hc, map_neg] at h1
    have h2 := congrArg Complex.re h1
    simp only [neg_re, conj_re] at h2
    apply Complex.ext <;> simp
    linarith
  have ht0 : ∀ τ : E →+* ℂ, (τ ξ).im ≠ 0 := fun τ h => by
    have := ht τ
    rw [h] at this
    exact hξ (by simpa using this)
  refine ⟨∑ τ : Ψ, N * (|C| / |(τ.1 ξ).im|), by positivity, fun Z hZ => ?_⟩
  have hGi : (ξ • Matrix.J (Fin N) E)⁻¹ = (-ξ⁻¹) • Matrix.J (Fin N) E := by
    apply Matrix.inv_eq_right_inv
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.J_squared]
    simp [hξ]
  have hGm : ∀ τ : E →+* ℂ, (ξ • Matrix.J (Fin N) E).map τ =
      ((τ ξ).im : ℂ) • (I • Matrix.J (Fin N) ℂ) := fun τ => by
    rw [smul_smul, ← ht, ← map_J τ]
    ext i j; simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul]
  let H0 : Ψ → Matrix (Fin N ⊕ Fin N) (Fin N ⊕ Fin N) ℂ := fun τ =>
    fromRows (Z τ) (1 : Matrix (Fin N) (Fin N) ℂ) * (imH (Z τ))⁻¹ *
        (fromRows (Z τ) (1 : Matrix (Fin N) (Fin N) ℂ))ᴴ + I • Matrix.J (Fin N) ℂ
  let H : CM Ψ (2 * N) (2 * N) := fun τ => (((|(τ.1 ξ).im| : ℝ) : ℂ) • H0 τ).submatrix e e
  have hmaj : IsMaj Ψ ((ξ • Matrix.J (Fin N) E).submatrix e e) H := fun τ => by
    obtain ⟨p1, p2⟩ : (H0 τ).PosDef ∧ H0 τ * (I • Matrix.J (Fin N) ℂ) * H0 τ = _ :=
      exists_maj (hZ τ)
    refine ⟨(p1.smul (by exact_mod_cast abs_pos.2 (ht0 τ.1))).submatrix e.injective, ?_⟩
    have h0 : ((τ.1 ξ).im : ℂ) ≠ 0 := by exact_mod_cast ht0 τ.1
    have hinv : (((τ.1 ξ).im : ℂ) • (I • Matrix.J (Fin N) ℂ))⁻¹ =
        ((τ.1 ξ).im : ℂ)⁻¹ • (I • Matrix.J (Fin N) ℂ) := by
      apply Matrix.inv_eq_right_inv
      simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.J_squared]
      have : ((τ.1 ξ).im : ℂ)⁻¹ * I * ((τ.1 ξ).im * I) = -1 := by
        field_simp; simp
      rw [this]; simp
    simp only [H]
    rw [← Matrix.submatrix_map, hGm, Matrix.inv_submatrix_equiv, Matrix.submatrix_mul_equiv,
      Matrix.submatrix_mul_equiv, hinv]
    congr 1
    generalize I • Matrix.J (Fin N) ℂ = G at p2 ⊢
    simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, p2]
    congr 1
    have : ((|(τ.1 ξ).im| : ℝ) : ℂ) * ((|(τ.1 ξ).im| : ℝ) : ℂ) = (τ.1 ξ).im * (τ.1 ξ).im := by
      exact_mod_cast abs_mul_abs_self _
    field_simp
    linear_combination this
  have iso : ∀ W : Matrix (Fin N) (Fin N ⊕ Fin N) E,
      W.submatrix id e * (ξ • Matrix.J (Fin N) E).submatrix e e * ccT (W.submatrix id e) =
        ξ • (W * Matrix.J (Fin N) E * ccT W) := fun W => by
    have : ccT (W.submatrix id e) = (ccT W).submatrix e id := rfl
    rw [this, Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv, Matrix.mul_smul,
      Matrix.smul_mul, Matrix.submatrix_id_id]
  refine Exists.elim (hC ((ξ • Matrix.J (Fin N) E).submatrix e e) H ?_ ?_ ?_ ?_ ?_ hmaj ?_) ?_
  rotate_right
  · rintro W ⟨w1, ⟨w2, w3⟩, w4⟩
    have hW : W = (W.submatrix id e.symm).submatrix id e := by ext i j; simp
    have hli := li_submatrix e.symm w2
    have hint : IntM (W.submatrix id e.symm) := fun i j => w1 _ _
    generalize W.submatrix id e.symm = V at hW hli hint
    subst hW
    rw [iso, smul_eq_zero] at w3
    have w5 := w3.resolve_left hξ
    refine ⟨V, hint, hli, w5, fun τ => ?_⟩
    refine le_trans ?_ (Finset.single_le_sum (f := fun τ : Ψ => N * (|C| / |(τ.1 ξ).im|))
      (fun _ _ => by positivity) (Finset.mem_univ τ))
    have w6 := congrArg (fun X => X.map τ.1) w5
    simp only [Matrix.map_mul, Base.ccT_map, map_J, Matrix.map_zero _ (map_zero τ.1)] at w6
    rw [Matrix.trace, Complex.re_sum]
    refine (Finset.sum_le_card_nsmul _ _ (|C| / |(τ.1 ξ).im|) fun i _ => ?_).trans (by simp)
    have w7 := w4 i τ
    rw [hval_eq] at w7
    simp only [H, H0] at w7
    rw [← Matrix.submatrix_map, Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv,
      Matrix.submatrix_mul_equiv, Matrix.submatrix_id_id, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, w6, smul_zero, add_zero,
      Matrix.smul_apply, smul_eq_mul, Complex.re_ofReal_mul] at w7
    rw [le_div_iff₀' (abs_pos.2 (ht0 τ.1))]
    exact w7.trans (le_abs_self C)
  · have : ccT (ξ • Matrix.J (Fin N) E) = cc ξ • ccT (Matrix.J (Fin N) E) := by
      ext i j; simp [ccT, cc]
    change (ccT (ξ • Matrix.J (Fin N) E)).submatrix e e = _
    rw [this, hc, Base.ccT_J]; simp
  · rw [Matrix.det_submatrix_equiv_self, Matrix.det_smul]
    exact mul_ne_zero (pow_ne_zero _ hξ) (Matrix.isUnit_det_J _ _).ne_zero
  · exact fun i j => den_smul_J hi _ _
  · rw [Matrix.inv_submatrix_equiv, hGi]
    exact fun i j => den_smul_J (by simpa using hi'.neg) _ _
  · refine ⟨(fromCols (0 : Matrix (Fin N) (Fin N) E) (1 : Matrix (Fin N) (Fin N) E)).submatrix id e,
      li_submatrix e ?_, ?_⟩
    · have : LinearIndependent E fun i : Fin N ⊕ Fin N => (1 : M2 E N) i :=
        Matrix.linearIndependent_rows_iff_isUnit.2 isUnit_one
      convert this.comp Sum.inr Sum.inr_injective using 1
      ext i (j | j) <;> simp [Matrix.one_apply]
    · rw [iso]
      convert smul_zero ξ
      ext i j
      simp [ccT, cc, Matrix.J, Matrix.mul_apply, Matrix.one_apply]
  · intro v _ _
    refine Finset.sum_nonneg fun τ _ => ?_
    have := (hmaj τ).1.posSemidef.dotProduct_mulVec_nonneg (star fun a => τ.1 (v a))
    rw [star_star] at this
    exact (Complex.nonneg_iff.1 this).1
end GlobalTheory.SW.Reduct
