-- Prove2me | solution 1 for GlobalTheory.MinorInt.slice_volume
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T19:37:38.281431+00:00
-- url     : https://prove2.me/submissions/bc7e6bf2-6e06-40ef-830f-2530b229e166

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_LintegralMulRight
import Theorems.Thm_GlobalTheory_MinorInt_star_dot_self_re
import Theorems.Thm_GlobalTheory_MinorInt_form_gram_re
import Theorems.Thm_GlobalTheory_MinorInt_volume_ellipsoid_le
import Theorems.Thm_GlobalTheory_MinorInt_near_one
import Theorems.Thm_GlobalTheory_MinorInt_det_ne_zero_of_form
import Theorems.Thm_GlobalTheory_MinorInt_neg_on_perp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex MeasureTheory
open scoped ComplexConjugate ComplexOrder MatrixOrder
open GlobalTheory GlobalTheory.MinorInt
namespace GlobalTheory.MinorInt
theorem _root_.solution (ι κ : Type*) [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] :
    ∃ δ : ℝ, 0 < δ ∧ ∃ K : ENNReal, K < ⊤ ∧ ∀ (A : Matrix ι ι ℂ) (C : Matrix κ ι ℂ),
      (∀ i j, ‖(Aᴴ * A - Cᴴ * C - 1 : Matrix ι ι ℂ) i j‖ < δ) →
      volume {v : ι ⊕ κ → ℂ | (∀ i, ‖(Aᴴ *ᵥ (v ∘ Sum.inl) - Cᴴ *ᵥ (v ∘ Sum.inr)) i‖ ≤ 1) ∧
        ∑ c, ‖v (Sum.inr c)‖ ^ 2 - ∑ a, ‖v (Sum.inl a)‖ ^ 2 ≤ 2} ≤ K := by
  obtain ⟨δ, hδ, -, hnear⟩ := near_one ι
  set R : ℝ := 2 + 2 * (Fintype.card ι : ℝ) with hR
  refine ⟨δ, hδ, ENNReal.ofReal 2 * volume (Metric.closedBall (0 : ι ⊕ κ → ℂ) (Real.sqrt R)),
    ENNReal.mul_lt_top ENNReal.ofReal_lt_top measure_closedBall_lt_top, fun A C hAC => ?_⟩
  obtain ⟨-, hd2, hform⟩ := hnear _ hAC
  have hA := det_ne_zero_of_form A C hform
  set J : Matrix (ι ⊕ κ) (ι ⊕ κ) ℂ := fromBlocks 1 0 0 (-1) with hJ
  set M : Matrix ι (ι ⊕ κ) ℂ := fromCols Aᴴ (-Cᴴ) with hM
  set H : Matrix (ι ⊕ κ) (ι ⊕ κ) ℂ := (2 : ℂ) • (Mᴴ * M) - J with hH
  have hMv : ∀ v : ι ⊕ κ → ℂ, M *ᵥ v = Aᴴ *ᵥ (v ∘ Sum.inl) - Cᴴ *ᵥ (v ∘ Sum.inr) := by
    intro v
    rw [hM, fromCols_mulVec, neg_mulVec, sub_eq_add_neg]
  have hJv : ∀ v : ι ⊕ κ → ℂ, (star v ⬝ᵥ J *ᵥ v).re =
      ∑ a, ‖v (Sum.inl a)‖ ^ 2 - ∑ c, ‖v (Sum.inr c)‖ ^ 2 := by
    intro v
    have h1 := star_dot_self_re (v ∘ Sum.inl)
    have h2 := star_dot_self_re (v ∘ Sum.inr)
    simp only [Function.comp_apply] at h1 h2
    rw [← h1, ← h2, hJ, fromBlocks_mulVec]
    simp [dotProduct, Fintype.sum_sum_type, neg_mulVec, sub_eq_add_neg]
  have hHv : ∀ v : ι ⊕ κ → ℂ, (star v ⬝ᵥ H *ᵥ v).re =
      2 * ∑ i, ‖(M *ᵥ v) i‖ ^ 2 - (∑ a, ‖v (Sum.inl a)‖ ^ 2 - ∑ c, ‖v (Sum.inr c)‖ ^ 2) := by
    intro v
    rw [hH, sub_mulVec, dotProduct_sub, Complex.sub_re, hJv, smul_mulVec, dotProduct_smul,
      smul_eq_mul, ← form_gram_re]
    simp
  have hherm : H.IsHermitian := by
    refine IsHermitian.sub ?_ ?_
    · unfold IsHermitian
      rw [conjTranspose_smul, (isHermitian_conjTranspose_mul_self M).eq]; simp
    · unfold IsHermitian
      rw [hJ, fromBlocks_conjTranspose]; simp
  have hpsd : H.PosSemidef := by
    refine PosSemidef.of_dotProduct_mulVec_nonneg hherm fun v => ?_
    refine Complex.nonneg_iff.2 ⟨?_, (hherm.im_star_dotProduct_mulVec_self v).symm⟩
    rw [hHv, hMv]
    have := neg_on_perp A C hA hform (v ∘ Sum.inl) (v ∘ Sum.inr)
    simp only [Function.comp_apply] at this
    linarith
  have hJJ : J * J = 1 := by
    rw [hJ, fromBlocks_multiply]; simp [fromBlocks_one]
  have hdJ : ‖J.det‖ = 1 := by
    rw [hJ, det_fromBlocks_zero₂₁, det_neg]; simp
  have hdH : ‖H.det‖ = ‖(1 - (2 : ℂ) • (Aᴴ * A - Cᴴ * C)).det‖ := by
    have h1 : H = -J * (1 - (J * Mᴴ) * ((2 : ℂ) • M)) := by
      rw [hH, Matrix.mul_sub, Matrix.mul_one, Matrix.neg_mul, ← Matrix.mul_assoc,
        ← Matrix.mul_assoc, hJJ, Matrix.one_mul, Matrix.mul_smul]
      abel
    have h2 : M * (J * Mᴴ) = Aᴴ * A - Cᴴ * C := by
      rw [hM, hJ, conjTranspose_fromCols_eq_fromRows_conjTranspose, fromBlocks_mul_fromRows,
        fromCols_mul_fromRows]
      simp [sub_eq_add_neg]
    rw [h1, det_mul, det_one_sub_mul_comm, Matrix.smul_mul, h2, norm_mul, det_neg, norm_mul, hdJ]
    simp
  have hdH' : 1 / 2 ≤ ‖H.det‖ := hdH ▸ hd2
  have hne : H.det ≠ 0 := norm_pos_iff.1 (lt_of_lt_of_le (by norm_num) hdH')
  refine le_trans (measure_mono fun v hv => ?_) ((volume_ellipsoid_le R hpsd hne).trans ?_)
  · obtain ⟨hv1, hv2⟩ := hv
    show _ ≤ R
    rw [hHv, hMv]
    have : ∑ i, ‖(Aᴴ *ᵥ (v ∘ Sum.inl) - Cᴴ *ᵥ (v ∘ Sum.inr)) i‖ ^ 2 ≤ ∑ _i : ι, (1 : ℝ) :=
      Finset.sum_le_sum fun i _ => by have := hv1 i; have := norm_nonneg ((Aᴴ *ᵥ (v ∘ Sum.inl) - Cᴴ *ᵥ (v ∘ Sum.inr)) i); nlinarith
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] at this
    linarith
  · gcongr
    rw [inv_le_comm₀ (norm_pos_iff.2 hne) (by norm_num)]
    linarith
end GlobalTheory.MinorInt
