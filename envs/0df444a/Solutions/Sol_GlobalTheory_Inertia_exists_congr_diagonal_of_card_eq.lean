-- Prove2me | solution 1 for GlobalTheory.Inertia.exists_congr_diagonal_of_card_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T05:29:08.060253+00:00
-- url     : https://prove2.me/submissions/c6d85adc-7350-463f-96fa-189c6ac8b2b4

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_ExistsOrthogonalBasisDotProductApplyEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_PosIndexMapEqCardOfCongrDiagonal
import Theorems.Thm_GlobalTheory_Inertia_posIndex_neg
import Theorems.Thm_GlobalTheory_Inertia_negIndex_neg
import Theorems.Thm_GlobalTheory_Inertia_congr_mul
import Theorems.Thm_GlobalTheory_Inertia_posIndex_eq_card_of_congr_diagonal
import Theorems.Thm_GlobalTheory_Inertia_exists_congr_diagonal_real
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.Inertia.posIndex_neg
attribute [local simp] GlobalTheory.Inertia.negIndex_neg

set_option autoImplicit false
open GlobalTheory GlobalTheory.Inertia
open Module Matrix ReciprocityTheory.ChartRestriction.G
open scoped ComplexConjugate
variable {n m : Type*} [Fintype n] [Fintype m]
variable [DecidableEq n]
namespace GlobalTheory.Inertia
theorem _root_.solution {G : Matrix n n ℂ} (hG : G.IsHermitian)
    (hG0 : G.det ≠ 0) {e : n → ℝ} (he : ∀ k, e k ≠ 0)
    (hcard : (Finset.univ.filter fun k => 0 < e k).card = posIndex G) :
    ∃ P : Matrix n n ℂ, P.det ≠ 0 ∧ Pᵀ * G * P.map conj = diagonal fun k => (e k : ℂ) := by
  obtain ⟨P, d, hP, hd, hne⟩ := exists_congr_diagonal_real hG
  replace hne := hne hG0
  rw [posIndex_eq_card_of_congr_diagonal hP hd] at hcard
  simp only [Complex.ofReal_re] at hcard
  rw [← Fintype.card_subtype, ← Fintype.card_subtype] at hcard
  let f : {k // 0 < e k} ≃ {k // 0 < d k} := Fintype.equivOfCardEq hcard
  let σ : Equiv.Perm n := f.extendSubtype
  have hσ : ∀ k, 0 < e k / d (σ k) := by
    intro k
    by_cases hk : 0 < e k
    · exact div_pos hk (f.extendSubtype_mem k hk)
    · exact div_pos_of_neg_of_neg ((not_lt.1 hk).lt_of_ne (he k))
        ((not_lt.1 (f.extendSubtype_not_mem k hk)).lt_of_ne (hne _))
  have h1 : (P.submatrix id σ)ᵀ * G * (P.submatrix id σ).map conj =
      diagonal fun k => (d (σ k) : ℂ) := by
    have : (P.submatrix id σ)ᵀ * G * (P.submatrix id σ).map conj =
        (Pᵀ * G * P.map conj).submatrix σ σ := rfl
    rw [this, hd, submatrix_diagonal_equiv]
    rfl
  refine ⟨P.submatrix id σ * diagonal fun k => (√(e k / d (σ k)) : ℂ), ?_, ?_⟩
  · rw [det_mul, det_permute', det_diagonal]
    refine mul_ne_zero (mul_ne_zero ?_ hP) (Finset.prod_ne_zero_iff.2 fun k _ => ?_)
    · rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]
    · exact Complex.ofReal_ne_zero.2 (Real.sqrt_pos.2 (hσ k)).ne'
  · rw [congr_mul, h1, diagonal_transpose, diagonal_map (map_zero _), diagonal_mul_diagonal,
      diagonal_mul_diagonal]
    congr 1
    ext k
    rw [Complex.conj_ofReal, ← Complex.ofReal_mul, ← Complex.ofReal_mul, mul_right_comm,
      Real.mul_self_sqrt (hσ k).le, div_mul_cancel₀ _ (hne _)]
end GlobalTheory.Inertia
