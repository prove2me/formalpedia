-- Prove2me | solution 1 for GlobalTheory.WittTrace.exists_isometry_mul_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T04:36:08.00314+00:00
-- url     : https://prove2.me/submissions/07a8772b-8b91-44a0-bc7b-7828e7550c5d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_ExistsGlIsometryCompEqOfNondegenerate
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsIsometryOfLinearIndependent
import Theorems.Thm_GlobalTheory_WittTrace_exists_isometry_of_linearIndependent
import Theorems.Thm_GlobalTheory_WittTrace_linearIndependent_col_of_rank
import Theorems.Thm_GlobalTheory_HermWitt_exists_gl_isometry_mul_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace GlobalTheory.WittTrace
open Module Matrix GlobalTheory.HermDiag GlobalTheory.HermWitt
section Abstract
variable {E : Type*} [Field E] {c : E →+* E} {V : Type*} [AddCommGroup V] [Module E V]
end Abstract
private lemma exists_form_lemma {K : Type} [Field K] [StarRing K] {n : ℕ}
    (J : Matrix (Fin n) (Fin n) K) :
    ∃ B : (Fin n → K) →ₗ[K] (Fin n → K) →ₛₗ[starRingEnd K] K,
      ∀ z w, B z w = star w ⬝ᵥ J *ᵥ z :=
  ⟨LinearMap.mk₂'ₛₗ (RingHom.id K) (starRingEnd K) (fun z w => star w ⬝ᵥ J *ᵥ z)
    (fun _ _ _ => by simp [Matrix.mulVec_add, dotProduct_add])
    (fun _ _ _ => by simp [Matrix.mulVec_smul, dotProduct_smul])
    (fun _ _ _ => by simp [star_add, add_dotProduct])
    (fun _ _ _ => by simp [star_smul, smul_dotProduct, starRingEnd_apply]), fun _ _ => rfl⟩
private lemma entry_lemma_2 {K : Type} [Field K] [StarRing K] {n : ℕ} {m m' : Type*} [Fintype m]
    [Fintype m'] (J : Matrix (Fin n) (Fin n) K) (P : Matrix (Fin n) m K) (Q : Matrix (Fin n) m' K)
    (i : m) (j : m') : (Pᴴ * J * Q) i j = star (P.col i) ⬝ᵥ J *ᵥ Q.col j := by
  rw [Matrix.mul_assoc]
  simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, Matrix.col]
private lemma transpose_mul_transpose_mul_map_star_eq {K : Type} [Field K] [StarRing K] {n : ℕ} {m : Type*}
    [Fintype m] (J : Matrix (Fin n) (Fin n) K) (P : Matrix (Fin n) m K) :
    Pᵀ * Jᵀ * P.map star = (Pᴴ * J * P)ᵀ := by
  rw [transpose_mul, transpose_mul, conjTranspose_transpose, Matrix.mul_assoc]
private lemma eq_zero_of_mulVec_eq_zero_of_linearIndependent_col {K : Type} [Field K] {n a : ℕ} {X : Matrix (Fin n) (Fin a) K}
    (hX : LinearIndependent K X.col) (v : Fin a → K) (h : X *ᵥ v = 0) : v = 0 := by
  have e : X *ᵥ v = ∑ j, v j • X.col j := by
    ext i
    simp [Matrix.mulVec, dotProduct, Matrix.col, Finset.sum_apply, mul_comm]
  rw [e] at h
  funext j
  exact Fintype.linearIndependent_iff.1 hX v h j
end GlobalTheory.WittTrace
end

set_option autoImplicit false
open GlobalTheory GlobalTheory.WittTrace
open Module Matrix GlobalTheory.HermDiag GlobalTheory.HermWitt
namespace GlobalTheory.WittTrace
theorem _root_.solution (K : Type) [Field K] [StarRing K] (θ : K) (hθ : θ + star θ = 1)
    (n a : ℕ) (J : Matrix (Fin n) (Fin n) K) (X Y : Matrix (Fin n) (Fin a) K) (hJ : Jᴴ = J)
    (hdet : IsUnit J.det) (hX : X.rank = a) (hY : Y.rank = a)
    (hXY : Xᴴ * J * X = Yᴴ * J * Y) :
    ∃ g : Matrix (Fin n) (Fin n) K, gᴴ * J * g = J ∧ g * X = Y := by
  have hXl := linearIndependent_col_of_rank hX
  have hYl := linearIndependent_col_of_rank hY
  by_cases h2 : (2 : K) = 0
  · obtain ⟨B, hBd⟩ := exists_form_lemma J
    have hc : ∀ t : K, starRingEnd K (starRingEnd K t) = t := fun t => by simp
    have hB : ∀ x y, starRingEnd K (B x y) = B y x := by
      intro x y
      rw [hBd, hBd, starRingEnd_apply, ← star_dotProduct_star, star_star, star_mulVec,
        ← dotProduct_mulVec, hJ]
    have hrep : ∀ ψ : (Fin n → K) →ₗ[K] K, ∃ w, ∀ z, B z w = ψ z := by
      intro ψ
      obtain ⟨r, hr⟩ : ∃ r : Fin n → K, ∀ z, ψ z = r ⬝ᵥ z :=
        ⟨fun k => ψ (fun j => if k = j then 1 else 0), fun z => by
          rw [LinearMap.pi_apply_eq_sum_univ ψ z]; simp [dotProduct, mul_comm]⟩
      refine ⟨star ((Jᵀ)⁻¹ *ᵥ r), fun z => ?_⟩
      have hdT : IsUnit Jᵀ.det := by rwa [det_transpose]
      rw [hBd, hr, star_star, dotProduct_mulVec, ← mulVec_transpose, mulVec_mulVec,
        mul_nonsing_inv _ hdT, one_mulVec]
    have hs : ∀ b : K, starRingEnd K b = b → ∃ s : K, s ≠ 0 ∧ s + starRingEnd K s = b := by
      intro b hb
      by_cases hb0 : b = 0
      · refine ⟨1, one_ne_zero, ?_⟩
        rw [map_one, hb0, one_add_one_eq_two, h2]
      · have hθ0 : θ ≠ 0 := by
          rintro rfl
          simp at hθ
        refine ⟨θ * b, mul_ne_zero hθ0 hb0, ?_⟩
        rw [map_mul, hb, starRingEnd_apply]
        linear_combination b * hθ
    have hxy : ∀ i j, B (X.col i) (X.col j) = B (Y.col i) (Y.col j) := by
      intro i j
      rw [hBd, hBd, ← entry_lemma_2, ← entry_lemma_2, hXY]
    obtain ⟨γ, hγ, hγX⟩ := exists_isometry_of_linearIndependent hs hc hB hrep hXl hYl hxy
    refine ⟨LinearMap.toMatrix' (γ : (Fin n → K) →ₗ[K] (Fin n → K)), ?_, ?_⟩
    · set g := LinearMap.toMatrix' (γ : (Fin n → K) →ₗ[K] (Fin n → K))
      have hcol : ∀ j, g.col j = γ (Pi.single j 1) := fun j => by
        rw [← mulVec_single_one, LinearMap.toMatrix'_mulVec]; rfl
      ext i j
      rw [entry_lemma_2, hcol, hcol, ← hBd, hγ, hBd]
      simp
    · ext i j
      have e : (LinearMap.toMatrix' (γ : (Fin n → K) →ₗ[K] (Fin n → K)) * X).col j =
          LinearMap.toMatrix' (γ : (Fin n → K) →ₗ[K] (Fin n → K)) *ᵥ X.col j := by
        ext k
        simp [Matrix.col, Matrix.mul_apply, Matrix.mulVec, dotProduct]
      rw [LinearMap.toMatrix'_mulVec] at e
      have := congrFun e i
      simp only [LinearEquiv.coe_coe, hγX] at this
      exact this
  · have hc : ∀ t : K, starRingEnd K (starRingEnd K t) = t := fun t => by simp
    have hG : ∀ a b, starRingEnd K (Jᵀ a b) = Jᵀ b a := by
      intro a b
      rw [transpose_apply, transpose_apply, starRingEnd_apply, ← conjTranspose_apply, hJ]
    have hdT : Jᵀ.det ≠ 0 := by rw [det_transpose]; exact hdet.ne_zero
    have h0 : ∀ v, X *ᵥ v = 0 ↔ Y *ᵥ v = 0 := by
      intro v
      constructor
      · intro h; rw [eq_zero_of_mulVec_eq_zero_of_linearIndependent_col hXl v h, mulVec_zero]
      · intro h; rw [eq_zero_of_mulVec_eq_zero_of_linearIndependent_col hYl v h, mulVec_zero]
    have hXY' : Yᵀ * Jᵀ * Y.map (starRingEnd K) = Xᵀ * Jᵀ * X.map (starRingEnd K) := by
      have e := transpose_mul_transpose_mul_map_star_eq J X
      have e' := transpose_mul_transpose_mul_map_star_eq J Y
      change Yᵀ * Jᵀ * Y.map star = Xᵀ * Jᵀ * X.map star
      rw [e, e', hXY]
    obtain ⟨γ, hγ, hγX⟩ := exists_gl_isometry_mul_eq h2 hc hG hdT h0 hXY'
    refine ⟨γ, ?_, hγX⟩
    have e := transpose_mul_transpose_mul_map_star_eq J (γ : Matrix (Fin n) (Fin n) K)
    change (γ : Matrix (Fin n) (Fin n) K)ᵀ * Jᵀ * (γ : Matrix (Fin n) (Fin n) K).map star = Jᵀ at hγ
    rw [hγ] at e
    exact (transpose_inj.1 e).symm
end GlobalTheory.WittTrace
