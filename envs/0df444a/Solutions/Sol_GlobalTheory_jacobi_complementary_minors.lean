-- Prove2me | solution 1 for GlobalTheory.jacobi_complementary_minors
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T02:43:48.799157+00:00
-- url     : https://prove2.me/submissions/115670d6-8af6-4ced-8d14-8e67c0429cf2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PluckerMinorsProportional
import Theorems.Thm_P2M_GlobalTheory_det_mul_det_toBlocks___of_mul_eq_one_6c4eaa1f2b3e

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {K : Type} [Field K] {p q : ℕ}
    (α : Matrix (Fin p) (Fin p ⊕ Fin q) K) (β : Matrix (Fin q) (Fin p ⊕ Fin q) K)
    (hαβ : α * β.transpose = 0)
    (h₀ : ∃ π₀ : Equiv.Perm (Fin p ⊕ Fin q), (α.submatrix id (π₀ ∘ Sum.inl)).det ≠ 0)
    (h₁ : ∃ π₁ : Equiv.Perm (Fin p ⊕ Fin q), (β.submatrix id (π₁ ∘ Sum.inr)).det ≠ 0) :
    ∃ lam : K, ∀ π : Equiv.Perm (Fin p ⊕ Fin q),
      ((Equiv.Perm.sign π : ℤ) : K) * (α.submatrix id (π ∘ Sum.inl)).det =
        lam * (β.submatrix id (π ∘ Sum.inr)).det := by
  obtain ⟨π₀, hπ₀⟩ := h₀
  obtain ⟨π₁, hπ₁⟩ := h₁

  set M : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) K :=
    fromRows α ((1 : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) K).submatrix (π₀ ∘ Sum.inr) id) with hMdef
  have hMπ₀ : (M.submatrix id π₀).det = (α.submatrix id (π₀ ∘ Sum.inl)).det := by
    rw [← fromBlocks_toBlocks (M.submatrix id π₀)]
    have h21 : (M.submatrix id π₀).toBlocks₂₁ = 0 := by
      ext i j
      simp [M, toBlocks₂₁, one_apply]
    have h22 : (M.submatrix id π₀).toBlocks₂₂ = 1 := by
      ext i j
      simp [M, toBlocks₂₂, one_apply]
    rw [h21, h22, det_fromBlocks_zero₂₁]
    simp only [det_one, mul_one]
    rfl
  have hMdet : M.det ≠ 0 := by
    intro h
    apply hπ₀
    rw [← hMπ₀, det_permute', h, mul_zero]
  have hMu : IsUnit M.det := isUnit_iff_ne_zero.mpr hMdet
  set N := M⁻¹ with hN
  set g : Matrix (Fin q) (Fin q) K := β.submatrix id (π₀ ∘ Sum.inr) with hg

  have hD : ∀ π : Equiv.Perm (Fin p ⊕ Fin q),
      ((Equiv.Perm.sign π : ℤ) : K) * M.det * (N.submatrix (π ∘ Sum.inr) Sum.inr).det =
        (α.submatrix id (π ∘ Sum.inl)).det := by
    intro π
    have hXY : M.submatrix id π * N.submatrix π id = 1 := by
      rw [submatrix_mul_equiv, hN, mul_nonsing_inv _ hMu, submatrix_id_id]
    have := det_mul_det_toBlocks₂₂_of_mul_eq_one _ _ hXY
    rw [det_permute'] at this
    convert this using 2 <;> rfl
  have hβ : ∀ π : Equiv.Perm (Fin p ⊕ Fin q),
      β.submatrix id (π ∘ Sum.inr) = g * (N.submatrix (π ∘ Sum.inr) Sum.inr).transpose := by
    intro π
    have hT : β.transpose = N * (M * β.transpose) := by
      rw [← Matrix.mul_assoc, hN, nonsing_inv_mul _ hMu, Matrix.one_mul]
    ext k m
    have := congrFun (congrFun hT (π (Sum.inr m))) k
    rw [transpose_apply] at this
    simp only [submatrix_apply, id, Function.comp_apply, mul_apply, transpose_apply]
    rw [this, mul_apply, Fintype.sum_sum_type]
    have h0 : ∀ l, (M * β.transpose) (Sum.inl l) k = 0 := by
      intro l
      have := congrFun (congrFun hαβ l) k
      simpa [M, mul_apply] using this
    have h1 : ∀ k', (M * β.transpose) (Sum.inr k') k = g k k' := by
      intro k'
      simp [M, g, mul_apply, one_apply]
    simp only [h0, h1, mul_zero, Finset.sum_const_zero, zero_add]
    refine Finset.sum_congr rfl fun k' _ => ?_
    rw [mul_comm]
  have hdetβ : ∀ π : Equiv.Perm (Fin p ⊕ Fin q),
      (β.submatrix id (π ∘ Sum.inr)).det = g.det * (N.submatrix (π ∘ Sum.inr) Sum.inr).det := by
    intro π
    rw [hβ π, det_mul, det_transpose]
  have hg0 : g.det ≠ 0 := by
    intro h
    apply hπ₁
    rw [hdetβ, h, zero_mul]
  refine ⟨M.det / g.det, fun π => ?_⟩
  have hs : ((Equiv.Perm.sign π : ℤ) : K) * ((Equiv.Perm.sign π : ℤ) : K) = 1 := by
    rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self]
    simp
  have hc : M.det / g.det * (g.det * (N.submatrix (π ∘ Sum.inr) Sum.inr).det) =
      M.det * (N.submatrix (π ∘ Sum.inr) Sum.inr).det := by
    field_simp
  rw [← hD π, hdetβ π, hc]
  linear_combination (M.det * (N.submatrix (π ∘ Sum.inr) Sum.inr).det) * hs
end GlobalTheory
