-- Prove2me | solution 1 for GlobalTheory.rat_alternating_orthogonal_orthogonal_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:31:18.101197+00:00
-- url     : https://prove2.me/submissions/157e2314-6db1-46b8-baf7-5a672f709dd4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_RatAlternatingOrthogonalOrthogonalLeAlt

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
theorem _root_.solution :
    ∀ (r : ℕ) (Mq : Matrix (Fin r) (Fin r) ℚ) (V : Submodule ℚ (Fin r → ℚ)), Mqᵀ = -Mq →
      Mq.det ≠ 0 → ∀ x : Fin r → ℚ,
      (∀ y : Fin r → ℚ, (∀ w ∈ V, y ⬝ᵥ Mq *ᵥ w = 0) → x ⬝ᵥ Mq *ᵥ y = 0) → x ∈ V := by
  intro r Mq V hT hdet x hx
  have hB : ∀ u v : Fin r → ℚ, Matrix.toBilin' Mq u v = u ⬝ᵥ Mq *ᵥ v :=
    fun u v => Matrix.toBilin'_apply' Mq u v
  have hanti : ∀ u v : Fin r → ℚ, u ⬝ᵥ Mq *ᵥ v = -(v ⬝ᵥ Mq *ᵥ u) := by
    intro u v
    have h1 : v ⬝ᵥ Mqᵀ *ᵥ u = u ⬝ᵥ Mq *ᵥ v := by
      rw [Matrix.mulVec_transpose, dotProduct_comm, ← Matrix.dotProduct_mulVec]
    rw [← h1, hT, Matrix.neg_mulVec, dotProduct_neg]
  have hrefl : (Matrix.toBilin' Mq).IsRefl := by
    intro u v h
    rw [hB] at h ⊢
    rw [hanti, h, neg_zero]
  have hnd : (Matrix.toBilin' Mq).Nondegenerate :=
    LinearMap.BilinForm.nondegenerate_toBilin'_iff_det_ne_zero.mpr hdet
  rw [← LinearMap.BilinForm.orthogonal_orthogonal hnd hrefl V,
    LinearMap.BilinForm.mem_orthogonal_iff]
  intro y hy
  rw [LinearMap.BilinForm.mem_orthogonal_iff] at hy
  show Matrix.toBilin' Mq y x = 0
  rw [hB, hanti, hx y ?_, neg_zero]
  intro w hw
  have h := hy w hw
  change Matrix.toBilin' Mq w y = 0 at h
  rw [hB, hanti] at h
  exact neg_eq_zero.mp h
end GlobalTheory
