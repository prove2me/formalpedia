-- Prove2me | solution 1 for GeomQM.MomentumMap.lemma_5
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T10:58:07.282527+00:00
-- url     : https://prove2.me/submissions/e0974789-2dc9-46e8-bfdd-951948fe965a

import Mathlib
import Definitions.Def_GeomQM_MomentumMap_Defs

open Matrix

open GeomQM.MomentumMap in
theorem solution (n : ℕ) (A : Matrix (Fin n) (Fin n) ℂ) :
    (∀ ψ : Fin n → ℂ, (quadFnC A ψ).im = 0) ↔ A.IsHermitian := by
  have hhalf_im : (1 / 2 : ℂ).im = 0 := by norm_num
  have hhalf_re : (1 / 2 : ℂ).re = 1 / 2 := by norm_num
  constructor
  · intro h
    rw [← isSymmetric_toEuclideanLin_iff, LinearMap.isSymmetric_iff_inner_map_self_real]
    intro v
    have hv := h (WithLp.ofLp v)
    unfold quadFnC at hv
    rw [Complex.mul_im, hhalf_im, hhalf_re, zero_mul, add_zero] at hv
    have hz : (star (WithLp.ofLp v) ⬝ᵥ A *ᵥ WithLp.ofLp v).im = 0 := by linarith
    have key : inner ℂ (A.toEuclideanLin v) v
        = star (star (WithLp.ofLp v) ⬝ᵥ A *ᵥ WithLp.ofLp v) := by
      simp [PiLp.inner_apply, dotProduct, toEuclideanLin, mul_comm]
    rw [key, Complex.conj_eq_iff_im]
    simp [hz]
  · intro hA ψ
    have h0 : (star ψ ⬝ᵥ A *ᵥ ψ).im = 0 := hA.im_star_dotProduct_mulVec_self ψ
    unfold quadFnC
    rw [Complex.mul_im, h0, hhalf_im]
    ring
