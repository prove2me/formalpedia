-- Prove2me | solution 1 for GlobalTheory.gramChange_square
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:10:09.946355+00:00
-- url     : https://prove2.me/submissions/61f771b0-3de3-4baa-b8c5-ab4b0af50e7b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GramDetChangeOfBases
import Theorems.Thm_GlobalTheory_gramChange_gram_eq_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Polynomial
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {K : Type} [Field K] (σ : K →+* K) {n : ℕ} {ι : Type}
    [Fintype ι] [DecidableEq ι] (u v : ι → Fin n → K) (hu : LinearIndependent K u)
    (hv : LinearIndependent K v) (hvu : ∀ i, v i ∈ Submodule.span K (Set.range u)) :
    ∃ d : K, d ≠ 0 ∧ (Matrix.of fun i j => ∑ k, σ (v i k) * v j k).det
      = σ d * d * (Matrix.of fun i j => ∑ k, σ (u i k) * u j k).det := by
  classical
  let b := Module.Basis.span hu
  let P : Matrix ι ι K := Matrix.of fun i a => b.repr ⟨v i, hvu i⟩ a
  have hV : ∀ i, v i = ∑ a, P i a • u a := by
    intro i
    have h := congrArg Subtype.val (b.sum_repr ⟨v i, hvu i⟩)
    rw [Submodule.coe_sum] at h
    simp only [Submodule.coe_smul, b, Module.Basis.span_apply] at h
    exact h.symm
  have hVm : Matrix.of v = P * Matrix.of u := by
    ext i k
    rw [Matrix.mul_apply, Matrix.of_apply,
      show v i k = (∑ a, P i a • u a) k from congrFun (hV i) k]
    simp [Finset.sum_apply]
  refine ⟨P.det, ?_, ?_⟩
  · intro hd
    obtain ⟨w, hw0, hw⟩ := Matrix.exists_vecMul_eq_zero_iff.mpr hd
    have h1 : w ᵥ* Matrix.of v = 0 := by
      rw [hVm, ← Matrix.vecMul_vecMul, hw, Matrix.zero_vecMul]
    have h2 : ∑ i, w i • v i = 0 := by
      rw [← h1]
      ext k
      simp [Matrix.vecMul, dotProduct, Finset.sum_apply]
    exact hw0 (funext fun i => Fintype.linearIndependent_iff.mp hv w h2 i)
  · rw [gramChange_gram_eq_mul, gramChange_gram_eq_mul, hVm, Matrix.map_mul, transpose_mul,
      show P.map σ * (Matrix.of u).map σ * ((Matrix.of u)ᵀ * Pᵀ)
        = P.map σ * ((Matrix.of u).map σ * (Matrix.of u)ᵀ) * Pᵀ by
          simp only [Matrix.mul_assoc],
      det_mul, det_mul, det_transpose, RingHom.map_det,
      RingHom.mapMatrix_apply]
    ring
end GlobalTheory
