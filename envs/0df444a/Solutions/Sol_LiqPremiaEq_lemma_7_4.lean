-- Prove2me | solution 1 for LiqPremiaEq.lemma_7_4
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T20:42:54.568021+00:00
-- url     : https://prove2.me/submissions/947c5a30-3a8d-4a61-9c99-a9f527e53edf

import Mathlib
import Definitions.Def_LiqPremiaEq_IsPSDQuad

open Matrix
open scoped Kronecker

namespace Aux_LPE74

theorem q_transpose {n : Type*} [Fintype n] (M : Matrix n n ℝ) (b : n → ℝ) :
    b ⬝ᵥ (Mᵀ *ᵥ b) = b ⬝ᵥ (M *ᵥ b) := by
  rw [mulVec_transpose, dotProduct_comm, ← dotProduct_mulVec]

theorem psd_of {n : Type*} [Fintype n] (M : Matrix n n ℝ) (hM : Mᵀ = M)
    (h : ∀ b : n → ℝ, 0 ≤ b ⬝ᵥ (M *ᵥ b)) : M.PosSemidef := by
  apply PosSemidef.of_dotProduct_mulVec_nonneg
  · show Mᴴ = M
    rw [conjTranspose_eq_transpose_of_trivial, hM]
  · intro x
    simpa using h x

end Aux_LPE74

open LiqPremiaEq Aux_LPE74 in
theorem solution {ι κ : Type*} [Fintype ι] [Fintype κ] (A : Matrix ι ι ℝ) (B : Matrix κ κ ℝ)
    (hA : IsPSDQuad A) (hB : IsPSDQuad B) (hBsymm : Bᵀ = B) :
    IsPSDQuad (A ⊗ₖ B) := by
  intro b
  set As : Matrix ι ι ℝ := (1 / 2 : ℝ) • (A + Aᵀ) with hAs
  have hAs_symm : Asᵀ = As := by
    rw [hAs, transpose_smul, transpose_add, transpose_transpose, add_comm]
  have hAs_q : ∀ v : ι → ℝ, v ⬝ᵥ (As *ᵥ v) = v ⬝ᵥ (A *ᵥ v) := by
    intro v
    rw [hAs, smul_mulVec, add_mulVec, dotProduct_smul, dotProduct_add, q_transpose, smul_eq_mul]
    ring
  have hAsP : As.PosSemidef := psd_of As hAs_symm (fun v => by rw [hAs_q]; exact hA v)
  have hBP : B.PosSemidef := psd_of B hBsymm hB
  have hK := (hAsP.kronecker hBP).dotProduct_mulVec_nonneg b
  simp only [star_trivial] at hK
  have hT : (A ⊗ₖ B)ᵀ = Aᵀ ⊗ₖ B := by
    ext ⟨i, k⟩ ⟨i', k'⟩
    simp only [transpose_apply, kronecker_apply]
    rw [show B k' k = B k k' by rw [← transpose_apply B k k', hBsymm]]
  have hexp : As ⊗ₖ B = (1 / 2 : ℝ) • (A ⊗ₖ B + Aᵀ ⊗ₖ B) := by
    rw [hAs, smul_kronecker, add_kronecker]
  rw [hexp, smul_mulVec, add_mulVec, dotProduct_smul, dotProduct_add, ← hT, q_transpose,
    smul_eq_mul] at hK
  linarith
