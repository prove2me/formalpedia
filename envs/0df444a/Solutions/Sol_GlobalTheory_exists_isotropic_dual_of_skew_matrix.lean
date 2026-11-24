-- Prove2me | solution 1 for GlobalTheory.exists_isotropic_dual_of_skew_matrix
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:54:23.953967+00:00
-- url     : https://prove2.me/submissions/c5eb95b1-2e7b-4c89-a1a7-dc5aba927322

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsIsotropicDualOfSkewMatrix
import Theorems.Thm_GlobalTheory_exists_isotropic_dual_of_skew

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
theorem _root_.solution (r g : ℕ) (Mq : Matrix (Fin r) (Fin r) ℚ)
    (ε ψ : Fin g → Fin r → ℚ) (hM : Mqᵀ = -Mq) (hε : ∀ i j, ε i ⬝ᵥ Mq *ᵥ ε j = 0)
    (hψ : ∀ i j, ψ j ⬝ᵥ Mq *ᵥ ε i = if i = j then 1 else 0) :
    ∃ φ : Fin g → Fin r → ℚ, (∀ i j, φ i ⬝ᵥ Mq *ᵥ φ j = 0) ∧
      (∀ i j, φ j ⬝ᵥ Mq *ᵥ ε i = if i = j then 1 else 0) ∧
      ∀ j, φ j - ψ j ∈ Submodule.span ℚ (Set.range ε) := by
  obtain ⟨φ, h₁, h₂, h₃⟩ := exists_isotropic_dual_of_skew (Matrix.toLinearMap₂' ℚ Mq) ε ψ
    (fun x y => by
      simp only [Matrix.toLinearMap₂'_apply']
      rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hM, Matrix.neg_mulVec,
        neg_dotProduct, dotProduct_comm])
    (fun i j => by simpa only [Matrix.toLinearMap₂'_apply'] using hε i j)
    (fun i j => by simpa only [Matrix.toLinearMap₂'_apply'] using hψ i j)
  exact ⟨φ, fun i j => by simpa only [Matrix.toLinearMap₂'_apply'] using h₁ i j,
    fun i j => by simpa only [Matrix.toLinearMap₂'_apply'] using h₂ i j, h₃⟩
end GlobalTheory
