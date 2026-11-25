-- Prove2me | solution 1 for GlobalTheory.rightInv_of_upperTriangular_rightInv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:56:53.063441+00:00
-- url     : https://prove2.me/submissions/a28a2d70-e69b-49a9-9b68-62f6d2624773

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RightInvariantGLOfUpperTriangularRightInvariant
import Theorems.Thm_GlobalTheory_transvection_isUpper
import Theorems.Thm_GlobalTheory_rightInv_lower_transvection

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
variable {k : Type} [Field k] [Infinite k] {m : ℕ}
namespace GlobalTheory
theorem _root_.solution :
    ∀ {k : Type} [Field k] [Infinite k] {m : ℕ} (ψ Φ : Matrix (Fin m) (Fin m) k → k) (r : k → k),
      (∀ A₀ D : Matrix (Fin m) (Fin m) k, ∃ p : Polynomial k, ∀ x : k, Φ (A₀ + x • D) = p.eval x) →
      (∀ A : Matrix (Fin m) (Fin m) k, A.det ≠ 0 → ψ A = r A.det * Φ A) →
      (∀ A T : Matrix (Fin m) (Fin m) k, A.det ≠ 0 → T.det ≠ 0 → T.BlockTriangular id →
        ψ (A * T) = ψ A) →
      ∀ A B : Matrix (Fin m) (Fin m) k, A.det ≠ 0 → B.det ≠ 0 → ψ (A * B) = ψ A := by
  intro k _ _ m ψ Φ r hΦ hψ hT A B hA hB
  refine diagonal_transvection_induction_of_det_ne_zero
    (fun B => ∀ A : Matrix (Fin m) (Fin m) k, A.det ≠ 0 → ψ (A * B) = ψ A) B hB ?_ ?_ ?_ A hA
  · intro D hD A hA
    exact hT A _ hA hD (blockTriangular_diagonal D)
  · intro t A hA
    rcases lt_or_gt_of_ne t.hij with h | h
    · have hdet : (t.toMatrix).det ≠ 0 := by
        rw [TransvectionStruct.toMatrix, det_transvection_of_ne _ _ t.hij]; exact one_ne_zero
      exact hT A _ hA hdet (transvection_isUpper h t.c)
    · exact rightInv_lower_transvection ψ Φ r hΦ hψ hT A hA h t.c
  · intro B₁ B₂ h₁ h₂ P₁ P₂ A hA
    rw [← Matrix.mul_assoc, P₂ _ (by rw [det_mul]; exact mul_ne_zero hA h₁), P₁ _ hA]
end GlobalTheory
