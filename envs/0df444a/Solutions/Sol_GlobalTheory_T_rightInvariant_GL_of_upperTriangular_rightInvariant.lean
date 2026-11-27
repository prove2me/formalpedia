-- Prove2me | solution 1 for GlobalTheory.T.rightInvariant_GL_of_upperTriangular_rightInvariant
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T04:33:29.675663+00:00
-- url     : https://prove2.me/submissions/af0db680-d2fa-44af-9f09-94f7d058f334

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RightInvariantGLOfUpperTriangularRightInvariant
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RightInvariantGLOfUpperTriangularRightInvariantStatement
import Theorems.Thm_GlobalTheory_rightInv_of_upperTriangular_rightInv


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ {k : Type} [Field k] [Infinite k] {m : ℕ} (ψ Φ : Matrix (Fin m) (Fin m) k → k) (r : k → k), (∀ A₀ D : Matrix (Fin m) (Fin m) k, ∃ p : Polynomial k, ∀ x : k, Φ (A₀ + x • D) = p.eval x) → (∀ A : Matrix (Fin m) (Fin m) k, A.det ≠ 0 → ψ A = r A.det * Φ A) → (∀ A T : Matrix (Fin m) (Fin m) k, A.det ≠ 0 → T.det ≠ 0 → T.BlockTriangular id → ψ (A * T) = ψ A) → ∀ A B : Matrix (Fin m) (Fin m) k, A.det ≠ 0 → B.det ≠ 0 → ψ (A * B) = ψ A := by
  first | exact @GlobalTheory.rightInv_of_upperTriangular_rightInv | exact GlobalTheory.rightInv_of_upperTriangular_rightInv | (intros; apply GlobalTheory.rightInv_of_upperTriangular_rightInv <;> assumption)
end _root_.GlobalTheory.T
