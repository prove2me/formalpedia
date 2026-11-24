-- Prove2me | solution 1 for GlobalTheory.matrix_exp_smul_mul_eq_mul_exp_smul_of_intertwine
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:33:52.123141+00:00
-- url     : https://prove2.me/submissions/bade8229-8e00-43fc-a13b-79e47b887374

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_MatrixExpSmulMulEqMulExpSmulOfIntertwine
import Theorems.Thm_GlobalTheory_matrix_exp_mul_eq_mul_exp_of_intertwine

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
    ∀ (m r : ℕ) (X : Matrix (Fin m) (Fin m) ℂ) (ε : Matrix (Fin m) (Fin r) ℂ)
      (β : Matrix (Fin r) (Fin r) ℂ), X * ε = ε * β →
      ∀ s : ℝ, NormedSpace.exp (s • X) * ε = ε * NormedSpace.exp (s • β) := by
  intro m r X ε β h s
  apply matrix_exp_mul_eq_mul_exp_of_intertwine
  rw [Matrix.smul_mul, Matrix.mul_smul, h]
end GlobalTheory
