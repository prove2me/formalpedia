-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.IsometricMatrix.exp_mulVec_of_mulVec_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:33:49.885825+00:00
-- url     : https://prove2.me/submissions/5d35517c-f740-4233-95dc-93caddcf9864

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_MatrixExpSmulMulEqMulExpSmulOfIntertwine
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_BlockBasisChangeEntries
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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.IsometricMatrix
namespace GlobalTheory.CompanionTheory.IsometricMatrix
theorem _root_.solution {m : ℕ} (N : Matrix (Fin m) (Fin m) ℂ) (x : Fin m → ℂ)
    (hx : N *ᵥ x = 0) : NormedSpace.exp N *ᵥ x = x := by
  have hC : N * Matrix.replicateCol (Fin 1) x = Matrix.replicateCol (Fin 1) x * (0 : Matrix (Fin 1) (Fin 1) ℂ) := by
    ext i j
    have hi := congrFun hx i
    simp only [Matrix.mulVec, dotProduct, Pi.zero_apply] at hi
    simpa [Matrix.mul_apply, Matrix.replicateCol] using hi
  have hE := matrix_exp_mul_eq_mul_exp_of_intertwine N _ 0 hC
  simp only [NormedSpace.exp_zero, Matrix.mul_one] at hE
  ext i
  have hi := congrFun (congrFun hE i) 0
  simpa [Matrix.mulVec, dotProduct, Matrix.mul_apply, Matrix.replicateCol] using hi
end GlobalTheory.CompanionTheory.IsometricMatrix
