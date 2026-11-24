-- Prove2me | solution 1 for GlobalTheory.T.exists_GL_vecMul_eq_last_basis
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:06:43.819461+00:00
-- url     : https://prove2.me/submissions/b962c8a6-b6b5-44dc-aa39-3b5be8399b47

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsGLVecMulEqLastBasis
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsGLVecMulEqLastBasisStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_Matrixlemmas_exists_GL_vecMul_eq_single_last


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ {k : Type} [Field k] (n : ℕ) (ξ : Fin (n + 1) → k), ξ ≠ 0 → ∃ g : GL (Fin (n + 1)) k, Matrix.vecMul ξ (g : Matrix (Fin (n + 1)) (Fin (n + 1)) k) = Pi.single (Fin.last n) 1 := by
  first | exact @GlobalTheory.CompanionTheory.Matrixlemmas.exists_GL_vecMul_eq_single_last | exact GlobalTheory.CompanionTheory.Matrixlemmas.exists_GL_vecMul_eq_single_last | (intros; apply GlobalTheory.CompanionTheory.Matrixlemmas.exists_GL_vecMul_eq_single_last <;> assumption)
end _root_.GlobalTheory.T
