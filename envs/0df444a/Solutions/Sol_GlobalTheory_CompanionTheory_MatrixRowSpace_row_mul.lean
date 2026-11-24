-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.MatrixRowSpace.row_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T12:52:43.958815+00:00
-- url     : https://prove2.me/submissions/dba122c4-6488-4403-b228-bbd69b2dd2b5

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_RangeVecMulLinearEq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.MatrixRowSpace
variable {K : Type} [Field K]
namespace GlobalTheory.CompanionTheory.MatrixRowSpace
theorem _root_.solution {m n r : ℕ} (x : Matrix (Fin m) (Fin r) K) (c : Matrix (Fin r) (Fin n) K)
    (i : Fin m) : (x * c) i = c.vecMulLinear (x i) := by
  ext j
  simp [Matrix.mul_apply, Matrix.vecMul, dotProduct]
end GlobalTheory.CompanionTheory.MatrixRowSpace
