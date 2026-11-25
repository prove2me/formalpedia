-- Prove2me | solution 1 for GlobalTheory.T.exists_GL_last_basis_vecMul_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T18:17:46.718993+00:00
-- url     : https://prove2.me/submissions/59a35ff0-af8a-4d32-95a4-fdc2b236d484

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsGLLastBasisVecMulEq
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsGLLastBasisVecMulEqStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_RowSect_exists_GL_last_row


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open scoped Topology
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (k : Type) [Field k] (m : ℕ) (ξ : Fin (m + 1) → k), ξ ≠ 0 → ∃ h : GL (Fin (m + 1)) k, (Pi.single (Fin.last m) 1 : Fin (m + 1) → k) ᵥ* (h : Matrix (Fin (m + 1)) (Fin (m + 1)) k) = ξ := by
  first | exact @GlobalTheory.CompanionTheory.RowSect.exists_GL_last_row | exact GlobalTheory.CompanionTheory.RowSect.exists_GL_last_row | (intros; apply GlobalTheory.CompanionTheory.RowSect.exists_GL_last_row <;> assumption)
end _root_.GlobalTheory.T
