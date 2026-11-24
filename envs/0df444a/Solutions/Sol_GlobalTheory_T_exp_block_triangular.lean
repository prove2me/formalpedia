-- Prove2me | solution 1 for GlobalTheory.T.exp_block_triangular
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:08:03.334537+00:00
-- url     : https://prove2.me/submissions/1ced38e1-f883-4be0-8fe3-5c2ef95c444b

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExpBlockTriangular
import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExpBlockTriangularStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_Unitary_ExpUpper_blockTriangular_conj_exp


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Topology Filter
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ {n : ℕ} (U Y : Matrix (Fin n) (Fin n) ℂ), U ∈ Matrix.unitaryGroup (Fin n) ℂ → (Uᴴ * Y * U).BlockTriangular id → (Uᴴ * NormedSpace.exp Y * U).BlockTriangular id := by
  first | exact @GlobalTheory.CompanionTheory.Unitary.ExpUpper.blockTriangular_conj_exp | exact GlobalTheory.CompanionTheory.Unitary.ExpUpper.blockTriangular_conj_exp | (intros; apply GlobalTheory.CompanionTheory.Unitary.ExpUpper.blockTriangular_conj_exp <;> assumption)
end _root_.GlobalTheory.T
