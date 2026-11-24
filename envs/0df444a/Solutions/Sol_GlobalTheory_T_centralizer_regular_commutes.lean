-- Prove2me | solution 1 for GlobalTheory.T.centralizer_regular_commutes
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:04:21.324588+00:00
-- url     : https://prove2.me/submissions/f01b8adb-43d6-4727-813e-d7f58b8f59a8

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CentralizerRegularCommutes
import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CentralizerRegularCommutesStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_MatrixComm_commute_of_dominated_diag


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
theorem _root_.solution : ∀ {n : ℕ} (U H A Y : Matrix (Fin n) (Fin n) ℂ), U ∈ Matrix.unitaryGroup (Fin n) ℂ → (Uᴴ * H * U).IsDiag → (Uᴴ * A * U).IsDiag → (∀ i j, (Uᴴ * H * U) i i = (Uᴴ * H * U) j j → (Uᴴ * A * U) i i = (Uᴴ * A * U) j j) → H * Y = Y * H → Y * A = A * Y := by
  first | exact @GlobalTheory.CompanionTheory.MatrixComm.commute_of_dominated_diag | exact GlobalTheory.CompanionTheory.MatrixComm.commute_of_dominated_diag | (intros; apply GlobalTheory.CompanionTheory.MatrixComm.commute_of_dominated_diag <;> assumption)
end _root_.GlobalTheory.T
