-- Prove2me | solution 1 for GlobalTheory.T.commuting_hermitian_simultaneous_diag
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:05:38.870589+00:00
-- url     : https://prove2.me/submissions/016a9a12-a805-472f-a79c-d478d75c1137

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CommutingHermitianSimultaneousDiag
import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CommutingHermitianSimultaneousDiagStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_SimDiag_exists_unitary_isDiag


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
theorem _root_.solution : ∀ {n : ℕ} (S : Set (Matrix (Fin n) (Fin n) ℂ)), (∀ A ∈ S, Aᴴ = A) → (∀ A ∈ S, ∀ B ∈ S, A * B = B * A) → ∃ U ∈ Matrix.unitaryGroup (Fin n) ℂ, ∀ A ∈ S, (Uᴴ * A * U).IsDiag := by
  first | exact @GlobalTheory.CompanionTheory.SimDiag.exists_unitary_isDiag | exact GlobalTheory.CompanionTheory.SimDiag.exists_unitary_isDiag | (intros; apply GlobalTheory.CompanionTheory.SimDiag.exists_unitary_isDiag <;> assumption)
end _root_.GlobalTheory.T
