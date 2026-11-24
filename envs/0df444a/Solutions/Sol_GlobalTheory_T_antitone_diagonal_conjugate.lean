-- Prove2me | solution 1 for GlobalTheory.T.antitone_diagonal_conjugate
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:02:44.802099+00:00
-- url     : https://prove2.me/submissions/1266859f-c82d-4f6e-bd02-ad04df0cd7db

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_AntitoneDiagonalConjugate
import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_AntitoneDiagonalConjugateStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_FrameSort_exists_antitone_reorder


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
theorem _root_.solution : ∀ {n : ℕ} (U₀ : Matrix (Fin n) (Fin n) ℂ) (d : Fin n → ℝ), U₀ ∈ Matrix.unitaryGroup (Fin n) ℂ → ∃ U ∈ Matrix.unitaryGroup (Fin n) ℂ, ∃ h : Fin n → ℝ, Antitone h ∧ U * Matrix.diagonal (fun i => (h i : ℂ)) * Uᴴ = U₀ * Matrix.diagonal (fun i => (d i : ℂ)) * U₀ᴴ ∧ ∀ Z : Matrix (Fin n) (Fin n) ℂ, (U₀ᴴ * Z * U₀).IsDiag → (Uᴴ * Z * U).IsDiag := by
  first | exact @GlobalTheory.CompanionTheory.FrameSort.exists_antitone_reorder | exact GlobalTheory.CompanionTheory.FrameSort.exists_antitone_reorder | (intros; apply GlobalTheory.CompanionTheory.FrameSort.exists_antitone_reorder <;> assumption)
end _root_.GlobalTheory.T
