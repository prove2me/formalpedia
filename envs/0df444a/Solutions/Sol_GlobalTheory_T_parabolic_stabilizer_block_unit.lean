-- Prove2me | solution 1 for GlobalTheory.T.parabolic_stabilizer_block_unit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:21:11.742698+00:00
-- url     : https://prove2.me/submissions/f20905db-a44f-4171-924f-e3adee29acd5

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_LieAlgebraStarClosedBracket
import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_LieAlgebraStarClosedBracketStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_UnitaryBlock_block_diagonal_of_keeps_frame


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
theorem _root_.solution : ∀ {n D m : ℕ} (J : Matrix (Fin n) (Fin n) ℂ) (J' : Matrix (Fin m) (Fin m) ℂ) (C : Matrix (Fin n) (Fin D) ℂ) (R : Matrix (Fin n) (Fin m) ℂ), J * J = 1 → Jᴴ = J → Cᴴ * C = 1 → Rᴴ * R = 1 → J * R = R * J' → Cᴴ * R = 0 → C * Cᴴ + J * C * Cᴴ * J + R * Rᴴ = 1 → ∀ (g : Matrix (Fin n) (Fin n) ℂ) (h : Matrix (Fin D) (Fin D) ℂ), gᴴ * J * g = J → g * C = C * h → gᴴ * C = C * hᴴ → IsUnit h ∧ g * (J * C) = (J * C) * (hᴴ)⁻¹ ∧ g * R = R * (Rᴴ * g * R) ∧ (Rᴴ * g * R)ᴴ * J' * (Rᴴ * g * R) = J' := by
  first | exact @GlobalTheory.CompanionTheory.UnitaryBlock.block_diagonal_of_keeps_frame | exact GlobalTheory.CompanionTheory.UnitaryBlock.block_diagonal_of_keeps_frame | (intros; apply GlobalTheory.CompanionTheory.UnitaryBlock.block_diagonal_of_keeps_frame <;> assumption)
end _root_.GlobalTheory.T
