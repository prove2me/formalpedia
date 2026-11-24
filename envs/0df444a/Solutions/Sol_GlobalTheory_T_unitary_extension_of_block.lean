-- Prove2me | solution 1 for GlobalTheory.T.unitary_extension_of_block
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:25:59.854253+00:00
-- url     : https://prove2.me/submissions/d71cde18-09a8-4ccd-917b-3c637805ab59

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_UnitaryExtensionOfBlock
import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_UnitaryExtensionOfBlockStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_WittFrame_unitary_adapted_triangularises


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
theorem _root_.solution : ∀ {n D m : ℕ} (J : Matrix (Fin n) (Fin n) ℂ) (J' : Matrix (Fin m) (Fin m) ℂ) (C : Matrix (Fin n) (Fin D) ℂ) (R : Matrix (Fin n) (Fin m) ℂ), J * J = 1 → Jᴴ = J → Cᴴ * C = 1 → Cᴴ * J * C = 0 → Rᴴ * R = 1 → J * R = R * J' → Cᴴ * R = 0 → C * Cᴴ + J * C * Cᴴ * J + R * Rᴴ = 1 → ∀ U₀ ∈ Matrix.unitaryGroup (Fin m) ℂ, ∃ U ∈ Matrix.unitaryGroup (Fin n) ℂ, ∀ (s : Matrix (Fin n) (Fin n) ℂ) (b b' : Matrix (Fin D) (Fin D) ℂ) (t : Matrix (Fin m) (Fin m) ℂ), s * C = C * b → s * (R * U₀) = (R * U₀) * t → s * (J * C) = (J * C) * b' → b.BlockTriangular id → t.BlockTriangular id → (∀ x y, x < y → b' x y = 0) → (Uᴴ * s * U).BlockTriangular id := by
  first | exact @GlobalTheory.CompanionTheory.WittFrame.unitary_adapted_triangularises | exact GlobalTheory.CompanionTheory.WittFrame.unitary_adapted_triangularises | (intros; apply GlobalTheory.CompanionTheory.WittFrame.unitary_adapted_triangularises <;> assumption)
end _root_.GlobalTheory.T
