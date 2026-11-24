-- Prove2me | solution 1 for GlobalTheory.T.unitary_lift_commuting_involution
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:26:08.633258+00:00
-- url     : https://prove2.me/submissions/c7b9935c-1eca-4365-95b6-f09300434021

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_UnitaryLiftCommutingInvolution
import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_UnitaryLiftCommutingInvolutionStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_UnitaryAssembly_exists_unitary_assemble


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
theorem _root_.solution : ∀ {n D m : ℕ} (J : Matrix (Fin n) (Fin n) ℂ) (J' : Matrix (Fin m) (Fin m) ℂ) (C : Matrix (Fin n) (Fin D) ℂ) (R : Matrix (Fin n) (Fin m) ℂ), J * J = 1 → Jᴴ = J → Cᴴ * C = 1 → Cᴴ * J * C = 0 → Rᴴ * R = 1 → J * R = R * J' → Cᴴ * R = 0 → C * Cᴴ + J * C * Cᴴ * J + R * Rᴴ = 1 → ∀ k₀ ∈ Matrix.unitaryGroup (Fin D) ℂ, ∀ kR ∈ Matrix.unitaryGroup (Fin m) ℂ, kR * J' = J' * kR → ∃ k ∈ Matrix.unitaryGroup (Fin n) ℂ, k * J = J * k ∧ k * C = C * k₀ ∧ kᴴ * C = C * k₀ᴴ ∧ kᴴ * R = R * kRᴴ ∧ kᴴ * (J * C) = (J * C) * k₀ᴴ := by
  first | exact @GlobalTheory.CompanionTheory.UnitaryAssembly.exists_unitary_assemble | exact GlobalTheory.CompanionTheory.UnitaryAssembly.exists_unitary_assemble | (intros; apply GlobalTheory.CompanionTheory.UnitaryAssembly.exists_unitary_assemble <;> assumption)
end _root_.GlobalTheory.T
