-- Prove2me | solution 1 for GlobalTheory.T.unitary_frames_preserve_norm_sq_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:26:03.344949+00:00
-- url     : https://prove2.me/submissions/5926421b-1139-4f7f-af25-f6f07b158493

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_UnitaryFramesPreserveNormSqSum
import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_UnitaryFramesPreserveNormSqSumStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_UnitFrame_normSq_eq_of_unit_frames


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
theorem _root_.solution : ∀ (m : ℕ), 1 ≤ m → ∀ (J : Matrix (Fin m) (Fin m) ℂ) (fr fr' : GL (Fin m) ℂ) (ζ ζ' : ℂ) (s s' : ℤˣ), (ζ = 1 ∨ ζ = Complex.I) → (ζ' = 1 ∨ ζ' = Complex.I) → ζ • (fr.1ᵀ * J * fr.1.map star) = ((s : ℤ) : ℂ) • 1 → ζ' • (fr'.1ᵀ * J * fr'.1.map star) = ((s' : ℤ) : ℂ) • 1 → ∀ v : Fin m → ℂ, ∑ a, ‖((fr⁻¹).1 *ᵥ v) a‖ ^ 2 = ∑ a, ‖((fr'⁻¹).1 *ᵥ v) a‖ ^ 2 := by
  first | exact @GlobalTheory.CompanionTheory.UnitFrame.normSq_eq_of_unit_frames | exact GlobalTheory.CompanionTheory.UnitFrame.normSq_eq_of_unit_frames | (intros; apply GlobalTheory.CompanionTheory.UnitFrame.normSq_eq_of_unit_frames <;> assumption)
end _root_.GlobalTheory.T
