-- Prove2me | solution 1 for GlobalTheory.T.finiteDimensional_of_isCompactOperator_coercive
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T18:21:02.666319+00:00
-- url     : https://prove2.me/submissions/6c9b3a35-08d1-46bd-a604-fb520516a4f2

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_FiniteDimensionalOfCompactCoercive
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_FiniteDimensionalOfCompactCoerciveStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_Glob_finiteDimensional_of_compact_coercive


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped InnerProductSpace
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (A : H →L[ℂ] H), IsCompactOperator A → ∀ (S : Submodule ℂ H) (c : ℝ), 0 < c → (∀ u ∈ S, c * ‖u‖ ^ 2 ≤ (⟪u, A u⟫_ℂ).re) → FiniteDimensional ℂ S := by
  first | exact @GlobalTheory.CompanionTheory.Glob.finiteDimensional_of_compact_coercive | exact GlobalTheory.CompanionTheory.Glob.finiteDimensional_of_compact_coercive | (intros; apply GlobalTheory.CompanionTheory.Glob.finiteDimensional_of_compact_coercive <;> assumption)
end _root_.GlobalTheory.T
