-- Prove2me | solution 1 for GlobalTheory.T.setIntegral_le_pow_mul_setIntegral_of_expanding
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:57:47.50156+00:00
-- url     : https://prove2.me/submissions/a766fde0-fb02-4c71-abd0-2e7a5a8d5a35

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SetIntegralLeOfExpanding
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SetIntegralLeOfExpandingStatement
import Theorems.Thm_GlobalTheory_setIntegral_le_of_expanding


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (N : ℕ) (A Q : Set (Fin N → ℝ)) (K : ℝ) (f : (Fin N → ℝ) → (Fin N → ℝ)) (h₁ h₂ : (Fin N → ℝ) → ℝ), IsCompact A → IsCompact Q → 0 ≤ K → Continuous h₁ → Continuous h₂ → (∀ t, 0 ≤ h₁ t) → (∀ t, 0 ≤ h₂ t) → (∀ t ∈ A, f t ∈ Q ∧ h₁ t ≤ h₂ (f t)) → (∀ t ∈ A, ∀ t' ∈ A, ‖t - t'‖ ≤ K * ‖f t - f t'‖) → ∫ t in A, h₁ t ≤ K ^ N * ∫ t in Q, h₂ t := by
  first | exact @GlobalTheory.setIntegral_le_of_expanding | exact GlobalTheory.setIntegral_le_of_expanding | (intros; apply GlobalTheory.setIntegral_le_of_expanding <;> assumption)
end _root_.GlobalTheory.T
