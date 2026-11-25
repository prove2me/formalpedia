-- Prove2me | solution 1 for GlobalTheory.T.norm_creationAnnihilation_word_le_numberOperator_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T18:23:27.813797+00:00
-- url     : https://prove2.me/submissions/c1dcaae8-5830-4d66-860c-0c86126f8d9c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NormCreationAnnihilationWordLeNumberOperatorPow
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NormCreationAnnihilationWordLeNumberOperatorPowStatement
import Theorems.Thm_GlobalTheory_norm_word_le_number_pow


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
theorem _root_.solution : ∀ (T H κ : Type) [AddCommGroup T] [Module ℂ T] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [Fintype κ] (Φ : T →ₗ[ℂ] H) (a c : κ → Module.End ℂ T) (M : Module.End ℂ T) (r r' : ℝ), 1 ≤ r → r' ≤ r → (∀ j x y, inner ℂ (Φ (c j x)) (Φ y) = inner ℂ (Φ x) (Φ (a j y))) → (∀ j, a j * c j - c j * a j = (r' : ℂ) • 1) → M = ∑ j, c j * a j + (r : ℂ) • 1 → (∀ j, M * a j = a j * (M - (r : ℂ) • 1)) → (∀ j, M * c j = c j * (M + (r : ℂ) • 1)) → ∀ (l : List (Module.End ℂ T)) (d : ℕ), (∀ X ∈ l, X ∈ Submodule.span ℂ (Set.range a ∪ Set.range c)) → l.length ≤ d → ∃ C : ℝ, ∀ x, ‖Φ (l.prod x)‖ ≤ C * ‖Φ ((M ^ d) x)‖ := by
  first | exact @GlobalTheory.norm_word_le_number_pow | exact GlobalTheory.norm_word_le_number_pow | (intros; apply GlobalTheory.norm_word_le_number_pow <;> assumption)
end _root_.GlobalTheory.T
