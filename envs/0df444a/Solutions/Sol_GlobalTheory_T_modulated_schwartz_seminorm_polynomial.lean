-- Prove2me | solution 1 for GlobalTheory.T.modulated_schwartz_seminorm_polynomial
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T18:23:24.802681+00:00
-- url     : https://prove2.me/submissions/51be6359-461b-4ede-bd7a-99de13f6c9af

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ModulatedSchwartzSeminormPolynomial
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ModulatedSchwartzSeminormPolynomialStatement
import Theorems.Thm_GlobalTheory_CharModGrowth_seminorm_char_mul_polynomial_growth


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (P : LinearMap.BilinForm ℝ V) (h : SchwartzMap V ℂ) (v : V → SchwartzMap V ℂ),
    (∀ μ x, v μ x = Complex.exp (2 * Real.pi * Complex.I * (P x μ : ℂ)) * h x) →
    ∀ k n : ℕ, ∃ C : ℝ, ∀ μ, SchwartzMap.seminorm ℂ k n (v μ) ≤ C * (1 + ‖μ‖) ^ n := by
  first | exact @GlobalTheory.CharModGrowth.seminorm_char_mul_polynomial_growth | exact GlobalTheory.CharModGrowth.seminorm_char_mul_polynomial_growth | (intros; apply GlobalTheory.CharModGrowth.seminorm_char_mul_polynomial_growth <;> assumption)
end _root_.GlobalTheory.T
