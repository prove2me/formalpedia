-- Prove2me | solution 1 for GlobalTheory.T.integral_prime_sum_sq_ge_of_derSeries_large
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:15:04.990157+00:00
-- url     : https://prove2.me/submissions/25d6c8de-2d83-48c0-b514-ad4cb0a4b128

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_LargeMeanOfLargeDerivative
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_ZerosDisc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_LargeMeanOfLargeDerivativeStatement
import Theorems.Thm_GlobalTheory_Lin_LargeMean_large_mean_of_large_derivative


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology GlobalTheory.Lin
open scoped Classical
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ A : ℝ, 1 ≤ A → ∃ a b C r₀ K₀ : ℝ, 0 < a ∧ a < b ∧ 0 < C ∧ 0 < r₀ ∧ ∀ (c : ℕ → ℂ) (r : ℝ) (K k : ℕ), (∀ n, ‖c n‖ ≤ 1) → 0 < r → r ≤ r₀ → K₀ ≤ K → K ≤ k → k ≤ 2 * K → 1 / (A * r) ^ (k + 1) ≤ ‖derSeries c k ((1 + r : ℝ) : ℂ)‖ → Real.exp (-(C * K)) / r ^ 3 ≤ ∫ y in (Real.exp (a * K / r))..(Real.exp (b * K / r)), ‖∑ p ∈ primesIoc (Real.exp (a * K / r)) y, (Real.log p : ℂ) * c p / p‖ ^ 2 / y := by
  first | exact @GlobalTheory.Lin.LargeMean.large_mean_of_large_derivative | exact GlobalTheory.Lin.LargeMean.large_mean_of_large_derivative | (intros; apply GlobalTheory.Lin.LargeMean.large_mean_of_large_derivative <;> assumption)
end _root_.GlobalTheory.T
