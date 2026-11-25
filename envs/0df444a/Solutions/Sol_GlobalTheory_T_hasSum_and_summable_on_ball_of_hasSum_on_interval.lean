-- Prove2me | solution 1 for GlobalTheory.T.hasSum_and_summable_on_ball_of_hasSum_on_interval
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T18:18:29.393898+00:00
-- url     : https://prove2.me/submissions/0adb4395-68bc-4c5d-8ae1-da41aae52b8b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_GradedSeriesContinuationDominated
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_GradedSeriesContinuationDominatedStatement
import Theorems.Thm_GlobalTheory_gradedSeries_continuation_dominated


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
theorem _root_.solution : ∀ {ι : Type} (deg : ι → ℕ), (∀ k, {i | deg i = k}.Finite) → ∀ (a : ι → ℂ) (b : ι → ℝ) (C δ ρ : ℝ) (P P' : ℂ → ℂ), 0 < δ → (∀ i, 0 ≤ b i) → (∀ i, ‖a i‖ ≤ C * b i) → DifferentiableOn ℂ P (Metric.ball 0 ρ) → DifferentiableOn ℂ P' (Metric.ball 0 ρ) → (∀ x : ℝ, 0 < x → x < δ → HasSum (fun i => a i * (x : ℂ) ^ deg i) (P x) ∧ HasSum (fun i => (b i : ℂ) * (x : ℂ) ^ deg i) (P' x)) → ∀ X : ℂ, ‖X‖ < ρ → HasSum (fun i => a i * X ^ deg i) (P X) ∧ Summable (fun i => b i * ‖X‖ ^ deg i) := by
  first | exact @GlobalTheory.gradedSeries_continuation_dominated | exact GlobalTheory.gradedSeries_continuation_dominated | (intros; apply GlobalTheory.gradedSeries_continuation_dominated <;> assumption)
end _root_.GlobalTheory.T
