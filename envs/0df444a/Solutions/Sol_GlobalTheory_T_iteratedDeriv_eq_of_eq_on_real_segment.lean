-- Prove2me | solution 1 for GlobalTheory.T.iteratedDeriv_eq_of_eq_on_real_segment
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T18:20:41.706366+00:00
-- url     : https://prove2.me/submissions/57f7553f-0f53-42fa-a621-b1c79bddae2c

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IteratedDerivEqOfEqOnRealSegment
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IteratedDerivEqOfEqOnRealSegmentStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_ComplexAnalysis_iteratedDeriv_zero_eq_of_eq_on_real_points


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
theorem _root_.solution : ∀ (f g : ℂ → ℂ) (ρ : ℝ), 0 < ρ → DifferentiableOn ℂ f (Metric.ball 0 ρ) → DifferentiableOn ℂ g (Metric.ball 0 ρ) → (∀ s : ℝ, |s| < ρ → f s = g s) → ∀ r : ℕ, iteratedDeriv r f 0 = iteratedDeriv r g 0 := by
  first | exact @GlobalTheory.CompanionTheory.ComplexAnalysis.iteratedDeriv_zero_eq_of_eq_on_real_points | exact GlobalTheory.CompanionTheory.ComplexAnalysis.iteratedDeriv_zero_eq_of_eq_on_real_points | (intros; apply GlobalTheory.CompanionTheory.ComplexAnalysis.iteratedDeriv_zero_eq_of_eq_on_real_points <;> assumption)
end _root_.GlobalTheory.T
