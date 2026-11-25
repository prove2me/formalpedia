-- Prove2me | solution 1 for GlobalTheory.T.quadratic_box_integral_small_ball
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T18:24:32.495362+00:00
-- url     : https://prove2.me/submissions/c8c0b91c-2896-48d9-8a79-249019fa5cca

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_QuadraticBoxIntegralSmallBall
import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CoreR
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_QuadraticBoxIntegralSmallBallStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_WeilSiegel_Inf0_RealTail_tail_small


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Topology GlobalTheory.CompanionTheory.WeilSiegel.Inf0
open scoped ENNReal NNReal Matrix
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (P ι : Type) [Fintype P] [Fintype ι] (a : ℕ), 0 < a → ∀ (Q : (P → ι → ℝ) → (P → ℝ)), Measurable Q → ∀ C : ℝ≥0, (∀ t : P → ℝ, (∀ w, 0 < t w) → ∀ U : Set (P → ℝ), MeasurableSet U → (volume : Measure (P → ι → ℝ)) (Q ⁻¹' U ∩ boxR t) ≤ (C : ℝ≥0∞) * ENNReal.ofReal (∏ w, t w ^ a) * volume U) → ∀ f : (P → ι → ℝ) → ℝ, Measurable f → (∀ x, 0 ≤ f x) → (∀ N : ℕ, ∃ C' : ℝ, ∀ x, f x * (1 + ∑ w, ‖x w‖) ^ N ≤ C') → ∀ ε : ℝ, 0 < ε → ∃ δ R : ℝ, 0 < δ ∧ 0 < R ∧ ∀ U : Set (P → ℝ), MeasurableSet U → ∫⁻ x in Q ⁻¹' U ∩ (coreR δ R)ᶜ, ENNReal.ofReal (f x) ≤ ENNReal.ofReal ε * volume U := by
  first | exact @GlobalTheory.CompanionTheory.WeilSiegel.Inf0.RealTail.tail_small | exact GlobalTheory.CompanionTheory.WeilSiegel.Inf0.RealTail.tail_small | (intros; apply GlobalTheory.CompanionTheory.WeilSiegel.Inf0.RealTail.tail_small <;> assumption)
end _root_.GlobalTheory.T
