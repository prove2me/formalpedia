-- Prove2me | solution 1 for GlobalTheory.T.local_holomorphic_morse_inequality_uniform
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T18:24:17.481931+00:00
-- url     : https://prove2.me/submissions/f838e740-19b2-410e-8cf7-9e719a579dfc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LocalHolomorphicMorseInequalityUniform
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_IsLocalHomeomorph
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LocalHolomorphicMorseInequalityUniformStatement
import Theorems.Thm_GlobalTheory_morse_local
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_re


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology MeasureTheory Metric ReciprocityTheory.L2DbarEstimates
open scoped ComplexOrder
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (n : ℕ) (U K : Set (V n)) (φ g : V n → ℝ) (ε : ℝ), IsOpen U → IsCompact K → K ⊆ U → ContDiffOn ℝ 2 φ U → (∀ z ∈ U, ∀ ξ : Fin n → ℂ, 0 ≤ (leviV n (fun v => (φ v : ℂ)) z ξ).re) → ContinuousOn g U → (∀ z ∈ U, 0 < g z) → 0 < ε → ∃ δ : ℝ, 0 < δ ∧ (∀ z ∈ K, closedBall z δ ⊆ U) ∧ ∀ᶠ m : ℕ in atTop, ∀ z ∈ K, ∀ f : V n → ℂ, DifferentiableOn ℂ f U → ‖f z‖ ^ 2 * Real.exp (-(m * φ z)) * g z ≤ ((cHess n (fun v => (φ v : ℂ)) z).det.re / Real.pi ^ n + ε) * (m : ℝ) ^ n * ∫ w in ball z δ, ‖f w‖ ^ 2 * Real.exp (-(m * φ w)) * g w := by
  first | exact @GlobalTheory.morse_local | exact GlobalTheory.morse_local | (intros; apply GlobalTheory.morse_local <;> assumption)
end _root_.GlobalTheory.T
