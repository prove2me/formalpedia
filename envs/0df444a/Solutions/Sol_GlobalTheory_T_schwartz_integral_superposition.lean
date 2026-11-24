-- Prove2me | solution 1 for GlobalTheory.T.schwartz_integral_superposition
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:38:54.742022+00:00
-- url     : https://prove2.me/submissions/df5b9d58-d7d4-4d58-96de-a16411a056a9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzIntegralSuperposition
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzIntegralSuperpositionStatement
import Theorems.Thm_GlobalTheory_schwartz_clm_integral_comm


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
theorem _root_.solution : ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (P : Type) [TopologicalSpace P]
    [SecondCountableTopology P] [MeasurableSpace P] [OpensMeasurableSpace P] (ν : Measure P)
    (Φ : P → SchwartzMap E ℂ), Continuous Φ → ∀ (c : P → ℂ), AEStronglyMeasurable c ν →
    (∀ k n : ℕ, Integrable (fun ξ => ‖c ξ‖ * SchwartzMap.seminorm ℂ k n (Φ ξ)) ν) →
    ∀ (u : SchwartzMap E ℂ), (∀ x, u x = ∫ ξ, c ξ * Φ ξ x ∂ν) →
    ∀ (Λ : SchwartzMap E ℂ →L[ℂ] ℂ), Λ u = ∫ ξ, c ξ * Λ (Φ ξ) ∂ν := by
  first | exact @GlobalTheory.schwartz_clm_integral_comm | exact GlobalTheory.schwartz_clm_integral_comm | (intros; apply GlobalTheory.schwartz_clm_integral_comm <;> assumption)
end _root_.GlobalTheory.T
