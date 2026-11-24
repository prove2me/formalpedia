-- Prove2me | solution 1 for GlobalTheory.T.complex_phase_calculus_rootOfUnity
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:05:29.123279+00:00
-- url     : https://prove2.me/submissions/78ce6752-6318-4c38-aba6-570451ceea0e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ComplexPhaseCalculusRootOfUnity
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IntMIffInt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ComplexPhaseCalculusRootOfUnityStatement
import Theorems.Thm_GlobalTheory_Phase_Calc_calculus


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex GlobalTheory.SW GlobalTheory.Phase
open scoped ComplexConjugate Real
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : (∀ a b : ℂ, Ph a → Ph b → Ph (a * b)) ∧ (∀ a : ℂ, Ph a → Ph (conj a) ∧ Ph a⁻¹) ∧ (∀ t : ℝ, Ph (t : ℂ)) ∧ (∀ a : ℂ, IsMu a → Ph a ∧ ‖a‖ = 1) ∧ (∀ a : ℂ, Ph a → ‖a‖ = 1 → IsMu a) ∧ (∀ a b : ℂ, IsMu a → IsMu b → IsMu (a * b) ∧ IsMu a⁻¹ ∧ IsMu (conj a)) ∧ (∀ (a : ℂ) (k : ℕ), 0 < k → (IsMu (a ^ k) → IsMu a) ∧ (Ph (a ^ k) → Ph a)) ∧ (∀ q : ℚ, IsMu (cexp (π * I * (q : ℂ)))) ∧ ∀ a b : ℂ, b ≠ 0 → Ph b → Ph (a * b) → Ph a := by
  first | exact @GlobalTheory.Phase.Calc.calculus | exact GlobalTheory.Phase.Calc.calculus | (intros; apply GlobalTheory.Phase.Calc.calculus <;> assumption)
end _root_.GlobalTheory.T
