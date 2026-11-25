-- Prove2me | solution 1 for GlobalTheory.abs_two_mul_inner_le_of_norm_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T01:02:53.581534+00:00
-- url     : https://prove2.me/submissions/3f045d9c-9269-45ad-9154-11bdd3d371e2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_ExistsLinearIndependentNormLeSuccMin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_AbsTwoMulInnerLeOfNormSubEqInfDist

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Module Submodule
open scoped InnerProductSpace
open GlobalTheory
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {L : Submodule ℤ E}
namespace GlobalTheory
theorem _root_.solution {a y : E} (h₁ : ‖a‖ ≤ ‖a + y‖) (h₂ : ‖a‖ ≤ ‖a - y‖) :
    |2 * ⟪a, y⟫_ℝ| ≤ ‖y‖ ^ 2 := by
  have e₁ := pow_le_pow_left₀ (norm_nonneg _) h₁ 2
  have e₂ := pow_le_pow_left₀ (norm_nonneg _) h₂ 2
  rw [norm_add_sq_real] at e₁
  rw [norm_sub_sq_real] at e₂
  exact abs_le.2 ⟨by linarith, by linarith⟩
end GlobalTheory
