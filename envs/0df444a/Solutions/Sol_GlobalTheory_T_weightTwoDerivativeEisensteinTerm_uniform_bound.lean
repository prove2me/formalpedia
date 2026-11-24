-- Prove2me | solution 1 for GlobalTheory.T.weightTwoDerivativeEisensteinTerm_uniform_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:27:06.938814+00:00
-- url     : https://prove2.me/submissions/af0cf851-6a4e-45f9-ba53-40d65d185df2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_WeightTwoDerivativeEisensteinTermUniformBound
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DifferentiableRisingS
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_WeightTwoDerivativeEisensteinTermUniformBoundStatement
import Theorems.Thm_GlobalTheory_WeightTwoSum_Bound_eTerm_bound


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.WeightTwoSum
open scoped ContDiff nonZeroDivisors
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I] (φ : I → E →+* ℂ), IsCMType φ → ∀ (m : I → ℕ) (σ : ℂ) (r : ℝ), 0 ≤ σ.re → r < 1 → ∃ C : ℝ, ∀ z : I → ℂ, (∀ i, ‖z i‖ ≤ r) → ∀ x : E, x ≠ 0 → ‖eTerm φ m σ z x‖ ≤ C * |(Algebra.norm ℚ x : ℝ)| ^ (-(1 + σ.re)) := by
  first | exact @GlobalTheory.WeightTwoSum.Bound.eTerm_bound | exact GlobalTheory.WeightTwoSum.Bound.eTerm_bound | (intros; apply GlobalTheory.WeightTwoSum.Bound.eTerm_bound <;> assumption)
end _root_.GlobalTheory.T
