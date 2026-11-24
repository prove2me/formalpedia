-- Prove2me | solution 1 for GlobalTheory.integral_ball_translate
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:01:31.724109+00:00
-- url     : https://prove2.me/submissions/f1c97789-6ef3-4fdc-883f-980735ab1df5

import Mathlib
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_IsLocalHomeomorph
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormSqMulIntegralBallLeOfCircleInvariantStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousOnComplexHessianOfContDiffOnTwoStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ComplexHessianPosSemidefOfLeviFormNonnegStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UniformTaylorBoundLeviPluriharmonicSplitStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_TruncatedGaussianIntegralUniformPosSemidefStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LocalHolomorphicMorseInequalityUniform

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
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {n : ℕ} (z : V n) (δ : ℝ) (F : V n → ℝ) :
    ∫ w in ball (0 : V n) δ, F (z + w) = ∫ w in ball z δ, F w := by
  rw [← integral_indicator measurableSet_ball, ← integral_indicator measurableSet_ball]
  have key : (fun w => (ball (0 : V n) δ).indicator (fun w => F (z + w)) w) =
      fun w => (ball z δ).indicator F (z + w) := by
    funext w
    have hiff : w ∈ ball (0 : V n) δ ↔ z + w ∈ ball z δ := by
      simp [mem_ball, dist_eq_norm]
    by_cases hw : w ∈ ball (0 : V n) δ
    · simp [Set.indicator, hw, hiff.1 hw]
    · simp [Set.indicator, hw, (not_congr hiff).1 hw]
  rw [key]
  exact integral_add_left_eq_self (fun w => (ball z δ).indicator F w) z
end GlobalTheory
