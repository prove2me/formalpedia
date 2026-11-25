-- Prove2me | solution 1 for GlobalTheory.HermFrame.chTwo_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:51:08.73145+00:00
-- url     : https://prove2.me/submissions/78d4b5e0-36ca-460b-895f-4fd1ff42f545

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_MaIntEmpty
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_EventuallyDifferentiableAtOfContDiffAtTwo
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_LeTwoMulOfForallScale
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ExtFormAdjEqNegSecondForm
import Theorems.Thm_GlobalTheory_HermFrame_opNorm_zero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.HermFrame.opNorm_zero



set_option autoImplicit false
open Matrix Complex ComplexConjugate Filter Topology
open scoped ComplexOrder ContDiff
noncomputable section
open GlobalTheory GlobalTheory.HermFrame
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E]
  [IsScalarTower ℝ ℂ E]
variable {m n l : Type*}
variable [Fintype n] [DecidableEq n]
namespace GlobalTheory.HermFrame
theorem _root_.solution (H : E → Matrix n n ℂ) (z ξ₁ η₁ ξ₂ η₂ : E) :
    chTwo H z ξ₁ η₁ ξ₂ η₂ =
      (wedge (chernOne H z) (chernOne H z) ξ₁ η₁ ξ₂ η₂ - 2 * chernTwo H z ξ₁ η₁ ξ₂ η₂) / 2 := by
  have h : wedge (chernOne H z) (chernOne H z) ξ₁ η₁ ξ₂ η₂ = kappa ^ 2 * ∑ a, ∑ b,
      wedge (fun ξ η => curv H z ξ η a a) (fun ξ η => curv H z ξ η b b) ξ₁ η₁ ξ₂ η₂ := by
    simp only [wedge, chernOne, trace, diag_apply, Finset.sum_add_distrib, Finset.sum_sub_distrib,
      ← Finset.sum_mul_sum]
    ring
  simp only [h, chTwo, chernTwo, curvMinor, Finset.sum_sub_distrib]
  ring
end GlobalTheory.HermFrame
