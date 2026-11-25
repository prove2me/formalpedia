-- Prove2me | solution 1 for GlobalTheory.HermFrame.formAbsLe_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:49:45.586707+00:00
-- url     : https://prove2.me/submissions/3646b3d0-4f65-4e35-8b26-4e41e737aabc

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
namespace GlobalTheory.HermFrame
theorem _root_.solution {V : Type*} {α β : V → V → ℂ} {C : ℝ} :
    FormAbsLe α C β ↔ ∀ ξ, |diagVal α ξ| ≤ C * diagVal β ξ := by
  have h : ∀ (c : ℝ) ξ, diagVal (fun ξ η => c * β ξ η) ξ = c * diagVal β ξ := fun c ξ => by
    rw [diagVal, diagVal, mul_left_comm, re_ofReal_mul]
  simp only [FormAbsLe, FormLe, ← ofReal_neg, h, abs_le, forall_and, neg_mul]
end GlobalTheory.HermFrame
