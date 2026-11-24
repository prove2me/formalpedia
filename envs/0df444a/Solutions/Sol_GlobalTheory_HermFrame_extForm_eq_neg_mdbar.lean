-- Prove2me | solution 1 for GlobalTheory.HermFrame.extForm_eq_neg_mdbar
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:40:34.633722+00:00
-- url     : https://prove2.me/submissions/537f0336-71f2-4c08-92b2-c980c2d3887d

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
variable [Fintype m] [Fintype l] [DecidableEq m] [DecidableEq l]
variable {U : Set E} {H : E → Matrix (m ⊕ l) (m ⊕ l) ℂ} {z : E} {k : WithTop ℕ∞}
namespace GlobalTheory.HermFrame
theorem _root_.solution (H : E → Matrix (m ⊕ l) (m ⊕ l) ℂ) (z η : E) :
    extForm H z η = -mdbar (fun x => orthCoeff (H x)) z η := by
  have h : mdbar (fun x => orthLift (H x)) z η =
      fromRows (-mdbar (fun x => orthCoeff (H x)) z η) 0 := by
    ext (a | a) b <;> simp [orthLift, dbar_neg]
  rw [extForm, h, orthProj, fromCols_mul_fromRows]; simp
end GlobalTheory.HermFrame
