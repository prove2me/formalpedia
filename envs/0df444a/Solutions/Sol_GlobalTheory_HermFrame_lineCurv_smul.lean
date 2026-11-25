-- Prove2me | solution 1 for GlobalTheory.HermFrame.lineCurv_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:51:45.122298+00:00
-- url     : https://prove2.me/submissions/d16dd5e4-c02c-456c-8795-b55fbb79252b

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_MaIntEmpty
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_EventuallyDifferentiableAtOfContDiffAtTwo
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_LeTwoMulOfForallScale
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ExtFormAdjEqNegSecondForm
import Theorems.Thm_GlobalTheory_HermFrame_form_smul_left
import Theorems.Thm_GlobalTheory_HermFrame_form_smul_right
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
theorem _root_.solution (H : E → Matrix n n ℂ) (z : E) (w : n → ℂ) {c : ℂ} (hc : c ≠ 0) :
    lineCurv H z (c • w) = lineCurv H z w := by
  ext ξ η
  have hc' : conj c ≠ 0 := by simpa using hc
  simp only [lineCurv, mulVec_smul, form_smul_left, form_smul_right, mul_div_mul_left _ _ hc,
    mul_div_mul_left _ _ hc']
end GlobalTheory.HermFrame
