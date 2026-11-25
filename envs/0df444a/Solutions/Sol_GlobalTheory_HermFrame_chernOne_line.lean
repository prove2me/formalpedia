-- Prove2me | solution 1 for GlobalTheory.HermFrame.chernOne_line
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:48:59.776724+00:00
-- url     : https://prove2.me/submissions/9cb16407-0313-47cf-9330-e1555bb8cd92

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_MaIntEmpty
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_EventuallyDifferentiableAtOfContDiffAtTwo
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_LeTwoMulOfForallScale
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ExtFormAdjEqNegSecondForm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
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
theorem _root_.solution [Unique n] {H : E → Matrix n n ℂ} {z : E} {f : E → ℝ}
    (hf : ContDiffAt ℝ 2 f z) (hf0 : f z ≠ 0) (hH : ∀ᶠ x in 𝓝 z, H x default default = f x)
    (ξ η : E) : chernOne H z ξ η = -ddc (fun x => Real.log (f x)) z ξ η := by
  rw [chernOne, trace, Fintype.sum_unique, diag_apply, curv_line hf hf0 hH, ddc, mul_neg]
end GlobalTheory.HermFrame
