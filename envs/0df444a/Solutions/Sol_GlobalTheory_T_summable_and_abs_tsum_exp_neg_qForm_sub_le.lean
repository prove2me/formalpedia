-- Prove2me | solution 1 for GlobalTheory.T.summable_and_abs_tsum_exp_neg_qForm_sub_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:06:16.533823+00:00
-- url     : https://prove2.me/submissions/c1128cea-e1f9-4633-ace8-dbe487d4f559

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ThetaQForm
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_LamIdealOfNotPrimePow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ThetaQFormStatement
import Theorems.Thm_GlobalTheory_Hk_theta_qForm


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex ArithmeticFunction MeasureTheory Filter Topology NumberField GlobalTheory.Hk GlobalTheory.Mem
open scoped Classical
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ α γ l θ₁ θ₂ t : ℝ, 0 < α → 0 < γ → 0 < t → Summable (fun v : ℤ × ℤ => Real.exp (-(t * qForm α γ l θ₁ θ₂ v))) ∧ |∑' v : ℤ × ℤ, Real.exp (-(t * qForm α γ l θ₁ θ₂ v)) - Real.pi / Real.sqrt (α * γ) / t| ≤ Real.pi / Real.sqrt (α * γ) / t * ((α * t) ^ 2 + (γ * t) ^ 2 + (α * t) ^ 2 * (γ * t) ^ 2) := by
  first | exact @GlobalTheory.Hk.theta_qForm | exact GlobalTheory.Hk.theta_qForm | (intros; apply GlobalTheory.Hk.theta_qForm <;> assumption)
end _root_.GlobalTheory.T
