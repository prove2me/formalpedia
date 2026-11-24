-- Prove2me | solution 1 for GlobalTheory.integrable_exp_neg_mul_abs_line
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:01:27.013152+00:00
-- url     : https://prove2.me/submissions/2aa9f419-b0bd-4214-8127-ff3c41ef88d6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FderivIntegralApplyOfHolomorphicOfDominated
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IntegrableExpNegMulAbs
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_EqZeroOfExpDecayOfFourierEqZeroOnHalfLine
import Theorems.Thm_GlobalTheory_IntegrableExpNegAbs_integrable_exp_neg_mul_abs


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Filter Set
open scoped Topology FourierTransform
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {c : ℝ} (hc : 0 < c) :
    Integrable (fun s : ℝ => Real.exp (-(c * |s|))) := by
  first
  | exact @_root_.GlobalTheory.IntegrableExpNegAbs.integrable_exp_neg_mul_abs
  | exact _root_.GlobalTheory.IntegrableExpNegAbs.integrable_exp_neg_mul_abs
  | (apply _root_.GlobalTheory.IntegrableExpNegAbs.integrable_exp_neg_mul_abs <;> assumption)
  | (intros; apply _root_.GlobalTheory.IntegrableExpNegAbs.integrable_exp_neg_mul_abs <;> assumption)
  | (intros; apply @_root_.GlobalTheory.IntegrableExpNegAbs.integrable_exp_neg_mul_abs <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.IntegrableExpNegAbs.integrable_exp_neg_mul_abs ..)
end GlobalTheory
