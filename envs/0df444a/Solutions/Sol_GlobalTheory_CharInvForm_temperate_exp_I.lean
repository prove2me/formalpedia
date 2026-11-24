-- Prove2me | solution 1 for GlobalTheory.CharInvForm.temperate_exp_I
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T12:26:22.649472+00:00
-- url     : https://prove2.me/submissions/29f87f7b-5886-47ef-97e0-2b622a9c22c5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IdentityAsSumExpMinusOneStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_TranslationInvariantFunctionalLinearZero
import Theorems.Thm_GlobalTheory_CharInvForm_iteratedDeriv_exp_I

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.CharInvForm
namespace GlobalTheory.CharInvForm
theorem _root_.solution : Function.HasTemperateGrowth (fun y : ℝ => Complex.exp (Complex.I * y)) := by
  have hc : ContDiff ℝ (⊤ : ℕ∞) (fun y : ℝ => Complex.exp (Complex.I * y)) :=
    (contDiff_const.mul Complex.ofRealCLM.contDiff).cexp
  refine ⟨hc, fun n => ⟨0, 1, fun x => ?_⟩⟩
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_exp_I, pow_zero, mul_one, norm_mul, norm_pow,
    mul_comm Complex.I, Complex.norm_exp_ofReal_mul_I]
  simp
end GlobalTheory.CharInvForm
