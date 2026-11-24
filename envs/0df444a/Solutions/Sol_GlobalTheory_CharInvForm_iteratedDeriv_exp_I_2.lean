-- Prove2me | solution 2 for GlobalTheory.CharInvForm.iteratedDeriv_exp_I
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:10:41.729907+00:00
-- url     : https://prove2.me/submissions/c68d7ae0-2fa2-48e0-bcee-727720638e44

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IdentityAsSumExpMinusOneStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_TranslationInvariantFunctionalLinearZero

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
theorem _root_.solution (n : ℕ) :
    iteratedDeriv n (fun y : ℝ => Complex.exp (Complex.I * y)) =
      fun y : ℝ => Complex.I ^ n * Complex.exp (Complex.I * y) := by
  induction n with
  | zero => funext y; simp
  | succ n ih =>
    rw [iteratedDeriv_succ, ih]
    funext y
    have h1 : HasDerivAt (fun y : ℝ => (y : ℂ)) 1 y := by
      simpa using (hasDerivAt_id y).ofReal_comp
    have h : HasDerivAt (fun y : ℝ => Complex.I ^ n * Complex.exp (Complex.I * y))
        (Complex.I ^ n * (Complex.exp (Complex.I * y) * (Complex.I * 1))) y :=
      ((h1.const_mul Complex.I).cexp).const_mul (Complex.I ^ n)
    rw [h.deriv]; ring
end GlobalTheory.CharInvForm
