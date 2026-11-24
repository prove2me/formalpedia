-- Prove2me | solution 1 for GlobalTheory.PolynomialEvaluationMembership.pow_apply_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T19:27:16.953041+00:00
-- url     : https://prove2.me/submissions/f00128a8-294d-4614-b0b7-feefb457ff04

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AevalApplyMem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.PolynomialEvaluationMembership
namespace GlobalTheory.PolynomialEvaluationMembership
theorem _root_.solution {F V : Type} [Field F] [AddCommGroup V] [Module F V]
    (g : Module.End F V) (W : Submodule F V) (hW : ∀ x ∈ W, g x ∈ W) (n : ℕ) :
    ∀ x ∈ W, (g ^ n) x ∈ W := by
  induction n with
  | zero => intro x hx; simpa using hx
  | succ n ih =>
    intro x hx
    rw [pow_succ, Module.End.mul_apply]
    exact ih _ (hW x hx)
end GlobalTheory.PolynomialEvaluationMembership
