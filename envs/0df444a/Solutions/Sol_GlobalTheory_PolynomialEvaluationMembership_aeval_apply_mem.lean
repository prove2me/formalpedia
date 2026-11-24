-- Prove2me | solution 1 for GlobalTheory.PolynomialEvaluationMembership.aeval_apply_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T19:42:37.487653+00:00
-- url     : https://prove2.me/submissions/69200b9c-9982-4a2b-9ebf-bc9d3e8a33af

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AevalApplyMem
import Theorems.Thm_GlobalTheory_PolynomialEvaluationMembership_pow_apply_mem

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
    (g : Module.End F V) (W : Submodule F V) (hW : ∀ x ∈ W, g x ∈ W) (p : Polynomial F) :
    ∀ x ∈ W, (Polynomial.aeval g p) x ∈ W := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    intro x hx
    rw [map_add, LinearMap.add_apply]
    exact W.add_mem (hp x hx) (hq x hx)
  | monomial n a =>
    intro x hx
    rw [Polynomial.aeval_monomial, Module.End.mul_apply, Module.algebraMap_end_apply]
    exact W.smul_mem a (pow_apply_mem g W hW n x hx)
end GlobalTheory.PolynomialEvaluationMembership
