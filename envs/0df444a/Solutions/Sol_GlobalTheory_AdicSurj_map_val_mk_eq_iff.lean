-- Prove2me | solution 1 for GlobalTheory.AdicSurj.map_val_mk_eq_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:48:54.249202+00:00
-- url     : https://prove2.me/submissions/a7a846d5-c003-4dc4-a899-fe6a388b78d7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AdicCompletionTensorQuotientRingEquiv
import Theorems.Thm_GlobalTheory_AdicSurj_mem_smul_top_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing TensorProduct
open GlobalTheory GlobalTheory.AdicSurj
open AdicCompletion
variable (B : Type) {A : Type} [CommRing A] [CommRing B] [Algebra A B] (J : Ideal A)
namespace GlobalTheory.AdicSurj
theorem _root_.solution (s : AdicCauchySequence J A) (n : ℕ) (c : B) :
    (map J (Algebra.linearMap A B) (AdicCompletion.mk J A s)).val n = Submodule.Quotient.mk c ↔
      lev B J n (AdicCompletion.mk J A s) = Ideal.Quotient.mk _ c := by
  rw [map_val_apply, mk_apply_coe, lev_mk, Submodule.mkQ_apply, LinearMap.reduceModIdeal_apply,
    Submodule.Quotient.eq, Ideal.Quotient.eq, mem_smul_top_iff]
  rfl
end GlobalTheory.AdicSurj
