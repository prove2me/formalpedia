-- Prove2me | solution 1 for GlobalTheory.AdicSurj.psi_surjective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:55:19.997833+00:00
-- url     : https://prove2.me/submissions/c9c5dbd6-504c-4b8a-a19c-385532cc1116

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AdicCompletionTensorQuotientRingEquiv
import Theorems.Thm_GlobalTheory_AdicSurj_mem_smul_top_iff
import Theorems.Thm_GlobalTheory_AdicSurj_map_val_mk_eq_iff

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
theorem _root_.solution [IsNoetherianRing A] (hs : Function.Surjective (algebraMap A B)) :
    Function.Surjective (psi B J) := by
  intro y
  obtain ⟨t, rfl⟩ := AdicCompletion.mk_surjective _ _ y
  let t' : AdicCauchySequence J B := ⟨t.val, fun {m n} hmn ↦ by
    have h := t.property hmn
    rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] at h
    rw [SModEq.sub_mem, mem_smul_top_iff]; exact h⟩
  obtain ⟨x, hx⟩ := map_surjective J (f := Algebra.linearMap A B) hs (AdicCompletion.mk J _ t')
  obtain ⟨s, rfl⟩ := AdicCompletion.mk_surjective J A x
  refine ⟨AdicCompletion.mk J A s, ext_evalₐ fun n ↦ ?_⟩
  rw [evalₐ_psi, evalₐ_mk]
  refine (map_val_mk_eq_iff B J s n (t n)).mp ?_
  rw [hx]; rfl
end GlobalTheory.AdicSurj
