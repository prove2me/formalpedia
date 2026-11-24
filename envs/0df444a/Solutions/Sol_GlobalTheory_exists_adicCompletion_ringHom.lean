-- Prove2me | solution 1 for GlobalTheory.exists_adicCompletion_ringHom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:37:58.663+00:00
-- url     : https://prove2.me/submissions/11a61ff8-c6cc-4ac0-80ae-7bea12bd4a6c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsUniqueFactorCompletedStalkOfMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsMemPowSubMemPowSucc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IdealEqBotOfFlatQuotientOfMapMaximalIdeal
import Theorems.Thm_GlobalTheory_IsAdicFamily_comp
import Theorems.Thm_P2M_GlobalTheory_factorPow_eval__9207485a8623


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct LinearMap
open GlobalTheory
universe u v w
open IsLocalRing
variable {A : Type*} [CommRing A]
variable {B : Type*} [CommRing B] {φ : A →+* B} {I : Ideal A} {J : Ideal B}
namespace GlobalTheory
theorem _root_.solution (f : ∀ n : ℕ, A ⧸ I ^ n →+* B ⧸ J ^ n)
    (hf : ∀ {m n : ℕ} (h : m ≤ n), (Ideal.Quotient.factorPow J h).comp (f n) =
      (f m).comp (Ideal.Quotient.factorPow I h)) :
    ∃ ψ : AdicCompletion I A →+* AdicCompletion J B,
      ∀ n x, AdicCompletion.evalₐ J n (ψ x) = f n (AdicCompletion.evalₐ I n x) := by
  let g : ∀ n : ℕ, AdicCompletion I A →+* B ⧸ J ^ n := fun n =>
    (f n).comp (AdicCompletion.evalₐ I n : AdicCompletion I A →+* A ⧸ I ^ n)
  have hg : ∀ {m n : ℕ} (h : m ≤ n), (Ideal.Quotient.factorPow J h).comp (g n) = g m := by
    intro m n h
    ext x
    have := RingHom.congr_fun (hf h) (AdicCompletion.evalₐ I n x)
    simp only [RingHom.comp_apply, factorPow_evalₐ] at this
    exact this
  exact ⟨AdicCompletion.liftRingHom J g hg,
    fun n x => AdicCompletion.evalₐ_liftRingHom J g hg n x⟩
end GlobalTheory
