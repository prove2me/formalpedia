-- Prove2me | solution 1 for GlobalTheory.exists_adicCompletion_ringEquiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:46:52.344599+00:00
-- url     : https://prove2.me/submissions/953ce3ac-31f1-45ce-a861-778b3b195914

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsUniqueFactorCompletedStalkOfMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsMemPowSubMemPowSucc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IdealEqBotOfFlatQuotientOfMapMaximalIdeal
import Theorems.Thm_GlobalTheory_exists_adicCompletion_ringHom

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
theorem _root_.solution (hle : ∀ n : ℕ, I ^ n ≤ (J ^ n).comap φ)
    (h : ∀ n, Function.Bijective (Ideal.quotientMap (J ^ n) φ (hle n))) :
    ∃ ψ : AdicCompletion I A ≃+* AdicCompletion J B,
      (∀ n x, AdicCompletion.evalₐ J n (ψ x) =
        Ideal.quotientMap (J ^ n) φ (hle n) (AdicCompletion.evalₐ I n x)) ∧
      ∀ a, ψ (algebraMap A _ a) = algebraMap B _ (φ a) := by
  let e : ∀ n : ℕ, A ⧸ I ^ n ≃+* B ⧸ J ^ n := fun n => RingEquiv.ofBijective _ (h n)
  have he : ∀ {m n : ℕ} (hmn : m ≤ n) (x : A ⧸ I ^ n),
      Ideal.Quotient.factorPow J hmn (e n x) = e m (Ideal.Quotient.factorPow I hmn x) := by
    intro m n hmn x
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    rfl
  obtain ⟨ψ, hψ⟩ := exists_adicCompletion_ringHom (I := I) (J := J)
    (fun n => (e n : A ⧸ I ^ n →+* B ⧸ J ^ n)) (fun hmn => RingHom.ext fun x => he hmn x)
  obtain ⟨χ, hχ⟩ := exists_adicCompletion_ringHom (I := J) (J := I)
    (fun n => ((e n).symm : B ⧸ J ^ n →+* A ⧸ I ^ n))
    (fun {m n} hmn => RingHom.ext fun y => (e m).injective (by
      simp only [RingHom.comp_apply, RingHom.coe_coe, ← he, RingEquiv.apply_symm_apply]))
  refine ⟨RingEquiv.ofRingHom ψ χ ?_ ?_, hψ, fun a => ?_⟩
  · refine RingHom.ext fun y => AdicCompletion.ext_evalₐ fun n => ?_
    simp [hψ, hχ]
  · refine RingHom.ext fun y => AdicCompletion.ext_evalₐ fun n => ?_
    simp [hψ, hχ]
  · refine AdicCompletion.ext_evalₐ fun n => (hψ n _).trans ?_
    rw [AdicCompletion.algebraMap_apply, AdicCompletion.algebraMap_apply,
      AdicCompletion.evalₐ_of, AdicCompletion.evalₐ_of]
    rfl
end GlobalTheory
