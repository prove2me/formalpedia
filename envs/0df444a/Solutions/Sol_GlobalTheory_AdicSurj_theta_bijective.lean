-- Prove2me | solution 1 for GlobalTheory.AdicSurj.theta_bijective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:09:29.394141+00:00
-- url     : https://prove2.me/submissions/6fa6c64d-9765-45dd-aba9-bda1125a37cc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AdicCompletionTensorQuotientRingEquiv
import Theorems.Thm_GlobalTheory_AdicSurj_psi_surjective
import Theorems.Thm_GlobalTheory_AdicSurj_ker_psi

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
variable {A B : Type} [CommRing A] [CommRing B] [Algebra A B] (J : Ideal A)
namespace GlobalTheory.AdicSurj
theorem _root_.solution [IsNoetherianRing A] (hs : Function.Surjective (algebraMap A B)) :
    Function.Bijective (theta (B := B) J) := by
  let e := RingHom.quotientKerEquivOfSurjective (psi_surjective B J hs)
  have hker : RingHom.ker (psi B J) ≤
      RingHom.ker (Algebra.TensorProduct.includeRight (R := A) (A := B)
        (B := AdicCompletion J A)).toRingHom := by
    rw [ker_psi B J hs, Ideal.map_le_iff_le_comap]
    intro a ha
    have h0 : algebraMap A B a = 0 := LinearMap.mem_ker.mp ha
    rw [Ideal.mem_comap, RingHom.mem_ker]
    change (1 : B) ⊗ₜ[A] algebraMap A (AdicCompletion J A) a = 0
    rw [Algebra.algebraMap_eq_smul_one, ← TensorProduct.smul_tmul, Algebra.smul_def, h0, zero_mul,
      TensorProduct.zero_tmul]
  let σ : AdicCompletion (J.map (algebraMap A B)) B →+* B ⊗[A] AdicCompletion J A :=
    (Ideal.Quotient.lift _ _ hker).comp e.symm.toRingHom
  have hσ : ∀ x, σ (psi B J x) = 1 ⊗ₜ[A] x := by
    intro x
    have : e.symm (psi B J x) = Ideal.Quotient.mk _ x := e.symm_apply_eq.mpr rfl
    simp only [σ, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, this,
      Ideal.Quotient.lift_mk]
    rfl
  have hleft : ∀ t, σ (theta J t) = t := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | add a b ha hb => rw [map_add, map_add, ha, hb]
    | tmul b x =>
      obtain ⟨a, rfl⟩ := hs b
      rw [theta, Algebra.TensorProduct.lift_tmul, Algebra.ofId_apply,
        ← IsScalarTower.algebraMap_apply, ← psi_algebraMap B J a]
      change σ (psi B J _ * psi B J x) = _
      rw [← map_mul, hσ, ← Algebra.smul_def, ← TensorProduct.smul_tmul, Algebra.algebraMap_eq_smul_one]
  refine ⟨Function.LeftInverse.injective hleft, fun y ↦ ?_⟩
  obtain ⟨x, rfl⟩ := psi_surjective B J hs y
  refine ⟨1 ⊗ₜ[A] x, ?_⟩
  rw [theta, Algebra.TensorProduct.lift_tmul, map_one, one_mul]
  rfl
end GlobalTheory.AdicSurj
