-- Prove2me | solution 1 for GlobalTheory.AdicSurj.tensor_ringEquiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:24:40.808093+00:00
-- url     : https://prove2.me/submissions/39b02a91-b24b-4967-af3e-7b132bfa4c0c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AdicCompletionTensorQuotientRingEquiv
import Theorems.Thm_GlobalTheory_AdicSurj_theta_bijective

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
theorem _root_.solution [IsNoetherianRing A] (hs : Function.Surjective (algebraMap A B))
    (I : Ideal B) (hI : I = J.map (algebraMap A B)) (K : Type) [CommRing K] [Algebra B K] [Algebra A K]
    [IsScalarTower A B K] :
    Nonempty (AdicCompletion I B ⊗[B] K ≃+* AdicCompletion J A ⊗[A] K) := by
  subst hI
  let θ := AlgEquiv.ofBijective (theta (B := B) J) (theta_bijective J hs)
  exact ⟨(Algebra.TensorProduct.comm B _ K).toRingEquiv.trans
    ((Algebra.TensorProduct.congr (AlgEquiv.refl : K ≃ₐ[B] K) θ.symm).toRingEquiv.trans
    ((Algebra.TensorProduct.cancelBaseChange A B B K (AdicCompletion J A)).toRingEquiv.trans
    (Algebra.TensorProduct.comm A K (AdicCompletion J A)).toRingEquiv))⟩
end GlobalTheory.AdicSurj
