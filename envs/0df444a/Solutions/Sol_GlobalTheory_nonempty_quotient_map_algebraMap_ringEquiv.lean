-- Prove2me | solution 1 for GlobalTheory.nonempty_quotient_map_algebraMap_ringEquiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:25:06.253836+00:00
-- url     : https://prove2.me/submissions/91165da9-d674-413f-9911-8bc32f5cd4af

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsRingKrullDimQuotientMvPolynomialEqNat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsFormsAlgebraicIndependentSmulSubSumMem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open MvPolynomial
attribute [local instance] MvPolynomial.gradedAlgebra
variable {σ : Type*} {o : Type*} [CommRing o]
namespace GlobalTheory
theorem _root_.solution (I : Ideal (MvPolynomial σ o)) (J : Ideal o) :
    Nonempty (((MvPolynomial σ o ⧸ I) ⧸ J.map (algebraMap o (MvPolynomial σ o ⧸ I))) ≃+*
      (MvPolynomial σ (o ⧸ J) ⧸ I.map (map (Ideal.Quotient.mk J)))) := by
  have hs : Function.Surjective (map (σ := σ) (Ideal.Quotient.mk J)) :=
    map_surjective _ Ideal.Quotient.mk_surjective
  have h1 : J.map (algebraMap o (MvPolynomial σ o ⧸ I)) =
      (J.map (C : o →+* MvPolynomial σ o)).map (Ideal.Quotient.mk I) := by
    rw [Ideal.map_map]; rfl
  have h2 : RingHom.ker ((Ideal.Quotient.mk (I.map (map (Ideal.Quotient.mk J)))).comp
      (map (σ := σ) (Ideal.Quotient.mk J))) = I ⊔ J.map (C : o →+* MvPolynomial σ o) := by
    rw [← RingHom.comap_ker, Ideal.mk_ker, Ideal.comap_map_of_surjective _ hs,
      ← RingHom.ker_eq_comap_bot, MvPolynomial.ker_map, Ideal.mk_ker]
  exact ⟨(Ideal.quotEquivOfEq h1).trans <| (DoubleQuot.quotQuotEquivQuotSup I _).trans <|
    (Ideal.quotEquivOfEq h2.symm).trans <|
      RingHom.quotientKerEquivOfSurjective (Ideal.Quotient.mk_surjective.comp hs)⟩
end GlobalTheory
