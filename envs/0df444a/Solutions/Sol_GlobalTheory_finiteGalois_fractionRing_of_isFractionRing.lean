-- Prove2me | solution 1 for GlobalTheory.finiteGalois_fractionRing_of_isFractionRing
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:48:57.824677+00:00
-- url     : https://prove2.me/submissions/98b4a2dc-89fb-4952-bc92-0208eed7bc47

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FiniteGaloisFractionRingOfIsFractionRing

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
namespace GlobalTheory
namespace _root_.GlobalTheory
theorem _root_.solution :
    ∀ (A K L : Type) [CommRing A] [IsDomain A] [Field K] [Algebra A K] [IsFractionRing A K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L] [Algebra A L], (∀ a : A, algebraMap A L a = algebraMap K L (algebraMap A K a)) → ∃ (_ : Algebra (FractionRing A) L) (_ : IsScalarTower A (FractionRing A) L), FiniteDimensional (FractionRing A) L ∧ IsGalois (FractionRing A) L ∧ ∀ (σ : L ≃ₐ[FractionRing A] L) (x : K), σ (algebraMap K L x) = algebraMap K L x := by
  intro A K L _ _ _ _ _ _ _ _ _ _ h
  let e : FractionRing A ≃ₐ[A] K := FractionRing.algEquiv A K
  letI alg : Algebra (FractionRing A) L := ((algebraMap K L).comp e.toRingHom).toAlgebra
  have hmap : ∀ y : FractionRing A, algebraMap (FractionRing A) L y = algebraMap K L (e y) :=
    fun _ => rfl
  have hcomp : (algebraMap (FractionRing A) L).comp (e.symm.toRingEquiv : K →+* FractionRing A) =
      ((RingEquiv.refl L : L ≃+* L) : L →+* L).comp (algebraMap K L) := by
    ext x; simp [hmap]
  refine ⟨alg, IsScalarTower.of_algebraMap_eq fun a => ?_, ?_, ?_, ?_⟩
  · rw [hmap, AlgEquiv.commutes, h]
  · exact Module.Finite.of_equiv_equiv e.symm.toRingEquiv (RingEquiv.refl L) hcomp
  · exact IsGalois.of_equiv_equiv (f := e.symm.toRingEquiv) (g := RingEquiv.refl L) hcomp
  · intro σ x
    have := σ.commutes (e.symm x)
    simpa [hmap] using this
end _root_.GlobalTheory
end GlobalTheory
