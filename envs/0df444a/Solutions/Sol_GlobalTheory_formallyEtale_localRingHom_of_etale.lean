-- Prove2me | solution 1 for GlobalTheory.formallyEtale_localRingHom_of_etale
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:57:39.328129+00:00
-- url     : https://prove2.me/submissions/b4f2fcc1-2f52-4426-8353-6baa156b5aec

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_StalkMapFlatFormallyEtaleEssFiniteTypeOfEtaleRes

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry
open GlobalTheory
universe u
namespace GlobalTheory
theorem _root_.solution {R S : Type} [CommRing R] [CommRing S]
    (f : R →+* S) (hf : f.Etale) (J : Ideal S) [J.IsPrime] :
    (Localization.localRingHom (J.comap f) J f rfl).FormallyEtale := by
  algebraize [f]
  let Rₓ := Localization.AtPrime (J.comap f)
  let Sₓ := Localization.AtPrime J
  let : Algebra Rₓ Sₓ := (Localization.localRingHom _ _ _ rfl).toAlgebra
  have : IsScalarTower R Rₓ Sₓ := .of_algebraMap_eq
    fun x ↦ (Localization.localRingHom_to_map _ _ _ rfl x).symm
  have : Algebra.FormallyEtale R Sₓ := inferInstance
  have : Algebra.FormallyEtale Rₓ Sₓ :=
    Algebra.FormallyEtale.localization_base (J.comap f).primeCompl
  exact (RingHom.formallyEtale_algebraMap (R := Rₓ) (S := Sₓ)).2 this
end GlobalTheory
