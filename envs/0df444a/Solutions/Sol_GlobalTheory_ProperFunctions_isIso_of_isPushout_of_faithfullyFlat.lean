-- Prove2me | solution 1 for GlobalTheory.ProperFunctions.isIso_of_isPushout_of_faithfullyFlat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T19:38:49.635857+00:00
-- url     : https://prove2.me/submissions/e9c55f32-7fd6-46d9-96dc-e38d6f23625b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsIsoAppTopOfIsPullbackOfSurjective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits AlgebraicGeometry TensorProduct Opposite
universe u
open GlobalTheory
open GlobalTheory.ProperFunctions
namespace GlobalTheory.ProperFunctions
theorem _root_.solution {R A K P : CommRingCat.{u}} {φ : R ⟶ A} {ψ : R ⟶ K}
    {inl : A ⟶ P} {inr : K ⟶ P} (H : IsPushout φ ψ inl inr) (hψ : ψ.hom.FaithfullyFlat)
    [IsIso inr] : IsIso φ := by
  have hb : Function.Bijective inr.hom := ConcreteCategory.bijective_of_isIso inr
  algebraize [φ.hom, ψ.hom, inl.hom, inr.hom, (φ ≫ inl).hom]
  have : IsScalarTower R A P := .of_algebraMap_eq' rfl
  have : IsScalarTower R K P := .of_algebraMap_eq' congr($(H.w).hom)
  have : Algebra.IsPushout R A K P := CommRingCat.isPushout_iff_isPushout.mp H
  have := RingHom.FaithfullyFlat.codescendsAlong_bijective (R := R) (S := A) (R' := K) (S' := P)
    hψ hb
  exact (ConcreteCategory.isIso_iff_bijective φ).mpr this
end GlobalTheory.ProperFunctions
