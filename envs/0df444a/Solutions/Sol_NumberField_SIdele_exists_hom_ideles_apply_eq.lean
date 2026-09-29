-- Prove2me | solution 1 for NumberField.SIdele.exists_hom_ideles_apply_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/295179ed-47c3-511f-8db0-4514413aebf2

import Mathlib
import Definitions.Def_NumberField_SIdeleModule
import Definitions.Def_IsDedekindDomain_FiniteUnitIdelesOutside
import Definitions.Def_M4aHerbrand_IdeleClassVocab
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_SIdele_exists_hom_ideles_apply_eq

set_option autoImplicit false
open IsDedekindDomain NumberField CategoryTheory

namespace PhiRep

def toIntLinearMapOfModules {V W : Type} [AddCommGroup V] [AddCommGroup W] (instV : Module ℤ V) (instW : Module ℤ W)
    (u : V →+ W) : @LinearMap ℤ ℤ _ _ (RingHom.id ℤ) V W _ _ instV instW :=
  @LinearMap.mk ℤ ℤ _ _ (RingHom.id ℤ) V W _ _ instV instW ⟨u, u.map_add⟩ (fun c m => by
    letI := instV
    letI := instW
    exact map_intCast_smul u ℤ ℤ c m)

theorem toIntLinearMapOfModules_apply {V W : Type} [AddCommGroup V] [AddCommGroup W] (instV : Module ℤ V) (instW : Module ℤ W)
    (u : V →+ W) (m : V) : @DFunLike.coe _ _ _ (@LinearMap.instFunLike ℤ ℤ V W _ _ _ _ instV instW (RingHom.id ℤ))
      (toIntLinearMapOfModules instV instW u) m = u m := rfl

end PhiRep

theorem solution
    (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] [Algebra E K] [IsGalois E K]
    (S : Finset (HeightOneSpectrum (𝓞 E))) (D : M4aHerbrand.IdeleGaloisDescent (𝓞 K) E K)
    [MulDistribMulAction (K ≃ₐ[E] K) (AdeleRing (𝓞 K) K)ˣ]
    (hactI : ∀ (g : K ≃ₐ[E] K) (x : (AdeleRing (𝓞 K) K)ˣ), g • x = D.unitsAct g x)
    (Φ : NumberField.SIdele.obj E K S →+ Additive (AdeleRing (𝓞 K) K)ˣ)
    (hΦρ : ∀ (g : K ≃ₐ[E] K) (y : NumberField.SIdele.obj E K S),
      Φ ((NumberField.SIdele.obj E K S).ρ g y) = Additive.ofMul (D.unitsAct g (Additive.toMul (Φ y)))) :
    ∃ ΦR : NumberField.SIdele.obj E K S ⟶ Rep.ofMulDistribMulAction (K ≃ₐ[E] K) (AdeleRing (𝓞 K) K)ˣ,
      ∀ y : NumberField.SIdele.obj E K S, ΦR.hom y = Φ y := by
  refine ⟨@Rep.ofHom ℤ (K ≃ₐ[E] K) _ _ _ _ _ _ (NumberField.SIdele.obj E K S).hV2
      (Rep.ofMulDistribMulAction (K ≃ₐ[E] K) (AdeleRing (𝓞 K) K)ˣ).hV2 _ _
      (@Representation.IntertwiningMap.mk ℤ (K ≃ₐ[E] K) _ _ _ _ _ _ (NumberField.SIdele.obj E K S).hV2
        (Rep.ofMulDistribMulAction (K ≃ₐ[E] K) (AdeleRing (𝓞 K) K)ˣ).hV2 _ _
        (PhiRep.toIntLinearMapOfModules _ _ Φ) (fun g => DFunLike.ext _ _ fun y => ?_)), fun y => rfl⟩
  show Φ ((NumberField.SIdele.obj E K S).ρ g y) =
    (Rep.ofMulDistribMulAction (K ≃ₐ[E] K) (AdeleRing (𝓞 K) K)ˣ).ρ g (Φ y)
  rw [hΦρ, Rep.ofMulDistribMulAction_ρ_apply_apply, hactI]

end S_NumberField_SIdele_exists_hom_ideles_apply_eq
end P2MW
export P2MW.S_NumberField_SIdele_exists_hom_ideles_apply_eq (solution)
