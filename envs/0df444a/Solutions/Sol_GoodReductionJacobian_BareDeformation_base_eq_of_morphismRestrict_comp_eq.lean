-- Prove2me | solution 1 for GoodReductionJacobian.BareDeformation.base_eq_of_morphismRestrict_comp_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/cfe262ac-8663-54d3-b2d3-0d93f36a852e

import Definitions.Def_CerednikDrinfeld_QMFormalModuleOf
import Definitions.Def_GoodReductionJacobian_BareDeformation
import Definitions.Def_GoodReductionJacobian_IsRegluingBy
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverComap
import Definitions.Def_AlgebraicGeometry_OModulePresheafHom
import Definitions.Def_AlgebraicGeometry_SquareZeroDeformation
import Definitions.Def_AlgebraicGeometry_SquareZeroRelTangent
import Definitions.Def_AlgebraicGeometry_SmallExtensionPairTangent
import Definitions.Def_AlgebraicGeometry_TangentCoordsOfPair
import Definitions.Def_AlgebraicGeometry_SmallExtensionTangentCoords
import Definitions.Def_AlgebraicGeometry_TangentCoordsOfPairAt
import Definitions.Def_Algebra_PointDerivations
import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_BareDeformation_base_eq_of_morphismRestrict_comp_eq

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM CerednikDrinfeld.SpecialFormal IsLocalRing AlgebraicGeometry.Scheme.TwoAffineOpenCover"

open scoped Quaternion TensorProduct NumberField

theorem solution
    (B B₁ : Type) [CommRing B] [CommRing B₁] [Algebra B B₁]
    (hπ : Function.Surjective (algebraMap B B₁)) (hker : IsNilpotent (RingHom.ker (algebraMap B B₁)))
    {A₁ : Scheme.{0}} (f₁ : A₁ ⟶ Spec (CommRingCat.of B₁)) (L₁ : RelativeGroupLaw B₁ f₁)
    (D₀ : BareDeformation f₁ L₁ B) (W : D₀.A.Opens)
    (α : (↑W : Scheme.{0}) ⟶ ↑W) (hα : (D₀.g ∣_ W) ≫ α = D₀.g ∣_ W) :
    ∀ x : ↑W, α.base x = x := by

  have hsurjSpec : Surjective (Spec.map (CommRingCat.ofHom (algebraMap B B₁))) := by
    refine ⟨fun p => ?_⟩
    have hle : RingHom.ker (algebraMap B B₁) ≤ p.asIdeal := by
      intro x hx
      obtain ⟨n, hn⟩ := hker
      have hxn : x ^ n ∈ (RingHom.ker (algebraMap B B₁)) ^ n := Ideal.pow_mem_pow hx n
      rw [hn, Ideal.zero_eq_bot, Ideal.mem_bot] at hxn
      exact p.isPrime.mem_of_pow_mem n (by rw [hxn]; exact Ideal.zero_mem _)
    haveI hq : (Ideal.map (algebraMap B B₁) p.asIdeal).IsPrime := Ideal.map_isPrime_of_surjective hπ hle
    refine ⟨⟨Ideal.map (algebraMap B B₁) p.asIdeal, hq⟩, ?_⟩
    apply PrimeSpectrum.ext
    show Ideal.comap (CommRingCat.ofHom (algebraMap B B₁)).hom (Ideal.map (algebraMap B B₁) p.asIdeal) = p.asIdeal
    rw [CommRingCat.hom_ofHom, Ideal.comap_map_of_surjective _ hπ, ← RingHom.ker_eq_comap_bot]
    exact sup_eq_left.mpr hle

  haveI hsurjg : Surjective D₀.g := MorphismProperty.of_isPullback D₀.cart.flip hsurjSpec
  haveI hsurjW : Surjective (D₀.g ∣_ W) :=
    MorphismProperty.of_isPullback (isPullback_morphismRestrict D₀.g W).flip hsurjg

  intro x
  obtain ⟨y, rfl⟩ := (D₀.g ∣_ W).surjective x
  have := congrArg (fun φ => φ.base y) hα
  simpa using this

end S_GoodReductionJacobian_BareDeformation_base_eq_of_morphismRestrict_comp_eq
end P2MW
export P2MW.S_GoodReductionJacobian_BareDeformation_base_eq_of_morphismRestrict_comp_eq (solution)
