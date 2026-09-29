-- Prove2me | solution 1 for GoodReductionJacobian.AbelianSchemePropertyBundle.exists_linearMap_primitives_HSucc_unit_injective_of_torsion_points_equiv
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/98386152-7d27-5093-b431-e78a2351d0f3

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import Definitions.Def_AlgebraicGeometry_OModulePresheafEulerChar
import Definitions.Def_Dieudonne_ModpRealization
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_action_isIso_shear_of_torsion_points_equiv
import Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_linearMap_primitives_HSucc_unit_injective_of_isIso_shear
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_linearMap_primitives_HSucc_unit_injective_of_torsion_points_equiv
p2m_attr_erase "simp" "RegularLocalRingQuotientAscent.dualNumberFst_apply"

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

theorem solution
    (K : Type u) [Field K] {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of K))
    (L : RelativeGroupLaw K f) (hc : L.IsCommutative) (hA : AbelianSchemePropertyBundle K f)
    (n : ℕ) (hfin : IsFinite (L.schemeNsmul n)) (hflat : Flat (L.schemeNsmul n))
    (hsurj : Function.Surjective (L.schemeNsmul n))
    (H : Type u) [CommRing H] [HopfAlgebra K H] [Module.Finite K H] [Coalgebra.IsCocomm K H]
    (e : ∀ (T : Type u) [CommRing T] [Algebra K T],
      WithConv (H →ₐ[K] T) ≃ L.torsionSubset (Spec.map (CommRingCat.ofHom (algebraMap K T))) n)
    (he_mul : ∀ (T : Type u) [CommRing T] [Algebra K T] (φ ψ : WithConv (H →ₐ[K] T)),
      ((e T (φ * ψ)).val : SchemeHomOver _ f) = L.mul _ (e T φ).val (e T ψ).val)
    (he_nat : ∀ (T T' : Type u) [CommRing T] [Algebra K T] [CommRing T'] [Algebra K T']
        (g' : T →ₐ[K] T') (φ : WithConv (H →ₐ[K] T)),
      ((e T' (.toConv (g'.comp φ.ofConv))).val : SchemeHomOver _ f).1 =
        Spec.map (CommRingCat.ofHom g'.toRingHom) ≫ (e T φ).val.1)
    (𝒦 : A.OrderedAffineCover) :
    ∃ θ : ↥(primitives K H) →ₗ[K] (OModulePresheaf.unit f).HSucc 𝒦 0, Function.Injective θ := by
  obtain ⟨act, hact, hpts, hsh, hiso⟩ :=
    GoodReductionJacobian.RelativeGroupLaw.exists_action_isIso_shear_of_torsion_points_equiv
      K f L hc n hfin hflat H e he_mul he_nat
  exact GoodReductionJacobian.AbelianSchemePropertyBundle.exists_linearMap_primitives_HSucc_unit_injective_of_isIso_shear
    K f L hc hA n hfin hflat hsurj H e he_mul he_nat act hact hpts hsh hiso 𝒦

end S_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_linearMap_primitives_HSucc_unit_injective_of_torsion_points_equiv
end P2MW
export P2MW.S_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_linearMap_primitives_HSucc_unit_injective_of_torsion_points_equiv (solution)
