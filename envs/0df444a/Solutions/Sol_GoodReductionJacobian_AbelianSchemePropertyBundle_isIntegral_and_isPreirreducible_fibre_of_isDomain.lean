-- Prove2me | solution 1 for GoodReductionJacobian.AbelianSchemePropertyBundle.isIntegral_and_isPreirreducible_fibre_of_isDomain
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/d2dc4793-5edb-54fa-bf42-ca09eb0c0f10

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_PolarisedAbelianScheme
import Definitions.Def_AlgebraicGeometry_PolarisationRosati
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor

import Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_geometricallyIntegral_of_commRing
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_AbelianSchemePropertyBundle_isIntegral_and_isPreirreducible_fibre_of_isDomain
p2m_attr_erase "simp" "GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChange_inv GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.baseChange_mul GoodReductionJacobian.RelativeGroupLaw.baseChange_one NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst NeronSpecialFibreInfra.neronEndRestrictEquiv_apply NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd NeronSpecialFibreInfra.neronEndExtension_genericFibreRestrict NeronSpecialFibreInfra.specClosedFibreInclusion_eq NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd_assoc NeronSpecialFibreInfra.genericFibreRestrict_neronEndExtension NeronSpecialFibreInfra.homOverId_coe NeronSpecialFibreInfra.homOverComp_coe NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd_assoc GoodReductionJacobian.RelativeGroupLaw.fibre_inv GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.fibre_mul GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.fibre_one GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe AlgebraicGeometry.schemeFibreEndo_snd AlgebraicGeometry.schemeFibreEndo_fst RegularLocalRingQuotientAscent.dualNumberFst_apply"

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation"

theorem solution
    {R : Type} [CommRing R] [IsNoetherianRing R] [IsDomain R] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of R)}
    (L : RelativeGroupLaw R f) (hA : AbelianSchemePropertyBundle R f) :
    (Smooth f ∧ QuasiCompact f ∧ IsIntegral A ∧
      ∀ s : ↥(Spec (CommRingCat.of R)), IsPreirreducible (f.base ⁻¹' {s} : Set ↥A)) ∧
    (Smooth (pullback.fst f f ≫ f) ∧ QuasiCompact (pullback.fst f f ≫ f) ∧ IsIntegral (pullback f f) ∧
      ∀ s : ↥(Spec (CommRingCat.of R)), IsPreirreducible ((pullback.fst f f ≫ f).base ⁻¹' {s} : Set ↥(pullback f f))) := by
  haveI : Smooth f := hA.smooth
  haveI : IsProper f := hA.proper
  haveI : GeometricallyIntegral f := hA.geometricallyIntegral_of_commRing
  haveI : IsIntegral A := GeometricallyIntegral.isIntegral_of_isLocallyNoetherian f
  haveI : IsLocallyNoetherian A := LocallyOfFiniteType.isLocallyNoetherian f
  haveI : IsIntegral (pullback f f) := inferInstance
  have hirrA : ∀ s : ↥(Spec (CommRingCat.of R)), IsIrreducible (f.base ⁻¹' {s} : Set ↥A) :=
    fun s => f.isIrreducible_preimage f.isOpenMap isIrreducible_singleton
  have hirr : ∀ s : ↥(Spec (CommRingCat.of R)),
      IsPreirreducible ((pullback.fst f f ≫ f).base ⁻¹' {s} : Set ↥(pullback f f)) := by
    intro s
    have h := (pullback.fst f f).isIrreducible_preimage (pullback.fst f f).isOpenMap (hirrA s)
    exact h.isPreirreducible
  exact ⟨⟨inferInstance, inferInstance, inferInstance, fun s => (hirrA s).isPreirreducible⟩,
    ⟨inferInstance, inferInstance, inferInstance, hirr⟩⟩

end S_GoodReductionJacobian_AbelianSchemePropertyBundle_isIntegral_and_isPreirreducible_fibre_of_isDomain
end P2MW
export P2MW.S_GoodReductionJacobian_AbelianSchemePropertyBundle_isIntegral_and_isPreirreducible_fibre_of_isDomain (solution)
