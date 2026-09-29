-- Prove2me | solution 1 for GoodReductionJacobian.AbelianSchemePropertyBundle.exists_isInvertible_pullback_iso_of_isDiscreteValuationRing
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/8fdaa323-28e4-5b17-9498-fb43f040be86

import Mathlib
import Definitions.Def_AlgebraicGeometry_PolarisedAbelianScheme
import Definitions.Def_AlgebraicGeometry_PolarisationRosati
import Theorems.Thm_AlgebraicGeometry_Smooth_isRegularLocalRing_stalk_of_isDiscreteValuationRing
import Theorems.Thm_AlgebraicGeometry_Scheme_isRegularRing_stalk_of_forall_isRegularLocalRing_stalk
import Theorems.Thm_IsRegularRing_uniqueFactorizationMonoid_of_isLocalRing
import Theorems.Thm_IsRegularLocalRing_isDomain
import Theorems.Thm_AlgebraicGeometry_isIntegral_of_isLocallyNoetherian_of_connectedSpace_of_forall_isDomain_stalk
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_isInvertible_pullback_iso_of_isOpenImmersion_of_uniqueFactorizationMonoid_stalk
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_isInvertible_pullback_iso_of_isDiscreteValuationRing
p2m_attr_erase "instance" "instTopologicallyFGOfFiniteType SheafOfModules.isIso_ihomModelToIhom PresheafOfModules.PullbackMonoidal.pullback_monoidal PresheafOfModules.PullbackMonoidal.isIso_δ PresheafOfModules.pushforward_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_η PresheafOfModules.free_monoidal PresheafOfModules.restrictScalars_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_δ_gS PresheafOfModules.pullback_oplaxMonoidal PresheafOfModules.PullbackMonoidal.instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb PresheafOfModules.pullback_monoidal' AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap AlgebraicGeometry.Scheme.Modules.pullback_monoidal AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization' AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap AlgebraicGeometry.Scheme.Modules.instLiftingPresheafOfModulesSheafifyPresheafWOpensCarrierCarrierCommRingCatGrothendieckTopologyObjFunctorOppositeIsSheafSheafCompPullback₀Pullback TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module"
p2m_attr_erase "instance" "CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free AlgebraicGeometry.Scheme.Modules.GlueOfCocycle.instSMulCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensSubtypeForallMinMemAddSubgroupFamilies AlgebraicGeometry.Scheme.Modules.GlueOfCocycle.instModulePreGlue AlgebraicGeometry.Scheme.Modules.GlueOfCocycle.instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensSubtypeForallMinMemAddSubgroupFamilies"
p2m_attr_erase "simp" "RegularLocalRingQuotientAscent.dualNumberFst_apply AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom SheafOfModules.ihomSectionsEquivFamily_unit AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply SheafOfModules.ihomEval_unit_app AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply SheafOfModules.unit_ihomSectionsEquivFamily AlgebraicGeometry.Scheme.Modules.familyOfHom_app AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply PresheafOfModules.freeεIso_hom_app PresheafOfModules.freeμIso_hom_app AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec"
p2m_attr_erase "simp" "CoherentBaseChange.TwoTermComplex.mk.injEq AlgebraicGeometry.Scheme.Modules.glueComponent_glueMk AlgebraicGeometry.Scheme.Modules.UnitCocycle.mk.injEq AlgebraicGeometry.Scheme.Modules.UnitCocycle.mk.sizeOf_spec"

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation"

theorem solution
    (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (KK : Type) [Field KK] [Algebra R KK] [IsFractionRing R KK]
    {A AK : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of R)) (hA : AbelianSchemePropertyBundle R f)
    (fK : AK ⟶ Spec (CommRingCat.of KK)) (gK : AK ⟶ A) (hgK : IsPullback gK fK f (Spec.map (CommRingCat.ofHom (algebraMap R KK))))
    (𝓛K : AK.Modules) (h𝓛K : Scheme.Modules.IsInvertible 𝓛K) :
    ∃ 𝓛 : A.Modules, Scheme.Modules.IsInvertible 𝓛 ∧ Nonempty ((Scheme.Modules.pullback gK).obj 𝓛 ≅ 𝓛K) := by
  haveI : Smooth f := hA.smooth
  haveI : IsProper f := hA.proper

  have hreg : ∀ x : A, IsRegularLocalRing (A.presheaf.stalk x) := fun x =>
    AlgebraicGeometry.Smooth.isRegularLocalRing_stalk_of_isDiscreteValuationRing R f x
  have hdom : ∀ x : A, IsDomain (A.presheaf.stalk x) := fun x => by
    haveI := hreg x; exact IsRegularLocalRing.isDomain _

  haveI : IsLocallyNoetherian A := LocallyOfFiniteType.isLocallyNoetherian f
  haveI : CompactSpace A := QuasiCompact.compactSpace_of_compactSpace f
  haveI : IsNoetherian A := ⟨⟩

  haveI : ConnectedSpace A := by
    rw [connectedSpace_iff_univ]
    have hfib : ∀ s : ↥(Spec (CommRingCat.of R)), _root_.IsConnected ((⇑f) ⁻¹' {s}) := fun s => hA.connectedFibres s
    have hsurj : Function.Surjective (⇑f) := fun s => by
      obtain ⟨a, ha⟩ := (hfib s).nonempty
      exact ⟨a, ha⟩
    have hq : Topology.IsQuotientMap (⇑f) := (f.isClosedMap).isQuotientMap f.continuous hsurj
    have h := Topology.IsCoinducing.isConnected_preimage_of_isClosed hfib hq.isCoinducing isClosed_univ isConnected_univ
    rwa [Set.preimage_univ] at h
  haveI : IsIntegral A :=
    AlgebraicGeometry.isIntegral_of_isLocallyNoetherian_of_connectedSpace_of_forall_isDomain_stalk A hdom
  have hfact : ∀ x : A, UniqueFactorizationMonoid (A.presheaf.stalk x) := fun x => by
    haveI := AlgebraicGeometry.Scheme.isRegularRing_stalk_of_forall_isRegularLocalRing_stalk hreg x
    exact IsRegularRing.uniqueFactorizationMonoid_of_isLocalRing _

  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  haveI : IsLocalization.Away ϖ KK := by
    refine (IsLocalization.iff_of_le_of_exists_dvd (M := Submonoid.powers ϖ) (S := KK) (nonZeroDivisors R) ?_ ?_).mpr
      (show IsLocalization (nonZeroDivisors R) KK from inferInstance)
    · exact Submonoid.powers_le.mpr (mem_nonZeroDivisors_of_ne_zero hϖ.ne_zero)
    · intro n hn
      have hn0 : n ≠ 0 := nonZeroDivisors.ne_zero hn
      obtain ⟨m, u, hm⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hn0 hϖ
      exact ⟨ϖ ^ m, ⟨m, rfl⟩, ⟨↑u⁻¹, by rw [hm, mul_comm (↑u : R), mul_assoc, Units.mul_inv, mul_one]⟩⟩
  have hopen : IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap R KK))) :=
    IsOpenImmersion.of_isLocalization ϖ
  haveI : IsOpenImmersion gK := MorphismProperty.of_isPullback hgK.flip hopen
  exact Scheme.Modules.IsInvertible.exists_isInvertible_pullback_iso_of_isOpenImmersion_of_uniqueFactorizationMonoid_stalk
    hfact gK 𝓛K h𝓛K

end S_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_isInvertible_pullback_iso_of_isDiscreteValuationRing
end P2MW
export P2MW.S_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_isInvertible_pullback_iso_of_isDiscreteValuationRing (solution)
