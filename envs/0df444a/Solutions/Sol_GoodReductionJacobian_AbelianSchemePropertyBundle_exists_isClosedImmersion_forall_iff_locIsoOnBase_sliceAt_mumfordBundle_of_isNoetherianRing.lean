-- Prove2me | solution 1 for GoodReductionJacobian.AbelianSchemePropertyBundle.exists_isClosedImmersion_forall_iff_locIsoOnBase_sliceAt_mumfordBundle_of_isNoetherianRing
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/4c0dd3f0-679c-594f-b9b8-22ca7a731681

import Mathlib
import Definitions.Def_AlgebraicGeometry_PolarisationRosati
import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidalV2
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawTranslate
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_isClosedImmersion_forall_iff_isInStabilizer
import Theorems.Thm_AlgebraicGeometry_bijective_app_of_isProper_of_flat_of_geometricallyReduced_of_geometricallyConnected
import Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_geometricallyIntegral
import Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_of_isPullback
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_pullback_dual_monoidalV2
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_dual_monoidalV2
import Theorems.Thm_AlgebraicGeometry_Polarisation_LocIsoOnBase_equivalence
import Theorems.Thm_AlgebraicGeometry_Polarisation_LocIsoOnBase_tensor
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_isClosedImmersion_forall_iff_locIsoOnBase_sliceAt_mumfordBundle_of_isNoetherianRing
p2m_attr_erase "instance" "TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free AlgebraicGeometry.OModulePresheaf.isScalarTower AlgebraicGeometry.Scheme.OrderedAffineCover.instLinearOrder AlgebraicGeometry.OModulePresheaf.module AlgebraicGeometry.Scheme.OrderedAffineCover.instFintype AlgebraicGeometry.Scheme.OrderedAffineCover.instFintypeIdx AlgebraicGeometry.OModulePresheaf.addCommGroup AlgebraicGeometry.Scheme.OrderedAffineCover.instDecidableEqIdx AlgebraicGeometry.OModulePresheaf.moduleSections AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ"
p2m_attr_erase "instance" "AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule AlgebraicGeometry.SubalgebraStages.compactSpace_pullback AlgebraicGeometry.SubalgebraStages.quasiSeparatedSpace_pullback AlgebraicGeometry.SubalgebraStages.compactSpace_obj AlgebraicGeometry.SubalgebraStages.quasiSeparatedSpace_obj AlgebraicGeometry.SubalgebraStages.quasiCompact_snd AlgebraicGeometry.SubalgebraStages.isAffineHom_leg AlgebraicGeometry.SubalgebraStages.isAffineHom_trans"
p2m_attr_erase "instance" "AlgebraicGeometry.SubalgebraStages.isAffineHom_diagram_map AlgebraicGeometry.SubalgebraStages.quasiSeparated_snd AlgebraicGeometry.SubalgebraStages.isCofiltered_op IsDirectLimit.Module.instDirectLimitCoeLinearMapIdOfOfNonempty AdicCompletion.instIsLocalRingMaximalIdeal"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.mk.injEq AlgebraicGeometry.OModulePresheaf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.mk.injEq AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ AlgebraicGeometry.SubalgebraStages.specCone_π_app AlgebraicGeometry.SubalgebraStages.specLeg_specHom AlgebraicGeometry.SubalgebraStages.specLeg_specTrans AlgebraicGeometry.SubalgebraStages.cone_pt AlgebraicGeometry.SubalgebraStages.trans_fst AlgebraicGeometry.SubalgebraStages.diagram_obj"
p2m_attr_erase "simp" "AlgebraicGeometry.SubalgebraStages.leg_snd AlgebraicGeometry.SubalgebraStages.diagram_map AlgebraicGeometry.SubalgebraStages.specTrans_refl AlgebraicGeometry.SubalgebraStages.trans_snd AlgebraicGeometry.SubalgebraStages.specTrans_specHom AlgebraicGeometry.SubalgebraStages.specCone_pt AlgebraicGeometry.SubalgebraStages.cone_π_app AlgebraicGeometry.SubalgebraStages.specDiagram_map AlgebraicGeometry.SubalgebraStages.specDiagram_obj AlgebraicGeometry.SubalgebraStages.leg_fst AlgebraicGeometry.SubalgebraStages.leg_trans IsDirectLimit.Module.linearEquiv_symm_apply IsDirectLimit.linearEquiv_symm_apply IsDirectLimit.lift_of IsDirectLimit.Module.linearEquiv_apply IsDirectLimit.Module.lift_of IsDirectLimit.Equiv_apply RegularLocalRingQuotientAscent.dualNumberFst_apply GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChange_inv GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.baseChange_mul GoodReductionJacobian.RelativeGroupLaw.baseChange_one NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst NeronSpecialFibreInfra.neronEndRestrictEquiv_apply NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd NeronSpecialFibreInfra.neronEndExtension_genericFibreRestrict NeronSpecialFibreInfra.specClosedFibreInclusion_eq"
p2m_attr_erase "simp" "NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd_assoc NeronSpecialFibreInfra.genericFibreRestrict_neronEndExtension NeronSpecialFibreInfra.homOverId_coe NeronSpecialFibreInfra.homOverComp_coe NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd_assoc GoodReductionJacobian.RelativeGroupLaw.fibre_inv GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.fibre_mul GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.fibre_one GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe AlgebraicGeometry.schemeFibreEndo_snd AlgebraicGeometry.schemeFibreEndo_fst"

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry NeronModelInfra~schemeHomOverComp~schemeHomOverComp_coe GoodReductionJacobian P2MW.S_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_isClosedImmersion_forall_iff_locIsoOnBase_sliceAt_mumfordBundle_of_isNoetherianRing.GoodReductionJacobian AlgebraicGeometry.Polarisation"

universe u

noncomputable section

namespace GoodReductionJacobian
p2m_export "GoodReductionJacobian" "AbelianSchemePropertyBundle schemeHomOverComp schemeHomOverComp_coe RelativeGroupLaw RelativeGroupLaw.fstPoint RelativeGroupLaw.sndPoint RelativeGroupLaw.mulRight RelativeGroupLaw.exists_isClosedImmersion_forall_iff_isInStabilizer AbelianSchemePropertyBundle.geometricallyIntegral"
namespace KRepNoethAux
p2m_open "GoodReductionJacobian"

variable {S : Type u} [CommRing S] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of S)}

theorem mul_val_congr (L : RelativeGroupLaw S f) {T : Scheme.{u}} {t t' : T ⟶ Spec (CommRingCat.of S)} (h : t = t')
    (P Q : SchemeHomOver t f) (P' Q' : SchemeHomOver t' f) (hP : P.1 = P'.1) (hQ : Q.1 = Q'.1) :
    (L.mul t P Q).1 = (L.mul t' P' Q').1 := by
  subst h
  obtain ⟨P, hP0⟩ := P; obtain ⟨Q, hQ0⟩ := Q; obtain ⟨P', hP1⟩ := P'; obtain ⟨Q', hQ1⟩ := Q'
  simp only at hP hQ
  subst hP; subst hQ
  rfl

theorem locIsoOnBase_of_iso {R : Type u} [CommRing R] {X : Scheme.{u}} (g : X ⟶ Spec (CommRingCat.of R))
    {M M' : X.Modules} (e : M ≅ M') : LocIsoOnBase g M M' :=
  fun _ => ⟨⊤, trivial, ⟨(Scheme.Modules.pullback (g ⁻¹ᵁ ⊤).ι).mapIso e⟩⟩

theorem locIsoOnBase_pullback_of_isInvertible_base {R : Type u} [CommRing R] {X : Scheme.{u}}
    (g : X ⟶ Spec (CommRingCat.of R)) {N : (Spec (CommRingCat.of R)).Modules} (hN : Scheme.Modules.IsInvertible N) :
    LocIsoOnBase g ((Scheme.Modules.pullback g).obj N) (𝟙_ _) := by
  intro s
  obtain ⟨U, hs, ⟨e⟩⟩ := hN.exists_trivialization s
  refine ⟨U, hs, ⟨?_⟩⟩
  refine (Scheme.Modules.pullbackComp (g ⁻¹ᵁ U).ι g).app N ≪≫
    (Scheme.Modules.pullbackCongr (morphismRestrict_ι g U).symm).app N ≪≫
    ((Scheme.Modules.pullbackComp (g ∣_ U) U.ι).app N).symm ≪≫
    (Scheme.Modules.pullback (g ∣_ U)).mapIso e ≪≫
    Scheme.Modules.pullbackTensorUnitObjIso (g ∣_ U) ≪≫
    (Scheme.Modules.pullbackTensorUnitObjIso (g ⁻¹ᵁ U).ι).symm

theorem nonempty_tensor_dual_iso_unit {X : Scheme.{u}} {Q : X.Modules} (hQ : Scheme.Modules.IsInvertible Q) :
    Nonempty (Q ⊗ Scheme.Modules.dual Q ≅ 𝟙_ _) :=
  hQ.dual_monoidalV2.2

theorem nonempty_dual_tensor_iso_unit {X : Scheme.{u}} {Q : X.Modules} (hQ : Scheme.Modules.IsInvertible Q) :
    Nonempty (Scheme.Modules.dual Q ⊗ Q ≅ 𝟙_ _) := by
  obtain ⟨-, ⟨d⟩⟩ := hQ.dual_monoidalV2
  exact ⟨β_ _ _ ≪≫ d⟩

theorem nonempty_dual_unit_iso (X : Scheme.{u}) : Nonempty (Scheme.Modules.dual (𝟙_ X.Modules) ≅ 𝟙_ _) := by
  obtain ⟨-, ⟨d⟩⟩ := (Scheme.Modules.isInvertible_unit X).dual_monoidalV2
  exact ⟨(λ_ _).symm ≪≫ d⟩

def swapMiddle {C : Type*} [Category C] [MonoidalCategory C] [BraidedCategory C] (W X Y Z : C) :
    (W ⊗ X) ⊗ (Y ⊗ Z) ≅ (W ⊗ Y) ⊗ (X ⊗ Z) :=
  α_ W X (Y ⊗ Z) ≪≫ whiskerLeftIso W ((α_ X Y Z).symm ≪≫ whiskerRightIso (β_ X Y) Z ≪≫ α_ Y X Z) ≪≫
    (α_ W Y (X ⊗ Z)).symm

theorem locIsoOnBase_of_tensor_dual_dual_unit {R : Type u} [CommRing R] {Z : Scheme.{u}}
    (g : Z ⟶ Spec (CommRingCat.of R)) {M X Y : Z.Modules}
    (hX : Scheme.Modules.IsInvertible X) (hY : Scheme.Modules.IsInvertible Y)
    (h : LocIsoOnBase g (M ⊗ (Scheme.Modules.dual X ⊗ Scheme.Modules.dual Y)) (𝟙_ _)) :
    LocIsoOnBase g M (X ⊗ Y) := by
  obtain ⟨dX⟩ := nonempty_dual_tensor_iso_unit hX
  obtain ⟨dY⟩ := nonempty_dual_tensor_iso_unit hY
  have h1 : LocIsoOnBase g ((M ⊗ (Scheme.Modules.dual X ⊗ Scheme.Modules.dual Y)) ⊗ (X ⊗ Y)) (X ⊗ Y) :=
    (LocIsoOnBase.equivalence _).trans (LocIsoOnBase.tensor h ((LocIsoOnBase.equivalence _).refl (X ⊗ Y)))
      (locIsoOnBase_of_iso g (λ_ _))
  let I : (M ⊗ (Scheme.Modules.dual X ⊗ Scheme.Modules.dual Y)) ⊗ (X ⊗ Y) ≅ M :=
    α_ _ _ _ ≪≫ whiskerLeftIso M (swapMiddle _ _ _ _ ≪≫ (dX ⊗ᵢ dY) ≪≫ λ_ _) ≪≫ ρ_ M
  exact (LocIsoOnBase.equivalence _).trans (locIsoOnBase_of_iso g I.symm) h1

theorem locIsoOnBase_tensor_dual_dual_unit_of {R : Type u} [CommRing R] {Z : Scheme.{u}}
    (g : Z ⟶ Spec (CommRingCat.of R)) {M X Y : Z.Modules}
    (hX : Scheme.Modules.IsInvertible X) (hY : Scheme.Modules.IsInvertible Y)
    (h : LocIsoOnBase g M (X ⊗ Y)) :
    LocIsoOnBase g (M ⊗ (Scheme.Modules.dual X ⊗ Scheme.Modules.dual Y)) (𝟙_ _) := by
  obtain ⟨dX⟩ := nonempty_tensor_dual_iso_unit hX
  obtain ⟨dY⟩ := nonempty_tensor_dual_iso_unit hY
  have h1 : LocIsoOnBase g (M ⊗ (Scheme.Modules.dual X ⊗ Scheme.Modules.dual Y))
      ((X ⊗ Y) ⊗ (Scheme.Modules.dual X ⊗ Scheme.Modules.dual Y)) :=
    LocIsoOnBase.tensor h ((LocIsoOnBase.equivalence _).refl _)
  let I : (X ⊗ Y) ⊗ (Scheme.Modules.dual X ⊗ Scheme.Modules.dual Y) ≅ 𝟙_ _ :=
    swapMiddle _ _ _ _ ≪≫ (dX ⊗ᵢ dY) ≪≫ λ_ _
  exact (LocIsoOnBase.equivalence _).trans h1 (locIsoOnBase_of_iso g I)

section Geometry

variable (hA : AbelianSchemePropertyBundle S f)
include hA

theorem isProper : IsProper f := hA.proper

theorem flat : Flat f := by
  haveI := hA.smooth
  infer_instance

private theorem _root_.GoodReductionJacobian.KRepNoethAux.geometricallyIntegral : GeometricallyIntegral f := by
  refine ⟨fun K _ y Z fst snd h => ?_⟩
  have hZ : AbelianSchemePropertyBundle K snd := hA.of_isPullback h
  haveI : GeometricallyIntegral snd := hZ.geometricallyIntegral
  exact GeometricallyIntegral.isIntegral_of_subsingleton snd

p2m_export "GoodReductionJacobian.KRepNoethAux" "geometricallyIntegral"
theorem geometricallyConnected : GeometricallyConnected f := by
  refine ⟨fun K _ y Z fst snd h => ?_⟩
  haveI : IsIntegral Z := (geometricallyIntegral hA).1 y fst snd h
  infer_instance

theorem geometricallyReduced : GeometricallyReduced f := by
  haveI := geometricallyIntegral hA
  infer_instance

theorem bijective_appTop_baseChange (B : Type u) [CommRing B] [Algebra S B] :
    Function.Bijective (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S B)))).appTop := by
  haveI := isProper hA
  haveI := flat hA
  haveI := hA.smooth
  haveI := geometricallyConnected hA
  haveI := geometricallyReduced hA
  exact AlgebraicGeometry.bijective_app_of_isProper_of_flat_of_geometricallyReduced_of_geometricallyConnected
    (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S B)))) ⊤

end Geometry

section Slice

variable (L : RelativeGroupLaw S f) {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of S)} (x : SchemeHomOver t f)

theorem sliceAt_fst : sliceAt f x ≫ pullback.fst f f = pullback.fst f t := pullback.lift_fst _ _ _

theorem sliceAt_snd : sliceAt f x ≫ pullback.snd f f = pullback.snd f t ≫ x.1 := pullback.lift_snd _ _ _

theorem sliceAt_addMor : sliceAt f x ≫ addMor f L = L.mulRight t x := by
  have hψ : sliceAt f x ≫ (pullback.fst f f ≫ f) = pullback.snd f t ≫ t := by
    rw [← Category.assoc, sliceAt_fst, pullback.condition]
  have h := congrArg Subtype.val
    (L.mul_natural (pullback.fst f f ≫ f) (pullback.snd f t ≫ t) (sliceAt f x) hψ
      ⟨pullback.fst f f, rfl⟩ ⟨pullback.snd f f, pullback.condition.symm⟩)
  simp only [schemeHomOverComp_coe] at h
  change sliceAt f x ≫ addMor f L = _ at h
  rw [h]
  unfold RelativeGroupLaw.mulRight
  refine mul_val_congr L rfl _ _ _ _ ?_ ?_
  · simp [schemeHomOverComp, sliceAt_fst, RelativeGroupLaw.fstPoint]
  · simp [schemeHomOverComp, sliceAt_snd, RelativeGroupLaw.sndPoint]

theorem nonempty_sliceAt_mumfordBundle_iso (𝓛 : A.Modules) :
    Nonempty ((Scheme.Modules.pullback (sliceAt f x)).obj (mumfordBundle f L 𝓛) ≅
      (Scheme.Modules.pullback (L.mulRight t x)).obj 𝓛 ⊗
        ((Scheme.Modules.pullback (pullback.fst f t)).obj (Scheme.Modules.dual 𝓛) ⊗
          (Scheme.Modules.pullback (pullback.snd f t ≫ x.1)).obj (Scheme.Modules.dual 𝓛))) := by
  refine ⟨?_⟩
  refine Scheme.Modules.pullbackTensorObjIso (sliceAt f x) _ _ ≪≫ ?_
  refine (?_ ⊗ᵢ (Scheme.Modules.pullbackTensorObjIso (sliceAt f x) _ _ ≪≫ (?_ ⊗ᵢ ?_)))
  · exact (Scheme.Modules.pullbackComp (sliceAt f x) (addMor f L)).app 𝓛 ≪≫
      (Scheme.Modules.pullbackCongr (sliceAt_addMor L x)).app 𝓛
  · exact (Scheme.Modules.pullbackComp (sliceAt f x) (pullback.fst f f)).app _ ≪≫
      (Scheme.Modules.pullbackCongr (sliceAt_fst x)).app _
  · exact (Scheme.Modules.pullbackComp (sliceAt f x) (pullback.snd f f)).app _ ≪≫
      (Scheme.Modules.pullbackCongr (sliceAt_snd x)).app _

end Slice

section Dictionary

variable (L : RelativeGroupLaw S f) {𝓛 : A.Modules} (hinv : Scheme.Modules.IsInvertible 𝓛)
  {R : Type u} [CommRing R] {t : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of S)} (x : SchemeHomOver t f)
include hinv

theorem isInStabilizer_iff_locIsoOnBase :
    L.IsInStabilizer 𝓛 t x ↔
      LocIsoOnBase (pullback.snd f t)
        ((Scheme.Modules.pullback (sliceAt f x)).obj (mumfordBundle f L 𝓛)) (𝟙_ ((pullback f t).Modules)) := by

  set g : pullback f t ⟶ Spec (CommRingCat.of R) := pullback.snd f t with hg
  set P : (pullback f t).Modules := (Scheme.Modules.pullback (L.mulRight t x)).obj 𝓛 with hP
  set Q : (pullback f t).Modules := (Scheme.Modules.pullback (pullback.fst f t)).obj 𝓛 with hQ
  set Q' : (pullback f t).Modules := (Scheme.Modules.pullback (pullback.fst f t)).obj (Scheme.Modules.dual 𝓛) with hQ'
  set Y' : (pullback f t).Modules :=
    (Scheme.Modules.pullback (pullback.snd f t ≫ x.1)).obj (Scheme.Modules.dual 𝓛) with hY'
  have hQinv : Scheme.Modules.IsInvertible Q := hinv.pullback _

  obtain ⟨eQ'⟩ : Nonempty (Q' ≅ Scheme.Modules.dual Q) := hinv.pullback_dual_monoidalV2 (pullback.fst f t)

  have hY'triv : LocIsoOnBase g Y' (𝟙_ _) := by
    have hb : Scheme.Modules.IsInvertible ((Scheme.Modules.pullback x.1).obj (Scheme.Modules.dual 𝓛)) :=
      hinv.dual_monoidalV2.1.pullback _
    have h0 := locIsoOnBase_pullback_of_isInvertible_base g hb
    exact (LocIsoOnBase.equivalence _).trans
      (locIsoOnBase_of_iso g ((Scheme.Modules.pullbackComp (pullback.snd f t) x.1).app _).symm) h0

  obtain ⟨eΛ⟩ := nonempty_sliceAt_mumfordBundle_iso L x 𝓛

  have hdef : L.IsInStabilizer 𝓛 t x ↔ LocIsoOnBase g P Q := Iff.rfl
  rw [hdef]
  constructor
  ·
    intro h
    obtain ⟨dQ⟩ := nonempty_tensor_dual_iso_unit hQinv
    have h1 : LocIsoOnBase g (Q' ⊗ Y') (Scheme.Modules.dual Q ⊗ 𝟙_ _) :=
      LocIsoOnBase.tensor (locIsoOnBase_of_iso g eQ') hY'triv
    have h2 : LocIsoOnBase g (P ⊗ (Q' ⊗ Y')) (Q ⊗ (Scheme.Modules.dual Q ⊗ 𝟙_ _)) := LocIsoOnBase.tensor h h1
    have I : Q ⊗ (Scheme.Modules.dual Q ⊗ 𝟙_ _) ≅ 𝟙_ _ := (α_ _ _ _).symm ≪≫ (dQ ⊗ᵢ Iso.refl _) ≪≫ λ_ _
    exact (LocIsoOnBase.equivalence _).trans (locIsoOnBase_of_iso g eΛ)
      ((LocIsoOnBase.equivalence _).trans h2 (locIsoOnBase_of_iso g I))
  ·
    intro h
    obtain ⟨du⟩ := nonempty_dual_unit_iso (pullback f t)
    have h1 : LocIsoOnBase g (Scheme.Modules.dual Q ⊗ Scheme.Modules.dual (𝟙_ _)) (Q' ⊗ Y') :=
      LocIsoOnBase.tensor (locIsoOnBase_of_iso g eQ'.symm)
        ((LocIsoOnBase.equivalence _).trans (locIsoOnBase_of_iso g du) ((LocIsoOnBase.equivalence _).symm hY'triv))
    have h2 : LocIsoOnBase g (P ⊗ (Scheme.Modules.dual Q ⊗ Scheme.Modules.dual (𝟙_ _))) (P ⊗ (Q' ⊗ Y')) :=
      LocIsoOnBase.tensor ((LocIsoOnBase.equivalence _).refl P) h1
    have h3 : LocIsoOnBase g (P ⊗ (Scheme.Modules.dual Q ⊗ Scheme.Modules.dual (𝟙_ _))) (𝟙_ _) :=
      (LocIsoOnBase.equivalence _).trans h2
        ((LocIsoOnBase.equivalence _).trans ((LocIsoOnBase.equivalence _).symm (locIsoOnBase_of_iso g eΛ)) h)
    have h4 : LocIsoOnBase g P (Q ⊗ 𝟙_ _) :=
      locIsoOnBase_of_tensor_dual_dual_unit g hQinv (Scheme.Modules.isInvertible_unit _) h3
    exact (LocIsoOnBase.equivalence _).trans h4 (locIsoOnBase_of_iso g (ρ_ Q))

end Dictionary

end GoodReductionJacobian.KRepNoethAux

end

open GoodReductionJacobian.KRepNoethAux in
theorem solution
    {S : Type u} [CommRing S] [IsNoetherianRing S] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of S)}
    (hA : AbelianSchemePropertyBundle S f) (L : RelativeGroupLaw S f)
    (𝓛 : A.Modules) (hinv : Scheme.Modules.IsInvertible 𝓛) :
    ∃ (K : Scheme.{u}) (ι : K ⟶ A), IsClosedImmersion ι ∧
      ∀ (R : Type u) [CommRing R] (t : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of S)) (x : SchemeHomOver t f),
        (∃ k : Spec (CommRingCat.of R) ⟶ K, k ≫ ι = x.1) ↔
          LocIsoOnBase (pullback.snd f t)
            ((Scheme.Modules.pullback (sliceAt f x)).obj (mumfordBundle f L 𝓛)) (𝟙_ ((pullback f t).Modules)) := by
  haveI : IsProper f := isProper hA
  haveI : Flat f := flat hA
  haveI : GeometricallyIntegral f := geometricallyIntegral hA
  have hH0 : ∀ (B : Type u) [CommRing B] [Algebra S B],
      Function.Bijective (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S B)))).appTop :=
    fun B _ _ => bijective_appTop_baseChange hA B
  obtain ⟨K, ι, hcl, hK⟩ := L.exists_isClosedImmersion_forall_iff_isInStabilizer hH0 𝓛 hinv
  refine ⟨K, ι, hcl, fun R _ t x => (hK t x).trans ?_⟩
  exact isInStabilizer_iff_locIsoOnBase L hinv x

end S_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_isClosedImmersion_forall_iff_locIsoOnBase_sliceAt_mumfordBundle_of_isNoetherianRing
end P2MW
export P2MW.S_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_isClosedImmersion_forall_iff_locIsoOnBase_sliceAt_mumfordBundle_of_isNoetherianRing (solution)
