-- Prove2me | solution 1 for GoodReductionJacobian.exists_not_mem_forall_nonempty_relativeGroupLaw_geometricFibre_of_not_mem
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/b5d38ce7-5464-52e4-90ae-f30797da6d00

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_ProjSpace
import Definitions.Def_AlgebraicGeometry_FramedPolarisedAbelianScheme
import Definitions.Def_AlgebraicGeometry_ModulesPullbackLocalSection
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_fg_subalgebra_relativeGroupLaw_pullback_snd_of_locallyOfFinitePresentation
import Theorems.Thm_Subalgebra_exists_algHom_localizationAway_forall_apply_eq_coe_of_fg
import Theorems.Thm_GoodReductionJacobian_exists_relativeGroupLaw_baseChange_adicCompletion_one_eq_of_forall_nonempty_relativeGroupLaw_geometricFibre
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_one_eq_of_abelianSchemePropertyBundle_of_isPullback_of_faithfullyFlat
import Theorems.Thm_IsLocalRing_faithfullyFlat_adicCompletion_maximalIdeal
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_exists_not_mem_forall_nonempty_relativeGroupLaw_geometricFibre_of_not_mem
p2m_attr_erase "instance" "AlgebraicGeometry.SubalgebraStages.compactSpace_pullback AlgebraicGeometry.SubalgebraStages.quasiSeparatedSpace_pullback AlgebraicGeometry.SubalgebraStages.compactSpace_obj AlgebraicGeometry.SubalgebraStages.quasiSeparatedSpace_obj AlgebraicGeometry.SubalgebraStages.quasiCompact_snd AlgebraicGeometry.SubalgebraStages.isAffineHom_leg AlgebraicGeometry.SubalgebraStages.isAffineHom_trans AlgebraicGeometry.SubalgebraStages.isAffineHom_diagram_map AlgebraicGeometry.SubalgebraStages.quasiSeparated_snd AlgebraicGeometry.SubalgebraStages.isCofiltered_op AlgebraicGeometry.isClosedImmersion_adicThickeningι AlgebraicGeometry.OModulePresheaf.isScalarTower AlgebraicGeometry.Scheme.OrderedAffineCover.instLinearOrder AlgebraicGeometry.OModulePresheaf.module AlgebraicGeometry.Scheme.OrderedAffineCover.instFintype AlgebraicGeometry.Scheme.OrderedAffineCover.instFintypeIdx AlgebraicGeometry.OModulePresheaf.addCommGroup AlgebraicGeometry.Scheme.OrderedAffineCover.instDecidableEqIdx AlgebraicGeometry.OModulePresheaf.moduleSections TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module"
p2m_attr_erase "instance" "CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free AlgebraicGeometry.SquareZero.isLocalRing' AlgebraicGeometry.SquareZero.isLocalRing AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module"
p2m_attr_erase "instance" "ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule instTopologicallyFGOfFiniteType AlgebraicCurve.CurveModel.isProper AlgebraicCurve.CurveModel.isIntegral AlgebraicCurve.CurveModel.smooth AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instSMulAlgEquiv AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instMulActionAlgEquiv AlgebraicCurve.Pic0.instSMulAlgEquiv AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing"
p2m_attr_erase "instance" "AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin AlgebraicCurve.CurveModel.chartRing_finitePresentation AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation IsDirectLimit.Module.instDirectLimitCoeLinearMapIdOfOfNonempty AdicCompletion.instIsLocalRingMaximalIdeal AlgebraicGeometry.OModulePresheaf.moduleSectionsHomSub AlgebraicGeometry.OModulePresheaf.smulSections AlgebraicGeometry.ProjSpace.twistObj.addCommGroup AlgebraicGeometry.ProjSpace.twistFam.module AlgebraicGeometry.ProjSpace.twistObj.module AlgebraicGeometry.ProjSpace.twistObj.moduleSections AlgebraicGeometry.ProjSpace.twistFam.addCommGroup AlgebraicGeometry.OModulePresheaf.familyFramesGradedModule.moduleBase AlgebraicGeometry.OModulePresheaf.FamilyFrames.module AlgebraicGeometry.OModulePresheaf.FamilyFrames.addCommGroup"
p2m_attr_erase "simp" "AlgebraicGeometry.SubalgebraStages.specCone_π_app AlgebraicGeometry.SubalgebraStages.specLeg_specHom AlgebraicGeometry.SubalgebraStages.specLeg_specTrans AlgebraicGeometry.SubalgebraStages.cone_pt AlgebraicGeometry.SubalgebraStages.trans_fst AlgebraicGeometry.SubalgebraStages.diagram_obj AlgebraicGeometry.SubalgebraStages.leg_snd AlgebraicGeometry.SubalgebraStages.diagram_map AlgebraicGeometry.SubalgebraStages.specTrans_refl AlgebraicGeometry.SubalgebraStages.trans_snd AlgebraicGeometry.SubalgebraStages.specTrans_specHom AlgebraicGeometry.SubalgebraStages.specCone_pt AlgebraicGeometry.SubalgebraStages.cone_π_app AlgebraicGeometry.SubalgebraStages.specDiagram_map AlgebraicGeometry.SubalgebraStages.specDiagram_obj AlgebraicGeometry.SubalgebraStages.leg_fst AlgebraicGeometry.SubalgebraStages.leg_trans AlgebraicGeometry.adicThickeningTransition_ι AlgebraicGeometry.Scheme.OrderedAffineCover.mk.injEq AlgebraicGeometry.OModulePresheaf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app"
p2m_attr_erase "simp" "AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq AlgebraicGeometry.SmallExtension.pairFst_apply AlgebraicGeometry.SmallExtension.pairSnd_apply AlgebraicGeometry.SmallExtension.tensorToDualHom_tmul AlgebraicGeometry.TangentPoints.map_coe AlgebraicGeometry.SquareZero.basePoint_toBase_assoc AlgebraicGeometry.SquareZero.basePoint_toBase AlgebraicGeometry.SquareZero.basePoint_specMap AlgebraicGeometry.SquareZero.basePointOver_coe AlgebraicGeometry.SquareZero.specMap_toBase_assoc AlgebraicGeometry.SquareZero.specMapOver_coe AlgebraicGeometry.RelPicard.TrivialModDeformations.map_coe AlgebraicGeometry.SquareZero.specMap_toBase AlgebraicGeometry.SquareZero.basePoint_specMap_assoc AlgebraicGeometry.RelTangentPoints.const_coe AlgebraicGeometry.SquareZero.zeroSection_fst AlgebraicGeometry.SquareZero.zeroSection_snd_assoc AlgebraicGeometry.SquareZero.zeroSection_fst_assoc AlgebraicGeometry.TangentPoints.zero_coe AlgebraicGeometry.SquareZero.zeroSection_snd AlgebraicGeometry.RelTangentPoints.translate_coe Algebra.PointDerivations.map_apply_coe RegularLocalRingQuotientAscent.dualNumberFst_apply AlgebraicGeometry.schemeFibreEndo_snd AlgebraicGeometry.schemeFibreEndo_fst AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq AlgebraicCurve.CurveModel.mk.injEq AlgebraicCurve.CurveModel.mk.sizeOf_spec AlgebraicCurve.Place.mk.injEq AlgebraicCurve.Divisor.degree_single AlgebraicCurve.Divisor.smul_single AlgebraicCurve.Place.smul_toValuationSubring AlgebraicCurve.Place.heightOneSpectrum_asIdeal AlgebraicCurve.Place.coe_algebraMap AlgebraicCurve.Place.ord_one AlgebraicCurve.Place.coe_smulRingEquiv_apply AlgebraicCurve.Pic0.coe_degZeroSMulHom AlgebraicCurve.Place.deg_smul"
p2m_attr_erase "simp" "AlgebraicCurve.Pic0.mk_zero AlgebraicCurve.Place.mk.sizeOf_spec AlgebraicCurve.Divisor.degree_smul AlgebraicCurve.Pic0.mk_add AlgebraicCurve.Place.ord_zero AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint IsDirectLimit.Module.linearEquiv_symm_apply IsDirectLimit.linearEquiv_symm_apply IsDirectLimit.lift_of IsDirectLimit.Module.linearEquiv_apply IsDirectLimit.Module.lift_of IsDirectLimit.Equiv_apply AlgebraicGeometry.OModulePresheaf.internalHom.ofAffHom_apply AlgebraicGeometry.OModulePresheaf.internalHom.toAffHom_app AlgebraicGeometry.ProjSpace.twistObj.mk.injEq AlgebraicGeometry.ProjSpace.twistObj.zero_val AlgebraicGeometry.ProjSpace.twistObj.add_val AlgebraicGeometry.ProjSpace.twist_res_val AlgebraicGeometry.ProjSpace.twist_smul_val AlgebraicGeometry.ProjSpace.twistGradeToObj_val AlgebraicGeometry.ProjSpace.twistObj.smul_val AlgebraicGeometry.ProjSpace.twistGradeEquiv_apply_val AlgebraicGeometry.ProjSpace.twistObj.mk.sizeOf_spec"

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry GoodReductionJacobian P2MW.S_GoodReductionJacobian_exists_not_mem_forall_nonempty_relativeGroupLaw_geometricFibre_of_not_mem.GoodReductionJacobian NeronModelInfra"

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

namespace GoodReductionJacobian
p2m_export "GoodReductionJacobian" "AbelianSchemePropertyBundle schemeHomOverComp schemeHomOverComp_coe RelativeGroupLaw RelativeGroupLaw.exists_fg_subalgebra_relativeGroupLaw_pullback_snd_of_locallyOfFinitePresentation exists_relativeGroupLaw_baseChange_adicCompletion_one_eq_of_forall_nonempty_relativeGroupLaw_geometricFibre RelativeGroupLaw.exists_one_eq_of_abelianSchemePropertyBundle_of_isPullback_of_faithfullyFlat"
namespace OSHost
p2m_open "GoodReductionJacobian"

section transport

variable {R : Type u} [CommRing R] {X Y : Scheme.{u}}
  {fX : X ⟶ Spec (CommRingCat.of R)} {fY : Y ⟶ Spec (CommRingCat.of R)}
  (e : X ≅ Y) (he : e.hom ≫ fY = fX)

include he in
theorem inv_comp_eq : e.inv ≫ fX = fY := by
  rw [← he, Iso.inv_hom_id_assoc]

def toY {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} (x : SchemeHomOver t fX) : SchemeHomOver t fY :=
  ⟨x.1 ≫ e.hom, by rw [Category.assoc, he, x.2]⟩

def toX {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} (y : SchemeHomOver t fY) : SchemeHomOver t fX :=
  ⟨y.1 ≫ e.inv, by rw [Category.assoc, inv_comp_eq e he, y.2]⟩

@[scoped simp] theorem toY_coe {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} (x : SchemeHomOver t fX) :
    (toY e he x).1 = x.1 ≫ e.hom := rfl
@[scoped simp] theorem toX_coe {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} (y : SchemeHomOver t fY) :
    (toX e he y).1 = y.1 ≫ e.inv := rfl

@[scoped simp] theorem toY_toX {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} (y : SchemeHomOver t fY) :
    toY e he (toX e he y) = y := Subtype.ext (by simp)
@[scoped simp] theorem toX_toY {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} (x : SchemeHomOver t fX) :
    toX e he (toY e he x) = x := Subtype.ext (by simp)

theorem comp_toX {T T' : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} {t' : T' ⟶ Spec (CommRingCat.of R)}
    (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') (y : SchemeHomOver t fY) :
    schemeHomOverComp ψ hψ (toX e he y) = toX e he (schemeHomOverComp ψ hψ y) :=
  Subtype.ext (by simp [Category.assoc])

theorem comp_toY {T T' : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} {t' : T' ⟶ Spec (CommRingCat.of R)}
    (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') (x : SchemeHomOver t fX) :
    schemeHomOverComp ψ hψ (toY e he x) = toY e he (schemeHomOverComp ψ hψ x) :=
  Subtype.ext (by simp [Category.assoc])

def transport (L : RelativeGroupLaw R fY) : RelativeGroupLaw R fX where
  mul t x y := toX e he (L.mul t (toY e he x) (toY e he y))
  one t := toX e he (L.one t)
  inv t x := toX e he (L.inv t (toY e he x))
  mul_assoc t x y z := by simp only [toY_toX, L.mul_assoc]
  one_mul t x := by simp only [toY_toX, L.one_mul, toX_toY]
  mul_one t x := by simp only [toY_toX, L.mul_one, toX_toY]
  inv_mul_cancel t x := by simp only [toY_toX, L.inv_mul_cancel]
  mul_natural t t' ψ hψ x y := by
    rw [comp_toX, L.mul_natural, comp_toY, comp_toY]

end transport

end GoodReductionJacobian.OSHost
p2m_reactivate "P2MW.S_GoodReductionJacobian_exists_not_mem_forall_nonempty_relativeGroupLaw_geometricFibre_of_not_mem.GoodReductionJacobian P2MW.S_GoodReductionJacobian_exists_not_mem_forall_nonempty_relativeGroupLaw_geometricFibre_of_not_mem.GoodReductionJacobian.OSHost"
p2m_reactivate "P2MW.S_GoodReductionJacobian_exists_not_mem_forall_nonempty_relativeGroupLaw_geometricFibre_of_not_mem.GoodReductionJacobian"

namespace GoodReductionJacobian p2m_export "GoodReductionJacobian" "AbelianSchemePropertyBundle schemeHomOverComp schemeHomOverComp_coe RelativeGroupLaw RelativeGroupLaw.exists_fg_subalgebra_relativeGroupLaw_pullback_snd_of_locallyOfFinitePresentation exists_relativeGroupLaw_baseChange_adicCompletion_one_eq_of_forall_nonempty_relativeGroupLaw_geometricFibre RelativeGroupLaw.exists_one_eq_of_abelianSchemePropertyBundle_of_isPullback_of_faithfullyFlat" namespace OSHost end GoodReductionJacobian.OSHost
p2m_open_scoped "GoodReductionJacobian" in
open GoodReductionJacobian.OSHost in

theorem GoodReductionJacobian.OSHost.exists_away_relativeGroupLaw_of_relativeGroupLaw_localizationAtPrime
    {S : Type u} [CommRing S] [IsNoetherianRing S] {Z : Scheme.{u}} (f : Z ⟶ Spec (CommRingCat.of S))
    (hsm : Smooth f) (hpr : IsProper f)
    (s : ↥(Spec (CommRingCat.of S)))
    (Lp : RelativeGroupLaw (Localization.AtPrime s.asIdeal)
        (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.AtPrime s.asIdeal)))))) :
    ∃ (r : S), r ∉ s.asIdeal ∧
      Nonempty (RelativeGroupLaw (Localization.Away r)
        (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away r)))))) := by

  haveI := hsm
  haveI := hpr
  obtain ⟨T, hTfg, -, LT, -⟩ :=
    RelativeGroupLaw.exists_fg_subalgebra_relativeGroupLaw_pullback_snd_of_locallyOfFinitePresentation
      (A₀ := S) (A := Localization.AtPrime s.asIdeal) f Lp ∅

  obtain ⟨r, hr, ψₐ, -⟩ := Subalgebra.exists_algHom_localizationAway_forall_apply_eq_coe_of_fg s.asIdeal T hTfg
  let ψ : ↥T →+* Localization.Away r := ψₐ.toRingHom
  have hψ : ψ.comp (algebraMap S ↥T) = algebraMap S (Localization.Away r) := ψₐ.comp_algebraMap

  let Lψ := LT.baseChange (Spec.map (CommRingCat.ofHom ψ))
  have hcomp : Spec.map (CommRingCat.ofHom ψ) ≫ Spec.map (CommRingCat.ofHom (algebraMap S ↥T)) =
      Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away r))) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hψ]
  let d : pullback f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away r)))) ≅
      pullback (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S ↥T)))) (Spec.map (CommRingCat.ofHom ψ)) :=
    pullback.congrHom rfl hcomp.symm ≪≫
      (pullbackLeftPullbackSndIso f (Spec.map (CommRingCat.ofHom (algebraMap S ↥T))) (Spec.map (CommRingCat.ofHom ψ))).symm
  have hd : d.hom ≫ pullback.snd _ _ = pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away r)))) := by
    simp only [d, Iso.trans_hom, Iso.symm_hom, Category.assoc, pullbackLeftPullbackSndIso_inv_snd_snd]
    exact pullback.lift_snd _ _ _
  exact ⟨r, hr, ⟨transport d hd Lψ⟩⟩

namespace OSO4

p2m_open "GoodReductionJacobian P2MW.S_GoodReductionJacobian_exists_not_mem_forall_nonempty_relativeGroupLaw_geometricFibre_of_not_mem.GoodReductionJacobian"

section OfIso

variable {R : Type u} [CommRing R] {A A' : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}
  {f' : A' ⟶ Spec (CommRingCat.of R)} (e : A' ≅ A) (he : e.hom ≫ f = f')

def fwd {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} (x : SchemeHomOver t f') : SchemeHomOver t f :=
  ⟨x.1 ≫ e.hom, by rw [Category.assoc, he, x.2]⟩

def bwd {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} (y : SchemeHomOver t f) : SchemeHomOver t f' :=
  ⟨y.1 ≫ e.inv, by rw [← he, Category.assoc, e.inv_hom_id_assoc, y.2]⟩

@[scoped simp] theorem fwd_coe {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} (x : SchemeHomOver t f') :
    (fwd e he x).1 = x.1 ≫ e.hom := rfl
@[scoped simp] theorem bwd_coe {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} (y : SchemeHomOver t f) :
    (bwd e he y).1 = y.1 ≫ e.inv := rfl

@[scoped simp] theorem fwd_bwd {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} (y : SchemeHomOver t f) :
    fwd e he (bwd e he y) = y := Subtype.ext (by simp)
@[scoped simp] theorem bwd_fwd {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} (x : SchemeHomOver t f') :
    bwd e he (fwd e he x) = x := Subtype.ext (by simp)

theorem fwd_schemeHomOverComp {T T' : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} {t' : T' ⟶ Spec (CommRingCat.of R)}
    (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') (x : SchemeHomOver t f') :
    fwd e he (schemeHomOverComp ψ hψ x) = schemeHomOverComp ψ hψ (fwd e he x) :=
  Subtype.ext (by simp)

def ofIso (G : RelativeGroupLaw R f) : RelativeGroupLaw R f' where
  mul t x y := bwd e he (G.mul t (fwd e he x) (fwd e he y))
  one t := bwd e he (G.one t)
  inv t x := bwd e he (G.inv t (fwd e he x))
  mul_assoc t x y z := by simp only [fwd_bwd, G.mul_assoc]
  one_mul t x := by simp only [fwd_bwd, G.one_mul, bwd_fwd]
  mul_one t x := by simp only [fwd_bwd, G.mul_one, bwd_fwd]
  inv_mul_cancel t x := by simp only [fwd_bwd, G.inv_mul_cancel]
  mul_natural t t' ψ hψ x y := by
    apply Subtype.ext
    simp only [GoodReductionJacobian.schemeHomOverComp_coe, bwd_coe]
    have h := congrArg Subtype.val (G.mul_natural t t' ψ hψ (fwd e he x) (fwd e he y))
    simp only [GoodReductionJacobian.schemeHomOverComp_coe] at h
    rw [fwd_schemeHomOverComp, fwd_schemeHomOverComp, ← h, Category.assoc]

end OfIso
p2m_reactivate "P2MW.S_GoodReductionJacobian_exists_not_mem_forall_nonempty_relativeGroupLaw_geometricFibre_of_not_mem.GoodReductionJacobian P2MW.S_GoodReductionJacobian_exists_not_mem_forall_nonempty_relativeGroupLaw_geometricFibre_of_not_mem.GoodReductionJacobian.OSHost"

theorem nonempty_of_comp {S : Type u} [CommRing S] {Z : Scheme.{u}} (f : Z ⟶ Spec (CommRingCat.of S))
    {R' : Type u} [CommRing R'] (a : S →+* R') {k : Type u} [CommRing k] (y : R' →+* k) (x : S →+* k)
    (hyx : y.comp a = x)
    (L : RelativeGroupLaw R' (pullback.snd f (Spec.map (CommRingCat.ofHom a)))) :
    Nonempty (RelativeGroupLaw k (pullback.snd f (Spec.map (CommRingCat.ofHom x)))) := by
  set ga : Spec (CommRingCat.of R') ⟶ Spec (CommRingCat.of S) := Spec.map (CommRingCat.ofHom a) with hga
  set gy : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R') := Spec.map (CommRingCat.ofHom y) with hgy
  have hcomp : gy ≫ ga = Spec.map (CommRingCat.ofHom x) := by
    rw [hgy, hga, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hyx]
  let Lk : RelativeGroupLaw k (pullback.snd (pullback.snd f ga) gy) := L.baseChange gy
  let e : pullback f (Spec.map (CommRingCat.ofHom x)) ≅ pullback (pullback.snd f ga) gy :=
    pullback.congrHom rfl hcomp.symm ≪≫ (pullbackLeftPullbackSndIso f ga gy).symm
  have he : e.hom ≫ pullback.snd (pullback.snd f ga) gy = pullback.snd f (Spec.map (CommRingCat.ofHom x)) := by
    simp only [e, Iso.trans_hom, Iso.symm_hom, Category.assoc, pullbackLeftPullbackSndIso_inv_snd_snd]
    rw [pullback.congrHom_hom, pullback.lift_snd, Category.comp_id]
  exact ⟨ofIso e he Lk⟩

end OSO4
p2m_reactivate "P2MW.S_GoodReductionJacobian_exists_not_mem_forall_nonempty_relativeGroupLaw_geometricFibre_of_not_mem.GoodReductionJacobian P2MW.S_GoodReductionJacobian_exists_not_mem_forall_nonempty_relativeGroupLaw_geometricFibre_of_not_mem.GoodReductionJacobian.OSHost P2MW.S_GoodReductionJacobian_exists_not_mem_forall_nonempty_relativeGroupLaw_geometricFibre_of_not_mem.OSO4"

namespace GoodReductionJacobian p2m_export "GoodReductionJacobian" "AbelianSchemePropertyBundle schemeHomOverComp schemeHomOverComp_coe RelativeGroupLaw RelativeGroupLaw.exists_fg_subalgebra_relativeGroupLaw_pullback_snd_of_locallyOfFinitePresentation exists_relativeGroupLaw_baseChange_adicCompletion_one_eq_of_forall_nonempty_relativeGroupLaw_geometricFibre RelativeGroupLaw.exists_one_eq_of_abelianSchemePropertyBundle_of_isPullback_of_faithfullyFlat" end GoodReductionJacobian
p2m_open_scoped "GoodReductionJacobian" in
theorem GoodReductionJacobian.forall_nonempty_relativeGroupLaw_geometricFibre_of_relativeGroupLaw_baseChange_away
    {S : Type u} [CommRing S] [IsNoetherianRing S] {Z : Scheme.{u}} (f : Z ⟶ Spec (CommRingCat.of S))
    (hsm : Smooth f) (hpr : IsProper f)
    (hproj : ∃ (N : ℕ) (ι : Z ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) S)),
      IsClosedImmersion ι ∧ ι ≫ ProjSpace.π S N = f)
    (hconn : ∀ (k : Type u) [Field k] [IsAlgClosed k] (x : S →+* k),
      ConnectedSpace ↥(pullback f (Spec.map (CommRingCat.ofHom x))))
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of S))) f)
    (r : S) (L : RelativeGroupLaw (Localization.Away r)
        (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away r))))))
    (s' : ↥(Spec (CommRingCat.of S))) (hr : r ∉ s'.asIdeal) :
    (∀ (k : Type u) [Field k] [IsAlgClosed k] (x : S →+* k), RingHom.ker x = s'.asIdeal →
        Nonempty (RelativeGroupLaw k (pullback.snd f (Spec.map (CommRingCat.ofHom x))))) := by
  intro k _ _ x hx
  have hxr : IsUnit (x r) := by
    rw [isUnit_iff_ne_zero, Ne, ← RingHom.mem_ker, hx]; exact hr
  exact OSO4.nonempty_of_comp f (algebraMap S (Localization.Away r)) (IsLocalization.Away.lift r hxr) x
    (IsLocalization.Away.lift_comp r hxr) L

namespace GoodReductionJacobian
p2m_export "GoodReductionJacobian" "AbelianSchemePropertyBundle schemeHomOverComp schemeHomOverComp_coe RelativeGroupLaw RelativeGroupLaw.exists_fg_subalgebra_relativeGroupLaw_pullback_snd_of_locallyOfFinitePresentation exists_relativeGroupLaw_baseChange_adicCompletion_one_eq_of_forall_nonempty_relativeGroupLaw_geometricFibre RelativeGroupLaw.exists_one_eq_of_abelianSchemePropertyBundle_of_isPullback_of_faithfullyFlat"
namespace OSO2
p2m_open "GoodReductionJacobian"

theorem exists_geomPoint {T : Type u} [CommRing T] (t : Spec (CommRingCat.of T)) :
    ∃ (k : Type u) (_ : Field k) (_ : IsAlgClosed k) (g₀ : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of T)),
      Set.range g₀.base = {t} := by
  let K : Type u := (Spec (CommRingCat.of T)).residueField t
  refine ⟨AlgebraicClosure K, inferInstance, inferInstance,
    Spec.map (CommRingCat.ofHom (algebraMap K (AlgebraicClosure K))) ≫
      (Spec (CommRingCat.of T)).fromSpecResidueField t, ?_⟩
  apply Set.Subset.antisymm
  · rintro _ ⟨x, rfl⟩
    rw [Scheme.Hom.comp_apply]
    have := Scheme.range_fromSpecResidueField (X := Spec (CommRingCat.of T)) t
    exact this ▸ Set.mem_range_self _
  · intro y hy
    rw [Set.mem_singleton_iff] at hy
    rw [hy]
    obtain ⟨x⟩ : Nonempty (Spec (CommRingCat.of (AlgebraicClosure K))) := ⟨(default : PrimeSpectrum _)⟩
    refine ⟨x, ?_⟩
    rw [Scheme.Hom.comp_apply]
    have := Scheme.range_fromSpecResidueField (X := Spec (CommRingCat.of T)) t
    exact (this ▸ Set.mem_range_self _ : _ ∈ ({t} : Set _))

theorem isConnected_preimage_of_geomPoint {R T k : Type u} [CommRing R] [CommRing T] [Field k] {A : Scheme.{u}}
    (f : A ⟶ Spec (CommRingCat.of R)) (ι : Spec (CommRingCat.of T) ⟶ Spec (CommRingCat.of R))
    (t : Spec (CommRingCat.of T)) (g₀ : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of T))
    (hg₀ : Set.range g₀.base = {t})
    (hA : ConnectedSpace ↥(pullback f (g₀ ≫ ι))) :
    _root_.IsConnected ((pullback.snd f ι).base ⁻¹' {t}) := by

  have huniv : _root_.IsConnected (Set.univ : Set ↥(pullback f (g₀ ≫ ι))) := isConnected_univ

  have hfib : (pullback.snd f ι).base ⁻¹' {t}
      = Set.range (pullback.fst (pullback.snd f ι) g₀).base := by
    have := Scheme.Pullback.range_fst (pullback.snd f ι) g₀
    rw [hg₀] at this
    exact this.symm

  let e := pullbackLeftPullbackSndIso f ι g₀
  have hsurj : Function.Surjective e.inv.base := fun y =>
    ⟨e.hom.base y, by
      have := congr_arg (fun h : pullback (pullback.snd f ι) g₀ ⟶ _ => h.base y) e.hom_inv_id
      simpa using this⟩
  have hrange : Set.range (pullback.fst (pullback.snd f ι) g₀).base
      = (e.inv ≫ pullback.fst (pullback.snd f ι) g₀).base '' Set.univ := by
    rw [Set.image_univ]
    ext z
    constructor
    · rintro ⟨y, rfl⟩
      obtain ⟨w, rfl⟩ := hsurj y
      exact ⟨w, (Scheme.Hom.comp_apply _ _ _).symm⟩
    · rintro ⟨w, rfl⟩
      exact ⟨e.inv.base w, (Scheme.Hom.comp_apply _ _ _).symm⟩
  rw [hfib, hrange]
  exact huniv.image _ (e.inv ≫ pullback.fst (pullback.snd f ι) g₀).base.hom.continuous.continuousOn

theorem abelianSchemePropertyBundle_baseChange {R T : Type u} [CommRing R] [CommRing T] {A : Scheme.{u}}
    (f : A ⟶ Spec (CommRingCat.of R)) (hs : Smooth f) (hp : IsProper f)
    (hgeo : ∀ (k : Type u) [Field k] [IsAlgClosed k] (g : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R)),
      ConnectedSpace ↥(pullback f g))
    (ι : Spec (CommRingCat.of T) ⟶ Spec (CommRingCat.of R))
    (L : RelativeGroupLaw T (pullback.snd f ι)) :
    AbelianSchemePropertyBundle T (pullback.snd f ι) where
  smooth := MorphismProperty.pullback_snd (P := @Smooth) _ _ hs
  proper := MorphismProperty.pullback_snd (P := @IsProper) _ _ hp
  connectedFibres t := by
    obtain ⟨k, _, _, g₀, hg₀⟩ := exists_geomPoint t
    exact isConnected_preimage_of_geomPoint f ι t g₀ hg₀ (hgeo k (g₀ ≫ ι))
  hasGroupLaw := ⟨L⟩

theorem descend {R : Type u} [CommRing R] (S T : Type u) [CommRing S] [CommRing T] [Algebra S T]
    [Module.FaithfullyFlat S T] (φ : R →+* S) {A : Scheme.{u}}
    (f : A ⟶ Spec (CommRingCat.of R)) (hs : Smooth f) (hp : IsProper f)
    (e : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) f)
    (hgeo : ∀ (k : Type u) [Field k] [IsAlgClosed k] (g : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R)),
      ConnectedSpace ↥(pullback f g))
    (L' : RelativeGroupLaw T (pullback.snd f (Spec.map (CommRingCat.ofHom ((algebraMap S T).comp φ)))))
    (hL' : (L'.one (𝟙 _)).1 =
      pullback.lift (Spec.map (CommRingCat.ofHom ((algebraMap S T).comp φ)) ≫ e.1) (𝟙 _)
        (by rw [Category.assoc, e.2, Category.comp_id, Category.id_comp])) :
    ∃ L : RelativeGroupLaw S (pullback.snd f (Spec.map (CommRingCat.ofHom φ))),
      (L.one (𝟙 _)).1 = pullback.lift (Spec.map (CommRingCat.ofHom φ) ≫ e.1) (𝟙 _)
        (by rw [Category.assoc, e.2, Category.comp_id, Category.id_comp]) := by

  have hcomp : Spec.map (CommRingCat.ofHom (algebraMap S T)) ≫ Spec.map (CommRingCat.ofHom φ)
      = Spec.map (CommRingCat.ofHom ((algebraMap S T).comp φ)) := by
    rw [CommRingCat.ofHom_comp, Spec.map_comp]

  let c : pullback f (Spec.map (CommRingCat.ofHom ((algebraMap S T).comp φ)))
      ⟶ pullback f (Spec.map (CommRingCat.ofHom φ)) :=
    pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom (algebraMap S T)))
      (by rw [pullback.condition, Category.assoc, hcomp])
  have hc : IsPullback c (pullback.snd f (Spec.map (CommRingCat.ofHom ((algebraMap S T).comp φ))))
      (pullback.snd f (Spec.map (CommRingCat.ofHom φ))) (Spec.map (CommRingCat.ofHom (algebraMap S T))) := by
    refine IsPullback.of_right ?_ (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback f (Spec.map (CommRingCat.ofHom φ)))
    rw [pullback.lift_fst, hcomp]
    exact IsPullback.of_hasPullback _ _
  have hA' := abelianSchemePropertyBundle_baseChange f hs hp hgeo _ L'

  let eS : SchemeHomOver (𝟙 (Spec (CommRingCat.of S))) (pullback.snd f (Spec.map (CommRingCat.ofHom φ))) :=
    ⟨pullback.lift (Spec.map (CommRingCat.ofHom φ) ≫ e.1) (𝟙 _)
        (by rw [Category.assoc, e.2, Category.comp_id, Category.id_comp]),
      by rw [pullback.lift_snd]⟩
  have he' : (L'.one (𝟙 _)).1 ≫ c = Spec.map (CommRingCat.ofHom (algebraMap S T)) ≫ eS.1 := by
    rw [hL']
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst, Category.assoc, pullback.lift_fst,
        ← Category.assoc, hcomp]
    · rw [Category.assoc, pullback.lift_snd, ← Category.assoc, pullback.lift_snd, Category.id_comp,
        Category.assoc, pullback.lift_snd, Category.comp_id]
  obtain ⟨L, hL⟩ :=
    GoodReductionJacobian.RelativeGroupLaw.exists_one_eq_of_abelianSchemePropertyBundle_of_isPullback_of_faithfullyFlat
      T (pullback.snd f (Spec.map (CommRingCat.ofHom φ))) eS
      (pullback.snd f (Spec.map (CommRingCat.ofHom ((algebraMap S T).comp φ)))) c hc hA' L' he'
  exact ⟨L, hL⟩

end GoodReductionJacobian.OSO2
p2m_reactivate "P2MW.S_GoodReductionJacobian_exists_not_mem_forall_nonempty_relativeGroupLaw_geometricFibre_of_not_mem.GoodReductionJacobian P2MW.S_GoodReductionJacobian_exists_not_mem_forall_nonempty_relativeGroupLaw_geometricFibre_of_not_mem.GoodReductionJacobian.OSHost P2MW.S_GoodReductionJacobian_exists_not_mem_forall_nonempty_relativeGroupLaw_geometricFibre_of_not_mem.OSO4"
p2m_reactivate "P2MW.S_GoodReductionJacobian_exists_not_mem_forall_nonempty_relativeGroupLaw_geometricFibre_of_not_mem.GoodReductionJacobian P2MW.S_GoodReductionJacobian_exists_not_mem_forall_nonempty_relativeGroupLaw_geometricFibre_of_not_mem.GoodReductionJacobian.OSHost P2MW.S_GoodReductionJacobian_exists_not_mem_forall_nonempty_relativeGroupLaw_geometricFibre_of_not_mem.OSO4"

p2m_open_scoped "GoodReductionJacobian" in
open GoodReductionJacobian.OSO2 in
theorem GoodReductionJacobian.exists_relativeGroupLaw_baseChange_localizationAtPrime_one_eq_of_forall_nonempty_relativeGroupLaw_geometricFibre
    {S : Type u} [CommRing S] [IsNoetherianRing S] {Z : Scheme.{u}} (f : Z ⟶ Spec (CommRingCat.of S))
    (hsm : Smooth f) (hpr : IsProper f)
    (hproj : ∃ (N : ℕ) (ι : Z ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) S)),
      IsClosedImmersion ι ∧ ι ≫ ProjSpace.π S N = f)
    (hconn : ∀ (k : Type u) [Field k] [IsAlgClosed k] (x : S →+* k),
      ConnectedSpace ↥(pullback f (Spec.map (CommRingCat.ofHom x))))
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of S))) f)
    (s : ↥(Spec (CommRingCat.of S))) (hs : (∀ (k : Type u) [Field k] [IsAlgClosed k] (x : S →+* k), RingHom.ker x = s.asIdeal →
        Nonempty (RelativeGroupLaw k (pullback.snd f (Spec.map (CommRingCat.ofHom x)))))) :
    ∃ L : RelativeGroupLaw (Localization.AtPrime s.asIdeal)
        (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.AtPrime s.asIdeal))))),
      (L.one (𝟙 _)).1 =
        pullback.lift (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.AtPrime s.asIdeal))) ≫ ε.1) (𝟙 _)
          (by rw [Category.assoc, ε.2, Category.comp_id, Category.id_comp]) := by

  have hgeo : ∀ (k : Type u) [Field k] [IsAlgClosed k] (g : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of S)),
      ConnectedSpace ↥(pullback f g) := by
    intro k _ _ g
    rw [← Spec.map_preimage g, ← CommRingCat.ofHom_hom (Spec.preimage g)]
    exact hconn k (Spec.preimage g).hom
  haveI : Module.FaithfullyFlat (Localization.AtPrime s.asIdeal)
      (AdicCompletion (IsLocalRing.maximalIdeal (Localization.AtPrime s.asIdeal)) (Localization.AtPrime s.asIdeal)) :=
    IsLocalRing.faithfullyFlat_adicCompletion_maximalIdeal _
  obtain ⟨L', hL'⟩ :=
    GoodReductionJacobian.exists_relativeGroupLaw_baseChange_adicCompletion_one_eq_of_forall_nonempty_relativeGroupLaw_geometricFibre
      f hsm hpr hproj hconn ε s hs
  exact descend (Localization.AtPrime s.asIdeal)
    (AdicCompletion (IsLocalRing.maximalIdeal (Localization.AtPrime s.asIdeal)) (Localization.AtPrime s.asIdeal))
    (algebraMap S (Localization.AtPrime s.asIdeal)) f hsm hpr ε hgeo L' hL'

theorem solution
    {S : Type u} [CommRing S] [IsNoetherianRing S] {Z : Scheme.{u}} (f : Z ⟶ Spec (CommRingCat.of S))
    (hsm : Smooth f) (hpr : IsProper f)
    (hproj : ∃ (N : ℕ) (ι : Z ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) S)),
      IsClosedImmersion ι ∧ ι ≫ ProjSpace.π S N = f)
    (hconn : ∀ (k : Type u) [Field k] [IsAlgClosed k] (x : S →+* k),
      ConnectedSpace ↥(pullback f (Spec.map (CommRingCat.ofHom x))))
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of S))) f)
    (s : ↥(Spec (CommRingCat.of S)))
    (hs : (∀ (k : Type u) [Field k] [IsAlgClosed k] (x : S →+* k), RingHom.ker x = s.asIdeal →
        Nonempty (RelativeGroupLaw k (pullback.snd f (Spec.map (CommRingCat.ofHom x)))))) :
    ∃ r : S, r ∉ s.asIdeal ∧ ∀ s' : ↥(Spec (CommRingCat.of S)), r ∉ s'.asIdeal →
      (∀ (k : Type u) [Field k] [IsAlgClosed k] (x : S →+* k), RingHom.ker x = s'.asIdeal →
        Nonempty (RelativeGroupLaw k (pullback.snd f (Spec.map (CommRingCat.ofHom x))))) := by

  obtain ⟨Lp, -⟩ :=
    GoodReductionJacobian.exists_relativeGroupLaw_baseChange_localizationAtPrime_one_eq_of_forall_nonempty_relativeGroupLaw_geometricFibre
      f hsm hpr hproj hconn ε s hs

  obtain ⟨r, hr, ⟨Lr⟩⟩ :=
    GoodReductionJacobian.OSHost.exists_away_relativeGroupLaw_of_relativeGroupLaw_localizationAtPrime f hsm hpr s Lp

  exact ⟨r, hr, fun s' hs' =>
    GoodReductionJacobian.forall_nonempty_relativeGroupLaw_geometricFibre_of_relativeGroupLaw_baseChange_away
      f hsm hpr hproj hconn ε r Lr s' hs'⟩

end S_GoodReductionJacobian_exists_not_mem_forall_nonempty_relativeGroupLaw_geometricFibre_of_not_mem
end P2MW
export P2MW.S_GoodReductionJacobian_exists_not_mem_forall_nonempty_relativeGroupLaw_geometricFibre_of_not_mem (solution)
