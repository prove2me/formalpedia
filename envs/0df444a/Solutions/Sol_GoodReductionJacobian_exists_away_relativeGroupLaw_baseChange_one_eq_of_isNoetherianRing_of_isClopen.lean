-- Prove2me | solution 1 for GoodReductionJacobian.exists_away_relativeGroupLaw_baseChange_one_eq_of_isNoetherianRing_of_isClopen
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/458d0480-7df7-5fd9-b96a-006866b24300

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_AlgebraicGeometry_ProjSpace
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import Theorems.Thm_GoodReductionJacobian_exists_relativeGroupLaw_baseChange_localizationAtPrime_one_eq_of_isNoetherianRing_of_isClopen
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_fg_subalgebra_relativeGroupLaw_pullback_snd_of_locallyOfFinitePresentation
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_one_eq_of_section
import Theorems.Thm_Subalgebra_exists_algHom_localizationAway_forall_apply_eq_coe_of_fg
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_exists_away_relativeGroupLaw_baseChange_one_eq_of_isNoetherianRing_of_isClopen
p2m_attr_erase "instance" "AlgebraicGeometry.isClosedImmersion_adicThickeningι AlgebraicGeometry.OModulePresheaf.isScalarTower AlgebraicGeometry.Scheme.OrderedAffineCover.instLinearOrder AlgebraicGeometry.OModulePresheaf.module AlgebraicGeometry.Scheme.OrderedAffineCover.instFintype AlgebraicGeometry.Scheme.OrderedAffineCover.instFintypeIdx AlgebraicGeometry.OModulePresheaf.addCommGroup AlgebraicGeometry.Scheme.OrderedAffineCover.instDecidableEqIdx AlgebraicGeometry.OModulePresheaf.moduleSections TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free AlgebraicGeometry.SquareZero.isLocalRing' AlgebraicGeometry.SquareZero.isLocalRing AlgebraicGeometry.Scheme.Hom.opensMapFinal AlgebraicGeometry.RelPicard.RigidifiedLineBundle.setoid AlgebraicGeometry.RelPicard.RigidifiedLineBundle.instInhabited"
p2m_attr_erase "instance" "AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule instTopologicallyFGOfFiniteType"
p2m_attr_erase "instance" "AlgebraicCurve.CurveModel.isProper AlgebraicCurve.CurveModel.isIntegral AlgebraicCurve.CurveModel.smooth AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instSMulAlgEquiv AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instMulActionAlgEquiv AlgebraicCurve.Pic0.instSMulAlgEquiv AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin AlgebraicCurve.CurveModel.chartRing_finitePresentation"
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicGeometry.SubalgebraStages.compactSpace_pullback AlgebraicGeometry.SubalgebraStages.quasiSeparatedSpace_pullback AlgebraicGeometry.SubalgebraStages.compactSpace_obj AlgebraicGeometry.SubalgebraStages.quasiSeparatedSpace_obj AlgebraicGeometry.SubalgebraStages.quasiCompact_snd AlgebraicGeometry.SubalgebraStages.isAffineHom_leg AlgebraicGeometry.SubalgebraStages.isAffineHom_trans AlgebraicGeometry.SubalgebraStages.isAffineHom_diagram_map AlgebraicGeometry.SubalgebraStages.quasiSeparated_snd AlgebraicGeometry.SubalgebraStages.isCofiltered_op IsDirectLimit.Module.instDirectLimitCoeLinearMapIdOfOfNonempty AdicCompletion.instIsLocalRingMaximalIdeal AlgebraicGeometry.OModulePresheaf.moduleSectionsHomSub AlgebraicGeometry.OModulePresheaf.smulSections AlgebraicGeometry.ProjSpace.twistObj.addCommGroup AlgebraicGeometry.ProjSpace.twistFam.module AlgebraicGeometry.ProjSpace.twistObj.module AlgebraicGeometry.ProjSpace.twistObj.moduleSections AlgebraicGeometry.ProjSpace.twistFam.addCommGroup AlgebraicGeometry.OModulePresheaf.familyFramesGradedModule.moduleBase AlgebraicGeometry.OModulePresheaf.FamilyFrames.module AlgebraicGeometry.OModulePresheaf.FamilyFrames.addCommGroup"
p2m_attr_erase "simp" "AlgebraicGeometry.adicThickeningTransition_ι AlgebraicGeometry.Scheme.OrderedAffineCover.mk.injEq AlgebraicGeometry.OModulePresheaf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq AlgebraicGeometry.SmallExtension.pairFst_apply AlgebraicGeometry.SmallExtension.pairSnd_apply AlgebraicGeometry.SmallExtension.tensorToDualHom_tmul AlgebraicGeometry.TangentPoints.map_coe AlgebraicGeometry.SquareZero.basePoint_toBase_assoc"
p2m_attr_erase "simp" "AlgebraicGeometry.SquareZero.basePoint_toBase AlgebraicGeometry.SquareZero.basePoint_specMap AlgebraicGeometry.SquareZero.basePointOver_coe AlgebraicGeometry.SquareZero.specMap_toBase_assoc AlgebraicGeometry.SquareZero.specMapOver_coe AlgebraicGeometry.RelPicard.TrivialModDeformations.map_coe AlgebraicGeometry.SquareZero.specMap_toBase AlgebraicGeometry.SquareZero.basePoint_specMap_assoc AlgebraicGeometry.RelPicard.RigidifiedLineBundle.mk.sizeOf_spec AlgebraicGeometry.RelPicard.RigidifiedLineBundle.mk.injEq AlgebraicGeometry.RelTangentPoints.const_coe AlgebraicGeometry.SquareZero.zeroSection_fst AlgebraicGeometry.SquareZero.zeroSection_snd_assoc AlgebraicGeometry.SquareZero.zeroSection_fst_assoc AlgebraicGeometry.TangentPoints.zero_coe AlgebraicGeometry.SquareZero.zeroSection_snd AlgebraicGeometry.RelTangentPoints.translate_coe Algebra.PointDerivations.map_apply_coe RegularLocalRingQuotientAscent.dualNumberFst_apply AlgebraicGeometry.schemeFibreEndo_snd AlgebraicGeometry.schemeFibreEndo_fst AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj"
p2m_attr_erase "simp" "AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq AlgebraicCurve.CurveModel.mk.injEq AlgebraicCurve.CurveModel.mk.sizeOf_spec AlgebraicCurve.Place.mk.injEq AlgebraicCurve.Divisor.degree_single AlgebraicCurve.Divisor.smul_single AlgebraicCurve.Place.smul_toValuationSubring AlgebraicCurve.Place.heightOneSpectrum_asIdeal AlgebraicCurve.Place.coe_algebraMap AlgebraicCurve.Place.ord_one AlgebraicCurve.Place.coe_smulRingEquiv_apply AlgebraicCurve.Pic0.coe_degZeroSMulHom AlgebraicCurve.Place.deg_smul AlgebraicCurve.Pic0.mk_zero AlgebraicCurve.Place.mk.sizeOf_spec AlgebraicCurve.Divisor.degree_smul AlgebraicCurve.Pic0.mk_add AlgebraicCurve.Place.ord_zero AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase"
p2m_attr_erase "simp" "AlgebraicCurve.CurveModel.coe_tma AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicGeometry.SubalgebraStages.specCone_π_app AlgebraicGeometry.SubalgebraStages.specLeg_specHom AlgebraicGeometry.SubalgebraStages.specLeg_specTrans AlgebraicGeometry.SubalgebraStages.cone_pt AlgebraicGeometry.SubalgebraStages.trans_fst AlgebraicGeometry.SubalgebraStages.diagram_obj AlgebraicGeometry.SubalgebraStages.leg_snd AlgebraicGeometry.SubalgebraStages.diagram_map AlgebraicGeometry.SubalgebraStages.specTrans_refl AlgebraicGeometry.SubalgebraStages.trans_snd AlgebraicGeometry.SubalgebraStages.specTrans_specHom AlgebraicGeometry.SubalgebraStages.specCone_pt AlgebraicGeometry.SubalgebraStages.cone_π_app AlgebraicGeometry.SubalgebraStages.specDiagram_map AlgebraicGeometry.SubalgebraStages.specDiagram_obj AlgebraicGeometry.SubalgebraStages.leg_fst AlgebraicGeometry.SubalgebraStages.leg_trans IsDirectLimit.Module.linearEquiv_symm_apply IsDirectLimit.linearEquiv_symm_apply IsDirectLimit.lift_of IsDirectLimit.Module.linearEquiv_apply IsDirectLimit.Module.lift_of IsDirectLimit.Equiv_apply AlgebraicGeometry.OModulePresheaf.internalHom.ofAffHom_apply AlgebraicGeometry.OModulePresheaf.internalHom.toAffHom_app AlgebraicGeometry.ProjSpace.twistObj.mk.injEq AlgebraicGeometry.ProjSpace.twistObj.zero_val AlgebraicGeometry.ProjSpace.twistObj.add_val AlgebraicGeometry.ProjSpace.twist_res_val AlgebraicGeometry.ProjSpace.twist_smul_val AlgebraicGeometry.ProjSpace.twistGradeToObj_val AlgebraicGeometry.ProjSpace.twistObj.smul_val"
p2m_attr_erase "simp" "AlgebraicGeometry.ProjSpace.twistGradeEquiv_apply_val AlgebraicGeometry.ProjSpace.twistObj.mk.sizeOf_spec"

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GoodReductionJacobian NeronModelInfra

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

namespace H2bTop

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

end H2bTop
p2m_reactivate "P2MW.S_GoodReductionJacobian_exists_away_relativeGroupLaw_baseChange_one_eq_of_isNoetherianRing_of_isClopen.H2bTop"

open H2bTop in
theorem solution
    {R : Type u} [CommRing R] [IsNoetherianRing R] {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of R))
    (hs : Smooth f) (hp : IsProper f)
    (N : ℕ) (ι : A ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R)) (hι : IsClosedImmersion ι)
    (hιf : ι ≫ ProjSpace.π R N = f)
    (e : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) f)
    (W : Set ↥(Spec (CommRingCat.of R))) (hW : IsClopen W)
    (hc : ∀ s : Spec (CommRingCat.of R), s ∈ W → _root_.IsConnected (f.base ⁻¹' {s}))
    (hfib : ∀ (k : Type u) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R)),
      Set.range s.base ⊆ W → AbelianSchemePropertyBundle k (pullback.snd f s))
    (s : Spec (CommRingCat.of R)) (hsW : s ∈ W) :
    ∃ (r : R), r ∉ s.asIdeal ∧
      ∃ L : RelativeGroupLaw (Localization.Away r)
        (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away r))))),
        (L.one (𝟙 _)).1 = pullback.lift (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away r))) ≫ e.1) (𝟙 _)
          (by rw [Category.assoc, e.2, Category.comp_id, Category.id_comp]) := by

  obtain ⟨Lp, -⟩ :=
    GoodReductionJacobian.exists_relativeGroupLaw_baseChange_localizationAtPrime_one_eq_of_isNoetherianRing_of_isClopen
      f hs hp N ι hι hιf e W hW hc hfib s hsW

  haveI := hs
  haveI := hp
  obtain ⟨T, hTfg, -, LT, -⟩ :=
    RelativeGroupLaw.exists_fg_subalgebra_relativeGroupLaw_pullback_snd_of_locallyOfFinitePresentation
      (A₀ := R) (A := Localization.AtPrime s.asIdeal) f Lp ∅

  obtain ⟨r, hr, ψₐ, -⟩ := Subalgebra.exists_algHom_localizationAway_forall_apply_eq_coe_of_fg s.asIdeal T hTfg
  let ψ : ↥T →+* Localization.Away r := ψₐ.toRingHom
  have hψ : ψ.comp (algebraMap R ↥T) = algebraMap R (Localization.Away r) := ψₐ.comp_algebraMap

  let Lψ := LT.baseChange (Spec.map (CommRingCat.ofHom ψ))
  have hcomp : Spec.map (CommRingCat.ofHom ψ) ≫ Spec.map (CommRingCat.ofHom (algebraMap R ↥T)) =
      Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away r))) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hψ]
  let d : pullback f (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away r)))) ≅
      pullback (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R ↥T)))) (Spec.map (CommRingCat.ofHom ψ)) :=
    pullback.congrHom rfl hcomp.symm ≪≫
      (pullbackLeftPullbackSndIso f (Spec.map (CommRingCat.ofHom (algebraMap R ↥T))) (Spec.map (CommRingCat.ofHom ψ))).symm
  have hd : d.hom ≫ pullback.snd _ _ = pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away r)))) := by
    simp only [d, Iso.trans_hom, Iso.symm_hom, Category.assoc, pullbackLeftPullbackSndIso_inv_snd_snd]
    exact pullback.lift_snd _ _ _
  let Lr : RelativeGroupLaw (Localization.Away r)
      (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away r))))) :=
    transport d hd Lψ

  let er : SchemeHomOver (𝟙 _) (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away r))))) :=
    ⟨pullback.lift (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away r))) ≫ e.1) (𝟙 _)
      (by rw [Category.assoc, e.2, Category.comp_id, Category.id_comp]), pullback.lift_snd _ _ _⟩
  obtain ⟨L, hL, -⟩ := RelativeGroupLaw.exists_one_eq_of_section Lr er
  exact ⟨r, hr, L, by rw [hL]⟩

end S_GoodReductionJacobian_exists_away_relativeGroupLaw_baseChange_one_eq_of_isNoetherianRing_of_isClopen
end P2MW
export P2MW.S_GoodReductionJacobian_exists_away_relativeGroupLaw_baseChange_one_eq_of_isNoetherianRing_of_isClopen (solution)
