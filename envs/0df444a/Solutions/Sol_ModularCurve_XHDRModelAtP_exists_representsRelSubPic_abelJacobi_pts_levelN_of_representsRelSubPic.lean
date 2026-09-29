-- Prove2me | solution 1 for ModularCurve.XHDRModelAtP.exists_representsRelSubPic_abelJacobi_pts_levelN_of_representsRelSubPic
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/1c72f472-730e-5900-b38d-e04dd50b90eb

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_ModularCurve_JZeroNeronObjectAtP
import Definitions.Def_ModularCurve_XH
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_AlgebraicGeometry_RelSubPicGroup
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivOfPoint
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicGeometry_RelSubPicBaseChange
import Definitions.Def_AlgebraicGeometry_RelativePic0DesignationBaseChange

import Theorems.Thm_AlgebraicGeometry_RelPicard_exists_representsRelSubPic_baseChange
import Theorems.Thm_AlgebraicGeometry_RelPicard_baseChange_relativeGroupLaw_mul_compat
import Theorems.Thm_AlgebraicGeometry_RelPicard_exists_abelJacobi_of_representsRelSubPic
import Theorems.Thm_AlgebraicGeometry_RelPicard_exists_pic0_equiv_points_of_representsRelSubPic_of_abelJacobi
import Theorems.Thm_ModularCurve_JOneES_exists_transcendental_finiteDimensional_laurentBaseChange
import Theorems.Thm_AlgebraicCurve_isCurveOver_of_transcendental_of_perfectField
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XHDRModelAtP_exists_representsRelSubPic_abelJacobi_pts_levelN_of_representsRelSubPic
p2m_attr_erase "instance" "PresheafOfModules.ExteriorPower.instModulePresheafAb AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instNeg AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulInt AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAddCommGroup AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAdd AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSub AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulNat AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instZero TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt"
p2m_attr_erase "instance" "AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions SheafOfModules.isIso_ihomModelToIhom AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion AlgebraicGeometry.RelEffCartierDiv.subsingleton_of_degree_zero AlgebraicGeometry.OModulePresheaf.isScalarTower AlgebraicGeometry.Scheme.OrderedAffineCover.instLinearOrder AlgebraicGeometry.OModulePresheaf.module AlgebraicGeometry.Scheme.OrderedAffineCover.instFintype AlgebraicGeometry.Scheme.OrderedAffineCover.instFintypeIdx AlgebraicGeometry.OModulePresheaf.addCommGroup AlgebraicGeometry.Scheme.OrderedAffineCover.instDecidableEqIdx AlgebraicGeometry.OModulePresheaf.moduleSections AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero"
p2m_attr_erase "instance" "AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup"
p2m_attr_erase "instance" "ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule"
p2m_attr_erase "simp" "AlgebraicGeometry.RelPicard.thetaBundle_def AlgebraicGeometry.RelPicard.picardBundle_def AlgebraicGeometry.Scheme.Modules.exteriorPower_obj PresheafOfModules.exteriorPower_map_ιMulti PresheafOfModules.ExteriorPower.appₗ_apply AlgebraicGeometry.RelPicard.fst_toProdSpec AlgebraicGeometry.RelPicard.toProdSpec_fst_assoc AlgebraicGeometry.RelPicard.pointsSubBasepointModule_cons AlgebraicGeometry.RelPicard.pointsSubBasepointModule_nil AlgebraicGeometry.RelPicard.fst_toProdSpec_assoc AlgebraicGeometry.RelPicard.toProdSpec_fst AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.sub_app AlgebraicGeometry.Scheme.IdealSheafData.sres_sresTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.add_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.sizeOf_spec AlgebraicGeometry.Scheme.IdealSheafData.coe_resLE AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.smul_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_ofLE_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.ideal_range AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zero_app AlgebraicGeometry.Scheme.IdealSheafData.sres_sres AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.comp_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.neg_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.id_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_mulRight_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.nsmul_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.injEq AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zsmul_app AlgebraicGeometry.SmoothProperCurve.FiniteMapData.twoAffineOpenCover_U1 AlgebraicGeometry.SmoothProperCurve.FiniteMapData.mk.injEq AlgebraicGeometry.SmoothProperCurve.FiniteMapData.mk.sizeOf_spec AlgebraicGeometry.SmoothProperCurve.FiniteMapData.twoAffineOpenCover_U0 AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec"
p2m_attr_erase "simp" "TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicGeometry.Scheme.Modules.toUnitSection_ofUnitSection AlgebraicGeometry.Scheme.Modules.pullbackSection_def AlgebraicGeometry.Scheme.Modules.ofUnitSection_toUnitSection AlgebraicCurve.coe_cechH0Equiv_apply AlgebraicCurve.cechH1ToH1_mk AlgebraicCurve.lSpaceOn_univ AlgebraicCurve.lSpaceOn_empty AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom SheafOfModules.ihomSectionsEquivFamily_unit AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply SheafOfModules.ihomEval_unit_app AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply SheafOfModules.unit_ihomSectionsEquivFamily AlgebraicGeometry.Scheme.Modules.familyOfHom_app AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule AlgebraicGeometry.prodKerGraph_one AlgebraicGeometry.fibrePowOver.proj_comp AlgebraicGeometry.prodKerGraph_zero AlgebraicGeometry.RelEffCartierDiv.empty_I AlgebraicGeometry.fibrePowOver.proj_comp_assoc AlgebraicCurve.SymmetricPowerPackage.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicCurve.SymmetricPowerPackage.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.mk.injEq AlgebraicGeometry.OModulePresheaf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.mk.injEq AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U"
p2m_attr_erase "simp" "AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq TwoChartCech.Mumford.dK_apply TwoChartCech.Mumford.ι0_apply TwoChartCech.Mumford.ι1_apply TwoChartCech.KerCoprod.dK_apply TwoChartCech.KerCoprod.ι1_apply TwoChartCech.KerCoprod.ι0_apply AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app AlgebraicGeometry.RelPicard.rigSection_snd AlgebraicGeometry.RelPicard.RigidifiedLineBundle.ofInvertible_L AlgebraicGeometry.RelPicard.rigSection_snd_assoc"

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry P2MW.S_ModularCurve_XHDRModelAtP_exists_representsRelSubPic_abelJacobi_pts_levelN_of_representsRelSubPic.AlgebraicGeometry NeronModelInfra GoodReductionJacobian ModularCurve P2MW.S_ModularCurve_XHDRModelAtP_exists_representsRelSubPic_abelJacobi_pts_levelN_of_representsRelSubPic.ModularCurve ModularCurve.XHDRLevel ModularCurve.JZeroNeronObjectAtP AlgebraicGeometry.RelPicard P2MW.S_ModularCurve_XHDRModelAtP_exists_representsRelSubPic_abelJacobi_pts_levelN_of_representsRelSubPic.AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve AlgebraicCurve"

open scoped MatrixGroups

universe u v

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Spec.map_comp SmoothOfRelativeDimension IsProper GeometricallyIntegral Spec Spec.map Scheme Smooth GeometricallyConnected geometrically RelEffCartierDiv RelEffCartierDiv.ofPoint"
namespace RelPicard
p2m_export "AlgebraicGeometry.RelPicard" "RepresentsRelSubPic algEquivZeroCut algEquivZeroGroupCut RepresentsRelSubPic.relativeGroupLaw BaseChange.κ BaseChange.κ_hom_snd BaseChange.κ_hom_fst BaseChange.ofR exists_representsRelSubPic_baseChange baseChange_relativeGroupLaw_mul_compat exists_abelJacobi_of_representsRelSubPic exists_pic0_equiv_points_of_representsRelSubPic_of_abelJacobi"
namespace GPTS
p2m_open "AlgebraicGeometry.RelPicard AlgebraicGeometry"

theorem mul_val_congr {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}
    (L : RelativeGroupLaw R f) {T : Scheme.{u}} {t₁ t₂ : T ⟶ Spec (CommRingCat.of R)} (ht : t₁ = t₂)
    (x₁ y₁ : SchemeHomOver t₁ f) (x₂ y₂ : SchemeHomOver t₂ f) (hx : x₁.1 = x₂.1) (hy : y₁.1 = y₂.1) :
    (L.mul t₁ x₁ y₁).1 = (L.mul t₂ x₂ y₂).1 := by
  subst ht
  obtain rfl : x₁ = x₂ := Subtype.ext hx
  obtain rfl : y₁ = y₂ := Subtype.ext hy
  rfl

theorem exists_pts_of_representsRelSubPic_baseChange
    (R : Type u) [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R)) [IsProper c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (D : RelativePic0Designation R c) (h : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D)
    (hsm : Smooth D.toBase)
    (R' : Type u) [CommRing R'] [Algebra R R'] (hgc : GeometricallyConnected (D.baseChange R').toBase)
    [SmoothOfRelativeDimension 1 (baseChange R c R')] [GeometricallyIntegral (baseChange R c R')]
    (hpr' : IsProper (D.baseChange R').toBase)
    (K : Type u) [Field K] [IsAlgClosed K] [Algebra R K] [Algebra R' K] [IsScalarTower R R' K]
    (F : Type v) [Field F] [Algebra K F] [IsCurveOver K F] (M : CurveModel K F)
    (e' : M.C ⟶ pullback (baseChange R c R') (specMap R' K)) [IsIso e']
    (he' : e' ≫ pullback.snd (baseChange R c R') (specMap R' K) = M.toBase) :
    ∃ (h' : RepresentsRelSubPic (baseChange R c R') (sectionBaseChange R' ε)
        (algEquivZeroCut (baseChange R c R') (sectionBaseChange R' ε)) (D.baseChange R'))
      (aj' : SchemeHomOver (baseChange R c R') (D.baseChange R').toBase)
      (pts' : Pic0 K F ≃ SchemeHomOver (specMap R' K) (D.baseChange R').toBase)
      (pts : Pic0 K F ≃ SchemeHomOver (specMap R K) D.toBase),
      Nonempty (h'.poincare.L ≅ (BaseChange.ofR c ε R'
        (h.poincare.pullbackAlong ⟨pullback.fst D.toBase (specMap R R'), pullback.condition⟩)).L) ∧
      (∀ (K' : Type u) [Field K'] (t : Spec (CommRingCat.of K') ⟶ Spec (CommRingCat.of R')) (x : SchemeHomOver t (baseChange R c R')),
        Nonempty ((h'.poincare.pullbackAlong
            ⟨x.1 ≫ aj'.1, (Category.assoc _ _ _).trans ((congrArg (x.1 ≫ ·) aj'.2).trans x.2)⟩).L ≅
          (RelEffCartierDiv.ofPoint (baseChange R c R') x.1 x.2).lineBundle ⊗
            (RelEffCartierDiv.ofPoint (baseChange R c R') (t ≫ (sectionBaseChange R' ε).1)
              ((Category.assoc _ _ _).trans ((congrArg (t ≫ ·) (sectionBaseChange R' ε).2).trans (Category.comp_id t)))).idealModule)) ∧
      (sectionBaseChange R' ε).1 ≫ aj'.1 = (D.baseChange R').zeroSection ∧
      (∀ z : Pic0 K F, (pts z).1 = (pts' z).1 ≫ pullback.fst D.toBase (specMap R R')) ∧
      (∀ x y : Pic0 K F, pts (x + y) =
        (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c ε) h).mul (specMap R K) (pts x) (pts y)) ∧
      (∀ x y : Pic0 K F, pts' (x + y) =
        (RepresentsRelSubPic.relativeGroupLaw
          (P := algEquivZeroGroupCut (baseChange R c R') (sectionBaseChange R' ε)) h').mul (specMap R' K) (pts' x) (pts' y)) ∧
      ∀ (x s : {q : Spec (CommRingCat.of K) ⟶ M.C // q ≫ M.toBase = 𝟙 _}),
        s.1 ≫ e' ≫ pullback.fst (baseChange R c R') (specMap R' K) = specMap R' K ≫ (sectionBaseChange R' ε).1 →
        ∃ Dv : Divisor.degZero (K := K) (F := F),
          (Dv : Divisor K F) = Finsupp.single (M.pointEquivPlace x) 1 - Finsupp.single (M.pointEquivPlace s) 1 ∧
          (pts' (Pic0.mk Dv)).1 = x.1 ≫ e' ≫ pullback.fst (baseChange R c R') (specMap R' K) ≫ aj'.1 := by

  obtain ⟨h', hP⟩ := exists_representsRelSubPic_baseChange R c ε D h R'
  obtain ⟨aj', hajε', haj'⟩ := exists_abelJacobi_of_representsRelSubPic R' (baseChange R c R') (sectionBaseChange R' ε)
    (D.baseChange R') h'
  haveI : Smooth (D.baseChange R').toBase := by
    rw [RelativePic0Designation.baseChange_toBase]; infer_instance
  haveI : GeometricallyConnected (D.baseChange R').toBase := hgc
  obtain ⟨_, hdict⟩ := exists_pic0_equiv_points_of_representsRelSubPic_of_abelJacobi R' (baseChange R c R')
    (sectionBaseChange R' ε) (D.baseChange R') h' inferInstance hpr' inferInstance aj' hajε' haj'
  obtain ⟨pts', hadd', hnorm'⟩ := hdict K (algebraMap R' K) F M e' he'

  have hbase : specMap R' K ≫ specMap R R' = specMap R K := by
    simp only [specMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]
  let fwd : SchemeHomOver (specMap R' K) (D.baseChange R').toBase → SchemeHomOver (specMap R K) D.toBase := fun w =>
    ⟨w.1 ≫ pullback.fst D.toBase (specMap R R'), by
      rw [Category.assoc, pullback.condition, ← Category.assoc]
      erw [w.2]
      exact hbase⟩
  let bwd : SchemeHomOver (specMap R K) D.toBase → SchemeHomOver (specMap R' K) (D.baseChange R').toBase := fun w =>
    ⟨pullback.lift w.1 (specMap R' K) (by rw [w.2, hbase]), pullback.lift_snd _ _ _⟩
  have hfb : ∀ w, fwd (bwd w) = w := fun w => Subtype.ext (pullback.lift_fst _ _ _)
  have hbf : ∀ w, bwd (fwd w) = w := fun w => by
    apply Subtype.ext
    apply pullback.hom_ext
    · exact pullback.lift_fst _ _ _
    · rw [pullback.lift_snd]; exact w.2.symm
  let Φ : SchemeHomOver (specMap R' K) (D.baseChange R').toBase ≃ SchemeHomOver (specMap R K) D.toBase :=
    ⟨fwd, bwd, hbf, hfb⟩
  refine ⟨h', aj', pts', pts'.trans Φ, hP, haj', hajε', fun z => rfl, ?_, hadd', hnorm'⟩

  intro x y
  apply Subtype.ext
  show (pts' (x + y)).1 ≫ pullback.fst D.toBase (specMap R R') = _
  rw [hadd', baseChange_relativeGroupLaw_mul_compat R c ε D h R' h' hP (specMap R' K) (pts' x) (pts' y)
    ⟨(pts' x).1 ≫ pullback.fst D.toBase (specMap R R'), by rw [Category.assoc, pullback.condition, ← Category.assoc, (pts' x).2]⟩
    ⟨(pts' y).1 ≫ pullback.fst D.toBase (specMap R R'), by rw [Category.assoc, pullback.condition, ← Category.assoc, (pts' y).2]⟩
    rfl rfl]
  exact mul_val_congr _ hbase _ _ _ _ rfl rfl

theorem exists_abelJacobi_pts_of_representsRelSubPic_baseChange
    (R : Type u) [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R)) [IsProper c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (D : RelativePic0Designation R c) (h : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D)
    (hsm : Smooth D.toBase)
    (R' : Type u) [CommRing R'] [Algebra R R'] (hgc : GeometricallyConnected (D.baseChange R').toBase)
    [SmoothOfRelativeDimension 1 (baseChange R c R')] [GeometricallyIntegral (baseChange R c R')]
    (hpr' : IsProper (D.baseChange R').toBase)
    (K : Type u) [Field K] [IsAlgClosed K] [Algebra R K] [Algebra R' K] [IsScalarTower R R' K]
    (F : Type v) [Field F] [Algebra K F] [IsCurveOver K F] (M : CurveModel K F)
    (e : M.C ⟶ pullback c (specMap R K)) [IsIso e]
    (he : e ≫ pullback.snd c (specMap R K) = M.toBase) :
    ∃ (h' : RepresentsRelSubPic (baseChange R c R') (sectionBaseChange R' ε)
        (algEquivZeroCut (baseChange R c R') (sectionBaseChange R' ε)) (D.baseChange R'))
      (aj' : SchemeHomOver (baseChange R c R') (D.baseChange R').toBase)
      (aj : M.C ⟶ D.P)
      (εbar : {q : Spec (CommRingCat.of K) ⟶ M.C // q ≫ M.toBase = 𝟙 _})
      (pts : Pic0 K F ≃ SchemeHomOver (specMap R K) D.toBase),
      Nonempty (h'.poincare.L ≅ (BaseChange.ofR c ε R'
        (h.poincare.pullbackAlong ⟨pullback.fst D.toBase (specMap R R'), pullback.condition⟩)).L) ∧
      (∀ (K' : Type u) [Field K'] (t : Spec (CommRingCat.of K') ⟶ Spec (CommRingCat.of R')) (x : SchemeHomOver t (baseChange R c R')),
        Nonempty ((h'.poincare.pullbackAlong
            ⟨x.1 ≫ aj'.1, (Category.assoc _ _ _).trans ((congrArg (x.1 ≫ ·) aj'.2).trans x.2)⟩).L ≅
          (RelEffCartierDiv.ofPoint (baseChange R c R') x.1 x.2).lineBundle ⊗
            (RelEffCartierDiv.ofPoint (baseChange R c R') (t ≫ (sectionBaseChange R' ε).1)
              ((Category.assoc _ _ _).trans ((congrArg (t ≫ ·) (sectionBaseChange R' ε).2).trans (Category.comp_id t)))).idealModule)) ∧
      (sectionBaseChange R' ε).1 ≫ aj'.1 = (D.baseChange R').zeroSection ∧
      aj ≫ D.toBase = M.toBase ≫ specMap R K ∧
      εbar.1 ≫ e ≫ pullback.fst c (specMap R K) = specMap R K ≫ ε.1 ∧
      εbar.1 ≫ aj = specMap R K ≫ D.zeroSection ∧
      (∀ x y : Pic0 K F, pts (x + y) =
        (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c ε) h).mul (specMap R K) (pts x) (pts y)) ∧
      (∀ x : {q : Spec (CommRingCat.of K) ⟶ M.C // q ≫ M.toBase = 𝟙 _},
        ∃ Dv : Divisor.degZero (K := K) (F := F),
          (Dv : Divisor K F) = Finsupp.single (M.pointEquivPlace x) 1 - Finsupp.single (M.pointEquivPlace εbar) 1 ∧
          (pts (Pic0.mk Dv)).1 = x.1 ≫ aj) ∧

      (∃ k₀ : pullback c (specMap R K) ⟶ pullback c (specMap R R'),
        k₀ ≫ pullback.fst c (specMap R R') = pullback.fst c (specMap R K) ∧
        k₀ ≫ pullback.snd c (specMap R R') = pullback.snd c (specMap R K) ≫ specMap R' K ∧
        aj = e ≫ k₀ ≫ aj'.1 ≫ pullback.fst D.toBase (specMap R R')) ∧

      ∃ k : pullback c (specMap R K) ⟶ D.P, aj = e ≫ k ∧
        ∀ τ : pullback c (specMap R K) ⟶ pullback c (specMap R K),
          τ ≫ pullback.fst c (specMap R K) = pullback.fst c (specMap R K) →
          (∃ s : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of K),
            τ ≫ pullback.snd c (specMap R K) = pullback.snd c (specMap R K) ≫ s ∧ s ≫ specMap R' K = specMap R' K) →
          τ ≫ k = k := by
  have hbase : specMap R' K ≫ specMap R R' = specMap R K := by
    simp only [specMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]

  let cg : pullback c (specMap R K) ≅ pullback c (specMap R' K ≫ specMap R R') := pullback.congrHom rfl hbase.symm
  let e' : M.C ⟶ pullback (baseChange R c R') (specMap R' K) := e ≫ cg.hom ≫ (BaseChange.κ c R' (specMap R' K)).inv
  haveI : IsIso e' := inferInstance
  have hκsnd : (BaseChange.κ c R' (specMap R' K)).inv ≫ pullback.snd (baseChange R c R') (specMap R' K) =
      pullback.snd c (specMap R' K ≫ specMap R R') := by
    rw [Iso.inv_comp_eq, BaseChange.κ_hom_snd]
  have hκfst : (BaseChange.κ c R' (specMap R' K)).inv ≫ pullback.fst (baseChange R c R') (specMap R' K) ≫
      pullback.fst c (specMap R R') = pullback.fst c (specMap R' K ≫ specMap R R') := by
    rw [Iso.inv_comp_eq, BaseChange.κ_hom_fst]
  have hcgfst : cg.hom ≫ pullback.fst c (specMap R' K ≫ specMap R R') = pullback.fst c (specMap R K) := by
    simp only [cg, pullback.congrHom_hom, pullback.lift_fst, Category.comp_id]
  have hcgsnd : cg.hom ≫ pullback.snd c (specMap R' K ≫ specMap R R') = pullback.snd c (specMap R K) := by
    simp only [cg, pullback.congrHom_hom, pullback.lift_snd, Category.comp_id]
  have he' : e' ≫ pullback.snd (baseChange R c R') (specMap R' K) = M.toBase := by
    simp only [e', Category.assoc, hκsnd, hcgsnd, he]
  obtain ⟨h', aj', pts', pts, hP, haj', hajε', hpts, hadd, -, hnorm'⟩ :=
    exists_pts_of_representsRelSubPic_baseChange R c ε D h hsm R' hgc hpr' K F M e' he'

  let εpt : Spec (CommRingCat.of K) ⟶ pullback c (specMap R K) :=
    pullback.lift (specMap R K ≫ ε.1) (𝟙 _) (by rw [Category.assoc, ε.2, Category.comp_id, Category.id_comp])
  let εbar : {q : Spec (CommRingCat.of K) ⟶ M.C // q ≫ M.toBase = 𝟙 _} :=
    ⟨εpt ≫ inv e, by rw [Category.assoc, ← he, IsIso.inv_hom_id_assoc, pullback.lift_snd]⟩
  have hεbar : εbar.1 ≫ e ≫ pullback.fst c (specMap R K) = specMap R K ≫ ε.1 := by
    show (εpt ≫ inv e) ≫ e ≫ _ = _
    rw [Category.assoc, IsIso.inv_hom_id_assoc, pullback.lift_fst]

  have hb3 : pullback.fst (baseChange R c R') (specMap R' K) ≫ pullback.snd c (specMap R R') =
      pullback.snd (baseChange R c R') (specMap R' K) ≫ specMap R' K := pullback.condition
  have hεbar' : εbar.1 ≫ e' ≫ pullback.fst (baseChange R c R') (specMap R' K) = specMap R' K ≫ (sectionBaseChange R' ε).1 := by
    apply pullback.hom_ext
    · have : (specMap R' K ≫ (sectionBaseChange R' ε).1) ≫ pullback.fst c (specMap R R') = specMap R K ≫ ε.1 := by
        rw [Category.assoc, sectionBaseChange_coe_fst, ← Category.assoc, hbase]
      rw [this, ← hεbar]
      simp only [e', Category.assoc, hκfst, hcgfst]
    · have : (specMap R' K ≫ (sectionBaseChange R' ε).1) ≫ pullback.snd c (specMap R R') = specMap R' K := by
        rw [Category.assoc, sectionBaseChange_coe_snd, Category.comp_id]
      rw [this]
      show εbar.1 ≫ (e' ≫ pullback.fst (baseChange R c R') (specMap R' K)) ≫ pullback.snd c (specMap R R') = _
      have hε2 : (εpt ≫ inv e) ≫ M.toBase = 𝟙 _ := εbar.2
      rw [Category.assoc, Category.assoc, hb3, reassoc_of% he', reassoc_of% hε2]

  let aj : M.C ⟶ D.P := e' ≫ pullback.fst (baseChange R c R') (specMap R' K) ≫ aj'.1 ≫ pullback.fst D.toBase (specMap R R')
  refine ⟨h', aj', aj, εbar, pts, hP, haj', hajε', ?_, hεbar, ?_, hadd, ?_, ?_⟩
  ·
    have h1 : pullback.fst D.toBase (specMap R R') ≫ D.toBase = pullback.snd D.toBase (specMap R R') ≫ specMap R R' :=
      pullback.condition
    have h2 : aj'.1 ≫ pullback.snd D.toBase (specMap R R') = pullback.snd c (specMap R R') := aj'.2
    simp only [aj, Category.assoc, h1, reassoc_of% h2, reassoc_of% hb3, reassoc_of% he']
    conv_lhs => rw [hbase]
  ·
    have : εbar.1 ≫ aj = (εbar.1 ≫ e' ≫ pullback.fst (baseChange R c R') (specMap R' K)) ≫ aj'.1 ≫
        pullback.fst D.toBase (specMap R R') := by simp only [aj, Category.assoc]
    rw [this, hεbar', Category.assoc, reassoc_of% hajε', RelativePic0Designation.baseChange_zeroSection_fst]
    conv_lhs => rw [← Category.assoc, hbase]
  · intro x
    obtain ⟨Dv, hDv, hx⟩ := hnorm' x εbar hεbar'
    refine ⟨Dv, hDv, ?_⟩
    rw [hpts, hx]
    simp only [aj, Category.assoc]
  ·
    let k₀ : pullback c (specMap R K) ⟶ pullback c (specMap R R') :=
      cg.hom ≫ (BaseChange.κ c R' (specMap R' K)).inv ≫ pullback.fst (baseChange R c R') (specMap R' K)
    have hk₀fst : k₀ ≫ pullback.fst c (specMap R R') = pullback.fst c (specMap R K) := by
      simp only [k₀, Category.assoc, hκfst, hcgfst]
    have hk₀snd : k₀ ≫ pullback.snd c (specMap R R') = pullback.snd c (specMap R K) ≫ specMap R' K := by
      simp only [k₀, Category.assoc, hb3, reassoc_of% hκsnd, reassoc_of% hcgsnd]
    refine ⟨⟨k₀, hk₀fst, hk₀snd, by simp only [aj, e', k₀, Category.assoc]⟩, ?_⟩
    refine ⟨k₀ ≫ aj'.1 ≫ pullback.fst D.toBase (specMap R R'), by simp only [aj, e', k₀, Category.assoc], ?_⟩
    intro τ h1 ⟨s, h2, hs⟩
    suffices hτ : τ ≫ k₀ = k₀ by rw [← Category.assoc, hτ]
    apply pullback.hom_ext
    · rw [Category.assoc, hk₀fst, h1]
    · rw [Category.assoc, hk₀snd, reassoc_of% h2, hs]

end AlgebraicGeometry.RelPicard.GPTS

namespace ModularCurve
p2m_export "ModularCurve" "XHDRLevel.R XHDRLevel.ΓN XHDRModelAtP infSubgroup translation_mem_GammaH xHFunctionField xHFunctionFieldBar JH qExpFunctionFieldC arithmeticGalois galois_smul_pic0_def laurentBaseChange jqModC JZeroNeronObjectAtP JOneES.exists_transcendental_finiteDimensional_laurentBaseChange"
namespace GPTS_S4
p2m_open "ModularCurve"

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in

theorem gal_equivariance (F₀ : IntermediateField ℚ (LaurentSeries ℚ)) (R : Type) [CommRing R] [Algebra R (AlgebraicClosure ℚ)]
    (hσR : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
      (σ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ).comp (algebraMap R (AlgebraicClosure ℚ)) =
        algebraMap R (AlgebraicClosure ℚ))
    {X : Scheme.{0}} (c : X ⟶ Spec (CommRingCat.of R))
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (Mη : CurveModel (AlgebraicClosure ℚ) (laurentBaseChange (AlgebraicClosure ℚ) F₀))
    (eη : Mη.C ⟶ pullback c (Spec.map (CommRingCat.ofHom (algebraMap R (AlgebraicClosure ℚ))))) [IsIso eη]
    (heη : eη ≫ pullback.snd c _ = Mη.toBase)
    (hgal : ∀ (g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
      (x x' : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Mη.C // q ≫ Mη.toBase = 𝟙 _}),
      x'.1 ≫ eη ≫ pullback.fst c _ =
        Spec.map (CommRingCat.ofHom (g : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ)) ≫
          x.1 ≫ eη ≫ pullback.fst c _ →
      Mη.pointEquivPlace x' =
        arithmeticGalois (L := AlgebraicClosure ℚ) F₀ g • Mη.pointEquivPlace x)
    {J : Scheme.{0}} {f : J ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f)
    (k : pullback c (Spec.map (CommRingCat.ofHom (algebraMap R (AlgebraicClosure ℚ)))) ⟶ J)
    [IsCurveOver (AlgebraicClosure ℚ) (laurentBaseChange (AlgebraicClosure ℚ) F₀)]
    (pts : Pic0 (AlgebraicClosure ℚ) (laurentBaseChange (AlgebraicClosure ℚ) F₀) ≃ SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R (AlgebraicClosure ℚ)))) f)
    (hadd : ∀ x y, pts (x + y) = L.mul _ (pts x) (pts y))
    (hnorm : ∀ (x s : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Mη.C // q ≫ Mη.toBase = 𝟙 _}),
      s.1 ≫ eη ≫ pullback.fst c (Spec.map (CommRingCat.ofHom (algebraMap R (AlgebraicClosure ℚ)))) = (Spec.map (CommRingCat.ofHom (algebraMap R (AlgebraicClosure ℚ)))) ≫ ε.1 →
      ∃ D : Divisor.degZero (K := AlgebraicClosure ℚ) (F := (laurentBaseChange (AlgebraicClosure ℚ) F₀)),
        (D : Divisor (AlgebraicClosure ℚ) (laurentBaseChange (AlgebraicClosure ℚ) F₀)) =
          Finsupp.single (Mη.pointEquivPlace x) 1 - Finsupp.single (Mη.pointEquivPlace s) 1 ∧
        (pts (Pic0.mk D)).1 = x.1 ≫ eη ≫ k)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
    (hk : ∀ hσ : (Spec.map (CommRingCat.ofHom (algebraMap R (AlgebraicClosure ℚ)))) ≫ 𝟙 _ =
        Spec.map (CommRingCat.ofHom (σ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ)) ≫
          (Spec.map (CommRingCat.ofHom (algebraMap R (AlgebraicClosure ℚ)))),
      pullback.map c _ c _ (𝟙 X) (Spec.map (CommRingCat.ofHom (σ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ))) (𝟙 _)
        (by simp) hσ ≫ k = k)
    (x : Pic0 (AlgebraicClosure ℚ) (laurentBaseChange (AlgebraicClosure ℚ) F₀)) :
    (pts (σ • x)).1 = Spec.map (CommRingCat.ofHom (σ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ)) ≫ (pts x).1 := by
  have hσfix : Spec.map (CommRingCat.ofHom (σ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ)) ≫ (Spec.map (CommRingCat.ofHom (algebraMap R (AlgebraicClosure ℚ)))) = (Spec.map (CommRingCat.ofHom (algebraMap R (AlgebraicClosure ℚ)))) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    exact hσR σ

  have hinvη : inv eη ≫ Mη.toBase = pullback.snd c (Spec.map (CommRingCat.ofHom (algebraMap R (AlgebraicClosure ℚ)))) := by
    rw [IsIso.inv_comp_eq, heη]
  let toM : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R (AlgebraicClosure ℚ)))) c →
      {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Mη.C // q ≫ Mη.toBase = 𝟙 _} :=
    fun y => ⟨pullback.lift y.1 (𝟙 _) (by rw [y.2, Category.id_comp]) ≫ inv eη, by
      rw [Category.assoc, hinvη, pullback.lift_snd]⟩
  have htoM : ∀ (y : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R (AlgebraicClosure ℚ)))) c) {Z : Scheme.{0}} (k : X ⟶ Z),
      (toM y).1 ≫ eη ≫ pullback.fst c (Spec.map (CommRingCat.ofHom (algebraMap R (AlgebraicClosure ℚ)))) ≫ k = y.1 ≫ k := by
    intro y Z k
    show (pullback.lift y.1 (𝟙 _) _ ≫ inv eη) ≫ eη ≫ pullback.fst c _ ≫ k = y.1 ≫ k
    rw [Category.assoc, IsIso.inv_hom_id_assoc, pullback.lift_fst_assoc]
  have htoM₀ : ∀ (y : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R (AlgebraicClosure ℚ)))) c), (toM y).1 ≫ eη ≫ pullback.fst c (Spec.map (CommRingCat.ofHom (algebraMap R (AlgebraicClosure ℚ)))) = y.1 := by
    intro y
    simpa only [Category.comp_id] using htoM y (𝟙 X)

  let sη : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R (AlgebraicClosure ℚ)))) c := ⟨(Spec.map (CommRingCat.ofHom (algebraMap R (AlgebraicClosure ℚ)))) ≫ ε.1, by rw [Category.assoc, ε.2, Category.comp_id]⟩
  let tw : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R (AlgebraicClosure ℚ)))) c → SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R (AlgebraicClosure ℚ)))) c := fun y =>
    ⟨Spec.map (CommRingCat.ofHom (σ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ)) ≫ y.1, by rw [Category.assoc, y.2, hσfix]⟩
  have htw_s : tw sη = sη := Subtype.ext (by
    show Spec.map _ ≫ (Spec.map (CommRingCat.ofHom (algebraMap R (AlgebraicClosure ℚ)))) ≫ ε.1 = (Spec.map (CommRingCat.ofHom (algebraMap R (AlgebraicClosure ℚ)))) ≫ ε.1
    rw [← Category.assoc, hσfix])
  have hplace_tw : ∀ y : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R (AlgebraicClosure ℚ)))) c,
      Mη.pointEquivPlace (toM (tw y)) =
        arithmeticGalois (L := AlgebraicClosure ℚ) F₀ σ •
          Mη.pointEquivPlace (toM y) := by
    intro y
    apply hgal σ (toM y) (toM (tw y))
    rw [htoM₀, htoM₀]
  let ofPlace : Place (AlgebraicClosure ℚ) (laurentBaseChange (AlgebraicClosure ℚ) F₀) → SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R (AlgebraicClosure ℚ)))) c :=
    fun v => ⟨(Mη.pointEquivPlace.symm v).1 ≫ eη ≫ pullback.fst c (Spec.map (CommRingCat.ofHom (algebraMap R (AlgebraicClosure ℚ)))), by
      rw [Category.assoc, Category.assoc, pullback.condition, ← Category.assoc eη, heη, ← Category.assoc,
        (Mη.pointEquivPlace.symm v).2, Category.id_comp]⟩
  have hplace_ofPlace : ∀ v, Mη.pointEquivPlace (toM (ofPlace v)) = v := by
    intro v
    have key : (toM (ofPlace v)).1 ≫ eη = (Mη.pointEquivPlace.symm v).1 ≫ eη := by
      apply pullback.hom_ext
      · rw [Category.assoc, Category.assoc]; exact htoM₀ (ofPlace v)
      · simp only [Category.assoc, heη, (Mη.pointEquivPlace.symm v).2]
        exact (toM (ofPlace v)).2
    have : toM (ofPlace v) = Mη.pointEquivPlace.symm v :=
      Subtype.ext (by simpa using congrArg (· ≫ inv eη) key)
    rw [this, Equiv.apply_symm_apply]

  set g := arithmeticGalois (L := AlgebraicClosure ℚ) F₀ σ with hg
  let w₀ : Place (AlgebraicClosure ℚ) (laurentBaseChange (AlgebraicClosure ℚ) F₀) := Mη.pointEquivPlace (toM sη)
  have hs_cond : (toM sη).1 ≫ eη ≫ pullback.fst c (Spec.map (CommRingCat.ofHom (algebraMap R (AlgebraicClosure ℚ)))) = (Spec.map (CommRingCat.ofHom (algebraMap R (AlgebraicClosure ℚ)))) ≫ ε.1 := htoM₀ sη
  have hw₀ : g • w₀ = w₀ := by
    have := hplace_tw sη
    rw [htw_s] at this
    exact this.symm
  have hdeg1 : ∀ v : Place (AlgebraicClosure ℚ) (laurentBaseChange (AlgebraicClosure ℚ) F₀), v.deg = 1 :=
    fun v => IsCurveOver.deg_eq_one_of_isAlgClosed v

  have hΔmem : ∀ v : Place (AlgebraicClosure ℚ) (laurentBaseChange (AlgebraicClosure ℚ) F₀),
      Finsupp.single v (1 : ℤ) - Finsupp.single w₀ 1 ∈
        Divisor.degZero (K := AlgebraicClosure ℚ) (F := (laurentBaseChange (AlgebraicClosure ℚ) F₀)) := by
    intro v
    rw [Divisor.mem_degZero, map_sub, Divisor.degree_single, Divisor.degree_single, hdeg1, hdeg1]
    simp
  let Δ : Place (AlgebraicClosure ℚ) (laurentBaseChange (AlgebraicClosure ℚ) F₀) →
      Divisor.degZero (K := AlgebraicClosure ℚ) (F := (laurentBaseChange (AlgebraicClosure ℚ) F₀)) :=
    fun v => ⟨_, hΔmem v⟩

  have hgen : ∀ v, (pts (σ • Pic0.mk (Δ v))).1 = Spec.map (CommRingCat.ofHom (σ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ)) ≫ (pts (Pic0.mk (Δ v))).1 := by
    intro v
    obtain ⟨D₁, hD₁, hpts₁⟩ := hnorm (toM (ofPlace v)) (toM sη) hs_cond
    rw [hplace_ofPlace] at hD₁
    obtain ⟨D₂, hD₂, hpts₂⟩ := hnorm (toM (tw (ofPlace v))) (toM sη) hs_cond
    rw [hplace_tw, hplace_ofPlace] at hD₂
    have hΔ1 : Δ v = D₁ := Subtype.ext hD₁.symm
    have hsmul : σ • Pic0.mk (Δ v) = Pic0.mk D₂ := by
      rw [galois_smul_pic0_def, SemilinearAut.pic0_smul_mk]
      congr 1
      apply Subtype.ext
      rw [SemilinearAut.coe_degZeroSMulHom, hD₂, ← hg]
      show g • (Finsupp.single v (1 : ℤ) - Finsupp.single w₀ 1) = _
      rw [smul_sub, SemilinearAut.smul_single, SemilinearAut.smul_single, hw₀]
    rw [hsmul, hpts₂, hΔ1, hpts₁]

    have hσ' : (Spec.map (CommRingCat.ofHom (algebraMap R (AlgebraicClosure ℚ)))) ≫ 𝟙 _ =
        Spec.map (CommRingCat.ofHom (σ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ)) ≫
          (Spec.map (CommRingCat.ofHom (algebraMap R (AlgebraicClosure ℚ)))) := by rw [Category.comp_id, hσfix]
    have heq : ∀ y : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R (AlgebraicClosure ℚ)))) c,
        (toM (tw y)).1 ≫ eη ≫
          pullback.map c _ c _ (𝟙 X) (Spec.map (CommRingCat.ofHom (σ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ))) (𝟙 _)
            (by simp) hσ' =
        Spec.map (CommRingCat.ofHom (σ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ)) ≫ (toM y).1 ≫ eη := by
      intro y
      have e1 := htoM₀ (tw y)
      have e2 := htoM₀ y
      have e3 : ∀ z : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R (AlgebraicClosure ℚ)))) c,
          (toM z).1 ≫ eη ≫ pullback.snd c _ = 𝟙 _ := fun z => by rw [heη]; exact (toM z).2
      apply pullback.hom_ext
      · simp only [Category.assoc, pullback.lift_fst, Category.comp_id, e1, e2]
        rfl
      · simp only [Category.assoc, pullback.lift_snd, reassoc_of% (e3 (tw y)), e3 y, Category.comp_id]
    conv_lhs => rw [← hk hσ']
    rw [reassoc_of% (heq (ofPlace v))]

  letI := L.pointGroup (Spec.map (CommRingCat.ofHom (algebraMap R (AlgebraicClosure ℚ))))
  have hmul_def : ∀ a b : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R (AlgebraicClosure ℚ)))) f, a * b = L.mul _ a b := fun _ _ => rfl
  let Φ₁ : Pic0 (AlgebraicClosure ℚ) (laurentBaseChange (AlgebraicClosure ℚ) F₀) →+ Additive (SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R (AlgebraicClosure ℚ)))) f) :=
    AddMonoidHom.mk' (fun y => Additive.ofMul (pts (σ • y))) (by
      intro a b
      apply Additive.toMul.injective
      show pts (σ • (a + b)) = pts (σ • a) * pts (σ • b)
      rw [smul_add, hadd, hmul_def])
  let Φ₂ : Pic0 (AlgebraicClosure ℚ) (laurentBaseChange (AlgebraicClosure ℚ) F₀) →+ Additive (SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R (AlgebraicClosure ℚ)))) f) :=
    AddMonoidHom.mk' (fun y => Additive.ofMul (GoodReductionJacobian.schemeHomOverComp (Spec.map (CommRingCat.ofHom (σ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ))) hσfix (pts y))) (by
      intro a b
      apply Additive.toMul.injective
      show GoodReductionJacobian.schemeHomOverComp _ hσfix (pts (a + b)) =
        GoodReductionJacobian.schemeHomOverComp _ hσfix (pts a) * GoodReductionJacobian.schemeHomOverComp _ hσfix (pts b)
      rw [hadd, L.mul_natural, hmul_def])
  suffices hΦ : Φ₁ = Φ₂ by
    have := congrArg (fun Φ : Pic0 (AlgebraicClosure ℚ) (laurentBaseChange (AlgebraicClosure ℚ) F₀) →+ Additive (SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R (AlgebraicClosure ℚ)))) f) => (Additive.toMul (Φ x)).1) hΦ
    exact this

  have hclos : AddSubgroup.closure (Set.range fun v => Pic0.mk (Δ v)) = ⊤ := by
    rw [eq_top_iff]
    rintro y -
    obtain ⟨D, rfl⟩ := Pic0.mk_surjective y
    have hdegD : Divisor.degree (D : Divisor (AlgebraicClosure ℚ) (laurentBaseChange (AlgebraicClosure ℚ) F₀)) = 0 := D.2

    have hdec : (D : Divisor (AlgebraicClosure ℚ) (laurentBaseChange (AlgebraicClosure ℚ) F₀)) =
        (D : Divisor (AlgebraicClosure ℚ) (laurentBaseChange (AlgebraicClosure ℚ) F₀)).sum
          (fun v n => n • (Finsupp.single v (1 : ℤ) - Finsupp.single w₀ 1)) := by
      have hsum1 : (D : Divisor (AlgebraicClosure ℚ) (laurentBaseChange (AlgebraicClosure ℚ) F₀)).sum
          (fun v n => n • Finsupp.single v (1 : ℤ)) = D := by
        conv_rhs => rw [← Finsupp.sum_single (D : Divisor (AlgebraicClosure ℚ) (laurentBaseChange (AlgebraicClosure ℚ) F₀))]
        apply Finsupp.sum_congr
        intro v _
        rw [Finsupp.smul_single, smul_eq_mul, mul_one]
      have hsum2 : (D : Divisor (AlgebraicClosure ℚ) (laurentBaseChange (AlgebraicClosure ℚ) F₀)).sum
          (fun v n => n • Finsupp.single w₀ (1 : ℤ)) = 0 := by
        simp only [Finsupp.sum, ← Finset.sum_smul]
        have : (∑ v ∈ (D : Divisor (AlgebraicClosure ℚ) (laurentBaseChange (AlgebraicClosure ℚ) F₀)).support,
            (D : Divisor (AlgebraicClosure ℚ) (laurentBaseChange (AlgebraicClosure ℚ) F₀)) v) =
            Divisor.degree (D : Divisor (AlgebraicClosure ℚ) (laurentBaseChange (AlgebraicClosure ℚ) F₀)) := by
          conv_rhs => rw [← Finsupp.sum_single (D : Divisor (AlgebraicClosure ℚ) (laurentBaseChange (AlgebraicClosure ℚ) F₀)), map_finsuppSum]
          simp only [Finsupp.sum, Divisor.degree_single, hdeg1, Nat.cast_one, mul_one]
        rw [this, hdegD, zero_smul]
      simp only [smul_sub, Finsupp.sum_sub, hsum1, hsum2, sub_zero]
    let mkHom : Divisor.degZero (K := AlgebraicClosure ℚ) (F := (laurentBaseChange (AlgebraicClosure ℚ) F₀)) →+ Pic0 (AlgebraicClosure ℚ) (laurentBaseChange (AlgebraicClosure ℚ) F₀) :=
      { toFun := Pic0.mk, map_zero' := Pic0.mk_zero, map_add' := Pic0.mk_add }
    have hD' : D = ∑ v ∈ (D : Divisor (AlgebraicClosure ℚ) (laurentBaseChange (AlgebraicClosure ℚ) F₀)).support,
        (D : Divisor (AlgebraicClosure ℚ) (laurentBaseChange (AlgebraicClosure ℚ) F₀)) v • Δ v := by
      apply Subtype.ext
      rw [AddSubmonoidClass.coe_finsetSum]
      simp only [AddSubgroupClass.coe_zsmul]
      simpa only [Finsupp.sum] using hdec
    have hmk : Pic0.mk D = ∑ v ∈ (D : Divisor (AlgebraicClosure ℚ) (laurentBaseChange (AlgebraicClosure ℚ) F₀)).support,
        (D : Divisor (AlgebraicClosure ℚ) (laurentBaseChange (AlgebraicClosure ℚ) F₀)) v • Pic0.mk (Δ v) := by
      show mkHom D = ∑ v ∈ _, _ • mkHom (Δ v)
      conv_lhs => rw [hD']
      rw [map_sum]
      simp only [map_zsmul]
    rw [hmk]
    exact AddSubgroup.sum_mem _ fun v _ => AddSubgroup.zsmul_mem _ (AddSubgroup.subset_closure (Set.mem_range_self v)) _
  apply AddMonoidHom.eq_of_eqOn_dense hclos
  rintro _ ⟨v, rfl⟩
  apply Additive.toMul.injective
  apply Subtype.ext
  exact hgen v

end ModularCurve.GPTS_S4

namespace ModularCurve
p2m_export "ModularCurve" "XHDRLevel.R XHDRLevel.ΓN XHDRModelAtP infSubgroup translation_mem_GammaH xHFunctionField xHFunctionFieldBar JH qExpFunctionFieldC arithmeticGalois galois_smul_pic0_def laurentBaseChange jqModC JZeroNeronObjectAtP JOneES.exists_transcendental_finiteDimensional_laurentBaseChange"
namespace GPTS
p2m_open "ModularCurve"

open AlgebraicGeometry.RelPicard.GPTS

theorem ringHom_comp_algebraMap_eq (p : ℕ) (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    (σ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ).comp (algebraMap (XHDRLevel.R p) (AlgebraicClosure ℚ)) =
      algebraMap (XHDRLevel.R p) (AlgebraicClosure ℚ) := by
  ext q
  change σ (algebraMap (XHDRLevel.R p) (AlgebraicClosure ℚ) q) = algebraMap (XHDRLevel.R p) (AlgebraicClosure ℚ) q
  rw [IsScalarTower.algebraMap_apply (XHDRLevel.R p) ℚ (AlgebraicClosure ℚ)]
  exact σ.commutes _

theorem isCurveOver_xHFunctionFieldBar (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) :
    IsCurveOver (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) := by
  obtain ⟨x, hx, hfd⟩ :=
    ModularCurve.JOneES.exists_transcendental_finiteDimensional_laurentBaseChange
      (AlgebraicClosure ℚ) (CohCarrier.GammaH M H) (translation_mem_GammaH M H)
  exact AlgebraicCurve.isCurveOver_of_transcendental_of_perfectField hx hfd

set_option maxHeartbeats 3200000 in

theorem exists_abelJacobi_pts_galois (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ)
    {X : Scheme.{0}} (c : X ⟶ Spec (CommRingCat.of (XHDRLevel.R p))) [IsProper c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of (XHDRLevel.R p)))) c)
    (D : RelativePic0Designation (XHDRLevel.R p) c) (hD : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D)
    (hsm : Smooth D.toBase) (hgcQ : GeometricallyConnected (D.baseChange ℚ).toBase)
    (hprQ : IsProper (D.baseChange ℚ).toBase)
    [SmoothOfRelativeDimension 1 (baseChange (XHDRLevel.R p) c ℚ)] [GeometricallyIntegral (baseChange (XHDRLevel.R p) c ℚ)]
    (Mη : CurveModel (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H))
    (eη : Mη.C ⟶ pullback c (genPt p)) [IsIso eη]
    (heη : eη ≫ pullback.snd c (genPt p) = Mη.toBase)
    (hgal : ∀ (g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
      (x x' : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Mη.C // q ≫ Mη.toBase = 𝟙 _}),
      x'.1 ≫ eη ≫ pullback.fst c _ =
        Spec.map (CommRingCat.ofHom (g : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ)) ≫ x.1 ≫ eη ≫ pullback.fst c _ →
      Mη.pointEquivPlace x' =
        arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) g • Mη.pointEquivPlace x) :
    ∃ (h' : RepresentsRelSubPic (baseChange (XHDRLevel.R p) c ℚ) (sectionBaseChange ℚ ε)
        (algEquivZeroCut (baseChange (XHDRLevel.R p) c ℚ) (sectionBaseChange ℚ ε)) (D.baseChange ℚ))
      (aj' : SchemeHomOver (baseChange (XHDRLevel.R p) c ℚ) (D.baseChange ℚ).toBase)
      (aj : Mη.C ⟶ D.P)
      (εbar : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Mη.C // q ≫ Mη.toBase = 𝟙 _})
      (pts : JH M H ≃ SchemeHomOver (genPt p) D.toBase),
      Nonempty (h'.poincare.L ≅ (BaseChange.ofR c ε ℚ
        (hD.poincare.pullbackAlong ⟨pullback.fst D.toBase (specMap (XHDRLevel.R p) ℚ), pullback.condition⟩)).L) ∧
      (∀ (K' : Type) [Field K'] (t : Spec (CommRingCat.of K') ⟶ Spec (CommRingCat.of ℚ)) (x : SchemeHomOver t (baseChange (XHDRLevel.R p) c ℚ)),
        Nonempty ((h'.poincare.pullbackAlong
            ⟨x.1 ≫ aj'.1, (Category.assoc _ _ _).trans ((congrArg (x.1 ≫ ·) aj'.2).trans x.2)⟩).L ≅
          (RelEffCartierDiv.ofPoint (baseChange (XHDRLevel.R p) c ℚ) x.1 x.2).lineBundle ⊗
            (RelEffCartierDiv.ofPoint (baseChange (XHDRLevel.R p) c ℚ) (t ≫ (sectionBaseChange ℚ ε).1)
              ((Category.assoc _ _ _).trans ((congrArg (t ≫ ·) (sectionBaseChange ℚ ε).2).trans (Category.comp_id t)))).idealModule)) ∧
      (sectionBaseChange ℚ ε).1 ≫ aj'.1 = (D.baseChange ℚ).zeroSection ∧
      (∃ k₀ : pullback c (genPt p) ⟶ pullback c (specMap (XHDRLevel.R p) ℚ),
        k₀ ≫ pullback.fst c (specMap (XHDRLevel.R p) ℚ) = pullback.fst c (genPt p) ∧
        k₀ ≫ pullback.snd c (specMap (XHDRLevel.R p) ℚ) = pullback.snd c (genPt p) ≫ specMap ℚ (AlgebraicClosure ℚ) ∧
        aj = eη ≫ k₀ ≫ aj'.1 ≫ pullback.fst D.toBase (specMap (XHDRLevel.R p) ℚ)) ∧
      aj ≫ D.toBase = Mη.toBase ≫ genPt p ∧
      εbar.1 ≫ eη ≫ pullback.fst c (genPt p) = genPt p ≫ ε.1 ∧
      εbar.1 ≫ aj = genPt p ≫ D.zeroSection ∧
      (∀ x y : JH M H, pts (x + y) =
        (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c ε) hD).mul (genPt p) (pts x) (pts y)) ∧
      (∀ x : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Mη.C // q ≫ Mη.toBase = 𝟙 _},
        ∃ Dv : Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar M H)),
          (Dv : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) =
            Finsupp.single (Mη.pointEquivPlace x) 1 - Finsupp.single (Mη.pointEquivPlace εbar) 1 ∧
          (pts (Pic0.mk Dv)).1 = x.1 ≫ aj) ∧
      ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (x : JH M H),
        (pts (σ • x)).1 = Spec.map (CommRingCat.ofHom (σ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ)) ≫ (pts x).1 := by
  haveI : IsCurveOver (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) := isCurveOver_xHFunctionFieldBar M H
  obtain ⟨h', aj', aj, εbar, pts, hP, haj', hajε', hajover, hεbar, hajs, hadd, hnorm, hk₀, k, hk, hkinv⟩ :=
    exists_abelJacobi_pts_of_representsRelSubPic_baseChange (XHDRLevel.R p) c ε D hD hsm ℚ hgcQ hprQ (AlgebraicClosure ℚ)
      ↥(xHFunctionFieldBar M H) Mη eη heη
  refine ⟨h', aj', aj, εbar, pts, hP, haj', hajε', hk₀, hajover, hεbar, hajs, hadd, hnorm, ?_⟩
  intro σ x

  have hsec : ∀ s : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Mη.C // q ≫ Mη.toBase = 𝟙 _},
      s.1 ≫ eη ≫ pullback.fst c (genPt p) = genPt p ≫ ε.1 → s = εbar := by
    intro s hs
    apply Subtype.ext
    rw [← cancel_mono eη]
    apply pullback.hom_ext
    · rw [Category.assoc, Category.assoc, hs, hεbar]
    · rw [Category.assoc, Category.assoc, heη, s.2, εbar.2]
  refine ModularCurve.GPTS_S4.gal_equivariance (xHFunctionField M H) (XHDRLevel.R p) (ringHom_comp_algebraMap_eq p) c ε Mη eη heη hgal
    (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c ε) hD) k pts hadd ?_ σ ?_ x
  · intro y s hs
    obtain rfl := hsec s hs
    obtain ⟨Dv, hDv, hy⟩ := hnorm y
    exact ⟨Dv, hDv, by rw [hy, hk]⟩
  · intro hσ
    apply hkinv
    · rw [pullback.lift_fst, Category.comp_id]
    · refine ⟨Spec.map (CommRingCat.ofHom (σ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ)), pullback.lift_snd _ _ _, ?_⟩
      rw [specMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
      congr 2
      ext q
      exact σ.commutes q

end ModularCurve.GPTS

theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) [NeZero (M / p)]
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)
    [IsProper (toBase p (ΓN p M H hpM) hj)]

    [SmoothOfRelativeDimension 1 (baseChange (R p) (toBase p (ΓN p M H hpM) hj) ℚ)]
    [GeometricallyIntegral (baseChange (R p) (toBase p (ΓN p M H hpM) hj) ℚ)]

    (Meta₀ : CurveModel (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)))
    (eeta₀ : Meta₀.C ⟶ pullback (toBase p (XHDRLevel.ΓN p M H hpM) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ))))) [IsIso eeta₀]
    (heeta₀ : eeta₀ ≫ pullback.snd _ _ = Meta₀.toBase)
    (D₀ : RelativePic0Designation (R p) (toBase p (ΓN p M H hpM) hj))
    (hD₀ : RepresentsRelSubPic (toBase p (ΓN p M H hpM) hj) (NeronModelInfra.schemeHomOverComp 𝔛.εinf 𝔛.π) (algEquivZeroCut (toBase p (ΓN p M H hpM) hj) (NeronModelInfra.schemeHomOverComp 𝔛.εinf 𝔛.π)) D₀)
    (hsm₀ : Smooth D₀.toBase)

    (hprQ₀ : IsProper (pullback.snd D₀.toBase (Spec.map (CommRingCat.ofHom (algebraMap (R p) ℚ)))))
    (hgcQ₀ : GeometricallyConnected (pullback.snd D₀.toBase (Spec.map (CommRingCat.ofHom (algebraMap (R p) ℚ))))) :
    ∃ (hDQ : RepresentsRelSubPic (baseChange (R p) (toBase p (ΓN p M H hpM) hj) ℚ) (sectionBaseChange ℚ (NeronModelInfra.schemeHomOverComp 𝔛.εinf 𝔛.π))
          (algEquivZeroCut (baseChange (R p) (toBase p (ΓN p M H hpM) hj) ℚ) (sectionBaseChange ℚ (NeronModelInfra.schemeHomOverComp 𝔛.εinf 𝔛.π))) (D₀.baseChange ℚ))
      (ajQ : SchemeHomOver (baseChange (R p) (toBase p (ΓN p M H hpM) hj) ℚ) (D₀.baseChange ℚ).toBase)
      (kQ : pullback (toBase p (ΓN p M H hpM) hj) (genPt p) ⟶ pullback (toBase p (ΓN p M H hpM) hj) (specMap (R p) ℚ))
      (ajbar : Meta₀.C ⟶ D₀.P)
      (εbar : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Meta₀.C // q ≫ Meta₀.toBase = 𝟙 _})
      (pts : JH (M / p) (infSubgroup p M H hpM) ≃ SchemeHomOver (genPt p) D₀.toBase),

      Nonempty (hDQ.poincare.L ≅ (BaseChange.ofR (toBase p (ΓN p M H hpM) hj) (NeronModelInfra.schemeHomOverComp 𝔛.εinf 𝔛.π) ℚ
        (hD₀.poincare.pullbackAlong ⟨pullback.fst D₀.toBase (specMap (R p) ℚ), pullback.condition⟩)).L) ∧

      (sectionBaseChange ℚ (NeronModelInfra.schemeHomOverComp 𝔛.εinf 𝔛.π)).1 ≫ ajQ.1 = (D₀.baseChange ℚ).zeroSection ∧
      (∀ (K : Type) [Field K] (t : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of ℚ))
          (x : SchemeHomOver t (baseChange (R p) (toBase p (ΓN p M H hpM) hj) ℚ)),
        Nonempty ((hDQ.poincare.pullbackAlong
            ⟨x.1 ≫ ajQ.1, (Category.assoc _ _ _).trans ((congrArg (x.1 ≫ ·) ajQ.2).trans x.2)⟩).L ≅
          (RelEffCartierDiv.ofPoint (baseChange (R p) (toBase p (ΓN p M H hpM) hj) ℚ) x.1 x.2).lineBundle ⊗
            (RelEffCartierDiv.ofPoint (baseChange (R p) (toBase p (ΓN p M H hpM) hj) ℚ) (t ≫ (sectionBaseChange ℚ (NeronModelInfra.schemeHomOverComp 𝔛.εinf 𝔛.π)).1)
              ((Category.assoc _ _ _).trans ((congrArg (t ≫ ·) (sectionBaseChange ℚ (NeronModelInfra.schemeHomOverComp 𝔛.εinf 𝔛.π)).2).trans
                (Category.comp_id t)))).idealModule)) ∧

      kQ ≫ pullback.fst (toBase p (ΓN p M H hpM) hj) (specMap (R p) ℚ) = pullback.fst (toBase p (ΓN p M H hpM) hj) (genPt p) ∧
      kQ ≫ pullback.snd (toBase p (ΓN p M H hpM) hj) (specMap (R p) ℚ) = pullback.snd (toBase p (ΓN p M H hpM) hj) (genPt p) ≫ specMap ℚ (AlgebraicClosure ℚ) ∧

      ajbar = eeta₀ ≫ kQ ≫ ajQ.1 ≫ pullback.fst D₀.toBase (specMap (R p) ℚ) ∧
      ajbar ≫ D₀.toBase = Meta₀.toBase ≫ genPt p ∧
      εbar.1 ≫ eeta₀ ≫ pullback.fst (toBase p (ΓN p M H hpM) hj) (genPt p) = genPt p ≫ 𝔛.εinf.1 ≫ 𝔛.π.1 ∧
      εbar.1 ≫ ajbar = genPt p ≫ D₀.zeroSection ∧

      (∀ x y : JH (M / p) (infSubgroup p M H hpM),
        pts (x + y) = (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hD₀).mul _ (pts x) (pts y)) ∧

      (∀ (x s : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Meta₀.C // q ≫ Meta₀.toBase = 𝟙 _}),
        s.1 ≫ eeta₀ ≫ pullback.fst (toBase p (ΓN p M H hpM) hj) (genPt p) = genPt p ≫ 𝔛.εinf.1 ≫ 𝔛.π.1 →
        ∃ Dv : Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))),
          (Dv : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) =
            Finsupp.single (Meta₀.pointEquivPlace x) 1 - Finsupp.single (Meta₀.pointEquivPlace s) 1 ∧
          (pts (Pic0.mk Dv)).1 = x.1 ≫ ajbar) := by

  have hprQ' : IsProper (D₀.baseChange ℚ).toBase := hprQ₀
  have hgcQ' : GeometricallyConnected (D₀.baseChange ℚ).toBase := hgcQ₀
  haveI : IsCurveOver (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) :=
    ModularCurve.GPTS.isCurveOver_xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)
  obtain ⟨h', aj', aj, εbar, pts, hP, haj', hajε', hajover, hεbar, hajs, hadd, hnorm, ⟨k₀, hk₀₁, hk₀₂, hajk⟩, k, hk, hkinv⟩ :=
    AlgebraicGeometry.RelPicard.GPTS.exists_abelJacobi_pts_of_representsRelSubPic_baseChange (XHDRLevel.R p)
      (toBase p (ΓN p M H hpM) hj) (NeronModelInfra.schemeHomOverComp 𝔛.εinf 𝔛.π) D₀ hD₀ hsm₀ ℚ hgcQ' hprQ' (AlgebraicClosure ℚ)
      ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) Meta₀ eeta₀ heeta₀

  have hsec : ∀ s : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Meta₀.C // q ≫ Meta₀.toBase = 𝟙 _},
      s.1 ≫ eeta₀ ≫ pullback.fst (toBase p (ΓN p M H hpM) hj) (genPt p) = genPt p ≫ 𝔛.εinf.1 ≫ 𝔛.π.1 → s = εbar := by
    intro s hs
    apply Subtype.ext
    rw [← cancel_mono eeta₀]
    apply pullback.hom_ext
    · rw [Category.assoc, Category.assoc, hs, hεbar]; rfl
    · rw [Category.assoc, Category.assoc, heeta₀, s.2, εbar.2]
  refine ⟨h', aj', k₀, aj, εbar, pts, hP, hajε', haj', hk₀₁, hk₀₂, hajk, hajover, ?_, hajs, hadd, ?_⟩
  · exact hεbar
  · intro x s hs
    obtain rfl := hsec s hs
    exact hnorm x

#print axioms solution

end S_ModularCurve_XHDRModelAtP_exists_representsRelSubPic_abelJacobi_pts_levelN_of_representsRelSubPic
end P2MW
export P2MW.S_ModularCurve_XHDRModelAtP_exists_representsRelSubPic_abelJacobi_pts_levelN_of_representsRelSubPic (solution)
