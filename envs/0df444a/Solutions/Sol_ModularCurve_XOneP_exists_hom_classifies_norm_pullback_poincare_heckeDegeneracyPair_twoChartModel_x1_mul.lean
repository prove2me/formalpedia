-- Prove2me | solution 1 for ModularCurve.XOneP.exists_hom_classifies_norm_pullback_poincare_heckeDegeneracyPair_twoChartModel_x1_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/0dc912c3-65e8-5728-a597-70a62c6e58d2

import Mathlib
import Definitions.Def_ModularCurve_TwoChartModel
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_JOnePGeom
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_JacJ1Iface
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicGeometry_RelativePic0DesignationBaseChange
import Definitions.Def_AlgebraicGeometry_RelPicardPullback
import Definitions.Def_AlgebraicGeometry_ModulesRigidify
import Definitions.Def_AlgebraicGeometry_ModulesNormModule
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_ModularCurve_JOnePOpsV2
import Definitions.Def_ModularCurve_X1HeckeModule
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_RelSubPicGroup
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_AlgebraicGeometry_RelSubPicBaseChange
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivOfPoint
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_AlgebraicGeometry_RigidifiedLineBundleOfInvertible
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import Theorems.Thm_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_exists_hom_classifies_norm_pullback_poincare_of_twoGluedCurves_of_mem_of_ringKrullDim_le_one
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_norm_isInvertible_tensor_pullback_normModule_of_isFinite_of_isIntegrallyClosed
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_isIntegral
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_finiteType_chartAlgFin_and_chartAlgInf
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_locallyOfFiniteType_toBase
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_isIntegrallyClosed_stalk
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_isIntegrallyClosed_sections_of_isAffineOpen
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_geometricallyIntegral_baseChange_toBase_of_intermediateField_laurentSeries
import Theorems.Thm_ModularCurve_finiteDimensional_adjoin_of_coe_eq_coeffEmb_jq_of_eq_laurentBaseChange
import Theorems.Thm_ModularCurve_transcendental_of_coe_eq_coeffEmb_jq
import Theorems.Thm_AlgebraicGeometry_isIntegral_pullback_and_isIntegral_pullback_fst_comp_of_smooth_of_geometricallyConnected_pullback_snd_specMap
import Theorems.Thm_AlgebraicGeometry_isIntegrallyClosed_sections_of_smooth_of_forall_isIntegrallyClosed_sections
import Theorems.Thm_AlgebraicGeometry_SmoothOfRelativeDimension_topologicalKrullDim_le
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XOneP_exists_hom_classifies_norm_pullback_poincare_heckeDegeneracyPair_twoChartModel_x1_mul
p2m_attr_erase "instance" "AlgebraicGeometry.OModulePresheaf.isScalarTower AlgebraicGeometry.Scheme.OrderedAffineCover.instLinearOrder AlgebraicGeometry.OModulePresheaf.module AlgebraicGeometry.Scheme.OrderedAffineCover.instFintype AlgebraicGeometry.Scheme.OrderedAffineCover.instFintypeIdx AlgebraicGeometry.OModulePresheaf.addCommGroup AlgebraicGeometry.Scheme.OrderedAffineCover.instDecidableEqIdx AlgebraicGeometry.OModulePresheaf.moduleSections AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup"
p2m_attr_erase "instance" "ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instNeg AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulInt AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAddCommGroup AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAdd AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSub AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulNat AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instZero AlgebraicGeometry.RelEffCartierDiv.subsingleton_of_degree_zero AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion"
p2m_attr_erase "instance" "ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion SheafOfModules.isIso_ihomModelToIhom AlgebraicGeometry.Scheme.Modules.GlueOfCocycle.instSMulCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensSubtypeForallMinMemAddSubgroupFamilies AlgebraicGeometry.Scheme.Modules.GlueOfCocycle.instModulePreGlue AlgebraicGeometry.Scheme.Modules.GlueOfCocycle.instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensSubtypeForallMinMemAddSubgroupFamilies"
p2m_attr_erase "simp" "PresheafOfModules.pushforwardCongr_inv_app_app_apply PresheafOfModules.pushforwardNatTrans_app_app_apply PresheafOfModules.pushforwardCongr_hom_app_app_apply AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app TwoChartCech.Mumford.dK_apply TwoChartCech.Mumford.ι0_apply TwoChartCech.Mumford.ι1_apply TwoChartCech.KerCoprod.dK_apply TwoChartCech.KerCoprod.ι1_apply TwoChartCech.KerCoprod.ι0_apply AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ AlgebraicGeometry.Scheme.Modules.toUnitSection_ofUnitSection AlgebraicGeometry.Scheme.Modules.pullbackSection_def AlgebraicGeometry.Scheme.Modules.ofUnitSection_toUnitSection AlgebraicGeometry.RelPicard.thetaBundle_def AlgebraicGeometry.RelPicard.picardBundle_def AlgebraicGeometry.Scheme.OrderedAffineCover.mk.injEq AlgebraicGeometry.OModulePresheaf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.mk.injEq AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app"
p2m_attr_erase "simp" "AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq AlgebraicGeometry.RelPicard.fst_toProdSpec AlgebraicGeometry.RelPicard.toProdSpec_fst_assoc"
p2m_attr_erase "simp" "AlgebraicGeometry.RelPicard.pointsSubBasepointModule_cons AlgebraicGeometry.RelPicard.pointsSubBasepointModule_nil AlgebraicGeometry.RelPicard.fst_toProdSpec_assoc AlgebraicGeometry.RelPicard.toProdSpec_fst AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.sub_app AlgebraicGeometry.Scheme.IdealSheafData.sres_sresTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.add_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.sizeOf_spec AlgebraicGeometry.Scheme.IdealSheafData.coe_resLE AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.smul_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_ofLE_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.ideal_range AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zero_app AlgebraicGeometry.Scheme.IdealSheafData.sres_sres AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.comp_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.neg_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.id_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_mulRight_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.nsmul_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.injEq AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zsmul_app AlgebraicGeometry.prodKerGraph_one AlgebraicGeometry.fibrePowOver.proj_comp AlgebraicGeometry.prodKerGraph_zero AlgebraicGeometry.RelEffCartierDiv.empty_I AlgebraicGeometry.fibrePowOver.proj_comp_assoc AlgebraicCurve.SymmetricPowerPackage.mk.sizeOf_spec AlgebraicCurve.SymmetricPowerPackage.mk.injEq AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.coe_cechH0Equiv_apply AlgebraicCurve.cechH1ToH1_mk AlgebraicCurve.lSpaceOn_univ AlgebraicCurve.lSpaceOn_empty"
p2m_attr_erase "simp" "AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint"
p2m_attr_erase "simp" "AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom SheafOfModules.ihomSectionsEquivFamily_unit AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply SheafOfModules.ihomEval_unit_app AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply SheafOfModules.unit_ihomSectionsEquivFamily AlgebraicGeometry.Scheme.Modules.familyOfHom_app AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add AlgebraicGeometry.SmoothProperCurve.FiniteMapData.twoAffineOpenCover_U1 AlgebraicGeometry.SmoothProperCurve.FiniteMapData.mk.injEq AlgebraicGeometry.SmoothProperCurve.FiniteMapData.mk.sizeOf_spec AlgebraicGeometry.SmoothProperCurve.FiniteMapData.twoAffineOpenCover_U0 AlgebraicGeometry.Scheme.Modules.glueComponent_glueMk AlgebraicGeometry.Scheme.Modules.UnitCocycle.mk.injEq AlgebraicGeometry.Scheme.Modules.UnitCocycle.mk.sizeOf_spec AlgebraicGeometry.Scheme.Modules.ProjPresentation.mk.injEq AlgebraicGeometry.Scheme.Modules.ProjPresentation.mk.sizeOf_spec ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg RegularLocalRingQuotientAscent.dualNumberFst_apply"

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra GoodReductionJacobian AlgebraicGeometry.SmoothProperCurve AlgebraicCurve"

open scoped MatrixGroups

namespace R1AB31

theorem isOpenImmersion_specMap_fractionRing (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    (L : Type) [Field L] [Algebra A L] [IsFractionRing A L] :
    IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap A L))) := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible A
  have hinj : Function.Injective (algebraMap A L) := IsFractionRing.injective A L
  haveI : IsLocalization.Away ϖ L := by
    refine (isLocalization_iff _ _).mpr ⟨?_, ?_, ?_⟩
    · rintro ⟨_, n, rfl⟩
      exact isUnit_iff_ne_zero.mpr
        ((map_ne_zero_iff _ hinj).mpr (pow_ne_zero n hϖ.ne_zero))
    · intro z
      obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := A) z
      have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
      obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hb0 hϖ
      refine ⟨(a * ↑u⁻¹, ⟨ϖ ^ n, n, rfl⟩), ?_⟩
      have hu : algebraMap A L (u : A) ≠ 0 := (map_ne_zero_iff _ hinj).mpr u.ne_zero
      have hϖn : algebraMap A L (ϖ ^ n) ≠ 0 := (map_ne_zero_iff _ hinj).mpr (pow_ne_zero n hϖ.ne_zero)
      simp only [map_mul, map_pow, map_units_inv] at hu hϖn ⊢
      field_simp
    · intro x y hxy
      exact ⟨1, by rw [hinj hxy]⟩
  exact IsOpenImmersion.of_isLocalization ϖ

theorem ringKrullDim_stalk_le_one_of_asIdeal_eq_bot
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    (L : Type) [Field L] [Algebra A L] [IsFractionRing A L]
    {X : Scheme.{0}} (c : X ⟶ Spec (CommRingCat.of A))
    [SmoothOfRelativeDimension 1 (pullback.snd c (Spec.map (CommRingCat.ofHom (algebraMap A L))))]
    (x : X) (hx : (c.base x).asIdeal = ⊥) :
    ringKrullDim (X.presheaf.stalk x) ≤ 1 := by
  set s : Spec (CommRingCat.of L) ⟶ Spec (CommRingCat.of A) := Spec.map (CommRingCat.ofHom (algebraMap A L))
    with hs
  haveI : IsOpenImmersion s := isOpenImmersion_specMap_fractionRing A L
  have hinj : Function.Injective (algebraMap A L) := IsFractionRing.injective A L

  have hpt : c.base x = s.base (IsLocalRing.closedPoint L) := by
    apply PrimeSpectrum.ext
    rw [hx]
    change ⊥ = Ideal.comap (algebraMap A L) (IsLocalRing.maximalIdeal L)
    rw [IsLocalRing.maximalIdeal_eq_bot (R := L), Ideal.comap_bot_of_injective _ hinj]
  have hxr : x ∈ Set.range (pullback.fst c s).base := by
    have : Set.range ⇑(pullback.fst c s) = ⇑c ⁻¹' Set.range ⇑s := Scheme.Pullback.range_fst c s
    change x ∈ Set.range ⇑(pullback.fst c s)
    rw [this]
    exact ⟨IsLocalRing.closedPoint L, hpt.symm⟩
  obtain ⟨y, rfl⟩ := hxr
  have h1 := ringKrullDim_stalk_eq_coheight ((pullback.fst c s).base y)
  rw [coheight_eq_of_isOpenImmersion (pullback.fst c s)] at h1
  have h2 : (Order.coheight y : WithBot ℕ∞) ≤ Order.krullDim ↥(pullback c s) := Order.coheight_le_krullDim y
  have h3 : Order.krullDim ↥(pullback c s) = topologicalKrullDim ↥(pullback c s) :=
    (Order.krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := ↥(pullback c s)))).symm
  have h4 := AlgebraicGeometry.SmoothOfRelativeDimension.topologicalKrullDim_le (pullback.snd c s) 1
  calc ringKrullDim ((X.presheaf).stalk ((pullback.fst c s).base y))
      = (Order.coheight y : WithBot ℕ∞) := h1
    _ ≤ Order.krullDim ↥(pullback c s) := h2
    _ = topologicalKrullDim ↥(pullback c s) := h3
    _ ≤ 1 := by exact_mod_cast h4

theorem isPullback_curveChange {R : Type} [CommRing R] {C C' T : Scheme.{0}}
    {c : C ⟶ Spec (CommRingCat.of R)} {c' : C' ⟶ Spec (CommRingCat.of R)}
    (f : C' ⟶ C) (hf : f ≫ c = c') (t : T ⟶ Spec (CommRingCat.of R)) :
    IsPullback (pullback.fst c' t) (curveChange f hf t) f (pullback.fst c t) := by
  subst hf
  have hcomm : curveChange f rfl t ≫ pullback.fst c t = pullback.fst (f ≫ c) t ≫ f := by
    simp only [curveChange, pullback.lift_fst]
  have hsnd : curveChange f rfl t ≫ pullback.snd c t = pullback.snd (f ≫ c) t := curveChange_snd f rfl t
  have big : IsPullback (curveChange f rfl t ≫ pullback.snd c t) (pullback.fst (f ≫ c) t) t (f ≫ c) := by
    rw [hsnd]
    exact (IsPullback.of_hasPullback (f ≫ c) t).flip
  exact (IsPullback.of_right big hcomm (IsPullback.of_hasPullback c t).flip).flip

section Frame

variable (L : Type) [Field L] [CharZero L]
  (K : IntermediateField L (LaurentSeries L))
  (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
  [Algebra A ↥K] [IsScalarTower A L ↥K]
  (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j ≠ 0)]

theorem T_mem_Gamma1 (N : ℕ) : ModularGroup.T ∈ CongruenceSubgroup.Gamma1 N := by
  rw [CongruenceSubgroup.Gamma1_mem]; simp [ModularGroup.T]

theorem T_mem_Gamma0 (N : ℕ) : ModularGroup.T ∈ CongruenceSubgroup.Gamma0 N := by
  rw [CongruenceSubgroup.Gamma0_mem]; simp [ModularGroup.T]

include hj in
set_option synthInstance.maxHeartbeats 1600000 in

theorem finiteType_charts (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] (hT : ModularGroup.T ∈ Γ)
    (hK : K = ModularCurve.laurentBaseChange L (ModularCurve.qExpFunctionFieldC ℚ Γ)) :
    Algebra.FiniteType A ↥(TwoChartIntegralModel.chartAlgFin A (↥K) j) ∧
      Algebra.FiniteType A ↥(TwoChartIntegralModel.chartAlgInf A (↥K) j) := by
  have htj : Transcendental A j := ModularCurve.transcendental_of_coe_eq_coeffEmb_jq L K A j hj
  have hFD : FiniteDimensional ↥(IntermediateField.adjoin L ({j} : Set ↥K)) ↥K :=
    ModularCurve.finiteDimensional_adjoin_of_coe_eq_coeffEmb_jq_of_eq_laurentBaseChange Γ hT L K hK j hj
  haveI : CharZero ↥(IntermediateField.adjoin L ({j} : Set ↥K)) := by
    refine ⟨fun m n hmn => ?_⟩
    have h1 : (((m : ↥(IntermediateField.adjoin L ({j} : Set ↥K))) : ↥K) : LaurentSeries L) =
        (((n : ↥(IntermediateField.adjoin L ({j} : Set ↥K))) : ↥K) : LaurentSeries L) := by rw [hmn]
    have h2 : ((m : LaurentSeries L)) = (n : LaurentSeries L) := by simpa using h1
    have h3 : (HahnSeries.C (m : L) : LaurentSeries L) = HahnSeries.C (n : L) := by
      simpa [map_natCast] using h2
    exact_mod_cast HahnSeries.C_injective h3
  haveI : Algebra.IsAlgebraic ↥(IntermediateField.adjoin L ({j} : Set ↥K)) ↥K := Algebra.IsAlgebraic.of_finite _ _
  have hsep : Algebra.IsSeparable ↥(IntermediateField.adjoin L ({j} : Set ↥K)) ↥K := inferInstance
  exact AlgebraicCurve.TwoChartIntegralModel.finiteType_chartAlgFin_and_chartAlgInf A L (↥K) j htj hFD hsep

omit [CharZero L] [IsDiscreteValuationRing A] in

theorem nonempty_genericFibre :
    Nonempty ↑(pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A L)) := by
  have hgi : GeometricallyIntegral (SmoothProperCurve.baseChange A (TwoChartIntegralModel.toBase A (↥K) j) L) :=
    AlgebraicCurve.TwoChartIntegralModel.geometricallyIntegral_baseChange_toBase_of_intermediateField_laurentSeries
      L K A j
  haveI : Surjective (pullback.snd (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A L)) :=
    inferInstanceAs (Surjective (SmoothProperCurve.baseChange A (TwoChartIntegralModel.toBase A (↥K) j) L))
  obtain ⟨z, -⟩ := (pullback.snd (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A L)).surjective
    (IsLocalRing.closedPoint L)
  exact ⟨z⟩

end Frame

end R1AB31

open R1AB31 in
theorem solution
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hM : 5 ≤ M) (hpM : ¬ p ∣ M)
    (L : Type) [Field L] [CharZero L] [IsCyclotomicExtension {p} ℚ L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ p)
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p)))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAp : (p : A) ∈ IsLocalRing.maximalIdeal A) (hζA : ∃ z : A, algebraMap A L z = ζ)
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j ≠ 0)]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of A))) (ModularCurve.TwoChart.modelTo A (↥K) j))
    (D : RelativePic0Designation A (ModularCurve.TwoChart.modelTo A (↥K) j))
    (hrep : Nonempty (RepresentsRelSubPic (ModularCurve.TwoChart.modelTo A (↥K) j) ε (algEquivZeroCut (ModularCurve.TwoChart.modelTo A (↥K) j) ε) D))
    (hsm : Smooth D.toBase) (hsep : IsSeparated D.toBase)

    [IsProper (ModularCurve.TwoChart.modelTo A (↥K) j)]

    (hsmL : SmoothOfRelativeDimension 1 (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) L))
    (hgiL : GeometricallyIntegral (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) L))
    (hprL : IsProper (pullback.snd D.toBase (specMap A L)))
    (hgcL : GeometricallyConnected (pullback.snd D.toBase (specMap A L)))

    (hsf : ∀ (k : Type) [Field k] [IsAlgClosed k] (f : A →+* k), RingHom.ker f ≠ ⊥ →
      ∃ (C₁ C₂ : Scheme.{0}) (c₁ : C₁ ⟶ Spec (CommRingCat.of k)) (c₂ : C₂ ⟶ Spec (CommRingCat.of k))
        (_ : IsProper c₁) (_ : SmoothOfRelativeDimension 1 c₁) (_ : GeometricallyIntegral c₁)
        (_ : IsProper c₂) (_ : SmoothOfRelativeDimension 1 c₂) (_ : GeometricallyIntegral c₂)
        (i₁ : SchemeHomOver c₁ (pullback.snd (ModularCurve.TwoChart.modelTo A (↥K) j) (Spec.map (CommRingCat.ofHom f))))
        (i₂ : SchemeHomOver c₂ (pullback.snd (ModularCurve.TwoChart.modelTo A (↥K) j) (Spec.map (CommRingCat.ofHom f))))
        (_ : IsClosedImmersion i₁.1) (_ : IsClosedImmersion i₂.1) (n : ℕ)
        (_ : C₁.TwoAffineOpenCover) (_ : C₂.TwoAffineOpenCover),
        IsReduced (pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (Spec.map (CommRingCat.ofHom f))) ∧
        (∀ z : ↥(pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (Spec.map (CommRingCat.ofHom f))), z ∈ Set.range i₁.1.base ∨ z ∈ Set.range i₂.1.base) ∧
        IsReduced (pullback i₁.1 i₂.1) ∧ Nat.card ↥(pullback i₁.1 i₂.1) = n ∧ 0 < n)

    (ℓ : ℕ) [Fact ℓ.Prime]

    [Algebra A ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * ℓ)))]
    [IsScalarTower A L ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * ℓ)))]
    (jℓ : ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * ℓ))))
    (hjℓ : ((jℓ : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (jℓ ≠ 0)]

    (πα πβ : SchemeHomOver (ModularCurve.TwoChart.modelTo A (↥(ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * ℓ)))) jℓ) (ModularCurve.TwoChart.modelTo A (↥K) j))
    [IsFinite πα.1] [IsFinite πβ.1] [LocallyOfFinitePresentation πα.1] [LocallyOfFinitePresentation πβ.1]
    (ια ιβ : ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j) →ₐ[A] ↥(ModularCurve.TwoChart.chartAlgFin A (↥(ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * ℓ)))) jℓ))
    (U : (ModularCurve.TwoChartModel A (↥K) j).Opens)
    (hsurjα : Function.Surjective πα.1.base) (hsurjβ : Function.Surjective πβ.1.base)
    (hια : ∀ b : ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j), (((ια b : ↥(ModularCurve.TwoChart.chartAlgFin A (↥(ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * ℓ)))) jℓ)) : ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * ℓ)))) : LaurentSeries L) = ((b : ↥K) : LaurentSeries L))
    (hιβ : ∀ b : ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j), (((ιβ b : ↥(ModularCurve.TwoChart.chartAlgFin A (↥(ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * ℓ)))) jℓ)) : ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * ℓ)))) : LaurentSeries L) =
        ModularCurve.qExpand L ℓ ((b : ↥K) : LaurentSeries L))
    (hsqα : ModularCurve.TwoChart.ιFin A (↥(ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * ℓ)))) jℓ ≫ πα.1 = Spec.map (CommRingCat.ofHom ια.toRingHom) ≫ ModularCurve.TwoChart.ιFin A (↥K) j)
    (hsqβ : ModularCurve.TwoChart.ιFin A (↥(ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * ℓ)))) jℓ ≫ πβ.1 = Spec.map (CommRingCat.ofHom ιβ.toRingHom) ≫ ModularCurve.TwoChart.ιFin A (↥K) j)
    (hpreα : πα.1 ⁻¹ᵁ (ModularCurve.TwoChart.ιFin A (↥K) j).opensRange = (ModularCurve.TwoChart.ιFin A (↥(ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * ℓ)))) jℓ).opensRange)
    (hpreβ : πβ.1 ⁻¹ᵁ (ModularCurve.TwoChart.ιFin A (↥K) j).opensRange = (ModularCurve.TwoChart.ιFin A (↥(ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * ℓ)))) jℓ).opensRange)
    (hUdim : ∀ x : ↥(ModularCurve.TwoChartModel A (↥K) j), ringKrullDim ((ModularCurve.TwoChartModel A (↥K) j).presheaf.stalk x) ≤ 1 → x ∈ U)
    (hflα : Flat (πα.1 ∣_ U)) (hflβ : Flat (πβ.1 ∣_ U))
    (hrkα : ∀ y : ↥(ModularCurve.TwoChartModel A (↥K) j), y ∈ U → πα.1.finrank y = (if ℓ ∣ M * p then ℓ else ℓ + 1))
    (hrkβ : ∀ y : ↥(ModularCurve.TwoChartModel A (↥K) j), y ∈ U → πβ.1.finrank y = (if ℓ ∣ M * p then ℓ else ℓ + 1))
 :
    ∃ (𝒩 : (pullback (ModularCurve.TwoChart.modelTo A (↥K) j) D.toBase).Modules) (Tℓ : SchemeHomOver D.toBase D.toBase),
      Scheme.Modules.IsInvertible 𝒩 ∧
      (∀ (V : (pullback (ModularCurve.TwoChart.modelTo A (↥K) j) D.toBase).Opens) (d' : ℕ),
        Flat ((curveChange πα.1 πα.2 D.toBase) ∣_ V) → LocallyOfFinitePresentation ((curveChange πα.1 πα.2 D.toBase) ∣_ V) →
        (∀ y : V, ((curveChange πα.1 πα.2 D.toBase) ∣_ V).finrank y = d') →
        Nonempty ((Scheme.Modules.pullback V.ι).obj 𝒩 ≅
          Scheme.Modules.normModule ((curveChange πα.1 πα.2 D.toBase) ∣_ V) d'
            ((Scheme.Modules.pullback ((curveChange πα.1 πα.2 D.toBase) ⁻¹ᵁ V).ι).obj
              ((Scheme.Modules.pullback (curveChange πβ.1 πβ.2 D.toBase)).obj hrep.some.poincare.L)))) ∧
      Nonempty ((hrep.some.poincare.pullbackAlong Tℓ).L ≅
        Scheme.Modules.rigidify (rigSection (ModularCurve.TwoChart.modelTo A (↥K) j) D.toBase ε) (pullback.snd (ModularCurve.TwoChart.modelTo A (↥K) j) D.toBase) 𝒩) ∧
      (∀ {T : Scheme.{0}} (s : T ⟶ Spec (CommRingCat.of A)) (x y : SchemeHomOver s D.toBase),
        NeronModelInfra.schemeHomOverComp ((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hrep.some).mul s x y) Tℓ =
          (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hrep.some).mul s
            (NeronModelInfra.schemeHomOverComp x Tℓ) (NeronModelInfra.schemeHomOverComp y Tℓ)) ∧
      D.zeroSection ≫ Tℓ.1 = D.zeroSection := by
  classical

  haveI hMp : NeZero (M * p) := ⟨Nat.mul_ne_zero (NeZero.ne M) (Nat.Prime.ne_zero Fact.out)⟩

  obtain ⟨Nm, hNm⟩ :=
    AlgebraicGeometry.Scheme.Modules.exists_norm_isInvertible_tensor_pullback_normModule_of_isFinite_of_isIntegrallyClosed.{0}

  haveI hXint : IsIntegral (ModularCurve.TwoChartModel A (↥K) j) :=
    AlgebraicCurve.TwoChartIntegralModel.isIntegral A (↥K) j
  have hFT := R1AB31.finiteType_charts L K A j hj (CongruenceSubgroup.Gamma1 (M * p)) (R1AB31.T_mem_Gamma1 (M * p)) hK
  haveI := hFT.1
  haveI := hFT.2
  haveI hLFT : LocallyOfFiniteType (ModularCurve.TwoChart.modelTo A (↥K) j) :=
    AlgebraicCurve.TwoChartIntegralModel.locallyOfFiniteType_toBase A (↥K) j
  haveI : IsLocallyNoetherian (ModularCurve.TwoChartModel A (↥K) j) :=
    LocallyOfFiniteType.isLocallyNoetherian (ModularCurve.TwoChart.modelTo A (↥K) j)
  have hCnorm : ∀ x : ↥(ModularCurve.TwoChartModel A (↥K) j),
      IsIntegrallyClosed ((ModularCurve.TwoChartModel A (↥K) j).presheaf.stalk x) :=
    fun x => AlgebraicCurve.TwoChartIntegralModel.isIntegrallyClosed_stalk A (↥K) j x
  have hCsec : ∀ V : (ModularCurve.TwoChartModel A (↥K) j).Opens, IsAffineOpen V →
      IsIntegrallyClosed Γ(ModularCurve.TwoChartModel A (↥K) j, V) :=
    fun V hV => AlgebraicCurve.TwoChartIntegralModel.isIntegrallyClosed_sections_of_isAffineOpen A (↥K) j V hV
  have hne : Nonempty ↑(pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A L)) :=
    R1AB31.nonempty_genericFibre L K A j

  haveI hXℓint : IsIntegral (ModularCurve.TwoChartModel A
      (↥(ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * ℓ)))) jℓ) :=
    AlgebraicCurve.TwoChartIntegralModel.isIntegral A _ jℓ
  have hFTℓ := R1AB31.finiteType_charts L
    (ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * ℓ))) A jℓ hjℓ
    (CongruenceSubgroup.Gamma1 (M * p) ⊓ CongruenceSubgroup.Gamma0 (M * p * ℓ))
    (Subgroup.mem_inf.mpr ⟨R1AB31.T_mem_Gamma1 (M * p), R1AB31.T_mem_Gamma0 (M * p * ℓ)⟩) rfl
  haveI := hFTℓ.1
  haveI := hFTℓ.2
  haveI hLFTℓ : LocallyOfFiniteType (ModularCurve.TwoChart.modelTo A
      (↥(ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * ℓ)))) jℓ) :=
    AlgebraicCurve.TwoChartIntegralModel.locallyOfFiniteType_toBase A _ jℓ
  have hneℓ : Nonempty ↑(pullback (ModularCurve.TwoChart.modelTo A
      (↥(ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * ℓ)))) jℓ) (specMap A L)) :=
    R1AB31.nonempty_genericFibre L _ A jℓ

  have hI := AlgebraicGeometry.isIntegral_pullback_and_isIntegral_pullback_fst_comp_of_smooth_of_geometricallyConnected_pullback_snd_specMap
    A L (ModularCurve.TwoChart.modelTo A (↥K) j) hne D.toBase
  have hIℓ := AlgebraicGeometry.isIntegral_pullback_and_isIntegral_pullback_fst_comp_of_smooth_of_geometricallyConnected_pullback_snd_specMap
    A L (ModularCurve.TwoChart.modelTo A
      (↥(ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * ℓ)))) jℓ) hneℓ D.toBase
  haveI := hI.1
  haveI := hI.2
  haveI := hIℓ.1
  haveI := hIℓ.2

  have hnorm : ∀ V : (pullback (ModularCurve.TwoChart.modelTo A (↥K) j) D.toBase).Opens, IsAffineOpen V →
      IsIntegrallyClosed Γ(pullback (ModularCurve.TwoChart.modelTo A (↥K) j) D.toBase, V) :=
    fun V hV => AlgebraicGeometry.isIntegrallyClosed_sections_of_smooth_of_forall_isIntegrallyClosed_sections
      (pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) D.toBase) hCsec V hV
  have hnorm₂ : ∀ V : (pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (pullback.fst D.toBase D.toBase ≫ D.toBase)).Opens,
      IsAffineOpen V →
      IsIntegrallyClosed Γ(pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (pullback.fst D.toBase D.toBase ≫ D.toBase), V) :=
    fun V hV => AlgebraicGeometry.isIntegrallyClosed_sections_of_smooth_of_forall_isIntegrallyClosed_sections
      (pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (pullback.fst D.toBase D.toBase ≫ D.toBase)) hCsec V hV

  haveI hsα : Surjective πα.1 := ⟨hsurjα⟩
  have sqα := R1AB31.isPullback_curveChange πα.1 πα.2 D.toBase
  haveI : IsFinite (curveChange πα.1 πα.2 D.toBase) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback sqα inferInstance
  haveI : Surjective (curveChange πα.1 πα.2 D.toBase) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback sqα inferInstance

  have hVgen : ∀ x : ↥(ModularCurve.TwoChartModel A (↥K) j),
      ((ModularCurve.TwoChart.modelTo A (↥K) j).base x).asIdeal = ⊥ → x ∈ U :=
    fun x hx => hUdim x (R1AB31.ringKrullDim_stalk_le_one_of_asIdeal_eq_bot A L
      (ModularCurve.TwoChart.modelTo A (↥K) j) x hx)

  have hξU : genericPoint (ModularCurve.TwoChartModel A (↥K) j) ∈ U := by
    refine hUdim _ ?_
    have hF : IsField ↑((ModularCurve.TwoChartModel A (↥K) j).functionField) :=
      Field.toIsField _
    change ringKrullDim ↑((ModularCurve.TwoChartModel A (↥K) j).functionField) ≤ 1
    rw [ringKrullDim_eq_zero_of_isField hF]
    exact zero_le_one
  haveI : Nonempty ↥(↑U : Scheme.{0}) := ⟨⟨_, hξU⟩⟩
  haveI : IsIntegral (↑U : Scheme.{0}) := isIntegral_of_isOpenImmersion U.ι
  haveI : IsFinite (πα.1 ∣_ U) := IsZariskiLocalAtTarget.restrict (show IsFinite πα.1 from inferInstance) U
  haveI : LocallyOfFinitePresentation (πα.1 ∣_ U) :=
    IsZariskiLocalAtTarget.restrict (show LocallyOfFinitePresentation πα.1 from inferInstance) U
  set d : ℕ := (πα.1 ∣_ U).finrank ⟨_, hξU⟩ with hd
  have hrk : ∀ y : U, (πα.1 ∣_ U).finrank y = d := fun y =>
    (Scheme.Hom.isLocallyConstant_finrank (πα.1 ∣_ U)).apply_eq_of_preconnectedSpace y ⟨_, hξU⟩

  obtain ⟨Tℓ, h1, h2, h3⟩ :=
    AlgebraicGeometry.RelPicard.RepresentsRelSubPic.exists_hom_classifies_norm_pullback_poincare_of_twoGluedCurves_of_mem_of_ringKrullDim_le_one
      A (ModularCurve.TwoChart.modelTo A (↥K) j)
      (ModularCurve.TwoChart.modelTo A
        (↥(ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * ℓ)))) jℓ)
      hCnorm ε hsf πβ πα D hrep.some hnorm hnorm₂ Nm hNm U d hrk hUdim hVgen

  have hπ := hNm (curveChange πα.1 πα.2 D.toBase) hnorm
  have hPinv : Scheme.Modules.IsInvertible
      ((Scheme.Modules.pullback (curveChange πβ.1 πβ.2 D.toBase)).obj hrep.some.poincare.L) :=
    hrep.some.poincare.isInvertible.pullback _
  refine ⟨Nm (curveChange πα.1 πα.2 D.toBase)
      ((Scheme.Modules.pullback (curveChange πβ.1 πβ.2 D.toBase)).obj hrep.some.poincare.L), Tℓ,
    hπ.1 _ hPinv, ?_, h1, h2, h3⟩
  intro V d' hfl hlfp hrk'
  exact hπ.2.2.2.2.2 V d' hfl hlfp hrk' _ hPinv

end S_ModularCurve_XOneP_exists_hom_classifies_norm_pullback_poincare_heckeDegeneracyPair_twoChartModel_x1_mul
end P2MW
export P2MW.S_ModularCurve_XOneP_exists_hom_classifies_norm_pullback_poincare_heckeDegeneracyPair_twoChartModel_x1_mul (solution)
