-- Prove2me | solution 1 for ModularCurve.exists_abelJacobi_pts_relativeGroupLaw_of_dRModelPackage_of_representsRelSubPic
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/08ff0af8-a4dc-5877-a9b1-205fce6eb529

import Mathlib
import Definitions.Def_ModularCurve_DRModelPackage
import Definitions.Def_ModularCurve_DRModelLegTwoInput
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
import Definitions.Def_AlgebraicCurve_CurveModel
import Theorems.Thm_AlgebraicGeometry_RelPicard_exists_representsRelSubPic_baseChange
import Theorems.Thm_AlgebraicGeometry_RelPicard_baseChange_relativeGroupLaw_mul_compat
import Theorems.Thm_AlgebraicGeometry_RelPicard_exists_abelJacobi_of_representsRelSubPic
import Theorems.Thm_AlgebraicGeometry_RelPicard_exists_pic0_equiv_points_of_representsRelSubPic_of_abelJacobi
import Theorems.Thm_AlgebraicGeometry_RelPicard_isProper_and_geometricallyConnected_of_representsRelSubPic_algEquivZeroCut_of_finiteMapData
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveFiniteMapData
import Definitions.Def_AlgebraicCurve_AdelicIndex
import Theorems.Thm_ModularCurve_geometricallyIntegral_baseChangeToBase_twoChartIntegralModel_rat
import Theorems.Thm_AlgebraicGeometry_SmoothProperCurve_exists_genus_forall_geometricFibre_riemannRoch_imp_eq_of_connectedSpace
import Theorems.Thm_ModularCurve_geometricallyIntegral_baseChangeToBase_twoChartIntegralModel_away
import Theorems.Thm_AlgebraicGeometry_SmoothProperCurve_FiniteMapData_forall_exists_le_m_of_one_le
import Theorems.Thm_ModularCurve_DRModelPackage_exists_finiteMapData_baseChange_away_one_le_m
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_abelJacobi_pts_relativeGroupLaw_of_dRModelPackage_of_representsRelSubPic
p2m_attr_erase "instance" "PresheafOfModules.ExteriorPower.instModulePresheafAb AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instNeg AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulInt AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAddCommGroup AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAdd AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSub AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulNat AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instZero AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions SheafOfModules.isIso_ihomModelToIhom AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver"
p2m_attr_erase "instance" "AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion AlgebraicGeometry.RelEffCartierDiv.subsingleton_of_degree_zero AlgebraicGeometry.OModulePresheaf.isScalarTower AlgebraicGeometry.Scheme.OrderedAffineCover.instLinearOrder AlgebraicGeometry.OModulePresheaf.module AlgebraicGeometry.Scheme.OrderedAffineCover.instFintype AlgebraicGeometry.Scheme.OrderedAffineCover.instFintypeIdx AlgebraicGeometry.OModulePresheaf.addCommGroup AlgebraicGeometry.Scheme.OrderedAffineCover.instDecidableEqIdx AlgebraicGeometry.OModulePresheaf.moduleSections AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ"
p2m_attr_erase "instance" "AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule AlgebraicGeometry.RelEffCartierDiv.isClosedImmersion_subschemeι_resProdMap AlgebraicGeometry.RelEffCartierDiv.isOpenImmersion_resProdMap ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf"
p2m_attr_erase "instance" "AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin AlgebraicCurve.CurveModel.chartRing_finitePresentation instIsScalarTowerIntegralClosure instNeZeroIdealUnderOfNontrivialOfIsDomainOfIsIntegral_definitions instAlgebraIntegralClosure_1 isInvariant_integralClosure instAlgebraIntegralClosure continuousSMulDiscrete_integralClosure mulSemiringActionIntegralClosure smulCommClass_integralClosure instIsDomainIntegralClosure instIsIntegralIntegralClosure instCommRingIntegralClosure instFaithfulSMulIntegralClosure instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid"
p2m_attr_erase "instance" "ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent ModularCurve.B3.instIsElliptic_goodModel ModularCurve.instIsScalarTowerJAdjoin WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular"
p2m_attr_erase "simp" "AlgebraicGeometry.RelPicard.thetaBundle_def AlgebraicGeometry.RelPicard.picardBundle_def AlgebraicGeometry.Scheme.Modules.exteriorPower_obj PresheafOfModules.exteriorPower_map_ιMulti PresheafOfModules.ExteriorPower.appₗ_apply AlgebraicGeometry.RelPicard.fst_toProdSpec AlgebraicGeometry.RelPicard.toProdSpec_fst_assoc AlgebraicGeometry.RelPicard.pointsSubBasepointModule_cons AlgebraicGeometry.RelPicard.pointsSubBasepointModule_nil AlgebraicGeometry.RelPicard.fst_toProdSpec_assoc AlgebraicGeometry.RelPicard.toProdSpec_fst AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.sub_app AlgebraicGeometry.Scheme.IdealSheafData.sres_sresTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.add_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.sizeOf_spec AlgebraicGeometry.Scheme.IdealSheafData.coe_resLE AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.smul_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_ofLE_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.ideal_range AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zero_app AlgebraicGeometry.Scheme.IdealSheafData.sres_sres AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.comp_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.neg_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.id_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_mulRight_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.nsmul_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.injEq AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zsmul_app AlgebraicGeometry.Scheme.Modules.toUnitSection_ofUnitSection AlgebraicGeometry.Scheme.Modules.pullbackSection_def AlgebraicGeometry.Scheme.Modules.ofUnitSection_toUnitSection AlgebraicCurve.coe_cechH0Equiv_apply AlgebraicCurve.cechH1ToH1_mk AlgebraicCurve.lSpaceOn_univ AlgebraicCurve.lSpaceOn_empty AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring"
p2m_attr_erase "simp" "AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd"
p2m_attr_erase "simp" "ModularCurve.eisensteinSystem_of_not_dvd AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom SheafOfModules.ihomSectionsEquivFamily_unit AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply SheafOfModules.ihomEval_unit_app AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply SheafOfModules.unit_ihomSectionsEquivFamily AlgebraicGeometry.Scheme.Modules.familyOfHom_app AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq"
p2m_attr_erase "simp" "AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule AlgebraicGeometry.prodKerGraph_one AlgebraicGeometry.fibrePowOver.proj_comp AlgebraicGeometry.prodKerGraph_zero AlgebraicGeometry.RelEffCartierDiv.empty_I AlgebraicGeometry.fibrePowOver.proj_comp_assoc AlgebraicCurve.SymmetricPowerPackage.mk.sizeOf_spec AlgebraicCurve.SymmetricPowerPackage.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.mk.injEq AlgebraicGeometry.OModulePresheaf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.mk.injEq AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app"
p2m_attr_erase "simp" "AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq TwoChartCech.Mumford.dK_apply"
p2m_attr_erase "simp" "TwoChartCech.Mumford.ι0_apply TwoChartCech.Mumford.ι1_apply TwoChartCech.KerCoprod.dK_apply TwoChartCech.KerCoprod.ι1_apply TwoChartCech.KerCoprod.ι0_apply AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app AlgebraicGeometry.RelPicard.rigSection_snd AlgebraicGeometry.RelPicard.RigidifiedLineBundle.ofInvertible_L AlgebraicGeometry.RelPicard.rigSection_snd_assoc AlgebraicGeometry.RelEffCartierDiv.IsUniversal.lift_comp AlgebraicGeometry.RelEffCartierDiv.functor_map_fst AlgebraicGeometry.RelEffCartierDiv.IsUniversal.homEquiv_apply AlgebraicGeometry.RelEffCartierDiv.IsUniversal.lift_pullbackAlong AlgebraicGeometry.RelEffCartierDiv.IsUniversal.homEquiv_symm_apply AlgebraicGeometry.RelEffCartierDiv.IsUniversal.lift_comp_assoc CoherentBaseChange.FibreH0Family.mk.sizeOf_spec CoherentBaseChange.FibreH0Family.mk.injEq AlgebraicGeometry.RelEffCartierDiv.supportedIn_top AlgebraicGeometry.RelEffCartierDiv.mem_supportedIn_iff AlgebraicGeometry.RelEffCartierDiv.supportedIn_top_eq AlgebraicGeometry.RelEffCartierDiv.restrictAlong_extendAlong AlgebraicGeometry.RelEffCartierDiv.extendAlong_I AlgebraicGeometry.RelEffCartierDiv.resProdMap_snd AlgebraicGeometry.RelEffCartierDiv.restrictAlong_I AlgebraicGeometry.RelEffCartierDiv.extendAlong_restrictAlong AlgebraicGeometry.RelEffCartierDiv.resProdMap_fst_assoc AlgebraicGeometry.RelEffCartierDiv.resProdMap_snd_assoc AlgebraicGeometry.RelEffCartierDiv.resProdMap_fst ModularCurve.qExpandAlgHomC_apply ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong ModularCurve.CharPModel.FibreModel.mk.injEq ModularCurve.CharPModel.FibreModel.mk.sizeOf_spec ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero"
p2m_attr_erase "simp" "ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add"
p2m_attr_erase "simp" "ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg RegularLocalRingQuotientAscent.dualNumberFst_apply WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply ModularCurve.CharPReduction.coeffRed_coeff ModularCurve.CharPReduction.redLocHom_apply AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap ModularCurve.cuspCount_one ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring ModularCurve.coe_cuspidalDivisor₀ ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar"
p2m_attr_erase "simp" "HahnSeries.ramScale_apply compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm ModularCurve.ProjectiveLine.map_mk ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply"
p2m_attr_erase "simp" "HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ"
p2m_attr_erase "simp" "TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff ModularCurve.PlaceSpecialization.mk.injEq ModularCurve.PlaceSpecialization.mk.sizeOf_spec AlgebraicGeometry.Scheme.Modules.ProjPresentation.mk.injEq AlgebraicGeometry.Scheme.Modules.ProjPresentation.mk.sizeOf_spec"

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry P2MW.S_ModularCurve_exists_abelJacobi_pts_relativeGroupLaw_of_dRModelPackage_of_representsRelSubPic.AlgebraicGeometry NeronModelInfra~schemeHomOverComp GoodReductionJacobian ModularCurve P2MW.S_ModularCurve_exists_abelJacobi_pts_relativeGroupLaw_of_dRModelPackage_of_representsRelSubPic.ModularCurve AlgebraicGeometry.RelPicard P2MW.S_ModularCurve_exists_abelJacobi_pts_relativeGroupLaw_of_dRModelPackage_of_representsRelSubPic.AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve AlgebraicCurve~genus"

universe u v

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Spec.map_comp Surjective isIso_iff_isOpenImmersion_and_surjective SmoothOfRelativeDimension IsProper Scheme.Opens.range_ι Scheme.Hom GeometricallyIntegral LocallyOfFiniteType Spec Spec.map Scheme Smooth IsOpenImmersion Scheme.Pullback.range_snd smoothOfRelativeDimension_isStableUnderBaseChange IsOpenImmersion.isoOfRangeEq GeometricallyConnected Scheme.Opens geometrically IsOpenImmersion.isoOfRangeEq_hom_fac Scheme.Hom.coe_opensRange RelEffCartierDiv RelEffCartierDiv.ofPoint RelPicard.exists_representsRelSubPic_baseChange RelPicard.isProper_and_geometricallyConnected_of_representsRelSubPic_algEquivZeroCut_of_finiteMapData SmoothProperCurve.FiniteMapData SmoothProperCurve.exists_genus_forall_geometricFibre_riemannRoch_imp_eq_of_connectedSpace SmoothProperCurve.FiniteMapData.forall_exists_le_m_of_one_le"
namespace RelPicard
p2m_export "AlgebraicGeometry.RelPicard" "RepresentsRelSubPic algEquivZeroCut algEquivZeroGroupCut RepresentsRelSubPic.relativeGroupLaw RepresentsRelSubPic.relativeGroupLaw_isCommutative BaseChange.κ BaseChange.κ_hom_snd BaseChange.κ_hom_fst BaseChange.ofR exists_representsRelSubPic_baseChange baseChange_relativeGroupLaw_mul_compat exists_abelJacobi_of_representsRelSubPic exists_pic0_equiv_points_of_representsRelSubPic_of_abelJacobi isProper_and_geometricallyConnected_of_representsRelSubPic_algEquivZeroCut_of_finiteMapData"
namespace L3T
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
    (hsm : Smooth D.toBase) (hgc : GeometricallyConnected D.toBase)
    (R' : Type u) [CommRing R'] [Algebra R R']
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
  haveI : GeometricallyConnected (D.baseChange R').toBase := by
    rw [RelativePic0Designation.baseChange_toBase]; infer_instance
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
    (hsm : Smooth D.toBase) (hgc : GeometricallyConnected D.toBase)
    (R' : Type u) [CommRing R'] [Algebra R R']
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
    exists_pts_of_representsRelSubPic_baseChange R c ε D h hsm hgc R' hpr' K F M e' he'

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

end AlgebraicGeometry.RelPicard.L3T

namespace L3T_S4

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in

theorem gal_equivariance_int (p : ℕ) [NeZero p]
    {X : Scheme.{0}} (c : X ⟶ Spec (CommRingCat.of ℤ))
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℤ))) c)
    (Mη : CurveModel (AlgebraicClosure ℚ) (modularFunctionFieldBar p))
    (eη : Mη.C ⟶ pullback c (Spec.map (CommRingCat.ofHom (algebraMap ℤ (AlgebraicClosure ℚ))))) [IsIso eη]
    (heη : eη ≫ pullback.snd c _ = Mη.toBase)
    (hgal : ∀ (g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
      (x x' : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Mη.C // q ≫ Mη.toBase = 𝟙 _}),
      x'.1 ≫ eη ≫ pullback.fst c _ =
        Spec.map (CommRingCat.ofHom (g : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ)) ≫
          x.1 ≫ eη ≫ pullback.fst c _ →
      Mη.pointEquivPlace x' =
        arithmeticGalois (L := AlgebraicClosure ℚ) (modularFunctionFieldFull p) g • Mη.pointEquivPlace x)
    {J : Scheme.{0}} {f : J ⟶ Spec (CommRingCat.of ℤ)} (L : RelativeGroupLaw ℤ f)
    (k : pullback c (Spec.map (CommRingCat.ofHom (algebraMap ℤ (AlgebraicClosure ℚ)))) ⟶ J)
    [IsCurveOver (AlgebraicClosure ℚ) (modularFunctionFieldBar p)]
    (pts : Pic0 (AlgebraicClosure ℚ) (modularFunctionFieldBar p) ≃ SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap ℤ (AlgebraicClosure ℚ)))) f)
    (hadd : ∀ x y, pts (x + y) = L.mul _ (pts x) (pts y))
    (hnorm : ∀ (x s : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Mη.C // q ≫ Mη.toBase = 𝟙 _}),
      s.1 ≫ eη ≫ pullback.fst c (Spec.map (CommRingCat.ofHom (algebraMap ℤ (AlgebraicClosure ℚ)))) = (Spec.map (CommRingCat.ofHom (algebraMap ℤ (AlgebraicClosure ℚ)))) ≫ ε.1 →
      ∃ D : Divisor.degZero (K := AlgebraicClosure ℚ) (F := modularFunctionFieldBar p),
        (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar p)) =
          Finsupp.single (Mη.pointEquivPlace x) 1 - Finsupp.single (Mη.pointEquivPlace s) 1 ∧
        (pts (Pic0.mk D)).1 = x.1 ≫ eη ≫ k)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
    (hk : ∀ hσ : (Spec.map (CommRingCat.ofHom (algebraMap ℤ (AlgebraicClosure ℚ)))) ≫ 𝟙 _ =
        Spec.map (CommRingCat.ofHom (σ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ)) ≫
          (Spec.map (CommRingCat.ofHom (algebraMap ℤ (AlgebraicClosure ℚ)))),
      pullback.map c _ c _ (𝟙 X) (Spec.map (CommRingCat.ofHom (σ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ))) (𝟙 _)
        (by simp) hσ ≫ k = k)
    (x : JZero p) :
    (pts (σ • x)).1 = Spec.map (CommRingCat.ofHom (σ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ)) ≫ (pts x).1 := by
  have hσfix : Spec.map (CommRingCat.ofHom (σ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ)) ≫ (Spec.map (CommRingCat.ofHom (algebraMap ℤ (AlgebraicClosure ℚ)))) = (Spec.map (CommRingCat.ofHom (algebraMap ℤ (AlgebraicClosure ℚ)))) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    exact RingHom.ext_int _ _

  have hinvη : inv eη ≫ Mη.toBase = pullback.snd c (Spec.map (CommRingCat.ofHom (algebraMap ℤ (AlgebraicClosure ℚ)))) := by
    rw [IsIso.inv_comp_eq, heη]
  let toM : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap ℤ (AlgebraicClosure ℚ)))) c →
      {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Mη.C // q ≫ Mη.toBase = 𝟙 _} :=
    fun y => ⟨pullback.lift y.1 (𝟙 _) (by rw [y.2, Category.id_comp]) ≫ inv eη, by
      rw [Category.assoc, hinvη, pullback.lift_snd]⟩
  have htoM : ∀ (y : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap ℤ (AlgebraicClosure ℚ)))) c) {Z : Scheme.{0}} (k : X ⟶ Z),
      (toM y).1 ≫ eη ≫ pullback.fst c (Spec.map (CommRingCat.ofHom (algebraMap ℤ (AlgebraicClosure ℚ)))) ≫ k = y.1 ≫ k := by
    intro y Z k
    show (pullback.lift y.1 (𝟙 _) _ ≫ inv eη) ≫ eη ≫ pullback.fst c _ ≫ k = y.1 ≫ k
    rw [Category.assoc, IsIso.inv_hom_id_assoc, pullback.lift_fst_assoc]
  have htoM₀ : ∀ (y : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap ℤ (AlgebraicClosure ℚ)))) c), (toM y).1 ≫ eη ≫ pullback.fst c (Spec.map (CommRingCat.ofHom (algebraMap ℤ (AlgebraicClosure ℚ)))) = y.1 := by
    intro y
    simpa only [Category.comp_id] using htoM y (𝟙 X)

  let sη : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap ℤ (AlgebraicClosure ℚ)))) c := ⟨(Spec.map (CommRingCat.ofHom (algebraMap ℤ (AlgebraicClosure ℚ)))) ≫ ε.1, by rw [Category.assoc, ε.2, Category.comp_id]⟩
  let tw : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap ℤ (AlgebraicClosure ℚ)))) c → SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap ℤ (AlgebraicClosure ℚ)))) c := fun y =>
    ⟨Spec.map (CommRingCat.ofHom (σ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ)) ≫ y.1, by rw [Category.assoc, y.2, hσfix]⟩
  have htw_s : tw sη = sη := Subtype.ext (by
    show Spec.map _ ≫ (Spec.map (CommRingCat.ofHom (algebraMap ℤ (AlgebraicClosure ℚ)))) ≫ ε.1 = (Spec.map (CommRingCat.ofHom (algebraMap ℤ (AlgebraicClosure ℚ)))) ≫ ε.1
    rw [← Category.assoc, hσfix])
  have hplace_tw : ∀ y : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap ℤ (AlgebraicClosure ℚ)))) c,
      Mη.pointEquivPlace (toM (tw y)) =
        arithmeticGalois (L := AlgebraicClosure ℚ) (modularFunctionFieldFull p) σ •
          Mη.pointEquivPlace (toM y) := by
    intro y
    apply hgal σ (toM y) (toM (tw y))
    rw [htoM₀, htoM₀]
  let ofPlace : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar p) → SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap ℤ (AlgebraicClosure ℚ)))) c :=
    fun v => ⟨(Mη.pointEquivPlace.symm v).1 ≫ eη ≫ pullback.fst c (Spec.map (CommRingCat.ofHom (algebraMap ℤ (AlgebraicClosure ℚ)))), by
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

  set g := arithmeticGalois (L := AlgebraicClosure ℚ) (modularFunctionFieldFull p) σ with hg
  let w₀ : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar p) := Mη.pointEquivPlace (toM sη)
  have hs_cond : (toM sη).1 ≫ eη ≫ pullback.fst c (Spec.map (CommRingCat.ofHom (algebraMap ℤ (AlgebraicClosure ℚ)))) = (Spec.map (CommRingCat.ofHom (algebraMap ℤ (AlgebraicClosure ℚ)))) ≫ ε.1 := htoM₀ sη
  have hw₀ : g • w₀ = w₀ := by
    have := hplace_tw sη
    rw [htw_s] at this
    exact this.symm
  have hdeg1 : ∀ v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar p), v.deg = 1 :=
    fun v => IsCurveOver.deg_eq_one_of_isAlgClosed v

  have hΔmem : ∀ v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar p),
      Finsupp.single v (1 : ℤ) - Finsupp.single w₀ 1 ∈
        Divisor.degZero (K := AlgebraicClosure ℚ) (F := modularFunctionFieldBar p) := by
    intro v
    rw [Divisor.mem_degZero, map_sub, Divisor.degree_single, Divisor.degree_single, hdeg1, hdeg1]
    simp
  let Δ : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar p) →
      Divisor.degZero (K := AlgebraicClosure ℚ) (F := modularFunctionFieldBar p) :=
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

    have hσ' : (Spec.map (CommRingCat.ofHom (algebraMap ℤ (AlgebraicClosure ℚ)))) ≫ 𝟙 _ =
        Spec.map (CommRingCat.ofHom (σ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ)) ≫
          (Spec.map (CommRingCat.ofHom (algebraMap ℤ (AlgebraicClosure ℚ)))) := by rw [Category.comp_id, hσfix]
    have heq : ∀ y : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap ℤ (AlgebraicClosure ℚ)))) c,
        (toM (tw y)).1 ≫ eη ≫
          pullback.map c _ c _ (𝟙 X) (Spec.map (CommRingCat.ofHom (σ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ))) (𝟙 _)
            (by simp) hσ' =
        Spec.map (CommRingCat.ofHom (σ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ)) ≫ (toM y).1 ≫ eη := by
      intro y
      have e1 := htoM₀ (tw y)
      have e2 := htoM₀ y
      have e3 : ∀ z : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap ℤ (AlgebraicClosure ℚ)))) c,
          (toM z).1 ≫ eη ≫ pullback.snd c _ = 𝟙 _ := fun z => by rw [heη]; exact (toM z).2
      apply pullback.hom_ext
      · simp only [Category.assoc, pullback.lift_fst, Category.comp_id, e1, e2]
        rfl
      · simp only [Category.assoc, pullback.lift_snd, reassoc_of% (e3 (tw y)), e3 y, Category.comp_id]
    conv_lhs => rw [← hk hσ']
    rw [reassoc_of% (heq (ofPlace v))]

  letI := L.pointGroup (Spec.map (CommRingCat.ofHom (algebraMap ℤ (AlgebraicClosure ℚ))))
  have hmul_def : ∀ a b : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap ℤ (AlgebraicClosure ℚ)))) f, a * b = L.mul _ a b := fun _ _ => rfl
  let Φ₁ : JZero p →+ Additive (SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap ℤ (AlgebraicClosure ℚ)))) f) :=
    AddMonoidHom.mk' (fun y => Additive.ofMul (pts (σ • y))) (by
      intro a b
      apply Additive.toMul.injective
      show pts (σ • (a + b)) = pts (σ • a) * pts (σ • b)
      rw [smul_add, hadd, hmul_def])
  let Φ₂ : JZero p →+ Additive (SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap ℤ (AlgebraicClosure ℚ)))) f) :=
    AddMonoidHom.mk' (fun y => Additive.ofMul (GoodReductionJacobian.schemeHomOverComp (Spec.map (CommRingCat.ofHom (σ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ))) hσfix (pts y))) (by
      intro a b
      apply Additive.toMul.injective
      show GoodReductionJacobian.schemeHomOverComp _ hσfix (pts (a + b)) =
        GoodReductionJacobian.schemeHomOverComp _ hσfix (pts a) * GoodReductionJacobian.schemeHomOverComp _ hσfix (pts b)
      rw [hadd, L.mul_natural, hmul_def])
  suffices hΦ : Φ₁ = Φ₂ by
    have := congrArg (fun Φ : JZero p →+ Additive (SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap ℤ (AlgebraicClosure ℚ)))) f) => (Additive.toMul (Φ x)).1) hΦ
    exact this

  have hclos : AddSubgroup.closure (Set.range fun v => Pic0.mk (Δ v)) = ⊤ := by
    rw [eq_top_iff]
    rintro y -
    obtain ⟨D, rfl⟩ := Pic0.mk_surjective y
    have hdegD : Divisor.degree (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar p)) = 0 := D.2

    have hdec : (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar p)) =
        (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar p)).sum
          (fun v n => n • (Finsupp.single v (1 : ℤ) - Finsupp.single w₀ 1)) := by
      have hsum1 : (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar p)).sum
          (fun v n => n • Finsupp.single v (1 : ℤ)) = D := by
        conv_rhs => rw [← Finsupp.sum_single (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar p))]
        apply Finsupp.sum_congr
        intro v _
        rw [Finsupp.smul_single, smul_eq_mul, mul_one]
      have hsum2 : (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar p)).sum
          (fun v n => n • Finsupp.single w₀ (1 : ℤ)) = 0 := by
        simp only [Finsupp.sum, ← Finset.sum_smul]
        have : (∑ v ∈ (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar p)).support,
            (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar p)) v) =
            Divisor.degree (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar p)) := by
          conv_rhs => rw [← Finsupp.sum_single (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar p)), map_finsuppSum]
          simp only [Finsupp.sum, Divisor.degree_single, hdeg1, Nat.cast_one, mul_one]
        rw [this, hdegD, zero_smul]
      simp only [smul_sub, Finsupp.sum_sub, hsum1, hsum2, sub_zero]
    let mkHom : Divisor.degZero (K := AlgebraicClosure ℚ) (F := modularFunctionFieldBar p) →+ JZero p :=
      { toFun := Pic0.mk, map_zero' := Pic0.mk_zero, map_add' := Pic0.mk_add }
    have hD' : D = ∑ v ∈ (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar p)).support,
        (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar p)) v • Δ v := by
      apply Subtype.ext
      rw [AddSubmonoidClass.coe_finsetSum]
      simp only [AddSubgroupClass.coe_zsmul]
      simpa only [Finsupp.sum] using hdec
    have hmk : Pic0.mk D = ∑ v ∈ (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar p)).support,
        (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar p)) v • Pic0.mk (Δ v) := by
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

end L3T_S4

namespace ModularCurve
p2m_export "ModularCurve" "DRModel DRModel.toBase DRModelPackage modularFunctionFieldFull arithmeticGalois galois_smul_pic0_def modularFunctionFieldBar JZero geometricallyIntegral_baseChangeToBase_twoChartIntegralModel_rat geometricallyIntegral_baseChangeToBase_twoChartIntegralModel_away DRModelPackage.exists_finiteMapData_baseChange_away_one_le_m"
namespace L3T
p2m_open "ModularCurve"

open AlgebraicGeometry.RelPicard.L3T

set_option maxHeartbeats 3200000 in

theorem exists_abelJacobi_pts_galois (p : ℕ) [NeZero p]
    {C : Scheme.{0}} (c : C ⟶ Spec (CommRingCat.of ℤ)) [IsProper c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℤ))) c)
    (D : RelativePic0Designation ℤ c) (hD : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D)
    (hsm : Smooth D.toBase) (hgc : GeometricallyConnected D.toBase)
    [SmoothOfRelativeDimension 1 (baseChange ℤ c ℚ)] [GeometricallyIntegral (baseChange ℤ c ℚ)]
    (hprQ : IsProper (D.baseChange ℚ).toBase)
    [IsCurveOver (AlgebraicClosure ℚ) (modularFunctionFieldBar p)]
    (Mη : CurveModel (AlgebraicClosure ℚ) (modularFunctionFieldBar p))
    (eη : Mη.C ⟶ pullback c (specMap ℤ (AlgebraicClosure ℚ))) [IsIso eη]
    (heη : eη ≫ pullback.snd c (specMap ℤ (AlgebraicClosure ℚ)) = Mη.toBase)
    (hgal : ∀ (g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
      (x x' : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Mη.C // q ≫ Mη.toBase = 𝟙 _}),
      x'.1 ≫ eη ≫ pullback.fst c _ =
        Spec.map (CommRingCat.ofHom (g : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ)) ≫ x.1 ≫ eη ≫ pullback.fst c _ →
      Mη.pointEquivPlace x' = arithmeticGalois (L := AlgebraicClosure ℚ) (modularFunctionFieldFull p) g • Mη.pointEquivPlace x) :
    ∃ (h' : RepresentsRelSubPic (baseChange ℤ c ℚ) (sectionBaseChange ℚ ε)
        (algEquivZeroCut (baseChange ℤ c ℚ) (sectionBaseChange ℚ ε)) (D.baseChange ℚ))
      (aj' : SchemeHomOver (baseChange ℤ c ℚ) (D.baseChange ℚ).toBase)
      (aj : Mη.C ⟶ D.P)
      (εbar : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Mη.C // q ≫ Mη.toBase = 𝟙 _})
      (pts : JZero p ≃ SchemeHomOver (specMap ℤ (AlgebraicClosure ℚ)) D.toBase),
      Nonempty (h'.poincare.L ≅ (BaseChange.ofR c ε ℚ
        (hD.poincare.pullbackAlong ⟨pullback.fst D.toBase (specMap ℤ ℚ), pullback.condition⟩)).L) ∧
      (∀ (K' : Type) [Field K'] (t : Spec (CommRingCat.of K') ⟶ Spec (CommRingCat.of ℚ)) (x : SchemeHomOver t (baseChange ℤ c ℚ)),
        Nonempty ((h'.poincare.pullbackAlong
            ⟨x.1 ≫ aj'.1, (Category.assoc _ _ _).trans ((congrArg (x.1 ≫ ·) aj'.2).trans x.2)⟩).L ≅
          (RelEffCartierDiv.ofPoint (baseChange ℤ c ℚ) x.1 x.2).lineBundle ⊗
            (RelEffCartierDiv.ofPoint (baseChange ℤ c ℚ) (t ≫ (sectionBaseChange ℚ ε).1)
              ((Category.assoc _ _ _).trans ((congrArg (t ≫ ·) (sectionBaseChange ℚ ε).2).trans (Category.comp_id t)))).idealModule)) ∧
      (sectionBaseChange ℚ ε).1 ≫ aj'.1 = (D.baseChange ℚ).zeroSection ∧
      (∃ k₀ : pullback c (specMap ℤ (AlgebraicClosure ℚ)) ⟶ pullback c (specMap ℤ ℚ),
        k₀ ≫ pullback.fst c (specMap ℤ ℚ) = pullback.fst c (specMap ℤ (AlgebraicClosure ℚ)) ∧
        k₀ ≫ pullback.snd c (specMap ℤ ℚ) = pullback.snd c (specMap ℤ (AlgebraicClosure ℚ)) ≫ specMap ℚ (AlgebraicClosure ℚ) ∧
        aj = eη ≫ k₀ ≫ aj'.1 ≫ pullback.fst D.toBase (specMap ℤ ℚ)) ∧
      aj ≫ D.toBase = Mη.toBase ≫ specMap ℤ (AlgebraicClosure ℚ) ∧
      εbar.1 ≫ eη ≫ pullback.fst c (specMap ℤ (AlgebraicClosure ℚ)) = specMap ℤ (AlgebraicClosure ℚ) ≫ ε.1 ∧
      εbar.1 ≫ aj = specMap ℤ (AlgebraicClosure ℚ) ≫ D.zeroSection ∧
      (∀ x y : JZero p, pts (x + y) =
        (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c ε) hD).mul
          (specMap ℤ (AlgebraicClosure ℚ)) (pts x) (pts y)) ∧
      (∀ x : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Mη.C // q ≫ Mη.toBase = 𝟙 _},
        ∃ Dv : Divisor.degZero (K := AlgebraicClosure ℚ) (F := modularFunctionFieldBar p),
          (Dv : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar p)) =
            Finsupp.single (Mη.pointEquivPlace x) 1 - Finsupp.single (Mη.pointEquivPlace εbar) 1 ∧
          (pts (Pic0.mk Dv)).1 = x.1 ≫ aj) ∧
      ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (x : JZero p),
        (pts (σ • x)).1 = Spec.map (CommRingCat.ofHom (σ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ)) ≫ (pts x).1 := by
  obtain ⟨h', aj', aj, εbar, pts, hP, haj', hajε', hajover, hεbar, hajs, hadd, hnorm, hk₀, k, hk, hkinv⟩ :=
    exists_abelJacobi_pts_of_representsRelSubPic_baseChange ℤ c ε D hD hsm hgc ℚ hprQ (AlgebraicClosure ℚ)
      (modularFunctionFieldBar p) Mη eη heη
  refine ⟨h', aj', aj, εbar, pts, hP, haj', hajε', hk₀, hajover, hεbar, hajs, hadd, hnorm, ?_⟩
  intro σ x

  have hsec : ∀ s : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Mη.C // q ≫ Mη.toBase = 𝟙 _},
      s.1 ≫ eη ≫ pullback.fst c (specMap ℤ (AlgebraicClosure ℚ)) = specMap ℤ (AlgebraicClosure ℚ) ≫ ε.1 → s = εbar := by
    intro s hs
    apply Subtype.ext
    rw [← cancel_mono eη]
    apply pullback.hom_ext
    · rw [Category.assoc, Category.assoc, hs, hεbar]
    · rw [Category.assoc, Category.assoc, heη, s.2, εbar.2]
  refine L3T_S4.gal_equivariance_int p c ε Mη eη heη hgal (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c ε) hD)
    k pts hadd ?_ σ ?_ x
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

end ModularCurve.L3T

namespace ModularCurve p2m_export "ModularCurve" "DRModel DRModel.toBase DRModelPackage modularFunctionFieldFull arithmeticGalois galois_smul_pic0_def modularFunctionFieldBar JZero geometricallyIntegral_baseChangeToBase_twoChartIntegralModel_rat geometricallyIntegral_baseChangeToBase_twoChartIntegralModel_away DRModelPackage.exists_finiteMapData_baseChange_away_one_le_m" namespace L3T end ModularCurve.L3T
p2m_open_scoped "ModularCurve" in
theorem ModularCurve.L3T.smoothOfRelativeDimension_one_baseChange_rat (p : ℕ) [Fact p.Prime] (𝔛 : DRModelPackage p) :
    SmoothOfRelativeDimension 1 (baseChange ℤ (DRModel.toBase p) ℚ) := by
  have h : baseChange ℤ (DRModel.toBase p) ℚ = inv 𝔛.e₀ ≫ 𝔛.M₀.toBase := by
    rw [← 𝔛.he₀, IsIso.inv_hom_id_assoc]
  rw [h]
  exact inferInstanceAs (SmoothOfRelativeDimension (0 + 1) (inv 𝔛.e₀ ≫ 𝔛.M₀.toBase))

namespace ModularCurve
p2m_export "ModularCurve" "DRModel DRModel.toBase DRModelPackage modularFunctionFieldFull arithmeticGalois galois_smul_pic0_def modularFunctionFieldBar JZero geometricallyIntegral_baseChangeToBase_twoChartIntegralModel_rat geometricallyIntegral_baseChangeToBase_twoChartIntegralModel_away DRModelPackage.exists_finiteMapData_baseChange_away_one_le_m"
namespace L3T
p2m_open "ModularCurve"

theorem isProper_baseChange_rat_of_isProper_baseChange_away {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of ℤ))
    (p : ℕ) [Fact p.Prime]
    (h : IsProper (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap ℤ (Localization.Away (p : ℤ))))))) :
    IsProper (pullback.snd f (specMap ℤ ℚ)) := by

  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  let φ : Localization.Away (p : ℤ) →+* ℚ :=
    IsLocalization.Away.lift (p : ℤ) (g := algebraMap ℤ ℚ) (by simpa using hp0.isUnit)
  have hφ : φ.comp (algebraMap ℤ (Localization.Away (p : ℤ))) = algebraMap ℤ ℚ :=
    IsLocalization.lift_comp _
  let a : Spec (CommRingCat.of (Localization.Away (p : ℤ))) ⟶ Spec (CommRingCat.of ℤ) :=
    Spec.map (CommRingCat.ofHom (algebraMap ℤ (Localization.Away (p : ℤ))))
  let b : Spec (CommRingCat.of ℚ) ⟶ Spec (CommRingCat.of (Localization.Away (p : ℤ))) :=
    Spec.map (CommRingCat.ofHom φ)
  have hba : b ≫ a = specMap ℤ ℚ := by
    change Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hφ]

  have hbig : IsPullback (pullback.fst f (specMap ℤ ℚ)) (pullback.snd f (specMap ℤ ℚ)) f (specMap ℤ ℚ) :=
    IsPullback.of_hasPullback f (specMap ℤ ℚ)
  have hright : IsPullback (pullback.fst f a) (pullback.snd f a) f a := IsPullback.of_hasPullback f a

  let k : pullback f (specMap ℤ ℚ) ⟶ pullback f a :=
    pullback.lift (pullback.fst f (specMap ℤ ℚ)) (pullback.snd f (specMap ℤ ℚ) ≫ b)
      (by rw [Category.assoc, hba]; exact pullback.condition)
  have hk₁ : k ≫ pullback.fst f a = pullback.fst f (specMap ℤ ℚ) := pullback.lift_fst _ _ _
  have hk₂ : k ≫ pullback.snd f a = pullback.snd f (specMap ℤ ℚ) ≫ b := pullback.lift_snd _ _ _
  have hleft : IsPullback k (pullback.snd f (specMap ℤ ℚ)) (pullback.snd f a) b := by
    refine IsPullback.of_right ?_ hk₂ hright
    rw [hk₁, hba]
    exact hbig
  exact MorphismProperty.of_isPullback (P := @IsProper) hleft h

theorem smoothOfRelativeDimension_one_baseChange_away (p : ℕ) [Fact p.Prime] (𝔛 : DRModelPackage p) :
    SmoothOfRelativeDimension 1 (baseChange ℤ (DRModel.toBase p) (Localization.Away (p : ℤ))) := by
  let c := DRModel.toBase p
  let a : Spec (CommRingCat.of (Localization.Away (p : ℤ))) ⟶ Spec (CommRingCat.of ℤ) :=
    specMap ℤ (Localization.Away (p : ℤ))
  let U := 𝔛.smoothLocus

  haveI : Smooth (pullback.snd c a) := 𝔛.smooth_away
  have h1 : Smooth (pullback.fst c a ≫ c) := by
    rw [pullback.condition]; infer_instance

  let W : (DRModel p).Opens := (pullback.fst c a).opensRange
  let e : pullback c a ≅ (W : Scheme.{0}) :=
    IsOpenImmersion.isoOfRangeEq (pullback.fst c a) W.ι (by rw [Scheme.Opens.range_ι, Scheme.Hom.coe_opensRange])
  have he : e.hom ≫ W.ι = pullback.fst c a := IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _
  have hWsm : Smooth (W.ι ≫ c) := by
    have : W.ι ≫ c = e.inv ≫ (pullback.fst c a ≫ c) := by
      rw [← he, Category.assoc, e.inv_hom_id_assoc]
    rw [this]; infer_instance
  have hWU : W ≤ U := 𝔛.smoothLocus_maximal W hWsm

  have hrange : Set.range (pullback.fst c a) ⊆ (U : Set (DRModel p)) := by
    intro x hx
    apply hWU
    change x ∈ (W : Set (DRModel p))
    rw [Scheme.Hom.coe_opensRange]
    exact hx
  haveI hsurj : Surjective (pullback.snd U.ι (pullback.fst c a)) := by
    refine ⟨fun y => ?_⟩
    have hy : y ∈ Set.range (pullback.snd U.ι (pullback.fst c a)) := by
      rw [Scheme.Pullback.range_snd]
      change (pullback.fst c a) y ∈ Set.range U.ι
      rw [Scheme.Opens.range_ι]
      exact hrange ⟨y, rfl⟩
    exact hy
  haveI : IsIso (pullback.snd U.ι (pullback.fst c a)) :=
    (isIso_iff_isOpenImmersion_and_surjective _).mpr ⟨inferInstance, hsurj⟩

  have hcomp : pullback.snd c a =
      inv (pullback.snd U.ι (pullback.fst c a)) ≫ (pullbackRightPullbackFstIso c a U.ι).hom ≫
        pullback.snd (U.ι ≫ c) a := by
    rw [pullbackRightPullbackFstIso_hom_snd, IsIso.inv_hom_id_assoc]
  change SmoothOfRelativeDimension 1 (pullback.snd c a)
  rw [hcomp]
  have hr := (smoothOfRelativeDimension_isStableUnderBaseChange 1).respectsIso
  rw [MorphismProperty.cancel_left_of_respectsIso (P := @SmoothOfRelativeDimension 1),
    MorphismProperty.cancel_left_of_respectsIso (P := @SmoothOfRelativeDimension 1)]
  infer_instance

end ModularCurve.L3T

theorem solution
    (p : ℕ) [Fact p.Prime] (𝔛 : DRModelPackage p) (I : 𝔛.LegTwoInput) [IsProper (DRModel.toBase p)]
    [IsCurveOver (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar p)]
    (D : RelativePic0Designation ℤ (DRModel.toBase p))
    (hD : RepresentsRelSubPic (DRModel.toBase p) 𝔛.εinf (algEquivZeroCut (DRModel.toBase p) 𝔛.εinf) D)
    (hsm : Smooth D.toBase) (hconn : GeometricallyConnected D.toBase) :
    ∃ (h' : RepresentsRelSubPic (baseChange ℤ (DRModel.toBase p) ℚ) (sectionBaseChange ℚ 𝔛.εinf)
          (algEquivZeroCut (baseChange ℤ (DRModel.toBase p) ℚ) (sectionBaseChange ℚ 𝔛.εinf)) (D.baseChange ℚ))
      (ajQ : SchemeHomOver (baseChange ℤ (DRModel.toBase p) ℚ) (D.baseChange ℚ).toBase)
      (aj : 𝔛.Mη.C ⟶ D.P)
      (εbar : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Mη.C // q ≫ 𝔛.Mη.toBase = 𝟙 _})
      (pts : JZero p ≃ SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap ℤ (AlgebraicClosure ℚ)))) D.toBase),

      (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut (DRModel.toBase p) 𝔛.εinf) hD).IsCommutative ∧
      LocallyOfFiniteType D.toBase ∧
      (∀ s : Spec (CommRingCat.of ℤ), _root_.IsPreconnected (D.toBase.base ⁻¹' {s})) ∧
      (∀ x y : JZero p, pts (x + y) =
        (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut (DRModel.toBase p) 𝔛.εinf) hD).mul _
          (pts x) (pts y)) ∧
      (∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (x : JZero p),
        (pts (σ • x)).1 =
          Spec.map (CommRingCat.ofHom (σ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ)) ≫ (pts x).1) ∧
      IsProper (pullback.snd D.toBase
        (Spec.map (CommRingCat.ofHom (algebraMap ℤ (Localization.Away (p : ℤ)))))) ∧

      Nonempty (h'.poincare.L ≅ (BaseChange.ofR (DRModel.toBase p) 𝔛.εinf ℚ
        (hD.poincare.pullbackAlong ⟨pullback.fst D.toBase (specMap ℤ ℚ), pullback.condition⟩)).L) ∧

      (sectionBaseChange ℚ 𝔛.εinf).1 ≫ ajQ.1 = (D.baseChange ℚ).zeroSection ∧
      (∀ (K : Type) [Field K] (t : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of ℚ))
          (x : SchemeHomOver t (baseChange ℤ (DRModel.toBase p) ℚ)),
        Nonempty ((h'.poincare.pullbackAlong
            ⟨x.1 ≫ ajQ.1, (Category.assoc _ _ _).trans ((congrArg (x.1 ≫ ·) ajQ.2).trans x.2)⟩).L ≅
          (RelEffCartierDiv.ofPoint (baseChange ℤ (DRModel.toBase p) ℚ) x.1 x.2).lineBundle ⊗
            (RelEffCartierDiv.ofPoint (baseChange ℤ (DRModel.toBase p) ℚ) (t ≫ (sectionBaseChange ℚ 𝔛.εinf).1)
              ((Category.assoc _ _ _).trans ((congrArg (t ≫ ·) (sectionBaseChange ℚ 𝔛.εinf).2).trans
                (Category.comp_id t)))).idealModule)) ∧

      (∃ k₀ : pullback (DRModel.toBase p) (specMap ℤ (AlgebraicClosure ℚ)) ⟶ pullback (DRModel.toBase p) (specMap ℤ ℚ),
        k₀ ≫ pullback.fst (DRModel.toBase p) (specMap ℤ ℚ) = pullback.fst (DRModel.toBase p) (specMap ℤ (AlgebraicClosure ℚ)) ∧
        k₀ ≫ pullback.snd (DRModel.toBase p) (specMap ℤ ℚ) =
          pullback.snd (DRModel.toBase p) (specMap ℤ (AlgebraicClosure ℚ)) ≫ specMap ℚ (AlgebraicClosure ℚ) ∧
        aj = 𝔛.eη ≫ k₀ ≫ ajQ.1 ≫ pullback.fst D.toBase (specMap ℤ ℚ)) ∧
      aj ≫ D.toBase = 𝔛.Mη.toBase ≫ Spec.map (CommRingCat.ofHom (algebraMap ℤ (AlgebraicClosure ℚ))) ∧
      εbar.1 ≫ 𝔛.eη ≫ pullback.fst (DRModel.toBase p) _ =
        Spec.map (CommRingCat.ofHom (algebraMap ℤ (AlgebraicClosure ℚ))) ≫ 𝔛.εinf.1 ∧
      εbar.1 ≫ aj = Spec.map (CommRingCat.ofHom (algebraMap ℤ (AlgebraicClosure ℚ))) ≫ D.zeroSection ∧
      ∀ x : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Mη.C // q ≫ 𝔛.Mη.toBase = 𝟙 _},
        ∃ Dv : Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar p)),
          (Dv : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar p)) =
            Finsupp.single (𝔛.Mη.pointEquivPlace x) 1 - Finsupp.single (𝔛.Mη.pointEquivPlace εbar) 1 ∧
          (pts (Pic0.mk Dv)).1 = x.1 ≫ aj := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  haveI := ModularCurve.L3T.smoothOfRelativeDimension_one_baseChange_rat p 𝔛
  haveI : GeometricallyIntegral (baseChange ℤ (DRModel.toBase p) ℚ) :=
    ModularCurve.geometricallyIntegral_baseChangeToBase_twoChartIntegralModel_rat p

  have hpa : IsProper (pullback.snd D.toBase (Spec.map (CommRingCat.ofHom (algebraMap ℤ (Localization.Away (p : ℤ)))))) := by

    haveI := ModularCurve.L3T.smoothOfRelativeDimension_one_baseChange_away p 𝔛
    haveI : GeometricallyIntegral (baseChange ℤ (DRModel.toBase p) (Localization.Away (p : ℤ))) :=
      ModularCurve.geometricallyIntegral_baseChangeToBase_twoChartIntegralModel_away p
    obtain ⟨hDaway, -⟩ := AlgebraicGeometry.RelPicard.exists_representsRelSubPic_baseChange ℤ (DRModel.toBase p) 𝔛.εinf D hD
      (Localization.Away (p : ℤ))

    obtain ⟨𝔉₀, h𝔉₀⟩ := ModularCurve.DRModelPackage.exists_finiteMapData_baseChange_away_one_le_m p 𝔛
    have h𝔉 : ∀ m₀ : ℕ, ∃ 𝔉 : SmoothProperCurve.FiniteMapData (baseChange ℤ (DRModel.toBase p) (Localization.Away (p : ℤ)))
        (sectionBaseChange (Localization.Away (p : ℤ)) 𝔛.εinf), m₀ ≤ 𝔉.m := fun m₀ => by
      obtain ⟨𝔉', h', -, -⟩ := AlgebraicGeometry.SmoothProperCurve.FiniteMapData.forall_exists_le_m_of_one_le 𝔉₀ h𝔉₀ m₀
      exact ⟨𝔉', h'⟩

    haveI : IsDomain (Localization.Away (p : ℤ)) :=
      IsLocalization.isDomain_of_le_nonZeroDivisors (M := Submonoid.powers (p : ℤ)) _
        (powers_le_nonZeroDivisors_of_noZeroDivisors (show (p : ℤ) ≠ 0 by exact_mod_cast (Fact.out : p.Prime).ne_zero))
    haveI : ConnectedSpace (PrimeSpectrum (Localization.Away (p : ℤ))) := inferInstance
    obtain ⟨g, hg⟩ := AlgebraicGeometry.SmoothProperCurve.exists_genus_forall_geometricFibre_riemannRoch_imp_eq_of_connectedSpace
      (Localization.Away (p : ℤ)) (baseChange ℤ (DRModel.toBase p) (Localization.Away (p : ℤ)))
      (sectionBaseChange (Localization.Away (p : ℤ)) 𝔛.εinf) 𝔉₀
    haveI : LocallyOfFiniteType (D.baseChange (Localization.Away (p : ℤ))).toBase := by
      rw [RelativePic0Designation.baseChange_toBase]; infer_instance
    have := (AlgebraicGeometry.RelPicard.isProper_and_geometricallyConnected_of_representsRelSubPic_algEquivZeroCut_of_finiteMapData
      (Localization.Away (p : ℤ)) (baseChange ℤ (DRModel.toBase p) (Localization.Away (p : ℤ)))
      (sectionBaseChange (Localization.Away (p : ℤ)) 𝔛.εinf) h𝔉 g hg (D.baseChange (Localization.Away (p : ℤ))) hDaway).1
    rwa [RelativePic0Designation.baseChange_toBase] at this
  have hprQ : IsProper (D.baseChange ℚ).toBase := by
    rw [RelativePic0Designation.baseChange_toBase]
    exact ModularCurve.L3T.isProper_baseChange_rat_of_isProper_baseChange_away D.toBase p hpa
  obtain ⟨h', ajQ, aj, εbar, pts, hP, haj', hajε', hk₀, hajover, hεbar, hajs, hadd, hnorm, hgalois⟩ :=
    ModularCurve.L3T.exists_abelJacobi_pts_galois p (DRModel.toBase p) 𝔛.εinf D hD hsm hconn hprQ 𝔛.Mη 𝔛.eη 𝔛.heη 𝔛.hgal
  haveI : Smooth D.toBase := hsm
  haveI : GeometricallyConnected D.toBase := hconn
  refine ⟨h', ajQ, aj, εbar, pts, ?_, inferInstance, ?_, hadd, hgalois, hpa, hP, hajε', haj', hk₀, hajover, hεbar, hajs, hnorm⟩
  · exact RepresentsRelSubPic.relativeGroupLaw_isCommutative (P := algEquivZeroGroupCut (DRModel.toBase p) 𝔛.εinf) hD
  · intro s
    exact (D.toBase.isConnected_preimage_singleton s).isPreconnected

end S_ModularCurve_exists_abelJacobi_pts_relativeGroupLaw_of_dRModelPackage_of_representsRelSubPic
end P2MW
export P2MW.S_ModularCurve_exists_abelJacobi_pts_relativeGroupLaw_of_dRModelPackage_of_representsRelSubPic (solution)
