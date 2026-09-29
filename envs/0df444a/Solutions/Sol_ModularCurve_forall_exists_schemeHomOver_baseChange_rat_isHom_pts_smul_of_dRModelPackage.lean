-- Prove2me | solution 1 for ModularCurve.forall_exists_schemeHomOver_baseChange_rat_isHom_pts_smul_of_dRModelPackage
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/99efd012-4f97-5546-888d-8cf8bc49697b

import Mathlib
import Definitions.Def_ModularCurve_DRModelPackage
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_AlgebraicGeometry_RelSubPicGroup
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_ModularCurve_HeckeModule
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivOfPoint
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicGeometry_RelSubPicBaseChange
import Definitions.Def_AlgebraicGeometry_RelativePic0DesignationBaseChange
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_GaloisRep_Flat
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_ModularCurve_GeometricBaseChange
import Definitions.Def_ModularCurve_LaurentCoeff
import Definitions.Def_AlgebraicCurve_CurveModelConstruction
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_ModularCurve_X0
import Definitions.Def_ModularCurve_HeckeOperator
import Definitions.Def_ModularCurve_IgusaScheme
import Theorems.Thm_AlgebraicCurve_CurveModel_exists_hom_of_algHom
import Theorems.Thm_ModularCurve_heckeAlphaBarIntegral_of_prime
import Theorems.Thm_ModularCurve_heckeBetaBarIntegral_of_prime
import Theorems.Thm_ModularCurve_finiteAlong_heckeAlphaBar_of_prime
import Theorems.Thm_ModularCurve_finiteAlong_heckeBetaBar_of_prime
import Theorems.Thm_ModularCurve_transcendental_jq
import Theorems.Thm_ModularCurve_finiteDimensional_adjoin_jFull_modularFunctionFieldFull
import Theorems.Thm_ModularCurve_coeffMap_qExpand
import Definitions.Def_AlgebraicGeometry_RelPicardPullback
import Definitions.Def_AlgebraicGeometry_RigidifiedLineBundleOfInvertible
import Definitions.Def_AlgebraicGeometry_ModulesNormModule
import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidal
import Theorems.Thm_AlgebraicGeometry_Scheme_Hom_finrank_pullbackMap_of_comp_eq
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_normModule
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_nonempty_pullback_normModule_iso
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_nonempty_normModule_unit_iso
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_nonempty_normModule_tensor_iso
import Theorems.Thm_AlgebraicGeometry_RelPicard_FibrewiseAlgEquivZero_ofInvertible_normModule_curveChange
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Theorems.Thm_AlgebraicGeometry_RelPicard_exists_representsRelSubPic_baseChange
import Theorems.Thm_NeronModelInfra_NeronModelPropertyBundle_of_abelianSchemePropertyBundle
import Theorems.Thm_AlgebraicGeometry_RelPicard_exists_pic0_equiv_points_of_representsRelSubPic_of_abelJacobi
import Theorems.Thm_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_existsUnique_hom_of_transform
import Theorems.Thm_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_comp_mul_eq_mul_comp_of_transform
import Theorems.Thm_GaloisRep_isDiscreteValuationRing_ratLocalizedAt
import Theorems.Thm_GaloisRep_isFractionRing_ratLocalizedAt
import Theorems.Thm_AlgebraicGeometry_RelPicard_schemeHomOverComp_relativeGroupLaw_mul_endExtensionEquiv_symm
import Definitions.Def_JacJ1_ChartAlgebra
import Definitions.Def_ModularCurve_FibreModel
import Definitions.Def_ModularCurve_X0ModL
import Theorems.Thm_ModularCurve_IgusaScheme_exists_algEquiv_rat_tensor_chartAlg_chartRing
import Theorems.Thm_ModularCurve_IgusaScheme_exists_algEquiv_tensor_chartAlg_chartRing
import Theorems.Thm_ModularCurve_pointEquivPlace_comp_eq_restrictAlong_of_baseChange
import Theorems.Thm_ModularCurve_exists_ofGenerator_baseChangeIso_chartPin_and_placeCompat
import Theorems.Thm_ModularCurve_heckeOperatorBar_points_eq_comp_of_transform
import Theorems.Thm_ModularCurve_transcendental_jqModC
import Theorems.Thm_ModularCurve_coeffEmb_jq
import Theorems.Thm_ModularCurve_isCurveOver_modularFunctionFieldBar
import Theorems.Thm_ModularCurve_essFiniteType_modularFunctionFieldBar
import Theorems.Thm_AlgebraicCurve_isCurveOver_iff_exists_transcendental_finiteDimensional
import Theorems.Thm_AlgebraicCurve_finiteDimensional_adjoin_of_transcendental
import Theorems.Thm_AlgebraicGeometry_RelPicard_baseChange_relativeGroupLaw_mul_compat
import Theorems.Thm_ModularCurve_heckeOperatorsCommuteBar
import Theorems.Thm_ModularCurve_heckeOperatorBar_points_eq_comp_of_transform_rat
import Theorems.Thm_ModularCurve_geometricallyIntegral_baseChangeToBase_twoChartIntegralModel_rat
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_forall_exists_schemeHomOver_baseChange_rat_isHom_pts_smul_of_dRModelPackage
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions SheafOfModules.isIso_ihomModelToIhom instTopologicallyFGOfFiniteType AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instNeg AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulInt AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAddCommGroup AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAdd AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSub AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulNat AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instZero AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom"
p2m_attr_erase "instance" "AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion AlgebraicGeometry.RelEffCartierDiv.subsingleton_of_degree_zero AlgebraicGeometry.OModulePresheaf.isScalarTower AlgebraicGeometry.Scheme.OrderedAffineCover.instLinearOrder AlgebraicGeometry.OModulePresheaf.module AlgebraicGeometry.Scheme.OrderedAffineCover.instFintype AlgebraicGeometry.Scheme.OrderedAffineCover.instFintypeIdx AlgebraicGeometry.OModulePresheaf.addCommGroup AlgebraicGeometry.Scheme.OrderedAffineCover.instDecidableEqIdx AlgebraicGeometry.OModulePresheaf.moduleSections AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π"
p2m_attr_erase "instance" "AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule instIsScalarTowerIntegralClosure instNeZeroIdealUnderOfNontrivialOfIsDomainOfIsIntegral_definitions instAlgebraIntegralClosure_1 isInvariant_integralClosure instAlgebraIntegralClosure continuousSMulDiscrete_integralClosure mulSemiringActionIntegralClosure smulCommClass_integralClosure instIsDomainIntegralClosure instIsIntegralIntegralClosure instCommRingIntegralClosure instFaithfulSMulIntegralClosure instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions"
p2m_attr_erase "instance" "WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent ModularCurve.B3.instIsElliptic_goodModel ModularCurve.instIsScalarTowerJAdjoin WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero"
p2m_attr_erase "simp" "ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ PresheafOfModules.pushforwardCongr_inv_app_app_apply PresheafOfModules.pushforwardNatTrans_app_app_apply PresheafOfModules.pushforwardCongr_hom_app_app_apply TwoChartCech.Mumford.dK_apply TwoChartCech.Mumford.ι0_apply TwoChartCech.Mumford.ι1_apply TwoChartCech.KerCoprod.dK_apply TwoChartCech.KerCoprod.ι1_apply TwoChartCech.KerCoprod.ι0_apply AlgebraicGeometry.Scheme.Modules.toUnitSection_ofUnitSection"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.Modules.pullbackSection_def AlgebraicGeometry.Scheme.Modules.ofUnitSection_toUnitSection PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom SheafOfModules.ihomSectionsEquivFamily_unit AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply SheafOfModules.ihomEval_unit_app AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply SheafOfModules.unit_ihomSectionsEquivFamily AlgebraicGeometry.Scheme.Modules.familyOfHom_app AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply RegularLocalRingQuotientAscent.dualNumberFst_apply AlgebraicGeometry.RelPicard.fst_toProdSpec AlgebraicGeometry.RelPicard.toProdSpec_fst_assoc AlgebraicGeometry.RelPicard.pointsSubBasepointModule_cons AlgebraicGeometry.RelPicard.pointsSubBasepointModule_nil AlgebraicGeometry.RelPicard.fst_toProdSpec_assoc AlgebraicGeometry.RelPicard.toProdSpec_fst AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.sub_app AlgebraicGeometry.Scheme.IdealSheafData.sres_sresTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.add_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.sizeOf_spec AlgebraicGeometry.Scheme.IdealSheafData.coe_resLE AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.smul_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_ofLE_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.ideal_range AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zero_app AlgebraicGeometry.Scheme.IdealSheafData.sres_sres AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.comp_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.neg_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.id_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_mulRight_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.nsmul_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.injEq AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zsmul_app AlgebraicGeometry.RelPicard.thetaBundle_def"
p2m_attr_erase "simp" "AlgebraicGeometry.RelPicard.picardBundle_def AlgebraicGeometry.SmoothProperCurve.FiniteMapData.twoAffineOpenCover_U1 AlgebraicGeometry.SmoothProperCurve.FiniteMapData.mk.injEq AlgebraicGeometry.SmoothProperCurve.FiniteMapData.mk.sizeOf_spec AlgebraicGeometry.SmoothProperCurve.FiniteMapData.twoAffineOpenCover_U0 AlgebraicCurve.coe_cechH0Equiv_apply AlgebraicCurve.cechH1ToH1_mk AlgebraicCurve.lSpaceOn_univ AlgebraicCurve.lSpaceOn_empty AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule AlgebraicGeometry.prodKerGraph_one AlgebraicGeometry.fibrePowOver.proj_comp AlgebraicGeometry.prodKerGraph_zero AlgebraicGeometry.RelEffCartierDiv.empty_I AlgebraicGeometry.fibrePowOver.proj_comp_assoc AlgebraicCurve.SymmetricPowerPackage.mk.sizeOf_spec AlgebraicCurve.SymmetricPowerPackage.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.mk.injEq"
p2m_attr_erase "simp" "AlgebraicGeometry.OModulePresheaf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.mk.injEq AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U"
p2m_attr_erase "simp" "DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_cuspidalDivisor₀ ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven"
p2m_attr_erase "simp" "ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar HahnSeries.ramScale_apply WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply ModularCurve.CharPReduction.coeffRed_coeff ModularCurve.CharPReduction.redLocHom_apply AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap ModularCurve.cuspCount_one ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one"
p2m_attr_erase "simp" "WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm"
p2m_attr_erase "simp" "ModularCurve.ProjectiveLine.map_mk ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton"
p2m_attr_erase "simp" "WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right"
p2m_attr_erase "simp" "FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff ModularCurve.PlaceSpecialization.mk.injEq ModularCurve.PlaceSpecialization.mk.sizeOf_spec"

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra GoodReductionJacobian ModularCurve~jBar P2MW.S_ModularCurve_forall_exists_schemeHomOver_baseChange_rat_isHom_pts_smul_of_dRModelPackage.ModularCurve AlgebraicCurve AlgebraicGeometry.SmoothProperCurve"

universe u

open scoped TensorProduct
p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry ModularCurve~jBar P2MW.S_ModularCurve_forall_exists_schemeHomOver_baseChange_rat_isHom_pts_smul_of_dRModelPackage.ModularCurve AlgebraicCurve AlgebraicGeometry.SmoothProperCurve ModularCurve.IgusaScheme"

set_option linter.unusedSectionVars false

noncomputable section

namespace ModularCurve
p2m_export "ModularCurve" "DRModel DRModel.toBase DRModelPackage qExpand modularFunctionFieldFull full_degeneracy_le full_degeneracy_map_le IgusaScheme.jFull IgusaScheme baseChangeEquiv baseChangeEquiv_one_tmul coeffMap_id coeffMap_congr coeffEmb laurentBaseChange coeffEmb_mem_laurentBaseChange arithmeticGalois modularFunctionFieldBar JZero heckeOperatorBar heckeModuleBar heckeModuleBar_heckeGen_smul heckeModuleBar_C_smul heckeAlphaBar coe_heckeAlphaBar heckeBetaBar coe_heckeBetaBar HeckeAlphaBarIntegral HeckeBetaBarIntegral HeckeAlg heckeAlphaBarIntegral_of_prime heckeBetaBarIntegral_of_prime finiteAlong_heckeAlphaBar_of_prime finiteAlong_heckeBetaBar_of_prime transcendental_jq finiteDimensional_adjoin_jFull_modularFunctionFieldFull jqModC coeffMap_qExpand CharPModel.jBar pointEquivPlace_comp_eq_restrictAlong_of_baseChange exists_ofGenerator_baseChangeIso_chartPin_and_placeCompat transcendental_jqModC coeffEmb_jq isCurveOver_modularFunctionFieldBar essFiniteType_modularFunctionFieldBar heckeOperatorsCommuteBar heckeOperatorBar_points_eq_comp_of_transform_rat geometricallyIntegral_baseChangeToBase_twoChartIntegralModel_rat"
namespace HeckeGenQStepB
p2m_open "ModularCurve~jBar"

open IntermediateField

section Maps

variable (p q : ℕ) [NeZero p] [NeZero q]

def alpha0 : ↥(modularFunctionFieldFull p) →+* ↥(modularFunctionFieldFull (p * q)) :=
  RingHomClass.toRingHom
    (IntermediateField.inclusion (full_degeneracy_le (N := p) (M := p * q) (dvd_mul_right p q)))

@[scoped simp] theorem coe_alpha0 (x : ↥(modularFunctionFieldFull p)) :
    (alpha0 p q x : LaurentSeries ℚ) = x :=
  IntermediateField.coe_inclusion (full_degeneracy_le (N := p) (M := p * q) (dvd_mul_right p q)) x

def beta0 : ↥(modularFunctionFieldFull p) →+* ↥(modularFunctionFieldFull (p * q)) where
  toFun x := ⟨qExpand ℚ q (x : LaurentSeries ℚ), full_degeneracy_map_le (N := p) q ⟨x, x.2, rfl⟩⟩
  map_one' := Subtype.ext (map_one (qExpand ℚ q))
  map_mul' _ _ := Subtype.ext (map_mul (qExpand ℚ q) _ _)
  map_zero' := Subtype.ext (map_zero (qExpand ℚ q))
  map_add' _ _ := Subtype.ext (map_add (qExpand ℚ q) _ _)

@[scoped simp] theorem coe_beta0 (x : ↥(modularFunctionFieldFull p)) :
    (beta0 p q x : LaurentSeries ℚ) = qExpand ℚ q (x : LaurentSeries ℚ) := rfl

def alpha0ₐ : ↥(modularFunctionFieldFull p) →ₐ[ℚ] ↥(modularFunctionFieldFull (p * q)) :=
  (alpha0 p q).toRatAlgHom

def beta0ₐ : ↥(modularFunctionFieldFull p) →ₐ[ℚ] ↥(modularFunctionFieldFull (p * q)) :=
  (beta0 p q).toRatAlgHom

@[scoped simp] theorem alpha0ₐ_toRingHom : (alpha0ₐ p q).toRingHom = alpha0 p q := rfl
@[scoped simp] theorem beta0ₐ_toRingHom : (beta0ₐ p q).toRingHom = beta0 p q := rfl
@[scoped simp] theorem alpha0ₐ_apply (x) : alpha0ₐ p q x = alpha0 p q x := rfl
@[scoped simp] theorem beta0ₐ_apply (x) : beta0ₐ p q x = beta0 p q x := rfl

end Maps

section Transport

theorem coeffEmb_rat_apply (x : LaurentSeries ℚ) : coeffEmb ℚ x = x := by
  have h : algebraMap ℚ ℚ = RingHom.id ℚ := RingHom.ext_rat _ _
  rw [coeffEmb, coeffMap_congr h, coeffMap_id]

theorem laurentBaseChange_rat (F₀ : IntermediateField ℚ (LaurentSeries ℚ)) :
    laurentBaseChange ℚ F₀ = F₀ := by
  have himg : ⇑(coeffEmb ℚ) '' (F₀ : Set (LaurentSeries ℚ)) = F₀ := by
    ext x
    simp only [Set.mem_image, coeffEmb_rat_apply, exists_eq_right, SetLike.mem_coe]
  rw [laurentBaseChange, himg]
  exact IntermediateField.adjoin_self ℚ F₀

theorem transport {E₁ E₂ E₁' E₂' : IntermediateField ℚ (LaurentSeries ℚ)}
    (h₁ : E₁ = E₁') (h₂ : E₂ = E₂') (φ : ↥E₁ →+* ↥E₂) (φ' : ↥E₁' →+* ↥E₂')
    (hφ : ∀ (x : ↥E₁) (x' : ↥E₁'), (x : LaurentSeries ℚ) = x' →
      (φ x : LaurentSeries ℚ) = φ' x') :
    (φ.IsIntegral → φ'.IsIntegral) ∧
    (@Module.Finite ↥E₁ ↥E₂ _ _ φ.toAlgebra.toModule →
      @Module.Finite ↥E₁' ↥E₂' _ _ φ'.toAlgebra.toModule) ∧
    @Module.finrank ↥E₁ ↥E₂ _ _ φ.toAlgebra.toModule =
      @Module.finrank ↥E₁' ↥E₂' _ _ φ'.toAlgebra.toModule := by
  subst h₁ h₂
  obtain rfl : φ = φ' := RingHom.ext fun x => Subtype.ext (hφ x x rfl)
  exact ⟨id, id, rfl⟩

variable (p q : ℕ) [NeZero p] [Fact q.Prime]

theorem alpha0_isIntegral : (alpha0 p q).IsIntegral :=
  (transport (laurentBaseChange_rat _) (laurentBaseChange_rat _)
    (heckeAlphaBar ℚ p q : laurentBaseChange ℚ (modularFunctionFieldFull p) →+*
      laurentBaseChange ℚ (modularFunctionFieldFull (p * q))) (alpha0 p q)
    (fun x x' h => by simpa using h)).1 (heckeAlphaBarIntegral_of_prime ℚ p q)

theorem beta0_isIntegral : (beta0 p q).IsIntegral :=
  (transport (laurentBaseChange_rat _) (laurentBaseChange_rat _)
    (heckeBetaBar ℚ p q : laurentBaseChange ℚ (modularFunctionFieldFull p) →+*
      laurentBaseChange ℚ (modularFunctionFieldFull (p * q))) (beta0 p q)
    (fun x x' h => by simp [h])).1 (heckeBetaBarIntegral_of_prime ℚ p q)

theorem alpha0_finiteAlong : FiniteAlong ℚ (alpha0ₐ p q) :=
  (transport (laurentBaseChange_rat _) (laurentBaseChange_rat _)
    (heckeAlphaBar ℚ p q : laurentBaseChange ℚ (modularFunctionFieldFull p) →+*
      laurentBaseChange ℚ (modularFunctionFieldFull (p * q))) (alpha0 p q)
    (fun x x' h => by simpa using h)).2.1 (finiteAlong_heckeAlphaBar_of_prime ℚ p q)

theorem beta0_finiteAlong : FiniteAlong ℚ (beta0ₐ p q) :=
  (transport (laurentBaseChange_rat _) (laurentBaseChange_rat _)
    (heckeBetaBar ℚ p q : laurentBaseChange ℚ (modularFunctionFieldFull p) →+*
      laurentBaseChange ℚ (modularFunctionFieldFull (p * q))) (beta0 p q)
    (fun x x' h => by simp [h])).2.1 (finiteAlong_heckeBetaBar_of_prime ℚ p q)

end Transport

section IsoTransport

variable {Y X X' : Scheme.{0}} (π : Y ⟶ X) (e : X ⟶ X') [IsIso e]

theorem isFinite_comp_iso [IsFinite π] : IsFinite (π ≫ e) := inferInstance
theorem flat_comp_iso [Flat π] : Flat (π ≫ e) := inferInstance
theorem lfp_comp_iso [LocallyOfFinitePresentation π] : LocallyOfFinitePresentation (π ≫ e) :=
  inferInstance

theorem finrank_comp_iso [Flat π] [IsFinite π] (x' : X') :
    (π ≫ e).finrank x' = π.finrank ((inv e).base x') := by
  have hsq : IsPullback (𝟙 Y) (π ≫ e) π (inv e) := IsPullback.of_horiz_isIso ⟨by simp⟩
  exact Scheme.Hom.finrank_of_isPullback (𝟙 Y) (π ≫ e) π (inv e) hsq x'

end IsoTransport

section Main

variable (p q : ℕ) [NeZero p] [Fact q.Prime]
  (htrans₀ : Transcendental ℚ (jFull (p * q)))
  [hfd₀ : FiniteDimensional
    ↥(IntermediateField.adjoin ℚ ({jFull (p * q)} : Set ↥(modularFunctionFieldFull (p * q))))
    ↥(modularFunctionFieldFull (p * q))]
  [hfd_inv₀ : FiniteDimensional
    ↥(IntermediateField.adjoin ℚ ({(jFull (p * q))⁻¹} : Set ↥(modularFunctionFieldFull (p * q))))
    ↥(modularFunctionFieldFull (p * q))]

theorem stepB {Xℚ : Scheme.{0}} (bℚ : Xℚ ⟶ Spec (CommRingCat.of ℚ))
    (M₀ : CurveModel ℚ ↥(modularFunctionFieldFull p))
    (e₀ : M₀.C ⟶ Xℚ) [IsIso e₀] (he₀ : e₀ ≫ bℚ = M₀.toBase) :
    let M₀' : CurveModel ℚ ↥(modularFunctionFieldFull (p * q)) :=
      CurveModel.ofGenerator ℚ (jFull (p * q)) htrans₀
    ∃ (πα₀ πβ₀ : M₀'.C ⟶ M₀.C),

      πα₀ ≫ M₀.toBase = M₀'.toBase ∧ πβ₀ ≫ M₀.toBase = M₀'.toBase ∧
      (πα₀ ≫ e₀) ≫ bℚ = M₀'.toBase ∧ (πβ₀ ≫ e₀) ≫ bℚ = M₀'.toBase ∧

      IsFinite (πα₀ ≫ e₀) ∧ Flat (πα₀ ≫ e₀) ∧ LocallyOfFinitePresentation (πα₀ ≫ e₀) ∧
      (∀ y, (πα₀ ≫ e₀).finrank y = finrankAlong ℚ (alpha0ₐ p q)) ∧
      IsFinite (πβ₀ ≫ e₀) ∧ Flat (πβ₀ ≫ e₀) ∧ LocallyOfFinitePresentation (πβ₀ ≫ e₀) ∧
      (∀ y, (πβ₀ ≫ e₀).finrank y = finrankAlong ℚ (beta0ₐ p q)) ∧

      IsFinite πα₀ ∧ Flat πα₀ ∧ LocallyOfFinitePresentation πα₀ ∧
      IsFinite πβ₀ ∧ Flat πβ₀ ∧ LocallyOfFinitePresentation πβ₀ ∧

      M₀'.C.fromSpecStalk (genericPoint M₀'.C) ≫ πα₀ =
        Spec.map (CommRingCat.ofHom
          (M₀'.ffEquiv.toRingHom.comp ((alpha0 p q).comp M₀.ffEquiv.symm.toRingHom))) ≫
          M₀.C.fromSpecStalk (genericPoint M₀.C) ∧
      M₀'.C.fromSpecStalk (genericPoint M₀'.C) ≫ πβ₀ =
        Spec.map (CommRingCat.ofHom
          (M₀'.ffEquiv.toRingHom.comp ((beta0 p q).comp M₀.ffEquiv.symm.toRingHom))) ≫
          M₀.C.fromSpecStalk (genericPoint M₀.C) ∧

      (∀ y : closedPoints M₀'.C, ∃ h : πα₀.base y.1 ∈ closedPoints M₀.C,
        M₀.placeOfPoint ⟨πα₀.base y.1, h⟩ =
          (M₀'.placeOfPoint y).restrictAlong (alpha0ₐ p q) (alpha0_isIntegral p q)) ∧
      (∀ y : closedPoints M₀'.C, ∃ h : πβ₀.base y.1 ∈ closedPoints M₀.C,
        M₀.placeOfPoint ⟨πβ₀.base y.1, h⟩ =
          (M₀'.placeOfPoint y).restrictAlong (beta0ₐ p q) (beta0_isIntegral p q)) := by
  intro M₀'
  obtain ⟨πα₀, hαb, hαfin, hαfl, hαlfp, hαrk, hαgen, hαpl, -⟩ :=
    CurveModel.exists_hom_of_algHom M₀ M₀' (alpha0ₐ p q) (alpha0_isIntegral p q)
      (alpha0_finiteAlong p q)
  obtain ⟨πβ₀, hβb, hβfin, hβfl, hβlfp, hβrk, hβgen, hβpl, -⟩ :=
    CurveModel.exists_hom_of_algHom M₀ M₀' (beta0ₐ p q) (beta0_isIntegral p q)
      (beta0_finiteAlong p q)
  refine ⟨πα₀, πβ₀, hαb, hβb, ?_, ?_, isFinite_comp_iso _ _, flat_comp_iso _ _, lfp_comp_iso _ _,
    ?_, isFinite_comp_iso _ _, flat_comp_iso _ _, lfp_comp_iso _ _, ?_,
    hαfin, hαfl, hαlfp, hβfin, hβfl, hβlfp, hαgen, hβgen, hαpl, hβpl⟩
  · rw [Category.assoc, he₀, hαb]
  · rw [Category.assoc, he₀, hβb]
  · intro y; rw [finrank_comp_iso, hαrk]
  · intro y; rw [finrank_comp_iso, hβrk]

include htrans₀ hfd₀ hfd_inv₀ in

theorem stepB_obtain {Xℚ : Scheme.{0}} (bℚ : Xℚ ⟶ Spec (CommRingCat.of ℚ))
    (M₀ : CurveModel ℚ ↥(modularFunctionFieldFull p))
    (e₀ : M₀.C ⟶ Xℚ) [IsIso e₀] (he₀ : e₀ ≫ bℚ = M₀.toBase) :
    ∃ (Y : Scheme.{0}) (cY : Y ⟶ Spec (CommRingCat.of ℚ)) (πα πβ : Y ⟶ Xℚ),
      πα ≫ bℚ = cY ∧ πβ ≫ bℚ = cY ∧
      ∃ d : ℕ, IsFinite πα ∧ Flat πα ∧ LocallyOfFinitePresentation πα ∧ (∀ y, πα.finrank y = d) ∧
        IsFinite πβ ∧ Flat πβ ∧ LocallyOfFinitePresentation πβ := by
  obtain ⟨πα₀, πβ₀, -, -, hα, hβ, h1, h2, h3, h4, h5, h6, h7, -⟩ :=
    stepB p q htrans₀ bℚ M₀ e₀ he₀
  exact ⟨_, _, πα₀ ≫ e₀, πβ₀ ≫ e₀, hα, hβ, _, h1, h2, h3, h4, h5, h6, h7⟩

end Main

section Inputs

variable (N : ℕ) [NeZero N]

theorem transcendental_jFull : Transcendental ℚ (jFull N) := fun halg =>
  transcendental_jq (by
    simpa using halg.algHom (SubringClass.subtype (modularFunctionFieldFull N)).toRatAlgHom)

scoped instance finiteDimensional_adjoin_jFull :
    FiniteDimensional ↥(IntermediateField.adjoin ℚ ({jFull N} : Set ↥(modularFunctionFieldFull N)))
      ↥(modularFunctionFieldFull N) :=
  finiteDimensional_adjoin_jFull_modularFunctionFieldFull N

scoped instance finiteDimensional_adjoin_jFull_inv :
    FiniteDimensional ↥(IntermediateField.adjoin ℚ ({(jFull N)⁻¹} : Set ↥(modularFunctionFieldFull N)))
      ↥(modularFunctionFieldFull N) :=
  CurveModel.finiteDimensional_congr ℚ (CurveModel.adjoin_simple_inv_eq ℚ (jFull N)).symm

example (p q : ℕ) [NeZero p] [Fact q.Prime] : CurveModel ℚ ↥(modularFunctionFieldFull (p * q)) :=
  CurveModel.ofGenerator ℚ (jFull (p * q)) (transcendental_jFull (p * q))

end Inputs

section BaseChangeCompat

variable (L : Type*) [Field L] [Algebra ℚ L] [Algebra.IsAlgebraic ℚ L] (p q : ℕ) [NeZero p] [NeZero q]

theorem alpha0_baseChange (f : ↥(modularFunctionFieldFull p)) :
    heckeAlphaBar L p q (baseChangeEquiv L (modularFunctionFieldFull p) (1 ⊗ₜ f)) =
      baseChangeEquiv L (modularFunctionFieldFull (p * q)) (1 ⊗ₜ alpha0 p q f) := by
  apply Subtype.ext
  rw [coe_heckeAlphaBar, baseChangeEquiv_one_tmul, baseChangeEquiv_one_tmul]
  dsimp only
  rw [coe_alpha0]

theorem beta0_baseChange (f : ↥(modularFunctionFieldFull p)) :
    heckeBetaBar L p q (baseChangeEquiv L (modularFunctionFieldFull p) (1 ⊗ₜ f)) =
      baseChangeEquiv L (modularFunctionFieldFull (p * q)) (1 ⊗ₜ beta0 p q f) := by
  apply Subtype.ext
  rw [coe_heckeBetaBar, baseChangeEquiv_one_tmul, baseChangeEquiv_one_tmul]
  dsimp only
  rw [coe_beta0, coeffEmb, coeffMap_qExpand]

end BaseChangeCompat

end ModularCurve.HeckeGenQStepB
p2m_reactivate "P2MW.S_ModularCurve_forall_exists_schemeHomOver_baseChange_rat_isHom_pts_smul_of_dRModelPackage.ModularCurve P2MW.S_ModularCurve_forall_exists_schemeHomOver_baseChange_rat_isHom_pts_smul_of_dRModelPackage.ModularCurve.HeckeGenQStepB"
p2m_reactivate "P2MW.S_ModularCurve_forall_exists_schemeHomOver_baseChange_rat_isHom_pts_smul_of_dRModelPackage.ModularCurve"

end
p2m_reactivate "P2MW.S_ModularCurve_forall_exists_schemeHomOver_baseChange_rat_isHom_pts_smul_of_dRModelPackage.ModularCurve P2MW.S_ModularCurve_forall_exists_schemeHomOver_baseChange_rat_isHom_pts_smul_of_dRModelPackage.ModularCurve.HeckeGenQStepB"

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve ModularCurve~jBar P2MW.S_ModularCurve_forall_exists_schemeHomOver_baseChange_rat_isHom_pts_smul_of_dRModelPackage.ModularCurve"
open scoped TensorProduct

namespace Lp

theorem exists_iso_pullback_of_pasting {S T T' X P P' : Scheme.{u}}
    (c : X ⟶ S) (g : T ⟶ S) (g' : T' ⟶ T) (gg : T' ⟶ S) (hgg : g' ≫ g = gg)
    (eη : P' ⟶ pullback c gg) [IsIso eη] (b' : P' ⟶ T') (heη : eη ≫ pullback.snd c gg = b')
    (e₀ : P ⟶ pullback c g) [IsIso e₀] (b : P ⟶ T) (he₀ : e₀ ≫ pullback.snd c g = b) :
    ∃ (e : P' ⟶ pullback b g') (k : pullback c gg ⟶ pullback c g) (_ : IsIso e),
      e ≫ pullback.snd b g' = b' ∧
      k ≫ pullback.fst c g = pullback.fst c gg ∧
      e ≫ pullback.fst b g' = eη ≫ k ≫ inv e₀ ∧
      e ≫ pullback.fst b g' ≫ e₀ ≫ pullback.fst c g = eη ≫ pullback.fst c gg := by

  let k : pullback c gg ⟶ pullback c g :=
    pullback.lift (pullback.fst c gg) (pullback.snd c gg ≫ g')
      (by rw [Category.assoc, hgg]; exact pullback.condition)
  have hk₁ : k ≫ pullback.fst c g = pullback.fst c gg := pullback.lift_fst _ _ _
  have hk₂ : k ≫ pullback.snd c g = pullback.snd c gg ≫ g' := pullback.lift_snd _ _ _

  have big : IsPullback (k ≫ pullback.fst c g) (pullback.snd c gg) c (g' ≫ g) := by
    refine IsPullback.of_iso (IsPullback.of_hasPullback c gg) (Iso.refl _) (Iso.refl _) (Iso.refl _) (Iso.refl _)
      ?_ ?_ ?_ ?_
    · simp [hk₁]
    · simp
    · simp
    · simp [hgg]

  have left : IsPullback k (pullback.snd c gg) (pullback.snd c g) g' :=
    IsPullback.of_right big hk₂ (IsPullback.of_hasPullback c g)

  have hP : IsPullback (eη ≫ k ≫ inv e₀) b' b g' := by
    refine IsPullback.of_iso left (asIso eη).symm (asIso e₀).symm (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
    · simp
    · simp [← heη]
    · simp [← he₀]
    · simp
  refine ⟨hP.isoPullback.hom, k, inferInstance, hP.isoPullback_hom_snd, hk₁, hP.isoPullback_hom_fst, ?_⟩
  rw [← Category.assoc, hP.isoPullback_hom_fst]
  simp [hk₁]

end Lp
p2m_reactivate "P2MW.S_ModularCurve_forall_exists_schemeHomOver_baseChange_rat_isHom_pts_smul_of_dRModelPackage.ModularCurve P2MW.S_ModularCurve_forall_exists_schemeHomOver_baseChange_rat_isHom_pts_smul_of_dRModelPackage.ModularCurve.HeckeGenQStepB"

namespace Lp

theorem exists_iso_pullback_of_iso_pullback_comp {X S T U C C₀ : Scheme.{0}}
    (c : X ⟶ S) (gT : T ⟶ S) (g : U ⟶ T) (g' : U ⟶ S) (hg' : g' = g ≫ gT)
    (bη : C ⟶ U) (eη : C ⟶ pullback c g') [IsIso eη] (heη : eη ≫ pullback.snd c g' = bη)
    (b₀ : C₀ ⟶ T) (e₀ : C₀ ⟶ pullback c gT) [IsIso e₀] (he₀ : e₀ ≫ pullback.snd c gT = b₀) :
    ∃ (e : C ⟶ pullback b₀ g) (_ : IsIso e),
      e ≫ pullback.snd b₀ g = bη ∧ e ≫ pullback.fst b₀ g ≫ e₀ ≫ pullback.fst c gT = eη ≫ pullback.fst c g' := by
  obtain ⟨e, -, he, h1, -, -, h2⟩ :=
    exists_iso_pullback_of_pasting c gT g g' hg'.symm eη bη heη e₀ b₀ he₀
  exact ⟨e, he, h1, h2⟩

end Lp
p2m_reactivate "P2MW.S_ModularCurve_forall_exists_schemeHomOver_baseChange_rat_isHom_pts_smul_of_dRModelPackage.ModularCurve P2MW.S_ModularCurve_forall_exists_schemeHomOver_baseChange_rat_isHom_pts_smul_of_dRModelPackage.ModularCurve.HeckeGenQStepB"

namespace LpGlue

theorem ringHom_apply_eq_ratCast {S : Subring ℚ} {R : Type*} [DivisionRing R] [CharZero R]
    (f : ↥S →+* R) (q : ↥S) : f q = ((q : ℚ) : R) := by
  have hd : (((q : ℚ).den : ℕ) : R) ≠ 0 := Nat.cast_ne_zero.mpr (q : ℚ).den_ne_zero
  have hmul : f q * (((q : ℚ).den : ℕ) : R) = (((q : ℚ).num : ℤ) : R) := by
    rw [← map_natCast f, ← map_intCast f, ← map_mul]
    congr 1
    apply Subtype.ext
    push_cast
    exact Rat.mul_den_eq_num (q : ℚ)
  rw [Rat.cast_def, eq_div_iff hd, hmul]

theorem algebraMap_subring_eq_comp (S : Subring ℚ) (R : Type*) [DivisionRing R] [CharZero R]
    [Algebra ↥S R] [Algebra ℚ R] [Algebra ↥S ℚ] :
    algebraMap ↥S R = (algebraMap ℚ R).comp (algebraMap ↥S ℚ) :=
  RingHom.ext fun q => by
    rw [ringHom_apply_eq_ratCast, RingHom.comp_apply, ringHom_apply_eq_ratCast (algebraMap ↥S ℚ) q,
      Rat.cast_id, eq_ratCast]

theorem SpecMap_algebraMap_subring_eq_comp (S : Subring ℚ) (R : Type) [Field R] [CharZero R]
    [Algebra ↥S R] [Algebra ℚ R] [Algebra ↥S ℚ] :
    Spec.map (CommRingCat.ofHom (algebraMap ↥S R))
      = Spec.map (CommRingCat.ofHom (algebraMap ℚ R)) ≫ Spec.map (CommRingCat.ofHom (algebraMap ↥S ℚ)) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← algebraMap_subring_eq_comp S R]

end LpGlue
p2m_reactivate "P2MW.S_ModularCurve_forall_exists_schemeHomOver_baseChange_rat_isHom_pts_smul_of_dRModelPackage.ModularCurve P2MW.S_ModularCurve_forall_exists_schemeHomOver_baseChange_rat_isHom_pts_smul_of_dRModelPackage.ModularCurve.HeckeGenQStepB"

namespace ModularCurve p2m_export "ModularCurve" "DRModel DRModel.toBase DRModelPackage qExpand modularFunctionFieldFull full_degeneracy_le full_degeneracy_map_le IgusaScheme.jFull IgusaScheme baseChangeEquiv baseChangeEquiv_one_tmul coeffMap_id coeffMap_congr coeffEmb laurentBaseChange coeffEmb_mem_laurentBaseChange arithmeticGalois modularFunctionFieldBar JZero heckeOperatorBar heckeModuleBar heckeModuleBar_heckeGen_smul heckeModuleBar_C_smul heckeAlphaBar coe_heckeAlphaBar heckeBetaBar coe_heckeBetaBar HeckeAlphaBarIntegral HeckeBetaBarIntegral HeckeAlg heckeAlphaBarIntegral_of_prime heckeBetaBarIntegral_of_prime finiteAlong_heckeAlphaBar_of_prime finiteAlong_heckeBetaBar_of_prime transcendental_jq finiteDimensional_adjoin_jFull_modularFunctionFieldFull jqModC coeffMap_qExpand CharPModel.jBar pointEquivPlace_comp_eq_restrictAlong_of_baseChange exists_ofGenerator_baseChangeIso_chartPin_and_placeCompat transcendental_jqModC coeffEmb_jq isCurveOver_modularFunctionFieldBar essFiniteType_modularFunctionFieldBar heckeOperatorsCommuteBar heckeOperatorBar_points_eq_comp_of_transform_rat geometricallyIntegral_baseChangeToBase_twoChartIntegralModel_rat" end ModularCurve
p2m_open_scoped "ModularCurve" in

theorem ModularCurve.SpecMap_algebraMap_ratLocalizedAt_eq_comp (ℓ : ℕ) :
    Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) (AlgebraicClosure ℚ)))
      = Spec.map (CommRingCat.ofHom (algebraMap ℚ (AlgebraicClosure ℚ)))
        ≫ Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) ℚ)) :=
  LpGlue.SpecMap_algebraMap_subring_eq_comp (GaloisRep.ratLocalizedAt ℓ) (AlgebraicClosure ℚ)

p2m_open_scoped "ModularCurve" in
set_option maxHeartbeats 3200000 in

theorem ModularCurve.exists_baseChangeIso_rat_of_baseChangeIso_ratLocalizedAt
    (ℓ : ℕ) [Fact ℓ.Prime] (F₀ : IntermediateField ℚ (LaurentSeries ℚ))
    {X : Scheme.{0}} (c : X ⟶ Spec (CommRingCat.of ↥(GaloisRep.ratLocalizedAt ℓ)))
    (Mη : CurveModel (AlgebraicClosure ℚ) ↥(laurentBaseChange (AlgebraicClosure ℚ) F₀))
    (eη : Mη.C ⟶ pullback c (Spec.map (CommRingCat.ofHom
      (algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) (AlgebraicClosure ℚ))))) [IsIso eη]
    (heη : eη ≫ pullback.snd c _ = Mη.toBase)
    (M₀ : CurveModel ℚ ↥F₀)
    (e₀ : M₀.C ⟶ pullback c (Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) ℚ)))) [IsIso e₀]
    (he₀ : e₀ ≫ pullback.snd c _ = M₀.toBase)
    (hcompat : ∀ (x : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Mη.C // q ≫ Mη.toBase = 𝟙 _})
        (y : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶
          pullback c (Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) ℚ))))
        (x₀ : closedPoints M₀.C),
      y ≫ pullback.fst c _ = x.1 ≫ eη ≫ pullback.fst c _ →
      (y ≫ inv e₀).base (IsLocalRing.closedPoint (AlgebraicClosure ℚ)) = x₀.1 →
      ((Mη.pointEquivPlace x).toValuationSubring.toSubring.comap
          ((baseChangeEquiv (AlgebraicClosure ℚ) F₀).toAlgHom.toRingHom.comp
            (Algebra.TensorProduct.includeRight (R := ℚ) (A := AlgebraicClosure ℚ) (B := ↥F₀)).toRingHom) =
        (M₀.placeOfPoint x₀).toValuationSubring.toSubring)) :
    ∃ (eηℚ : Mη.C ⟶ pullback M₀.toBase (Spec.map (CommRingCat.ofHom (algebraMap ℚ (AlgebraicClosure ℚ)))))
      (_ : IsIso eηℚ),
      eηℚ ≫ pullback.snd _ _ = Mη.toBase ∧
      eηℚ ≫ pullback.fst _ _ ≫ e₀ ≫ pullback.fst c _ = eη ≫ pullback.fst c _ ∧
      ∀ (x : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Mη.C // q ≫ Mη.toBase = 𝟙 _})
        (x₀ : closedPoints M₀.C),
      (x.1 ≫ eηℚ ≫ pullback.fst _ _).base (IsLocalRing.closedPoint (AlgebraicClosure ℚ)) = x₀.1 →
      ((Mη.pointEquivPlace x).toValuationSubring.toSubring.comap
          ((baseChangeEquiv (AlgebraicClosure ℚ) F₀).toAlgHom.toRingHom.comp
            (Algebra.TensorProduct.includeRight (R := ℚ) (A := AlgebraicClosure ℚ) (B := ↥F₀)).toRingHom) =
        (M₀.placeOfPoint x₀).toValuationSubring.toSubring) := by
  obtain ⟨e, he, h1, h2⟩ := Lp.exists_iso_pullback_of_iso_pullback_comp c _ _ _
    (ModularCurve.SpecMap_algebraMap_ratLocalizedAt_eq_comp ℓ) Mη.toBase eη heη M₀.toBase e₀ he₀
  refine ⟨e, he, h1, h2, fun x x₀ hx => hcompat x (x.1 ≫ e ≫ pullback.fst _ _ ≫ e₀) x₀ ?_ ?_⟩
  ·
    simp only [Category.assoc]
    rw [h2]
  ·
    simp only [Category.assoc, IsIso.hom_inv_id, Category.comp_id]
    exact hx

namespace HGQSeams

section CurveChange

variable {R : Type u} [CommRing R] {C C' : Scheme.{u}}
  {c : C ⟶ Spec (CommRingCat.of R)} {c' : C' ⟶ Spec (CommRingCat.of R)}
  (π : C' ⟶ C) (hπ : π ≫ c = c')

theorem isFinite_curveChange [IsFinite π] {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) :
    IsFinite (curveChange π hπ t) :=
  MorphismProperty.pullback_map (P := @IsFinite) ‹IsFinite π› (inferInstance : IsFinite (𝟙 T)) hπ.symm
    (Category.id_comp t).symm

theorem flat_curveChange [Flat π] {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) :
    Flat (curveChange π hπ t) :=
  MorphismProperty.pullback_map (P := @Flat) ‹Flat π› (inferInstance : Flat (𝟙 T)) hπ.symm
    (Category.id_comp t).symm

theorem locallyOfFinitePresentation_curveChange [LocallyOfFinitePresentation π] {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R)) : LocallyOfFinitePresentation (curveChange π hπ t) :=
  MorphismProperty.pullback_map (P := @LocallyOfFinitePresentation) ‹LocallyOfFinitePresentation π›
    (inferInstance : LocallyOfFinitePresentation (𝟙 T)) hπ.symm (Category.id_comp t).symm

theorem finrank_curveChange [Flat π] [IsFinite π] {d : ℕ} (hd : ∀ y : C, π.finrank y = d)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) :
    ∀ y, (curveChange π hπ t).finrank y = d :=
  fun y => (Scheme.Hom.finrank_pullbackMap_of_comp_eq c c' t π hπ y).trans (hd _)

theorem isPullback_curveChange {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) :
    IsPullback (pullback.fst c' t) (curveChange π hπ t) π (pullback.fst c t) := by
  refine IsPullback.of_bot ?_ ?_ (IsPullback.of_hasPullback c t)
  · rw [curveChange_snd, hπ]
    exact IsPullback.of_hasPullback c' t
  · simp only [curveChange, pullback.lift_fst]

theorem isPullback_baseChangeSnd_curveChange {T T' : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}
    {t' : T' ⟶ Spec (CommRingCat.of R)} (ψ : SchemeHomOver t' t) :
    IsPullback (baseChangeSnd c' ψ) (curveChange π hπ t') (curveChange π hπ t) (baseChangeSnd c ψ) := by
  refine IsPullback.of_right ?_ (curveChange_baseChangeSnd π hπ ψ).symm (isPullback_curveChange π hπ t)
  have h1 : baseChangeSnd c' ψ ≫ pullback.fst c' t = pullback.fst c' t' := by
    simp only [baseChangeSnd, pullback.lift_fst, Category.comp_id]
  have h2 : baseChangeSnd c ψ ≫ pullback.fst c t = pullback.fst c t' := by
    simp only [baseChangeSnd, pullback.lift_fst, Category.comp_id]
  rw [h1, h2]
  exact isPullback_curveChange π hπ t'

end CurveChange
p2m_reactivate "P2MW.S_ModularCurve_forall_exists_schemeHomOver_baseChange_rat_isHom_pts_smul_of_dRModelPackage.ModularCurve P2MW.S_ModularCurve_forall_exists_schemeHomOver_baseChange_rat_isHom_pts_smul_of_dRModelPackage.ModularCurve.HeckeGenQStepB"

section Transform

variable {R : Type u} [CommRing R] {C C' : Scheme.{u}}
  {c : C ⟶ Spec (CommRingCat.of R)} {c' : C' ⟶ Spec (CommRingCat.of R)}
  {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c}
  (πα πβ : C' ⟶ C) (hα : πα ≫ c = c') (hβ : πβ ≫ c = c')
  [IsFinite πα] [Flat πα] [LocallyOfFinitePresentation πα]
  (d : ℕ) (hd : ∀ y : C, πα.finrank y = d)

include hd

theorem hinv {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (M : RigidifiedLineBundle c ε t) :
    Scheme.Modules.IsInvertible (Scheme.Modules.normModule (curveChange πα hα t) d
      ((Scheme.Modules.pullback (curveChange πβ hβ t)).obj M.L)) :=
  haveI := isFinite_curveChange πα hα t
  haveI := flat_curveChange πα hα t
  haveI := locallyOfFinitePresentation_curveChange πα hα t
  Scheme.Modules.IsInvertible.normModule _ d (finrank_curveChange πα hα hd t) (M.isInvertible.pullback _)

noncomputable def Phi {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (M : RigidifiedLineBundle c ε t) :
    RigidifiedLineBundle c ε t :=
  RigidifiedLineBundle.ofInvertible (ε := ε)
    (Scheme.Modules.normModule (curveChange πα hα t) d ((Scheme.Modules.pullback (curveChange πβ hβ t)).obj M.L))
    (hinv πα πβ hα hβ d hd t M)

theorem Phi_L {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (M : RigidifiedLineBundle c ε t) :
    (Phi πα πβ hα hβ d hd t M).L = (RigidifiedLineBundle.ofInvertible (ε := ε)
      (Scheme.Modules.normModule (curveChange πα hα t) d ((Scheme.Modules.pullback (curveChange πβ hβ t)).obj M.L))
      (hinv πα πβ hα hβ d hd t M)).L := rfl

theorem Phi_L_iso {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (M : RigidifiedLineBundle c ε t) :
    Nonempty ((Phi πα πβ hα hβ d hd t M).L ≅
      Scheme.Modules.rigidify (rigSection c t ε) (pullback.snd c t)
        (Scheme.Modules.normModule (curveChange πα hα t) d
          ((Scheme.Modules.pullback (curveChange πβ hβ t)).obj M.L))) :=
  ⟨Iso.refl _⟩

theorem hcongr {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (M M' : RigidifiedLineBundle c ε t)
    (h : Nonempty (M.L ≅ M'.L)) :
    Nonempty ((Phi πα πβ hα hβ d hd t M).L ≅ (Phi πα πβ hα hβ d hd t M').L) :=
  RigidifiedLineBundle.nonempty_ofInvertible_iso_of_iso _ _
    (Scheme.Modules.normModuleMapIso _ d ((Scheme.Modules.pullback _).mapIso h.some))

omit [IsFinite πα] [Flat πα] [LocallyOfFinitePresentation πα] hd in

theorem isAlgEquivZero_fibre_pullback {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}
    {M : RigidifiedLineBundle c ε t} (hM : FibrewiseAlgEquivZero M)
    (k : Type u) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ T) :
    IsAlgEquivZero (fibreAt c' t s)
      ((Scheme.Modules.pullback (pullback.fst (pullback.snd c' t) s)).obj
        ((Scheme.Modules.pullback (curveChange πβ hβ t)).obj M.L)) := by
  let e : Limits.pullback (pullback.snd c' t) s ⟶ Limits.pullback (pullback.snd c t) s :=
    pullback.map _ _ _ _ (curveChange πβ hβ t) (𝟙 _) (𝟙 T)
      (by rw [Category.comp_id, curveChange_snd]) (by simp)
  have he : e ≫ fibreAt c t s = fibreAt c' t s := by
    simp only [e, fibreAt, pullback.lift_snd, Category.comp_id]
  have hfst : e ≫ pullback.fst (pullback.snd c t) s =
      pullback.fst (pullback.snd c' t) s ≫ curveChange πβ hβ t := by
    simp only [e, pullback.lift_fst]
  refine IsAlgEquivZero.of_iso ?_ ((hM k s).pullback e he)
  exact (Scheme.Modules.pullbackComp _ _).app M.L ≪≫
    (Scheme.Modules.pullbackCongr hfst).app M.L ≪≫
    ((Scheme.Modules.pullbackComp _ _).app M.L).symm

theorem hcut {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (M : RigidifiedLineBundle c ε t)
    (hM : FibrewiseAlgEquivZero M) : FibrewiseAlgEquivZero (Phi πα πβ hα hβ d hd t M) :=
  FibrewiseAlgEquivZero.ofInvertible_normModule_curveChange (ε := ε) πα hα d hd
    ((Scheme.Modules.pullback (curveChange πβ hβ t)).obj M.L) (M.isInvertible.pullback _)
    (isAlgEquivZero_fibre_pullback πβ hβ hM) (hinv πα πβ hα hβ d hd t M)

theorem hunit {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) :
    Nonempty ((Phi (ε := ε) πα πβ hα hβ d hd t (RigidifiedLineBundle.unit t)).L ≅
      (RigidifiedLineBundle.unit (c := c) (ε := ε) t).L) := by
  haveI := isFinite_curveChange πα hα t
  haveI := flat_curveChange πα hα t
  haveI := locallyOfFinitePresentation_curveChange πα hα t

  obtain ⟨eN⟩ := Scheme.Modules.nonempty_normModule_unit_iso (curveChange πα hα t) d (finrank_curveChange πα hα hd t)
  let e0 : Scheme.Modules.normModule (curveChange πα hα t) d
      ((Scheme.Modules.pullback (curveChange πβ hβ t)).obj (RigidifiedLineBundle.unit (c := c) (ε := ε) t).L) ≅
      (RigidifiedLineBundle.unit (c := c) (ε := ε) t).L :=
    Scheme.Modules.normModuleMapIso _ d (Scheme.Modules.pullbackTensorUnitObjIso _) ≪≫ eN
  obtain ⟨e1⟩ := RigidifiedLineBundle.nonempty_ofInvertible_iso_of_iso (ε := ε)
    (hinv πα πβ hα hβ d hd t (RigidifiedLineBundle.unit t)) (RigidifiedLineBundle.unit (c := c) (ε := ε) t).isInvertible e0
  obtain ⟨e2⟩ := RigidifiedLineBundle.nonempty_ofInvertible_iso_of_rigidified (RigidifiedLineBundle.unit (c := c) (ε := ε) t)
  exact ⟨e1 ≪≫ e2⟩

theorem htensor {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (M M' : RigidifiedLineBundle c ε t) :
    Nonempty ((Phi πα πβ hα hβ d hd t (M.tensor M')).L ≅
      ((Phi πα πβ hα hβ d hd t M).tensor (Phi πα πβ hα hβ d hd t M')).L) := by
  haveI := isFinite_curveChange πα hα t
  haveI := flat_curveChange πα hα t
  haveI := locallyOfFinitePresentation_curveChange πα hα t
  have hA := M.isInvertible.pullback (curveChange πβ hβ t)
  have hB := M'.isInvertible.pullback (curveChange πβ hβ t)
  obtain ⟨eT⟩ := Scheme.Modules.nonempty_normModule_tensor_iso (curveChange πα hα t) d (finrank_curveChange πα hα hd t) _ _ hA hB

  let e0 := Scheme.Modules.normModuleMapIso (curveChange πα hα t) d
      (Scheme.Modules.pullbackTensorObjIso (curveChange πβ hβ t) M.L M'.L) ≪≫ eT
  obtain ⟨e1⟩ := RigidifiedLineBundle.nonempty_ofInvertible_iso_of_iso (ε := ε)
    (hinv πα πβ hα hβ d hd t (M.tensor M')) ((hinv πα πβ hα hβ d hd t M).tensor (hinv πα πβ hα hβ d hd t M')) e0
  obtain ⟨e2⟩ := RigidifiedLineBundle.nonempty_ofInvertible_tensor_iso (ε := ε)
    (hinv πα πβ hα hβ d hd t M) (hinv πα πβ hα hβ d hd t M')
  exact ⟨e1 ≪≫ e2⟩

theorem hnat {T T' : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} {t' : T' ⟶ Spec (CommRingCat.of R)}
    (ψ : SchemeHomOver t' t) (M : RigidifiedLineBundle c ε t) :
    Nonempty (((Phi πα πβ hα hβ d hd t M).pullbackAlong ψ).L ≅ (Phi πα πβ hα hβ d hd t' (M.pullbackAlong ψ)).L) := by
  haveI := isFinite_curveChange πα hα t
  haveI := flat_curveChange πα hα t
  haveI := locallyOfFinitePresentation_curveChange πα hα t
  have hA := M.isInvertible.pullback (curveChange πβ hβ t)

  obtain ⟨e1⟩ := RigidifiedLineBundle.nonempty_ofInvertible_pullbackAlong_iso (ε := ε) ψ (hinv πα πβ hα hβ d hd t M)

  obtain ⟨e2⟩ := Scheme.Modules.nonempty_pullback_normModule_iso (curveChange πα hα t) d
    (finrank_curveChange πα hα hd t) (baseChangeSnd c ψ) (curveChange πα hα t') (baseChangeSnd c' ψ)
    (isPullback_baseChangeSnd_curveChange πα hα ψ) hA

  let e3 : (Scheme.Modules.pullback (baseChangeSnd c' ψ)).obj ((Scheme.Modules.pullback (curveChange πβ hβ t)).obj M.L) ≅
      (Scheme.Modules.pullback (curveChange πβ hβ t')).obj ((Scheme.Modules.pullback (baseChangeSnd c ψ)).obj M.L) :=
    (Scheme.Modules.pullbackComp _ _).app M.L ≪≫
      (Scheme.Modules.pullbackCongr (curveChange_baseChangeSnd πβ hβ ψ).symm).app M.L ≪≫
      ((Scheme.Modules.pullbackComp _ _).app M.L).symm
  let e4 := e2 ≪≫ Scheme.Modules.normModuleMapIso (curveChange πα hα t') d e3
  obtain ⟨e5⟩ := RigidifiedLineBundle.nonempty_ofInvertible_iso_of_iso (ε := ε)
    ((hinv πα πβ hα hβ d hd t M).pullback (baseChangeSnd c ψ)) (hinv πα πβ hα hβ d hd t' (M.pullbackAlong ψ)) e4
  exact ⟨e1 ≪≫ e5⟩

end Transform
p2m_reactivate "P2MW.S_ModularCurve_forall_exists_schemeHomOver_baseChange_rat_isHom_pts_smul_of_dRModelPackage.ModularCurve P2MW.S_ModularCurve_forall_exists_schemeHomOver_baseChange_rat_isHom_pts_smul_of_dRModelPackage.ModularCurve.HeckeGenQStepB"

end HGQSeams
p2m_reactivate "P2MW.S_ModularCurve_forall_exists_schemeHomOver_baseChange_rat_isHom_pts_smul_of_dRModelPackage.ModularCurve P2MW.S_ModularCurve_forall_exists_schemeHomOver_baseChange_rat_isHom_pts_smul_of_dRModelPackage.ModularCurve.HeckeGenQStepB"

section MergeThreeA
open scoped TensorProduct
open ModularCurve.CharPModel ModularCurve.IgusaScheme

noncomputable section

namespace ModularCurve
p2m_export "ModularCurve" "DRModel DRModel.toBase DRModelPackage qExpand modularFunctionFieldFull full_degeneracy_le full_degeneracy_map_le IgusaScheme.jFull IgusaScheme baseChangeEquiv baseChangeEquiv_one_tmul coeffMap_id coeffMap_congr coeffEmb laurentBaseChange coeffEmb_mem_laurentBaseChange arithmeticGalois modularFunctionFieldBar JZero heckeOperatorBar heckeModuleBar heckeModuleBar_heckeGen_smul heckeModuleBar_C_smul heckeAlphaBar coe_heckeAlphaBar heckeBetaBar coe_heckeBetaBar HeckeAlphaBarIntegral HeckeBetaBarIntegral HeckeAlg heckeAlphaBarIntegral_of_prime heckeBetaBarIntegral_of_prime finiteAlong_heckeAlphaBar_of_prime finiteAlong_heckeBetaBar_of_prime transcendental_jq finiteDimensional_adjoin_jFull_modularFunctionFieldFull jqModC coeffMap_qExpand CharPModel.jBar pointEquivPlace_comp_eq_restrictAlong_of_baseChange exists_ofGenerator_baseChangeIso_chartPin_and_placeCompat transcendental_jqModC coeffEmb_jq isCurveOver_modularFunctionFieldBar essFiniteType_modularFunctionFieldBar heckeOperatorsCommuteBar heckeOperatorBar_points_eq_comp_of_transform_rat geometricallyIntegral_baseChangeToBase_twoChartIntegralModel_rat"
namespace HeckeGenQStepE
p2m_open "ModularCurve~jBar"

theorem exists_algEquiv_tensor_of_pins
    {R T F Fbar : Type*} [CommRing R] [Field T] [CommRing F] [CommRing Fbar]
    [Algebra R ℚ] [Algebra R T] [Algebra ℚ T] [IsScalarTower R ℚ T]
    [Algebra ℚ F] [Algebra R F] [IsScalarTower R ℚ F] [Algebra T Fbar]
    (A : Subalgebra R F) (B : Subalgebra ℚ F) (Bbar : Subalgebra T Fbar)
    (ι : F →+* Fbar) (hι : ∀ (q : ℚ) (x : F), ι (q • x) = algebraMap ℚ T q • ι x)
    (e₁ : ℚ ⊗[R] ↥A ≃ₐ[ℚ] ↥B) (h₁ : ∀ (q : ℚ) (a : ↥A), ((e₁ (q ⊗ₜ a) : ↥B) : F) = q • (a : F))
    (e₂ : T ⊗[R] ↥A ≃ₐ[T] ↥Bbar) (h₂ : ∀ a : ↥A, ((e₂ (1 ⊗ₜ a) : ↥Bbar) : Fbar) = ι (a : F)) :
    ∃ c : T ⊗[ℚ] ↥B ≃ₐ[T] ↥Bbar, ∀ b : ↥B, ((c (1 ⊗ₜ b) : ↥Bbar) : Fbar) = ι (b : F) := by
  let c : T ⊗[ℚ] ↥B ≃ₐ[T] ↥Bbar :=
    ((Algebra.TensorProduct.congr (AlgEquiv.refl : T ≃ₐ[T] T) e₁.symm).trans
      (Algebra.TensorProduct.cancelBaseChange R ℚ T T ↥A)).trans e₂
  refine ⟨c, fun b => ?_⟩

  have key : ∀ τ : ℚ ⊗[R] ↥A,
      ((e₂ (Algebra.TensorProduct.cancelBaseChange R ℚ T T ↥A ((1 : T) ⊗ₜ τ)) : ↥Bbar) : Fbar) =
        ι ((e₁ τ : ↥B) : F) := by
    intro τ
    induction τ using TensorProduct.induction_on with
    | zero => simp
    | tmul q a =>
        rw [Algebra.TensorProduct.cancelBaseChange_tmul, h₁, hι]
        have : (q • (1 : T)) ⊗ₜ[R] a = (algebraMap ℚ T q) • ((1 : T) ⊗ₜ[R] a) := by
          rw [TensorProduct.smul_tmul', Algebra.smul_def, mul_one, smul_eq_mul, mul_one]
        rw [this, map_smul, Subalgebra.coe_smul, h₂]
    | add x y hx hy =>
        rw [TensorProduct.tmul_add, map_add, map_add, Subalgebra.coe_add, hx, hy, map_add,
          Subalgebra.coe_add, map_add]
  have hc : c (1 ⊗ₜ b) = e₂ (Algebra.TensorProduct.cancelBaseChange R ℚ T T ↥A ((1 : T) ⊗ₜ e₁.symm b)) := by
    simp only [c, AlgEquiv.trans_apply, Algebra.TensorProduct.congr_apply, AlgEquiv.refl_toAlgHom,
      Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
    try rfl
  rw [hc, key, AlgEquiv.apply_symm_apply]

noncomputable def toBar (N : ℕ) [NeZero N] : ↥(modularFunctionFieldFull N) →+* modularFunctionFieldBar N :=
  (baseChangeEquiv (AlgebraicClosure ℚ) (modularFunctionFieldFull N)).toAlgHom.toRingHom.comp
    (Algebra.TensorProduct.includeRight (R := ℚ) (A := AlgebraicClosure ℚ)
      (B := ↥(modularFunctionFieldFull N))).toRingHom

set_option synthInstance.maxHeartbeats 1600000 in
theorem toBar_apply (N : ℕ) [NeZero N] (b : ↥(modularFunctionFieldFull N)) :
    toBar N b = ⟨coeffEmb (AlgebraicClosure ℚ) (b : LaurentSeries ℚ),
      coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) b.2⟩ := by
  show baseChangeEquiv (AlgebraicClosure ℚ) (modularFunctionFieldFull N) (1 ⊗ₜ b) = _
  exact baseChangeEquiv_one_tmul (AlgebraicClosure ℚ) (modularFunctionFieldFull N) b

set_option synthInstance.maxHeartbeats 1600000 in
theorem toBar_smul (N : ℕ) [NeZero N] (q : ℚ) (x : ↥(modularFunctionFieldFull N)) :
    toBar N (q • x) = algebraMap ℚ (AlgebraicClosure ℚ) q • toBar N x := by
  show baseChangeEquiv (AlgebraicClosure ℚ) (modularFunctionFieldFull N) (1 ⊗ₜ (q • x)) =
    algebraMap ℚ (AlgebraicClosure ℚ) q • baseChangeEquiv (AlgebraicClosure ℚ) (modularFunctionFieldFull N) (1 ⊗ₜ x)
  rw [← map_smul, TensorProduct.smul_tmul', ← TensorProduct.smul_tmul, Algebra.smul_def, mul_one,
    smul_eq_mul, mul_one]

set_option synthInstance.maxHeartbeats 1600000 in

theorem exists_chartIso (N : ℕ) [NeZero N] (ℓ : ℕ) [Fact ℓ.Prime] :
    (∃ cFin : (AlgebraicClosure ℚ) ⊗[ℚ] ↥(CurveModel.chartRing ℚ ({jFull N} : Set ↥(modularFunctionFieldFull N))) ≃ₐ[AlgebraicClosure ℚ]
        ↥(CurveModel.chartRing (AlgebraicClosure ℚ) ({CharPModel.jBar N} : Set (modularFunctionFieldBar N))),
      ∀ b : CurveModel.chartRing ℚ ({jFull N} : Set ↥(modularFunctionFieldFull N)),
        ((cFin (1 ⊗ₜ b) : ↥(CurveModel.chartRing (AlgebraicClosure ℚ) ({CharPModel.jBar N} : Set (modularFunctionFieldBar N)))) : (modularFunctionFieldBar N)) =
          (⟨coeffEmb (AlgebraicClosure ℚ) ((b : ↥(modularFunctionFieldFull N)) : LaurentSeries ℚ),
            coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (b : ↥(modularFunctionFieldFull N)).2⟩ : (modularFunctionFieldBar N))) ∧
    (∃ cInf : (AlgebraicClosure ℚ) ⊗[ℚ] ↥(CurveModel.chartRing ℚ ({(jFull N)⁻¹} : Set ↥(modularFunctionFieldFull N))) ≃ₐ[AlgebraicClosure ℚ]
        ↥(CurveModel.chartRing (AlgebraicClosure ℚ) ({(CharPModel.jBar N)⁻¹} : Set (modularFunctionFieldBar N))),
      ∀ b : CurveModel.chartRing ℚ ({(jFull N)⁻¹} : Set ↥(modularFunctionFieldFull N)),
        ((cInf (1 ⊗ₜ b) : ↥(CurveModel.chartRing (AlgebraicClosure ℚ) ({(CharPModel.jBar N)⁻¹} : Set (modularFunctionFieldBar N)))) : (modularFunctionFieldBar N)) =
          (⟨coeffEmb (AlgebraicClosure ℚ) ((b : ↥(modularFunctionFieldFull N)) : LaurentSeries ℚ),
            coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (b : ↥(modularFunctionFieldFull N)).2⟩ : (modularFunctionFieldBar N))) := by
  obtain ⟨⟨eFin, hFin⟩, ⟨eInf, hInf⟩⟩ := exists_algEquiv_tensor_chartAlg_chartRing N ℓ
  obtain ⟨e₁, h₁⟩ := exists_algEquiv_rat_tensor_chartAlg_chartRing N ℓ ({jFull N} : Set ↥(modularFunctionFieldFull N))
  obtain ⟨e₁', h₁'⟩ := exists_algEquiv_rat_tensor_chartAlg_chartRing N ℓ ({(jFull N)⁻¹} : Set ↥(modularFunctionFieldFull N))
  constructor
  · obtain ⟨c, hc⟩ := exists_algEquiv_tensor_of_pins (R := ↥(GaloisRep.ratLocalizedAt ℓ)) (T := AlgebraicClosure ℚ)
      (chartAlgFin N ℓ) (CurveModel.chartRing ℚ ({jFull N} : Set ↥(modularFunctionFieldFull N)))
      (CurveModel.chartRing (AlgebraicClosure ℚ) ({CharPModel.jBar N} : Set (modularFunctionFieldBar N)))
      (toBar N) (toBar_smul N) e₁ h₁ eFin (fun a => by rw [hFin, toBar_apply])
    exact ⟨c, fun b => by rw [hc, toBar_apply]⟩
  · obtain ⟨c, hc⟩ := exists_algEquiv_tensor_of_pins (R := ↥(GaloisRep.ratLocalizedAt ℓ)) (T := AlgebraicClosure ℚ)
      (chartAlgInf N ℓ) (CurveModel.chartRing ℚ ({(jFull N)⁻¹} : Set ↥(modularFunctionFieldFull N)))
      (CurveModel.chartRing (AlgebraicClosure ℚ) ({(CharPModel.jBar N)⁻¹} : Set (modularFunctionFieldBar N)))
      (toBar N) (toBar_smul N) e₁' h₁' eInf (fun a => by rw [hInf, toBar_apply])
    exact ⟨c, fun b => by rw [hc, toBar_apply]⟩

end ModularCurve.HeckeGenQStepE
p2m_reactivate "P2MW.S_ModularCurve_forall_exists_schemeHomOver_baseChange_rat_isHom_pts_smul_of_dRModelPackage.ModularCurve P2MW.S_ModularCurve_forall_exists_schemeHomOver_baseChange_rat_isHom_pts_smul_of_dRModelPackage.ModularCurve.HeckeGenQStepB"
p2m_reactivate "P2MW.S_ModularCurve_forall_exists_schemeHomOver_baseChange_rat_isHom_pts_smul_of_dRModelPackage.ModularCurve P2MW.S_ModularCurve_forall_exists_schemeHomOver_baseChange_rat_isHom_pts_smul_of_dRModelPackage.ModularCurve.HeckeGenQStepB"

end
p2m_reactivate "P2MW.S_ModularCurve_forall_exists_schemeHomOver_baseChange_rat_isHom_pts_smul_of_dRModelPackage.ModularCurve P2MW.S_ModularCurve_forall_exists_schemeHomOver_baseChange_rat_isHom_pts_smul_of_dRModelPackage.ModularCurve.HeckeGenQStepB"

end MergeThreeA
p2m_reactivate "P2MW.S_ModularCurve_forall_exists_schemeHomOver_baseChange_rat_isHom_pts_smul_of_dRModelPackage.ModularCurve P2MW.S_ModularCurve_forall_exists_schemeHomOver_baseChange_rat_isHom_pts_smul_of_dRModelPackage.ModularCurve.HeckeGenQStepB"

p2m_open_scoped "ModularCurve" in
open ModularCurve.CharPModel in
set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in

/-!
                                                                             -/

theorem ModularCurve.SpecMap_algebraMap_int_eq_comp :
    Spec.map (CommRingCat.ofHom (algebraMap ℤ (AlgebraicClosure ℚ)))
      = Spec.map (CommRingCat.ofHom (algebraMap ℚ (AlgebraicClosure ℚ)))
        ≫ Spec.map (CommRingCat.ofHom (algebraMap ℤ ℚ)) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq ℤ ℚ (AlgebraicClosure ℚ)]

p2m_open_scoped "ModularCurve" in
set_option maxHeartbeats 3200000 in

theorem ModularCurve.exists_baseChangeIso_rat_of_baseChangeIso_int
    (F₀ : IntermediateField ℚ (LaurentSeries ℚ))
    {X : Scheme.{0}} (c : X ⟶ Spec (CommRingCat.of ℤ))
    (Mη : CurveModel (AlgebraicClosure ℚ) ↥(laurentBaseChange (AlgebraicClosure ℚ) F₀))
    (eη : Mη.C ⟶ pullback c (Spec.map (CommRingCat.ofHom (algebraMap ℤ (AlgebraicClosure ℚ))))) [IsIso eη]
    (heη : eη ≫ pullback.snd c _ = Mη.toBase)
    (M₀ : CurveModel ℚ ↥F₀)
    (e₀ : M₀.C ⟶ pullback c (Spec.map (CommRingCat.ofHom (algebraMap ℤ ℚ)))) [IsIso e₀]
    (he₀ : e₀ ≫ pullback.snd c _ = M₀.toBase)
    (hcompat : ∀ (x : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Mη.C // q ≫ Mη.toBase = 𝟙 _})
        (y : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶
          pullback c (Spec.map (CommRingCat.ofHom (algebraMap ℤ ℚ))))
        (x₀ : closedPoints M₀.C),
      y ≫ pullback.fst c _ = x.1 ≫ eη ≫ pullback.fst c _ →
      (y ≫ inv e₀).base (IsLocalRing.closedPoint (AlgebraicClosure ℚ)) = x₀.1 →
      ((Mη.pointEquivPlace x).toValuationSubring.toSubring.comap
          ((baseChangeEquiv (AlgebraicClosure ℚ) F₀).toAlgHom.toRingHom.comp
            (Algebra.TensorProduct.includeRight (R := ℚ) (A := AlgebraicClosure ℚ) (B := ↥F₀)).toRingHom) =
        (M₀.placeOfPoint x₀).toValuationSubring.toSubring)) :
    ∃ (eηℚ : Mη.C ⟶ pullback M₀.toBase (Spec.map (CommRingCat.ofHom (algebraMap ℚ (AlgebraicClosure ℚ)))))
      (_ : IsIso eηℚ),
      eηℚ ≫ pullback.snd _ _ = Mη.toBase ∧
      eηℚ ≫ pullback.fst _ _ ≫ e₀ ≫ pullback.fst c _ = eη ≫ pullback.fst c _ ∧
      ∀ (x : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Mη.C // q ≫ Mη.toBase = 𝟙 _})
        (x₀ : closedPoints M₀.C),
      (x.1 ≫ eηℚ ≫ pullback.fst _ _).base (IsLocalRing.closedPoint (AlgebraicClosure ℚ)) = x₀.1 →
      ((Mη.pointEquivPlace x).toValuationSubring.toSubring.comap
          ((baseChangeEquiv (AlgebraicClosure ℚ) F₀).toAlgHom.toRingHom.comp
            (Algebra.TensorProduct.includeRight (R := ℚ) (A := AlgebraicClosure ℚ) (B := ↥F₀)).toRingHom) =
        (M₀.placeOfPoint x₀).toValuationSubring.toSubring) := by
  obtain ⟨e, he, h1, h2⟩ := Lp.exists_iso_pullback_of_iso_pullback_comp c _ _ _
    ModularCurve.SpecMap_algebraMap_int_eq_comp Mη.toBase eη heη M₀.toBase e₀ he₀
  refine ⟨e, he, h1, h2, fun x x₀ hx => hcompat x (x.1 ≫ e ≫ pullback.fst _ _ ≫ e₀) x₀ ?_ ?_⟩
  · simp only [Category.assoc]
    rw [h2]
  · simp only [Category.assoc, IsIso.hom_inv_id, Category.comp_id]
    exact hx

namespace S6C1

variable {R : Type u} [CommRing R] {A : Scheme.{u}} {g : A ⟶ Spec (CommRingCat.of R)}

def IsHom (L : RelativeGroupLaw R g) (φ : SchemeHomOver g g) : Prop :=
  ∀ {T : Scheme.{u}} (s : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver s g),
    NeronModelInfra.schemeHomOverComp (L.mul s x y) φ =
      L.mul s (NeronModelInfra.schemeHomOverComp x φ) (NeronModelInfra.schemeHomOverComp y φ)

def idEnd (g : A ⟶ Spec (CommRingCat.of R)) : SchemeHomOver g g := ⟨𝟙 A, Category.id_comp g⟩

@[scoped simp] theorem comp_idEnd {T : Scheme.{u}} {s : T ⟶ Spec (CommRingCat.of R)} (x : SchemeHomOver s g) :
    NeronModelInfra.schemeHomOverComp x (idEnd g) = x :=
  Subtype.ext (Category.comp_id _)

theorem comp_comp {T : Scheme.{u}} {s : T ⟶ Spec (CommRingCat.of R)} (x : SchemeHomOver s g)
    (φ ψ : SchemeHomOver g g) :
    NeronModelInfra.schemeHomOverComp x (NeronModelInfra.schemeHomOverComp φ ψ) =
      NeronModelInfra.schemeHomOverComp (NeronModelInfra.schemeHomOverComp x φ) ψ :=
  Subtype.ext (Category.assoc _ _ _).symm

theorem comp_mul (L : RelativeGroupLaw R g) {T : Scheme.{u}} {s : T ⟶ Spec (CommRingCat.of R)}
    (x : SchemeHomOver s g) (φ ψ : SchemeHomOver g g) :
    NeronModelInfra.schemeHomOverComp x (L.mul g φ ψ) =
      L.mul s (NeronModelInfra.schemeHomOverComp x φ) (NeronModelInfra.schemeHomOverComp x ψ) :=
  L.mul_natural g s x.1 x.2 φ ψ

theorem mul_mul_mul_comm' (L : RelativeGroupLaw R g) (hc : L.IsCommutative) {T : Scheme.{u}}
    (s : T ⟶ Spec (CommRingCat.of R)) (a b c d : SchemeHomOver s g) :
    L.mul s (L.mul s a b) (L.mul s c d) = L.mul s (L.mul s a c) (L.mul s b d) := by
  letI : CommGroup (SchemeHomOver s g) := { L.pointGroup s with mul_comm := hc s }
  exact mul_mul_mul_comm a b c d

theorem inv_mul' (L : RelativeGroupLaw R g) (hc : L.IsCommutative) {T : Scheme.{u}}
    (s : T ⟶ Spec (CommRingCat.of R)) (a b : SchemeHomOver s g) :
    L.inv s (L.mul s a b) = L.mul s (L.inv s a) (L.inv s b) := by
  letI : CommGroup (SchemeHomOver s g) := { L.pointGroup s with mul_comm := hc s }
  exact mul_inv a b

theorem isHom_idEnd (L : RelativeGroupLaw R g) : IsHom L (idEnd g) := by
  intro T s x y
  simp only [comp_idEnd]

theorem isHom_comp (L : RelativeGroupLaw R g) {φ ψ : SchemeHomOver g g} (hφ : IsHom L φ) (hψ : IsHom L ψ) :
    IsHom L (NeronModelInfra.schemeHomOverComp φ ψ) := by
  intro T s x y
  rw [comp_comp, hφ, hψ, comp_comp, comp_comp]

theorem isHom_mul (L : RelativeGroupLaw R g) (hc : L.IsCommutative) {φ ψ : SchemeHomOver g g}
    (hφ : IsHom L φ) (hψ : IsHom L ψ) : IsHom L (L.mul g φ ψ) := by
  intro T s x y
  rw [comp_mul, hφ, hψ, comp_mul, comp_mul]
  exact mul_mul_mul_comm' L hc s _ _ _ _

theorem isHom_inv (L : RelativeGroupLaw R g) (hc : L.IsCommutative) {φ : SchemeHomOver g g}
    (hφ : IsHom L φ) : IsHom L (L.inv g φ) := by
  intro T s x y
  letI := fun {T : Scheme.{u}} (s : T ⟶ Spec (CommRingCat.of R)) => L.pointGroup s

  have hev : ∀ {T : Scheme.{u}} {s : T ⟶ Spec (CommRingCat.of R)} (z : SchemeHomOver s g),
      NeronModelInfra.schemeHomOverComp z (L.inv g φ) = L.inv s (NeronModelInfra.schemeHomOverComp z φ) := by
    intro T s z
    letI := L.pointGroup s
    letI := L.pointGroup g
    have h1 : NeronModelInfra.schemeHomOverComp z (L.mul g (L.inv g φ) φ) =
        L.mul s (NeronModelInfra.schemeHomOverComp z (L.inv g φ)) (NeronModelInfra.schemeHomOverComp z φ) :=
      comp_mul L z _ _
    rw [L.inv_mul_cancel] at h1

    have h2 : NeronModelInfra.schemeHomOverComp z (L.one g) = L.one s := by
      have h3 := comp_mul L z (L.one g) (L.one g)
      rw [L.one_mul] at h3

      have : (NeronModelInfra.schemeHomOverComp z (L.one g) : SchemeHomOver s g) =
          (NeronModelInfra.schemeHomOverComp z (L.one g)) * (NeronModelInfra.schemeHomOverComp z (L.one g)) := h3
      exact left_eq_mul.mp this |>.symm ▸ rfl
    rw [h2] at h1

    exact eq_inv_of_mul_eq_one_left h1.symm
  rw [hev, hev, hev, hφ]
  exact inv_mul' L hc s _ _

noncomputable def evalHom (L : RelativeGroupLaw R g) {T : Scheme.{u}} {s : T ⟶ Spec (CommRingCat.of R)}
    (x : SchemeHomOver s g) :
    letI := L.pointGroup g; letI := L.pointGroup s
    SchemeHomOver g g →* SchemeHomOver s g :=
  letI := L.pointGroup g; letI := L.pointGroup s
  MonoidHom.mk' (fun φ => NeronModelInfra.schemeHomOverComp x φ) (fun φ ψ => comp_mul L x φ ψ)

theorem evalHom_apply (L : RelativeGroupLaw R g) {T : Scheme.{u}} {s : T ⟶ Spec (CommRingCat.of R)}
    (x : SchemeHomOver s g) (φ : SchemeHomOver g g) :
    (letI := L.pointGroup g; letI := L.pointGroup s; evalHom L x φ) = NeronModelInfra.schemeHomOverComp x φ := rfl

theorem comp_idEnd_zpow (L : RelativeGroupLaw R g) {T : Scheme.{u}} {s : T ⟶ Spec (CommRingCat.of R)}
    (x : SchemeHomOver s g) (n : ℤ) :
    NeronModelInfra.schemeHomOverComp x (letI := L.pointGroup g; idEnd g ^ n) = (letI := L.pointGroup s; x ^ n) := by
  letI := L.pointGroup g; letI := L.pointGroup s
  have h := map_zpow (evalHom L x) (idEnd g) n
  rw [evalHom_apply, evalHom_apply, comp_idEnd] at h
  exact h

theorem isHom_idEnd_zpow (L : RelativeGroupLaw R g) (hc : L.IsCommutative) (n : ℤ) :
    IsHom L (letI := L.pointGroup g; idEnd g ^ n) := by
  intro T s x y
  rw [comp_idEnd_zpow, comp_idEnd_zpow, comp_idEnd_zpow]
  letI : CommGroup (SchemeHomOver s g) := { L.pointGroup s with mul_comm := hc s }
  exact mul_zpow x y n

theorem zpow_val_eq (L : RelativeGroupLaw R g) {T : Scheme.{u}} {t₁ t₂ : T ⟶ Spec (CommRingCat.of R)}
    (h : t₁ = t₂) (x : SchemeHomOver t₁ g) (y : SchemeHomOver t₂ g) (hxy : x.1 = y.1) (n : ℤ) :
    (letI := L.pointGroup t₁; x ^ n).1 = (letI := L.pointGroup t₂; y ^ n).1 := by
  subst h
  obtain rfl : x = y := Subtype.ext hxy
  rfl

theorem mul_val_eq (L : RelativeGroupLaw R g) {T : Scheme.{u}} {t₁ t₂ : T ⟶ Spec (CommRingCat.of R)}
    (h : t₁ = t₂) (x x' : SchemeHomOver t₁ g) (y y' : SchemeHomOver t₂ g) (hxy : x.1 = y.1) (hxy' : x'.1 = y'.1) :
    (L.mul t₁ x x').1 = (L.mul t₂ y y').1 := by
  subst h
  obtain rfl : x = y := Subtype.ext hxy
  obtain rfl : x' = y' := Subtype.ext hxy'
  rfl

section BC
variable {R' : Type u} [CommRing R'] (ι : Spec (CommRingCat.of R') ⟶ Spec (CommRingCat.of R))

noncomputable def toBaseHom (L : RelativeGroupLaw R g) {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of R')) :
    letI := (L.baseChange ι).pointGroup t'; letI := L.pointGroup (t' ≫ ι)
    SchemeHomOver t' (RelativeGroupLaw.baseChangeStr ι g) →* SchemeHomOver (t' ≫ ι) g :=
  letI := (L.baseChange ι).pointGroup t'; letI := L.pointGroup (t' ≫ ι)
  MonoidHom.mk' (RelativeGroupLaw.baseChangePointToBase ι) (RelativeGroupLaw.baseChangePointToBase_mul ι L t')

theorem toBase_zpow_val (L : RelativeGroupLaw R g) {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of R'))
    (x : SchemeHomOver t' (RelativeGroupLaw.baseChangeStr ι g)) (n : ℤ) :
    (letI := (L.baseChange ι).pointGroup t'; x ^ n).1 ≫ pullback.fst g ι =
      (letI := L.pointGroup (t' ≫ ι); (RelativeGroupLaw.baseChangePointToBase ι x) ^ n).1 := by
  letI := (L.baseChange ι).pointGroup t'; letI := L.pointGroup (t' ≫ ι)
  have h := map_zpow (toBaseHom ι L t') x n
  have h' := congrArg Subtype.val h
  exact h'

theorem toBase_mul_val (L : RelativeGroupLaw R g) {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of R'))
    (x y : SchemeHomOver t' (RelativeGroupLaw.baseChangeStr ι g)) :
    ((L.baseChange ι).mul t' x y).1 ≫ pullback.fst g ι =
      (L.mul (t' ≫ ι) (RelativeGroupLaw.baseChangePointToBase ι x) (RelativeGroupLaw.baseChangePointToBase ι y)).1 :=
  congrArg Subtype.val (RelativeGroupLaw.baseChangePointToBase_mul ι L t' x y)

theorem isCommutative_baseChange (L : RelativeGroupLaw R g) (hc : L.IsCommutative) :
    (L.baseChange ι).IsCommutative := by
  intro T t' x y
  rw [RelativeGroupLaw.baseChange_mul, RelativeGroupLaw.baseChange_mul, hc]

end BC
p2m_reactivate "P2MW.S_ModularCurve_forall_exists_schemeHomOver_baseChange_rat_isHom_pts_smul_of_dRModelPackage.ModularCurve P2MW.S_ModularCurve_forall_exists_schemeHomOver_baseChange_rat_isHom_pts_smul_of_dRModelPackage.ModularCurve.HeckeGenQStepB"

theorem specRat_hom_ext {K : Type} [CommRing K] (f₁ f₂ : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of ℚ)) :
    f₁ = f₂ := by
  obtain ⟨a, rfl⟩ := Spec.map_surjective f₁
  obtain ⟨b, rfl⟩ := Spec.map_surjective f₂
  congr 1
  ext1
  exact Subsingleton.elim _ _

noncomputable def awayToRat (p : ℕ) (hp : p ≠ 0) : Localization.Away (p : ℤ) →+* ℚ :=
  IsLocalization.Away.lift (p : ℤ) (g := algebraMap ℤ ℚ)
    (by simpa using (show ((p : ℤ) : ℚ) ≠ 0 by exact_mod_cast hp))

theorem specMap_rat_eq (p : ℕ) (hp : p ≠ 0) :
    Spec.map (CommRingCat.ofHom (algebraMap ℤ ℚ)) =
      Spec.map (CommRingCat.ofHom (awayToRat p hp)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap ℤ (Localization.Away (p : ℤ)))) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  exact RingHom.ext_int _ _

theorem isProper_snd_rat {Dsch : Scheme.{0}} (Db : Dsch ⟶ Spec (CommRingCat.of ℤ)) (p : ℕ) (hp : p ≠ 0)
    (hpa : IsProper (pullback.snd Db (Spec.map (CommRingCat.ofHom (algebraMap ℤ (Localization.Away (p : ℤ))))))) :
    IsProper (pullback.snd Db (Spec.map (CommRingCat.ofHom (algebraMap ℤ ℚ)))) := by
  set ιA := Spec.map (CommRingCat.ofHom (algebraMap ℤ (Localization.Away (p : ℤ))))
  set ιQ := Spec.map (CommRingCat.ofHom (algebraMap ℤ ℚ))
  set f := Spec.map (CommRingCat.ofHom (awayToRat p hp))
  have hf : ιQ = f ≫ ιA := specMap_rat_eq p hp
  let k : pullback Db ιQ ⟶ pullback Db ιA :=
    pullback.lift (pullback.fst Db ιQ) (pullback.snd Db ιQ ≫ f) (by rw [pullback.condition, Category.assoc, ← hf])
  have hk₁ : k ≫ pullback.fst Db ιA = pullback.fst Db ιQ := pullback.lift_fst _ _ _
  have hk₂ : k ≫ pullback.snd Db ιA = pullback.snd Db ιQ ≫ f := pullback.lift_snd _ _ _
  have outer : IsPullback (k ≫ pullback.fst Db ιA) (pullback.snd Db ιQ) Db (f ≫ ιA) := by
    have h0 := IsPullback.of_hasPullback Db ιQ
    rw [← hk₁] at h0
    convert h0 using 2
    exact hf.symm
  have sq : IsPullback k (pullback.snd Db ιQ) (pullback.snd Db ιA) f :=
    IsPullback.of_right outer hk₂ (IsPullback.of_hasPullback Db ιA)
  rw [← sq.isoPullback_hom_snd]
  infer_instance

section Pts

variable {Dsch : Scheme.{0}} (Db : Dsch ⟶ Spec (CommRingCat.of ℤ))

theorem tQ_ιQ : Spec.map (CommRingCat.ofHom (algebraMap ℚ (AlgebraicClosure ℚ))) ≫
    Spec.map (CommRingCat.ofHom (algebraMap ℤ ℚ)) = Spec.map (CommRingCat.ofHom (algebraMap ℤ (AlgebraicClosure ℚ))) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq ℤ ℚ (AlgebraicClosure ℚ)]

noncomputable def liftQ (z : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap ℤ (AlgebraicClosure ℚ)))) Db) :
    SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap ℚ (AlgebraicClosure ℚ))))
      (pullback.snd Db (Spec.map (CommRingCat.ofHom (algebraMap ℤ ℚ)))) :=
  ⟨pullback.lift z.1 (Spec.map (CommRingCat.ofHom (algebraMap ℚ (AlgebraicClosure ℚ)))) (by rw [z.2, tQ_ιQ]),
    pullback.lift_snd _ _ _⟩

@[scoped simp] theorem liftQ_fst (z : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap ℤ (AlgebraicClosure ℚ)))) Db) :
    (liftQ Db z).1 ≫ pullback.fst Db _ = z.1 :=
  pullback.lift_fst _ _ _

noncomputable def pushZ (w : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap ℚ (AlgebraicClosure ℚ))))
      (pullback.snd Db (Spec.map (CommRingCat.ofHom (algebraMap ℤ ℚ))))) :
    SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap ℤ (AlgebraicClosure ℚ)))) Db :=
  ⟨w.1 ≫ pullback.fst Db _, by rw [Category.assoc, pullback.condition, ← Category.assoc, w.2, tQ_ιQ]⟩

theorem liftQ_pushZ (w) : liftQ Db (pushZ Db w) = w := by
  apply Subtype.ext
  apply pullback.hom_ext
  · exact liftQ_fst Db (pushZ Db w)
  · rw [(liftQ Db (pushZ Db w)).2, w.2]

theorem pushZ_liftQ (z) : pushZ Db (liftQ Db z) = z :=
  Subtype.ext (liftQ_fst Db z)

noncomputable def ptsQ {J : Type} (pts : J ≃ SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap ℤ (AlgebraicClosure ℚ)))) Db) :
    J ≃ SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap ℚ (AlgebraicClosure ℚ))))
      (pullback.snd Db (Spec.map (CommRingCat.ofHom (algebraMap ℤ ℚ)))) :=
  pts.trans ⟨liftQ Db, pushZ Db, pushZ_liftQ Db, liftQ_pushZ Db⟩

@[scoped simp] theorem ptsQ_fst {J : Type} (pts : J ≃ SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap ℤ (AlgebraicClosure ℚ)))) Db) (x : J) :
    (ptsQ Db pts x).1 ≫ pullback.fst Db _ = (pts x).1 :=
  liftQ_fst Db (pts x)

end Pts
p2m_reactivate "P2MW.S_ModularCurve_forall_exists_schemeHomOver_baseChange_rat_isHom_pts_smul_of_dRModelPackage.ModularCurve P2MW.S_ModularCurve_forall_exists_schemeHomOver_baseChange_rat_isHom_pts_smul_of_dRModelPackage.ModularCurve.HeckeGenQStepB"

end S6C1
p2m_reactivate "P2MW.S_ModularCurve_forall_exists_schemeHomOver_baseChange_rat_isHom_pts_smul_of_dRModelPackage.ModularCurve P2MW.S_ModularCurve_forall_exists_schemeHomOver_baseChange_rat_isHom_pts_smul_of_dRModelPackage.ModularCurve.HeckeGenQStepB P2MW.S_ModularCurve_forall_exists_schemeHomOver_baseChange_rat_isHom_pts_smul_of_dRModelPackage.S6C1"

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian ModularCurve~jBar P2MW.S_ModularCurve_forall_exists_schemeHomOver_baseChange_rat_isHom_pts_smul_of_dRModelPackage.ModularCurve AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve AlgebraicCurve"

set_option maxHeartbeats 3200000 in

theorem solution
    (p : ℕ) [Fact p.Prime] (𝔛 : DRModelPackage p) [IsProper (DRModel.toBase p)]
    [IsCurveOver (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar p)]
    (D : RelativePic0Designation ℤ (DRModel.toBase p))
    (hD : RepresentsRelSubPic (DRModel.toBase p) 𝔛.εinf (algEquivZeroCut (DRModel.toBase p) 𝔛.εinf) D)
    (hsm : Smooth D.toBase) (hconn : GeometricallyConnected D.toBase)

    (h' : RepresentsRelSubPic (baseChange ℤ (DRModel.toBase p) ℚ) (sectionBaseChange ℚ 𝔛.εinf)
          (algEquivZeroCut (baseChange ℤ (DRModel.toBase p) ℚ) (sectionBaseChange ℚ 𝔛.εinf)) (D.baseChange ℚ))
    (ajQ : SchemeHomOver (baseChange ℤ (DRModel.toBase p) ℚ) (D.baseChange ℚ).toBase)
    (aj : 𝔛.Mη.C ⟶ D.P)
    (εbar : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Mη.C // q ≫ 𝔛.Mη.toBase = 𝟙 _})
    (pts : JZero p ≃ SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap ℤ (AlgebraicClosure ℚ)))) D.toBase)
    (hcomm : (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut (DRModel.toBase p) 𝔛.εinf) hD).IsCommutative)
    (pts_add : ∀ x y : JZero p, pts (x + y) =
      (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut (DRModel.toBase p) 𝔛.εinf) hD).mul _ (pts x) (pts y))
    (hpa : IsProper (pullback.snd D.toBase
      (Spec.map (CommRingCat.ofHom (algebraMap ℤ (Localization.Away (p : ℤ)))))))
    (hP : Nonempty (h'.poincare.L ≅ (BaseChange.ofR (DRModel.toBase p) 𝔛.εinf ℚ
      (hD.poincare.pullbackAlong ⟨pullback.fst D.toBase (specMap ℤ ℚ), pullback.condition⟩)).L))
    (hajQε : (sectionBaseChange ℚ 𝔛.εinf).1 ≫ ajQ.1 = (D.baseChange ℚ).zeroSection)
    (haj : ∀ (K : Type) [Field K] (t : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of ℚ))
        (x : SchemeHomOver t (baseChange ℤ (DRModel.toBase p) ℚ)),
      Nonempty ((h'.poincare.pullbackAlong
          ⟨x.1 ≫ ajQ.1, (Category.assoc _ _ _).trans ((congrArg (x.1 ≫ ·) ajQ.2).trans x.2)⟩).L ≅
        (RelEffCartierDiv.ofPoint (baseChange ℤ (DRModel.toBase p) ℚ) x.1 x.2).lineBundle ⊗
          (RelEffCartierDiv.ofPoint (baseChange ℤ (DRModel.toBase p) ℚ) (t ≫ (sectionBaseChange ℚ 𝔛.εinf).1)
            ((Category.assoc _ _ _).trans ((congrArg (t ≫ ·) (sectionBaseChange ℚ 𝔛.εinf).2).trans
              (Category.comp_id t)))).idealModule))
    (k₀ : pullback (DRModel.toBase p) (specMap ℤ (AlgebraicClosure ℚ)) ⟶ pullback (DRModel.toBase p) (specMap ℤ ℚ))
    (hk₀fst : k₀ ≫ pullback.fst (DRModel.toBase p) (specMap ℤ ℚ) = pullback.fst (DRModel.toBase p) (specMap ℤ (AlgebraicClosure ℚ)))
    (hk₀snd : k₀ ≫ pullback.snd (DRModel.toBase p) (specMap ℤ ℚ) =
      pullback.snd (DRModel.toBase p) (specMap ℤ (AlgebraicClosure ℚ)) ≫ specMap ℚ (AlgebraicClosure ℚ))
    (haj_eq : aj = 𝔛.eη ≫ k₀ ≫ ajQ.1 ≫ pullback.fst D.toBase (specMap ℤ ℚ))
    (haj_over : aj ≫ D.toBase = 𝔛.Mη.toBase ≫ Spec.map (CommRingCat.ofHom (algebraMap ℤ (AlgebraicClosure ℚ))))
    (hεbar : εbar.1 ≫ 𝔛.eη ≫ pullback.fst (DRModel.toBase p) _ =
      Spec.map (CommRingCat.ofHom (algebraMap ℤ (AlgebraicClosure ℚ))) ≫ 𝔛.εinf.1)
    (hajs : εbar.1 ≫ aj = Spec.map (CommRingCat.ofHom (algebraMap ℤ (AlgebraicClosure ℚ))) ≫ D.zeroSection)
    (pts_aj : ∀ x : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Mη.C // q ≫ 𝔛.Mη.toBase = 𝟙 _},
      ∃ Dv : Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar p)),
        (Dv : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar p)) =
          Finsupp.single (𝔛.Mη.pointEquivPlace x) 1 - Finsupp.single (𝔛.Mη.pointEquivPlace εbar) 1 ∧
        (pts (Pic0.mk Dv)).1 = x.1 ≫ aj) :

    letI := heckeModuleBar p
    ∀ t : HeckeAlg,
      ∃ φη : SchemeHomOver
          (pullback.snd D.toBase (Spec.map (CommRingCat.ofHom (algebraMap ℤ ℚ))))
          (pullback.snd D.toBase (Spec.map (CommRingCat.ofHom (algebraMap ℤ ℚ)))),
        (∀ {T : Scheme.{0}} (s : T ⟶ Spec (CommRingCat.of ℚ))
            (x y : SchemeHomOver s (pullback.snd D.toBase (Spec.map (CommRingCat.ofHom (algebraMap ℤ ℚ))))),
          NeronModelInfra.schemeHomOverComp
              (((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut (DRModel.toBase p) 𝔛.εinf) hD).baseChange
                  (Spec.map (CommRingCat.ofHom (algebraMap ℤ ℚ)))).mul s x y) φη =
            ((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut (DRModel.toBase p) 𝔛.εinf) hD).baseChange
                (Spec.map (CommRingCat.ofHom (algebraMap ℤ ℚ)))).mul s
              (NeronModelInfra.schemeHomOverComp x φη) (NeronModelInfra.schemeHomOverComp y φη)) ∧
        (∀ (x : JZero p)
            (z zt : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶
              pullback D.toBase (Spec.map (CommRingCat.ofHom (algebraMap ℤ ℚ)))),
          z ≫ pullback.fst D.toBase _ = (pts x).1 → zt ≫ pullback.fst D.toBase _ = (pts (t • x)).1 → zt = z ≫ φη.1) := by
  intro t
  classical
  letI := heckeModuleBar p

  set ιQ : Spec (CommRingCat.of ℚ) ⟶ Spec (CommRingCat.of ℤ) := Spec.map (CommRingCat.ofHom (algebraMap ℤ ℚ)) with hιQ
  set Llaw := (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut (DRModel.toBase p) 𝔛.εinf) hD) with hLlaw
  set LQ : RelativeGroupLaw ℚ (pullback.snd D.toBase ιQ) := Llaw.baseChange ιQ with hLQ
  have hcQ : LQ.IsCommutative := S6C1.isCommutative_baseChange ιQ Llaw hcomm

  let cℚ := baseChange ℤ (DRModel.toBase p) ℚ
  let εℚ := sectionBaseChange ℚ 𝔛.εinf
  have lawEq : ∀ {T : Scheme.{0}} (s : T ⟶ Spec (CommRingCat.of ℚ))
      (x y : SchemeHomOver s (pullback.snd D.toBase ιQ)),
      LQ.mul s x y = (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut cℚ εℚ) h').mul s x y := by
    intro T s x y
    apply Subtype.ext
    apply pullback.hom_ext
    · rw [S6C1.toBase_mul_val ιQ Llaw s x y]
      exact (AlgebraicGeometry.RelPicard.baseChange_relativeGroupLaw_mul_compat ℤ (DRModel.toBase p) 𝔛.εinf D hD ℚ
        h' hP s x y (RelativeGroupLaw.baseChangePointToBase ιQ x) (RelativeGroupLaw.baseChangePointToBase ιQ y)
        rfl rfl).symm
    · rw [(LQ.mul s x y).2,
        ((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut cℚ εℚ) h').mul s x y).2]

  have hbase : ∀ (z : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ pullback D.toBase ιQ),
      (z ≫ pullback.snd D.toBase ιQ) ≫ ιQ = Spec.map (CommRingCat.ofHom (algebraMap ℤ (AlgebraicClosure ℚ))) :=
    fun z => specZIsTerminal.hom_ext _ _

  letI instG : ∀ {T : Scheme.{0}} (s : T ⟶ Spec (CommRingCat.of ℤ)), Group (SchemeHomOver s D.toBase) :=
    fun s => Llaw.pointGroup s
  have pts_zsmul : ∀ (a : ℤ) (x : JZero p), pts (a • x) = (pts x) ^ a := by
    intro a x
    let f : Multiplicative (JZero p) →* SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap ℤ (AlgebraicClosure ℚ)))) D.toBase :=
      MonoidHom.mk' (fun y => pts y.toAdd) (fun y y' => pts_add y.toAdd y'.toAdd)
    have := map_zpow f (Multiplicative.ofAdd x) a
    simpa [f] using this

  let PtsFst : HeckeAlg → SchemeHomOver (pullback.snd D.toBase ιQ) (pullback.snd D.toBase ιQ) → Prop :=
    fun t φ => ∀ (x : JZero p) (z : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ pullback D.toBase ιQ),
      z ≫ pullback.fst D.toBase ιQ = (pts x).1 → (z ≫ φ.1) ≫ pullback.fst D.toBase ιQ = (pts (t • x)).1

  suffices H : ∃ φη : SchemeHomOver (pullback.snd D.toBase ιQ) (pullback.snd D.toBase ιQ),
      S6C1.IsHom LQ φη ∧ PtsFst t φη by
    obtain ⟨φη, hφ, hP'⟩ := H
    refine ⟨φη, fun s x y => hφ s x y, ?_⟩
    intro x z zt hz hzt
    apply pullback.hom_ext
    · rw [hzt, ← hP' x z hz, Category.assoc]
    · rw [Category.assoc, φη.2]
      exact S6C1.specRat_hom_ext _ _

  let zpt : ∀ (z : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ pullback D.toBase ιQ),
      SchemeHomOver (z ≫ pullback.snd D.toBase ιQ) (pullback.snd D.toBase ιQ) := fun z => ⟨z, rfl⟩

  have gen : ∀ n : Nat.Primes, ∃ γ : SchemeHomOver (pullback.snd D.toBase ιQ) (pullback.snd D.toBase ιQ),
      S6C1.IsHom LQ γ ∧ PtsFst (MvPolynomial.X n) γ := by
    intro n
    haveI : Fact (n : ℕ).Prime := ⟨n.2⟩
    haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
    haveI : NeZero (n : ℕ) := ⟨n.2.ne_zero⟩
    haveI : NeZero (p * (n : ℕ)) := ⟨Nat.mul_ne_zero (NeZero.ne p) n.2.ne_zero⟩
    haveI := 𝔛.e₀_iso

    have htrans₀ := ModularCurve.HeckeGenQStepB.transcendental_jFull (p * (n : ℕ))
    obtain ⟨πα₀, πβ₀, hα₀, hβ₀, hα, hβ, hfinα, hflatα, hlfpα, hdα, hfinβ, hflatβ, hlfpβ, hdβ,
        hfinα₀, hflatα₀, hlfpα₀, hfinβ₀, hflatβ₀, hlfpβ₀, hgenα₀, hgenβ₀, hplα₀, hplβ₀⟩ :=
      ModularCurve.HeckeGenQStepB.stepB p (n : ℕ) htrans₀ cℚ 𝔛.M₀ 𝔛.e₀ 𝔛.he₀
    set πα := πα₀ ≫ 𝔛.e₀ with hπα
    set πβ := πβ₀ ≫ 𝔛.e₀ with hπβ
    set d : ℕ := finrankAlong ℚ (ModularCurve.HeckeGenQStepB.alpha0ₐ p (n : ℕ)) with hd_def
    haveI := hfinα; haveI := hflatα; haveI := hlfpα; haveI := hfinβ; haveI := hflatβ; haveI := hlfpβ

    let Φ : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of ℚ)),
        RigidifiedLineBundle cℚ εℚ t → RigidifiedLineBundle cℚ εℚ t := fun t M =>
      RigidifiedLineBundle.ofInvertible (ε := εℚ)
        (Scheme.Modules.normModule (curveChange πα hα t) d
          ((Scheme.Modules.pullback (curveChange πβ hβ t)).obj M.L))
        (HGQSeams.hinv (ε := εℚ) πα πβ hα hβ d hdα t M)
    obtain ⟨φη, hφη, -⟩ := RepresentsRelSubPic.existsUnique_hom_of_transform h' h' Φ
      (fun t M M' h => HGQSeams.hcongr (ε := εℚ) πα πβ hα hβ d hdα t M M' h)
      (fun ψ M => HGQSeams.hnat (ε := εℚ) πα πβ hα hβ d hdα ψ M)
      (fun t M hM => HGQSeams.hcut (ε := εℚ) πα πβ hα hβ d hdα t M hM)
    have hhom := RepresentsRelSubPic.comp_mul_eq_mul_comp_of_transform
      (P := algEquivZeroGroupCut cℚ εℚ) (P' := algEquivZeroGroupCut cℚ εℚ) h' h' Φ
      (fun t M hM => HGQSeams.hcut (ε := εℚ) πα πβ hα hβ d hdα t M hM)
      (fun t M M' => HGQSeams.htensor (ε := εℚ) πα πβ hα hβ d hdα t M M')
      (fun t => HGQSeams.hunit (ε := εℚ) πα πβ hα hβ d hdα t) φη hφη
    refine ⟨φη, ?_, ?_⟩
    ·
      intro T s x y
      simp only [lawEq]
      exact hhom.1 s x y
    ·

      have hsq₁ : IsPullback (k₀ ≫ pullback.fst (DRModel.toBase p) ιQ)
          (pullback.snd (DRModel.toBase p) (specMap ℤ (AlgebraicClosure ℚ))) (DRModel.toBase p)
          (specMap ℚ (AlgebraicClosure ℚ) ≫ ιQ) := by
        have h0 := IsPullback.of_hasPullback (DRModel.toBase p) (specMap ℤ (AlgebraicClosure ℚ))
        rw [← hk₀fst] at h0
        convert h0 using 2
        exact ModularCurve.SpecMap_algebraMap_int_eq_comp.symm
      have sq : IsPullback k₀ (pullback.snd (DRModel.toBase p) (specMap ℤ (AlgebraicClosure ℚ))) cℚ
          (specMap ℚ (AlgebraicClosure ℚ)) :=
        IsPullback.of_right hsq₁ hk₀snd (IsPullback.of_hasPullback (DRModel.toBase p) ιQ)
      haveI := 𝔛.eη_iso
      let eηQ : 𝔛.Mη.C ⟶ pullback cℚ (Spec.map (CommRingCat.ofHom (algebraMap ℚ (AlgebraicClosure ℚ)))) :=
        𝔛.eη ≫ sq.isoPullback.hom
      haveI heηQ_iso : IsIso eηQ := inferInstance
      have heηQ_fst : eηQ ≫ pullback.fst cℚ _ = 𝔛.eη ≫ k₀ := by
        simp only [eηQ, Category.assoc, IsPullback.isoPullback_hom_fst]
      have heηQ : eηQ ≫ pullback.snd cℚ _ = 𝔛.Mη.toBase := by
        simp only [eηQ, Category.assoc, IsPullback.isoPullback_hom_snd]
        exact 𝔛.heη
      have hgalQ : ∀ (g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
          (x x' : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Mη.C // q ≫ 𝔛.Mη.toBase = 𝟙 _}),
          x'.1 ≫ eηQ ≫ pullback.fst cℚ _ =
            Spec.map (CommRingCat.ofHom (g : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ)) ≫ x.1 ≫ eηQ ≫ pullback.fst cℚ _ →
          𝔛.Mη.pointEquivPlace x' =
            arithmeticGalois (L := AlgebraicClosure ℚ) (modularFunctionFieldFull p) g • 𝔛.Mη.pointEquivPlace x := by
        intro g x x' hx
        apply 𝔛.hgal g x x'
        rw [← hk₀fst]
        have hx' := congrArg (· ≫ pullback.fst (DRModel.toBase p) ιQ) hx
        simpa only [Category.assoc, heηQ_fst] using hx'

      haveI := 𝔛.eη_iso
      obtain ⟨eηℚ, hIηℚ, heηℚ, heηℚ_fst, hcompatℚ⟩ :=
        ModularCurve.exists_baseChangeIso_rat_of_baseChangeIso_int (modularFunctionFieldFull p) (DRModel.toBase p)
          𝔛.Mη 𝔛.eη 𝔛.heη 𝔛.M₀ 𝔛.e₀ 𝔛.he₀ 𝔛.hcompat
      haveI := hIηℚ

      have htrans' : Transcendental (AlgebraicClosure ℚ) (CharPModel.jBar (p * (n : ℕ))) := by
        have hjq : Transcendental (AlgebraicClosure ℚ)
            ((CharPModel.jBar (p * (n : ℕ)) : modularFunctionFieldBar (p * (n : ℕ))) : LaurentSeries (AlgebraicClosure ℚ)) := by
          have h' := transcendental_jqModC (AlgebraicClosure ℚ)
          have hcoe : ((CharPModel.jBar (p * (n : ℕ)) : modularFunctionFieldBar (p * (n : ℕ))) :
              LaurentSeries (AlgebraicClosure ℚ)) = jqModC (AlgebraicClosure ℚ) := coeffEmb_jq (AlgebraicClosure ℚ)
          exact hcoe ▸ h'
        exact (transcendental_algebraMap_iff
          (FaithfulSMul.algebraMap_injective (modularFunctionFieldBar (p * (n : ℕ)))
            (LaurentSeries (AlgebraicClosure ℚ)))).mp hjq
      haveI hne' : Fact (CharPModel.jBar (p * (n : ℕ)) ≠ 0) := ⟨fun h0 => htrans' (h0 ▸ isAlgebraic_zero)⟩
      haveI : Algebra.EssFiniteType (AlgebraicClosure ℚ) (modularFunctionFieldBar (p * (n : ℕ))) :=
        essFiniteType_modularFunctionFieldBar (p * (n : ℕ))
      obtain ⟨tgen, -, htgen_fd, -⟩ := isCurveOver_iff_exists_transcendental_finiteDimensional.mp
        (isCurveOver_modularFunctionFieldBar (p * (n : ℕ)))
      haveI := htgen_fd
      haveI hfd' : FiniteDimensional
          ↥(IntermediateField.adjoin (AlgebraicClosure ℚ)
            ({CharPModel.jBar (p * (n : ℕ))} : Set (modularFunctionFieldBar (p * (n : ℕ)))))
          (modularFunctionFieldBar (p * (n : ℕ))) :=
        finiteDimensional_adjoin_of_transcendental tgen htrans'
      haveI hfd_inv' : FiniteDimensional
          ↥(IntermediateField.adjoin (AlgebraicClosure ℚ)
            ({(CharPModel.jBar (p * (n : ℕ)))⁻¹} : Set (modularFunctionFieldBar (p * (n : ℕ)))))
          (modularFunctionFieldBar (p * (n : ℕ))) :=
        finiteDimensional_adjoin_of_transcendental tgen
          (fun halg => htrans' (by have h' := halg.inv; rwa [inv_inv] at h'))

      obtain ⟨⟨cFin, hcFin⟩, ⟨cInf, hcInf⟩⟩ := ModularCurve.HeckeGenQStepE.exists_chartIso (p * (n : ℕ)) 2

      obtain ⟨eη', hIη', heη', hcompat', -, -⟩ :=
        ModularCurve.exists_ofGenerator_baseChangeIso_chartPin_and_placeCompat (p * (n : ℕ))
          htrans' htrans₀ cFin hcFin cInf hcInf
      haveI := hIη'

      have hαI : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) p (n : ℕ) :=
        heckeAlphaBarIntegral_of_prime (AlgebraicClosure ℚ) p (n : ℕ)
      have hβI : HeckeBetaBarIntegral (AlgebraicClosure ℚ) p (n : ℕ) :=
        heckeBetaBarIntegral_of_prime (AlgebraicClosure ℚ) p (n : ℕ)
      have bridge : ∀ (π₀ : (CurveModel.ofGenerator ℚ (IgusaScheme.jFull (p * (n : ℕ))) htrans₀).C ⟶ 𝔛.M₀.C)
          (hπ₀ : π₀ ≫ 𝔛.M₀.toBase = (CurveModel.ofGenerator ℚ (IgusaScheme.jFull (p * (n : ℕ))) htrans₀).toBase)
          (y : {pt : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ (CurveModel.ofGenerator (AlgebraicClosure ℚ) (CharPModel.jBar (p * (n : ℕ))) htrans').C //
            pt ≫ (CurveModel.ofGenerator (AlgebraicClosure ℚ) (CharPModel.jBar (p * (n : ℕ))) htrans').toBase = 𝟙 _})
          (x : {pt : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Mη.C // pt ≫ 𝔛.Mη.toBase = 𝟙 _}),
          y.1 ≫ eη' ≫ pullback.fst _ _ ≫ (π₀ ≫ 𝔛.e₀) ≫ pullback.fst (DRModel.toBase p) _ =
            x.1 ≫ 𝔛.eη ≫ pullback.fst (DRModel.toBase p) _ →
          y.1 ≫ eη' ≫ pullback.map (CurveModel.ofGenerator ℚ (IgusaScheme.jFull (p * (n : ℕ))) htrans₀).toBase
              (Spec.map (CommRingCat.ofHom (algebraMap ℚ (AlgebraicClosure ℚ)))) 𝔛.M₀.toBase
              (Spec.map (CommRingCat.ofHom (algebraMap ℚ (AlgebraicClosure ℚ)))) π₀ (𝟙 _) (𝟙 _)
              (by rw [Category.comp_id, hπ₀]) (by rw [Category.comp_id, Category.id_comp]) =
            x.1 ≫ eηℚ := by
        intro π₀ hπ₀ y x hyx
        have hmf : pullback.map (CurveModel.ofGenerator ℚ (IgusaScheme.jFull (p * (n : ℕ))) htrans₀).toBase
              (Spec.map (CommRingCat.ofHom (algebraMap ℚ (AlgebraicClosure ℚ)))) 𝔛.M₀.toBase
              (Spec.map (CommRingCat.ofHom (algebraMap ℚ (AlgebraicClosure ℚ)))) π₀ (𝟙 _) (𝟙 _)
              (by rw [Category.comp_id, hπ₀]) (by rw [Category.comp_id, Category.id_comp]) ≫ pullback.fst _ _ =
            pullback.fst _ _ ≫ π₀ := pullback.lift_fst _ _ _
        have hms : pullback.map (CurveModel.ofGenerator ℚ (IgusaScheme.jFull (p * (n : ℕ))) htrans₀).toBase
              (Spec.map (CommRingCat.ofHom (algebraMap ℚ (AlgebraicClosure ℚ)))) 𝔛.M₀.toBase
              (Spec.map (CommRingCat.ofHom (algebraMap ℚ (AlgebraicClosure ℚ)))) π₀ (𝟙 _) (𝟙 _)
              (by rw [Category.comp_id, hπ₀]) (by rw [Category.comp_id, Category.id_comp]) ≫ pullback.snd _ _ =
            pullback.snd _ _ ≫ 𝟙 _ := pullback.lift_snd _ _ _
        apply pullback.hom_ext
        · simp only [Category.assoc, hmf]
          rw [← cancel_mono 𝔛.e₀]
          apply pullback.hom_ext
          · simp only [Category.assoc] at hyx ⊢
            rw [heηℚ_fst]
            exact hyx
          · simp only [Category.assoc]
            rw [𝔛.he₀, hπ₀, pullback.condition, pullback.condition, reassoc_of% heη', reassoc_of% y.2,
              reassoc_of% heηℚ, reassoc_of% x.2]
        · simp only [Category.assoc, hms, Category.comp_id]
          rw [heη', y.2, heηℚ, x.2]

      have down : ∀ (π : (CurveModel.ofGenerator ℚ (IgusaScheme.jFull (p * (n : ℕ))) htrans₀).C ⟶ pullback (DRModel.toBase p) ιQ)
          (y : {pt : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ (CurveModel.ofGenerator (AlgebraicClosure ℚ) (CharPModel.jBar (p * (n : ℕ))) htrans').C //
            pt ≫ (CurveModel.ofGenerator (AlgebraicClosure ℚ) (CharPModel.jBar (p * (n : ℕ))) htrans').toBase = 𝟙 _})
          (x : {pt : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Mη.C // pt ≫ 𝔛.Mη.toBase = 𝟙 _}),
          y.1 ≫ eη' ≫ pullback.fst _ _ ≫ π = x.1 ≫ eηQ ≫ pullback.fst cℚ _ →
          y.1 ≫ eη' ≫ pullback.fst _ _ ≫ π ≫ pullback.fst (DRModel.toBase p) _ =
            x.1 ≫ 𝔛.eη ≫ pullback.fst (DRModel.toBase p) _ := by
        intro π y x hyx
        have h1 := congrArg (· ≫ pullback.fst (DRModel.toBase p) ιQ) hyx
        simp only [Category.assoc] at h1
        rw [h1, reassoc_of% heηQ_fst]
        erw [hk₀fst]
      have hplaceα : ∀ (y : {pt : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ (CurveModel.ofGenerator (AlgebraicClosure ℚ) (CharPModel.jBar (p * (n : ℕ))) htrans').C //
            pt ≫ (CurveModel.ofGenerator (AlgebraicClosure ℚ) (CharPModel.jBar (p * (n : ℕ))) htrans').toBase = 𝟙 _})
          (x : {pt : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Mη.C // pt ≫ 𝔛.Mη.toBase = 𝟙 _}),
          y.1 ≫ eη' ≫ pullback.fst _ _ ≫ πα = x.1 ≫ eηQ ≫ pullback.fst cℚ _ →
          𝔛.Mη.pointEquivPlace x =
            Place.restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) p (n : ℕ)) hαI
              ((CurveModel.ofGenerator (AlgebraicClosure ℚ) (CharPModel.jBar (p * (n : ℕ))) htrans').pointEquivPlace y) :=
        fun y x hyx => ModularCurve.pointEquivPlace_comp_eq_restrictAlong_of_baseChange
          (modularFunctionFieldFull p) (modularFunctionFieldFull (p * (n : ℕ)))
          (ModularCurve.HeckeGenQStepB.alpha0 p (n : ℕ)) (ModularCurve.HeckeGenQStepB.alpha0_isIntegral p (n : ℕ))
          (heckeAlphaBar (AlgebraicClosure ℚ) p (n : ℕ)) hαI
          (ModularCurve.HeckeGenQStepB.alpha0_baseChange (AlgebraicClosure ℚ) p (n : ℕ))
          𝔛.M₀ (CurveModel.ofGenerator ℚ (IgusaScheme.jFull (p * (n : ℕ))) htrans₀) πα₀ hα₀ hgenα₀ 𝔛.Mη eηℚ heηℚ hcompatℚ
          (CurveModel.ofGenerator (AlgebraicClosure ℚ) (CharPModel.jBar (p * (n : ℕ))) htrans') eη' heη' hcompat' y x
          (bridge πα₀ hα₀ y x (by simpa only [hπα, Category.assoc] using down πα y x hyx))
      have hplaceβ : ∀ (y : {pt : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ (CurveModel.ofGenerator (AlgebraicClosure ℚ) (CharPModel.jBar (p * (n : ℕ))) htrans').C //
            pt ≫ (CurveModel.ofGenerator (AlgebraicClosure ℚ) (CharPModel.jBar (p * (n : ℕ))) htrans').toBase = 𝟙 _})
          (x : {pt : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Mη.C // pt ≫ 𝔛.Mη.toBase = 𝟙 _}),
          y.1 ≫ eη' ≫ pullback.fst _ _ ≫ πβ = x.1 ≫ eηQ ≫ pullback.fst cℚ _ →
          𝔛.Mη.pointEquivPlace x =
            Place.restrictAlong (heckeBetaBar (AlgebraicClosure ℚ) p (n : ℕ)) hβI
              ((CurveModel.ofGenerator (AlgebraicClosure ℚ) (CharPModel.jBar (p * (n : ℕ))) htrans').pointEquivPlace y) :=
        fun y x hyx => ModularCurve.pointEquivPlace_comp_eq_restrictAlong_of_baseChange
          (modularFunctionFieldFull p) (modularFunctionFieldFull (p * (n : ℕ)))
          (ModularCurve.HeckeGenQStepB.beta0 p (n : ℕ)) (ModularCurve.HeckeGenQStepB.beta0_isIntegral p (n : ℕ))
          (heckeBetaBar (AlgebraicClosure ℚ) p (n : ℕ)) hβI
          (ModularCurve.HeckeGenQStepB.beta0_baseChange (AlgebraicClosure ℚ) p (n : ℕ))
          𝔛.M₀ (CurveModel.ofGenerator ℚ (IgusaScheme.jFull (p * (n : ℕ))) htrans₀) πβ₀ hβ₀ hgenβ₀ 𝔛.Mη eηℚ heηℚ hcompatℚ
          (CurveModel.ofGenerator (AlgebraicClosure ℚ) (CharPModel.jBar (p * (n : ℕ))) htrans') eη' heη' hcompat' y x
          (bridge πβ₀ hβ₀ y x (by simpa only [hπβ, Category.assoc] using down πβ y x hyx))

      haveI : SmoothOfRelativeDimension 1 cℚ := by
        have h1 : SmoothOfRelativeDimension 1 (𝔛.e₀ ≫ cℚ) := by
          rw [show 𝔛.e₀ ≫ cℚ = 𝔛.M₀.toBase from 𝔛.he₀]
          infer_instance
        exact (MorphismProperty.cancel_left_of_respectsIso (@SmoothOfRelativeDimension 1) 𝔛.e₀ cℚ).mp h1
      haveI : GeometricallyIntegral cℚ := by

        exact ModularCurve.geometricallyIntegral_baseChangeToBase_twoChartIntegralModel_rat p
      have hsmQ : Smooth (D.baseChange ℚ).toBase := by haveI := hsm; exact inferInstance
      have hprQ : IsProper (D.baseChange ℚ).toBase :=
        S6C1.isProper_snd_rat D.toBase p (Fact.out : p.Prime).ne_zero hpa
      have hgcQ : GeometricallyConnected (D.baseChange ℚ).toBase := by haveI := hconn; exact inferInstance

      let ptsQ := S6C1.ptsQ D.toBase pts
      have ptsQ_fst : ∀ y, (ptsQ y).1 ≫ pullback.fst D.toBase ιQ = (pts y).1 :=
        fun y => S6C1.ptsQ_fst D.toBase pts y
      have haddQ : ∀ x y : JZero p, ptsQ (x + y) =
          (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut cℚ εℚ) h').mul _ (ptsQ x) (ptsQ y) := by
        intro x y
        rw [← lawEq]
        apply Subtype.ext
        apply pullback.hom_ext
        · rw [ptsQ_fst, pts_add, S6C1.toBase_mul_val ιQ Llaw]
          exact S6C1.mul_val_eq Llaw (S6C1.tQ_ιQ).symm _ _ _ _ (ptsQ_fst x).symm (ptsQ_fst y).symm
        · rw [(ptsQ (x + y)).2, (LQ.mul _ (ptsQ x) (ptsQ y)).2]
      have hnormQ : ∀ (x s : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Mη.C // q ≫ 𝔛.Mη.toBase = 𝟙 _}),
          s.1 ≫ eηQ ≫ pullback.fst cℚ _ = Spec.map (CommRingCat.ofHom (algebraMap ℚ (AlgebraicClosure ℚ))) ≫ εℚ.1 →
          ∃ Dv : Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar p)),
            (Dv : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar p)) =
              Finsupp.single (𝔛.Mη.pointEquivPlace x) 1 - Finsupp.single (𝔛.Mη.pointEquivPlace s) 1 ∧
            (ptsQ (Pic0.mk Dv)).1 = x.1 ≫ eηQ ≫ pullback.fst cℚ _ ≫ ajQ.1 := by
        intro x s hs

        have hsε : s = εbar := by
          apply Subtype.ext
          rw [← cancel_mono 𝔛.eη]
          apply pullback.hom_ext
          · calc (s.1 ≫ 𝔛.eη) ≫ pullback.fst (DRModel.toBase p) (specMap ℤ (AlgebraicClosure ℚ))
                = ((s.1 ≫ eηQ ≫ pullback.fst cℚ _) ≫ pullback.fst (DRModel.toBase p) ιQ) := by
                  rw [← hk₀fst]; simp only [Category.assoc]; rw [reassoc_of% heηQ_fst]
              _ = Spec.map (CommRingCat.ofHom (algebraMap ℤ (AlgebraicClosure ℚ))) ≫ 𝔛.εinf.1 := by
                  rw [hs, Category.assoc, sectionBaseChange_coe_fst, ← Category.assoc, S6C1.tQ_ιQ]
              _ = (εbar.1 ≫ 𝔛.eη) ≫ pullback.fst (DRModel.toBase p) (specMap ℤ (AlgebraicClosure ℚ)) := by
                  rw [Category.assoc]; exact hεbar.symm
          · simp only [Category.assoc]
            rw [𝔛.heη, s.2, εbar.2]
        subst hsε
        obtain ⟨Dv, hDv, hpts⟩ := pts_aj x
        refine ⟨Dv, hDv, ?_⟩
        apply pullback.hom_ext
        · rw [ptsQ_fst, hpts, haj_eq]
          simp only [Category.assoc]
          rw [reassoc_of% heηQ_fst]
        · rw [(ptsQ _).2]
          simp only [Category.assoc]
          exact S6C1.specRat_hom_ext _ _

      have key := ModularCurve.heckeOperatorBar_points_eq_comp_of_transform_rat p cℚ εℚ (D.baseChange ℚ) h'
        hsmQ hprQ hgcQ ajQ hajQε haj 𝔛.Mη eηQ heηQ hgalQ n
        _ _ πα πβ hα hβ d hdα Φ (fun t M => ⟨Iso.refl _⟩)
        (fun t M hM => HGQSeams.hcut (ε := εℚ) πα πβ hα hβ d hdα t M hM) φη hφη (fun s x y => hhom.1 s x y)
        _ eη' heη' hαI hβI hplaceα hplaceβ ptsQ haddQ hnormQ

      intro x z hz
      have hz' : z = (ptsQ x).1 := by
        apply pullback.hom_ext
        · rw [hz, ptsQ_fst]
        · exact S6C1.specRat_hom_ext _ _
      have hT : (MvPolynomial.X n : HeckeAlg) • x = heckeOperatorBar p n x :=
        heckeModuleBar_heckeGen_smul (ModularCurve.heckeOperatorsCommuteBar p) n x
      rw [hz', hT, ← ptsQ_fst (heckeOperatorBar p n x), key x]

  induction t using MvPolynomial.induction_on with
  | C a =>
    refine ⟨(letI := LQ.pointGroup (pullback.snd D.toBase ιQ); S6C1.idEnd (pullback.snd D.toBase ιQ) ^ a),
      S6C1.isHom_idEnd_zpow LQ hcQ a, ?_⟩
    intro x z hz
    rw [heckeModuleBar_C_smul, pts_zsmul]
    have h1 := congrArg Subtype.val (S6C1.comp_idEnd_zpow LQ (zpt z) a)
    rw [NeronModelInfra.schemeHomOverComp_coe] at h1
    change z ≫ _ = _ at h1
    rw [h1, S6C1.toBase_zpow_val ιQ Llaw _ (zpt z) a]
    exact S6C1.zpow_val_eq Llaw (hbase z) _ _ (by simp [zpt, hz]) a
  | add s s' ihs ihs' =>
    obtain ⟨φ, hφ, Pφ⟩ := ihs
    obtain ⟨φ', hφ', Pφ'⟩ := ihs'
    refine ⟨LQ.mul _ φ φ', S6C1.isHom_mul LQ hcQ hφ hφ', ?_⟩
    intro x z hz
    rw [add_smul, pts_add]
    have h1 := congrArg Subtype.val (S6C1.comp_mul LQ (zpt z) φ φ')
    rw [NeronModelInfra.schemeHomOverComp_coe] at h1
    change z ≫ _ = _ at h1
    rw [h1, S6C1.toBase_mul_val ιQ Llaw _ _ _]
    refine S6C1.mul_val_eq Llaw (hbase z) _ _ _ _ ?_ ?_
    · simpa using Pφ x z hz
    · simpa using Pφ' x z hz
  | mul_X s n ihs =>
    obtain ⟨φ, hφ, Pφ⟩ := ihs
    obtain ⟨γ, hγ, Pγ⟩ := gen n
    refine ⟨NeronModelInfra.schemeHomOverComp γ φ, S6C1.isHom_comp LQ hγ hφ, ?_⟩
    intro x z hz
    rw [mul_smul, NeronModelInfra.schemeHomOverComp_coe, ← Category.assoc]
    exact Pφ (MvPolynomial.X n • x) (z ≫ γ.1) (Pγ x z hz)

end S_ModularCurve_forall_exists_schemeHomOver_baseChange_rat_isHom_pts_smul_of_dRModelPackage
end P2MW
export P2MW.S_ModularCurve_forall_exists_schemeHomOver_baseChange_rat_isHom_pts_smul_of_dRModelPackage (solution)
