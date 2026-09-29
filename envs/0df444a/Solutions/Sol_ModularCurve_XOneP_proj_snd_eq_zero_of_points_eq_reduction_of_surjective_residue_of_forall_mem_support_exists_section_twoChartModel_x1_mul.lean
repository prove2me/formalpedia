-- Prove2me | solution 1 for ModularCurve.XOneP.proj_snd_eq_zero_of_points_eq_reduction_of_surjective_residue_of_forall_mem_support_exists_section_twoChartModel_x1_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/bd1473d8-3665-5b0d-a776-55f9e3c6a3d7

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
import Definitions.Def_AlgebraicGeometry_RelSubPicBaseChange
import Definitions.Def_AlgebraicGeometry_RelPicardPullback
import Definitions.Def_AlgebraicGeometry_ModulesRigidify
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_ModularCurve_JOnePOpsV2
import Definitions.Def_ModularCurve_X1HeckeModule
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_RelSubPicGroup
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivOfPoint
import Definitions.Def_ModularCurve_IgusaFunctionFieldX1
import Definitions.Def_AlgebraicCurve_GluedPic0
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_BaseChangeGalois
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_ModularCurve_X1HeckeModule
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidal
import Theorems.Thm_ModularCurve_XOneP_range_subset_smoothLocus_of_reduction_eq_of_not_mem_range_valuationSubring_twoChartModel_x1_mul
import Theorems.Thm_ModularCurve_XOneP_exists_schemeHomOver_poincare_iso_ofPoint_tensor_idealModule_of_reduction_fst_valuationSubring_twoChartModel_x1_mul
import Theorems.Thm_ModularCurve_XOneP_nonempty_poincare_pullbackAlong_points_pic0Mk_single_sub_single_iso_ofPoint_tensor_idealModule_twoChartModel_x1_mul
import Theorems.Thm_ModularCurve_XOneP_proj_snd_eq_zero_of_points_eq_reduction_of_poincare_iso_ofPoint_valuationSubring_twoChartModel_x1_mul
import Theorems.Thm_ModularCurve_XOneP_pts_add_eq_relativeGroupLaw_mul_and_pts_zero_eq_one_specialFibre_twoChartModel_x1_mul
import Theorems.Thm_ModularCurve_XOneP_exists_smoothLocus_maximal_twoChartModel_x1_mul
import Theorems.Thm_ModularCurve_XOneP_smoothOfRelativeDimension_one_and_geometricallyIntegral_baseChange_twoChartModel_x1_mul
import Theorems.Thm_AlgebraicCurve_isCurveOver_of_ringEquiv_functionField_of_isIntegral_of_smoothOfRelativeDimension_one
import Theorems.Thm_ModularCurve_isCurveOver_x1FunctionFieldBar
import Theorems.Thm_AlgebraicGeometry_IsSeparated_eq_of_spec_map_subtype_comp_eq
import Theorems.Thm_AlgebraicGeometry_RelPicard_relativeGroupLaw_baseChange_eq
import Theorems.Thm_AlgebraicGeometry_RelEffCartierDiv_nonempty_pullback_ofPoint_lineBundle_iso_and_idealModule_iso_of_range_subset
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_flat_toBase
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XOneP_proj_snd_eq_zero_of_points_eq_reduction_of_surjective_residue_of_forall_mem_support_exists_section_twoChartModel_x1_mul
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion CohCarrier.iotaDeg_range_finiteIndex CohCarrier.Gamma0Upper_finiteIndex CohCarrier.HeckeData.V_isScalarTower CohCarrier.HeckeData.opSubalgebra_isMulCommutative CohCarrier.HeckeData.mTheta_isPrime ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.instIsDomainTensorProduct"
p2m_attr_erase "instance" "AlgebraicClosure.Rat.isGalois ModularCurve.instIsElliptic_tateBase ModularCurve.instIsElliptic_tateLaurent ModularCurve.KatzGamma0Form.instModule ModularCurve.KatzGamma0Form.instZero ModularCurve.KatzLevelPForm.instSMul ModularCurve.KatzGamma0Form.instAdd ModularCurve.KatzLevelPForm.instAddCommGroup ModularCurve.KatzGamma0Form.instNeg ModularCurve.KatzGamma0Form.instAddCommGroup ModularCurve.KatzLevelPForm.instAdd ModularCurve.KatzLevelPForm.instSub ModularCurve.KatzLevelPForm.instNeg ModularCurve.KatzGamma0Form.instSMul ModularCurve.KatzGamma0Form.instSub ModularCurve.KatzLevelPForm.instZero ModularCurve.KatzLevelPForm.instModule KatzModularForm.instAddCommGroup KatzModularForm.instSub KatzModularForm.instZero KatzModularForm.instModule KatzModularForm.instAdd KatzModularForm.instNeg KatzModularForm.instSMul WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular ModularCurve.Gamma0Pair.isElliptic AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instNeg AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulInt"
p2m_attr_erase "instance" "AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAddCommGroup AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAdd AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSub AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulNat AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instZero AlgebraicGeometry.RelEffCartierDiv.subsingleton_of_degree_zero SheafOfModules.isIso_ihomModelToIhom AlgebraicGeometry.OModulePresheaf.isScalarTower AlgebraicGeometry.Scheme.OrderedAffineCover.instLinearOrder AlgebraicGeometry.OModulePresheaf.module AlgebraicGeometry.Scheme.OrderedAffineCover.instFintype AlgebraicGeometry.Scheme.OrderedAffineCover.instFintypeIdx AlgebraicGeometry.OModulePresheaf.addCommGroup AlgebraicGeometry.Scheme.OrderedAffineCover.instDecidableEqIdx AlgebraicGeometry.OModulePresheaf.moduleSections AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper"
p2m_attr_erase "instance" "AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule AlgebraicGeometry.RelEffCartierDiv.isClosedImmersion_subschemeι_resProdMap AlgebraicGeometry.RelEffCartierDiv.isOpenImmersion_resProdMap"
p2m_attr_erase "simp" "ModularCurve.jqNModC_one ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply"
p2m_attr_erase "simp" "AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule"
p2m_attr_erase "simp" "AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule CohCarrier.conjUpperMat_apply_11 CohCarrier.conjUpperMat_apply_10 CohCarrier.mem_Gamma0Upper CohCarrier.val_gamma0Units ModularCurve.JH.torsionGaloisRep_apply ModularCurve.qExpandAlgHomC_apply CohCarrier.Gen.dia.sizeOf_spec CohCarrier.Gen.U.injEq CohCarrier.Gen.T.sizeOf_spec CohCarrier.Gen.U.sizeOf_spec CohCarrier.Gen.T.injEq CohCarrier.Gen.dia.injEq CohCarrier.HeckeData.mk.sizeOf_spec CohCarrier.HeckeData.opAlgHom_X CohCarrier.HeckeData.toMLₒ_apply CohCarrier.HeckeData.mk.injEq CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply ModularCurve.ProjectiveLine.map_mk WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero"
p2m_attr_erase "simp" "ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_cuspidalDivisor₀ ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆"
p2m_attr_erase "simp" "ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.cuspData_yP ModularCurve.qTwistAlgHom_apply ModularCurve.cuspData_yQ ModularCurve.cuspData_xP ModularCurve.cuspData_xQ ModularCurve.val_cyclZeta ModularCurve.cuspShift_one ModularCurve.cuspShift_zero ModularCurve.LevelPData.mk.sizeOf_spec ModularCurve.KatzLevelPForm.neg_toFun ModularCurve.LevelP.coe_swapW ModularCurve.KatzLevelPForm.swap_swap KatzModularForm.pullbackLevelP_toFun ModularCurve.LevelPData.swap_xQ KatzModularForm.pullbackLevelP_zero ModularCurve.LevelPData.map_yP ModularCurve.KatzLevelPForm.swap_neg ModularCurve.KatzGamma0Form.toKatzLevelPForm_sub ModularCurve.KatzLevelPForm.swap_add KatzModularForm.swap_pullbackLevelP ModularCurve.KatzGamma0Form.toKatzLevelPForm_add ModularCurve.KatzLevelPForm.swap_smul ModularCurve.LevelPData.map_yQ ModularCurve.KatzLevelPForm.mk.injEq ModularCurve.KatzLevelPForm.zero_toFun KatzModularForm.pullbackLevelP_smul ModularCurve.LevelPData.swap_xP ModularCurve.KatzGamma0Form.toKatzLevelPForm_mul ModularCurve.KatzGamma0Form.toKatzLevelPForm_neg ModularCurve.LevelPData.variableChange_xQ KatzModularForm.pullbackGamma0_toKatzLevelPForm ModularCurve.KatzLevelPForm.mk.sizeOf_spec ModularCurve.KatzLevelPForm.swap_zero ModularCurve.LevelP.coe_unipotentU ModularCurve.KatzLevelPForm.mul_toFun ModularCurve.LevelPData.variableChange_yP"
p2m_attr_erase "simp" "ModularCurve.LevelPData.mk.injEq ModularCurve.KatzLevelPForm.sub_toFun ModularCurve.LevelPData.variableChange_xP ModularCurve.KatzLevelPForm.smul_toFun ModularCurve.LevelPData.swap_yP ModularCurve.LevelPData.map_xP ModularCurve.LevelPData.swap_swap ModularCurve.LevelPData.swap_yQ ModularCurve.KatzGamma0Form.toKatzLevelPForm_zero ModularCurve.KatzGamma0Form.mk.injEq ModularCurve.KatzLevelPForm.swap_toFun KatzModularForm.pullbackLevelP_add ModularCurve.KatzGamma0Form.mk.sizeOf_spec ModularCurve.LevelPData.variableChange_yQ ModularCurve.KatzLevelPForm.swap_sub ModularCurve.KatzGamma0Form.toKatzLevelPForm_smul ModularCurve.LevelPData.map_xQ ModularCurve.KatzLevelPForm.add_toFun KatzModularForm.c₆_toFun KatzModularForm.neg_toFun KatzModularForm.mul_toFun KatzModularForm.qExpansion_neg KatzModularForm.discr_toFun KatzModularForm.qExpansion_sub KatzModularForm.qExpansion_add KatzModularForm.qExpansion_mul KatzModularForm.zero_toFun KatzModularForm.mk.injEq KatzModularForm.qExpansion_smul KatzModularForm.smul_toFun KatzModularForm.add_toFun KatzModularForm.sub_toFun KatzModularForm.c₄_toFun KatzModularForm.qExpansion_zero KatzModularForm.mk.sizeOf_spec TateCurve.tateTorsionPoint_zero_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero"
p2m_attr_erase "simp" "TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial"
p2m_attr_erase "simp" "WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂"
p2m_attr_erase "simp" "WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff HahnSeries.ramScale_apply AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring ModularCurve.LevelN.coe_jGen ModularCurve.CharPReduction.coeffRed_coeff ModularCurve.CharPReduction.redLocHom_apply ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar ModularCurve.ComplexPlaceDictionaryOf.pt_ofGamma0 ModularCurve.ComplexPlaceDictionaryOf.mk.injEq ModularCurve.ComplexPlaceDictionaryOf.pt_toGamma0 ModularCurve.ComplexPlaceDictionaryOf.mk.sizeOf_spec ModularCurve.ComplexPlaceDictionary.mk.injEq ModularCurve.ComplexPlaceDictionary.mk.sizeOf_spec ModularCurve.gamma0PairMap_gen ModularCurve.moduliPointMapRingHom_mk ModularCurve.Gamma0Pair.mk.injEq ModularCurve.ModuliPoint.j_mk ModularCurve.Gamma0Pair.mk.sizeOf_spec ModularCurve.gamma0PairMap_toCurve WeierstrassCurve.ratPointHom_apply WeierstrassCurve.ratPointMap_zero RegularLocalRingQuotientAscent.dualNumberFst_apply AlgebraicGeometry.RelEffCartierDiv.supportedIn_top AlgebraicGeometry.RelEffCartierDiv.mem_supportedIn_iff AlgebraicGeometry.RelEffCartierDiv.supportedIn_top_eq AlgebraicGeometry.RelEffCartierDiv.IsUniversal.lift_comp AlgebraicGeometry.RelEffCartierDiv.functor_map_fst AlgebraicGeometry.RelEffCartierDiv.IsUniversal.homEquiv_apply AlgebraicGeometry.RelEffCartierDiv.IsUniversal.lift_pullbackAlong AlgebraicGeometry.RelEffCartierDiv.IsUniversal.homEquiv_symm_apply"
p2m_attr_erase "simp" "AlgebraicGeometry.RelEffCartierDiv.IsUniversal.lift_comp_assoc AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.sub_app AlgebraicGeometry.Scheme.IdealSheafData.sres_sresTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.add_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.sizeOf_spec AlgebraicGeometry.Scheme.IdealSheafData.coe_resLE AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.smul_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_ofLE_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.ideal_range AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zero_app AlgebraicGeometry.Scheme.IdealSheafData.sres_sres AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.comp_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.neg_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.id_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_mulRight_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.nsmul_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.injEq AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zsmul_app AlgebraicGeometry.prodKerGraph_one AlgebraicGeometry.fibrePowOver.proj_comp AlgebraicGeometry.prodKerGraph_zero AlgebraicGeometry.RelEffCartierDiv.empty_I AlgebraicGeometry.fibrePowOver.proj_comp_assoc AlgebraicCurve.SymmetricPowerPackage.mk.sizeOf_spec AlgebraicCurve.SymmetricPowerPackage.mk.injEq AlgebraicGeometry.RelPicard.fst_toProdSpec AlgebraicGeometry.RelPicard.toProdSpec_fst_assoc AlgebraicGeometry.RelPicard.pointsSubBasepointModule_cons AlgebraicGeometry.RelPicard.pointsSubBasepointModule_nil AlgebraicGeometry.RelPicard.fst_toProdSpec_assoc AlgebraicGeometry.RelPicard.toProdSpec_fst AlgebraicCurve.coe_cechH0Equiv_apply AlgebraicCurve.cechH1ToH1_mk AlgebraicCurve.lSpaceOn_univ AlgebraicCurve.lSpaceOn_empty AlgebraicGeometry.Scheme.Modules.toUnitSection_ofUnitSection AlgebraicGeometry.Scheme.Modules.pullbackSection_def AlgebraicGeometry.Scheme.Modules.ofUnitSection_toUnitSection PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom SheafOfModules.ihomSectionsEquivFamily_unit"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply SheafOfModules.ihomEval_unit_app AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply SheafOfModules.unit_ihomSectionsEquivFamily AlgebraicGeometry.Scheme.Modules.familyOfHom_app AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ AlgebraicGeometry.Scheme.OrderedAffineCover.mk.injEq AlgebraicGeometry.OModulePresheaf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.mk.injEq AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq TwoChartCech.Mumford.dK_apply TwoChartCech.Mumford.ι0_apply"
p2m_attr_erase "simp" "TwoChartCech.Mumford.ι1_apply TwoChartCech.KerCoprod.dK_apply TwoChartCech.KerCoprod.ι1_apply TwoChartCech.KerCoprod.ι0_apply AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app AlgebraicGeometry.RelEffCartierDiv.restrictAlong_extendAlong AlgebraicGeometry.RelEffCartierDiv.extendAlong_I AlgebraicGeometry.RelEffCartierDiv.resProdMap_snd AlgebraicGeometry.RelEffCartierDiv.restrictAlong_I AlgebraicGeometry.RelEffCartierDiv.extendAlong_restrictAlong AlgebraicGeometry.RelEffCartierDiv.resProdMap_fst_assoc AlgebraicGeometry.RelEffCartierDiv.resProdMap_snd_assoc AlgebraicGeometry.RelEffCartierDiv.resProdMap_fst AlgebraicGeometry.RelPicard.rigSection_snd AlgebraicGeometry.RelPicard.RigidifiedLineBundle.ofInvertible_L AlgebraicGeometry.RelPicard.rigSection_snd_assoc"

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra GoodReductionJacobian AlgebraicGeometry.SmoothProperCurve AlgebraicCurve IsLocalRing"

universe u

noncomputable section

namespace VR2Kit

noncomputable def tot (α : Type*) : (α →₀ ℤ) →+ ℤ := Finsupp.liftAddHom fun _ => AddMonoidHom.id ℤ

theorem tot_single {α : Type*} (a : α) (n : ℤ) : tot α (Finsupp.single a n) = n := by
  simp [tot]

theorem tot_eq_sum {α : Type*} (D : α →₀ ℤ) : tot α D = D.sum fun _ n => n := by
  simp only [tot, Finsupp.liftAddHom_apply]
  rfl

theorem pairs_decomposition {α : Type*} [DecidableEq α] (S : Finset α) :
    ∀ (N : ℕ) (D : α →₀ ℤ), D.support.card ≤ N → D.support ⊆ S → tot α D = 0 →
      ∃ l : List (α × α × ℤ), (∀ t ∈ l, t.1 ∈ S ∧ t.2.1 ∈ S) ∧
        D = (l.map fun t => t.2.2 • (Finsupp.single t.1 (1 : ℤ) - Finsupp.single t.2.1 1)).sum := by
  intro N
  induction N with
  | zero =>
    intro D hN _ _
    refine ⟨[], by simp, ?_⟩
    have : D.support = ∅ := Finset.card_eq_zero.mp (Nat.le_zero.mp hN)
    rw [Finsupp.support_eq_empty] at this
    simp [this]
  | succ N ih =>
    intro D hN hS hsum
    by_cases h0 : D = 0
    · exact ⟨[], by simp, by simp [h0]⟩
    obtain ⟨P, hP⟩ : D.support.Nonempty := Finsupp.support_nonempty_iff.mpr h0
    have hDP : D P ≠ 0 := Finsupp.mem_support_iff.mp hP
    have hQex : ∃ Q ∈ D.support, Q ≠ P := by
      by_contra hcon
      push Not at hcon
      have hsupp : D.support = {P} := Finset.eq_singleton_iff_unique_mem.mpr ⟨hP, hcon⟩
      have htot : tot α D = D P := by
        rw [tot_eq_sum, Finsupp.sum, hsupp, Finset.sum_singleton]
      exact hDP (htot ▸ hsum)
    obtain ⟨Q, hQ, hQP⟩ := hQex
    set E : α →₀ ℤ := D P • (Finsupp.single P (1 : ℤ) - Finsupp.single Q 1) with hE
    set D' : α →₀ ℤ := D - E with hD'
    have hEv : ∀ v, E v = D P * (Finsupp.single P (1 : ℤ) v - Finsupp.single Q 1 v) := by
      intro v; simp [hE, Finsupp.smul_apply]
    have hD'P : D' P = 0 := by
      rw [hD', Finsupp.sub_apply, hEv, Finsupp.single_eq_same, Finsupp.single_eq_of_ne hQP.symm]; ring
    have hsupp' : D'.support ⊆ D.support.erase P := by
      intro v hv
      rw [Finset.mem_erase]
      refine ⟨?_, ?_⟩
      · rintro rfl; exact (Finsupp.mem_support_iff.mp hv) hD'P
      · by_contra hvD
        have hv0 : D v = 0 := Finsupp.notMem_support_iff.mp hvD
        have hvP : v ≠ P := fun h => hvD (h ▸ hP)
        have hvQ : v ≠ Q := fun h => hvD (h ▸ hQ)
        apply Finsupp.mem_support_iff.mp hv
        rw [hD', Finsupp.sub_apply, hEv, hv0, Finsupp.single_eq_of_ne hvP, Finsupp.single_eq_of_ne hvQ]; ring
    have hcard : D'.support.card ≤ N := by
      have h1 := Finset.card_le_card hsupp'
      have h2 := Finset.card_erase_lt_of_mem hP
      omega
    have hsum' : tot α D' = 0 := by
      rw [hD', map_sub, hsum, hE, map_zsmul, map_sub, tot_single, tot_single]; simp
    obtain ⟨l', hl'S, hl'⟩ := ih D' hcard (hsupp'.trans ((Finset.erase_subset _ _).trans hS)) hsum'
    refine ⟨(P, Q, D P) :: l', ?_, ?_⟩
    · intro t ht
      rcases List.mem_cons.mp ht with rfl | ht
      · exact ⟨hS hP, hS hQ⟩
      · exact hl'S t ht
    · rw [List.map_cons, List.sum_cons, ← hl', hD', hE]; abel

theorem not_mem_range_of_forall_not_mem_range_fst {X C₁ C₂ T : Scheme.{u}} (i₁ : C₁ ⟶ X) (i₂ : C₂ ⟶ X) (c : T ⟶ C₁)
    (h : ∀ t, c.base t ∉ Set.range (pullback.fst i₁ i₂).base) (t : T) : (c ≫ i₁).base t ∉ Set.range i₂.base := by
  rintro ⟨w, hw⟩
  apply h t
  rw [Scheme.Pullback.range_fst]
  refine ⟨w, ?_⟩
  rw [Scheme.Hom.comp_base, TopCat.comp_app] at hw
  exact hw

theorem degree_eq_tot {K F : Type} [Field K] [Field F] [Algebra K F] (h1 : ∀ v : AlgebraicCurve.Place K F, v.deg = 1)
    (D : AlgebraicCurve.Divisor K F) : AlgebraicCurve.Divisor.degree D = tot _ D := by
  have : (AlgebraicCurve.Divisor.degree (K := K) (F := F)) = tot (AlgebraicCurve.Place K F) := by
    apply Finsupp.addHom_ext
    intro v n
    rw [AlgebraicCurve.Divisor.degree_single, tot_single, h1 v]; simp
  rw [this]

end VR2Kit

end

set_option maxHeartbeats 16000000 in
set_option synthInstance.maxHeartbeats 1600000 in
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

    (k : Type) [Field k] [IsAlgClosed k] [CharP k p] [Algebra A k]
    (C₁ C₂ : Scheme.{0}) (c₁ : C₁ ⟶ Spec (CommRingCat.of k)) (c₂ : C₂ ⟶ Spec (CommRingCat.of k))
    [IsProper c₁] [SmoothOfRelativeDimension 1 c₁] [GeometricallyIntegral c₁]
    [IsProper c₂] [SmoothOfRelativeDimension 1 c₂] [GeometricallyIntegral c₂]
    (i₁ : SchemeHomOver c₁ (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) k)) (i₂ : SchemeHomOver c₂ (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) k))
    [IsClosedImmersion i₁.1] [IsClosedImmersion i₂.1]
    (hcover : ∀ z : ↥(pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)), z ∈ Set.range i₁.1.base ∨ z ∈ Set.range i₂.1.base)
    (hred : IsReduced (pullback i₁.1 i₂.1)) (n : ℕ) (hn : Nat.card ↥(pullback i₁.1 i₂.1) = n) (hn0 : 0 < n)

    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of A))) (ModularCurve.TwoChart.modelTo A (↥K) j))
    (ε₁ : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c₁) (ε₂ : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c₂)
    (hε₁ : ε₁.1 ≫ i₁.1 = (sectionBaseChange k ε).1)

    (D : RelativePic0Designation A (ModularCurve.TwoChart.modelTo A (↥K) j))
    (hrep : Nonempty (RepresentsRelSubPic (ModularCurve.TwoChart.modelTo A (↥K) j) ε (algEquivZeroCut (ModularCurve.TwoChart.modelTo A (↥K) j) ε) D))
    (hsm : Smooth D.toBase) (hsep : IsSeparated D.toBase)

    (hreps : RepresentsRelSubPic (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) k) (sectionBaseChange k ε)
      (algEquivZeroCut (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) k) (sectionBaseChange k ε)) (D.baseChange k))
    (hPk : Nonempty (hreps.poincare.L ≅ (BaseChange.ofR (ModularCurve.TwoChart.modelTo A (↥K) j) ε k
      (hrep.some.poincare.pullbackAlong ⟨pullback.fst D.toBase (specMap A k), pullback.condition⟩)).L))
    (D₁ : RelativePic0Designation k c₁) (hrep₁ : Nonempty (RepresentsRelSubPic c₁ ε₁ (algEquivZeroCut c₁ ε₁) D₁))
    (D₂ : RelativePic0Designation k c₂) (hrep₂ : Nonempty (RepresentsRelSubPic c₂ ε₂ (algEquivZeroCut c₂ ε₂) D₂))

    (ν₂ : SchemeHomOver (D.baseChange k).toBase D₂.toBase)
    (hν₂ : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (a : SchemeHomOver t (D.baseChange k).toBase),
        Nonempty ((hrep₂.some.poincare.pullbackAlong (NeronModelInfra.schemeHomOverComp a ν₂)).L ≅
          Scheme.Modules.rigidify (rigSection c₂ t ε₂) (pullback.snd c₂ t)
            ((Scheme.Modules.pullback (curveChange i₂.1 i₂.2 t)).obj (hreps.poincare.pullbackAlong a).L)))

    [IsProper (ModularCurve.TwoChart.modelTo A (↥K) j)]

    [Algebra A (AlgebraicClosure ℚ)] [Algebra L (AlgebraicClosure ℚ)] [IsScalarTower A L (AlgebraicClosure ℚ)]

    (Mη : CurveModel (AlgebraicClosure ℚ) (ModularCurve.x1FunctionFieldBar (M * p)))
    (eη : Mη.C ⟶ pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ))) [IsIso eη]
    (heη : eη ≫ pullback.snd (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ)) = Mη.toBase)

    (G : ModularCurve.JOneP.NeronSpecialFibreGeom p)
    (pts : G.J0s ≃ SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) (D.baseChange k).toBase)
    (ptsI : G.JI ≃ SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) D₁.toBase)
    (ptsE : G.JE ≃ SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) D₂.toBase)
    (hadd : ∀ a b : G.J0s, Nonempty
      ((hreps.poincare.pullbackAlong (pts (a + b))).L ≅
        (hreps.poincare.pullbackAlong (pts a)).L ⊗ (hreps.poincare.pullbackAlong (pts b)).L))
    (haddI : ∀ a b : G.JI, Nonempty
      ((hrep₁.some.poincare.pullbackAlong (ptsI (a + b))).L ≅
        (hrep₁.some.poincare.pullbackAlong (ptsI a)).L ⊗ (hrep₁.some.poincare.pullbackAlong (ptsI b)).L))
    (haddE : ∀ a b : G.JE, Nonempty
      ((hrep₂.some.poincare.pullbackAlong (ptsE (a + b))).L ≅
        (hrep₂.some.poincare.pullbackAlong (ptsE a)).L ⊗ (hrep₂.some.poincare.pullbackAlong (ptsE b)).L))
    (hproj : ∀ x : G.J0s,
      ptsI (G.proj x).1 =
        postComp (RepresentsRelSubPic.pullbackHom i₁.1 i₁.2 hε₁ hreps hrep₁.some) (pts x) ∧
      ptsE (G.proj x).2 = postComp ν₂ (pts x))

    (gpts : ModularCurve.JOne (M * p) ≃ SchemeHomOver (specMap A (AlgebraicClosure ℚ)) D.toBase)
    (hgadd : ∀ x y : ModularCurve.JOne (M * p), gpts (x + y) =
      (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hrep.some).mul _ (gpts x) (gpts y))

    (hDL : RepresentsRelSubPic (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) L) (sectionBaseChange L ε)
        (algEquivZeroCut (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) L) (sectionBaseChange L ε)) (D.baseChange L))
    (ajL : SchemeHomOver (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) L) (D.baseChange L).toBase)
    (kL : pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ)) ⟶ pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A L))
    (ajbar : Mη.C ⟶ D.P)
    (εbar : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Mη.C // q ≫ Mη.toBase = 𝟙 _})
    (hPL : Nonempty (hDL.poincare.L ≅ (BaseChange.ofR (ModularCurve.TwoChart.modelTo A (↥K) j) ε L
      (hrep.some.poincare.pullbackAlong ⟨pullback.fst D.toBase (specMap A L), pullback.condition⟩)).L))
    (hajLε : (sectionBaseChange L ε).1 ≫ ajL.1 = (D.baseChange L).zeroSection)
    (hajL : (∀ (K' : Type) [Field K'] (t : Spec (CommRingCat.of K') ⟶ Spec (CommRingCat.of L))
        (x : SchemeHomOver t (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) L)),
      Nonempty ((hDL.poincare.pullbackAlong
          ⟨x.1 ≫ ajL.1, (Category.assoc _ _ _).trans ((congrArg (x.1 ≫ ·) ajL.2).trans x.2)⟩).L ≅
        (RelEffCartierDiv.ofPoint (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) L) x.1 x.2).lineBundle ⊗
          (RelEffCartierDiv.ofPoint (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) L) (t ≫ (sectionBaseChange L ε).1)
            ((Category.assoc _ _ _).trans ((congrArg (t ≫ ·) (sectionBaseChange L ε).2).trans
              (Category.comp_id t)))).idealModule)))
    (hkL₁ : kL ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A L) = pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ)))
    (hkL₂ : kL ≫ pullback.snd (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A L) = pullback.snd (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ)) ≫ specMap L (AlgebraicClosure ℚ))
    (hajbar : ajbar = eη ≫ kL ≫ ajL.1 ≫ pullback.fst D.toBase (specMap A L))
    (hajbar_over : ajbar ≫ D.toBase = Mη.toBase ≫ specMap A (AlgebraicClosure ℚ))
    (hεbar : εbar.1 ≫ eη ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ)) = specMap A (AlgebraicClosure ℚ) ≫ ε.1)
    (hεbar_aj : εbar.1 ≫ ajbar = specMap A (AlgebraicClosure ℚ) ≫ D.zeroSection)
    (hpts_aj : (∀ (x s : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Mη.C // q ≫ Mη.toBase = 𝟙 _}),
      s.1 ≫ eη ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ)) = specMap A (AlgebraicClosure ℚ) ≫ ε.1 →
      ∃ Dv : Divisor.degZero (K := AlgebraicClosure ℚ) (F := ModularCurve.x1FunctionFieldBar (M * p)),
        (Dv : Divisor (AlgebraicClosure ℚ) (ModularCurve.x1FunctionFieldBar (M * p))) =
          Finsupp.single (Mη.pointEquivPlace x) 1 - Finsupp.single (Mη.pointEquivPlace s) 1 ∧
        (gpts (Pic0.mk Dv)).1 = x.1 ≫ ajbar))

    (w : ModularCurve.IntegralWeightOneForm k M)
    (Mdl₁ : AlgebraicCurve.CurveModel k ↥(ModularCurve.igusaFunctionFieldX1C k M w)) (e₁ : Mdl₁.C ≅ C₁)
    (he₁ : e₁.hom ≫ c₁ = Mdl₁.toBase)

    (θ₁ : G.JI ≃+ AlgebraicCurve.Pic0 k ↥(ModularCurve.igusaFunctionFieldX1C k M w))
    (hθpin₁ : ∀ (g : G.JI) (x : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c₁),
      Nonempty ((hrep₁.some.poincare.pullbackAlong (ptsI g)).L ≅
        (RelEffCartierDiv.ofPoint c₁ x.1 x.2).lineBundle ⊗ (RelEffCartierDiv.ofPoint c₁ ε₁.1 ε₁.2).idealModule) →
      ∃ Dv : Divisor.degZero (K := k) (F := ↥(ModularCurve.igusaFunctionFieldX1C k M w)),
        (Dv : Divisor k ↥(ModularCurve.igusaFunctionFieldX1C k M w)) =
          Finsupp.single (Mdl₁.pointEquivPlace ⟨x.1 ≫ e₁.inv, by rw [← he₁, Category.assoc, e₁.inv_hom_id_assoc]; exact x.2⟩) 1 -
            Finsupp.single (Mdl₁.pointEquivPlace ⟨ε₁.1 ≫ e₁.inv, by rw [← he₁, Category.assoc, e₁.inv_hom_id_assoc]; exact ε₁.2⟩) 1 ∧
        θ₁ g = Pic0.mk Dv)

    (Pl : ValuationSubring (AlgebraicClosure ℚ)) (hPl : Pl.LiesOverPrime p)
    (ρ : A →+* ↥Pl) (hρ : Pl.subtype.comp ρ = algebraMap A (AlgebraicClosure ℚ))
    (O : Subring (AlgebraicClosure ℚ)) (hO : O ≤ Pl.toSubring)
    (ρO : A →+* ↥O) (hρO : O.subtype.comp ρO = algebraMap A (AlgebraicClosure ℚ))
    (πk : ↥Pl →+* k) (hAlgk : algebraMap A k = πk.comp ρ)

    (hπk : Function.Surjective ⇑πk)

    (red₁ : AlgebraicCurve.Place (AlgebraicClosure ℚ) ↥(ModularCurve.x1FunctionFieldBar (M * p)) →
      AlgebraicCurve.Place k ↥(ModularCurve.igusaFunctionFieldX1C k M w))
    (hred₁ : ∀ (P : AlgebraicCurve.Place (AlgebraicClosure ℚ) ↥(ModularCurve.x1FunctionFieldBar (M * p)))
        (ξ : SchemeHomOver (Spec.map (CommRingCat.ofHom ρO)) (ModularCurve.TwoChart.modelTo A (↥K) j))
        (c : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c₁),
      Spec.map (CommRingCat.ofHom O.subtype) ≫ ξ.1 =
        (Mη.pointEquivPlace.symm P).1 ≫ eη ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ)) →
      c.1 ≫ i₁.1 ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k) =
        Spec.map (CommRingCat.ofHom (πk.comp (Subring.inclusion hO))) ≫ ξ.1 →
      red₁ P = Mdl₁.pointEquivPlace ⟨c.1 ≫ e₁.inv, by rw [← he₁, Category.assoc, e₁.inv_hom_id_assoc]; exact c.2⟩) :
    ∀ (Dv : Divisor.degZero (K := AlgebraicClosure ℚ) (F := ModularCurve.x1FunctionFieldBar (M * p))),

      (∀ P ∈ (Dv : Divisor (AlgebraicClosure ℚ) (ModularCurve.x1FunctionFieldBar (M * p))).support,
        ∃ (ξ : SchemeHomOver (Spec.map (CommRingCat.ofHom ρO)) (ModularCurve.TwoChart.modelTo A (↥K) j))
          (c : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c₁),
          Spec.map (CommRingCat.ofHom O.subtype) ≫ ξ.1 =
            (Mη.pointEquivPlace.symm P).1 ≫ eη ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ)) ∧
          c.1 ≫ i₁.1 ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k) =
            Spec.map (CommRingCat.ofHom (πk.comp (Subring.inclusion hO))) ≫ ξ.1 ∧
          ∀ t, c.1.base t ∉ Set.range (pullback.fst i₁.1 i₂.1).base) →

      ∀ (z : SchemeHomOver (Spec.map (CommRingCat.ofHom ρO)) D.toBase),
        (gpts (Pic0.mk Dv)).1 = Spec.map (CommRingCat.ofHom O.subtype) ≫ z.1 →

        ∀ (y : G.J0s),
          (pts y).1 ≫ pullback.fst D.toBase (specMap A k) =
            Spec.map (CommRingCat.ofHom (πk.comp (Subring.inclusion hO))) ≫ z.1 →
          (G.proj y).2 = 0 := by
  intro Dv hgood z hz y hy
  classical

  obtain ⟨U, hUi, hUmax⟩ := ModularCurve.XOneP.exists_smoothLocus_maximal_twoChartModel_x1_mul p M hM hpM L ζ hζ K hK A hAp hζA j hj
  haveI := hUi
  obtain ⟨hsmL, hgiL⟩ :=
    ModularCurve.XOneP.smoothOfRelativeDimension_one_and_geometricallyIntegral_baseChange_twoChartModel_x1_mul p M hM hpM L ζ hζ K hK A hAp hζA j hj
  have hinjAK : Function.Injective (algebraMap A ↥K) := by
    rw [IsScalarTower.algebraMap_eq A L ↥K]
    exact (algebraMap L ↥K).injective.comp (IsFractionRing.injective A L)
  haveI : Flat (ModularCurve.TwoChart.modelTo A (↥K) j) := AlgebraicCurve.TwoChartIntegralModel.flat_toBase A (↥K) j hinjAK
  haveI : IsCurveOver (AlgebraicClosure ℚ) ↥(ModularCurve.x1FunctionFieldBar (M * p)) := ModularCurve.isCurveOver_x1FunctionFieldBar (M * p)
  have hdeg1 : ∀ v : AlgebraicCurve.Place (AlgebraicClosure ℚ) ↥(ModularCurve.x1FunctionFieldBar (M * p)), v.deg = 1 :=
    AlgebraicCurve.IsCurveOver.deg_eq_one_of_isAlgClosed
  haveI : IsCurveOver k ↥(ModularCurve.igusaFunctionFieldX1C k M w) :=
    AlgebraicCurve.isCurveOver_of_ringEquiv_functionField_of_isIntegral_of_smoothOfRelativeDimension_one
      Mdl₁.toBase Mdl₁.ffEquiv Mdl₁.ffEquiv_algebraMap
  have hdeg1k : ∀ v : AlgebraicCurve.Place k ↥(ModularCurve.igusaFunctionFieldX1C k M w), v.deg = 1 := AlgebraicCurve.IsCurveOver.deg_eq_one_of_isAlgClosed
  have hdz : ∀ P Q : AlgebraicCurve.Place (AlgebraicClosure ℚ) ↥(ModularCurve.x1FunctionFieldBar (M * p)),
      Finsupp.single P (1 : ℤ) - Finsupp.single Q 1 ∈ Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(ModularCurve.x1FunctionFieldBar (M * p))) := by
    intro P Q
    rw [Divisor.mem_degZero, map_sub, Divisor.degree_single, Divisor.degree_single, hdeg1, hdeg1]; simp
  have hdzk : ∀ P Q : AlgebraicCurve.Place k ↥(ModularCurve.igusaFunctionFieldX1C k M w),
      Finsupp.single P (1 : ℤ) - Finsupp.single Q 1 ∈ Divisor.degZero (K := k) (F := ↥(ModularCurve.igusaFunctionFieldX1C k M w)) := by
    intro P Q
    rw [Divisor.mem_degZero, map_sub, Divisor.degree_single, Divisor.degree_single, hdeg1k, hdeg1k]; simp

  let c : ModularCurve.TwoChartModel A (↥K) j ⟶ Spec (CommRingCat.of A) := ModularCurve.TwoChart.modelTo A (↥K) j
  let hD := hrep.some
  let Lw := RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hD
  let tA : Spec (CommRingCat.of ↥Pl) ⟶ Spec (CommRingCat.of A) := Spec.map (CommRingCat.ofHom ρ)
  let rk : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of ↥Pl) := Spec.map (CommRingCat.ofHom πk)
  let tκ : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of A) := specMap A k
  have hbase : tκ = rk ≫ tA := by
    show Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← hAlgk]
  have hbase' : rk ≫ tA = 𝟙 _ ≫ tκ := by rw [Category.id_comp]; exact hbase.symm
  let tQ : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Spec (CommRingCat.of A) := specMap A (AlgebraicClosure ℚ)
  let gq : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Spec (CommRingCat.of ↥Pl) := Spec.map (CommRingCat.ofHom Pl.subtype)
  have hgq : gq ≫ tA = tQ := by
    show Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hρ]
  let jO : Spec (CommRingCat.of ↥Pl) ⟶ Spec (CommRingCat.of ↥O) := Spec.map (CommRingCat.ofHom (Subring.inclusion hO))
  have hjO : jO ≫ Spec.map (CommRingCat.ofHom ρO) = tA := by
    show Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    apply RingHom.ext
    intro a
    apply Subtype.ext
    show ((O.subtype.comp ρO) a : AlgebraicClosure ℚ) = (Pl.subtype.comp ρ) a
    rw [hρO, hρ]
  have hgqjO : gq ≫ jO = Spec.map (CommRingCat.ofHom O.subtype) := by
    show Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rfl
  have hrkjO : rk ≫ jO = Spec.map (CommRingCat.ofHom (πk.comp (Subring.inclusion hO))) := by
    show Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  let ψq : SchemeHomOver tQ tA := ⟨gq, hgq⟩

  let zPl : SchemeHomOver tA D.toBase := ⟨jO ≫ z.1, by rw [Category.assoc, z.2, hjO]⟩
  have hz' : gq ≫ zPl.1 = (gpts (Pic0.mk Dv)).1 := by
    rw [hz, ← hgqjO, Category.assoc]
  have hy' : (pts y).1 ≫ pullback.fst D.toBase (specMap A k) = rk ≫ zPl.1 := by
    rw [hy, ← hrkjO, Category.assoc]

  have hpl : ∀ P ∈ (Dv : Divisor (AlgebraicClosure ℚ) (ModularCurve.x1FunctionFieldBar (M * p))).support,
      ∃ (ξ' : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (ModularCurve.TwoChart.modelTo A (↥K) j))
        (d : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c₁),
        Set.range ξ'.1.base ⊆ (U : Set (ModularCurve.TwoChartModel A (↥K) j)) ∧
        d.1 ≫ i₁.1 ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k) = Spec.map (CommRingCat.ofHom πk) ≫ ξ'.1 ∧
        (d.1 ≫ i₁.1).base (IsLocalRing.closedPoint k) ∉ Set.range i₂.1.base ∧
        red₁ P = Mdl₁.pointEquivPlace ⟨d.1 ≫ e₁.inv, by rw [← he₁, Category.assoc, e₁.inv_hom_id_assoc]; exact d.2⟩ ∧
        gq ≫ ξ'.1 = ((Mη.pointEquivPlace.symm P).1 ≫ eη ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ))) := by
    intro P hP
    obtain ⟨ξ, d, hgen, hsp, hnode⟩ := hgood P hP
    let ξ' : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (ModularCurve.TwoChart.modelTo A (↥K) j) := ⟨jO ≫ ξ.1, by rw [Category.assoc, ξ.2, hjO]⟩
    have hsp' : d.1 ≫ i₁.1 ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k) = Spec.map (CommRingCat.ofHom πk) ≫ ξ'.1 := by
      rw [hsp, ← hrkjO, Category.assoc]
    have hoff : (d.1 ≫ i₁.1).base (IsLocalRing.closedPoint k) ∉ Set.range i₂.1.base :=
      VR2Kit.not_mem_range_of_forall_not_mem_range_fst i₁.1 i₂.1 d.1 hnode _
    refine ⟨ξ', d, ?_, hsp', hoff, hred₁ P ξ d hgen hsp, ?_⟩
    · exact ModularCurve.XOneP.range_subset_smoothLocus_of_reduction_eq_of_not_mem_range_valuationSubring_twoChartModel_x1_mul p M hM hpM L ζ hζ K hK A hAp hζA j hj k C₁ C₂ c₁ c₂ i₁ i₂ hcover hred n hn hn0 hsmL U hUmax Pl hPl ρ hρ πk hAlgk hπk ξ' d hsp' hoff
    · rw [← hgen, ← hgqjO, Category.assoc]
  haveI : Nonempty (SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (ModularCurve.TwoChart.modelTo A (↥K) j)) :=
    ⟨⟨tA ≫ ε.1, by rw [Category.assoc, ε.2, Category.comp_id]⟩⟩
  haveI : Nonempty (SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c₁) := ⟨ε₁⟩
  choose! ξf df hUf hspf hofff hredf hgenf using hpl

  have ofPoint_congr : ∀ {T : Scheme.{0}} {g : T ⟶ Spec (CommRingCat.of A)} (a a' : T ⟶ ModularCurve.TwoChartModel A (↥K) j) (h : a = a')
      (ha : a ≫ c = g) (ha' : a' ≫ c = g), RelEffCartierDiv.ofPoint c a ha = RelEffCartierDiv.ofPoint c a' ha' := by
    rintro T g a _ rfl _ _; rfl
  let supp := (Dv : Divisor (AlgebraicClosure ℚ) (ModularCurve.x1FunctionFieldBar (M * p))).support
  have pair : ∀ P ∈ supp, ∀ Q ∈ supp, ∃ s : SchemeHomOver tA D.toBase,
      gq ≫ s.1 = (gpts (Pic0.mk ⟨Finsupp.single P (1 : ℤ) - Finsupp.single Q 1, hdz P Q⟩)).1 ∧
      ∀ y' : G.J0s, (pts y').1 ≫ pullback.fst D.toBase (specMap A k) = rk ≫ s.1 →
        (G.proj y').2 = 0 := by
    intro P hP Q hQ
    obtain ⟨s, ⟨es⟩⟩ := ModularCurve.XOneP.exists_schemeHomOver_poincare_iso_ofPoint_tensor_idealModule_of_reduction_fst_valuationSubring_twoChartModel_x1_mul p M hM hpM L ζ hζ K hK A hAp hζA j hj k C₁ C₂ c₁ c₂ i₁ i₂ hcover hred n hn hn0 ε ε₁ ε₂ hε₁ D hrep hsmL hgiL U hUmax Pl hPl ρ hρ πk hAlgk hπk
      (ξf P) (ξf Q) (df P) (df Q) (hUf P hP) (hUf Q hQ) (hspf P hP) (hofff P hP) (hspf Q hQ) (hofff Q hQ)
    refine ⟨s, ?_, ?_⟩
    ·
      obtain ⟨eG⟩ := ModularCurve.XOneP.nonempty_poincare_pullbackAlong_points_pic0Mk_single_sub_single_iso_ofPoint_tensor_idealModule_twoChartModel_x1_mul p M hM hpM L ζ hζ K hK A hAp hζA j hj k C₁ C₂ c₁ c₂ i₁ i₂ hcover hred n hn hn0 ε ε₁ ε₂ hε₁ D hrep Mη eη heη gpts hgadd hDL ajL kL ajbar εbar hPL hajLε hajL hkL₁ hkL₂ hajbar hajbar_over hεbar hεbar_aj hpts_aj P Q ⟨_, hdz P Q⟩ rfl
      obtain ⟨⟨e₁⟩, -⟩ := AlgebraicGeometry.RelEffCartierDiv.nonempty_pullback_ofPoint_lineBundle_iso_and_idealModule_iso_of_range_subset
        A c U (ξf P) (hUf P hP) ψq (by rw [Category.assoc, (ξf P).2]; exact hgq)
      obtain ⟨-, ⟨e₂⟩⟩ := AlgebraicGeometry.RelEffCartierDiv.nonempty_pullback_ofPoint_lineBundle_iso_and_idealModule_iso_of_range_subset
        A c U (ξf Q) (hUf Q hQ) ψq (by rw [Category.assoc, (ξf Q).2]; exact hgq)
      have hcmp := hD.ext_of_iso tQ (postComp s ψq) (gpts (Pic0.mk ⟨Finsupp.single P (1 : ℤ) - Finsupp.single Q 1, hdz P Q⟩)) ⟨?_⟩
      · exact congrArg Subtype.val hcmp
      refine (Scheme.Modules.pullbackCongr (baseChangeSnd_comp c s ψq).symm).app _ ≪≫
        ((Scheme.Modules.pullbackComp _ _).app _).symm ≪≫
        (Scheme.Modules.pullback (baseChangeSnd c ψq)).mapIso es ≪≫
        Scheme.Modules.pullbackTensorObjIso (baseChangeSnd c ψq) _ _ ≪≫ (e₁ ⊗ᵢ e₂) ≪≫ ?_ ≪≫ eG.symm
      refine eqToIso ?_ ⊗ᵢ eqToIso ?_
      · rw [ofPoint_congr (ψq.1 ≫ (ξf P).1) _ (hgenf P hP)]
      · rw [ofPoint_congr (ψq.1 ≫ (ξf Q).1) _ (hgenf Q hQ)]
    · intro y' hy'
      exact ModularCurve.XOneP.proj_snd_eq_zero_of_points_eq_reduction_of_poincare_iso_ofPoint_valuationSubring_twoChartModel_x1_mul p M hM hpM L ζ hζ K hK A hAp hζA j hj k C₁ C₂ c₁ c₂ i₁ i₂ hcover hred n hn hn0 ε ε₁ ε₂ hε₁ D hrep hsm hsep hreps hPk D₁ hrep₁ D₂ hrep₂ ν₂ hν₂ G pts ptsI ptsE hadd haddI haddE hproj U hUmax Pl hPl ρ hρ πk hAlgk hπk
        (ξf P) (ξf Q) (df P) (df Q) (hUf P hP) (hUf Q hQ) (hspf P hP) (hofff P hP) (hspf Q hQ) (hofff Q hQ) s ⟨es⟩ y' hy'
  haveI : Nonempty (SchemeHomOver tA D.toBase) := ⟨Lw.one tA⟩
  choose! sf hsgen hsrd using pair

  have htot : VR2Kit.tot _ (Dv : Divisor (AlgebraicClosure ℚ) (ModularCurve.x1FunctionFieldBar (M * p))) = 0 := by
    rw [← VR2Kit.degree_eq_tot hdeg1]; exact Dv.2
  obtain ⟨l, hlS, hDl⟩ := VR2Kit.pairs_decomposition supp _ _ le_rfl subset_rfl htot

  let pr : (AlgebraicCurve.Place (AlgebraicClosure ℚ) ↥(ModularCurve.x1FunctionFieldBar (M * p)) × AlgebraicCurve.Place (AlgebraicClosure ℚ) ↥(ModularCurve.x1FunctionFieldBar (M * p)) × ℤ) →
      Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(ModularCurve.x1FunctionFieldBar (M * p))) :=
    fun t => ⟨Finsupp.single t.1 (1 : ℤ) - Finsupp.single t.2.1 1, hdz _ _⟩
  have hDv : Dv = (l.map fun t => t.2.2 • pr t).sum := by
    apply Subtype.ext
    rw [AddSubmonoidClass.coe_list_sum, List.map_map]
    conv_lhs => rw [hDl]
    congr 1

  letI grpA : Group (SchemeHomOver tA D.toBase) := Lw.pointGroup tA
  letI grpQ : Group (SchemeHomOver tQ D.toBase) := Lw.pointGroup tQ
  letI grpK : Group (SchemeHomOver (𝟙 _ ≫ tκ) D.toBase) := Lw.pointGroup (𝟙 _ ≫ tκ)
  let φq : SchemeHomOver tA D.toBase →* SchemeHomOver tQ D.toBase :=
    { toFun := fun s => schemeHomOverComp gq hgq s
      map_one' := Lw.one_natural tA tQ gq hgq
      map_mul' := fun a b => Lw.mul_natural tA tQ gq hgq a b }
  let φk : SchemeHomOver tA D.toBase →* SchemeHomOver (𝟙 _ ≫ tκ) D.toBase :=
    { toFun := fun s => schemeHomOverComp rk hbase' s
      map_one' := Lw.one_natural tA _ rk hbase'
      map_mul' := fun a b => Lw.mul_natural tA _ rk hbase' a b }

  have hg0 : gpts 0 = (1 : SchemeHomOver tQ D.toBase) := by
    have h := hgadd 0 0
    rw [add_zero] at h
    exact mul_eq_left.mp h.symm
  let gM : Multiplicative (ModularCurve.JOne (M * p)) →* SchemeHomOver tQ D.toBase :=
    { toFun := fun x => gpts x.toAdd
      map_one' := hg0
      map_mul' := fun a b => hgadd a.toAdd b.toAdd }
  have hgM : ∀ x, gM (Multiplicative.ofAdd x) = gpts x := fun _ => rfl

  let S : SchemeHomOver tA D.toBase := (l.map fun t => (sf t.1 t.2.1) ^ t.2.2).prod
  have key : ∀ l' : List (AlgebraicCurve.Place (AlgebraicClosure ℚ) ↥(ModularCurve.x1FunctionFieldBar (M * p)) × AlgebraicCurve.Place (AlgebraicClosure ℚ) ↥(ModularCurve.x1FunctionFieldBar (M * p)) × ℤ),
      (∀ t ∈ l', t.1 ∈ supp ∧ t.2.1 ∈ supp) →
      φq (l'.map fun t => (sf t.1 t.2.1) ^ t.2.2).prod = gpts (Pic0.mk (l'.map fun t => t.2.2 • pr t).sum) := by
    intro l' hl'
    induction l' with
    | nil => simp only [List.map_nil, List.prod_nil, List.sum_nil, map_one, Pic0.mk_zero, hg0]
    | cons t l' ih =>
      have ht := hl' t (by simp)
      rw [List.map_cons, List.prod_cons, List.map_cons, List.sum_cons, map_mul, map_zpow,
        ih (fun t' ht' => hl' t' (by simp [ht'])), Pic0.mk_add, ← hgM (_ + _), ofAdd_add, map_mul, hgM, hgM]
      congr 1
      rw [show Pic0.mk (t.2.2 • pr t) = t.2.2 • Pic0.mk (pr t) from map_zsmul (QuotientAddGroup.mk' _) _ _, ← hgM, ofAdd_zsmul,
        map_zpow, hgM]
      congr 1
      exact Subtype.ext (hsgen t.1 ht.1 t.2.1 ht.2)
  have hSq : φq S = gpts (Pic0.mk Dv) := by rw [key l hlS, ← hDv]
  haveI := hsep
  have hSz : S = zPl := by
    have h1 : gq ≫ S.1 = gq ≫ zPl.1 := by rw [hz']; exact congrArg Subtype.val hSq
    exact Subtype.ext (AlgebraicGeometry.IsSeparated.eq_of_spec_map_subtype_comp_eq D.toBase Pl S.1 zPl.1 h1 (by rw [S.2, zPl.2]))

  obtain ⟨hptsadd, hpts0⟩ :=
    ModularCurve.XOneP.pts_add_eq_relativeGroupLaw_mul_and_pts_zero_eq_one_specialFibre_twoChartModel_x1_mul p M hM hpM L ζ hζ K hK A hAp hζA j hj k C₁ C₂ c₁ c₂ i₁ i₂ hcover hred n hn hn0 ε ε₁ ε₂ hε₁ D hrep hsm hsep hreps hPk D₁ hrep₁ D₂ hrep₂ ν₂ hν₂ G pts ptsI ptsE hadd haddI haddE hproj
  have hLk := AlgebraicGeometry.RelPicard.relativeGroupLaw_baseChange_eq A c ε D hD k hreps hPk
  let Yb : Multiplicative G.J0s →* SchemeHomOver (𝟙 _ ≫ tκ) D.toBase :=
    { toFun := fun a => GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase tκ (pts a.toAdd)
      map_one' := by
        show GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase tκ (pts 0) = Lw.one _
        rw [hpts0, hLk, GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_one]
      map_mul' := fun a b => by
        show GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase tκ (pts (a.toAdd + b.toAdd)) = Lw.mul _ _ _
        rw [hptsadd, hLk, GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_mul] }
  have hYb : ∀ a : G.J0s, (Yb (Multiplicative.ofAdd a)).1 = (pts a).1 ≫ pullback.fst D.toBase (specMap A k) := fun _ => rfl
  have hYinj : Function.Injective Yb := by
    intro a b hab
    have h := congrArg Subtype.val hab
    change (pts a.toAdd).1 ≫ pullback.fst D.toBase (specMap A k) = (pts b.toAdd).1 ≫ pullback.fst D.toBase (specMap A k) at h
    have : pts a.toAdd = pts b.toAdd := by
      apply Subtype.ext
      apply pullback.hom_ext
      · exact h
      · rw [(pts a.toAdd).2, (pts b.toAdd).2]
    exact Multiplicative.toAdd.injective (pts.injective this)
  let yf : (AlgebraicCurve.Place (AlgebraicClosure ℚ) ↥(ModularCurve.x1FunctionFieldBar (M * p)) × AlgebraicCurve.Place (AlgebraicClosure ℚ) ↥(ModularCurve.x1FunctionFieldBar (M * p)) × ℤ) → G.J0s :=
    fun t => pts.symm (GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase tκ (φk (sf t.1 t.2.1)))
  have hYf : ∀ t, Yb (Multiplicative.ofAdd (yf t)) = φk (sf t.1 t.2.1) := by
    intro t
    show GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase tκ (pts (pts.symm _)) = _
    rw [Equiv.apply_symm_apply, GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_ofBase]
  have hyread : ∀ t, (pts (yf t)).1 ≫ pullback.fst D.toBase (specMap A k) = rk ≫ (sf t.1 t.2.1).1 := by
    intro t; rw [← hYb]; exact congrArg Subtype.val (hYf t)
  have hYy : Yb (Multiplicative.ofAdd y) = φk zPl := Subtype.ext hy'
  have key2 : ∀ l' : List (AlgebraicCurve.Place (AlgebraicClosure ℚ) ↥(ModularCurve.x1FunctionFieldBar (M * p)) × AlgebraicCurve.Place (AlgebraicClosure ℚ) ↥(ModularCurve.x1FunctionFieldBar (M * p)) × ℤ),
      Yb (Multiplicative.ofAdd (l'.map fun t => t.2.2 • yf t).sum) = φk (l'.map fun t => (sf t.1 t.2.1) ^ t.2.2).prod := by
    intro l'
    induction l' with
    | nil => simp only [List.map_nil, List.sum_nil, List.prod_nil, ofAdd_zero, map_one]
    | cons t l' ih =>
      rw [List.map_cons, List.sum_cons, List.map_cons, List.prod_cons, ofAdd_add, map_mul, map_mul, ih, ofAdd_zsmul, map_zpow,
        map_zpow, hYf]
  have hysum : y = (l.map fun t => t.2.2 • yf t).sum := by
    apply Multiplicative.ofAdd.injective
    apply hYinj
    rw [hYy, key2, ← hSz]

  let Θ : G.J0s →+ G.JE := (AddMonoidHom.snd G.JI G.JE).comp G.proj
  have hΘ : ∀ a, Θ a = (G.proj a).2 := fun _ => rfl
  have hΘf : ∀ t ∈ l, Θ (yf t) = 0 := by
    intro t ht
    rw [hΘ]
    exact hsrd t.1 (hlS t ht).1 t.2.1 (hlS t ht).2 (yf t) (hyread t)
  rw [← hΘ, hysum, map_list_sum, List.map_map]
  apply List.sum_eq_zero
  intro x hx
  obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hx
  simp only [Function.comp_apply, map_zsmul, hΘf t ht, smul_zero]

end S_ModularCurve_XOneP_proj_snd_eq_zero_of_points_eq_reduction_of_surjective_residue_of_forall_mem_support_exists_section_twoChartModel_x1_mul
end P2MW
export P2MW.S_ModularCurve_XOneP_proj_snd_eq_zero_of_points_eq_reduction_of_surjective_residue_of_forall_mem_support_exists_section_twoChartModel_x1_mul (solution)
