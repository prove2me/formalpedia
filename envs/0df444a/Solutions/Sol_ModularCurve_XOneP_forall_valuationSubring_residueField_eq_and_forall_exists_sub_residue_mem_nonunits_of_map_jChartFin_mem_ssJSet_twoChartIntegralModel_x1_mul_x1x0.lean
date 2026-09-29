-- Prove2me | solution 1 for ModularCurve.XOneP.forall_valuationSubring_residueField_eq_and_forall_exists_sub_residue_mem_nonunits_of_map_jChartFin_mem_ssJSet_twoChartIntegralModel_x1_mul_x1x0
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/3edafb98-6d92-5b54-bd87-0e7ee39fae45

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_IgusaFunctionFieldX1
import Theorems.Thm_ModularCurve_XOneP_exists_ringEquiv_residueField_comap_igusaFunctionFieldX1C_of_gaussPresentation
import Theorems.Thm_ModularCurve_XOneP_gaussReduction_mem_igusaFunctionFieldX1C_and_surjective_x1_mul
import Theorems.Thm_ModularCurve_XOneGammaZeroP_exists_ringEquiv_residueField_x1FunctionFieldC_of_gaussPresentation_x1x0
import Theorems.Thm_ModularCurve_exists_powerSeries_coeffEmb_jq_mul_eq_and_div_eq_jqModC_and_qExpand
import Theorems.Thm_ModularCurve_forall_valuationSubring_igusaFunctionFieldX1C_comap_eq_imp_eq_and_exists_of_mem_ssJSet
import Theorems.Thm_ModularCurve_hasseRootFn_pow_mem_and_finite_and_isSeparable_igusaFunctionFieldX1C
import Theorems.Thm_IsCyclotomicExtension_Rat_surjective_algebraMap_int_residueField_of_isDiscreteValuationRing
import Theorems.Thm_ModularCurve_nonempty_integralWeightOneForm
import Theorems.Thm_ModularCurve_XOneP_exists_gaussValuationSubring_x1_mul
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XOneP_forall_valuationSubring_residueField_eq_and_forall_exists_sub_residue_mem_nonunits_of_map_jChartFin_mem_ssJSet_twoChartIntegralModel_x1_mul_x1x0
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion CohCarrier.iotaDeg_range_finiteIndex CohCarrier.Gamma0Upper_finiteIndex TateModule.instModule TateModule.instSMul"
p2m_attr_erase "instance" "CohCarrier.HeckeData.V_isScalarTower CohCarrier.HeckeData.opSubalgebra_isMulCommutative CohCarrier.HeckeData.mTheta_isPrime ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois ModularCurve.instIsElliptic_tateBase ModularCurve.instIsElliptic_tateLaurent ModularCurve.KatzGamma0Form.instModule ModularCurve.KatzGamma0Form.instZero ModularCurve.KatzLevelPForm.instSMul ModularCurve.KatzGamma0Form.instAdd ModularCurve.KatzLevelPForm.instAddCommGroup ModularCurve.KatzGamma0Form.instNeg ModularCurve.KatzGamma0Form.instAddCommGroup ModularCurve.KatzLevelPForm.instAdd ModularCurve.KatzLevelPForm.instSub ModularCurve.KatzLevelPForm.instNeg ModularCurve.KatzGamma0Form.instSMul ModularCurve.KatzGamma0Form.instSub ModularCurve.KatzLevelPForm.instZero ModularCurve.KatzLevelPForm.instModule KatzModularForm.instAddCommGroup KatzModularForm.instSub KatzModularForm.instZero KatzModularForm.instModule KatzModularForm.instAdd KatzModularForm.instNeg KatzModularForm.instSMul WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral"
p2m_attr_erase "instance" "WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free AlgebraicCurve.CurveModel.chartRing_finitePresentation"
p2m_attr_erase "instance" "AlgebraicCurve.CurveModel.isProper AlgebraicCurve.CurveModel.isIntegral AlgebraicCurve.CurveModel.smooth CuspForm.instModuleZModIntTwoCuspForms CuspForm.instAddCommGroupIntTwoCuspForms ModularCurve.instAlgebraIntermediateFieldLaurent ModularCurve.instIsScalarTowerKaehlerIntermediateFieldLaurent ModularCurve.instIsScalarTowerIntermediateFieldLaurent ModularCurve.instModuleKaehlerIntermediateFieldLaurent CuspForm.instModuleTwoCuspForms CuspForm.instIsScalarTowerTwoCuspForms CuspForm.instAddCommGroupTwoCuspForms CuspForm.instIsScalarTowerSelfTwoCuspForms CuspForm.instModuleQuotientTwoCuspForms CuspForm.GammaH_finiteIndex"
p2m_attr_erase "simp" "ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq"
p2m_attr_erase "simp" "AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none"
p2m_attr_erase "simp" "AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule CohCarrier.conjUpperMat_apply_11 CohCarrier.conjUpperMat_apply_10 CohCarrier.mem_Gamma0Upper CohCarrier.val_gamma0Units ModularCurve.JH.torsionGaloisRep_apply TateModule.smul_apply TateModule.coe_mulP TateModule.proj_apply TateModule.coe_add TateModule.coe_sub WeierstrassCurve.tateModuleRepOfBasis_V TateModule.coe_zero TateModule.rep_apply WeierstrassCurve.tateModuleRep_V WeierstrassCurve.tateModuleRepOfBasis_ρ_apply GaloisRep.padicIntToRingLevel_apply TateModule.coe_neg WeierstrassCurve.tateModuleRep_ρ_apply ModularCurve.qExpandAlgHomC_apply CohCarrier.Gen.dia.sizeOf_spec CohCarrier.Gen.U.injEq"
p2m_attr_erase "simp" "CohCarrier.Gen.T.sizeOf_spec CohCarrier.Gen.U.sizeOf_spec CohCarrier.Gen.T.injEq CohCarrier.Gen.dia.injEq CohCarrier.HeckeData.mk.sizeOf_spec CohCarrier.HeckeData.opAlgHom_X CohCarrier.HeckeData.toMLₒ_apply CohCarrier.HeckeData.mk.injEq CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply ModularCurve.ProjectiveLine.map_mk WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_cuspidalDivisor₀ ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen"
p2m_attr_erase "simp" "ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.cuspData_yP ModularCurve.qTwistAlgHom_apply ModularCurve.cuspData_yQ ModularCurve.cuspData_xP ModularCurve.cuspData_xQ ModularCurve.val_cyclZeta ModularCurve.cuspShift_one ModularCurve.cuspShift_zero ModularCurve.LevelPData.mk.sizeOf_spec ModularCurve.KatzLevelPForm.neg_toFun ModularCurve.LevelP.coe_swapW ModularCurve.KatzLevelPForm.swap_swap KatzModularForm.pullbackLevelP_toFun ModularCurve.LevelPData.swap_xQ KatzModularForm.pullbackLevelP_zero ModularCurve.LevelPData.map_yP ModularCurve.KatzLevelPForm.swap_neg ModularCurve.KatzGamma0Form.toKatzLevelPForm_sub"
p2m_attr_erase "simp" "ModularCurve.KatzLevelPForm.swap_add KatzModularForm.swap_pullbackLevelP ModularCurve.KatzGamma0Form.toKatzLevelPForm_add ModularCurve.KatzLevelPForm.swap_smul ModularCurve.LevelPData.map_yQ ModularCurve.KatzLevelPForm.mk.injEq ModularCurve.KatzLevelPForm.zero_toFun KatzModularForm.pullbackLevelP_smul ModularCurve.LevelPData.swap_xP ModularCurve.KatzGamma0Form.toKatzLevelPForm_mul ModularCurve.KatzGamma0Form.toKatzLevelPForm_neg ModularCurve.LevelPData.variableChange_xQ KatzModularForm.pullbackGamma0_toKatzLevelPForm ModularCurve.KatzLevelPForm.mk.sizeOf_spec ModularCurve.KatzLevelPForm.swap_zero ModularCurve.LevelP.coe_unipotentU ModularCurve.KatzLevelPForm.mul_toFun ModularCurve.LevelPData.variableChange_yP ModularCurve.LevelPData.mk.injEq ModularCurve.KatzLevelPForm.sub_toFun ModularCurve.LevelPData.variableChange_xP ModularCurve.KatzLevelPForm.smul_toFun ModularCurve.LevelPData.swap_yP ModularCurve.LevelPData.map_xP ModularCurve.LevelPData.swap_swap ModularCurve.LevelPData.swap_yQ ModularCurve.KatzGamma0Form.toKatzLevelPForm_zero ModularCurve.KatzGamma0Form.mk.injEq ModularCurve.KatzLevelPForm.swap_toFun KatzModularForm.pullbackLevelP_add ModularCurve.KatzGamma0Form.mk.sizeOf_spec ModularCurve.LevelPData.variableChange_yQ ModularCurve.KatzLevelPForm.swap_sub ModularCurve.KatzGamma0Form.toKatzLevelPForm_smul ModularCurve.LevelPData.map_xQ ModularCurve.KatzLevelPForm.add_toFun KatzModularForm.c₆_toFun KatzModularForm.neg_toFun KatzModularForm.mul_toFun KatzModularForm.qExpansion_neg"
p2m_attr_erase "simp" "KatzModularForm.discr_toFun KatzModularForm.qExpansion_sub KatzModularForm.qExpansion_add KatzModularForm.qExpansion_mul KatzModularForm.zero_toFun KatzModularForm.mk.injEq KatzModularForm.qExpansion_smul KatzModularForm.smul_toFun KatzModularForm.add_toFun KatzModularForm.sub_toFun KatzModularForm.c₄_toFun KatzModularForm.qExpansion_zero KatzModularForm.mk.sizeOf_spec TateCurve.tateTorsionPoint_zero_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄"
p2m_attr_erase "simp" "TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero"
p2m_attr_erase "simp" "WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm"
p2m_attr_erase "simp" "AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff HahnSeries.ramScale_apply AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring ModularCurve.LevelN.coe_jGen ModularCurve.CharPReduction.coeffRed_coeff ModularCurve.CharPReduction.redLocHom_apply ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar ModularCurve.ComplexPlaceDictionaryOf.pt_ofGamma0 ModularCurve.ComplexPlaceDictionaryOf.mk.injEq ModularCurve.ComplexPlaceDictionaryOf.pt_toGamma0 ModularCurve.ComplexPlaceDictionaryOf.mk.sizeOf_spec ModularCurve.ComplexPlaceDictionary.mk.injEq"
p2m_attr_erase "simp" "ModularCurve.ComplexPlaceDictionary.mk.sizeOf_spec AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces RegularLocalRingQuotientAscent.dualNumberFst_apply AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq AlgebraicCurve.CurveModel.mk.injEq AlgebraicCurve.CurveModel.mk.sizeOf_spec ModularCurve.coe_heckeBetaModLHOf ModularCurve.pairDiagModL_apply ModularCurve.coe_heckeAlphaModLH ModularCurve.pairUpModL_apply ModularCurve.coeff_qDecimate ModularCurve.coe_qExpFrobeniusModL ModularCurve.coe_qExpFrobeniusDegZeroPullbackModL ModularCurve.coe_qExpFrobeniusDegZeroPushforwardModL ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL ModularCurve.qEulerFun_coeff ModularCurve.diffQExp_D ModularCurve.qEulerOn_apply ModularCurve.qEuler_coeff AlgebraicCurve.gluedPolarDifferentials.coe_fst_apply AlgebraicCurve.gluedPolarDifferentials.coe_snd_apply AlgebraicCurve.GluedPic0.toPic0Pair_mk AlgebraicCurve.GluedPic0.toPic0Pair_nodeUnit CuspForm.heckeGenH_T CuspForm.coe_twoCuspEnd_apply"
p2m_attr_erase "simp" "CuspForm.twoCuspEndMod_reduce CuspForm.heckeGenH_U CuspForm.heckeGenH_dia ModularForm.AtkinLehnerDatum.mk.injEq ModularForm.AtkinLehnerDatum.alGL_coe ModularForm.AtkinLehnerDatum.mk.sizeOf_spec ModularForm.AtkinLehnerDatum.sqUnitSL_coe ModularForm.AtkinLehnerDatum.det_sqUnit ModularForm.AtkinLehnerDatum.det_mat ModularCurve.baseAut_x1ArithFrobC_apply ModularCurve.coe_qExpCoeffRingAut_apply ModularCurve.qExpCoeffSemilinearAutHom_apply ModularCurve.baseAut_x1x0ArithFrobC_apply ModularCurve.baseAut_qExpArithFrobC_apply ModularCurve.baseAut_qExpCoeffSemilinearAut ModularCurve.toRingAut_qExpCoeffSemilinearAut ModularForm.coe_atkinLehnerLin_apply CuspForm.coe_atkinLehnerLin_apply AlgebraicCurve.Pic.baseChange_mk AlgebraicCurve.Place.forgetConstants_toValuationSubring AlgebraicCurve.Place.constantFieldEquiv_symm_apply AlgebraicCurve.Place.ord_forgetConstants AlgebraicCurve.Place.extendConstants_toValuationSubring AlgebraicCurve.Place.constantFieldEquiv_apply_toValuationSubring AlgebraicCurve.Place.mem_fiberConstants AlgebraicCurve.Place.restrictConstants_toValuationSubring"

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry AlgebraicCurve.TwoChartIntegralModel

namespace SheetTotram

section Generic

variable {E : Type*} [Field E]

theorem mem_nonunits_comap_iff {E' : Type*} [Field E'] (P : ValuationSubring E) (g : E' →+* E) (x : E') :
    x ∈ (P.comap g).nonunits ↔ g x ∈ P.nonunits := by
  have h1 : x ∈ (P.comap g).nonunits ↔ x⁻¹ = 0 ∨ x⁻¹ ∉ P.comap g := by
    rw [← ValuationSubring.inv_mem_nonunits_iff, inv_inv]
  have h2 : g x ∈ P.nonunits ↔ (g x)⁻¹ = 0 ∨ (g x)⁻¹ ∉ P := by
    rw [← ValuationSubring.inv_mem_nonunits_iff, inv_inv]
  rw [h1, h2, ValuationSubring.mem_comap, map_inv₀, inv_eq_zero, inv_eq_zero, map_eq_zero_iff g g.injective]

theorem comap_comap_symm {E' : Type*} [Field E'] (P : ValuationSubring E) (e : E ≃+* E') :
    (P.comap e.symm.toRingHom).comap e.toRingHom = P := by
  ext x
  simp [ValuationSubring.mem_comap]

theorem comap_ne_top_of_isAlgebraic {F' E' : Type*} [Field F'] [Field E'] [Algebra F' E']
    [Algebra.IsAlgebraic F' E'] (Q : ValuationSubring E') (hQ : Q ≠ ⊤) :
    Q.comap (algebraMap F' E') ≠ ⊤ := by
  classical
  intro hO
  have hallF : ∀ c : F', algebraMap F' E' c ∈ Q := fun c => by
    have : c ∈ Q.comap (algebraMap F' E') := by rw [hO]; trivial
    exact this

  obtain ⟨e, heQ⟩ : ∃ e : E', e ∉ Q := by
    by_contra h
    push Not at h
    exact hQ (eq_top_iff.mpr fun x _ => h x)
  have he0 : e ≠ 0 := fun h => heQ (h ▸ Q.zero_mem)
  have heinv : e⁻¹ ∈ Q.nonunits := Q.inv_mem_nonunits_iff.mpr (Or.inr heQ)
  obtain ⟨heinvQ, hm⟩ := ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal.mp heinv

  obtain ⟨f, hf0, hfe⟩ := (Algebra.IsAlgebraic.isAlgebraic (R := F') e)
  have hlc : f.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hf0

  have key : (1 : E') = - ∑ i ∈ Finset.range f.natDegree,
      algebraMap F' E' (f.coeff i / f.leadingCoeff) * (e⁻¹) ^ (f.natDegree - i) := by
    have h1 : Polynomial.aeval e f = ∑ i ∈ Finset.range (f.natDegree + 1), algebraMap F' E' (f.coeff i) * e ^ i := by
      rw [Polynomial.aeval_eq_sum_range]
      simp only [Algebra.smul_def]
    rw [hfe, Finset.sum_range_succ] at h1

    have hcn : algebraMap F' E' f.leadingCoeff ≠ 0 := by
      simpa using (map_ne_zero_iff _ (algebraMap F' E').injective).mpr hlc
    have h2 : algebraMap F' E' (f.coeff f.natDegree) * e ^ f.natDegree =
        - ∑ i ∈ Finset.range f.natDegree, algebraMap F' E' (f.coeff i) * e ^ i := by
      linear_combination h1.symm
    have h3 : (1 : E') = (algebraMap F' E' f.leadingCoeff)⁻¹ * (e ^ f.natDegree)⁻¹ *
        (algebraMap F' E' (f.coeff f.natDegree) * e ^ f.natDegree) := by
      rw [Polynomial.coeff_natDegree]
      field_simp
    rw [h3, h2, mul_neg, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mem_range] at hi
    rw [map_div₀]
    have : (e⁻¹) ^ (f.natDegree - i) = (e ^ f.natDegree)⁻¹ * e ^ i := by
      rw [inv_pow, pow_sub₀ _ he0 hi.le, mul_inv, inv_inv]
    rw [this]
    ring

  have hmem : ∀ i ∈ Finset.range f.natDegree,
      algebraMap F' E' (f.coeff i / f.leadingCoeff) * (e⁻¹) ^ (f.natDegree - i) ∈ Q.nonunits := by
    intro i hi
    rw [Finset.mem_range] at hi
    rw [ValuationSubring.mem_nonunits_iff]
    have hv1 : Q.valuation (algebraMap F' E' (f.coeff i / f.leadingCoeff)) ≤ 1 :=
      (Q.valuation_le_one_iff _).mpr (hallF _)
    have hv2 : Q.valuation (e⁻¹) < 1 := (Q.mem_nonunits_iff).mp heinv
    rw [map_mul, map_pow]
    calc Q.valuation (algebraMap F' E' (f.coeff i / f.leadingCoeff)) * Q.valuation e⁻¹ ^ (f.natDegree - i)
        ≤ 1 * Q.valuation e⁻¹ ^ (f.natDegree - i) := by gcongr
      _ < 1 := by
        rw [one_mul]
        exact pow_lt_one₀ zero_le' hv2 (Nat.sub_ne_zero_of_lt hi)
  have hsum : (∑ i ∈ Finset.range f.natDegree,
      algebraMap F' E' (f.coeff i / f.leadingCoeff) * (e⁻¹) ^ (f.natDegree - i)) ∈ Q.nonunits := by
    rw [ValuationSubring.mem_nonunits_iff]
    apply Q.valuation.map_sum_lt one_ne_zero
    intro i hi
    exact (Q.mem_nonunits_iff).mp (hmem i hi)
  have h1Q : (1 : E') ∈ Q.nonunits := by
    rw [key, ValuationSubring.mem_nonunits_iff, Valuation.map_neg]
    exact (Q.mem_nonunits_iff).mp hsum
  rw [ValuationSubring.mem_nonunits_iff, map_one] at h1Q
  exact lt_irrefl _ h1Q

theorem exists_ringHom_extend_of_isAlgebraic {F' E' Ω : Type*} [Field F'] [Field E'] [Algebra F' E']
    [Algebra.IsAlgebraic F' E'] [Field Ω] [IsAlgClosed Ω] (Q : ValuationSubring E')
    (φ₀ : ↥(Q.comap (algebraMap F' E')) →+* Ω)
    (hφ₀ : RingHom.ker φ₀ = IsLocalRing.maximalIdeal ↥(Q.comap (algebraMap F' E'))) :
    ∃ φ : ↥Q →+* Ω, RingHom.ker φ = IsLocalRing.maximalIdeal ↥Q ∧
      ∀ f : ↥(Q.comap (algebraMap F' E')), φ ⟨algebraMap F' E' f, f.2⟩ = φ₀ f := by
  classical
  let incO : ↥(Q.comap (algebraMap F' E')) →+* ↥Q :=
    { toFun := fun f => ⟨algebraMap F' E' f, f.2⟩
      map_one' := Subtype.ext (map_one _)
      map_mul' := fun a b => Subtype.ext (map_mul _ _ _)
      map_zero' := Subtype.ext (map_zero _)
      map_add' := fun a b => Subtype.ext (map_add _ _ _) }
  have hincO : ∀ f : ↥(Q.comap (algebraMap F' E')), ((incO f : ↥Q) : E') = algebraMap F' E' f := fun f => rfl
  haveI hloc : IsLocalHom incO := by
    refine ⟨fun f hf => ?_⟩
    by_contra hnu
    have hfm : f ∈ IsLocalRing.maximalIdeal ↥(Q.comap (algebraMap F' E')) := (IsLocalRing.mem_maximalIdeal _).mpr hnu
    have h1 : ((f : ↥(Q.comap (algebraMap F' E'))) : F') ∈ (Q.comap (algebraMap F' E')).nonunits := ValuationSubring.coe_mem_nonunits_iff.mpr hfm
    have h2 : algebraMap F' E' f ∈ Q.nonunits := (mem_nonunits_comap_iff Q (algebraMap F' E') f).mp h1
    have h3 : (incO f) ∈ IsLocalRing.maximalIdeal ↥Q := ValuationSubring.coe_mem_nonunits_iff.mp h2
    exact (IsLocalRing.mem_maximalIdeal _).mp h3 hf
  let ιres : IsLocalRing.ResidueField ↥(Q.comap (algebraMap F' E')) →+* IsLocalRing.ResidueField ↥Q := IsLocalRing.ResidueField.map incO
  letI : Algebra (IsLocalRing.ResidueField ↥(Q.comap (algebraMap F' E'))) (IsLocalRing.ResidueField ↥Q) := ιres.toAlgebra
  have halgmap : ∀ x, algebraMap (IsLocalRing.ResidueField ↥(Q.comap (algebraMap F' E'))) (IsLocalRing.ResidueField ↥Q) x = ιres x := fun x => rfl

  haveI halg : Algebra.IsAlgebraic (IsLocalRing.ResidueField ↥(Q.comap (algebraMap F' E'))) (IsLocalRing.ResidueField ↥Q) := by
    constructor
    intro qbar
    obtain ⟨q, rfl⟩ := IsLocalRing.residue_surjective qbar
    obtain ⟨f, hf0, hfq⟩ := Algebra.IsAlgebraic.isAlgebraic (R := F') (q : E')
    have hsupp : f.support.Nonempty := Polynomial.support_nonempty.mpr hf0
    obtain ⟨i₀, hi₀, hmax⟩ := Finset.exists_max_image f.support
      (fun i => Q.valuation (algebraMap F' E' (f.coeff i))) hsupp
    have hc0 : f.coeff i₀ ≠ 0 := Polynomial.mem_support_iff.mp hi₀
    have hc0' : algebraMap F' E' (f.coeff i₀) ≠ 0 := by
      simpa using (map_ne_zero_iff _ (algebraMap F' E').injective).mpr hc0
    have hd : ∀ i, f.coeff i / f.coeff i₀ ∈ Q.comap (algebraMap F' E') := by
      intro i
      change algebraMap F' E' (f.coeff i / f.coeff i₀) ∈ Q
      rw [← Q.valuation_le_one_iff, map_div₀, map_div₀]
      by_cases hi : i ∈ f.support
      · rw [div_le_one₀ ((Valuation.pos_iff _).mpr hc0')]
        exact hmax i hi
      · rw [Polynomial.notMem_support_iff.mp hi, map_zero, map_zero, zero_div]
        exact zero_le'
    let d : ℕ → ↥(Q.comap (algebraMap F' E')) := fun i => ⟨f.coeff i / f.coeff i₀, hd i⟩
    have hd₀ : d i₀ = 1 := Subtype.ext (div_self hc0)
    let g : Polynomial (IsLocalRing.ResidueField ↥(Q.comap (algebraMap F' E'))) :=
      ∑ i ∈ f.support, Polynomial.C (IsLocalRing.residue ↥(Q.comap (algebraMap F' E')) (d i)) * Polynomial.X ^ i
    have hgcoeff : g.coeff i₀ = 1 := by
      simp only [g, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, mul_ite, mul_one,
        mul_zero]
      rw [Finset.sum_ite_eq, if_pos hi₀, hd₀, map_one]
    have hg0 : g ≠ 0 := fun h => by
      have := congrArg (fun r : Polynomial _ => r.coeff i₀) h
      simp only [hgcoeff, Polynomial.coeff_zero] at this
      exact one_ne_zero this
    refine ⟨g, hg0, ?_⟩
    have hrel : (∑ i ∈ f.support, incO (d i) * q ^ i : ↥Q) = 0 := by
      apply Subtype.ext
      push_cast
      simp only [hincO]
      have hf' := congrArg (Polynomial.aeval (q : E')) (Polynomial.as_sum_support_C_mul_X_pow f)
      rw [hfq, map_sum] at hf'
      simp only [map_mul, map_pow, Polynomial.aeval_C, Polynomial.aeval_X] at hf'
      have : ∑ i ∈ f.support, algebraMap F' E' (f.coeff i / f.coeff i₀) * (q : E') ^ i =
          (algebraMap F' E' (f.coeff i₀))⁻¹ * ∑ i ∈ f.support, algebraMap F' E' (f.coeff i) * (q : E') ^ i := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        rw [map_div₀]
        field_simp
      change ∑ i ∈ f.support, algebraMap F' E' (f.coeff i / f.coeff i₀) * (q : E') ^ i = 0
      rw [this, ← hf', mul_zero]
    calc Polynomial.aeval (IsLocalRing.residue ↥Q q) g
        = ∑ i ∈ f.support, ιres (IsLocalRing.residue ↥(Q.comap (algebraMap F' E')) (d i)) * IsLocalRing.residue ↥Q q ^ i := by
          simp only [g, map_sum, map_mul, map_pow, Polynomial.aeval_C, Polynomial.aeval_X, halgmap]
      _ = IsLocalRing.residue ↥Q (∑ i ∈ f.support, incO (d i) * q ^ i) := by
          simp only [map_sum, map_mul, map_pow, ιres, IsLocalRing.ResidueField.map_residue]
      _ = 0 := by rw [hrel, map_zero]

  haveI : IsLocalHom φ₀ := by
    refine ⟨fun a ha => ?_⟩
    by_contra hna
    have : a ∈ RingHom.ker φ₀ := by rw [hφ₀]; exact (IsLocalRing.mem_maximalIdeal _).mpr hna
    exact ha.ne_zero this
  letI : Algebra (IsLocalRing.ResidueField ↥(Q.comap (algebraMap F' E'))) Ω := (IsLocalRing.ResidueField.lift φ₀).toAlgebra
  let ψ : IsLocalRing.ResidueField ↥Q →ₐ[IsLocalRing.ResidueField ↥(Q.comap (algebraMap F' E'))] Ω := IsAlgClosed.lift
  refine ⟨ψ.toRingHom.comp (IsLocalRing.residue ↥Q), ?_, ?_⟩
  · have hψ : Function.Injective ψ.toRingHom := ψ.toRingHom.injective
    ext q
    simp only [RingHom.mem_ker, RingHom.coe_comp, Function.comp_apply]
    rw [map_eq_zero_iff ψ.toRingHom hψ, IsLocalRing.residue_eq_zero_iff]
  · intro f
    show ψ (IsLocalRing.residue ↥Q (incO f)) = φ₀ f
    rw [← IsLocalRing.ResidueField.map_residue, ← halgmap, AlgHom.commutes]
    exact IsLocalRing.ResidueField.lift_residue_apply φ₀ f

end Generic

end SheetTotram

section Modular

open ModularCurve SheetTotram

set_option maxHeartbeats 12800000 in
set_option synthInstance.maxHeartbeats 1600000 in
theorem solution
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hM : 5 ≤ M) (hpM : ¬ p ∣ M)
    (L : Type) [Field L] [CharZero L] [IsCyclotomicExtension {p} ℚ L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ p)
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p)))

    (K₁ : IntermediateField L (LaurentSeries L))
    (hK₁ : K₁ = ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ M p))
    (hle : K₁ ≤ K)
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAp : (p : A) ∈ IsLocalRing.maximalIdeal A) (hζA : ∃ z : A, algebraMap A L z = ζ)
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    [Algebra A ↥K₁] [IsScalarTower A L ↥K₁]
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j ≠ 0)]
    (j₁ : ↥K₁) (hj₁ : ((j₁ : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j₁ ≠ 0)]
    (ϖ : A) (hϖ : IsLocalRing.maximalIdeal A = Ideal.span {ϖ})

    (W₀ : ValuationSubring ↥K)
    (hW₀ : ∀ f : ↥K, f ∈ W₀ ↔ ∃ x y : PowerSeries A, y.map (IsLocalRing.residue A) ≠ 0 ∧
      (f : LaurentSeries L) * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap A L))
        = HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap A L)))

    (hSW₀ : ∀ s : ↥(chartAlgFin A (↥K) j), (s : ↥K) ∈ W₀)

    (y : ↥(XFin A (↥K) j))
    (hyϖ : algebraMap A ↥(chartAlgFin A (↥K) j) ϖ ∈ y.asIdeal)

    (hss : ∀ (Ω : Type) [Field Ω] [CharP Ω p] [IsAlgClosed Ω] [DecidableEq Ω]
      (φ : ↥(chartAlgFin A (↥K) j) →+* Ω),
      RingHom.ker φ = y.asIdeal → φ (jChartFin A (↥K) j) ∈ ModularCurve.ssJSet p Ω)

    (hy₀ : ∃ s : ↥(chartAlgFin A (↥K) j), s ∈ y.asIdeal ∧ (s : ↥K) ∉ W₀.nonunits) :

    (∀ P P' : ValuationSubring (IsLocalRing.ResidueField ↥W₀),
      (∀ s : ↥(chartAlgFin A (↥K) j), IsLocalRing.residue ↥W₀ ⟨(s : ↥K), hSW₀ s⟩ ∈ P) →
      (∀ s : ↥(chartAlgFin A (↥K) j),
        IsLocalRing.residue ↥W₀ ⟨(s : ↥K), hSW₀ s⟩ ∈ P.nonunits ↔ s ∈ y.asIdeal) →
      (∀ (u : ↥K₁) (hu : (IntermediateField.inclusion hle u : ↥K) ∈ W₀),
        IsLocalRing.residue ↥W₀ ⟨IntermediateField.inclusion hle u, hu⟩ ∈ P' ↔
          IsLocalRing.residue ↥W₀ ⟨IntermediateField.inclusion hle u, hu⟩ ∈ P) →
      P' = P) ∧

    (∀ P : ValuationSubring (IsLocalRing.ResidueField ↥W₀),
      (∀ s : ↥(chartAlgFin A (↥K) j), IsLocalRing.residue ↥W₀ ⟨(s : ↥K), hSW₀ s⟩ ∈ P) →
      (∀ s : ↥(chartAlgFin A (↥K) j),
        IsLocalRing.residue ↥W₀ ⟨(s : ↥K), hSW₀ s⟩ ∈ P.nonunits ↔ s ∈ y.asIdeal) →
      ∀ e : ↥P, ∃ (u : ↥K₁) (hu : (IntermediateField.inclusion hle u : ↥K) ∈ W₀),
        (e : IsLocalRing.ResidueField ↥W₀) - IsLocalRing.residue ↥W₀ ⟨IntermediateField.inclusion hle u, hu⟩ ∈ P.nonunits) := by
  classical
  haveI hp : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩

  have hpκ : (p : IsLocalRing.ResidueField A) = 0 := by
    rw [← map_natCast (IsLocalRing.residue A), IsLocalRing.residue_eq_zero_iff]
    exact hAp
  haveI hchar : CharP (IsLocalRing.ResidueField A) p := (CharP.charP_iff_prime_eq_zero Fact.out).mpr hpκ
  haveI hfin : Finite (IsLocalRing.ResidueField A) := by
    have hsZ := IsCyclotomicExtension.Rat.surjective_algebraMap_int_residueField_of_isDiscreteValuationRing p L A hAp
    refine Finite.of_surjective (ZMod.castHom (dvd_refl p) (IsLocalRing.ResidueField A)) ?_
    intro x
    obtain ⟨n, rfl⟩ := hsZ x
    exact ⟨(n : ZMod p), by simp⟩
  haveI : PerfectField (IsLocalRing.ResidueField A) := PerfectField.ofFinite
  obtain ⟨w⟩ := ModularCurve.nonempty_integralWeightOneForm (IsLocalRing.ResidueField A) M (by omega)

  obtain ⟨W₀', hW₀', hAW₀', -, -, hnu'⟩ :=
    ModularCurve.XOneP.exists_gaussValuationSubring_x1_mul p M hM hpM L ζ hζ K hK A hAp hζA j hj
  have hWW : W₀' = W₀ := by
    ext f
    rw [hW₀', hW₀]
  subst hWW
  have hAW₀ : ∀ a : A, algebraMap A ↥K a ∈ W₀' := hAW₀'
  have hnu := hnu'

  have hincl_coe : ∀ u : ↥K₁, ((IntermediateField.inclusion hle u : ↥K) : LaurentSeries L) = (u : LaurentSeries L) :=
    fun u => rfl
  let U₀ : ValuationSubring ↥K₁ := W₀'.comap (IntermediateField.inclusion hle).toRingHom
  have hU₀mem : ∀ u : ↥K₁, u ∈ U₀ ↔ (IntermediateField.inclusion hle u : ↥K) ∈ W₀' := fun u => Iff.rfl
  have hU₀ : ∀ f : ↥K₁, f ∈ U₀ ↔ ∃ x y : PowerSeries A, y.map (IsLocalRing.residue A) ≠ 0 ∧
      (f : LaurentSeries L) * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap A L))
        = HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap A L)) := by
    intro f
    rw [hU₀mem, hW₀]
    exact Iff.rfl
  have hinclA : ∀ a : A, IntermediateField.inclusion hle (algebraMap A ↥K₁ a) = algebraMap A ↥K a := by
    intro a
    apply Subtype.ext
    rw [IsScalarTower.algebraMap_apply A L ↥K₁, IsScalarTower.algebraMap_apply A L ↥K]
    rfl
  have hAU₀ : ∀ a : A, algebraMap A ↥K₁ a ∈ U₀ := by
    intro a
    rw [hU₀mem, hinclA]
    exact hAW₀ a
  obtain ⟨θ₁, hθ₁pres, hθ₁const⟩ :=
    ModularCurve.XOneGammaZeroP.exists_ringEquiv_residueField_x1FunctionFieldC_of_gaussPresentation_x1x0
      p M hM hpM L ζ hζ K₁ hK₁ A hAp hζA U₀ hU₀ hAU₀

  obtain ⟨hmem, hsurj⟩ :=
    ModularCurve.XOneP.gaussReduction_mem_igusaFunctionFieldX1C_and_surjective_x1_mul
      p M hM hpM L ζ hζ K hK A hAp hζA j hj w
  let Wid : ValuationSubring ↥K := W₀'.comap (AlgEquiv.refl : ↥K ≃ₐ[L] ↥K).toAlgHom.toRingHom
  have hWid : ∀ x : ↥K, x ∈ Wid ↔ x ∈ W₀' := fun x => Iff.rfl
  have hA₁ : ∀ a : A, algebraMap A ↥K a ∈ Wid := fun a => (hWid _).mpr (hAW₀ a)
  obtain ⟨θ₀, hθ₀pres, hθ₀const⟩ :=
    ModularCurve.XOneP.exists_ringEquiv_residueField_comap_igusaFunctionFieldX1C_of_gaussPresentation
      L K A W₀' hW₀ hnu hAW₀ M w hmem hsurj (AlgEquiv.refl : ↥K ≃ₐ[L] ↥K) (fun a => rfl) hA₁
  let eId : ↥W₀' ≃+* ↥Wid :=
    { toFun := fun x => ⟨x.1, (hWid x.1).mpr x.2⟩
      invFun := fun x => ⟨x.1, (hWid x.1).mp x.2⟩
      left_inv := fun x => rfl
      right_inv := fun x => rfl
      map_mul' := fun _ _ => rfl
      map_add' := fun _ _ => rfl }
  let θ : IsLocalRing.ResidueField ↥W₀' ≃+* ↥(igusaFunctionFieldX1C (IsLocalRing.ResidueField A) M w) :=
    (IsLocalRing.ResidueField.mapEquiv eId).trans θ₀
  have hθapp : ∀ f : ↥W₀', θ (IsLocalRing.residue ↥W₀' f) = θ₀ (IsLocalRing.residue ↥Wid (eId f)) := fun f => rfl
  have hθpres : ∀ (f : ↥W₀') (x y : PowerSeries A), y.map (IsLocalRing.residue A) ≠ 0 →
      ((f : ↥K) : LaurentSeries L) * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap A L))
        = HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap A L)) →
      ((θ (IsLocalRing.residue ↥W₀' f) : ↥(igusaFunctionFieldX1C (IsLocalRing.ResidueField A) M w)) :
          LaurentSeries (IsLocalRing.ResidueField A))
        = HahnSeries.ofPowerSeries ℤ (IsLocalRing.ResidueField A) (x.map (IsLocalRing.residue A)) /
          HahnSeries.ofPowerSeries ℤ (IsLocalRing.ResidueField A) (y.map (IsLocalRing.residue A)) := by
    intro f x y hy hxy
    rw [hθapp]
    exact hθ₀pres (eId f) x y hy (by first | simpa using hxy | exact hxy | (simpa [eId] using hxy))
  have hθconst : ∀ a : A, θ (IsLocalRing.residue ↥W₀' ⟨algebraMap A ↥K a, hAW₀ a⟩) =
      algebraMap (IsLocalRing.ResidueField A) ↥(igusaFunctionFieldX1C (IsLocalRing.ResidueField A) M w)
        (IsLocalRing.residue A a) := by
    intro a
    rw [hθapp]
    exact hθ₀const a

  let ιIg := IntermediateField.inclusion
    (ModularCurve.x1FunctionFieldC_le_igusaFunctionFieldX1C (IsLocalRing.ResidueField A) M w)
  have hθincl : ∀ (u : ↥K₁) (hu : (IntermediateField.inclusion hle u : ↥K) ∈ W₀'),
      θ (IsLocalRing.residue ↥W₀' ⟨IntermediateField.inclusion hle u, hu⟩) =
        ιIg (θ₁ (IsLocalRing.residue ↥U₀ ⟨u, (hU₀mem u).mpr hu⟩)) := by
    intro u hu
    obtain ⟨x, y, hy, hxy⟩ := (hU₀ u).mp ((hU₀mem u).mpr hu)
    have h1 := hθpres ⟨IntermediateField.inclusion hle u, hu⟩ x y hy hxy
    have h2 := hθ₁pres ⟨u, (hU₀mem u).mpr hu⟩ x y hy hxy
    apply Subtype.ext
    rw [h1, IntermediateField.coe_inclusion, h2]
  have hFsurj : ∀ z : ↥(x1FunctionFieldC (IsLocalRing.ResidueField A) M),
      ∃ (u : ↥K₁) (hu : (IntermediateField.inclusion hle u : ↥K) ∈ W₀'),
        θ₁ (IsLocalRing.residue ↥U₀ ⟨u, (hU₀mem u).mpr hu⟩) = z := by
    intro z
    obtain ⟨e, rfl⟩ := θ₁.surjective z
    obtain ⟨u', rfl⟩ := IsLocalRing.residue_surjective e
    exact ⟨u'.1, (hU₀mem _).mp u'.2, rfl⟩

  obtain ⟨⟨xj, yj, hyj, hjpres, hjred⟩, -⟩ :=
    ModularCurve.exists_powerSeries_coeffEmb_jq_mul_eq_and_div_eq_jqModC_and_qExpand p L A hAp
  have hj₁pres : ((j₁ : ↥K₁) : LaurentSeries L) * HahnSeries.ofPowerSeries ℤ L (yj.map (algebraMap A L))
      = HahnSeries.ofPowerSeries ℤ L (xj.map (algebraMap A L)) := by
    rw [hj₁]; exact hjpres
  have hj₁U : j₁ ∈ U₀ := (hU₀ j₁).mpr ⟨xj, yj, hyj, hj₁pres⟩
  have hj₁W : (IntermediateField.inclusion hle j₁ : ↥K) ∈ W₀' := (hU₀mem j₁).mp hj₁U
  let jbar : ↥(x1FunctionFieldC (IsLocalRing.ResidueField A) M) :=
    θ₁ (IsLocalRing.residue ↥U₀ ⟨j₁, hj₁U⟩)
  have hjbar : (jbar : LaurentSeries (IsLocalRing.ResidueField A)) = jqModC (IsLocalRing.ResidueField A) := by
    have := hθ₁pres ⟨j₁, hj₁U⟩ xj yj hyj hj₁pres
    rw [hjred] at this
    exact this
  have hinclj : (IntermediateField.inclusion hle j₁ : ↥K) = j :=
    Subtype.ext (by rw [IntermediateField.coe_inclusion, hj₁, hj])
  have hWj : (⟨(jChartFin A (↥K) j : ↥K), hSW₀ _⟩ : ↥W₀') = ⟨IntermediateField.inclusion hle j₁, hj₁W⟩ :=
    Subtype.ext hinclj.symm
  have hρj : θ (IsLocalRing.residue ↥W₀' ⟨(jChartFin A (↥K) j : ↥K), hSW₀ _⟩) = ιIg jbar := by
    rw [hWj, hθincl]

  letI algK₀ : Algebra ↥(x1FunctionFieldC (IsLocalRing.ResidueField A) M)
      ↥(igusaFunctionFieldX1C (IsLocalRing.ResidueField A) M w) := ιIg.toRingHom.toAlgebra
  haveI : Module.Finite ↥(x1FunctionFieldC (IsLocalRing.ResidueField A) M)
      ↥(igusaFunctionFieldX1C (IsLocalRing.ResidueField A) M w) :=
    (ModularCurve.hasseRootFn_pow_mem_and_finite_and_isSeparable_igusaFunctionFieldX1C
      p M hM hpM (IsLocalRing.ResidueField A) w).2.1
  haveI : Algebra.IsAlgebraic ↥(x1FunctionFieldC (IsLocalRing.ResidueField A) M)
      ↥(igusaFunctionFieldX1C (IsLocalRing.ResidueField A) M w) := Algebra.IsAlgebraic.of_finite _ _
  have halgmap : ∀ z, algebraMap ↥(x1FunctionFieldC (IsLocalRing.ResidueField A) M)
      ↥(igusaFunctionFieldX1C (IsLocalRing.ResidueField A) M w) z = ιIg z := fun z => rfl

  let ρW : ↥(chartAlgFin A (↥K) j) →+* ↥W₀' :=
    { toFun := fun s => ⟨(s : ↥K), hSW₀ s⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  let ρ : ↥(chartAlgFin A (↥K) j) →+* IsLocalRing.ResidueField ↥W₀' := (IsLocalRing.residue ↥W₀').comp ρW
  have hρ : ∀ s, ρ s = IsLocalRing.residue ↥W₀' ⟨(s : ↥K), hSW₀ s⟩ := fun s => rfl
  let ρIg : ↥(chartAlgFin A (↥K) j) →+* ↥(igusaFunctionFieldX1C (IsLocalRing.ResidueField A) M w) :=
    θ.toRingHom.comp ρ
  have hρIg : ∀ s, ρIg s = θ (ρ s) := fun s => rfl
  have hρIgsymm : ∀ s, θ.symm (ρIg s) = ρ s := fun s => θ.symm_apply_apply _

  let toO : ValuationSubring (IsLocalRing.ResidueField ↥W₀') →
      ValuationSubring ↥(x1FunctionFieldC (IsLocalRing.ResidueField A) M) :=
    fun P => (P.comap θ.symm.toRingHom).comap
      (algebraMap _ ↥(igusaFunctionFieldX1C (IsLocalRing.ResidueField A) M w))
  have hOmem : ∀ P z, z ∈ toO P ↔ θ.symm (ιIg z) ∈ P := fun P z => Iff.rfl
  have hQmem : ∀ (P : ValuationSubring (IsLocalRing.ResidueField ↥W₀')) x,
      x ∈ P.comap θ.symm.toRingHom ↔ θ.symm x ∈ P := fun P x => Iff.rfl
  have key : ∀ P : ValuationSubring (IsLocalRing.ResidueField ↥W₀'),
      (∀ s : ↥(chartAlgFin A (↥K) j), IsLocalRing.residue ↥W₀' ⟨(s : ↥K), hSW₀ s⟩ ∈ P) →
      (∀ s : ↥(chartAlgFin A (↥K) j),
        IsLocalRing.residue ↥W₀' ⟨(s : ↥K), hSW₀ s⟩ ∈ P.nonunits ↔ s ∈ y.asIdeal) →
      ∃ hjO : jbar ∈ toO P,
        (∀ O₁ O₂ : ValuationSubring ↥(igusaFunctionFieldX1C (IsLocalRing.ResidueField A) M w),
          O₁.comap (IntermediateField.inclusion
            (ModularCurve.x1FunctionFieldC_le_igusaFunctionFieldX1C (IsLocalRing.ResidueField A) M w)).toRingHom
              = toO P →
          O₂.comap (IntermediateField.inclusion
            (ModularCurve.x1FunctionFieldC_le_igusaFunctionFieldX1C (IsLocalRing.ResidueField A) M w)).toRingHom
              = toO P →
          O₁ = O₂) ∧
        (∃ O' : ValuationSubring ↥(igusaFunctionFieldX1C (IsLocalRing.ResidueField A) M w),
          O'.comap (IntermediateField.inclusion
            (ModularCurve.x1FunctionFieldC_le_igusaFunctionFieldX1C (IsLocalRing.ResidueField A) M w)).toRingHom
              = toO P ∧
          ∀ e : ↥O', ∃ f : ↥(toO P),
            (e : ↥(igusaFunctionFieldX1C (IsLocalRing.ResidueField A) M w)) -
              IntermediateField.inclusion
                (ModularCurve.x1FunctionFieldC_le_igusaFunctionFieldX1C (IsLocalRing.ResidueField A) M w)
                (f : ↥(x1FunctionFieldC (IsLocalRing.ResidueField A) M))
              ∈ O'.nonunits) := by
    intro P hSP hcen

    have hκO : ∀ c : IsLocalRing.ResidueField A,
        algebraMap (IsLocalRing.ResidueField A) ↥(x1FunctionFieldC (IsLocalRing.ResidueField A) M) c ∈ toO P := by
      intro c
      obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective c
      have h1 : ιIg (algebraMap (IsLocalRing.ResidueField A) _ (IsLocalRing.residue A a)) =
          algebraMap (IsLocalRing.ResidueField A) _ (IsLocalRing.residue A a) := ιIg.commutes _
      rw [hOmem, h1, ← hθconst a, RingEquiv.symm_apply_apply]
      exact hSP (algebraMap A ↥(chartAlgFin A (↥K) j) a)

    obtain ⟨s₀, hs₀y, hs₀u⟩ := hy₀
    have hr0 : IsLocalRing.residue ↥W₀' ⟨(s₀ : ↥K), hSW₀ s₀⟩ ≠ 0 := by
      rw [Ne, IsLocalRing.residue_eq_zero_iff, ← ValuationSubring.coe_mem_nonunits_iff]
      exact hs₀u
    have hrP : IsLocalRing.residue ↥W₀' ⟨(s₀ : ↥K), hSW₀ s₀⟩ ∈ P.nonunits := (hcen s₀).mpr hs₀y
    have hPne : P ≠ ⊤ := by
      intro hP
      have h := (P.inv_mem_nonunits_iff (x := (IsLocalRing.residue ↥W₀' ⟨(s₀ : ↥K), hSW₀ s₀⟩)⁻¹)).mp
        (by rw [inv_inv]; exact hrP)
      rcases h with h | h
      · exact hr0 (inv_eq_zero.mp h)
      · apply h
        rw [hP]
        trivial
    have hQne : P.comap θ.symm.toRingHom ≠ ⊤ := by
      intro hQ
      apply hPne
      rw [← comap_comap_symm P θ, hQ]
      rfl
    have hO : toO P ≠ ⊤ := comap_ne_top_of_isAlgebraic _ hQne
    have hjO : jbar ∈ toO P := by
      rw [hOmem, ← hρj, RingEquiv.symm_apply_apply]
      exact hSP _

    have hssO : ∀ (Ω : Type) [Field Ω] [CharP Ω p] [IsAlgClosed Ω] [DecidableEq Ω] (φ₀ : ↥(toO P) →+* Ω),
        RingHom.ker φ₀ = IsLocalRing.maximalIdeal ↥(toO P) →
          φ₀ ⟨jbar, hjO⟩ ∈ ModularCurve.ssJSet p Ω := by
      intro Ω _ _ _ _ φ₀ hφ₀
      obtain ⟨φ, hφker, hφext⟩ := exists_ringHom_extend_of_isAlgebraic (P.comap θ.symm.toRingHom) φ₀ hφ₀
      have hmemQ : ∀ s : ↥(chartAlgFin A (↥K) j), ρIg s ∈ P.comap θ.symm.toRingHom := by
        intro s
        rw [hQmem, hρIgsymm]
        exact hSP s
      let ρQ : ↥(chartAlgFin A (↥K) j) →+* ↥(P.comap θ.symm.toRingHom) := ρIg.codRestrict _ hmemQ
      have hρQ : ∀ s, ((ρQ s : ↥(P.comap θ.symm.toRingHom)) :
          ↥(igusaFunctionFieldX1C (IsLocalRing.ResidueField A) M w)) = ρIg s := fun s => rfl
      have hψker : RingHom.ker (φ.comp ρQ) = y.asIdeal := by
        ext s
        rw [RingHom.mem_ker, RingHom.comp_apply, ← RingHom.mem_ker, hφker, ← ValuationSubring.coe_mem_nonunits_iff,
          hρQ, mem_nonunits_comap_iff, ← hcen s]
        have : θ.symm.toRingHom (ρIg s) = IsLocalRing.residue ↥W₀' ⟨(s : ↥K), hSW₀ s⟩ := hρIgsymm s
        rw [this]
      have hssj := hss Ω (φ.comp ρQ) hψker
      have hj1' : ((ρQ (jChartFin A (↥K) j) : ↥(P.comap θ.symm.toRingHom)) :
          ↥(igusaFunctionFieldX1C (IsLocalRing.ResidueField A) M w)) = algebraMap _ _ jbar := by
        rw [hρQ, hρIg, hρ, hρj, halgmap]
      have hj1 : (ρQ (jChartFin A (↥K) j)) =
          ⟨algebraMap _ _ jbar, ((hOmem P jbar).mp hjO : _)⟩ := Subtype.ext hj1'
      have hφj : (φ.comp ρQ) (jChartFin A (↥K) j) = φ₀ ⟨jbar, hjO⟩ := by
        rw [RingHom.comp_apply, hj1]
        exact hφext ⟨jbar, hjO⟩
      rw [← hφj]
      exact hssj
    exact ⟨hjO, ModularCurve.forall_valuationSubring_igusaFunctionFieldX1C_comap_eq_imp_eq_and_exists_of_mem_ssJSet
      p (IsLocalRing.ResidueField A) M hM hpM w jbar hjbar (toO P) hκO hO hjO hssO⟩
  have hθincl' : ∀ (u : ↥K₁) (hu : (IntermediateField.inclusion hle u : ↥K) ∈ W₀'),
      (IntermediateField.inclusion
        (ModularCurve.x1FunctionFieldC_le_igusaFunctionFieldX1C (IsLocalRing.ResidueField A) M w)).toRingHom
          (θ₁ (IsLocalRing.residue ↥U₀ ⟨u, (hU₀mem u).mpr hu⟩)) =
        θ (IsLocalRing.residue ↥W₀' ⟨IntermediateField.inclusion hle u, hu⟩) := fun u hu => (hθincl u hu).symm

  refine ⟨fun P P' hSP hcen hFP => ?_, fun P hSP hcen e => ?_⟩
  · obtain ⟨hjO, huniq, -⟩ := key P hSP hcen
    have hQ'O : (P'.comap θ.symm.toRingHom).comap (IntermediateField.inclusion
        (ModularCurve.x1FunctionFieldC_le_igusaFunctionFieldX1C (IsLocalRing.ResidueField A) M w)).toRingHom
          = toO P := by
      ext z
      obtain ⟨u, hu, rfl⟩ := hFsurj z
      rw [ValuationSubring.mem_comap, hQmem, hθincl', RingEquiv.symm_apply_apply, hOmem, ← hθincl u hu,
        RingEquiv.symm_apply_apply]
      exact hFP u hu
    have hQQ := huniq (P'.comap θ.symm.toRingHom) (P.comap θ.symm.toRingHom) hQ'O rfl
    rw [← comap_comap_symm P' θ, ← comap_comap_symm P θ, hQQ]
  · obtain ⟨hjO, huniq, O', hO'O, hO'triv⟩ := key P hSP hcen
    have hO'Q : O' = P.comap θ.symm.toRingHom := huniq O' _ hO'O rfl
    subst hO'Q
    have heQ : θ (e : IsLocalRing.ResidueField ↥W₀') ∈ P.comap θ.symm.toRingHom := by
      rw [hQmem, RingEquiv.symm_apply_apply]
      exact e.2
    obtain ⟨f, hf⟩ := hO'triv ⟨θ e, heQ⟩
    obtain ⟨u, hu, hfu⟩ := hFsurj (f : ↥(x1FunctionFieldC (IsLocalRing.ResidueField A) M))
    refine ⟨u, hu, ?_⟩
    have hx : θ ((e : IsLocalRing.ResidueField ↥W₀') -
        IsLocalRing.residue ↥W₀' ⟨IntermediateField.inclusion hle u, hu⟩) ∈ (P.comap θ.symm.toRingHom).nonunits := by
      rw [map_sub, hθincl u hu, hfu]
      exact hf
    have h2 := (mem_nonunits_comap_iff (P.comap θ.symm.toRingHom) θ.toRingHom _).mpr hx
    rwa [comap_comap_symm] at h2

end Modular

end S_ModularCurve_XOneP_forall_valuationSubring_residueField_eq_and_forall_exists_sub_residue_mem_nonunits_of_map_jChartFin_mem_ssJSet_twoChartIntegralModel_x1_mul_x1x0
end P2MW
export P2MW.S_ModularCurve_XOneP_forall_valuationSubring_residueField_eq_and_forall_exists_sub_residue_mem_nonunits_of_map_jChartFin_mem_ssJSet_twoChartIntegralModel_x1_mul_x1x0 (solution)
