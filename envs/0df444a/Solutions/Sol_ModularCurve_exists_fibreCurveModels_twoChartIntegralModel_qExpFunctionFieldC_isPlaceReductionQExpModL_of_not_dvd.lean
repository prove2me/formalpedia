-- Prove2me | solution 1 for ModularCurve.exists_fibreCurveModels_twoChartIntegralModel_qExpFunctionFieldC_isPlaceReductionQExpModL_of_not_dvd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/2c6312ac-2e73-58d1-a57a-57321d8cf397

import Mathlib
import Definitions.Def_ModularCurve_QExpReductionModL
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_LaurentCoeff
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_GaloisRep_Flat
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_CurveModelConstruction
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_FLTPrelim_Ramification
import Theorems.Thm_ModularCurve_exists_genericFibreIso_ofGenerator_twoChartIntegralModel_chartCentre_and_galoisCompat
import Theorems.Thm_ModularCurve_exists_curveModel_specialFibreIso_twoChartIntegralModel_qExpFunctionFieldC_chartCentre_of_not_dvd
import Theorems.Thm_ModularCurve_exists_isPlaceReductionQExpModL_chartCentre_of_not_dvd
import Theorems.Thm_ModularCurve_JOneES_exists_transcendental_finiteDimensional_laurentBaseChange
import Theorems.Thm_ModularCurve_transcendental_jqModC
import Theorems.Thm_AlgebraicCurve_finiteDimensional_adjoin_of_transcendental
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_fibreCurveModels_twoChartIntegralModel_qExpFunctionFieldC_isPlaceReductionQExpModL_of_not_dvd
p2m_attr_erase "instance" "ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois CohCarrier.iotaDeg_range_finiteIndex CohCarrier.Gamma0Upper_finiteIndex TateModule.instModule TateModule.instSMul CohCarrier.HeckeData.V_isScalarTower CohCarrier.HeckeData.opSubalgebra_isMulCommutative CohCarrier.HeckeData.mTheta_isPrime ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions"
p2m_attr_erase "instance" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.instIsElliptic_tateBase ModularCurve.instIsElliptic_tateLaurent ModularCurve.KatzGamma0Form.instModule ModularCurve.KatzGamma0Form.instZero ModularCurve.KatzLevelPForm.instSMul ModularCurve.KatzGamma0Form.instAdd ModularCurve.KatzLevelPForm.instAddCommGroup ModularCurve.KatzGamma0Form.instNeg ModularCurve.KatzGamma0Form.instAddCommGroup ModularCurve.KatzLevelPForm.instAdd ModularCurve.KatzLevelPForm.instSub ModularCurve.KatzLevelPForm.instNeg ModularCurve.KatzGamma0Form.instSMul ModularCurve.KatzGamma0Form.instSub ModularCurve.KatzLevelPForm.instZero ModularCurve.KatzLevelPForm.instModule KatzModularForm.instAddCommGroup KatzModularForm.instSub KatzModularForm.instZero KatzModularForm.instModule KatzModularForm.instAdd KatzModularForm.instNeg KatzModularForm.instSMul WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions"
p2m_attr_erase "instance" "WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular ModularCurve.IgusaScheme.isOpenImmersion_fInf ModularCurve.IgusaScheme.isOpenImmersion_ιInf ModularCurve.IgusaScheme.fact_jFull_ne_zero ModularCurve.IgusaScheme.isOpenImmersion_ιFin ModularCurve.IgusaScheme.isOpenImmersion_fFin"
p2m_attr_erase "simp" "ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul CohCarrier.conjUpperMat_apply_11 CohCarrier.conjUpperMat_apply_10 CohCarrier.mem_Gamma0Upper CohCarrier.val_gamma0Units AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap ModularCurve.JH.torsionGaloisRep_apply TateModule.smul_apply TateModule.coe_mulP TateModule.proj_apply TateModule.coe_add TateModule.coe_sub WeierstrassCurve.tateModuleRepOfBasis_V TateModule.coe_zero TateModule.rep_apply WeierstrassCurve.tateModuleRep_V WeierstrassCurve.tateModuleRepOfBasis_ρ_apply GaloisRep.padicIntToRingLevel_apply TateModule.coe_neg WeierstrassCurve.tateModuleRep_ρ_apply ModularCurve.qExpandAlgHomC_apply ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL CohCarrier.Gen.dia.sizeOf_spec CohCarrier.Gen.U.injEq"
p2m_attr_erase "simp" "CohCarrier.Gen.T.sizeOf_spec CohCarrier.Gen.U.sizeOf_spec CohCarrier.Gen.T.injEq CohCarrier.Gen.dia.injEq CohCarrier.HeckeData.mk.sizeOf_spec CohCarrier.HeckeData.opAlgHom_X CohCarrier.HeckeData.toMLₒ_apply CohCarrier.HeckeData.mk.injEq CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.ProjectiveLine.map_mk ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring"
p2m_attr_erase "simp" "ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_cuspidalDivisor₀ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint"
p2m_attr_erase "simp" "AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.Place.differentialCoeff_zero"
p2m_attr_erase "simp" "AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule ModularCurve.LevelN.coe_jGen"
p2m_attr_erase "simp" "HahnSeries.ramScale_apply WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.cuspData_yP ModularCurve.qTwistAlgHom_apply ModularCurve.cuspData_yQ ModularCurve.cuspData_xP ModularCurve.cuspData_xQ ModularCurve.val_cyclZeta ModularCurve.cuspShift_one ModularCurve.cuspShift_zero ModularCurve.LevelPData.mk.sizeOf_spec ModularCurve.KatzLevelPForm.neg_toFun ModularCurve.LevelP.coe_swapW ModularCurve.KatzLevelPForm.swap_swap KatzModularForm.pullbackLevelP_toFun ModularCurve.LevelPData.swap_xQ KatzModularForm.pullbackLevelP_zero"
p2m_attr_erase "simp" "ModularCurve.LevelPData.map_yP ModularCurve.KatzLevelPForm.swap_neg ModularCurve.KatzGamma0Form.toKatzLevelPForm_sub ModularCurve.KatzLevelPForm.swap_add KatzModularForm.swap_pullbackLevelP ModularCurve.KatzGamma0Form.toKatzLevelPForm_add ModularCurve.KatzLevelPForm.swap_smul ModularCurve.LevelPData.map_yQ ModularCurve.KatzLevelPForm.mk.injEq ModularCurve.KatzLevelPForm.zero_toFun KatzModularForm.pullbackLevelP_smul ModularCurve.LevelPData.swap_xP ModularCurve.KatzGamma0Form.toKatzLevelPForm_mul ModularCurve.KatzGamma0Form.toKatzLevelPForm_neg ModularCurve.LevelPData.variableChange_xQ KatzModularForm.pullbackGamma0_toKatzLevelPForm ModularCurve.KatzLevelPForm.mk.sizeOf_spec ModularCurve.KatzLevelPForm.swap_zero ModularCurve.LevelP.coe_unipotentU ModularCurve.KatzLevelPForm.mul_toFun ModularCurve.LevelPData.variableChange_yP ModularCurve.LevelPData.mk.injEq ModularCurve.KatzLevelPForm.sub_toFun ModularCurve.LevelPData.variableChange_xP ModularCurve.KatzLevelPForm.smul_toFun ModularCurve.LevelPData.swap_yP ModularCurve.LevelPData.map_xP ModularCurve.LevelPData.swap_swap ModularCurve.LevelPData.swap_yQ ModularCurve.KatzGamma0Form.toKatzLevelPForm_zero ModularCurve.KatzGamma0Form.mk.injEq ModularCurve.KatzLevelPForm.swap_toFun KatzModularForm.pullbackLevelP_add ModularCurve.KatzGamma0Form.mk.sizeOf_spec ModularCurve.LevelPData.variableChange_yQ ModularCurve.KatzLevelPForm.swap_sub ModularCurve.KatzGamma0Form.toKatzLevelPForm_smul ModularCurve.LevelPData.map_xQ ModularCurve.KatzLevelPForm.add_toFun KatzModularForm.c₆_toFun"
p2m_attr_erase "simp" "KatzModularForm.neg_toFun KatzModularForm.mul_toFun KatzModularForm.qExpansion_neg KatzModularForm.discr_toFun KatzModularForm.qExpansion_sub KatzModularForm.qExpansion_add KatzModularForm.qExpansion_mul KatzModularForm.zero_toFun KatzModularForm.mk.injEq KatzModularForm.qExpansion_smul KatzModularForm.smul_toFun KatzModularForm.add_toFun KatzModularForm.sub_toFun KatzModularForm.c₄_toFun KatzModularForm.qExpansion_zero KatzModularForm.mk.sizeOf_spec TateCurve.tateTorsionPoint_zero_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁"
p2m_attr_erase "simp" "TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆"
p2m_attr_erase "simp" "Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply"
p2m_attr_erase "simp" "WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff GoodReductionJacobian.RelativePic0Designation.mk.sizeOf_spec GoodReductionJacobian.AvatarSchemeBridge.mk.injEq MilneJVScheme.JacobianSchemeData.mk.injEq GoodReductionJacobian.AvatarSchemeBridge.mk.sizeOf_spec MilneJVScheme.JacobianSchemeData.mk.sizeOf_spec GoodReductionJacobian.RelativePic0Designation.mk.injEq GoodReductionJacobian.schemeHomOverComp_coe NeronModelInfra.schemeHomOverEquivOverHom_apply GoodReductionJacobian.RelativeGroupLaw.mk.sizeOf_spec NeronModelInfra.schemeHomOverEquivOverHom_symm_apply NeronModelInfra.overHomToSchemeHomOver_coe GoodReductionJacobian.RelativeGroupLaw.mk.injEq NeronModelInfra.overHomToSchemeHomOver_schemeHomOverToOverHom NeronModelInfra.schemeHomOverToOverHom_left NeronModelInfra.schemeHomOverToOverHom_overHomToSchemeHomOver ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe ModularCurve.CharPModel.FibreModel.mk.injEq ModularCurve.CharPModel.FibreModel.mk.sizeOf_spec ModularCurve.IgusaScheme.ιInf_igusaTo_assoc ModularCurve.IgusaScheme.coe_jFull ModularCurve.IgusaScheme.coe_jInvChartInf ModularCurve.IgusaScheme.coe_jChartFin ModularCurve.IgusaScheme.ιFin_igusaTo"
p2m_attr_erase "simp" "ModularCurve.IgusaScheme.ιInf_igusaTo ModularCurve.IgusaScheme.ιFin_igusaTo_assoc"

set_option autoImplicit false

noncomputable section

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve ModularCurve~coeffMap_injective P2MW.S_ModularCurve_exists_fibreCurveModels_twoChartIntegralModel_qExpFunctionFieldC_isPlaceReductionQExpModL_of_not_dvd.ModularCurve IsLocalRing"

namespace ModularCurve
p2m_export "ModularCurve" "IsPlaceReductionQExpModL qExpFunctionFieldC arithmeticGalois coeffMap coeffMap_coeff coeffEmb laurentBaseChange coeffEmb_mem_laurentBaseChange jqModC map_jqModC exists_genericFibreIso_ofGenerator_twoChartIntegralModel_chartCentre_and_galoisCompat exists_curveModel_specialFibreIso_twoChartIntegralModel_qExpFunctionFieldC_chartCentre_of_not_dvd exists_isPlaceReductionQExpModL_chartCentre_of_not_dvd JOneES.exists_transcendental_finiteDimensional_laurentBaseChange transcendental_jqModC"
namespace FibreCurveModelsGlue
p2m_open "ModularCurve~coeffMap_injective"

section TwoChart

universe u

open AlgebraicCurve.TwoChartIntegralModel

variable (R : Type u) [CommRing R] (F : Type u) [Field F] [Algebra R F] (j : F) [Fact (j ≠ 0)]

theorem span_overlap_aux {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : X ⟶ Z) (y : Y) (z : Z)
    (k : WalkingSpan) (fi : k ⟶ WalkingSpan.left) (fj : k ⟶ WalkingSpan.right)
    (w : (span f g).obj k) (h₁ : (span f g).map fi w = y) (h₂ : (span f g).map fj w = z) :
    ∃ x : X, f.base x = y ∧ g.base x = z := by
  match k, fi, fj, w, h₁, h₂ with
  | none, WidePushoutShape.Hom.init _, WidePushoutShape.Hom.init _, w, h₁, h₂ => exact ⟨w, h₁, h₂⟩

theorem ιFin_eq_ιInf_iff (x₀ : XFin R F j) (xi : XInf R F j) :
    (ιFin R F j).base x₀ = (ιInf R F j).base xi ↔
      ∃ w : XMid R F j, (fFin R F j).base w = x₀ ∧ (fInf R F j).base w = xi := by
  constructor
  · intro h
    obtain ⟨k, fi, fj, w, h₁, h₂⟩ :=
      (Scheme.IsLocallyDirected.ι_eq_ι_iff (F := span (fFin R F j) (fInf R F j))
        (i := WalkingSpan.left) (j := WalkingSpan.right) (xi := x₀) (xj := xi)).mp h
    exact span_overlap_aux _ _ _ _ k fi fj w h₁ h₂
  · rintro ⟨w, rfl, rfl⟩
    change (fFin R F j ≫ ιFin R F j).base w = (fInf R F j ≫ ιInf R F j).base w
    rw [glue_condition]

theorem range_fInf : Set.range (fInf R F j).base =
    ((PrimeSpectrum.basicOpen (jInvChartInf R F j) :
        TopologicalSpace.Opens (PrimeSpectrum (chartAlgInf R F j))) :
      Set (PrimeSpectrum (chartAlgInf R F j))) := by
  letI := (inclInf R F j).toRingHom.toAlgebra
  haveI := isLocalization_away_inclInf R F j
  exact PrimeSpectrum.localization_away_comap_range (chartAlgMid R F j) (jInvChartInf R F j)

theorem range_fFin : Set.range (fFin R F j).base =
    ((PrimeSpectrum.basicOpen (jChartFin R F j) :
        TopologicalSpace.Opens (PrimeSpectrum (chartAlgFin R F j))) :
      Set (PrimeSpectrum (chartAlgFin R F j))) := by
  letI := (inclFin R F j).toRingHom.toAlgebra
  haveI := isLocalization_away_inclFin R F j
  exact PrimeSpectrum.localization_away_comap_range (chartAlgMid R F j) (jChartFin R F j)

theorem ιInf_mem_range_ιFin_iff (xi : XInf R F j) :
    (ιInf R F j).base xi ∈ Set.range (ιFin R F j).base ↔ jInvChartInf R F j ∉ xi.asIdeal := by
  rw [← PrimeSpectrum.mem_basicOpen, ← SetLike.mem_coe, ← range_fInf, Set.mem_range]
  constructor
  · rintro ⟨x₀, h⟩
    obtain ⟨w, -, hw⟩ := (ιFin_eq_ιInf_iff R F j x₀ xi).mp h
    exact ⟨w, hw⟩
  · rintro ⟨w, rfl⟩
    exact ⟨(fFin R F j).base w, (ιFin_eq_ιInf_iff R F j _ _).mpr ⟨w, rfl, rfl⟩⟩

theorem ιFin_mem_range_ιInf_iff (x₀ : XFin R F j) :
    (ιFin R F j).base x₀ ∈ Set.range (ιInf R F j).base ↔ jChartFin R F j ∉ x₀.asIdeal := by
  rw [← PrimeSpectrum.mem_basicOpen, ← SetLike.mem_coe, ← range_fFin, Set.mem_range]
  constructor
  · rintro ⟨xi, h⟩
    obtain ⟨w, hw, -⟩ := (ιFin_eq_ιInf_iff R F j x₀ xi).mp h.symm
    exact ⟨w, hw⟩
  · rintro ⟨w, rfl⟩
    exact ⟨(fInf R F j).base w, ((ιFin_eq_ιInf_iff R F j _ _).mpr ⟨w, rfl, rfl⟩).symm⟩

variable {R F j}

theorem exists_eq_specMap_comp_ιFin {O : Type u} [CommRing O] [IsLocalRing O]
    (g : Spec (CommRingCat.of O) ⟶ AlgebraicCurve.TwoChartIntegralModel R F j)
    (h : g.base (closedPoint O) ∈ Set.range (ιFin R F j).base) :
    ∃ β : chartAlgFin R F j →+* O, g = Spec.map (CommRingCat.ofHom β) ≫ ιFin R F j := by
  have hmem : g.base (closedPoint O) ∈ (ιFin R F j).opensRange := h
  have htop := Scheme.preimage_eq_top_of_closedPoint_mem g hmem
  have hrange : Set.range g.base ⊆ Set.range (ιFin R F j).base := by
    rintro _ ⟨s, rfl⟩
    have : s ∈ g ⁻¹ᵁ (ιFin R F j).opensRange := by rw [htop]; trivial
    exact this
  refine ⟨(Spec.preimage (IsOpenImmersion.lift (ιFin R F j) g hrange)).hom, ?_⟩
  rw [CommRingCat.ofHom_hom, Spec.map_preimage, IsOpenImmersion.lift_fac]

theorem exists_eq_specMap_comp_ιInf {O : Type u} [CommRing O] [IsLocalRing O]
    (g : Spec (CommRingCat.of O) ⟶ AlgebraicCurve.TwoChartIntegralModel R F j)
    (h : g.base (closedPoint O) ∈ Set.range (ιInf R F j).base) :
    ∃ β : chartAlgInf R F j →+* O, g = Spec.map (CommRingCat.ofHom β) ≫ ιInf R F j := by
  have hmem : g.base (closedPoint O) ∈ (ιInf R F j).opensRange := h
  have htop := Scheme.preimage_eq_top_of_closedPoint_mem g hmem
  have hrange : Set.range g.base ⊆ Set.range (ιInf R F j).base := by
    rintro _ ⟨s, rfl⟩
    have : s ∈ g ⁻¹ᵁ (ιInf R F j).opensRange := by rw [htop]; trivial
    exact this
  refine ⟨(Spec.preimage (IsOpenImmersion.lift (ιInf R F j) g hrange)).hom, ?_⟩
  rw [CommRingCat.ofHom_hom, Spec.map_preimage, IsOpenImmersion.lift_fac]

theorem exists_chart_factorisation_fin {O : Type u} [CommRing O] [IsLocalRing O]
    (g : Spec (CommRingCat.of O) ⟶ AlgebraicCurve.TwoChartIntegralModel R F j) :
    (∃ β : chartAlgFin R F j →+* O, g = Spec.map (CommRingCat.ofHom β) ≫ ιFin R F j) ∨
      (∃ β : chartAlgInf R F j →+* O, g = Spec.map (CommRingCat.ofHom β) ≫ ιInf R F j ∧
        β (jInvChartInf R F j) ∈ maximalIdeal O) := by
  by_cases h : g.base (closedPoint O) ∈ Set.range (ιFin R F j).base
  · exact Or.inl (exists_eq_specMap_comp_ιFin g h)
  · obtain ⟨β, hβ⟩ := exists_eq_specMap_comp_ιInf g
      ((mem_range_ιFin_or_mem_range_ιInf R F j _).resolve_left h)
    refine Or.inr ⟨β, hβ, ?_⟩
    by_contra hnot
    apply h
    rw [hβ, Scheme.Hom.comp_base, TopCat.comp_app]
    refine (ιInf_mem_range_ιFin_iff R F j _).mpr ?_
    rw [Spec.map_apply]
    exact hnot

theorem exists_chart_factorisation_inf {O : Type u} [CommRing O] [IsLocalRing O]
    (g : Spec (CommRingCat.of O) ⟶ AlgebraicCurve.TwoChartIntegralModel R F j) :
    (∃ β : chartAlgInf R F j →+* O, g = Spec.map (CommRingCat.ofHom β) ≫ ιInf R F j) ∨
      (∃ β : chartAlgFin R F j →+* O, g = Spec.map (CommRingCat.ofHom β) ≫ ιFin R F j ∧
        β (jChartFin R F j) ∈ maximalIdeal O) := by
  by_cases h : g.base (closedPoint O) ∈ Set.range (ιInf R F j).base
  · exact Or.inl (exists_eq_specMap_comp_ιInf g h)
  · obtain ⟨β, hβ⟩ := exists_eq_specMap_comp_ιFin g
      ((mem_range_ιFin_or_mem_range_ιInf R F j _).resolve_right h)
    refine Or.inr ⟨β, hβ, ?_⟩
    by_contra hnot
    apply h
    rw [hβ, Scheme.Hom.comp_base, TopCat.comp_app]
    refine (ιFin_mem_range_ιInf_iff R F j _).mpr ?_
    rw [Spec.map_apply]
    exact hnot

theorem exists_chart_factorisation {O : Type u} [CommRing O] [IsLocalRing O]
    (g : Spec (CommRingCat.of O) ⟶ AlgebraicCurve.TwoChartIntegralModel R F j) :
    (∃ β : chartAlgFin R F j →+* O, g = Spec.map (CommRingCat.ofHom β) ≫ ιFin R F j) ∨
      (∃ β : chartAlgInf R F j →+* O, g = Spec.map (CommRingCat.ofHom β) ≫ ιInf R F j) := by
  rcases exists_chart_factorisation_fin g with h | ⟨β, hβ, -⟩
  · exact Or.inl h
  · exact Or.inr ⟨β, hβ⟩

end TwoChart

section Valuation

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem mem_of_mem_nonunits {O : ValuationSubring F} {x : F} (hx : x ∈ O.nonunits) : x ∈ O :=
  O.nonunits_subset hx

theorem sub_mem_nonunits {O : ValuationSubring F} {x y : F} (hx : x ∈ O.nonunits)
    (hy : y ∈ O.nonunits) : x - y ∈ O.nonunits := by
  rw [ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal] at hx hy ⊢
  obtain ⟨hx, hx'⟩ := hx
  obtain ⟨hy, hy'⟩ := hy
  exact ⟨sub_mem hx hy, Ideal.sub_mem _ hx' hy'⟩

theorem false_of_mem_of_inv_mem_nonunits {O : ValuationSubring F} {u : F} (hu0 : u ≠ 0)
    (hu : u ∈ O) (hui : u⁻¹ ∈ O.nonunits) : False := by
  rw [ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal] at hui
  obtain ⟨hui, hm⟩ := hui
  have hunit : IsUnit (⟨u⁻¹, hui⟩ : O) :=
    IsUnit.of_mul_eq_one ⟨u, hu⟩ (Subtype.ext (inv_mul_cancel₀ hu0))
  exact (IsLocalRing.mem_maximalIdeal _ |>.mp hm) hunit

theorem eq_zero_of_algebraMap_mem_nonunits (P : Place K F) {c : K}
    (hc : algebraMap K F c ∈ P.toValuationSubring.nonunits) : c = 0 := by
  by_contra h0
  refine false_of_mem_of_inv_mem_nonunits (O := P.toValuationSubring)
    (u := algebraMap K F c⁻¹) ?_ (P.algebraMap_mem' _) ?_
  · rw [map_inv₀]; exact inv_ne_zero ((map_ne_zero _).mpr h0)
  · rwa [map_inv₀, inv_inv]

theorem const_eq_of_sub_mem_nonunits (P : Place K F) {f : F} {c d : K}
    (hc : f - algebraMap K F c ∈ P.toValuationSubring.nonunits)
    (hd : f - algebraMap K F d ∈ P.toValuationSubring.nonunits) : c = d := by
  have h := sub_mem_nonunits hd hc
  rw [sub_sub_sub_cancel_left, ← map_sub] at h
  exact (sub_eq_zero.mp (eq_zero_of_algebraMap_mem_nonunits P h))

theorem mem_of_sub_algebraMap_mem_nonunits (P : Place K F) {f : F} {c : K}
    (hc : f - algebraMap K F c ∈ P.toValuationSubring.nonunits) : f ∈ P.toValuationSubring := by
  have h := add_mem (mem_of_mem_nonunits hc) (P.algebraMap_mem' c)
  rwa [sub_add_cancel] at h

end Valuation

section Coeff

theorem coeffMap_injective {R S : Type*} [CommRing R] [CommRing S] {f : R →+* S}
    (hf : Function.Injective f) : Function.Injective (coeffMap f) := by
  intro x y h
  ext n
  apply hf
  have := congrArg (fun z : LaurentSeries S => z.coeff n) h
  simpa only [coeffMap_coeff] using this

end Coeff

end ModularCurve.FibreCurveModelsGlue

end

open scoped MatrixGroups in
p2m_open "ModularCurve~coeffMap_injective" in open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra AlgebraicCurve _root_.P2MW.S_ModularCurve_exists_fibreCurveModels_twoChartIntegralModel_qExpFunctionFieldC_isPlaceReductionQExpModL_of_not_dvd.ModularCurve IsLocalRing ModularCurve.FibreCurveModelsGlue AlgebraicCurve.TwoChartIntegralModel in

set_option maxHeartbeats 12800000 in
set_option synthInstance.maxHeartbeats 1600000 in
theorem solution
    (M : ℕ) [NeZero M] (Γ : Subgroup SL(2, ℤ))
    (hΓ₁ : CongruenceSubgroup.Gamma1 M ≤ Γ) (hΓ₀ : Γ ≤ CongruenceSubgroup.Gamma0 M)
    (p : ℕ) [Fact p.Prime] (hpM : ¬ p ∣ M)
    (j : ↥(qExpFunctionFieldC ℚ Γ)) [Fact (j ≠ 0)] (hj : (j : LaurentSeries ℚ) = jqModC ℚ) :
    ∃ (Mη : CurveModel (AlgebraicClosure ℚ)
        ↥(laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ Γ)))
      (eη : Mη.C ⟶ pullback
        (TwoChartIntegralModel.toBase ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ Γ) j)
        (Spec.map (CommRingCat.ofHom
          (algebraMap ↥(GaloisRep.ratLocalizedAt p) (AlgebraicClosure ℚ)))))
      (_ : IsIso eη)
      (_ : eη ≫ pullback.snd _ _ = Mη.toBase)
      (_ : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
        (x x' : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Mη.C // q ≫ Mη.toBase = 𝟙 _}),
        x'.1 ≫ eη ≫ pullback.fst _ _ =
          Spec.map (CommRingCat.ofHom (σ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ)) ≫
            x.1 ≫ eη ≫ pullback.fst _ _ →
        Mη.pointEquivPlace x' =
          arithmeticGalois (L := AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ Γ) σ •
            Mη.pointEquivPlace x)
      (ρ : ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime p →
        (↥(GaloisRep.ratLocalizedAt p) →+* ↥A))
      (_ : ∀ (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p),
        A.subtype.comp (ρ A hA) = algebraMap ↥(GaloisRep.ratLocalizedAt p) (AlgebraicClosure ℚ))
      (Ms : ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime p →
        CurveModel (ResidueField ↥A) ↥(qExpFunctionFieldC (ResidueField ↥A) Γ))
      (es : ∀ (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p),
        (Ms A hA).C ⟶ pullback
          (TwoChartIntegralModel.toBase ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ Γ) j)
          (Spec.map (CommRingCat.ofHom ((residue ↥A).comp (ρ A hA)))))
      (_ : ∀ (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p), IsIso (es A hA))
      (_ : ∀ (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p),
        es A hA ≫ pullback.snd _ _ = (Ms A hA).toBase),
    ∀ (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
      [IsAlgClosed (ResidueField ↥A)],
      ∃ r : Place (AlgebraicClosure ℚ)
            ↥(laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ Γ)) →
          Place (ResidueField ↥A) ↥(qExpFunctionFieldC (ResidueField ↥A) Γ),
        IsPlaceReductionQExpModL A Γ r ∧
        ∀ (xA : SchemeHomOver (Spec.map (CommRingCat.ofHom (ρ A hA)))
            (TwoChartIntegralModel.toBase ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ Γ) j))
          (x : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Mη.C // q ≫ Mη.toBase = 𝟙 _})
          (y : {q : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ (Ms A hA).C //
            q ≫ (Ms A hA).toBase = 𝟙 _}),
          x.1 ≫ eη ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom A.subtype) ≫ xA.1 →
          y.1 ≫ es A hA ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (residue ↥A)) ≫ xA.1 →
          (Ms A hA).pointEquivPlace y = r (Mη.pointEquivPlace x) := by
  classical

  haveI : Γ.FiniteIndex := Subgroup.finiteIndex_of_le hΓ₁
  have hT : ModularGroup.T ∈ Γ := by
    apply hΓ₁
    rw [CongruenceSubgroup.Gamma1_mem]
    simp [ModularGroup.T]
  let jb : ↥(laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ Γ)) :=
    ⟨coeffEmb (AlgebraicClosure ℚ) ((j : ↥(qExpFunctionFieldC ℚ Γ)) : LaurentSeries ℚ),
      coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) j.2⟩
  have hjb : (jb : LaurentSeries (AlgebraicClosure ℚ)) =
      coeffEmb (AlgebraicClosure ℚ) ((j : ↥(qExpFunctionFieldC ℚ Γ)) : LaurentSeries ℚ) := rfl
  have hjbq : (jb : LaurentSeries (AlgebraicClosure ℚ)) = jqModC (AlgebraicClosure ℚ) := by
    rw [hjb, hj]
    exact map_jqModC _
  have htrans : Transcendental (AlgebraicClosure ℚ) jb := by
    have h := ModularCurve.transcendental_jqModC (AlgebraicClosure ℚ)
    rw [← hjbq] at h
    exact (transcendental_algebraMap_iff
      (algebraMap ↥(laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ Γ))
        (LaurentSeries (AlgebraicClosure ℚ))).injective).mp h
  haveI : Fact (jb ≠ 0) := ⟨fun h => htrans (by rw [h]; exact isAlgebraic_zero)⟩
  haveI hfd : FiniteDimensional
      ↥(IntermediateField.adjoin (AlgebraicClosure ℚ)
        ({jb} : Set ↥(laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ Γ))))
      ↥(laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ Γ)) := by
    obtain ⟨x, -, hx⟩ :=
      ModularCurve.JOneES.exists_transcendental_finiteDimensional_laurentBaseChange
        (AlgebraicClosure ℚ) Γ hT
    haveI := hx
    exact AlgebraicCurve.finiteDimensional_adjoin_of_transcendental x htrans
  haveI : FiniteDimensional
      ↥(IntermediateField.adjoin (AlgebraicClosure ℚ)
        ({jb⁻¹} : Set ↥(laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ Γ))))
      ↥(laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ Γ)) := by
    rw [CurveModel.adjoin_simple_inv_eq]; exact hfd

  obtain ⟨eη, hiso, heη, hcFin, hcInf, hgal⟩ :=
    ModularCurve.exists_genericFibreIso_ofGenerator_twoChartIntegralModel_chartCentre_and_galoisCompat
      (qExpFunctionFieldC ℚ Γ) p j jb hjb htrans
  obtain ⟨ρ, hρ, Ms, es, hes_iso, hes, πFin, πInf, hS⟩ :=
    ModularCurve.exists_curveModel_specialFibreIso_twoChartIntegralModel_qExpFunctionFieldC_chartCentre_of_not_dvd
      M Γ hΓ₁ hΓ₀ p hpM j hj
  refine ⟨CurveModel.ofGenerator (AlgebraicClosure ℚ) jb htrans, eη, hiso, heη, hgal, ρ, hρ, Ms, es,
    hes_iso, hes, ?_⟩
  intro A hA _
  obtain ⟨hyFin, hyInf, hpins⟩ := hS A hA
  obtain ⟨hpFin, hpInf⟩ := hpins

  obtain ⟨r, hr, hvFin, hvInf⟩ :=
    ModularCurve.exists_isPlaceReductionQExpModL_chartCentre_of_not_dvd M Γ hΓ₁ hΓ₀ p hpM j hj A hA
  refine ⟨r, hr, ?_⟩
  intro xA x y hx hy
  haveI := hes_iso A hA

  obtain ⟨P, hPx⟩ : ∃ P, (CurveModel.ofGenerator (AlgebraicClosure ℚ) jb htrans).pointEquivPlace x = P :=
    ⟨_, rfl⟩
  rw [hPx]

  have hj0 : ((j : ↥(qExpFunctionFieldC ℚ Γ)) : LaurentSeries ℚ) ≠ 0 := fun h =>
    (Fact.out : j ≠ 0) (by exact_mod_cast h)
  have hπj : (πInf A hA (jInvChartInf ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ Γ) j) :
        ↥(qExpFunctionFieldC (ResidueField ↥A) Γ)) *
      πFin A hA (jChartFin ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ Γ) j) = 1 := by
    obtain ⟨y₁, h₁, h₁'⟩ := hyInf (jInvChartInf ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ Γ) j)
    obtain ⟨y₂, h₂, h₂'⟩ := hyFin (jChartFin ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ Γ) j)
    have hprod : coeffMap A.subtype (y₁ * y₂) = 1 := by
      rw [map_mul, h₁, h₂, coe_jInvChartInf, coe_jChartFin, IntermediateField.coe_inv, map_inv₀,
        inv_mul_cancel₀ ((map_ne_zero _).mpr hj0)]
    have h12 : y₁ * y₂ = 1 :=
      coeffMap_injective (f := A.subtype) Subtype.val_injective (by rw [hprod, map_one])
    apply Subtype.ext
    rw [MulMemClass.coe_mul, OneMemClass.coe_one, h₁', h₂', ← map_mul, h12, map_one]
  have hπFin0 : (πFin A hA (jChartFin ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ Γ) j) :
      ↥(qExpFunctionFieldC (ResidueField ↥A) Γ)) ≠ 0 := right_ne_zero_of_mul_eq_one hπj
  have hπInf0 : (πInf A hA (jInvChartInf ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ Γ) j) :
      ↥(qExpFunctionFieldC (ResidueField ↥A) Γ)) ≠ 0 := left_ne_zero_of_mul_eq_one hπj
  have hπInf_eq : (πInf A hA (jInvChartInf ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ Γ) j) :
      ↥(qExpFunctionFieldC (ResidueField ↥A) Γ)) =
      (πFin A hA (jChartFin ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ Γ) j))⁻¹ :=
    eq_inv_of_mul_eq_one_left hπj
  have hπFin_eq : (πFin A hA (jChartFin ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ Γ) j) :
      ↥(qExpFunctionFieldC (ResidueField ↥A) Γ)) =
      (πInf A hA (jInvChartInf ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ Γ) j))⁻¹ :=
    eq_inv_of_mul_eq_one_right hπj

  have hpt : ∀ y' : {q : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ (Ms A hA).C //
        q ≫ (Ms A hA).toBase = 𝟙 _},
      y'.1 ≫ es A hA ≫ pullback.fst _ _ = y.1 ≫ es A hA ≫ pullback.fst _ _ → y' = y := by
    intro y' h
    apply Subtype.ext
    rw [← cancel_mono (es A hA)]
    apply pullback.hom_ext
    · simpa only [Category.assoc] using h
    · simp only [Category.assoc, hes]
      rw [y'.2, y.2]

  have hκ0 : ∀ c : ResidueField ↥A, c ∈ maximalIdeal (ResidueField ↥A) → c = 0 := by
    intro c hc
    by_contra hne
    exact ((IsLocalRing.mem_maximalIdeal _).mp hc) (isUnit_iff_ne_zero.mpr hne)

  obtain ⟨y', hy'⟩ := (Ms A hA).pointEquivPlace.surjective (r P)
  rw [← hy']

  rcases exists_chart_factorisation xA.1 with ⟨βA, hβA⟩ | ⟨βA, hβA⟩
  ·
    have hxc : x.1 ≫ eη ≫ pullback.fst _ _ =
        Spec.map (CommRingCat.ofHom (A.subtype.comp βA)) ≫
          ιFin ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ Γ) j := by
      rw [hx, hβA, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]
    have hP := hcFin x (A.subtype.comp βA) hxc
    rw [hPx] at hP
    have hyc : y.1 ≫ es A hA ≫ pullback.fst _ _ =
        Spec.map (CommRingCat.ofHom ((residue ↥A).comp βA)) ≫
          ιFin ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ Γ) j := by
      rw [hy, hβA, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]
    have hRP : ∀ b : ↥(chartAlgFin ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ Γ) j),
        (πFin A hA b : ↥(qExpFunctionFieldC (ResidueField ↥A) Γ)) -
            algebraMap (ResidueField ↥A) ↥(qExpFunctionFieldC (ResidueField ↥A) Γ)
              (residue ↥A (βA b)) ∈ (r P).toValuationSubring.nonunits := by
      intro b
      obtain ⟨yb, h1, h2⟩ := hyFin b
      exact hvFin P βA (fun b' => hP b') b yb (πFin A hA b) h1 h2
    congr 1
    rcases exists_chart_factorisation_fin (y'.1 ≫ es A hA ≫ pullback.fst _ _) with
      ⟨β'', hβ''⟩ | ⟨β'', hβ'', hβ''j⟩
    ·
      have hQ' := hpFin y' β'' hβ''
      rw [hy'] at hQ'
      have hββ : β'' = (residue ↥A).comp βA :=
        RingHom.ext fun b => const_eq_of_sub_mem_nonunits (r P) (hQ' b) (hRP b)
      exact (hpt y' (by rw [hβ'', hββ, ← hyc])).symm
    ·
      exfalso
      have hQ' := hpInf y' β'' hβ'' (jInvChartInf ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ Γ) j)
      rw [hy', hκ0 _ hβ''j, map_zero, sub_zero, hπInf_eq] at hQ'
      exact false_of_mem_of_inv_mem_nonunits hπFin0
        (mem_of_sub_algebraMap_mem_nonunits (r P) (hRP _)) hQ'
  ·
    have hxc : x.1 ≫ eη ≫ pullback.fst _ _ =
        Spec.map (CommRingCat.ofHom (A.subtype.comp βA)) ≫
          ιInf ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ Γ) j := by
      rw [hx, hβA, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]
    have hP := hcInf x (A.subtype.comp βA) hxc
    rw [hPx] at hP
    have hyc : y.1 ≫ es A hA ≫ pullback.fst _ _ =
        Spec.map (CommRingCat.ofHom ((residue ↥A).comp βA)) ≫
          ιInf ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ Γ) j := by
      rw [hy, hβA, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]
    have hRP : ∀ b : ↥(chartAlgInf ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ Γ) j),
        (πInf A hA b : ↥(qExpFunctionFieldC (ResidueField ↥A) Γ)) -
            algebraMap (ResidueField ↥A) ↥(qExpFunctionFieldC (ResidueField ↥A) Γ)
              (residue ↥A (βA b)) ∈ (r P).toValuationSubring.nonunits := by
      intro b
      obtain ⟨yb, h1, h2⟩ := hyInf b
      exact hvInf P βA (fun b' => hP b') b yb (πInf A hA b) h1 h2
    congr 1
    rcases exists_chart_factorisation_inf (y'.1 ≫ es A hA ≫ pullback.fst _ _) with
      ⟨β'', hβ''⟩ | ⟨β'', hβ'', hβ''j⟩
    · have hQ' := hpInf y' β'' hβ''
      rw [hy'] at hQ'
      have hββ : β'' = (residue ↥A).comp βA :=
        RingHom.ext fun b => const_eq_of_sub_mem_nonunits (r P) (hQ' b) (hRP b)
      exact (hpt y' (by rw [hβ'', hββ, ← hyc])).symm
    · exfalso
      have hQ' := hpFin y' β'' hβ'' (jChartFin ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ Γ) j)
      rw [hy', hκ0 _ hβ''j, map_zero, sub_zero, hπFin_eq] at hQ'
      exact false_of_mem_of_inv_mem_nonunits hπInf0
        (mem_of_sub_algebraMap_mem_nonunits (r P) (hRP _)) hQ'

end S_ModularCurve_exists_fibreCurveModels_twoChartIntegralModel_qExpFunctionFieldC_isPlaceReductionQExpModL_of_not_dvd
end P2MW
export P2MW.S_ModularCurve_exists_fibreCurveModels_twoChartIntegralModel_qExpFunctionFieldC_isPlaceReductionQExpModL_of_not_dvd (solution)
