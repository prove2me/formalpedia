-- Prove2me | solution 1 for ModularCurve.XOneP.coe_mem_adjoin_gaussReductions_chartAlg_igusaFunctionFieldX1C_x1_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/6eab20c5-0f78-51d4-b93f-0225fb99dce1

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_AlgebraicCurve_CurveModelConstruction
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_IgusaFunctionFieldX1
import Definitions.Def_ModularCurve_JqCoeff
import Theorems.Thm_ModularCurve_XOneP_exists_valuationSubring_pair_x1_mul
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_le_and_height_eq_one_and_exists_div_of_valuationSubring_of_transcendental
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_finite_polynomial_chartAlgFin_and_chartAlgInf
import Theorems.Thm_ModularCurve_finiteDimensional_adjoin_of_coe_eq_coeffEmb_jq_of_eq_laurentBaseChange
import Theorems.Thm_ModularCurve_transcendental_of_coe_eq_coeffEmb_jq
import Theorems.Thm_ModularCurve_transcendental_jqModC
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XOneP_coe_mem_adjoin_gaussReductions_chartAlg_igusaFunctionFieldX1C_x1_mul
p2m_attr_erase "instance" "WeierstrassCurve.Affine.Point.instFinite ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver"
p2m_attr_erase "instance" "AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion CohCarrier.iotaDeg_range_finiteIndex CohCarrier.Gamma0Upper_finiteIndex TateModule.instModule TateModule.instSMul GaloisRepAdic.instAddCommGroup GaloisRepAdic.instFree GaloisRepAdic.instFinite GaloisRepAdic.instModule ResidualGaloisRep.instModule ResidualGaloisRep.instModuleFinite ResidualGaloisRep.instAddCommGroup CohCarrier.HeckeData.V_isScalarTower CohCarrier.HeckeData.opSubalgebra_isMulCommutative CohCarrier.HeckeData.mTheta_isPrime ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois ModularCurve.instIsElliptic_tateBase ModularCurve.instIsElliptic_tateLaurent ModularCurve.KatzGamma0Form.instModule ModularCurve.KatzGamma0Form.instZero ModularCurve.KatzLevelPForm.instSMul ModularCurve.KatzGamma0Form.instAdd ModularCurve.KatzLevelPForm.instAddCommGroup ModularCurve.KatzGamma0Form.instNeg ModularCurve.KatzGamma0Form.instAddCommGroup ModularCurve.KatzLevelPForm.instAdd ModularCurve.KatzLevelPForm.instSub ModularCurve.KatzLevelPForm.instNeg ModularCurve.KatzGamma0Form.instSMul ModularCurve.KatzGamma0Form.instSub ModularCurve.KatzLevelPForm.instZero ModularCurve.KatzLevelPForm.instModule KatzModularForm.instAddCommGroup KatzModularForm.instSub"
p2m_attr_erase "instance" "KatzModularForm.instZero KatzModularForm.instModule KatzModularForm.instAdd KatzModularForm.instNeg KatzModularForm.instSMul WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular ModularCurve.Gamma0Pair.isElliptic TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module"
p2m_attr_erase "instance" "CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free"
p2m_attr_erase "simp" "ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq"
p2m_attr_erase "simp" "AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty"
p2m_attr_erase "simp" "AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule CohCarrier.conjUpperMat_apply_11 CohCarrier.conjUpperMat_apply_10 CohCarrier.mem_Gamma0Upper CohCarrier.val_gamma0Units ModularCurve.JH.torsionGaloisRep_apply TateModule.smul_apply TateModule.coe_mulP TateModule.proj_apply TateModule.coe_add TateModule.coe_sub WeierstrassCurve.tateModuleRepOfBasis_V TateModule.coe_zero TateModule.rep_apply WeierstrassCurve.tateModuleRep_V WeierstrassCurve.tateModuleRepOfBasis_ρ_apply GaloisRep.padicIntToRingLevel_apply TateModule.coe_neg WeierstrassCurve.tateModuleRep_ρ_apply"
p2m_attr_erase "simp" "GaloisRepAdic.mk.injEq GaloisRepAdic.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.injEq ResidualGaloisRep.mk.sizeOf_spec ResidualGaloisRep.mk.injEq ResidualGaloisRep.Equiv.mk.sizeOf_spec ResidualGaloisRep.Equiv.mk.injEq ModularCurve.qExpandAlgHomC_apply CohCarrier.Gen.dia.sizeOf_spec CohCarrier.Gen.U.injEq CohCarrier.Gen.T.sizeOf_spec CohCarrier.Gen.U.sizeOf_spec CohCarrier.Gen.T.injEq CohCarrier.Gen.dia.injEq CohCarrier.HeckeData.mk.sizeOf_spec CohCarrier.HeckeData.opAlgHom_X CohCarrier.HeckeData.toMLₒ_apply CohCarrier.HeckeData.mk.injEq CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply ModularCurve.ProjectiveLine.map_mk WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div"
p2m_attr_erase "simp" "ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_cuspidalDivisor₀ ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.cuspData_yP"
p2m_attr_erase "simp" "ModularCurve.qTwistAlgHom_apply ModularCurve.cuspData_yQ ModularCurve.cuspData_xP ModularCurve.cuspData_xQ ModularCurve.val_cyclZeta ModularCurve.cuspShift_one ModularCurve.cuspShift_zero ModularCurve.LevelPData.mk.sizeOf_spec ModularCurve.KatzLevelPForm.neg_toFun ModularCurve.LevelP.coe_swapW ModularCurve.KatzLevelPForm.swap_swap KatzModularForm.pullbackLevelP_toFun ModularCurve.LevelPData.swap_xQ KatzModularForm.pullbackLevelP_zero ModularCurve.LevelPData.map_yP ModularCurve.KatzLevelPForm.swap_neg ModularCurve.KatzGamma0Form.toKatzLevelPForm_sub ModularCurve.KatzLevelPForm.swap_add KatzModularForm.swap_pullbackLevelP ModularCurve.KatzGamma0Form.toKatzLevelPForm_add ModularCurve.KatzLevelPForm.swap_smul ModularCurve.LevelPData.map_yQ ModularCurve.KatzLevelPForm.mk.injEq ModularCurve.KatzLevelPForm.zero_toFun KatzModularForm.pullbackLevelP_smul ModularCurve.LevelPData.swap_xP ModularCurve.KatzGamma0Form.toKatzLevelPForm_mul ModularCurve.KatzGamma0Form.toKatzLevelPForm_neg ModularCurve.LevelPData.variableChange_xQ KatzModularForm.pullbackGamma0_toKatzLevelPForm ModularCurve.KatzLevelPForm.mk.sizeOf_spec ModularCurve.KatzLevelPForm.swap_zero ModularCurve.LevelP.coe_unipotentU ModularCurve.KatzLevelPForm.mul_toFun ModularCurve.LevelPData.variableChange_yP ModularCurve.LevelPData.mk.injEq ModularCurve.KatzLevelPForm.sub_toFun ModularCurve.LevelPData.variableChange_xP ModularCurve.KatzLevelPForm.smul_toFun ModularCurve.LevelPData.swap_yP"
p2m_attr_erase "simp" "ModularCurve.LevelPData.map_xP ModularCurve.LevelPData.swap_swap ModularCurve.LevelPData.swap_yQ ModularCurve.KatzGamma0Form.toKatzLevelPForm_zero ModularCurve.KatzGamma0Form.mk.injEq ModularCurve.KatzLevelPForm.swap_toFun KatzModularForm.pullbackLevelP_add ModularCurve.KatzGamma0Form.mk.sizeOf_spec ModularCurve.LevelPData.variableChange_yQ ModularCurve.KatzLevelPForm.swap_sub ModularCurve.KatzGamma0Form.toKatzLevelPForm_smul ModularCurve.LevelPData.map_xQ ModularCurve.KatzLevelPForm.add_toFun KatzModularForm.c₆_toFun KatzModularForm.neg_toFun KatzModularForm.mul_toFun KatzModularForm.qExpansion_neg KatzModularForm.discr_toFun KatzModularForm.qExpansion_sub KatzModularForm.qExpansion_add KatzModularForm.qExpansion_mul KatzModularForm.zero_toFun KatzModularForm.mk.injEq KatzModularForm.qExpansion_smul KatzModularForm.smul_toFun KatzModularForm.add_toFun KatzModularForm.sub_toFun KatzModularForm.c₄_toFun KatzModularForm.qExpansion_zero KatzModularForm.mk.sizeOf_spec TateCurve.tateTorsionPoint_zero_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero"
p2m_attr_erase "simp" "TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec"
p2m_attr_erase "simp" "EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.coordsOrZero_some"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁"
p2m_attr_erase "simp" "PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff HahnSeries.ramScale_apply AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply"
p2m_attr_erase "simp" "AlgebraicCurve.ConstantReduction.coe_degZeroMap ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring ModularCurve.LevelN.coe_jGen ModularCurve.CharPReduction.coeffRed_coeff ModularCurve.CharPReduction.redLocHom_apply ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar ModularCurve.ComplexPlaceDictionaryOf.pt_ofGamma0 ModularCurve.ComplexPlaceDictionaryOf.mk.injEq ModularCurve.ComplexPlaceDictionaryOf.pt_toGamma0 ModularCurve.ComplexPlaceDictionaryOf.mk.sizeOf_spec ModularCurve.ComplexPlaceDictionary.mk.injEq ModularCurve.ComplexPlaceDictionary.mk.sizeOf_spec ModularCurve.gamma0PairMap_gen ModularCurve.moduliPointMapRingHom_mk ModularCurve.Gamma0Pair.mk.injEq ModularCurve.ModuliPoint.j_mk ModularCurve.Gamma0Pair.mk.sizeOf_spec ModularCurve.gamma0PairMap_toCurve WeierstrassCurve.ratPointHom_apply WeierstrassCurve.ratPointMap_zero RegularLocalRingQuotientAscent.dualNumberFst_apply AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec"
p2m_attr_erase "simp" "CoherentBaseChange.TwoTermComplex.mk.injEq"

set_option autoImplicit false

set_option autoImplicit false

noncomputable section

open HahnSeries IsLocalRing
open scoped TensorProduct

namespace ModularCurve
p2m_export "ModularCurve" "intSeriesC intFormRatiosC div_mem_qExpFunctionFieldC x1FunctionFieldC x1FunctionField jNum jq coeffMap coeffMap_coeff coeffMap_single algebraMap_laurentSeries_eq_single coeffEmb laurentBaseChange IntegralWeightOneForm IntegralWeightOneForm.hasseRootFn igusaFunctionFieldX1C x1FunctionFieldC_le_igusaFunctionFieldX1C hasseRootFn_mem_igusaFunctionFieldX1C jqModC jqModC_rat map_jqModC XOneP.exists_valuationSubring_pair_x1_mul finiteDimensional_adjoin_of_coe_eq_coeffEmb_jq_of_eq_laurentBaseChange transcendental_of_coe_eq_coeffEmb_jq"
namespace GaussRedCore
p2m_open "ModularCurve~coeffMap_ofPowerSeries"

section Pres

variable {A : Type} [CommRing A] [IsDomain A] {L : Type} [Field L] [Algebra A L] [IsFractionRing A L]

variable (L) in

abbrev toL (x : PowerSeries A) : LaurentSeries L := ofPowerSeries ℤ L (x.map (algebraMap A L))

variable [IsLocalRing A]

abbrev toκ (x : PowerSeries A) : LaurentSeries (ResidueField A) :=
  ofPowerSeries ℤ (ResidueField A) (x.map (residue A))

variable (L) in

def Pres (f : LaurentSeries L) (x y : PowerSeries A) : Prop :=
  y.map (residue A) ≠ 0 ∧ f * toL L y = toL L x

omit [IsDomain A] [IsFractionRing A L] [IsLocalRing A] in
@[scoped simp] theorem toL_mul (x y : PowerSeries A) : toL L (x * y) = toL L x * toL L y := by simp [toL, map_mul]
omit [IsDomain A] [IsFractionRing A L] [IsLocalRing A] in
@[scoped simp] theorem toL_add (x y : PowerSeries A) : toL L (x + y) = toL L x + toL L y := by simp [toL, map_add]
omit [IsDomain A] [IsFractionRing A L] [IsLocalRing A] in
@[scoped simp] theorem toL_one : toL L (1 : PowerSeries A) = 1 := by simp [toL]
omit [IsDomain A] [IsFractionRing A L] [IsLocalRing A] in
@[scoped simp] theorem toL_zero : toL L (0 : PowerSeries A) = 0 := by simp [toL]
omit [IsDomain A] in
@[scoped simp] theorem toκ_mul (x y : PowerSeries A) : toκ (x * y) = toκ x * toκ y := by simp [toκ, map_mul]
omit [IsDomain A] in
@[scoped simp] theorem toκ_add (x y : PowerSeries A) : toκ (x + y) = toκ x + toκ y := by simp [toκ, map_add]
omit [IsDomain A] in
@[scoped simp] theorem toκ_one : toκ (1 : PowerSeries A) = 1 := by simp [toκ]
omit [IsDomain A] in
@[scoped simp] theorem toκ_zero : toκ (0 : PowerSeries A) = 0 := by simp [toκ]
omit [IsDomain A] in
theorem toκ_eq_zero_iff (x : PowerSeries A) : toκ x = 0 ↔ x.map (residue A) = 0 := by
  constructor
  · intro e; exact ofPowerSeries_injective (e.trans (map_zero _).symm)
  · intro e; rw [toκ, e, map_zero]

omit [IsDomain A] [IsLocalRing A] in
theorem toL_injective : Function.Injective (toL (A := A) L) := fun x y h =>
  PowerSeries.map_injective (algebraMap A L) (IsFractionRing.injective A L) (ofPowerSeries_injective h)

omit [IsDomain A] [IsFractionRing A L] in
theorem Pres.mul {f g : LaurentSeries L} {x y x' y' : PowerSeries A}
    (hf : Pres L f x y) (hg : Pres L g x' y') : Pres L (f * g) (x * x') (y * y') := by
  refine ⟨by rw [map_mul]; exact mul_ne_zero hf.1 hg.1, ?_⟩
  rw [toL_mul, toL_mul, ← hf.2, ← hg.2]; ring

omit [IsDomain A] [IsFractionRing A L] in
theorem Pres.add {f g : LaurentSeries L} {x y x' y' : PowerSeries A}
    (hf : Pres L f x y) (hg : Pres L g x' y') : Pres L (f + g) (x * y' + x' * y) (y * y') := by
  refine ⟨by rw [map_mul]; exact mul_ne_zero hf.1 hg.1, ?_⟩
  rw [toL_mul, toL_add, toL_mul, toL_mul, ← hf.2, ← hg.2]; ring

omit [IsDomain A] [IsFractionRing A L] in
theorem Pres.one : Pres L (1 : LaurentSeries L) (1 : PowerSeries A) 1 :=
  ⟨by simp, by simp⟩

omit [IsDomain A] [IsFractionRing A L] in
theorem Pres.zero : Pres L (0 : LaurentSeries L) (0 : PowerSeries A) 1 :=
  ⟨by simp, by simp⟩

omit [IsDomain A] in

theorem Pres.unique {f : LaurentSeries L} {x y x' y' : PowerSeries A}
    (h : Pres L f x y) (h' : Pres L f x' y') :
    x.map (residue A) * y'.map (residue A) = x'.map (residue A) * y.map (residue A) := by
  have : toL L (x * y') = toL L (x' * y) := by
    rw [toL_mul, toL_mul, ← h.2, ← h'.2]; ring
  have := toL_injective this
  rw [← map_mul, ← map_mul, this]

omit [IsDomain A] in

theorem Pres.red_eq {f : LaurentSeries L} {x y x' y' : PowerSeries A}
    (h : Pres L f x y) (h' : Pres L f x' y') : toκ x / toκ y = toκ x' / toκ y' := by
  have hy : toκ y ≠ 0 := fun e => h.1 ((toκ_eq_zero_iff y).mp e)
  have hy' : toκ y' ≠ 0 := fun e => h'.1 ((toκ_eq_zero_iff y').mp e)
  have e := congrArg (ofPowerSeries ℤ (ResidueField A)) (h.unique h')
  rw [map_mul, map_mul] at e
  rw [div_eq_div_iff hy hy']
  exact e

omit [IsDomain A] [IsFractionRing A L] in

theorem Pres.algebraMap (a : A) :
    Pres L (algebraMap L (LaurentSeries L) (algebraMap A L a)) (PowerSeries.C a) 1 := by
  refine ⟨by simp, ?_⟩
  rw [toL_one, mul_one, toL, PowerSeries.map_C, ofPowerSeries_C, HahnSeries.C_apply,
    algebraMap_laurentSeries_eq_single]

end Pres

section ResidueToK

variable {A : Type} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] (k : Type) [Field k] [Algebra A k]
  {p : ℕ} [Fact p.Prime] [CharP k p]

omit [Fact p.Prime] in

theorem algebraMap_eq_zero_of_mem_maximalIdeal
    (hp0 : (p : A) ≠ 0) (hAp : (p : A) ∈ maximalIdeal A) {a : A} (ha : a ∈ maximalIdeal A) : algebraMap A k a = 0 := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible A
  have hmax := (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ
  obtain ⟨n, u, hn⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hp0 hϖ
  have hn0 : n ≠ 0 := by
    rintro rfl
    rw [pow_zero, mul_one] at hn
    exact (mem_maximalIdeal _).mp hAp (hn ▸ u.isUnit)
  have hϖ0 : algebraMap A k ϖ = 0 := by
    have : algebraMap A k p = 0 := by rw [map_natCast]; exact CharP.cast_eq_zero k p
    rw [hn, map_mul, map_pow] at this
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h (u.isUnit.map _).ne_zero
    · exact pow_eq_zero_iff hn0 |>.mp h
  rw [hmax, Ideal.mem_span_singleton'] at ha
  obtain ⟨c, rfl⟩ := ha
  rw [map_mul, hϖ0, mul_zero]

def residueToK (hp0 : (p : A) ≠ 0) (hAp : (p : A) ∈ maximalIdeal A) : ResidueField A →+* k :=
  Ideal.Quotient.lift (maximalIdeal A) (algebraMap A k)
    (fun _ ha => algebraMap_eq_zero_of_mem_maximalIdeal k hp0 hAp ha)

omit [Fact p.Prime] in
@[scoped simp] theorem residueToK_residue (hp0 : (p : A) ≠ 0) (hAp : (p : A) ∈ maximalIdeal A) (a : A) :
    residueToK k hp0 hAp (residue A a) = algebraMap A k a := rfl

omit [IsDomain A] [IsDiscreteValuationRing A] [Field k] [Algebra A k] [Fact p.Prime] [CharP k p] in

theorem coeffMap_ofPowerSeries {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (y : PowerSeries R) :
    coeffMap f (ofPowerSeries ℤ R y) = ofPowerSeries ℤ S (y.map f) := by
  ext n
  rw [coeffMap_coeff]
  rcases le_or_gt 0 n with hn | hn
  · obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hn
    rw [ofPowerSeries_apply_coeff, ofPowerSeries_apply_coeff, PowerSeries.coeff_map]
  · have hn' : n ∉ Set.range (fun m : ℕ => (m : ℤ)) := by
      rintro ⟨m, rfl⟩; exact (not_le.mpr hn) (Int.natCast_nonneg m)
    rw [ofPowerSeries_apply, ofPowerSeries_apply, embDomain_notin_range, embDomain_notin_range, map_zero]
    · simpa using hn'
    · simpa using hn'

omit [Fact p.Prime] in

theorem coeffMap_residueToK_toκ (hp0 : (p : A) ≠ 0) (hAp : (p : A) ∈ maximalIdeal A) (x : PowerSeries A) :
    coeffMap (residueToK k hp0 hAp) (toκ x) = ofPowerSeries ℤ k (x.map (algebraMap A k)) := by
  rw [toκ, coeffMap_ofPowerSeries, ← RingHom.comp_apply (PowerSeries.map _), ← PowerSeries.map_comp]
  congr 2

omit [Fact p.Prime] in

theorem coeffMap_residueToK_intSeriesC (hp0 : (p : A) ≠ 0) (hAp : (p : A) ∈ maximalIdeal A) (s : PowerSeries ℤ) :
    coeffMap (residueToK k hp0 hAp) (intSeriesC (ResidueField A) s) = intSeriesC k s := by
  rw [intSeriesC, intSeriesC, coeffMap_ofPowerSeries, ← RingHom.comp_apply (PowerSeries.map _), ← PowerSeries.map_comp,
    show (residueToK k hp0 hAp).comp (Int.castRingHom _) = Int.castRingHom k from RingHom.ext_int _ _]

variable {M : ℕ}

def overResidueField (hp0 : (p : A) ≠ 0) (hAp : (p : A) ∈ maximalIdeal A) (w : IntegralWeightOneForm k M) :
    IntegralWeightOneForm (ResidueField A) M where
  form := w.form
  series := w.series
  isIntegralQExp := w.isIntegralQExp
  intSeriesC_ne_zero h := w.intSeriesC_ne_zero (by
    rw [← coeffMap_residueToK_intSeriesC k hp0 hAp, h, map_zero])

omit [Fact p.Prime] in

theorem coeffMap_mem_x1FunctionFieldC (hp0 : (p : A) ≠ 0) (hAp : (p : A) ∈ maximalIdeal A) {z : LaurentSeries (ResidueField A)}
    (hz : z ∈ x1FunctionFieldC (ResidueField A) M) :
    coeffMap (residueToK k hp0 hAp) z ∈ x1FunctionFieldC k M := by
  set φ := coeffMap (residueToK k hp0 hAp) with hφ
  change z ∈ Subfield.closure (Set.range (algebraMap (ResidueField A) (LaurentSeries (ResidueField A))) ∪
    intFormRatiosC (ResidueField A) (CongruenceSubgroup.Gamma1 M)) at hz
  change φ z ∈ Subfield.closure (Set.range (algebraMap k (LaurentSeries k)) ∪
    intFormRatiosC k (CongruenceSubgroup.Gamma1 M))
  have hle : (Subfield.closure (Set.range (algebraMap (ResidueField A) (LaurentSeries (ResidueField A))) ∪
      intFormRatiosC (ResidueField A) (CongruenceSubgroup.Gamma1 M))).map φ ≤
      Subfield.closure (Set.range (algebraMap k (LaurentSeries k)) ∪
        intFormRatiosC k (CongruenceSubgroup.Gamma1 M)) := by
    rw [RingHom.map_field_closure]
    apply Subfield.closure_mono
    rintro _ ⟨v, hv | hv, rfl⟩
    · obtain ⟨c, rfl⟩ := hv
      left
      refine ⟨residueToK k hp0 hAp c, ?_⟩
      rw [algebraMap_laurentSeries_eq_single, algebraMap_laurentSeries_eq_single, hφ, coeffMap_single]
    · right
      obtain ⟨wt, f, g, pf, pg, hf, hg, hg0, rfl⟩ := hv
      refine ⟨wt, f, g, pf, pg, hf, hg, ?_, ?_⟩
      · rw [← coeffMap_residueToK_intSeriesC k hp0 hAp]
        exact (map_ne_zero φ).mpr hg0
      · rw [map_div₀, hφ, coeffMap_residueToK_intSeriesC, coeffMap_residueToK_intSeriesC]
  exact hle ⟨z, hz, rfl⟩

theorem coeffMap_mem_igusaFunctionFieldX1C (hp0 : (p : A) ≠ 0) (hAp : (p : A) ∈ maximalIdeal A) (w : IntegralWeightOneForm k M)
    {z : LaurentSeries (ResidueField A)}
    (hz : z ∈ igusaFunctionFieldX1C (ResidueField A) M (overResidueField k hp0 hAp w)) :
    coeffMap (residueToK k hp0 hAp) z ∈ igusaFunctionFieldX1C k M w := by
  set φ := coeffMap (residueToK k hp0 hAp) with hφ
  change z ∈ Subfield.closure (Set.range (algebraMap (ResidueField A) (LaurentSeries (ResidueField A))) ∪
    ((x1FunctionFieldC (ResidueField A) M : Set (LaurentSeries (ResidueField A))) ∪
      {(overResidueField k hp0 hAp w).hasseRootFn})) at hz
  change φ z ∈ Subfield.closure (Set.range (algebraMap k (LaurentSeries k)) ∪
    ((x1FunctionFieldC k M : Set (LaurentSeries k)) ∪ {w.hasseRootFn}))
  have hle : (Subfield.closure (Set.range (algebraMap (ResidueField A) (LaurentSeries (ResidueField A))) ∪
      ((x1FunctionFieldC (ResidueField A) M : Set (LaurentSeries (ResidueField A))) ∪
        {(overResidueField k hp0 hAp w).hasseRootFn}))).map φ ≤
      Subfield.closure (Set.range (algebraMap k (LaurentSeries k)) ∪
        ((x1FunctionFieldC k M : Set (LaurentSeries k)) ∪ {w.hasseRootFn})) := by
    rw [RingHom.map_field_closure]
    apply Subfield.closure_mono
    rintro _ ⟨v, hv | hv | hv, rfl⟩
    · obtain ⟨c, rfl⟩ := hv
      left
      refine ⟨residueToK k hp0 hAp c, ?_⟩
      rw [algebraMap_laurentSeries_eq_single, algebraMap_laurentSeries_eq_single, hφ, coeffMap_single]
    · exact Or.inr (Or.inl (coeffMap_mem_x1FunctionFieldC k hp0 hAp hv))
    · rw [Set.mem_singleton_iff] at hv
      subst hv
      refine Or.inr (Or.inr ?_)
      rw [Set.mem_singleton_iff, IntegralWeightOneForm.hasseRootFn, IntegralWeightOneForm.hasseRootFn, map_inv₀,
        hφ, coeffMap_residueToK_intSeriesC]
      rfl
  exact hle ⟨z, hz, rfl⟩

end ResidueToK

structure Setup (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    (L : Type) [Field L] [Algebra A L] [IsFractionRing A L]
    (K : IntermediateField L (LaurentSeries L)) [Algebra A ↥K] [IsScalarTower A L ↥K]
    (k : Type) [Field k] [Algebra A k] (p : ℕ) [Fact p.Prime] [CharP k p] (M : ℕ) where

  W₀ : ValuationSubring ↥K

  mem_W₀_iff : ∀ f : ↥K, f ∈ W₀ ↔ ∃ x y : PowerSeries A, Pres L (f : LaurentSeries L) x y

  algebraMap_mem_W₀ : ∀ a : A, algebraMap A ↥K a ∈ W₀

  hp0 : (p : A) ≠ 0

  hAp : (p : A) ∈ maximalIdeal A

  w : IntegralWeightOneForm k M

  red_mem : ∀ (f : ↥K) (x y : PowerSeries A), Pres L (f : LaurentSeries L) x y →
    toκ x / toκ y ∈ igusaFunctionFieldX1C (ResidueField A) M (overResidueField k hp0 hAp w)

namespace Setup

variable {A : Type} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  {L : Type} [Field L] [Algebra A L] [IsFractionRing A L]
  {K : IntermediateField L (LaurentSeries L)} [Algebra A ↥K] [IsScalarTower A L ↥K]
  {k : Type} [Field k] [Algebra A k] {p : ℕ} [Fact p.Prime] [CharP k p] {M : ℕ}
  (D : Setup A L K k p M)

theorem exists_pres (f : ↥D.W₀) : ∃ x y : PowerSeries A, Pres L ((f : ↥K) : LaurentSeries L) x y :=
  (D.mem_W₀_iff f).mp f.2

def gaussRedFun (f : ↥D.W₀) : LaurentSeries (ResidueField A) :=
  toκ (D.exists_pres f).choose / toκ (D.exists_pres f).choose_spec.choose

theorem gaussRedFun_spec {f : ↥D.W₀} {x y : PowerSeries A} (h : Pres L ((f : ↥K) : LaurentSeries L) x y) :
    D.gaussRedFun f = toκ x / toκ y :=
  Pres.red_eq (D.exists_pres f).choose_spec.choose_spec h

omit [Algebra A ↥K] [IsScalarTower A L ↥K] [Fact p.Prime] [CharP k p] [IsFractionRing A L] in
theorem toκ_ne_zero_of_pres {f : LaurentSeries L} {x y : PowerSeries A} (h : Pres L f x y) : toκ y ≠ 0 :=
  fun e => h.1 ((toκ_eq_zero_iff y).mp e)

def gaussRed : ↥D.W₀ →+* LaurentSeries (ResidueField A) where
  toFun := D.gaussRedFun
  map_one' := by
    have h1 : Pres L (((1 : ↥D.W₀) : ↥K) : LaurentSeries L) (1 : PowerSeries A) 1 := by
      simpa using (Pres.one (A := A) (L := L))
    rw [D.gaussRedFun_spec h1, div_self]
    simp
  map_mul' f g := by
    obtain ⟨x, y, hf⟩ := D.exists_pres f
    obtain ⟨x', y', hg⟩ := D.exists_pres g
    have hfg : Pres L (((f * g : ↥D.W₀) : ↥K) : LaurentSeries L) (x * x') (y * y') := hf.mul hg
    rw [D.gaussRedFun_spec hfg, D.gaussRedFun_spec hf, D.gaussRedFun_spec hg, toκ_mul, toκ_mul,
      div_mul_div_comm]
  map_zero' := by
    have h0 : Pres L (((0 : ↥D.W₀) : ↥K) : LaurentSeries L) (0 : PowerSeries A) 1 := by
      simpa using (Pres.zero (A := A) (L := L))
    rw [D.gaussRedFun_spec h0]
    simp
  map_add' f g := by
    obtain ⟨x, y, hf⟩ := D.exists_pres f
    obtain ⟨x', y', hg⟩ := D.exists_pres g
    have hfg : Pres L (((f + g : ↥D.W₀) : ↥K) : LaurentSeries L) (x * y' + x' * y) (y * y') := hf.add hg
    rw [D.gaussRedFun_spec hfg, D.gaussRedFun_spec hf, D.gaussRedFun_spec hg,
      div_add_div _ _ (toκ_ne_zero_of_pres hf) (toκ_ne_zero_of_pres hg), toκ_add, toκ_mul, toκ_mul, toκ_mul]
    ring

theorem gaussRed_spec {f : ↥D.W₀} {x y : PowerSeries A} (h : Pres L ((f : ↥K) : LaurentSeries L) x y) :
    D.gaussRed f = toκ x / toκ y :=
  D.gaussRedFun_spec h

theorem gaussRed_eq_zero_iff {f : ↥D.W₀} {x y : PowerSeries A} (h : Pres L ((f : ↥K) : LaurentSeries L) x y) :
    D.gaussRed f = 0 ↔ x.map (residue A) = 0 := by
  rw [D.gaussRed_spec h, div_eq_zero_iff, or_iff_left (toκ_ne_zero_of_pres h), toκ_eq_zero_iff]

theorem gaussRed_mem (f : ↥D.W₀) :
    D.gaussRed f ∈ igusaFunctionFieldX1C (ResidueField A) M (overResidueField k D.hp0 D.hAp D.w) := by
  obtain ⟨x, y, h⟩ := D.exists_pres f
  rw [D.gaussRed_spec h]
  exact D.red_mem _ x y h

def gaussRedK : ↥D.W₀ →+* LaurentSeries k := (coeffMap (residueToK k D.hp0 D.hAp)).comp D.gaussRed

theorem gaussRedK_spec {f : ↥D.W₀} {x y : PowerSeries A} (h : Pres L ((f : ↥K) : LaurentSeries L) x y) :
    D.gaussRedK f = ofPowerSeries ℤ k (x.map (algebraMap A k)) / ofPowerSeries ℤ k (y.map (algebraMap A k)) := by
  rw [gaussRedK, RingHom.comp_apply, D.gaussRed_spec h, map_div₀, coeffMap_residueToK_toκ, coeffMap_residueToK_toκ]

theorem gaussRedK_algebraMap (a : A) :
    D.gaussRedK ⟨_, D.algebraMap_mem_W₀ a⟩ = algebraMap k (LaurentSeries k) (algebraMap A k a) := by
  have h : Pres L (((⟨_, D.algebraMap_mem_W₀ a⟩ : ↥D.W₀) : ↥K) : LaurentSeries L) (PowerSeries.C a) 1 := by
    have e : (((⟨_, D.algebraMap_mem_W₀ a⟩ : ↥D.W₀) : ↥K) : LaurentSeries L) =
        algebraMap L (LaurentSeries L) (algebraMap A L a) := by
      change ((algebraMap A ↥K a : ↥K) : LaurentSeries L) = _
      rw [IsScalarTower.algebraMap_apply A L ↥K]
      rfl
    rw [e]
    exact Pres.algebraMap a
  rw [D.gaussRedK_spec h, PowerSeries.map_C, map_one, map_one, div_one, ofPowerSeries_C, HahnSeries.C_apply,
    algebraMap_laurentSeries_eq_single]

theorem gaussRedK_mem (f : ↥D.W₀) : D.gaussRedK f ∈ igusaFunctionFieldX1C k M D.w :=
  coeffMap_mem_igusaFunctionFieldX1C k D.hp0 D.hAp D.w (D.gaussRed_mem f)

variable (B : Subalgebra A ↥K)

def inclW₀ (hB : ∀ b ∈ B, b ∈ D.W₀) : ↥B →+* ↥D.W₀ where
  toFun b := ⟨b, hB b b.2⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

def ρ (hB : ∀ b ∈ B, b ∈ D.W₀) : ↥B →+* ↥(igusaFunctionFieldX1C k M D.w) :=
  (D.gaussRedK.comp (D.inclW₀ B hB)).codRestrict (igusaFunctionFieldX1C k M D.w) (fun _ => D.gaussRedK_mem _)

theorem coe_ρ (hB : ∀ b ∈ B, b ∈ D.W₀) (b : ↥B) :
    ((D.ρ B hB b : ↥(igusaFunctionFieldX1C k M D.w)) : LaurentSeries k) = D.gaussRedK ⟨b, hB b b.2⟩ := rfl

theorem ρ_algebraMap (hB : ∀ b ∈ B, b ∈ D.W₀) (a : A) :
    D.ρ B hB (algebraMap A ↥B a) = algebraMap k ↥(igusaFunctionFieldX1C k M D.w) (algebraMap A k a) := by
  apply Subtype.ext
  rw [coe_ρ]
  exact D.gaussRedK_algebraMap a

def ρₐ (hB : ∀ b ∈ B, b ∈ D.W₀) :
    letI : Algebra A ↥(igusaFunctionFieldX1C k M D.w) :=
      ((algebraMap k ↥(igusaFunctionFieldX1C k M D.w)).comp (algebraMap A k)).toAlgebra
    ↥B →ₐ[A] ↥(igusaFunctionFieldX1C k M D.w) :=
  letI : Algebra A ↥(igusaFunctionFieldX1C k M D.w) :=
    ((algebraMap k ↥(igusaFunctionFieldX1C k M D.w)).comp (algebraMap A k)).toAlgebra
  { D.ρ B hB with commutes' := fun a => D.ρ_algebraMap B hB a }

set_option synthInstance.maxHeartbeats 1600000 in

def θ (hB : ∀ b ∈ B, b ∈ D.W₀) : k ⊗[A] ↥B →ₐ[k] ↥(igusaFunctionFieldX1C k M D.w) :=
  letI : Algebra A ↥(igusaFunctionFieldX1C k M D.w) :=
    ((algebraMap k ↥(igusaFunctionFieldX1C k M D.w)).comp (algebraMap A k)).toAlgebra
  haveI : IsScalarTower A k ↥(igusaFunctionFieldX1C k M D.w) := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  Algebra.TensorProduct.lift (R := A) (S := k) (A := k) (B := ↥B) (C := ↥(igusaFunctionFieldX1C k M D.w))
    (Algebra.ofId k ↥(igusaFunctionFieldX1C k M D.w)) (D.ρₐ B hB)
    (fun x y => Commute.all ((Algebra.ofId k ↥(igusaFunctionFieldX1C k M D.w)) x) ((D.ρₐ B hB) y))

set_option synthInstance.maxHeartbeats 1600000 in
theorem θ_tmul (hB : ∀ b ∈ B, b ∈ D.W₀) (a : k) (b : ↥B) :
    D.θ B hB (a ⊗ₜ[A] b) = algebraMap k _ a * D.ρ B hB b := by
  letI : Algebra A ↥(igusaFunctionFieldX1C k M D.w) :=
    ((algebraMap k ↥(igusaFunctionFieldX1C k M D.w)).comp (algebraMap A k)).toAlgebra
  haveI : IsScalarTower A k ↥(igusaFunctionFieldX1C k M D.w) := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  exact Algebra.TensorProduct.lift_tmul _ _ _ a b

theorem coe_θ_tmul (hB : ∀ b ∈ B, b ∈ D.W₀) (a : k) (b : ↥B) :
    ((D.θ B hB (a ⊗ₜ[A] b) : ↥(igusaFunctionFieldX1C k M D.w)) : LaurentSeries k) =
      algebraMap k (LaurentSeries k) a * D.gaussRedK ⟨b, hB b b.2⟩ := by
  rw [D.θ_tmul B hB a b]
  rfl

theorem coe_θ_one_tmul (hB : ∀ b ∈ B, b ∈ D.W₀) {b : ↥B} {x y : PowerSeries A} (h : Pres L ((b : ↥K) : LaurentSeries L) x y) :
    ((D.θ B hB ((1 : k) ⊗ₜ[A] b) : ↥(igusaFunctionFieldX1C k M D.w)) : LaurentSeries k) =
      ofPowerSeries ℤ k (x.map (algebraMap A k)) / ofPowerSeries ℤ k (y.map (algebraMap A k)) := by
  rw [D.coe_θ_tmul B hB, map_one, one_mul]
  exact D.gaussRedK_spec h

theorem coeff_coe_ρ (hB : ∀ b ∈ B, b ∈ D.W₀) (b : ↥B) (m : ℤ) :
    ((D.ρ B hB b : ↥(igusaFunctionFieldX1C k M D.w)) : LaurentSeries k).coeff m =
      residueToK k D.hp0 D.hAp ((D.gaussRed (D.inclW₀ B hB b)).coeff m) := rfl

theorem ρ_eq_zero_of_gaussRed_eq_zero (hB : ∀ b ∈ B, b ∈ D.W₀) {b : ↥B} (h : D.gaussRed (D.inclW₀ B hB b) = 0) :
    D.ρ B hB b = 0 := by
  apply Subtype.ext
  change D.gaussRedK (D.inclW₀ B hB b) = 0
  rw [gaussRedK, RingHom.comp_apply, h, map_zero]

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 6400000 in

theorem ker_θ (hB : ∀ b ∈ B, b ∈ D.W₀) :
    RingHom.ker (D.θ B hB).toRingHom = Ideal.span {z | ∃ b, z = (1 : k) ⊗ₜ[A] b ∧ D.θ B hB z = 0} := by
  classical
  refine le_antisymm ?_ (Ideal.span_le.mpr ?_)
  swap
  · rintro _ ⟨b, rfl, h⟩
    exact h
  intro z hz
  rw [RingHom.mem_ker] at hz
  change D.θ B hB z = 0 at hz

  letI : Algebra (ResidueField A) k := (residueToK k D.hp0 D.hAp).toAlgebra
  have hsmul : ∀ (c : ResidueField A) (a : k), c • a = residueToK k D.hp0 D.hAp c * a := fun c a => Algebra.smul_def c a
  let bk := Module.Basis.ofVectorSpace (ResidueField A) k

  let Φ : (Module.Basis.ofVectorSpaceIndex (ResidueField A) k →₀ ↥B) →ₗ[A] k ⊗[A] ↥B :=
    Finsupp.lsum ℕ (fun j => TensorProduct.mk A k ↥B (bk j))
  have hΦ : ∀ f, Φ f = f.sum (fun j b => bk j ⊗ₜ[A] b) := fun f => Finsupp.lsum_apply _ _ _

  let lift : ResidueField A → A := fun c => (Ideal.Quotient.mk_surjective c).choose
  have hlift : ∀ c, residue A (lift c) = c := fun c => (Ideal.Quotient.mk_surjective c).choose_spec

  have hsurj : ∀ z : k ⊗[A] ↥B, ∃ f, Φ f = z := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => exact ⟨0, map_zero Φ⟩
    | tmul a b =>
      refine ⟨(bk.repr a).sum (fun j c => Finsupp.single j (lift c • b)), ?_⟩
      rw [map_finsuppSum]
      simp only [Φ, Finsupp.lsum_single, TensorProduct.mk_apply]
      conv_rhs => rw [← bk.linearCombination_repr a]
      rw [Finsupp.linearCombination_apply, Finsupp.sum, Finsupp.sum, TensorProduct.sum_tmul]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [← TensorProduct.smul_tmul, Algebra.smul_def, hsmul, ← hlift ((bk.repr a) j), residueToK_residue, hlift]
    | add x y hx hy =>
      obtain ⟨f, rfl⟩ := hx
      obtain ⟨g, rfl⟩ := hy
      exact ⟨f + g, map_add Φ f g⟩
  obtain ⟨f, rfl⟩ := hsurj z

  have hρ : ∀ j ∈ f.support, D.ρ B hB (f j) = 0 := by

    have hθ : D.θ B hB (Φ f) = f.sum (fun j b => algebraMap k _ (bk j) * D.ρ B hB b) := by
      rw [hΦ, map_finsuppSum]
      exact Finsupp.sum_congr fun j _ => D.θ_tmul B hB _ _
    rw [hθ] at hz

    have hcoeff : ∀ m : ℤ, ∀ j ∈ f.support, (D.gaussRed (D.inclW₀ B hB (f j))).coeff m = 0 := by
      intro m
      have h0 := congrArg (fun u : ↥(igusaFunctionFieldX1C k M D.w) => (u : LaurentSeries k).coeff m) hz
      simp only [Finsupp.sum, ZeroMemClass.coe_zero] at h0
      rw [AddSubmonoidClass.coe_finsetSum, ← HahnSeries.coeff.addMonoidHom_apply, map_sum] at h0
      simp only [HahnSeries.coeff.addMonoidHom_apply, HahnSeries.coeff_zero] at h0
      have h1 : ∑ j ∈ f.support, (D.gaussRed (D.inclW₀ B hB (f j))).coeff m • bk j = 0 := by
        rw [← h0]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [hsmul, MulMemClass.coe_mul, ← coeff_coe_ρ, mul_comm]
        change _ = (algebraMap k (LaurentSeries k) (bk j) * _).coeff m
        rw [algebraMap_laurentSeries_eq_single, ← HahnSeries.C_apply, HahnSeries.C_mul_eq_smul, HahnSeries.coeff_smul,
          smul_eq_mul]
      exact linearIndependent_iff'.mp bk.linearIndependent f.support _ h1
    intro j hj
    apply D.ρ_eq_zero_of_gaussRed_eq_zero B hB
    ext m
    rw [hcoeff m j hj, HahnSeries.coeff_zero]

  rw [hΦ, Finsupp.sum]
  refine Ideal.sum_mem _ fun j hj => ?_
  have e : bk j ⊗ₜ[A] (f j) = (bk j ⊗ₜ[A] (1 : ↥B)) * ((1 : k) ⊗ₜ[A] f j) := by
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  rw [e]
  refine Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨f j, rfl, ?_⟩)
  rw [D.θ_tmul, map_one, one_mul, hρ j hj]

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 6400000 in

theorem θ_mem_chartRing (hB : ∀ b ∈ B, b ∈ D.W₀) {S : Set ↥K} (hSB : S ⊆ B) (hBS : ∀ b ∈ B, IsIntegral (Algebra.adjoin A S) b)
    (u : ↥(igusaFunctionFieldX1C k M D.w))
    (hSu : ∀ (s : ↥K) (hs : s ∈ S), IsIntegral (Algebra.adjoin k ({u} : Set ↥(igusaFunctionFieldX1C k M D.w)))
      (D.θ B hB ((1 : k) ⊗ₜ[A] (⟨s, hSB hs⟩ : ↥B))))
    (z : k ⊗[A] ↥B) :
    D.θ B hB z ∈ AlgebraicCurve.CurveModel.chartRing k ({u} : Set ↥(igusaFunctionFieldX1C k M D.w)) := by
  classical
  set C := AlgebraicCurve.CurveModel.chartRing k ({u} : Set ↥(igusaFunctionFieldX1C k M D.w)) with hC

  let ψ : ↥B →+* ↥(igusaFunctionFieldX1C k M D.w) :=
    (D.θ B hB).toRingHom.comp (Algebra.TensorProduct.includeRight (R := A) (A := k) (B := ↥B)).toRingHom
  have hψ : ∀ b : ↥B, ψ b = D.θ B hB ((1 : k) ⊗ₜ[A] b) := fun _ => rfl
  have hψρ : ∀ b : ↥B, ψ b = D.ρ B hB b := fun b => by rw [hψ, D.θ_tmul, map_one, one_mul]

  have hRB : Algebra.adjoin A S ≤ B := Algebra.adjoin_le hSB
  let inclRB : ↥(Algebra.adjoin A S) →+* ↥B := (Subalgebra.inclusion hRB).toRingHom
  have hRC : ∀ r : ↥(Algebra.adjoin A S), ψ (inclRB r) ∈ C := by
    rintro ⟨r, hr⟩
    induction hr using Algebra.adjoin_induction with
    | mem x hx =>
      change D.θ B hB ((1 : k) ⊗ₜ[A] (⟨x, hSB hx⟩ : ↥B)) ∈ C
      rw [hC, AlgebraicCurve.CurveModel.mem_chartRing_iff]
      exact hSu x hx
    | algebraMap a =>
      change ψ (algebraMap A ↥B a) ∈ C
      rw [hψρ, D.ρ_algebraMap]
      exact Subalgebra.algebraMap_mem _ _
    | add x y hx hy ihx ihy =>
      have e : inclRB ⟨x + y, add_mem hx hy⟩ = inclRB ⟨x, hx⟩ + inclRB ⟨y, hy⟩ := rfl
      rw [e, RingHom.map_add]
      exact Subalgebra.add_mem _ ihx ihy
    | mul x y hx hy ihx ihy =>
      have e : inclRB ⟨x * y, mul_mem hx hy⟩ = inclRB ⟨x, hx⟩ * inclRB ⟨y, hy⟩ := rfl
      rw [e, RingHom.map_mul]
      exact Subalgebra.mul_mem _ ihx ihy
  let φ : ↥(Algebra.adjoin A S) →+* ↥C := (ψ.comp inclRB).codRestrict C hRC

  have key : ∀ b : ↥B, D.ρ B hB b ∈ C := by
    intro b
    obtain ⟨P, hPm, hPb⟩ := hBS b b.2

    have hPB : P.eval₂ inclRB b = 0 := by
      apply Subtype.val_injective
      rw [show ((P.eval₂ inclRB b : ↥B) : ↥K) = (Subalgebra.val B).toRingHom (P.eval₂ inclRB b) from rfl,
        Polynomial.hom_eval₂]
      exact hPb
    have hint : IsIntegral ↥C (ψ b) := by
      refine ⟨P.map φ, hPm.map φ, ?_⟩
      rw [Polynomial.eval₂_map, show (algebraMap ↥C ↥(igusaFunctionFieldX1C k M D.w)).comp φ = ψ.comp inclRB from
          RingHom.ext fun _ => rfl,
        ← Polynomial.hom_eval₂, hPB, RingHom.map_zero]
    haveI : Algebra.IsIntegral ↥(Algebra.adjoin k ({u} : Set ↥(igusaFunctionFieldX1C k M D.w))) ↥C :=
      IsIntegralClosure.isIntegral_algebra ↥(Algebra.adjoin k ({u} : Set ↥(igusaFunctionFieldX1C k M D.w)))
        (A := ↥C) ↥(igusaFunctionFieldX1C k M D.w)
    rw [← hψρ, hC, AlgebraicCurve.CurveModel.mem_chartRing_iff]
    exact isIntegral_trans (R := ↥(Algebra.adjoin k ({u} : Set ↥(igusaFunctionFieldX1C k M D.w)))) (A := ↥C) (ψ b) hint

  induction z using TensorProduct.induction_on with
  | zero => rw [map_zero]; exact Subalgebra.zero_mem _
  | tmul a b =>
    rw [D.θ_tmul]
    exact Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ a) (key b)
  | add x y hx hy => rw [map_add]; exact Subalgebra.add_mem _ hx hy

def θChart (hB : ∀ b ∈ B, b ∈ D.W₀) {S : Set ↥K} (hSB : S ⊆ B) (hBS : ∀ b ∈ B, IsIntegral (Algebra.adjoin A S) b)
    (u : ↥(igusaFunctionFieldX1C k M D.w))
    (hSu : ∀ (s : ↥K) (hs : s ∈ S), IsIntegral (Algebra.adjoin k ({u} : Set ↥(igusaFunctionFieldX1C k M D.w)))
      (D.θ B hB ((1 : k) ⊗ₜ[A] (⟨s, hSB hs⟩ : ↥B)))) :
    k ⊗[A] ↥B →ₐ[k] ↥(AlgebraicCurve.CurveModel.chartRing k ({u} : Set ↥(igusaFunctionFieldX1C k M D.w))) :=
  (D.θ B hB).codRestrict _ (D.θ_mem_chartRing B hB hSB hBS u hSu)

@[scoped simp] theorem coe_θChart (hB : ∀ b ∈ B, b ∈ D.W₀) {S : Set ↥K} (hSB : S ⊆ B) (hBS : ∀ b ∈ B, IsIntegral (Algebra.adjoin A S) b)
    (u : ↥(igusaFunctionFieldX1C k M D.w))
    (hSu : ∀ (s : ↥K) (hs : s ∈ S), IsIntegral (Algebra.adjoin k ({u} : Set ↥(igusaFunctionFieldX1C k M D.w)))
      (D.θ B hB ((1 : k) ⊗ₜ[A] (⟨s, hSB hs⟩ : ↥B)))) (z : k ⊗[A] ↥B) :
    (D.θChart B hB hSB hBS u hSu z : ↥(igusaFunctionFieldX1C k M D.w)) = D.θ B hB z := rfl

theorem ker_θChart (hB : ∀ b ∈ B, b ∈ D.W₀) {S : Set ↥K} (hSB : S ⊆ B) (hBS : ∀ b ∈ B, IsIntegral (Algebra.adjoin A S) b)
    (u : ↥(igusaFunctionFieldX1C k M D.w))
    (hSu : ∀ (s : ↥K) (hs : s ∈ S), IsIntegral (Algebra.adjoin k ({u} : Set ↥(igusaFunctionFieldX1C k M D.w)))
      (D.θ B hB ((1 : k) ⊗ₜ[A] (⟨s, hSB hs⟩ : ↥B)))) :
    RingHom.ker (D.θChart B hB hSB hBS u hSu).toRingHom =
      Ideal.span {z | ∃ b, z = (1 : k) ⊗ₜ[A] b ∧ D.θChart B hB hSB hBS u hSu z = 0} := by
  have hk : RingHom.ker (D.θChart B hB hSB hBS u hSu).toRingHom = RingHom.ker (D.θ B hB).toRingHom := by
    ext z
    simp only [RingHom.mem_ker, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom]
    rw [← Subtype.coe_inj, coe_θChart]
    rfl
  have hs : {z | ∃ b, z = (1 : k) ⊗ₜ[A] b ∧ D.θChart B hB hSB hBS u hSu z = 0} =
      {z | ∃ b, z = (1 : k) ⊗ₜ[A] b ∧ D.θ B hB z = 0} := by
    ext z
    simp only [Set.mem_setOf_eq]
    refine exists_congr fun b => and_congr_right fun _ => ?_
    rw [← Subtype.coe_inj, coe_θChart]
    rfl
  rw [hk, hs]
  exact D.ker_θ B hB

end Setup
p2m_reactivate "P2MW.S_ModularCurve_XOneP_coe_mem_adjoin_gaussReductions_chartAlg_igusaFunctionFieldX1C_x1_mul.ModularCurve.GaussRedCore.Setup"

end ModularCurve.GaussRedCore
p2m_reactivate "P2MW.S_ModularCurve_XOneP_coe_mem_adjoin_gaussReductions_chartAlg_igusaFunctionFieldX1C_x1_mul.ModularCurve.GaussRedCore.Setup P2MW.S_ModularCurve_XOneP_coe_mem_adjoin_gaussReductions_chartAlg_igusaFunctionFieldX1C_x1_mul.ModularCurve P2MW.S_ModularCurve_XOneP_coe_mem_adjoin_gaussReductions_chartAlg_igusaFunctionFieldX1C_x1_mul.ModularCurve.GaussRedCore"
p2m_reactivate "P2MW.S_ModularCurve_XOneP_coe_mem_adjoin_gaussReductions_chartAlg_igusaFunctionFieldX1C_x1_mul.ModularCurve.GaussRedCore.Setup P2MW.S_ModularCurve_XOneP_coe_mem_adjoin_gaussReductions_chartAlg_igusaFunctionFieldX1C_x1_mul.ModularCurve"

end
p2m_reactivate "P2MW.S_ModularCurve_XOneP_coe_mem_adjoin_gaussReductions_chartAlg_igusaFunctionFieldX1C_x1_mul.ModularCurve.GaussRedCore.Setup P2MW.S_ModularCurve_XOneP_coe_mem_adjoin_gaussReductions_chartAlg_igusaFunctionFieldX1C_x1_mul.ModularCurve P2MW.S_ModularCurve_XOneP_coe_mem_adjoin_gaussReductions_chartAlg_igusaFunctionFieldX1C_x1_mul.ModularCurve.GaussRedCore"

noncomputable section

p2m_open "HahnSeries IsLocalRing ModularCurve~coeffMap_ofPowerSeries P2MW.S_ModularCurve_XOneP_coe_mem_adjoin_gaussReductions_chartAlg_igusaFunctionFieldX1C_x1_mul.ModularCurve P2MW.S_ModularCurve_XOneP_coe_mem_adjoin_gaussReductions_chartAlg_igusaFunctionFieldX1C_x1_mul.ModularCurve.GaussRedCore"
open scoped TensorProduct IntermediateField

namespace ModularCurve
p2m_export "ModularCurve" "intSeriesC intFormRatiosC div_mem_qExpFunctionFieldC x1FunctionFieldC x1FunctionField jNum jq coeffMap coeffMap_coeff coeffMap_single algebraMap_laurentSeries_eq_single coeffEmb laurentBaseChange IntegralWeightOneForm IntegralWeightOneForm.hasseRootFn igusaFunctionFieldX1C x1FunctionFieldC_le_igusaFunctionFieldX1C hasseRootFn_mem_igusaFunctionFieldX1C jqModC jqModC_rat map_jqModC XOneP.exists_valuationSubring_pair_x1_mul finiteDimensional_adjoin_of_coe_eq_coeffEmb_jq_of_eq_laurentBaseChange transcendental_of_coe_eq_coeffEmb_jq"
namespace SURJ0Aux
p2m_open "ModularCurve~coeffMap_ofPowerSeries"

section Generic

variable {k : Type} [Field k] {Ω : Type} [Field Ω] [Algebra k Ω]

open scoped IntermediateField.algebraAdjoinAdjoin in

theorem mem_adjoin_of_isIntegral_of_dvr (S : Set Ω) [IsNoetherianRing ↥(Algebra.adjoin k S)]
    [Ring.DimensionLEOne ↥(Algebra.adjoin k S)]
    (hdvr : ∀ (𝔪 : Ideal ↥(Algebra.adjoin k S)) [𝔪.IsMaximal], IsDiscreteValuationRing (Localization.AtPrime 𝔪))
    {z : Ω} (hzF : z ∈ IntermediateField.adjoin k S) (hz : IsIntegral ↥(Algebra.adjoin k S) z) :
    z ∈ Algebra.adjoin k S := by
  haveI : IsDedekindDomainDvr ↥(Algebra.adjoin k S) :=
    { is_dvr_at_nonzero_prime := fun P hP hPp => by
        haveI := hPp
        haveI : P.IsMaximal := hPp.isMaximal hP
        exact hdvr P }
  have hz' : IsIntegral ↥(Algebra.adjoin k S) (⟨z, hzF⟩ : ↥(IntermediateField.adjoin k S)) := by
    refine (isIntegral_algHom_iff
      (IsScalarTower.toAlgHom ↥(Algebra.adjoin k S) ↥(IntermediateField.adjoin k S) Ω) ?_).mp hz
    exact Subtype.val_injective
  obtain ⟨r, hr⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral hz'
  have := congrArg Subtype.val hr
  rw [IntermediateField.algebraAdjoinAdjoin.coe_algebraMap] at this
  change (r : Ω) = z at this
  rw [← this]
  exact r.2

end Generic
p2m_reactivate "P2MW.S_ModularCurve_XOneP_coe_mem_adjoin_gaussReductions_chartAlg_igusaFunctionFieldX1C_x1_mul.ModularCurve.GaussRedCore.Setup P2MW.S_ModularCurve_XOneP_coe_mem_adjoin_gaussReductions_chartAlg_igusaFunctionFieldX1C_x1_mul.ModularCurve P2MW.S_ModularCurve_XOneP_coe_mem_adjoin_gaussReductions_chartAlg_igusaFunctionFieldX1C_x1_mul.ModularCurve.GaussRedCore"

section ChartLe

variable {R : Type} [CommRing R] {F : Type} [Field F] [Algebra R F]

theorem chartAlg_le_valuationSubring (S : Set F) (V : ValuationSubring F)
    (hR : ∀ a : R, algebraMap R F a ∈ V) (hS : S ⊆ V) :
    ∀ b ∈ AlgebraicCurve.TwoChartIntegralModel.chartAlg R F S, b ∈ V := by
  intro b hb
  rw [AlgebraicCurve.TwoChartIntegralModel.mem_chartAlg_iff] at hb

  let V' : Subalgebra R F :=
    { V.toSubring with
      algebraMap_mem' := hR }
  have hle : Algebra.adjoin R S ≤ V' := Algebra.adjoin_le hS
  let φ : ↥(Algebra.adjoin R S) →+* ↥V :=
    { toFun := fun r => ⟨r, hle r.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  have hbV : IsIntegral ↥V b := hb.map_of_comp_eq φ (RingHom.id F) (by ext; rfl)
  obtain ⟨v, hv⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral hbV
  rw [← hv]
  exact v.2

end ChartLe
p2m_reactivate "P2MW.S_ModularCurve_XOneP_coe_mem_adjoin_gaussReductions_chartAlg_igusaFunctionFieldX1C_x1_mul.ModularCurve.GaussRedCore.Setup P2MW.S_ModularCurve_XOneP_coe_mem_adjoin_gaussReductions_chartAlg_igusaFunctionFieldX1C_x1_mul.ModularCurve P2MW.S_ModularCurve_XOneP_coe_mem_adjoin_gaussReductions_chartAlg_igusaFunctionFieldX1C_x1_mul.ModularCurve.GaussRedCore"

section JPres

variable {A : Type} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  {L : Type} [Field L] [CharZero L] [Algebra A L] [IsFractionRing A L]

theorem pres_jq :
    Pres L (coeffEmb L jq) (jNum.map (Int.castRingHom A)) PowerSeries.X := by
  refine ⟨by rw [PowerSeries.map_X]; exact PowerSeries.X_ne_zero, ?_⟩
  have hj : coeffEmb L jq = jqModC L := by
    rw [coeffEmb, ← jqModC_rat]
    exact map_jqModC (algebraMap ℚ L)
  rw [hj, toL, toL, PowerSeries.map_X, ofPowerSeries_X, ← RingHom.comp_apply (PowerSeries.map _),
    ← PowerSeries.map_comp, RingHom.ext_int ((algebraMap A L).comp (Int.castRingHom A)) (Int.castRingHom L),
    jqModC, mul_comm, ← mul_assoc, single_mul_single]
  simp

variable (k : Type) [Field k] [Algebra A k]

omit [IsDomain A] [IsDiscreteValuationRing A] in

theorem red_pres_jq :
    ofPowerSeries ℤ k ((jNum.map (Int.castRingHom A)).map (algebraMap A k)) /
      ofPowerSeries ℤ k ((PowerSeries.X : PowerSeries A).map (algebraMap A k)) = jqModC k := by
  rw [PowerSeries.map_X, ofPowerSeries_X, ← RingHom.comp_apply (PowerSeries.map _), ← PowerSeries.map_comp,
    RingHom.ext_int ((algebraMap A k).comp (Int.castRingHom A)) (Int.castRingHom k),
    div_eq_iff (single_ne_zero one_ne_zero), jqModC, mul_comm (single (-1 : ℤ) (1 : k)), mul_assoc,
    single_mul_single]
  simp

end JPres
p2m_reactivate "P2MW.S_ModularCurve_XOneP_coe_mem_adjoin_gaussReductions_chartAlg_igusaFunctionFieldX1C_x1_mul.ModularCurve.GaussRedCore.Setup P2MW.S_ModularCurve_XOneP_coe_mem_adjoin_gaussReductions_chartAlg_igusaFunctionFieldX1C_x1_mul.ModularCurve P2MW.S_ModularCurve_XOneP_coe_mem_adjoin_gaussReductions_chartAlg_igusaFunctionFieldX1C_x1_mul.ModularCurve.GaussRedCore"

section Chart

variable {A : Type} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  {L : Type} [Field L] [Algebra A L] [IsFractionRing A L]
  {K : IntermediateField L (LaurentSeries L)} [Algebra A ↥K] [IsScalarTower A L ↥K]
  {k : Type} [Field k] [Algebra A k] {p : ℕ} [Fact p.Prime] [CharP k p] {M : ℕ}
  (D : Setup A L K k p M) (B : Subalgebra A ↥K)

abbrev Red : Set (LaurentSeries k) := {r : LaurentSeries k | ∃ (b : ↥(B)) (x y : PowerSeries A),
            y.map (IsLocalRing.residue A) ≠ 0 ∧
            (((b : ↥K) : LaurentSeries L)) * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap A L))
              = HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap A L)) ∧
            r = HahnSeries.ofPowerSeries ℤ k (x.map (algebraMap A k)) /
                  HahnSeries.ofPowerSeries ℤ k (y.map (algebraMap A k))}

abbrev ρK (hB : ∀ b ∈ B, b ∈ D.W₀) : ↥B →+* LaurentSeries k := D.gaussRedK.comp (D.inclW₀ B hB)

theorem red_eq_range_ρK (hB : ∀ b ∈ B, b ∈ D.W₀) :
    Red (A := A) (L := L) (K := K) (k := k) B = Set.range (ρK D B hB) := by
  ext r
  constructor
  · rintro ⟨b, x, y, hy, hxy, rfl⟩
    exact ⟨b, D.gaussRedK_spec (f := ⟨b, hB b b.2⟩) ⟨hy, hxy⟩⟩
  · rintro ⟨b, rfl⟩
    obtain ⟨x, y, h⟩ := (D.mem_W₀_iff (b : ↥K)).mp (hB b b.2)
    exact ⟨b, x, y, h.1, h.2, D.gaussRedK_spec (f := ⟨b, hB b b.2⟩) h⟩

theorem ρK_algebraMap (hB : ∀ b ∈ B, b ∈ D.W₀) (a : A) :
    ρK D B hB (algebraMap A ↥B a) = algebraMap k (LaurentSeries k) (algebraMap A k a) :=
  D.gaussRedK_algebraMap a

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 6400000 in

theorem isNoetherianRing_and_dimensionLEOne_adjoin_red (hB : ∀ b ∈ B, b ∈ D.W₀) (s : ↥B)
    (hfin : letI := (Polynomial.aeval (R := A) s).toRingHom.toAlgebra; Module.Finite (Polynomial A) ↥B)
    (htr : Transcendental k (ρK D B hB s)) :
    IsNoetherianRing ↥(Algebra.adjoin k (Red (A := A) (L := L) (K := K) (k := k) B)) ∧
      Ring.DimensionLEOne ↥(Algebra.adjoin k (Red (A := A) (L := L) (K := K) (k := k) B)) := by
  classical
  rw [red_eq_range_ρK D B hB]

  have hρdef : ∀ b, ρK D B hB b = D.gaussRedK ⟨b, hB b b.2⟩ := fun _ => rfl
  let R : Subalgebra k (LaurentSeries k) := Algebra.adjoin k (Set.range (ρK D B hB))

  letI algAX : Algebra (Polynomial A) ↥B := (Polynomial.aeval (R := A) s).toRingHom.toAlgebra
  have hsmul : ∀ (P : Polynomial A) (b : ↥B), P • b = Polynomial.aeval s P * b := fun P b => Algebra.smul_def P b
  obtain ⟨G, hG⟩ := Module.Finite.fg_top (R := Polynomial A) (M := ↥B)

  have hρP : ∀ P : Polynomial A, ρK D B hB (Polynomial.aeval s P) = Polynomial.aeval (ρK D B hB s) (P.map (algebraMap A k)) := by
    intro P
    rw [Polynomial.aeval_def, Polynomial.aeval_def, Polynomial.eval₂_map, Polynomial.hom_eval₂]
    congr 1
    exact RingHom.ext fun a => ρK_algebraMap D B hB a
  let T : Subalgebra k (LaurentSeries k) := Algebra.adjoin k (insert (ρK D B hB s) ((ρK D B hB : ↥B → LaurentSeries k) '' (G : Set ↥B)))
  have hTR : T = R := by
    apply le_antisymm
    · apply Algebra.adjoin_le
      rintro _ (rfl | ⟨g, -, rfl⟩)
      · exact Algebra.subset_adjoin ⟨s, rfl⟩
      · exact Algebra.subset_adjoin ⟨g, rfl⟩
    · apply Algebra.adjoin_le
      rintro _ ⟨b, rfl⟩
      have hb : b ∈ Submodule.span (Polynomial A) (G : Set ↥B) := by rw [hG]; exact Submodule.mem_top
      induction hb using Submodule.span_induction with
      | mem g hg => exact Algebra.subset_adjoin (Set.mem_insert_of_mem _ ⟨g, hg, rfl⟩)
      | zero => rw [map_zero]; exact Subalgebra.zero_mem _
      | add x y _ _ hx hy => rw [map_add]; exact Subalgebra.add_mem _ hx hy
      | smul P x _ hx =>
        rw [hsmul, map_mul, hρP]
        refine Subalgebra.mul_mem _ ?_ hx
        exact Algebra.adjoin_mono (Set.singleton_subset_iff.mpr (Set.mem_insert (ρK D B hB s) _))
          (Polynomial.aeval_mem_adjoin_singleton k (ρK D B hB s))

  have hNoeth : IsNoetherianRing ↥R := by
    rw [← hTR]
    haveI : Algebra.FiniteType k ↥T :=
      Algebra.FiniteType.adjoin_of_finite (Set.toFinite _)
    exact Algebra.FiniteType.isNoetherianRing k ↥T
  refine ⟨hNoeth, ?_⟩

  let ku : Subalgebra k (LaurentSeries k) := Algebra.adjoin k {ρK D B hB s}
  have hkuR : ku ≤ R := Algebra.adjoin_mono (Set.singleton_subset_iff.mpr ⟨s, rfl⟩)
  letI algKuR : Algebra ↥ku ↥R := (Subalgebra.inclusion hkuR).toRingHom.toAlgebra
  haveI : IsScalarTower k ↥ku ↥R := IsScalarTower.of_algebraMap_eq (fun _ => rfl)

  have hinj : Function.Injective (Polynomial.aeval (R := k) (ρK D B hB s)) := transcendental_iff_injective.mp htr
  let e : Polynomial k ≃ₐ[k] ↥ku :=
    (AlgEquiv.ofInjective (Polynomial.aeval (ρK D B hB s)) hinj).trans
      (Subalgebra.equivOfEq _ _ (Algebra.adjoin_singleton_eq_range_aeval k (ρK D B hB s)).symm)
  haveI : IsPrincipalIdealRing ↥ku := IsPrincipalIdealRing.of_surjective e.toRingHom e.surjective

  haveI : IsScalarTower ↥ku ↥R (LaurentSeries k) := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let u' : ↥ku := ⟨ρK D B hB s, Algebra.self_mem_adjoin_singleton k (ρK D B hB s)⟩
  let φ : Polynomial A →+* ↥ku := (Polynomial.aeval u').toRingHom.comp (Polynomial.mapRingHom (algebraMap A k))
  have hφ : (algebraMap ↥ku (LaurentSeries k)).comp φ = (ρK D B hB).comp (algebraMap (Polynomial A) ↥B) := by
    apply Polynomial.ringHom_ext
    · intro a
      change ((Polynomial.aeval u' ((Polynomial.C a).map (algebraMap A k)) : ↥ku) : LaurentSeries k) =
        ρK D B hB (Polynomial.aeval s (Polynomial.C a))
      rw [Polynomial.map_C, Polynomial.aeval_C, Polynomial.aeval_C, ρK_algebraMap]
      rfl
    · change ((Polynomial.aeval u' ((Polynomial.X : Polynomial A).map (algebraMap A k)) : ↥ku) : LaurentSeries k) =
        ρK D B hB (Polynomial.aeval s (Polynomial.X : Polynomial A))
      rw [Polynomial.map_X, Polynomial.aeval_X, Polynomial.aeval_X]
  haveI : Algebra.IsIntegral (Polynomial A) ↥B := Algebra.IsIntegral.of_finite _ _
  have hgen : ∀ b : ↥B, IsIntegral ↥ku (ρK D B hB b) := fun b =>
    (Algebra.IsIntegral.isIntegral (R := Polynomial A) b).map_of_comp_eq φ (ρK D B hB) hφ
  have hRint : ∀ x ∈ R, IsIntegral ↥ku x := by
    intro x hx
    induction hx using Algebra.adjoin_induction with
    | mem x hx =>
      obtain ⟨b, rfl⟩ := hx
      exact hgen b
    | algebraMap c => exact isIntegral_algebraMap (A := LaurentSeries k) (x := algebraMap k ↥ku c)
    | add x y _ _ ihx ihy => exact ihx.add ihy
    | mul x y _ _ ihx ihy => exact ihx.mul ihy
  haveI hint : Algebra.IsIntegral ↥ku ↥R :=
    ⟨fun r => (isIntegral_algHom_iff (IsScalarTower.toAlgHom ↥ku ↥R (LaurentSeries k))
      Subtype.val_injective).mp (hRint r r.2)⟩
  refine ⟨fun {P} hP hPp => ?_⟩
  have hq : (P.comap (algebraMap ↥ku ↥R)) ≠ ⊥ := fun h => hP (Ideal.eq_bot_of_comap_eq_bot h)
  haveI : (P.comap (algebraMap ↥ku ↥R)).IsMaximal := Ideal.IsPrime.isMaximal inferInstance hq
  exact Ideal.isMaximal_of_isIntegral_of_isMaximal_comap (R := ↥ku) P inferInstance

theorem coe_mem_adjoinField_red (hB : ∀ b ∈ B, b ∈ D.W₀)
    (h6c : ∀ r₀ : LaurentSeries (ResidueField A),
      r₀ ∈ igusaFunctionFieldX1C (ResidueField A) M (overResidueField k D.hp0 D.hAp D.w) →
      ∃ (f : ↥K) (x y : PowerSeries A), y.map (residue A) ≠ 0 ∧
        (f : LaurentSeries L) * ofPowerSeries ℤ L (y.map (algebraMap A L)) = ofPowerSeries ℤ L (x.map (algebraMap A L)) ∧
        toκ x / toκ y = r₀)
    (hfrac : ∀ f : ↥D.W₀, ∃ a b : ↥B, D.gaussRed ⟨b, hB b b.2⟩ ≠ 0 ∧ ((f : ↥K) : ↥K) * (b : ↥K) = (a : ↥K))
    (z : ↥(igusaFunctionFieldX1C k M D.w)) :
    (z : LaurentSeries k) ∈ IntermediateField.adjoin k (Red (A := A) (L := L) (K := K) (k := k) B) := by
  set F := IntermediateField.adjoin k (Red (A := A) (L := L) (K := K) (k := k) B) with hF

  have hRedB : ∀ b : ↥B, D.gaussRedK ⟨b, hB b b.2⟩ ∈ Red (A := A) (L := L) (K := K) (k := k) B := by
    intro b
    obtain ⟨x, y, h⟩ := (D.mem_W₀_iff (b : ↥K)).mp (hB b b.2)
    exact ⟨b, x, y, h.1, h.2, D.gaussRedK_spec (f := ⟨b, hB b b.2⟩) h⟩

  have key : ∀ r₀ : LaurentSeries (ResidueField A),
      r₀ ∈ igusaFunctionFieldX1C (ResidueField A) M (overResidueField k D.hp0 D.hAp D.w) →
      coeffMap (residueToK k D.hp0 D.hAp) r₀ ∈ F := by
    intro r₀ hr₀
    obtain ⟨f, x, y, hy, hfy, hr⟩ := h6c r₀ hr₀
    have hfW : f ∈ D.W₀ := (D.mem_W₀_iff f).mpr ⟨x, y, hy, hfy⟩
    have hgf : D.gaussRed ⟨f, hfW⟩ = r₀ := by rw [D.gaussRed_spec (f := ⟨f, hfW⟩) ⟨hy, hfy⟩]; exact hr
    obtain ⟨a, b, hb0, hfab⟩ := hfrac ⟨f, hfW⟩
    have hW : (⟨f, hfW⟩ : ↥D.W₀) * ⟨b, hB b b.2⟩ = ⟨a, hB a a.2⟩ := Subtype.ext hfab
    have e := congrArg D.gaussRed hW
    rw [map_mul, hgf] at e
    have hr₀ : r₀ = D.gaussRed ⟨a, hB a a.2⟩ / D.gaussRed ⟨b, hB b b.2⟩ := by
      rw [eq_div_iff hb0]; exact e
    rw [hr₀, map_div₀]
    change D.gaussRedK ⟨a, hB a a.2⟩ / D.gaussRedK ⟨b, hB b b.2⟩ ∈ F
    exact div_mem (IntermediateField.subset_adjoin k _ (hRedB a)) (IntermediateField.subset_adjoin k _ (hRedB b))

  have hle : igusaFunctionFieldX1C k M D.w ≤ F := by
    change IntermediateField.adjoin k ((x1FunctionFieldC k M : Set (LaurentSeries k)) ∪ {D.w.hasseRootFn}) ≤ F
    rw [IntermediateField.adjoin_le_iff]
    rintro r (hr | hr)
    ·
      have hx1 : x1FunctionFieldC k M ≤ F := by
        change IntermediateField.adjoin k (intFormRatiosC k (CongruenceSubgroup.Gamma1 M)) ≤ F
        rw [IntermediateField.adjoin_le_iff]
        rintro _ ⟨wt, f, g, pf, pg, hf, hg, hg0, rfl⟩
        have hg0' : intSeriesC (ResidueField A) pg ≠ 0 := by
          intro h0
          apply hg0
          rw [← coeffMap_residueToK_intSeriesC k D.hp0 D.hAp, h0, map_zero]
        have hmem : intSeriesC (ResidueField A) pf / intSeriesC (ResidueField A) pg ∈
            igusaFunctionFieldX1C (ResidueField A) M (overResidueField k D.hp0 D.hAp D.w) :=
          x1FunctionFieldC_le_igusaFunctionFieldX1C _ _ _ (div_mem_qExpFunctionFieldC f g hf hg hg0')
        have := key _ hmem
        rwa [map_div₀, coeffMap_residueToK_intSeriesC, coeffMap_residueToK_intSeriesC] at this
      exact hx1 hr
    · rw [Set.mem_singleton_iff] at hr
      subst hr
      have hmem := hasseRootFn_mem_igusaFunctionFieldX1C (ResidueField A) M (overResidueField k D.hp0 D.hAp D.w)
      have := key _ hmem
      rw [IntegralWeightOneForm.hasseRootFn, map_inv₀, coeffMap_residueToK_intSeriesC] at this
      exact this
  exact hle z.2

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 6400000 in

theorem coe_mem_adjoin_red_of_mem_chartRing (hB : ∀ b ∈ B, b ∈ D.W₀)
    (h6c : ∀ r₀ : LaurentSeries (ResidueField A),
      r₀ ∈ igusaFunctionFieldX1C (ResidueField A) M (overResidueField k D.hp0 D.hAp D.w) →
      ∃ (f : ↥K) (x y : PowerSeries A), y.map (residue A) ≠ 0 ∧
        (f : LaurentSeries L) * ofPowerSeries ℤ L (y.map (algebraMap A L)) = ofPowerSeries ℤ L (x.map (algebraMap A L)) ∧
        toκ x / toκ y = r₀)
    (hfrac : ∀ f : ↥D.W₀, ∃ a b : ↥B, D.gaussRed ⟨b, hB b b.2⟩ ≠ 0 ∧ ((f : ↥K) : ↥K) * (b : ↥K) = (a : ↥K))
    (s : ↥B) (hfin : letI := (Polynomial.aeval (R := A) s).toRingHom.toAlgebra; Module.Finite (Polynomial A) ↥B)
    (htr : Transcendental k (ρK D B hB s))
    (hdvr : ∀ (𝔪 : Ideal ↥(Algebra.adjoin k (Red (A := A) (L := L) (K := K) (k := k) B))) [𝔪.IsMaximal],
      IsDiscreteValuationRing (Localization.AtPrime 𝔪))
    (u : ↥(igusaFunctionFieldX1C k M D.w)) (hu : (u : LaurentSeries k) ∈ Red (A := A) (L := L) (K := K) (k := k) B)
    (z : ↥(igusaFunctionFieldX1C k M D.w))
    (hz : z ∈ AlgebraicCurve.CurveModel.chartRing k ({u} : Set ↥(igusaFunctionFieldX1C k M D.w))) :
    (z : LaurentSeries k) ∈ Algebra.adjoin k (Red (A := A) (L := L) (K := K) (k := k) B) := by
  obtain ⟨hN, hD⟩ := isNoetherianRing_and_dimensionLEOne_adjoin_red D B hB s hfin htr
  haveI := hN
  haveI := hD
  set R := Algebra.adjoin k (Red (A := A) (L := L) (K := K) (k := k) B) with hR

  rw [AlgebraicCurve.CurveModel.mem_chartRing_iff] at hz
  have hle : ∀ x ∈ Algebra.adjoin k ({u} : Set ↥(igusaFunctionFieldX1C k M D.w)), (x : LaurentSeries k) ∈ R := by
    intro x hx
    induction hx using Algebra.adjoin_induction with
    | mem x hx =>
      rw [Set.mem_singleton_iff] at hx
      subst hx
      exact Algebra.subset_adjoin hu
    | algebraMap c => exact Subalgebra.algebraMap_mem R c
    | add x y _ _ hx hy => rw [AddMemClass.coe_add]; exact Subalgebra.add_mem R hx hy
    | mul x y _ _ hx hy => rw [MulMemClass.coe_mul]; exact Subalgebra.mul_mem R hx hy
  let φ : ↥(Algebra.adjoin k ({u} : Set ↥(igusaFunctionFieldX1C k M D.w))) →+* ↥R :=
    { toFun := fun x => ⟨((x : ↥(igusaFunctionFieldX1C k M D.w)) : LaurentSeries k), hle x x.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  have hz' : IsIntegral ↥R (z : LaurentSeries k) :=
    hz.map_of_comp_eq φ ((igusaFunctionFieldX1C k M D.w).val : ↥(igusaFunctionFieldX1C k M D.w) →+* LaurentSeries k)
      (by ext x; rfl)
  exact mem_adjoin_of_isIntegral_of_dvr _ hdvr (coe_mem_adjoinField_red D B hB h6c hfrac z) hz'

end Chart
p2m_reactivate "P2MW.S_ModularCurve_XOneP_coe_mem_adjoin_gaussReductions_chartAlg_igusaFunctionFieldX1C_x1_mul.ModularCurve.GaussRedCore.Setup P2MW.S_ModularCurve_XOneP_coe_mem_adjoin_gaussReductions_chartAlg_igusaFunctionFieldX1C_x1_mul.ModularCurve P2MW.S_ModularCurve_XOneP_coe_mem_adjoin_gaussReductions_chartAlg_igusaFunctionFieldX1C_x1_mul.ModularCurve.GaussRedCore"

end ModularCurve.SURJ0Aux
p2m_reactivate "P2MW.S_ModularCurve_XOneP_coe_mem_adjoin_gaussReductions_chartAlg_igusaFunctionFieldX1C_x1_mul.ModularCurve.GaussRedCore.Setup P2MW.S_ModularCurve_XOneP_coe_mem_adjoin_gaussReductions_chartAlg_igusaFunctionFieldX1C_x1_mul.ModularCurve P2MW.S_ModularCurve_XOneP_coe_mem_adjoin_gaussReductions_chartAlg_igusaFunctionFieldX1C_x1_mul.ModularCurve.GaussRedCore"
p2m_reactivate "P2MW.S_ModularCurve_XOneP_coe_mem_adjoin_gaussReductions_chartAlg_igusaFunctionFieldX1C_x1_mul.ModularCurve.GaussRedCore.Setup P2MW.S_ModularCurve_XOneP_coe_mem_adjoin_gaussReductions_chartAlg_igusaFunctionFieldX1C_x1_mul.ModularCurve P2MW.S_ModularCurve_XOneP_coe_mem_adjoin_gaussReductions_chartAlg_igusaFunctionFieldX1C_x1_mul.ModularCurve.GaussRedCore"

open ModularCurve.SURJ0Aux in
set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 6400000 in
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
    (w : ModularCurve.IntegralWeightOneForm k M) :
    (∀ z : ↥(ModularCurve.igusaFunctionFieldX1C k M w),
      ((z : ↥(ModularCurve.igusaFunctionFieldX1C k M w)) : LaurentSeries k) ∈
        IntermediateField.adjoin k {r : LaurentSeries k |
          ∃ (b : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)) (x y : PowerSeries A),
            y.map (IsLocalRing.residue A) ≠ 0 ∧
            (((b : ↥K) : LaurentSeries L)) * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap A L))
              = HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap A L)) ∧
            r = HahnSeries.ofPowerSeries ℤ k (x.map (algebraMap A k)) /
                  HahnSeries.ofPowerSeries ℤ k (y.map (algebraMap A k))}) ∧
    (∀ z : ↥(ModularCurve.igusaFunctionFieldX1C k M w),
      ((z : ↥(ModularCurve.igusaFunctionFieldX1C k M w)) : LaurentSeries k) ∈
        IntermediateField.adjoin k {r : LaurentSeries k |
          ∃ (b : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A (↥K) j)) (x y : PowerSeries A),
            y.map (IsLocalRing.residue A) ≠ 0 ∧
            (((b : ↥K) : LaurentSeries L)) * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap A L))
              = HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap A L)) ∧
            r = HahnSeries.ofPowerSeries ℤ k (x.map (algebraMap A k)) /
                  HahnSeries.ofPowerSeries ℤ k (y.map (algebraMap A k))}) := by
  classical

  have hp0 : (p : A) ≠ 0 := fun h => (Fact.out : p.Prime).ne_zero (by
    have := congrArg (algebraMap A L) h
    rw [map_natCast, map_zero] at this
    exact_mod_cast this)
  obtain ⟨W₀, W₁, h1, h2, -, h4, -, h6, h6c⟩ :=
    ModularCurve.XOneP.exists_valuationSubring_pair_x1_mul p M hM hpM L ζ hζ K hK A hAp hζA j hj
      (overResidueField k hp0 hAp w)
  have hA : ∀ a : A, algebraMap A ↥K a ∈ W₀ := (h1 0).1
  have hjW : j ∈ W₀ ∧ j⁻¹ ∈ W₀ := by
    have := h2 0 Polynomial.X (by rw [Polynomial.map_X]; exact Polynomial.X_ne_zero)
    simpa using this
  let D : Setup A L K k p M :=
    { W₀ := W₀
      mem_W₀_iff := h4
      algebraMap_mem_W₀ := hA
      hp0 := hp0
      hAp := hAp
      w := w
      red_mem := fun f x y h => (h6 f x y h.1 h.2).1 }
  have hBfin : ∀ b ∈ AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j, b ∈ D.W₀ :=
    chartAlg_le_valuationSubring _ W₀ hA (by simpa using hjW.1)
  have hBinf : ∀ b ∈ AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A (↥K) j, b ∈ D.W₀ :=
    chartAlg_le_valuationSubring _ W₀ hA (by simpa using hjW.2)
  have hj0 : (j : ↥K) ≠ 0 := Fact.out
  have hjpres : Pres L ((j : LaurentSeries L)) (jNum.map (Int.castRingHom A)) PowerSeries.X := by
    rw [hj]; exact pres_jq
  have hgj : D.gaussRedK ⟨j, hjW.1⟩ = jqModC k := by
    rw [D.gaussRedK_spec (f := ⟨j, hjW.1⟩) hjpres]
    exact red_pres_jq k
  have h6c' : ∀ r₀ : LaurentSeries (ResidueField A),
      r₀ ∈ igusaFunctionFieldX1C (ResidueField A) M (overResidueField k D.hp0 D.hAp D.w) →
      ∃ (f : ↥K) (x y : PowerSeries A), y.map (residue A) ≠ 0 ∧
        (f : LaurentSeries L) * ofPowerSeries ℤ L (y.map (algebraMap A L)) = ofPowerSeries ℤ L (x.map (algebraMap A L)) ∧
        toκ x / toκ y = r₀ := fun r₀ hr₀ => h6c r₀ hr₀

  have htj : Transcendental A j := ModularCurve.transcendental_of_coe_eq_coeffEmb_jq L K A j hj
  haveI : NeZero (M * p) := ⟨Nat.mul_ne_zero (NeZero.ne M) (Fact.out : p.Prime).ne_zero⟩
  have hT : ModularGroup.T ∈ CongruenceSubgroup.Gamma1 (M * p) := by
    rw [CongruenceSubgroup.Gamma1_mem]
    simp [ModularGroup.T]
  have hFD : FiniteDimensional ↥(IntermediateField.adjoin L ({j} : Set ↥K)) ↥K :=
    ModularCurve.finiteDimensional_adjoin_of_coe_eq_coeffEmb_jq_of_eq_laurentBaseChange
      (CongruenceSubgroup.Gamma1 (M * p)) hT L K hK j hj
  haveI := hFD
  haveI : Algebra.IsIntegral ↥(IntermediateField.adjoin L ({j} : Set ↥K)) ↥K := Algebra.IsIntegral.of_finite _ _
  have hsep : Algebra.IsSeparable ↥(IntermediateField.adjoin L ({j} : Set ↥K)) ↥K := Algebra.IsSeparable.of_integral _ _

  haveI : Fact ((j : ↥K)⁻¹ ≠ 0) := ⟨inv_ne_zero hj0⟩
  have htj' : Transcendental A (j⁻¹ : ↥K) := fun h => htj (IsAlgebraic.inv_iff.mp h)
  have hadj : IntermediateField.adjoin L ({j⁻¹} : Set ↥K) = IntermediateField.adjoin L ({j} : Set ↥K) := by
    apply le_antisymm
    · rw [IntermediateField.adjoin_le_iff, Set.singleton_subset_iff]
      exact IntermediateField.inv_mem _ (IntermediateField.mem_adjoin_simple_self L j)
    · rw [IntermediateField.adjoin_le_iff, Set.singleton_subset_iff]
      have := IntermediateField.inv_mem _ (IntermediateField.mem_adjoin_simple_self L (j⁻¹ : ↥K))
      simpa using this
  have hFD' : FiniteDimensional ↥(IntermediateField.adjoin L ({j⁻¹} : Set ↥K)) ↥K := by rw [hadj]; exact hFD
  have hsep' : Algebra.IsSeparable ↥(IntermediateField.adjoin L ({j⁻¹} : Set ↥K)) ↥K := by rw [hadj]; exact hsep

  have hA' : ∀ a ∈ IsLocalRing.maximalIdeal A, algebraMap A ↥K a ∈ W₀.nonunits := (h1 0).2
  have hWj : ∀ P : Polynomial A, P.map (IsLocalRing.residue A) ≠ 0 →
      Polynomial.aeval j P ∈ W₀ ∧ (Polynomial.aeval j P)⁻¹ ∈ W₀ := h2 0
  have hWjinv : ∀ P : Polynomial A, P.map (IsLocalRing.residue A) ≠ 0 →
      Polynomial.aeval (j⁻¹ : ↥K) P ∈ W₀ ∧ (Polynomial.aeval (j⁻¹ : ↥K) P)⁻¹ ∈ W₀ := by
    intro P hP

    have hrev : P.reverse.map (IsLocalRing.residue A) ≠ 0 := by
      intro h0
      apply hP
      ext m
      rw [Polynomial.coeff_map, Polynomial.coeff_zero]
      by_cases hm : m ≤ P.natDegree
      · have := congrArg (fun Q => Polynomial.coeff Q (P.natDegree - m)) h0
        simp only [Polynomial.coeff_map, Polynomial.coeff_zero, Polynomial.coeff_reverse,
          Polynomial.revAt_le (Nat.sub_le _ _), Nat.sub_sub_self hm] at this
        exact this
      · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (not_le.mp hm), map_zero]
    obtain ⟨hr1, hr2⟩ := hWj P.reverse hrev
    letI : Invertible (j⁻¹ : ↥K) := invertibleOfNonzero (inv_ne_zero hj0)
    have hinv : ⅟(j⁻¹ : ↥K) = j := by
      rw [invOf_eq_inv, inv_inv]
    have key : Polynomial.aeval (j⁻¹ : ↥K) P = Polynomial.aeval j P.reverse * (j⁻¹ : ↥K) ^ P.natDegree := by
      have := Polynomial.eval₂_reverse_mul_pow (algebraMap A ↥K) (j⁻¹ : ↥K) P
      rw [hinv] at this
      rw [Polynomial.aeval_def, Polynomial.aeval_def]
      exact this.symm
    refine ⟨?_, ?_⟩
    · rw [key]
      exact mul_mem hr1 (pow_mem hjW.2 _)
    · rw [key, mul_inv, inv_pow, inv_inv]
      exact mul_mem hr2 (pow_mem hjW.1 _)
  have hnu : ∀ b : ↥K, b ∈ D.W₀ → (b ∈ W₀.nonunits → False) → ∀ hb : b ∈ D.W₀, D.gaussRed ⟨b, hb⟩ ≠ 0 := by
    intro b hbW hnn hb h0
    obtain ⟨x, y, hpres⟩ := (D.mem_W₀_iff b).mp hb
    have hx : x.map (residue A) = 0 := (D.gaussRed_eq_zero_iff (f := ⟨b, hb⟩) hpres).mp h0
    exact hnn (((h6 b x y hpres.1 hpres.2).2).mpr hx)
  have hfrac_fin : ∀ f : ↥D.W₀, ∃ a b : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j),
      D.gaussRed ⟨b, hBfin b b.2⟩ ≠ 0 ∧ ((f : ↥K) : ↥K) * (b : ↥K) = (a : ↥K) := by
    obtain ⟨-, ⟨𝔓, -, -, hcentre, -, hloc⟩, -⟩ :=
      AlgebraicCurve.TwoChartIntegralModel.le_and_height_eq_one_and_exists_div_of_valuationSubring_of_transcendental
        A L (↥K) j htj hFD hsep W₀ hA hA' hWj
    intro f
    obtain ⟨a, b, hb𝔓, hfab⟩ := (hloc (f : ↥K)).mp f.2
    refine ⟨a, b, hnu b (hBfin b b.2) (fun hn => hb𝔓 ((hcentre b).mpr hn)) _, hfab⟩
  have hfrac_inf : ∀ f : ↥D.W₀, ∃ a b : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A (↥K) j),
      D.gaussRed ⟨b, hBinf b b.2⟩ ≠ 0 ∧ ((f : ↥K) : ↥K) * (b : ↥K) = (a : ↥K) := by
    obtain ⟨-, ⟨𝔓, -, -, hcentre, -, hloc⟩, -⟩ :=
      AlgebraicCurve.TwoChartIntegralModel.le_and_height_eq_one_and_exists_div_of_valuationSubring_of_transcendental
        A L (↥K) (j⁻¹ : ↥K) htj' hFD' hsep' W₀ hA hA' hWjinv
    intro f
    obtain ⟨a, b, hb𝔓, hfab⟩ := (hloc (f : ↥K)).mp f.2
    refine ⟨a, b, hnu b (hBinf b b.2) (fun hn => hb𝔓 ((hcentre b).mpr hn)) _, hfab⟩
  exact ⟨fun z => coe_mem_adjoinField_red D _ hBfin h6c' hfrac_fin z,
    fun z => coe_mem_adjoinField_red D _ hBinf h6c' hfrac_inf z⟩

end
p2m_reactivate "P2MW.S_ModularCurve_XOneP_coe_mem_adjoin_gaussReductions_chartAlg_igusaFunctionFieldX1C_x1_mul.ModularCurve.GaussRedCore.Setup P2MW.S_ModularCurve_XOneP_coe_mem_adjoin_gaussReductions_chartAlg_igusaFunctionFieldX1C_x1_mul.ModularCurve P2MW.S_ModularCurve_XOneP_coe_mem_adjoin_gaussReductions_chartAlg_igusaFunctionFieldX1C_x1_mul.ModularCurve.GaussRedCore"

end S_ModularCurve_XOneP_coe_mem_adjoin_gaussReductions_chartAlg_igusaFunctionFieldX1C_x1_mul
end P2MW
export P2MW.S_ModularCurve_XOneP_coe_mem_adjoin_gaussReductions_chartAlg_igusaFunctionFieldX1C_x1_mul (solution)
