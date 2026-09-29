-- Prove2me | solution 1 for ModularCurve.XOneP.exists_span_and_residueIndependent_gauss_heckeRoof_x1_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/403ba79c-2bff-54dc-a9ef-88869f2eb03e

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_X1HeckeOperator
import Definitions.Def_ModularCurve_IgusaFunctionFieldX1
import Definitions.Def_ModularCurve_JqCoeff
import Theorems.Thm_ModularCurve_XOneP_exists_fin_span_heckeRoof_x1_mul
import Theorems.Thm_ModularCurve_finrank_adjoin_jqNModC_igusaFunctionFieldX1C_eq
import Theorems.Thm_ModularCurve_XOneP_exists_valuationSubring_pair_x1_mul
import Theorems.Thm_ModularCurve_nonempty_integralWeightOneForm
import Theorems.Thm_ModularCurve_modularFunctionFieldFullC_le_qExpFunctionFieldC_gamma0
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XOneP_exists_span_and_residueIndependent_gauss_heckeRoof_x1_mul
p2m_attr_erase "instance" "CohCarrier.iotaDeg_range_finiteIndex CohCarrier.Gamma0Upper_finiteIndex TateModule.instModule TateModule.instSMul GaloisRepAdic.instAddCommGroup GaloisRepAdic.instFree GaloisRepAdic.instFinite GaloisRepAdic.instModule ResidualGaloisRep.instModule ResidualGaloisRep.instModuleFinite ResidualGaloisRep.instAddCommGroup WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instFinite ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.Gamma0Pair.isElliptic CohCarrier.HeckeData.V_isScalarTower CohCarrier.HeckeData.opSubalgebra_isMulCommutative CohCarrier.HeckeData.mTheta_isPrime AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "instance" "AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.instIsElliptic_tateBase ModularCurve.instIsElliptic_tateLaurent ModularCurve.KatzGamma0Form.instModule ModularCurve.KatzGamma0Form.instZero ModularCurve.KatzLevelPForm.instSMul ModularCurve.KatzGamma0Form.instAdd ModularCurve.KatzLevelPForm.instAddCommGroup ModularCurve.KatzGamma0Form.instNeg ModularCurve.KatzGamma0Form.instAddCommGroup ModularCurve.KatzLevelPForm.instAdd ModularCurve.KatzLevelPForm.instSub ModularCurve.KatzLevelPForm.instNeg ModularCurve.KatzGamma0Form.instSMul ModularCurve.KatzGamma0Form.instSub ModularCurve.KatzLevelPForm.instZero ModularCurve.KatzLevelPForm.instModule KatzModularForm.instAddCommGroup"
p2m_attr_erase "instance" "KatzModularForm.instSub KatzModularForm.instZero KatzModularForm.instModule KatzModularForm.instAdd KatzModularForm.instNeg KatzModularForm.instSMul WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular AlgebraicCurve.TwoChartIntegralModel.isOpenImmersion_ιInf AlgebraicCurve.TwoChartIntegralModel.isOpenImmersion_fInf AlgebraicCurve.TwoChartIntegralModel.isOpenImmersion_ιFin AlgebraicCurve.TwoChartIntegralModel.isOpenImmersion_fFin AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module"
p2m_attr_erase "instance" "TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free AlgebraicCurve.CurveModel.chartRing_finitePresentation AlgebraicCurve.CurveModel.isProper AlgebraicCurve.CurveModel.isIntegral AlgebraicCurve.CurveModel.smooth"
p2m_attr_erase "simp" "ModularCurve.JH.torsionGaloisRep_apply CohCarrier.conjUpperMat_apply_11 CohCarrier.conjUpperMat_apply_10 CohCarrier.mem_Gamma0Upper CohCarrier.val_gamma0Units TateModule.smul_apply TateModule.coe_mulP TateModule.proj_apply TateModule.coe_add TateModule.coe_sub WeierstrassCurve.tateModuleRepOfBasis_V TateModule.coe_zero TateModule.rep_apply WeierstrassCurve.tateModuleRep_V WeierstrassCurve.tateModuleRepOfBasis_ρ_apply GaloisRep.padicIntToRingLevel_apply TateModule.coe_neg WeierstrassCurve.tateModuleRep_ρ_apply GaloisRepAdic.mk.injEq GaloisRepAdic.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.injEq ResidualGaloisRep.mk.sizeOf_spec ResidualGaloisRep.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq ResidualGaloisRep.Equiv.mk.sizeOf_spec ResidualGaloisRep.Equiv.mk.injEq ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff"
p2m_attr_erase "simp" "ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_cuspidalDivisor₀ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero"
p2m_attr_erase "simp" "ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar ModularCurve.ProjectiveLine.map_mk"
p2m_attr_erase "simp" "ModularCurve.gamma0PairMap_gen ModularCurve.moduliPointMapRingHom_mk ModularCurve.Gamma0Pair.mk.injEq ModularCurve.ModuliPoint.j_mk ModularCurve.Gamma0Pair.mk.sizeOf_spec ModularCurve.gamma0PairMap_toCurve WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero WeierstrassCurve.ratPointHom_apply WeierstrassCurve.ratPointMap_zero AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one CohCarrier.Gen.dia.sizeOf_spec CohCarrier.Gen.U.injEq CohCarrier.Gen.T.sizeOf_spec CohCarrier.Gen.U.sizeOf_spec CohCarrier.Gen.T.injEq CohCarrier.Gen.dia.injEq CohCarrier.HeckeData.mk.sizeOf_spec CohCarrier.HeckeData.opAlgHom_X CohCarrier.HeckeData.toMLₒ_apply CohCarrier.HeckeData.mk.injEq CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd"
p2m_attr_erase "simp" "AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd"
p2m_attr_erase "simp" "ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.cuspData_yP ModularCurve.qTwistAlgHom_apply ModularCurve.cuspData_yQ ModularCurve.cuspData_xP ModularCurve.cuspData_xQ ModularCurve.val_cyclZeta ModularCurve.cuspShift_one ModularCurve.cuspShift_zero ModularCurve.LevelPData.mk.sizeOf_spec ModularCurve.KatzLevelPForm.neg_toFun ModularCurve.LevelP.coe_swapW ModularCurve.KatzLevelPForm.swap_swap KatzModularForm.pullbackLevelP_toFun ModularCurve.LevelPData.swap_xQ KatzModularForm.pullbackLevelP_zero ModularCurve.LevelPData.map_yP ModularCurve.KatzLevelPForm.swap_neg ModularCurve.KatzGamma0Form.toKatzLevelPForm_sub ModularCurve.KatzLevelPForm.swap_add KatzModularForm.swap_pullbackLevelP ModularCurve.KatzGamma0Form.toKatzLevelPForm_add ModularCurve.KatzLevelPForm.swap_smul ModularCurve.LevelPData.map_yQ ModularCurve.KatzLevelPForm.mk.injEq ModularCurve.KatzLevelPForm.zero_toFun KatzModularForm.pullbackLevelP_smul ModularCurve.LevelPData.swap_xP ModularCurve.KatzGamma0Form.toKatzLevelPForm_mul ModularCurve.KatzGamma0Form.toKatzLevelPForm_neg"
p2m_attr_erase "simp" "ModularCurve.LevelPData.variableChange_xQ KatzModularForm.pullbackGamma0_toKatzLevelPForm ModularCurve.KatzLevelPForm.mk.sizeOf_spec ModularCurve.KatzLevelPForm.swap_zero ModularCurve.LevelP.coe_unipotentU ModularCurve.KatzLevelPForm.mul_toFun ModularCurve.LevelPData.variableChange_yP ModularCurve.LevelPData.mk.injEq ModularCurve.KatzLevelPForm.sub_toFun ModularCurve.LevelPData.variableChange_xP ModularCurve.KatzLevelPForm.smul_toFun ModularCurve.LevelPData.swap_yP ModularCurve.LevelPData.map_xP ModularCurve.LevelPData.swap_swap ModularCurve.LevelPData.swap_yQ ModularCurve.KatzGamma0Form.toKatzLevelPForm_zero ModularCurve.KatzGamma0Form.mk.injEq ModularCurve.KatzLevelPForm.swap_toFun KatzModularForm.pullbackLevelP_add ModularCurve.KatzGamma0Form.mk.sizeOf_spec ModularCurve.LevelPData.variableChange_yQ ModularCurve.KatzLevelPForm.swap_sub ModularCurve.KatzGamma0Form.toKatzLevelPForm_smul ModularCurve.LevelPData.map_xQ ModularCurve.KatzLevelPForm.add_toFun KatzModularForm.c₆_toFun KatzModularForm.neg_toFun KatzModularForm.mul_toFun KatzModularForm.qExpansion_neg KatzModularForm.discr_toFun KatzModularForm.qExpansion_sub KatzModularForm.qExpansion_add KatzModularForm.qExpansion_mul KatzModularForm.zero_toFun KatzModularForm.mk.injEq KatzModularForm.qExpansion_smul KatzModularForm.smul_toFun KatzModularForm.add_toFun KatzModularForm.sub_toFun KatzModularForm.c₄_toFun"
p2m_attr_erase "simp" "KatzModularForm.qExpansion_zero KatzModularForm.mk.sizeOf_spec TateCurve.tateTorsionPoint_zero_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂"
p2m_attr_erase "simp" "WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.genusOnePic0Equiv_apply WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec"
p2m_attr_erase "simp" "WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff HahnSeries.ramScale_apply AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring ModularCurve.LevelN.coe_jGen ModularCurve.CharPReduction.coeffRed_coeff ModularCurve.CharPReduction.redLocHom_apply ModularCurve.ComplexPlaceDictionaryOf.pt_ofGamma0 ModularCurve.ComplexPlaceDictionaryOf.mk.injEq ModularCurve.ComplexPlaceDictionaryOf.pt_toGamma0 ModularCurve.ComplexPlaceDictionaryOf.mk.sizeOf_spec ModularCurve.ComplexPlaceDictionary.mk.injEq ModularCurve.ComplexPlaceDictionary.mk.sizeOf_spec AlgebraicCurve.TwoChartIntegralModel.ιInf_toBase AlgebraicCurve.TwoChartIntegralModel.polynomialToChartFin_X AlgebraicCurve.TwoChartIntegralModel.coe_chartBaseChange AlgebraicCurve.TwoChartIntegralModel.polynomialToChartInf_X AlgebraicCurve.TwoChartIntegralModel.ιFin_toBase AlgebraicCurve.TwoChartIntegralModel.ιFin_toBase_assoc AlgebraicCurve.TwoChartIntegralModel.coe_jChartFin AlgebraicCurve.TwoChartIntegralModel.ιInf_toBase_assoc AlgebraicCurve.TwoChartIntegralModel.coe_jInvChartInf AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces RegularLocalRingQuotientAscent.dualNumberFst_apply AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0"
p2m_attr_erase "simp" "TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq AlgebraicCurve.CurveModel.mk.injEq AlgebraicCurve.CurveModel.mk.sizeOf_spec"

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace IGDEGAssembly

theorem forall_eq_zero_of_sum_mul_pow_eq_zero {E : Type*} [Field E] {k : Type*} [Field k] [Algebra k E]
    (F : IntermediateField k E) (x : E) (d : ℕ) (hd : 0 < d)
    (hfin : Module.finrank ↥F ↥(IntermediateField.adjoin ↥F ({x} : Set E)) = d)
    (r : Fin d → E) (hr : ∀ i, r i ∈ F) (hsum : ∑ i, r i * x ^ (i : ℕ) = 0) : ∀ i, r i = 0 := by
  classical

  haveI : FiniteDimensional ↥F ↥(IntermediateField.adjoin ↥F ({x} : Set E)) :=
    Module.finite_of_finrank_pos (by omega)
  have hx : IsIntegral ↥F x := by
    have : IsIntegral ↥F (IntermediateField.AdjoinSimple.gen ↥F x) := IsIntegral.of_finite ↥F _
    simpa using this.map (IntermediateField.val _)
  have hdeg : (minpoly ↥F x).natDegree = d := by
    rw [← IntermediateField.adjoin.finrank hx, hfin]

  let P : Polynomial ↥F := ∑ i : Fin d, Polynomial.C (⟨r i, hr i⟩ : ↥F) * Polynomial.X ^ (i : ℕ)
  have hPx : Polynomial.aeval x P = 0 := by
    simp only [P, map_sum, map_mul, Polynomial.aeval_C, map_pow, Polynomial.aeval_X]
    simpa using hsum
  have hPdeg : P.natDegree < d := by
    refine lt_of_le_of_lt (Polynomial.natDegree_sum_le_of_forall_le _ _ (n := d - 1) fun i _ => ?_) (by omega)
    refine (Polynomial.natDegree_C_mul_X_pow_le _ _).trans ?_
    have := i.2; omega
  have hP0 : P = 0 := by
    by_contra hP
    have h1 := minpoly.degree_le_of_ne_zero ↥F x hP hPx
    have h2 : (minpoly ↥F x).natDegree ≤ P.natDegree := Polynomial.natDegree_le_natDegree h1
    omega
  intro i
  have := congrArg (fun Q => Polynomial.coeff Q i) hP0
  simp only [P, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_zero] at this
  rw [Finset.sum_eq_single i] at this
  · simpa using congrArg Subtype.val this
  · intro j _ hji; rw [if_neg]; exact fun h => hji (Fin.ext h.symm)
  · intro h; exact absurd (Finset.mem_univ i) h

end IGDEGAssembly

namespace IGDEGAssembly

section Pres

variable {A : Type*} [CommRing A] {L : Type*} [Field L] [Algebra A L]

noncomputable def emb (A L : Type*) [CommRing A] [Field L] [Algebra A L] : PowerSeries A →+* LaurentSeries L :=
  (HahnSeries.ofPowerSeries ℤ L).comp (PowerSeries.map (algebraMap A L))

theorem emb_apply (z : PowerSeries A) : emb A L z = HahnSeries.ofPowerSeries ℤ L (z.map (algebraMap A L)) := rfl

theorem emb_injective [FaithfulSMul A L] : Function.Injective (emb A L) := by
  intro a b h
  rw [emb_apply, emb_apply] at h
  exact PowerSeries.map_injective _ (FaithfulSMul.algebraMap_injective A L) (HahnSeries.ofPowerSeries_injective h)

theorem pres_mul {F G : LaurentSeries L} {x y u v : PowerSeries A}
    (h1 : F * emb A L y = emb A L x) (h2 : G * emb A L v = emb A L u) :
    (F * G) * emb A L (y * v) = emb A L (x * u) := by
  rw [map_mul, map_mul, ← h1, ← h2]; ring

theorem pres_sum {n : ℕ} (F : Fin n → LaurentSeries L) (x y : Fin n → PowerSeries A)
    (h : ∀ i, F i * emb A L (y i) = emb A L (x i)) :
    (∑ i, F i) * emb A L (∏ i, y i) = emb A L (∑ i, x i * ∏ k ∈ Finset.univ.erase i, y k) := by
  classical
  rw [Finset.sum_mul, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, ← h i, mul_assoc, ← map_mul, Finset.mul_prod_erase _ _ (Finset.mem_univ i)]

end Pres

end IGDEGAssembly

namespace IGDEGAssembly
namespace Exp

open PowerSeries

variable {A : Type*} [CommRing A]

noncomputable def expandPS (N : ℕ) (x : PowerSeries A) : PowerSeries A :=
  PowerSeries.mk fun n => if N ∣ n then PowerSeries.coeff (n / N) x else 0

theorem coeff_expandPS (N : ℕ) (x : PowerSeries A) (n : ℕ) :
    PowerSeries.coeff n (expandPS N x) = if N ∣ n then PowerSeries.coeff (n / N) x else 0 := by
  rw [expandPS, PowerSeries.coeff_mk]

theorem coeff_expandPS_mul (N : ℕ) [NeZero N] (x : PowerSeries A) (m : ℕ) :
    PowerSeries.coeff (N * m) (expandPS N x) = PowerSeries.coeff m x := by
  rw [coeff_expandPS, if_pos (dvd_mul_right N m), Nat.mul_div_cancel_left m (Nat.pos_of_ne_zero (NeZero.ne N))]

theorem map_expandPS {B : Type*} [CommRing B] (φ : A →+* B) (N : ℕ) (x : PowerSeries A) :
    (expandPS N x).map φ = expandPS N (x.map φ) := by
  ext n
  simp only [PowerSeries.coeff_map, coeff_expandPS]
  split_ifs <;> simp

theorem expandPS_eq_zero_iff (N : ℕ) [NeZero N] (x : PowerSeries A) : expandPS N x = 0 ↔ x = 0 := by
  constructor
  · intro h
    ext m
    have := congrArg (PowerSeries.coeff (N * m)) h
    rwa [coeff_expandPS_mul, map_zero] at this
  · rintro rfl
    ext n
    rw [coeff_expandPS]
    split_ifs <;> simp

theorem coeff_ofPowerSeries {R : Type*} [CommRing R] (y : PowerSeries R) (k : ℤ) :
    (HahnSeries.ofPowerSeries ℤ R y).coeff k = if 0 ≤ k then PowerSeries.coeff k.toNat y else 0 := by
  split_ifs with hk
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hk
    rw [Int.toNat_natCast]
    exact HahnSeries.ofPowerSeries_apply_coeff y n
  · apply HahnSeries.embDomain_notin_range
    rintro ⟨n, hn⟩
    apply hk
    have : (n : ℤ) = k := by simpa using hn
    omega

theorem qExpand_ofPowerSeries {R : Type*} [CommRing R] (N : ℕ) [NeZero N] (y : PowerSeries R) :
    ModularCurve.qExpand R N (HahnSeries.ofPowerSeries ℤ R y) = HahnSeries.ofPowerSeries ℤ R (expandPS N y) := by
  have hN : (0 : ℤ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  ext k
  by_cases hk : (N : ℤ) ∣ k
  · obtain ⟨m, rfl⟩ := hk
    rw [ModularCurve.qExpand_coeff_mul, coeff_ofPowerSeries, coeff_ofPowerSeries]
    by_cases hm : 0 ≤ m
    · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hm
      have htn : ((N : ℤ) * (n : ℤ)).toNat = N * n := by rw [← Nat.cast_mul, Int.toNat_natCast]
      rw [if_pos hm, if_pos (by positivity), Int.toNat_natCast, htn, coeff_expandPS_mul]
    · rw [if_neg hm, if_neg]
      intro h
      exact hm ((mul_nonneg_iff_of_pos_left hN).mp h)
  · rw [ModularCurve.qExpand_coeff_of_not_dvd N _ hk, coeff_ofPowerSeries]
    split_ifs with h0
    · rw [coeff_expandPS, if_neg]
      intro hd
      apply hk
      obtain ⟨c, hc⟩ := hd
      refine ⟨c, ?_⟩
      have : ((k.toNat : ℕ) : ℤ) = k := Int.toNat_of_nonneg h0
      rw [← this, hc]; push_cast; ring
    · rfl

end IGDEGAssembly.Exp

namespace IGDEGAssembly

open IGDEGAssembly.Exp

section JPow

variable (R : Type*) [CommRing R]

theorem jqModC_pow_mul_ofPowerSeries_X_pow (i : ℕ) :
    ModularCurve.jqModC R ^ i * HahnSeries.ofPowerSeries ℤ R (PowerSeries.X ^ i) =
      HahnSeries.ofPowerSeries ℤ R ((ModularCurve.jNum.map (Int.castRingHom R)) ^ i) := by
  rw [ModularCurve.jqModC_pow, HahnSeries.ofPowerSeries_X_pow, mul_comm (HahnSeries.single _ _) _, mul_assoc,
    HahnSeries.single_mul_single, neg_add_cancel, one_mul]
  change _ * (1 : LaurentSeries R) = _
  rw [mul_one]

theorem jqNModC_pow_mul_ofPowerSeries_X_pow (N : ℕ) [NeZero N] (i : ℕ) :
    ModularCurve.jqNModC R N ^ i * HahnSeries.ofPowerSeries ℤ R (PowerSeries.X ^ (N * i)) =
      HahnSeries.ofPowerSeries ℤ R (expandPS N ((ModularCurve.jNum.map (Int.castRingHom R)) ^ i)) := by
  have h := congrArg (ModularCurve.qExpand R N) (jqModC_pow_mul_ofPowerSeries_X_pow R i)
  rw [map_mul, map_pow, qExpand_ofPowerSeries, qExpand_ofPowerSeries] at h
  rw [ModularCurve.jqNModC, ← h]
  congr 2

  ext n
  rw [coeff_expandPS, PowerSeries.coeff_X_pow, PowerSeries.coeff_X_pow]
  by_cases hNn : N ∣ n
  · obtain ⟨m, rfl⟩ := hNn
    rw [if_pos (dvd_mul_right N m), Nat.mul_div_cancel_left m (Nat.pos_of_ne_zero (NeZero.ne N))]
    by_cases hm : m = i
    · subst hm; simp
    · rw [if_neg hm, if_neg]
      intro h; exact hm (Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero (NeZero.ne N)) h)
  · rw [if_neg hNn, if_neg]
    rintro rfl; exact hNn (dvd_mul_right N i)

end JPow

section Red

variable {A : Type*} [CommRing A] [IsLocalRing A]

noncomputable def red (A : Type*) [CommRing A] [IsLocalRing A] : PowerSeries A →+* LaurentSeries (IsLocalRing.ResidueField A) :=
  (HahnSeries.ofPowerSeries ℤ _).comp (PowerSeries.map (IsLocalRing.residue A))

theorem red_apply (z : PowerSeries A) :
    red A z = HahnSeries.ofPowerSeries ℤ _ (z.map (IsLocalRing.residue A)) := rfl

theorem red_ne_zero_iff (z : PowerSeries A) : red A z ≠ 0 ↔ z.map (IsLocalRing.residue A) ≠ 0 := by
  rw [red_apply, Ne, Ne, ← (HahnSeries.ofPowerSeries_injective (Γ := ℤ) (R := IsLocalRing.ResidueField A)).eq_iff, map_zero]

theorem red_expandPS (N : ℕ) [NeZero N] (z : PowerSeries A) :
    red A (expandPS N z) = ModularCurve.qExpand _ N (red A z) := by
  rw [red_apply, red_apply, map_expandPS, qExpand_ofPowerSeries]

theorem red_jNum_pow (i : ℕ) :
    red A ((ModularCurve.jNum.map (Int.castRingHom A)) ^ i) =
      HahnSeries.ofPowerSeries ℤ _ ((ModularCurve.jNum.map (Int.castRingHom (IsLocalRing.ResidueField A))) ^ i) := by
  rw [red_apply, map_pow, ← RingHom.comp_apply (PowerSeries.map (IsLocalRing.residue A)) (PowerSeries.map (Int.castRingHom A)),
    ← PowerSeries.map_comp, RingHom.ext_int ((IsLocalRing.residue A).comp (Int.castRingHom A)) (Int.castRingHom _)]

theorem map_jNum_pow_ne_zero (i : ℕ) : ((ModularCurve.jNum.map (Int.castRingHom A)) ^ i).map (IsLocalRing.residue A) ≠ 0 := by
  rw [map_pow, ← RingHom.comp_apply (PowerSeries.map (IsLocalRing.residue A)) (PowerSeries.map (Int.castRingHom A)),
    ← PowerSeries.map_comp, RingHom.ext_int ((IsLocalRing.residue A).comp (Int.castRingHom A)) (Int.castRingHom _)]
  apply pow_ne_zero
  intro h
  have := congrArg (PowerSeries.coeff 0) h
  rw [PowerSeries.coeff_map, PowerSeries.coeff_zero_eq_constantCoeff_apply, ModularCurve.constantCoeff_jNum, map_one, map_zero] at this
  exact one_ne_zero this

theorem map_X_pow_ne_zero [Nontrivial (IsLocalRing.ResidueField A)] (k : ℕ) : ((PowerSeries.X : PowerSeries A) ^ k).map (IsLocalRing.residue A) ≠ 0 := by
  rw [map_pow, PowerSeries.map_X]; exact pow_ne_zero _ PowerSeries.X_ne_zero

end Red

end IGDEGAssembly

namespace IGDEGAssembly

open IGDEGAssembly.Exp

section EmbJ

variable {A : Type*} [CommRing A] {L : Type*} [Field L] [Algebra A L]

theorem emb_X_pow (k : ℕ) : emb A L (PowerSeries.X ^ k) = HahnSeries.ofPowerSeries ℤ L (PowerSeries.X ^ k) := by
  rw [emb_apply, map_pow, PowerSeries.map_X]

theorem map_algebraMap_jNum_pow (i : ℕ) :
    ((ModularCurve.jNum.map (Int.castRingHom A)) ^ i).map (algebraMap A L) = (ModularCurve.jNum.map (Int.castRingHom L)) ^ i := by
  rw [map_pow, ← RingHom.comp_apply (PowerSeries.map (algebraMap A L)) (PowerSeries.map (Int.castRingHom A)), ← PowerSeries.map_comp,
    RingHom.ext_int ((algebraMap A L).comp (Int.castRingHom A)) (Int.castRingHom L)]

theorem emb_jNum_pow (i : ℕ) :
    emb A L ((ModularCurve.jNum.map (Int.castRingHom A)) ^ i) = HahnSeries.ofPowerSeries ℤ L ((ModularCurve.jNum.map (Int.castRingHom L)) ^ i) := by
  rw [emb_apply, map_algebraMap_jNum_pow]

theorem emb_expandPS_jNum_pow (N : ℕ) [NeZero N] (i : ℕ) :
    emb A L (expandPS N ((ModularCurve.jNum.map (Int.castRingHom A)) ^ i)) =
      HahnSeries.ofPowerSeries ℤ L (expandPS N ((ModularCurve.jNum.map (Int.castRingHom L)) ^ i)) := by
  rw [emb_apply, map_expandPS, map_algebraMap_jNum_pow]

end EmbJ

end IGDEGAssembly

namespace IGDEGAssembly

open IGDEGAssembly.Exp

section Core

variable {A : Type} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] {L : Type} [Field L] [Algebra A L] [FaithfulSMul A L]

theorem mem_nonunits_iff_or' {K : Type*} [Field K] (V : ValuationSubring K) (x : K) :
    x ∈ V.nonunits ↔ x ∈ V ∧ (x = 0 ∨ x⁻¹ ∉ V) := by
  rw [ValuationSubring.mem_nonunits_iff, ← ValuationSubring.valuation_le_one_iff, ← ValuationSubring.valuation_le_one_iff]
  by_cases hx : x = 0
  · subst hx; simp
  · rw [map_inv₀]
    have h0 : V.valuation x ≠ 0 := (Valuation.ne_zero_iff _).mpr hx
    constructor
    · intro h
      exact ⟨h.le, Or.inr (by rw [not_le]; exact one_lt_inv_iff₀.mpr ⟨zero_lt_iff.mpr h0, h⟩)⟩
    · rintro ⟨-, h | h⟩
      · exact absurd h hx
      · rw [not_le] at h
        exact (one_lt_inv_iff₀.mp h).2

theorem red_ne_zero {z : PowerSeries A} (hz : z.map (IsLocalRing.residue A) ≠ 0) : red A z ≠ 0 :=
  (red_ne_zero_iff z).mpr hz

theorem sum_mul_pow_not_mem_nonunits
    (K₀ : IntermediateField L (LaurentSeries L)) {K' : Type} [Field K'] (val : K' →+* LaurentSeries L) (hval : Function.Injective val)
    (ι : ↥K₀ →+* K') (T : PowerSeries A →+* PowerSeries A)
    (hιT : ∀ (f : ↥K₀) (x y : PowerSeries A), (f : LaurentSeries L) * emb A L y = emb A L x → val (ι f) * emb A L (T y) = emb A L (T x))
    (hT : ∀ z : PowerSeries A, (T z).map (IsLocalRing.residue A) ≠ 0 ↔ z.map (IsLocalRing.residue A) ≠ 0)
    (τ : LaurentSeries (IsLocalRing.ResidueField A) →+* LaurentSeries (IsLocalRing.ResidueField A)) (hτ : Function.Injective τ)
    (hTτ : ∀ z : PowerSeries A, red A (T z) = τ (red A z))
    (W₀ : ValuationSubring ↥K₀)
    (hW₀ : ∀ f : ↥K₀, f ∈ W₀ ↔ ∃ x y : PowerSeries A, y.map (IsLocalRing.residue A) ≠ 0 ∧ (f : LaurentSeries L) * emb A L y = emb A L x)
    (Ig : Set (LaurentSeries (IsLocalRing.ResidueField A)))
    (h6a : ∀ (f : ↥K₀) (x y : PowerSeries A), y.map (IsLocalRing.residue A) ≠ 0 → (f : LaurentSeries L) * emb A L y = emb A L x →
      red A x / red A y ∈ Ig)
    (U : ValuationSubring K')
    (hU : ∀ f : K', f ∈ U ↔ ∃ x y : PowerSeries A, y.map (IsLocalRing.residue A) ≠ 0 ∧ val f * emb A L y = emb A L x)
    (d : ℕ) (J : K') (ξ η : Fin d → PowerSeries A) (hη : ∀ i, (η i).map (IsLocalRing.residue A) ≠ 0)
    (hJ : ∀ i : Fin d, val J ^ (i : ℕ) * emb A L (η i) = emb A L (ξ i))
    (g : LaurentSeries (IsLocalRing.ResidueField A)) (hg : ∀ i : Fin d, red A (ξ i) = g ^ (i : ℕ) * red A (η i))
    (hind : ∀ r : Fin d → LaurentSeries (IsLocalRing.ResidueField A), (∀ i, r i ∈ τ '' Ig) → ∑ i, r i * g ^ (i : ℕ) = 0 → ∀ i, r i = 0)
    (c : Fin d → ↥K₀) (hc : ∀ i, c i ∈ W₀) (hunit : ∃ i, c i ∉ W₀.nonunits) :
    ∑ i, ι (c i) * J ^ (i : ℕ) ∉ U.nonunits := by
  classical

  choose a b hb hab using fun i => (hW₀ (c i)).mp (hc i)

  obtain ⟨i₀, hi₀⟩ := hunit
  have ha0 : (a i₀).map (IsLocalRing.residue A) ≠ 0 := by
    have hc0 : c i₀ ≠ 0 ∧ (c i₀)⁻¹ ∈ W₀ := by
      have h := hi₀; rw [mem_nonunits_iff_or'] at h; push Not at h
      exact h (hc i₀)
    obtain ⟨a', b', hb', hab'⟩ := (hW₀ (c i₀)⁻¹).mp hc0.2
    have e : b i₀ * b' = a i₀ * a' := by
      apply emb_injective (A := A) (L := L)
      rw [map_mul, map_mul, ← hab i₀, ← hab']
      have hcc : ((c i₀ : ↥K₀) : LaurentSeries L) * (((c i₀)⁻¹ : ↥K₀) : LaurentSeries L) = 1 := by
        rw [← IntermediateField.coe_mul, mul_inv_cancel₀ hc0.1]; rfl
      calc emb A L (b i₀) * emb A L b' = (((c i₀ : ↥K₀) : LaurentSeries L) * (((c i₀)⁻¹ : ↥K₀) : LaurentSeries L)) * (emb A L (b i₀) * emb A L b') := by rw [hcc, one_mul]
        _ = ((c i₀ : ↥K₀) : LaurentSeries L) * emb A L (b i₀) * ((((c i₀)⁻¹ : ↥K₀) : LaurentSeries L) * emb A L b') := by ring
    intro h0
    have h1 : (b i₀ * b').map (IsLocalRing.residue A) ≠ 0 := by
      rw [map_mul]; exact mul_ne_zero (hb i₀) hb'
    rw [e, map_mul, h0, zero_mul] at h1
    exact h1 rfl

  set F : K' := ∑ i, ι (c i) * J ^ (i : ℕ) with hF
  set Y : PowerSeries A := ∏ i, (T (b i) * η i) with hY
  set X : PowerSeries A := ∑ i, (T (a i) * ξ i) * ∏ k ∈ Finset.univ.erase i, (T (b k) * η k) with hX
  have hpresi : ∀ i, val (ι (c i) * J ^ (i : ℕ)) * emb A L (T (b i) * η i) = emb A L (T (a i) * ξ i) := fun i => by
    rw [map_mul, map_pow]
    exact pres_mul (hιT (c i) (a i) (b i) (hab i)) (hJ i)
  have hpres : val F * emb A L Y = emb A L X := by
    rw [hF, map_sum, hY, hX]
    exact pres_sum (fun i => val (ι (c i) * J ^ (i : ℕ))) (fun i => T (a i) * ξ i) (fun i => T (b i) * η i) hpresi
  have hY0 : Y.map (IsLocalRing.residue A) ≠ 0 := by
    rw [hY, map_prod]
    exact Finset.prod_ne_zero_iff.mpr fun i _ => by rw [map_mul]; exact mul_ne_zero ((hT _).mpr (hb i)) (hη i)

  intro hFnon
  have hX0 : X.map (IsLocalRing.residue A) = 0 := by
    by_contra hX0
    have hX' : emb A L X ≠ 0 := fun h => hX0 (by
      have : X = 0 := emb_injective (A := A) (L := L) (by rw [h, map_zero])
      rw [this, map_zero])
    have hF0 : F ≠ 0 := by
      intro h0
      rw [h0, map_zero, zero_mul] at hpres
      exact hX' hpres.symm
    have hFinv : F⁻¹ ∈ U := (hU F⁻¹).mpr ⟨Y, X, hX0, by
      rw [map_inv₀, ← hpres, ← mul_assoc, inv_mul_cancel₀ ((map_ne_zero_iff _ hval).mpr hF0), one_mul]⟩
    have := (mem_nonunits_iff_or' U F).mp hFnon
    rcases this.2 with h | h
    · exact hF0 h
    · exact h hFinv

  have hden : ∀ i, red A (T (b i) * η i) ≠ 0 := fun i =>
    red_ne_zero (by rw [map_mul]; exact mul_ne_zero ((hT _).mpr (hb i)) (hη i))
  have hrmem : ∀ i : Fin d, τ (red A (a i) / red A (b i)) ∈ τ '' Ig := fun i => ⟨_, h6a (c i) (a i) (b i) (hb i) (hab i), rfl⟩
  have hsum : ∑ i : Fin d, τ (red A (a i) / red A (b i)) * g ^ (i : ℕ) = 0 := by
    have h1 : red A X = 0 := by rw [red_apply, hX0, map_zero]
    have hP : red A (∏ k, (T (b k) * η k)) ≠ 0 := by
      rw [map_prod]; exact Finset.prod_ne_zero_iff.mpr fun i _ => hden i
    have key : ∀ i : Fin d, red A ((T (a i) * ξ i) * ∏ k ∈ Finset.univ.erase i, (T (b k) * η k)) =
        (τ (red A (a i) / red A (b i)) * g ^ (i : ℕ)) * red A (∏ k, (T (b k) * η k)) := by
      intro i
      rw [← Finset.mul_prod_erase Finset.univ (fun k => T (b k) * η k) (Finset.mem_univ i), map_mul, map_mul, map_mul, map_mul,
        hTτ, hTτ, hg i]
      have hbi : τ (red A (b i)) ≠ 0 := by rw [← hTτ]; exact red_ne_zero ((hT _).mpr (hb i))
      rw [map_div₀]
      field_simp
    rw [hX, map_sum] at h1
    simp_rw [key] at h1
    rw [← Finset.sum_mul] at h1
    exact (mul_eq_zero.mp h1).resolve_right hP

  have hri : τ (red A (a i₀) / red A (b i₀)) = 0 := hind _ hrmem hsum i₀
  have : red A (a i₀) / red A (b i₀) = 0 := hτ (by rw [hri, map_zero])
  rw [div_eq_zero_iff] at this
  rcases this with h | h
  · exact (red_ne_zero ha0) h
  · exact (red_ne_zero (hb i₀)) h

end Core

end IGDEGAssembly

namespace IGDEGAssembly

open IGDEGAssembly.Exp

noncomputable def expandPSHom {A : Type*} [CommRing A] (N : ℕ) [NeZero N] : PowerSeries A →+* PowerSeries A where
  toFun := expandPS N
  map_one' := by
    apply HahnSeries.ofPowerSeries_injective (Γ := ℤ) (R := A)
    rw [← qExpand_ofPowerSeries, map_one, map_one]
  map_mul' x y := by
    apply HahnSeries.ofPowerSeries_injective (Γ := ℤ) (R := A)
    rw [← qExpand_ofPowerSeries, map_mul, map_mul, map_mul, qExpand_ofPowerSeries, qExpand_ofPowerSeries]
  map_zero' := (expandPS_eq_zero_iff N 0).mpr rfl
  map_add' x y := by
    apply HahnSeries.ofPowerSeries_injective (Γ := ℤ) (R := A)
    rw [← qExpand_ofPowerSeries, map_add, map_add, map_add, qExpand_ofPowerSeries, qExpand_ofPowerSeries]

@[scoped simp] theorem expandPSHom_apply {A : Type*} [CommRing A] (N : ℕ) [NeZero N] (x : PowerSeries A) : expandPSHom N x = expandPS N x := rfl

end IGDEGAssembly
p2m_reactivate "P2MW.S_ModularCurve_XOneP_exists_span_and_residueIndependent_gauss_heckeRoof_x1_mul.IGDEGAssembly"

open IGDEGAssembly IGDEGAssembly.Exp in

theorem solution
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hM : 5 ≤ M) (hpM : ¬ p ∣ M)
    (L : Type) [Field L] [CharZero L] [IsCyclotomicExtension {p} ℚ L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ p)
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p)))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAp : (p : A) ∈ IsLocalRing.maximalIdeal A) (hζA : ∃ z : A, algebraMap A L z = ζ)
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓp : ℓ ≠ p)
    [Algebra A ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * ℓ)))] [IsScalarTower A L ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * ℓ)))]
    (ι : ↥K →ₐ[L] ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * ℓ))))
    (hι : (∀ f : ↥K, ((ι f : ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * ℓ)))) : LaurentSeries L) = (f : LaurentSeries L)) ∨
      (∀ f : ↥K, ((ι f : ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * ℓ)))) : LaurentSeries L) = ModularCurve.qExpand L ℓ (f : LaurentSeries L)))
    (W₀ : ValuationSubring ↥K)
    (hW₀ : ∀ f : ↥K, f ∈ W₀ ↔ ∃ x y : PowerSeries A, y.map (IsLocalRing.residue A) ≠ 0 ∧
        (f : LaurentSeries L) * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap A L))
          = HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap A L)))
    (U : ValuationSubring ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * ℓ))))
    (hU : ∀ f : ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * ℓ))), f ∈ U ↔ ∃ x y : PowerSeries A, y.map (IsLocalRing.residue A) ≠ 0 ∧
        (f : LaurentSeries L) * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap A L))
          = HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap A L))) :
    ∃ n : ℕ,
      (∃ b : Fin n → ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * ℓ))), ∀ z : ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * ℓ))), ∃ c : Fin n → ↥K, z = ∑ i, ι (c i) * b i) ∧
      (∃ u : Fin n → ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * ℓ))), (∀ i, u i ∈ U) ∧
        ∀ c : Fin n → ↥K, (∀ i, c i ∈ W₀) → (∃ i, c i ∉ W₀.nonunits) → ∑ i, ι (c i) * u i ∉ U.nonunits) := by
  classical
  haveI hℓ0 : NeZero ℓ := ⟨(Fact.out : ℓ.Prime).ne_zero⟩
  haveI hMℓ : NeZero (M * ℓ) := ⟨mul_ne_zero (NeZero.ne M) (Fact.out : ℓ.Prime).ne_zero⟩
  haveI : NeZero (M * p) := ⟨mul_ne_zero (NeZero.ne M) (Fact.out : p.Prime).ne_zero⟩
  haveI : NeZero (M * p * ℓ) := ⟨mul_ne_zero (NeZero.ne (M * p)) (Fact.out : ℓ.Prime).ne_zero⟩
  haveI : FaithfulSMul A L := (faithfulSMul_iff_algebraMap_injective A L).mpr (IsFractionRing.injective A L)
  refine ⟨if ℓ ∣ M then ℓ else ℓ + 1, ModularCurve.XOneP.exists_fin_span_heckeRoof_x1_mul p M hM hpM L K hK ℓ hℓp ι hι, ?_⟩

  have hp0 : (p : IsLocalRing.ResidueField A) = 0 := by
    rw [← map_natCast (IsLocalRing.residue A), IsLocalRing.residue_eq_zero_iff]; exact hAp
  haveI : CharP (IsLocalRing.ResidueField A) p := by
    have h := CharP.ringChar_of_prime_eq_zero (Fact.out : p.Prime) hp0
    exact h ▸ ringChar.charP (IsLocalRing.ResidueField A)
  obtain ⟨w⟩ := ModularCurve.nonempty_integralWeightOneForm (IsLocalRing.ResidueField A) M (by omega)

  subst hK
  have hjq_mem : ModularCurve.jq ∈ ModularCurve.x1FunctionField (M * p) := by
    have h1 : ModularCurve.jqModC ℚ ∈ ModularCurve.modularFunctionFieldFullC ℚ (M * p) := ModularCurve.jqModC_mem_full ℚ (M * p)
    have h2 := ModularCurve.modularFunctionFieldFullC_le_qExpFunctionFieldC_gamma0 ℚ (M * p) h1
    exact ModularCurve.qExpFunctionFieldC_mono ℚ (CongruenceSubgroup.Gamma1_in_Gamma0 (M * p)) h2
  let j : ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p))) :=
    ⟨ModularCurve.coeffEmb L ModularCurve.jq, ModularCurve.coeffEmb_mem_laurentBaseChange L hjq_mem⟩
  have hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq := rfl
  haveI : Fact (j ≠ 0) := ⟨fun h => by
    have h1 : (ModularCurve.coeffEmb L ModularCurve.jq).coeff (-1) = 0 := by
      rw [← hj, h]; rfl
    rw [ModularCurve.coeffEmb_coeff, ModularCurve.coeff_jq_neg_one, map_one] at h1
    exact one_ne_zero h1⟩
  obtain ⟨W₀', W₁', -, -, -, -, -, h6', -⟩ :=
    ModularCurve.XOneP.exists_valuationSubring_pair_x1_mul p M hM hpM L ζ hζ _ rfl A hAp hζA j hj w
  have h6a : ∀ (f : ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p)))) (x y : PowerSeries A),
      y.map (IsLocalRing.residue A) ≠ 0 → (f : LaurentSeries L) * emb A L y = emb A L x →
      red A x / red A y ∈ (ModularCurve.igusaFunctionFieldX1C (IsLocalRing.ResidueField A) M w : Set _) :=
    fun f x y hy hxy => (h6' f x y hy hxy).1

  obtain ⟨hα, Ig', hIg', hβ⟩ := ModularCurve.finrank_adjoin_jqNModC_igusaFunctionFieldX1C_eq p (IsLocalRing.ResidueField A) M hM hpM w ℓ hℓp
  have hdpos : 0 < (if ℓ ∣ M then ℓ else ℓ + 1) := by split_ifs <;> have := (Fact.out : ℓ.Prime).pos <;> omega
  have indα := forall_eq_zero_of_sum_mul_pow_eq_zero (ModularCurve.igusaFunctionFieldX1C (IsLocalRing.ResidueField A) M w)
    (ModularCurve.jqNModC (IsLocalRing.ResidueField A) (M * ℓ)) _ hdpos hα
  have indβ := forall_eq_zero_of_sum_mul_pow_eq_zero Ig' (ModularCurve.jqModC (IsLocalRing.ResidueField A)) _ hdpos hβ

  have memKℓ : ∀ (e : ℕ) [NeZero e], e ∣ M * p * ℓ →
      ModularCurve.coeffEmb L (ModularCurve.qExpand ℚ e (ModularCurve.jqModC ℚ)) ∈
        ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * ℓ)) := by
    intro e _ he
    apply ModularCurve.coeffEmb_mem_laurentBaseChange L
    have h1 := ModularCurve.jqModCd_mem_full ℚ (M * p * ℓ) he
    have h2 := ModularCurve.modularFunctionFieldFullC_le_qExpFunctionFieldC_gamma0 ℚ (M * p * ℓ) h1
    exact ModularCurve.qExpFunctionFieldC_mono ℚ inf_le_right h2

  have hU' : ∀ f : ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * ℓ))), f ∈ U ↔ ∃ x y : PowerSeries A, y.map (IsLocalRing.residue A) ≠ 0 ∧
      (algebraMap _ (LaurentSeries L) f) * emb A L y = emb A L x := hU
  rcases hι with hια | hιβ
  ·
    let J : ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * ℓ))) := ⟨_, memKℓ (M * ℓ) ⟨p, by ring⟩⟩
    have hJ : algebraMap _ (LaurentSeries L) J = ModularCurve.jqNModC L (M * ℓ) := by
      show ModularCurve.coeffEmb L _ = _
      rw [ModularCurve.coeffEmb, ← ModularCurve.jqNModC, ModularCurve.coeffMap_jqNModC]
    refine ⟨fun i => J ^ (i : ℕ), fun i => ?_, fun c hc hunit => ?_⟩
    ·
      refine (hU' _).mpr ⟨expandPS (M * ℓ) ((ModularCurve.jNum.map (Int.castRingHom A)) ^ (i : ℕ)), PowerSeries.X ^ (M * ℓ * i),
        map_X_pow_ne_zero _, ?_⟩
      rw [map_pow, hJ, emb_X_pow, emb_expandPS_jNum_pow]
      exact jqNModC_pow_mul_ofPowerSeries_X_pow L (M * ℓ) i
    · refine sum_mul_pow_not_mem_nonunits (A := A) (L := L) _ (algebraMap (↥(ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * ℓ)))) (LaurentSeries L)) (algebraMap (↥(ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * ℓ)))) (LaurentSeries L)).injective ι.toRingHom
        (RingHom.id _) (fun f x y h => by simpa [hια f] using h) (fun z => Iff.rfl) (RingHom.id _) (fun _ _ h => h) (fun z => rfl)
        W₀ hW₀ _ h6a U hU' _ J
        (fun i => expandPS (M * ℓ) ((ModularCurve.jNum.map (Int.castRingHom A)) ^ (i : ℕ))) (fun i => PowerSeries.X ^ (M * ℓ * i))
        (fun i => map_X_pow_ne_zero _) (fun i => ?_) (ModularCurve.jqNModC (IsLocalRing.ResidueField A) (M * ℓ)) (fun i => ?_) ?_ c hc hunit
      · rw [hJ, emb_X_pow, emb_expandPS_jNum_pow]
        exact jqNModC_pow_mul_ofPowerSeries_X_pow L (M * ℓ) i
      · rw [red_expandPS, red_jNum_pow, qExpand_ofPowerSeries, red_apply, map_pow, PowerSeries.map_X]
        exact (jqNModC_pow_mul_ofPowerSeries_X_pow (IsLocalRing.ResidueField A) (M * ℓ) i).symm
      · intro r hr hsum
        refine indα r (fun i => ?_) hsum
        obtain ⟨z, hz, hzr⟩ := hr i
        rw [← hzr]; simpa using hz
  ·
    let J : ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * ℓ))) := ⟨_, memKℓ 1 (one_dvd _)⟩
    have hJ : algebraMap _ (LaurentSeries L) J = ModularCurve.jqModC L := by
      show ModularCurve.coeffEmb L _ = _
      rw [ModularCurve.qExpand_one_apply, ModularCurve.coeffEmb, ModularCurve.coeffMap_jqModC]
    have hJi : ∀ i : ℕ, ModularCurve.jqModC L ^ i * emb A L (PowerSeries.X ^ i) = emb A L ((ModularCurve.jNum.map (Int.castRingHom A)) ^ i) := by
      intro i
      rw [emb_X_pow, emb_jNum_pow]
      exact jqModC_pow_mul_ofPowerSeries_X_pow L i
    refine ⟨fun i => J ^ (i : ℕ), fun i => ?_, fun c hc hunit => ?_⟩
    · exact (hU' _).mpr ⟨(ModularCurve.jNum.map (Int.castRingHom A)) ^ (i : ℕ), PowerSeries.X ^ (i : ℕ), map_X_pow_ne_zero _,
        by rw [map_pow, hJ]; exact hJi i⟩
    · refine sum_mul_pow_not_mem_nonunits (A := A) (L := L) _ (algebraMap (↥(ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * ℓ)))) (LaurentSeries L)) (algebraMap (↥(ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * ℓ)))) (LaurentSeries L)).injective ι.toRingHom
        (expandPSHom ℓ) (fun f x y h => ?_) (fun z => ?_) (ModularCurve.qExpand _ ℓ) (ModularCurve.qExpand_injective (R := IsLocalRing.ResidueField A) (N := ℓ)) (fun z => red_expandPS ℓ z)
        W₀ hW₀ _ h6a U hU' _ J
        (fun i => (ModularCurve.jNum.map (Int.castRingHom A)) ^ (i : ℕ)) (fun i => PowerSeries.X ^ (i : ℕ))
        (fun i => map_X_pow_ne_zero _) (fun i => by rw [hJ]; exact hJi i) (ModularCurve.jqModC (IsLocalRing.ResidueField A)) (fun i => ?_) ?_ c hc hunit
      ·
        show algebraMap _ (LaurentSeries L) (ι f) * emb A L (expandPS ℓ y) = emb A L (expandPS ℓ x)
        rw [show algebraMap _ (LaurentSeries L) (ι f) = ModularCurve.qExpand L ℓ (f : LaurentSeries L) from hιβ f,
          emb_apply, emb_apply, map_expandPS, map_expandPS, ← qExpand_ofPowerSeries, ← qExpand_ofPowerSeries, ← map_mul,
          ← emb_apply, ← emb_apply, h]
      · show (expandPS ℓ z).map _ ≠ 0 ↔ _
        rw [map_expandPS, Ne, expandPS_eq_zero_iff]
      · rw [red_jNum_pow, red_apply, (PowerSeries.map (IsLocalRing.residue A)).map_pow, PowerSeries.map_X]
        exact (jqModC_pow_mul_ofPowerSeries_X_pow (IsLocalRing.ResidueField A) i).symm
      · intro r hr hsum
        refine indβ r (fun i => ?_) hsum
        obtain ⟨z, hz, hzr⟩ := hr i
        rw [← hzr]
        show ModularCurve.qExpand _ ℓ z ∈ (Ig' : Set _)
        rw [hIg']
        exact ⟨z, hz, rfl⟩

end S_ModularCurve_XOneP_exists_span_and_residueIndependent_gauss_heckeRoof_x1_mul
end P2MW
export P2MW.S_ModularCurve_XOneP_exists_span_and_residueIndependent_gauss_heckeRoof_x1_mul (solution)
