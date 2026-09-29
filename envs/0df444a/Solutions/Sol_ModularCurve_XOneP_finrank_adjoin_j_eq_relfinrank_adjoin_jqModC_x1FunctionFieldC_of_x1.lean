-- Prove2me | solution 1 for ModularCurve.XOneP.finrank_adjoin_j_eq_relfinrank_adjoin_jqModC_x1FunctionFieldC_of_x1
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/eea095e9-bfd0-5d21-81f2-a348c6e9feb3

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_IgusaFunctionFieldX1
import Theorems.Thm_ValuationSubring_exists_ringHom_laurentSeries_residueField_of_forall_mem_iff_exists_powerSeries
import Theorems.Thm_ModularCurve_exists_gaussValuationSubring_laurentBaseChange_x1FunctionField
import Theorems.Thm_ModularCurve_exists_valuationSubring_adjoin_isDiscreteValuationRing_mem_iff_of_laurentBaseChange_x1FunctionField
import Theorems.Thm_ModularCurve_XOneP_gaussReduction_mem_x1FunctionFieldC_of_x1
import Theorems.Thm_ModularCurve_XOneP_mem_valuationSubring_iff_exists_powerSeries_of_x1
import Theorems.Thm_ValuationSubring_finsum_ramificationIdx_mul_inertiaDeg_eq_finrank
import Theorems.Thm_ModularCurve_finiteDimensional_adjoin_of_coe_eq_coeffEmb_jq_of_eq_laurentBaseChange
import Theorems.Thm_ModularCurve_transcendental_of_coe_eq_coeffEmb_jq
import Theorems.Thm_ModularCurve_exists_powerSeries_coeffEmb_jq_mul_eq_and_div_eq_jqModC_and_qExpand
import Theorems.Thm_ModularCurve_transcendental_jqModC
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XOneP_finrank_adjoin_j_eq_relfinrank_adjoin_jqModC_x1FunctionFieldC_of_x1
p2m_attr_erase "instance" "AlgebraicCurve.TwoChartIntegralModel.isOpenImmersion_ιInf AlgebraicCurve.TwoChartIntegralModel.isOpenImmersion_fInf AlgebraicCurve.TwoChartIntegralModel.isOpenImmersion_ιFin AlgebraicCurve.TwoChartIntegralModel.isOpenImmersion_fFin GaloisRepAdic.instAddCommGroup GaloisRepAdic.instFree GaloisRepAdic.instFinite GaloisRepAdic.instModule ResidualGaloisRep.instModule ResidualGaloisRep.instModuleFinite ResidualGaloisRep.instAddCommGroup WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instFinite AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin CohCarrier.iotaDeg_range_finiteIndex CohCarrier.Gamma0Upper_finiteIndex TateModule.instModule TateModule.instSMul CohCarrier.HeckeData.V_isScalarTower CohCarrier.HeckeData.opSubalgebra_isMulCommutative CohCarrier.HeckeData.mTheta_isPrime ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.instIsDomainTensorProduct"
p2m_attr_erase "instance" "AlgebraicClosure.Rat.isGalois AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.instIsElliptic_tateBase ModularCurve.instIsElliptic_tateLaurent ModularCurve.KatzGamma0Form.instModule ModularCurve.KatzGamma0Form.instZero"
p2m_attr_erase "instance" "ModularCurve.KatzLevelPForm.instSMul ModularCurve.KatzGamma0Form.instAdd ModularCurve.KatzLevelPForm.instAddCommGroup ModularCurve.KatzGamma0Form.instNeg ModularCurve.KatzGamma0Form.instAddCommGroup ModularCurve.KatzLevelPForm.instAdd ModularCurve.KatzLevelPForm.instSub ModularCurve.KatzLevelPForm.instNeg ModularCurve.KatzGamma0Form.instSMul ModularCurve.KatzGamma0Form.instSub ModularCurve.KatzLevelPForm.instZero ModularCurve.KatzLevelPForm.instModule KatzModularForm.instAddCommGroup KatzModularForm.instSub KatzModularForm.instZero KatzModularForm.instModule KatzModularForm.instAdd KatzModularForm.instNeg KatzModularForm.instSMul WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup"
p2m_attr_erase "instance" "TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free AlgebraicCurve.CurveModel.chartRing_finitePresentation AlgebraicCurve.CurveModel.isProper AlgebraicCurve.CurveModel.isIntegral AlgebraicCurve.CurveModel.smooth"
p2m_attr_erase "simp" "ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg AlgebraicCurve.TwoChartIntegralModel.ιInf_toBase AlgebraicCurve.TwoChartIntegralModel.polynomialToChartFin_X AlgebraicCurve.TwoChartIntegralModel.coe_chartBaseChange AlgebraicCurve.TwoChartIntegralModel.polynomialToChartInf_X AlgebraicCurve.TwoChartIntegralModel.ιFin_toBase AlgebraicCurve.TwoChartIntegralModel.ιFin_toBase_assoc AlgebraicCurve.TwoChartIntegralModel.coe_jChartFin AlgebraicCurve.TwoChartIntegralModel.ιInf_toBase_assoc AlgebraicCurve.TwoChartIntegralModel.coe_jInvChartInf GaloisRepAdic.mk.injEq GaloisRepAdic.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.injEq ResidualGaloisRep.mk.sizeOf_spec ResidualGaloisRep.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq ResidualGaloisRep.Equiv.mk.sizeOf_spec ResidualGaloisRep.Equiv.mk.injEq AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces CohCarrier.conjUpperMat_apply_11 CohCarrier.conjUpperMat_apply_10 CohCarrier.mem_Gamma0Upper CohCarrier.val_gamma0Units"
p2m_attr_erase "simp" "AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap ModularCurve.JH.torsionGaloisRep_apply TateModule.smul_apply TateModule.coe_mulP TateModule.proj_apply TateModule.coe_add TateModule.coe_sub WeierstrassCurve.tateModuleRepOfBasis_V TateModule.coe_zero TateModule.rep_apply WeierstrassCurve.tateModuleRep_V WeierstrassCurve.tateModuleRepOfBasis_ρ_apply GaloisRep.padicIntToRingLevel_apply TateModule.coe_neg WeierstrassCurve.tateModuleRep_ρ_apply ModularCurve.qExpandAlgHomC_apply ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL CohCarrier.Gen.dia.sizeOf_spec CohCarrier.Gen.U.injEq CohCarrier.Gen.T.sizeOf_spec CohCarrier.Gen.U.sizeOf_spec CohCarrier.Gen.T.injEq CohCarrier.Gen.dia.injEq CohCarrier.HeckeData.mk.sizeOf_spec CohCarrier.HeckeData.opAlgHom_X"
p2m_attr_erase "simp" "CohCarrier.HeckeData.toMLₒ_apply CohCarrier.HeckeData.mk.injEq CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.ProjectiveLine.map_mk ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.coe_cuspidalDivisor₀ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero"
p2m_attr_erase "simp" "ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe"
p2m_attr_erase "simp" "AlgebraicCurve.mulAdele_one AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule"
p2m_attr_erase "simp" "AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule ModularCurve.LevelN.coe_jGen HahnSeries.ramScale_apply WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.cuspData_yP ModularCurve.qTwistAlgHom_apply ModularCurve.cuspData_yQ ModularCurve.cuspData_xP ModularCurve.cuspData_xQ ModularCurve.val_cyclZeta"
p2m_attr_erase "simp" "ModularCurve.cuspShift_one ModularCurve.cuspShift_zero ModularCurve.LevelPData.mk.sizeOf_spec ModularCurve.KatzLevelPForm.neg_toFun ModularCurve.LevelP.coe_swapW ModularCurve.KatzLevelPForm.swap_swap KatzModularForm.pullbackLevelP_toFun ModularCurve.LevelPData.swap_xQ KatzModularForm.pullbackLevelP_zero ModularCurve.LevelPData.map_yP ModularCurve.KatzLevelPForm.swap_neg ModularCurve.KatzGamma0Form.toKatzLevelPForm_sub ModularCurve.KatzLevelPForm.swap_add KatzModularForm.swap_pullbackLevelP ModularCurve.KatzGamma0Form.toKatzLevelPForm_add ModularCurve.KatzLevelPForm.swap_smul ModularCurve.LevelPData.map_yQ ModularCurve.KatzLevelPForm.mk.injEq ModularCurve.KatzLevelPForm.zero_toFun KatzModularForm.pullbackLevelP_smul ModularCurve.LevelPData.swap_xP ModularCurve.KatzGamma0Form.toKatzLevelPForm_mul ModularCurve.KatzGamma0Form.toKatzLevelPForm_neg ModularCurve.LevelPData.variableChange_xQ KatzModularForm.pullbackGamma0_toKatzLevelPForm ModularCurve.KatzLevelPForm.mk.sizeOf_spec ModularCurve.KatzLevelPForm.swap_zero ModularCurve.LevelP.coe_unipotentU ModularCurve.KatzLevelPForm.mul_toFun ModularCurve.LevelPData.variableChange_yP ModularCurve.LevelPData.mk.injEq ModularCurve.KatzLevelPForm.sub_toFun ModularCurve.LevelPData.variableChange_xP ModularCurve.KatzLevelPForm.smul_toFun ModularCurve.LevelPData.swap_yP ModularCurve.LevelPData.map_xP ModularCurve.LevelPData.swap_swap ModularCurve.LevelPData.swap_yQ ModularCurve.KatzGamma0Form.toKatzLevelPForm_zero ModularCurve.KatzGamma0Form.mk.injEq"
p2m_attr_erase "simp" "ModularCurve.KatzLevelPForm.swap_toFun KatzModularForm.pullbackLevelP_add ModularCurve.KatzGamma0Form.mk.sizeOf_spec ModularCurve.LevelPData.variableChange_yQ ModularCurve.KatzLevelPForm.swap_sub ModularCurve.KatzGamma0Form.toKatzLevelPForm_smul ModularCurve.LevelPData.map_xQ ModularCurve.KatzLevelPForm.add_toFun KatzModularForm.c₆_toFun KatzModularForm.neg_toFun KatzModularForm.mul_toFun KatzModularForm.qExpansion_neg KatzModularForm.discr_toFun KatzModularForm.qExpansion_sub KatzModularForm.qExpansion_add KatzModularForm.qExpansion_mul KatzModularForm.zero_toFun KatzModularForm.mk.injEq KatzModularForm.qExpansion_smul KatzModularForm.smul_toFun KatzModularForm.add_toFun KatzModularForm.sub_toFun KatzModularForm.c₄_toFun KatzModularForm.qExpansion_zero KatzModularForm.mk.sizeOf_spec TateCurve.tateTorsionPoint_zero_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ"
p2m_attr_erase "simp" "TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec"
p2m_attr_erase "simp" "WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT"
p2m_attr_erase "simp" "WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm"
p2m_attr_erase "simp" "AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff RegularLocalRingQuotientAscent.dualNumberFst_apply AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq AlgebraicCurve.CurveModel.mk.injEq AlgebraicCurve.CurveModel.mk.sizeOf_spec"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 32000000

open CongruenceSubgroup ModularCurve
open scoped MatrixGroups ModularForm

noncomputable section

namespace S1cAux

theorem exists_reductionField
    (L : Type) [Field L] (K : IntermediateField L (LaurentSeries L))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    (W₀ : ValuationSubring ↥K)
    (hW₀ : ∀ f : ↥K, f ∈ W₀ ↔ ∃ x y : PowerSeries A, y.map (IsLocalRing.residue A) ≠ 0 ∧
      (f : LaurentSeries L) * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap A L))
        = HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap A L)))
    (hA : ∀ a : A, algebraMap A ↥K a ∈ W₀)
    (hnu : ∀ (f : ↥K) (x y : PowerSeries A), y.map (IsLocalRing.residue A) ≠ 0 →
      (f : LaurentSeries L) * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap A L))
        = HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap A L)) →
      (f ∈ W₀.nonunits ↔ x.map (IsLocalRing.residue A) = 0)) :
    ∃ R₀ : IntermediateField (IsLocalRing.ResidueField A) (LaurentSeries (IsLocalRing.ResidueField A)),
      ∀ z : LaurentSeries (IsLocalRing.ResidueField A), z ∈ R₀ ↔
        ∃ (f : ↥K) (x y : PowerSeries A), y.map (IsLocalRing.residue A) ≠ 0 ∧
          (f : LaurentSeries L) * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap A L))
            = HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap A L)) ∧
          HahnSeries.ofPowerSeries ℤ (IsLocalRing.ResidueField A) (x.map (IsLocalRing.residue A)) /
            HahnSeries.ofPowerSeries ℤ (IsLocalRing.ResidueField A) (y.map (IsLocalRing.residue A)) = z := by
  classical
  obtain ⟨red, hred, hker⟩ :=
    ValuationSubring.exists_ringHom_laurentSeries_residueField_of_forall_mem_iff_exists_powerSeries
      L K A W₀ hW₀ hnu

  have hconst : ∀ a : A, red ⟨algebraMap A ↥K a, hA a⟩ =
      algebraMap (IsLocalRing.ResidueField A) (LaurentSeries (IsLocalRing.ResidueField A))
        (IsLocalRing.residue A a) := by
    intro a
    have h1 : (1 : PowerSeries A).map (IsLocalRing.residue A) ≠ 0 := by rw [map_one]; exact one_ne_zero
    have hpres : ((⟨algebraMap A ↥K a, hA a⟩ : ↥W₀) : ↥K) = algebraMap A ↥K a := rfl
    have h2 : ((algebraMap A ↥K a : ↥K) : LaurentSeries L) *
        HahnSeries.ofPowerSeries ℤ L ((1 : PowerSeries A).map (algebraMap A L)) =
        HahnSeries.ofPowerSeries ℤ L ((PowerSeries.C a).map (algebraMap A L)) := by
      rw [map_one, map_one, mul_one, PowerSeries.map_C, HahnSeries.ofPowerSeries_C,
        IsScalarTower.algebraMap_apply A L ↥K]
      show algebraMap L (LaurentSeries L) (algebraMap A L a) = _
      rw [algebraMap_laurentSeries_eq_single, HahnSeries.C_apply]
    rw [hred _ (PowerSeries.C a) 1 h1 (by rw [hpres]; exact h2), PowerSeries.map_C, map_one, map_one,
      div_one, HahnSeries.ofPowerSeries_C, algebraMap_laurentSeries_eq_single, HahnSeries.C_apply]
  let R₀ : IntermediateField (IsLocalRing.ResidueField A) (LaurentSeries (IsLocalRing.ResidueField A)) :=
    { carrier := Set.range red
      mul_mem' := by
        rintro _ _ ⟨f, rfl⟩ ⟨g, rfl⟩
        exact ⟨f * g, map_mul red f g⟩
      one_mem' := ⟨1, map_one red⟩
      add_mem' := by
        rintro _ _ ⟨f, rfl⟩ ⟨g, rfl⟩
        exact ⟨f + g, map_add red f g⟩
      zero_mem' := ⟨0, map_zero red⟩
      algebraMap_mem' := by
        intro c
        obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective c
        exact ⟨_, hconst a⟩
      inv_mem' := by
        rintro _ ⟨f, rfl⟩
        by_cases hz : red f = 0
        · rw [hz, inv_zero]; exact ⟨0, map_zero red⟩
        · have hf : f ∉ IsLocalRing.maximalIdeal ↥W₀ := by
            rw [← hker]; exact hz
          have hu : IsUnit f := by
            by_contra h
            exact hf ((IsLocalRing.mem_maximalIdeal f).mpr h)
          obtain ⟨u, rfl⟩ := hu
          exact ⟨↑u⁻¹, map_units_inv red u⟩ }
  refine ⟨R₀, fun z => ⟨?_, ?_⟩⟩
  · rintro ⟨f, rfl⟩
    obtain ⟨x, y, hy, hxy⟩ := (hW₀ (f : ↥K)).mp f.2
    exact ⟨f, x, y, hy, hxy, (hred f x y hy hxy).symm⟩
  · rintro ⟨f, x, y, hy, hxy, rfl⟩
    have hf : f ∈ W₀ := (hW₀ f).mpr ⟨x, y, hy, hxy⟩
    exact ⟨⟨f, hf⟩, hred ⟨f, hf⟩ x y hy hxy⟩

theorem exists_red_and_reductionField
    (L : Type) [Field L] (K : IntermediateField L (LaurentSeries L))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    (W₀ : ValuationSubring ↥K)
    (hW₀ : ∀ f : ↥K, f ∈ W₀ ↔ ∃ x y : PowerSeries A, y.map (IsLocalRing.residue A) ≠ 0 ∧
      (f : LaurentSeries L) * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap A L))
        = HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap A L)))
    (hA : ∀ a : A, algebraMap A ↥K a ∈ W₀)
    (hnu : ∀ (f : ↥K) (x y : PowerSeries A), y.map (IsLocalRing.residue A) ≠ 0 →
      (f : LaurentSeries L) * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap A L))
        = HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap A L)) →
      (f ∈ W₀.nonunits ↔ x.map (IsLocalRing.residue A) = 0)) :
    ∃ (red : ↥W₀ →+* LaurentSeries (IsLocalRing.ResidueField A))
      (R₀ : IntermediateField (IsLocalRing.ResidueField A) (LaurentSeries (IsLocalRing.ResidueField A))),
      (∀ (f : ↥W₀) (x y : PowerSeries A), y.map (IsLocalRing.residue A) ≠ 0 →
        ((f : ↥K) : LaurentSeries L) * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap A L))
          = HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap A L)) →
        red f = HahnSeries.ofPowerSeries ℤ (IsLocalRing.ResidueField A) (x.map (IsLocalRing.residue A)) /
          HahnSeries.ofPowerSeries ℤ (IsLocalRing.ResidueField A) (y.map (IsLocalRing.residue A))) ∧
      RingHom.ker red = IsLocalRing.maximalIdeal ↥W₀ ∧
      (∀ a : A, red ⟨algebraMap A ↥K a, hA a⟩ =
        algebraMap (IsLocalRing.ResidueField A) (LaurentSeries (IsLocalRing.ResidueField A))
          (IsLocalRing.residue A a)) ∧
      (∀ z : LaurentSeries (IsLocalRing.ResidueField A), z ∈ R₀ ↔ ∃ w : ↥W₀, red w = z) ∧
      (∀ z : LaurentSeries (IsLocalRing.ResidueField A), z ∈ R₀ ↔
        ∃ (f : ↥K) (x y : PowerSeries A), y.map (IsLocalRing.residue A) ≠ 0 ∧
          (f : LaurentSeries L) * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap A L))
            = HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap A L)) ∧
          HahnSeries.ofPowerSeries ℤ (IsLocalRing.ResidueField A) (x.map (IsLocalRing.residue A)) /
            HahnSeries.ofPowerSeries ℤ (IsLocalRing.ResidueField A) (y.map (IsLocalRing.residue A)) = z) := by
  classical
  obtain ⟨red, hred, hker⟩ :=
    ValuationSubring.exists_ringHom_laurentSeries_residueField_of_forall_mem_iff_exists_powerSeries
      L K A W₀ hW₀ hnu

  have hconst : ∀ a : A, red ⟨algebraMap A ↥K a, hA a⟩ =
      algebraMap (IsLocalRing.ResidueField A) (LaurentSeries (IsLocalRing.ResidueField A))
        (IsLocalRing.residue A a) := by
    intro a
    have h1 : (1 : PowerSeries A).map (IsLocalRing.residue A) ≠ 0 := by rw [map_one]; exact one_ne_zero
    have hpres : ((⟨algebraMap A ↥K a, hA a⟩ : ↥W₀) : ↥K) = algebraMap A ↥K a := rfl
    have h2 : ((algebraMap A ↥K a : ↥K) : LaurentSeries L) *
        HahnSeries.ofPowerSeries ℤ L ((1 : PowerSeries A).map (algebraMap A L)) =
        HahnSeries.ofPowerSeries ℤ L ((PowerSeries.C a).map (algebraMap A L)) := by
      rw [map_one, map_one, mul_one, PowerSeries.map_C, HahnSeries.ofPowerSeries_C,
        IsScalarTower.algebraMap_apply A L ↥K]
      show algebraMap L (LaurentSeries L) (algebraMap A L a) = _
      rw [algebraMap_laurentSeries_eq_single, HahnSeries.C_apply]
    rw [hred _ (PowerSeries.C a) 1 h1 (by rw [hpres]; exact h2), PowerSeries.map_C, map_one, map_one,
      div_one, HahnSeries.ofPowerSeries_C, algebraMap_laurentSeries_eq_single, HahnSeries.C_apply]
  let R₀ : IntermediateField (IsLocalRing.ResidueField A) (LaurentSeries (IsLocalRing.ResidueField A)) :=
    { carrier := Set.range red
      mul_mem' := by
        rintro _ _ ⟨f, rfl⟩ ⟨g, rfl⟩
        exact ⟨f * g, map_mul red f g⟩
      one_mem' := ⟨1, map_one red⟩
      add_mem' := by
        rintro _ _ ⟨f, rfl⟩ ⟨g, rfl⟩
        exact ⟨f + g, map_add red f g⟩
      zero_mem' := ⟨0, map_zero red⟩
      algebraMap_mem' := by
        intro c
        obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective c
        exact ⟨_, hconst a⟩
      inv_mem' := by
        rintro _ ⟨f, rfl⟩
        by_cases hz : red f = 0
        · rw [hz, inv_zero]; exact ⟨0, map_zero red⟩
        · have hf : f ∉ IsLocalRing.maximalIdeal ↥W₀ := by
            rw [← hker]; exact hz
          have hu : IsUnit f := by
            by_contra h
            exact hf ((IsLocalRing.mem_maximalIdeal f).mpr h)
          obtain ⟨u, rfl⟩ := hu
          exact ⟨↑u⁻¹, map_units_inv red u⟩ }
  refine ⟨red, R₀, hred, hker, hconst, fun z => Iff.rfl, fun z => ⟨?_, ?_⟩⟩
  · rintro ⟨f, rfl⟩
    obtain ⟨x, y, hy, hxy⟩ := (hW₀ (f : ↥K)).mp f.2
    exact ⟨f, x, y, hy, hxy, (hred f x y hy hxy).symm⟩
  · rintro ⟨f, x, y, hy, hxy, rfl⟩
    have hf : f ∈ W₀ := (hW₀ f).mpr ⟨x, y, hy, hxy⟩
    exact ⟨⟨f, hf⟩, hred ⟨f, hf⟩ x y hy hxy⟩

theorem coeffEmb_intSeriesC (L : Type*) [Field L] [CharZero L] (q : PowerSeries ℤ) :
    coeffEmb L (intSeriesC ℚ q) = HahnSeries.ofPowerSeries ℤ L (q.map (Int.castRingHom L)) := by
  ext n
  rw [coeffEmb_coeff, intSeriesC, PowerSeries.coeff_coe, PowerSeries.coeff_coe]
  split_ifs
  · simp
  · simp

theorem map_intCast_map {A B : Type*} [CommRing A] [CommRing B] (φ : A →+* B) (q : PowerSeries ℤ) :
    (q.map (Int.castRingHom A)).map φ = q.map (Int.castRingHom B) := by
  have h : φ.comp (Int.castRingHom A) = Int.castRingHom B := RingHom.ext_int _ _
  rw [← h, PowerSeries.map_comp, RingHom.comp_apply]

theorem one_mem_strictPeriods_Gamma1 (N : ℕ) :
    (1 : ℝ) ∈ ((Gamma1 N : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
  rw [Subgroup.mem_strictPeriods_iff]
  refine ⟨ModularGroup.T, ?_, ?_⟩
  · exact (by rw [Gamma1_mem]; simp [ModularGroup.coe_T] : ModularGroup.T ∈ Gamma1 N)
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [ModularGroup.T, Matrix.GeneralLinearGroup.upperRightHom]

theorem exists_ratio_presentation
    (p : ℕ) (M : ℕ) [NeZero (M * p)]
    (L : Type) [Field L] [CharZero L]
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = laurentBaseChange L (x1FunctionField (M * p)))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    {k : ℤ} (f g : ModularForm ((Gamma1 (M * p) : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) k)
    (pf pg : PowerSeries ℤ) (hf : IsIntegralQExp f pf) (hg : IsIntegralQExp g pg)
    (hg0 : intSeriesC (IsLocalRing.ResidueField A) pg ≠ 0) :
    ∃ F : ↥K,
      (pg.map (Int.castRingHom A)).map (IsLocalRing.residue A) ≠ 0 ∧
      (F : LaurentSeries L) * HahnSeries.ofPowerSeries ℤ L ((pg.map (Int.castRingHom A)).map (algebraMap A L))
        = HahnSeries.ofPowerSeries ℤ L ((pf.map (Int.castRingHom A)).map (algebraMap A L)) ∧
      HahnSeries.ofPowerSeries ℤ (IsLocalRing.ResidueField A) ((pf.map (Int.castRingHom A)).map (IsLocalRing.residue A)) /
        HahnSeries.ofPowerSeries ℤ (IsLocalRing.ResidueField A) ((pg.map (Int.castRingHom A)).map (IsLocalRing.residue A))
        = intSeriesC (IsLocalRing.ResidueField A) pf / intSeriesC (IsLocalRing.ResidueField A) pg := by
  have hpg0 : pg ≠ 0 := by
    rintro rfl; exact hg0 (by rw [intSeriesC_zero])
  have hgQ : intSeriesC ℚ pg ≠ 0 := by
    intro h
    apply hpg0
    apply PowerSeries.map_injective (Int.castRingHom ℚ) Int.cast_injective
    rw [map_zero]
    exact HahnSeries.ofPowerSeries_injective (h.trans (map_zero (HahnSeries.ofPowerSeries ℤ ℚ)).symm)
  have hmem : intSeriesC ℚ pf / intSeriesC ℚ pg ∈ x1FunctionField (M * p) :=
    div_mem_qExpFunctionFieldC f g hf hg hgQ
  have hFK : coeffEmb L (intSeriesC ℚ pf / intSeriesC ℚ pg) ∈ K := by
    rw [hK]; exact coeffEmb_mem_laurentBaseChange L hmem
  refine ⟨⟨_, hFK⟩, ?_, ?_, ?_⟩
  · rw [map_intCast_map]; exact fun h => hg0 (by rw [intSeriesC, h, map_zero])
  · rw [map_intCast_map, map_intCast_map]
    show coeffEmb L (intSeriesC ℚ pf / intSeriesC ℚ pg) * _ = _
    rw [map_div₀, coeffEmb_intSeriesC, coeffEmb_intSeriesC]
    have hne : HahnSeries.ofPowerSeries ℤ L (pg.map (Int.castRingHom L)) ≠ 0 := by
      intro h
      apply hpg0
      apply PowerSeries.map_injective (Int.castRingHom L) Int.cast_injective
      rw [map_zero]
      exact HahnSeries.ofPowerSeries_injective (h.trans (map_zero (HahnSeries.ofPowerSeries ℤ L)).symm)
    rw [div_mul_cancel₀ _ hne]
  · rw [map_intCast_map, map_intCast_map]; rfl

end S1cAux

end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CongruenceSubgroup ModularCurve
open scoped MatrixGroups ModularForm

theorem DegMAux_T_mem (N : ℕ) : ModularGroup.T ∈ CongruenceSubgroup.Gamma1 N := by
  rw [CongruenceSubgroup.Gamma1_mem]; simp [ModularGroup.coe_T]

theorem solution
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hM : 5 ≤ M) (hpM : ¬ p ∣ M)
    (L : Type) [Field L] [CharZero L] [IsCyclotomicExtension {p} ℚ L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ p)
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField M))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAp : (p : A) ∈ IsLocalRing.maximalIdeal A) (hζA : ∃ z : A, algebraMap A L z = ζ)
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j ≠ 0)] :
    Module.finrank ↥(IntermediateField.adjoin L ({j} : Set ↥K)) ↥K =
      IntermediateField.relfinrank
        (IntermediateField.adjoin (IsLocalRing.ResidueField A)
          ({ModularCurve.jqModC (IsLocalRing.ResidueField A)} : Set (LaurentSeries (IsLocalRing.ResidueField A))))
        (ModularCurve.x1FunctionFieldC (IsLocalRing.ResidueField A) M) := by
  classical
  haveI hp : Fact p.Prime := inferInstance

  obtain ⟨W, hW, hWA, hWm, hWj, hWnu⟩ :=
    ModularCurve.exists_gaussValuationSubring_laurentBaseChange_x1FunctionField M L K hK A j hj
  set Ej : IntermediateField L ↥K := IntermediateField.adjoin L ({j} : Set ↥K) with hEj
  haveI hFD : FiniteDimensional ↥Ej ↥K :=
    ModularCurve.finiteDimensional_adjoin_of_coe_eq_coeffEmb_jq_of_eq_laurentBaseChange
      (CongruenceSubgroup.Gamma1 M) (DegMAux_T_mem M) L K (by rw [hK]; rfl) j hj
  obtain ⟨OE, hDVR, hOEW, hOEpoly, hOEnu, hOEϖ⟩ :=
    ModularCurve.exists_valuationSubring_adjoin_isDiscreteValuationRing_mem_iff_of_laurentBaseChange_x1FunctionField
      M L K hK A j hj W hW
  haveI := hDVR
  have hOK : ∀ x : ↥OE, algebraMap ↥OE ↥K x = ((x : ↥Ej) : ↥K) := fun _ => rfl
  haveI : IsScalarTower ↥OE ↥Ej ↥K := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : Module.Finite ↥OE ↥(integralClosure ↥OE ↥K) := IsIntegralClosure.finite ↥OE ↥Ej ↥K _
  have hOW : ∀ x : ↥OE, algebraMap ↥OE ↥K x ∈ W := fun x => (hOEW x).mp x.2
  have hAKinj : Function.Injective (algebraMap A ↥K) := by
    rw [IsScalarTower.algebraMap_eq A L ↥K]
    exact (algebraMap L ↥K).injective.comp (IsFractionRing.injective A L)
  have htj : Transcendental A j := ModularCurve.transcendental_of_coe_eq_coeffEmb_jq L K A j hj
  obtain ⟨ϖ, hϖirr⟩ := IsDiscreteValuationRing.exists_irreducible A
  have hϖ : IsLocalRing.maximalIdeal A = Ideal.span {ϖ} :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖirr
  have hϖ𝔪 : ϖ ∈ IsLocalRing.maximalIdeal A := by rw [hϖ]; exact Ideal.mem_span_singleton_self ϖ

  obtain ⟨red, R₀, hred, hker, hconst, hR₀rng, hR₀⟩ :=
    S1cAux.exists_red_and_reductionField L K A W hW hWA hWnu

  have hAjW : ∀ (u : ↥K), u ∈ W → ∀ P : Polynomial A, Polynomial.aeval u P ∈ W := by
    intro u hu P
    let SW : Subalgebra A ↥K := { W.toSubring with algebraMap_mem' := hWA }
    have h1 : Algebra.adjoin A {u} ≤ SW := Algebra.adjoin_le (Set.singleton_subset_iff.mpr hu)
    exact h1 (Polynomial.aeval_mem_adjoin_singleton A u)
  let φA : A →+* ↥W := (algebraMap A ↥K).codRestrict W.toSubring hWA
  have hevalW : ∀ (u : ↥W) (P : Polynomial A),
      ((Polynomial.eval₂ φA u P : ↥W) : ↥K) = Polynomial.aeval (u : ↥K) P := by
    intro u P
    rw [show ((Polynomial.eval₂ φA u P : ↥W) : ↥K) = W.subtype (Polynomial.eval₂ φA u P) from rfl,
      Polynomial.hom_eval₂, Polynomial.aeval_def]
    congr 1
  have hredeval : ∀ (u : ↥W) (P : Polynomial A),
      red (Polynomial.eval₂ φA u P) = Polynomial.aeval (red u) (P.map (IsLocalRing.residue A)) := by
    intro u P
    rw [Polynomial.hom_eval₂, Polynomial.aeval_def, Polynomial.eval₂_map]
    congr 1
    exact RingHom.ext (fun a => hconst a)
  have hredaeval : ∀ (u : ↥K) (hu : u ∈ W) (P : Polynomial A),
      red ⟨Polynomial.aeval u P, hAjW u hu P⟩ =
        Polynomial.aeval (red ⟨u, hu⟩) (P.map (IsLocalRing.residue A)) := by
    intro u hu P
    rw [← hredeval ⟨u, hu⟩ P]
    congr 1
    apply Subtype.ext
    rw [hevalW]

  have hredquot : ∀ (u : ↥K) (hu : u ∈ W) (t : LaurentSeries (IsLocalRing.ResidueField A)), red ⟨u, hu⟩ = t →
      Transcendental (IsLocalRing.ResidueField A) t → ∀ (e : ↥K) (he : e ∈ W) (P Q : Polynomial A),
      Q.map (IsLocalRing.residue A) ≠ 0 → e * Polynomial.aeval u Q = Polynomial.aeval u P →
      red ⟨e, he⟩ = Polynomial.aeval t (P.map (IsLocalRing.residue A)) /
        Polynomial.aeval t (Q.map (IsLocalRing.residue A)) := by
    intro u hu t ht htr e he P Q hQ hePQ
    have hQt : Polynomial.aeval t (Q.map (IsLocalRing.residue A)) ≠ 0 := fun h0 =>
      hQ ((transcendental_iff.mp htr) _ h0)
    rw [eq_div_iff hQt, ← ht, ← hredaeval u hu Q, ← hredaeval u hu P, ← map_mul]
    congr 1
    exact Subtype.ext hePQ
  have hmem_adjoin_quot : ∀ (t : LaurentSeries (IsLocalRing.ResidueField A)) (P Q : Polynomial A),
      Polynomial.aeval t (P.map (IsLocalRing.residue A)) / Polynomial.aeval t (Q.map (IsLocalRing.residue A)) ∈
        IntermediateField.adjoin (IsLocalRing.ResidueField A) ({t} : Set (LaurentSeries (IsLocalRing.ResidueField A))) := by
    intro t P Q
    have hmem : ∀ R : Polynomial (IsLocalRing.ResidueField A), Polynomial.aeval t R ∈
        IntermediateField.adjoin (IsLocalRing.ResidueField A) ({t} : Set (LaurentSeries (IsLocalRing.ResidueField A))) := fun R =>
      (IntermediateField.algebra_adjoin_le_adjoin (IsLocalRing.ResidueField A) _) (Polynomial.aeval_mem_adjoin_singleton (IsLocalRing.ResidueField A) t)
    exact div_mem (hmem _) (hmem _)

  have hOEofPQ : ∀ P Q : Polynomial A, Q.map (IsLocalRing.residue A) ≠ 0 →
      ∃ x : ↥OE, ((x : ↥Ej) : ↥K) * Polynomial.aeval j Q = Polynomial.aeval j P := by
    intro P Q hQ
    have hQj : Polynomial.aeval j Q ≠ 0 := fun h0 => hQ (by rw [(transcendental_iff.mp htj) Q h0, Polynomial.map_zero])
    have hmemE : ∀ R : Polynomial A, Polynomial.aeval j R ∈ Ej := by
      intro R
      rw [hEj]
      have : Polynomial.aeval j R = Polynomial.aeval j (R.map (algebraMap A L)) := by
        rw [Polynomial.aeval_map_algebraMap]
      rw [this]
      exact (IntermediateField.algebra_adjoin_le_adjoin L _) (Polynomial.aeval_mem_adjoin_singleton L j)
    let e : ↥Ej := ⟨Polynomial.aeval j P * (Polynomial.aeval j Q)⁻¹, mul_mem (hmemE P) (inv_mem (hmemE Q))⟩
    have he : (e : ↥K) * Polynomial.aeval j Q = Polynomial.aeval j P := inv_mul_cancel_right₀ hQj _
    exact ⟨⟨e, (hOEpoly e).mpr ⟨P, Q, hQ, he⟩⟩, he⟩

  have hliftP : ∀ r : Polynomial (IsLocalRing.ResidueField A), ∃ R : Polynomial A, R.map (IsLocalRing.residue A) = r :=
    fun r => Polynomial.map_surjective _ IsLocalRing.residue_surjective r

  set jb : LaurentSeries (IsLocalRing.ResidueField A) := ModularCurve.jqModC (IsLocalRing.ResidueField A) with hjb
  set Kj : IntermediateField (IsLocalRing.ResidueField A) (LaurentSeries (IsLocalRing.ResidueField A)) :=
    IntermediateField.adjoin (IsLocalRing.ResidueField A) ({jb} : Set (LaurentSeries (IsLocalRing.ResidueField A))) with hKjdef

  have hjW : j ∈ W := by
    have h := (hWj Polynomial.X (by rw [Polynomial.map_X]; exact Polynomial.X_ne_zero)).1
    rwa [Polynomial.aeval_X] at h
  obtain ⟨⟨xj, yj, hyj, hxyj, hredj⟩, ⟨xjp, yjp, hyjp, hxyjp, hredjp⟩⟩ :=
    ModularCurve.exists_powerSeries_coeffEmb_jq_mul_eq_and_div_eq_jqModC_and_qExpand p L A hAp
  have hredj0 : red ⟨j, hjW⟩ = jb := by
    rw [hjb, ← hredj]
    exact hred ⟨j, hjW⟩ xj yj hyj (by rw [show (((⟨j, hjW⟩ : ↥W) : ↥K) : LaurentSeries L) = (j : LaurentSeries L) from rfl, hj]; exact hxyj)
  have hjbtr : Transcendental (IsLocalRing.ResidueField A) jb := by rw [hjb]; exact ModularCurve.transcendental_jqModC (IsLocalRing.ResidueField A)
  have hKj : ∀ z, z ∈ Kj ↔ ∃ x : ↥OE, red ⟨algebraMap ↥OE ↥K x, hOW x⟩ = z := by
    intro z
    constructor
    · intro hz
      rw [hKjdef] at hz
      obtain ⟨r, s₀, rfl⟩ := (IntermediateField.mem_adjoin_simple_iff (IsLocalRing.ResidueField A) z).mp hz
      obtain ⟨R, hR⟩ := hliftP r
      obtain ⟨S, hS⟩ := hliftP s₀
      by_cases hs : s₀ = 0
      · refine ⟨0, ?_⟩
        rw [hs, Polynomial.aeval_zero, div_zero]
        have : (⟨algebraMap ↥OE ↥K 0, hOW 0⟩ : ↥W) = 0 := Subtype.ext (map_zero _)
        rw [this, map_zero]
      · have hS0 : S.map (IsLocalRing.residue A) ≠ 0 := by rw [hS]; exact hs
        obtain ⟨x, hx⟩ := hOEofPQ R S hS0
        refine ⟨x, ?_⟩
        rw [← hR, ← hS]
        exact hredquot j hjW jb hredj0 hjbtr _ (hOW x) R S hS0 hx
    · rintro ⟨x, rfl⟩
      obtain ⟨P, Q, hQ, hxQ⟩ := (hOEpoly (x : ↥Ej)).mp x.2
      rw [hredquot j hjW jb hredj0 hjbtr _ (hOW x) P Q hQ hxQ, hKjdef]
      exact hmem_adjoin_quot jb P Q

  have hle : Kj ≤ R₀ := by
    intro z hz
    obtain ⟨x, rfl⟩ := (hKj z).mp hz
    exact (hR₀rng _).mpr ⟨_, rfl⟩

  haveI : NeZero (M * 1) := by rw [mul_one]; infer_instance
  have hle1 : ((Gamma1 (M * 1) : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) ≤
      ((Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) :=
    Subgroup.map_mono (Gamma1_le_of_dvd (dvd_mul_right M 1))
  have hK1 : K = laurentBaseChange L (x1FunctionField (M * 1)) := by rw [mul_one]; exact hK
  have hK₀R₀ : x1FunctionFieldC (IsLocalRing.ResidueField A) M ≤ R₀ := by
    rw [x1FunctionFieldC, qExpFunctionFieldC, IntermediateField.adjoin_le_iff]
    rintro _ ⟨k, f, g, pf, pg, hf, hg, hg0, rfl⟩
    obtain ⟨F, hy, hpres, hredF⟩ :=
      S1cAux.exists_ratio_presentation 1 M L K hK1 A (restrictForm hle1 f) (restrictForm hle1 g)
        pf pg hf hg hg0
    exact (hR₀ _).mpr ⟨F, _, _, hy, hpres, hredF⟩
  have hR₀K₀ : R₀ = x1FunctionFieldC (IsLocalRing.ResidueField A) M := by
    refine le_antisymm ?_ hK₀R₀
    intro z hz
    obtain ⟨f, x, y, hy, hf, rfl⟩ := (hR₀ z).mp hz
    exact ModularCurve.XOneP.gaussReduction_mem_x1FunctionFieldC_of_x1 p M hM hpM L ζ hζ K hK A hAp hζA
      j hj f x y hy hf

  have hWprop : ∀ x : ↥Ej, algebraMap ↥Ej ↥K x ∈ W ↔ x ∈ OE := fun x => (hOEW x).symm
  have hmemE : ∀ R : Polynomial A, Polynomial.aeval j R ∈ Ej := by
    intro R
    rw [hEj]
    have : Polynomial.aeval j R = Polynomial.aeval j (R.map (algebraMap A L)) := by
      rw [Polynomial.aeval_map_algebraMap]
    rw [this]
    exact (IntermediateField.algebra_adjoin_le_adjoin L _) (Polynomial.aeval_mem_adjoin_singleton L j)
  have hone : (1 : Polynomial A).map (IsLocalRing.residue A) ≠ 0 := by
    rw [Polynomial.map_one]; exact one_ne_zero
  have hPE : ∀ P : Polynomial A, (⟨Polynomial.aeval j P, hmemE P⟩ : ↥Ej) ∈ OE ∧
      ((⟨Polynomial.aeval j P, hmemE P⟩ : ↥Ej) ∈ OE.nonunits ↔ P.map (IsLocalRing.residue A) = 0) := by
    intro P
    have hpres : ((⟨Polynomial.aeval j P, hmemE P⟩ : ↥Ej) : ↥K) * Polynomial.aeval j (1 : Polynomial A) = Polynomial.aeval j P := by
      rw [map_one, mul_one]
    exact ⟨(hOEpoly _).mpr ⟨P, 1, hone, hpres⟩, hOEnu _ P 1 hone hpres⟩
  have huniq : ∀ B : ValuationSubring ↥K, (∀ x : ↥Ej, algebraMap ↥Ej ↥K x ∈ B ↔ x ∈ OE) → B = W := by
    intro B hB
    have hB' : ∀ x : ↥Ej, (x : ↥K) ∈ B ↔ x ∈ OE := hB
    have hBA : ∀ a : A, algebraMap A ↥K a ∈ B := by
      intro a
      have h : Polynomial.aeval j (Polynomial.C a) ∈ B :=
        (hB' ⟨Polynomial.aeval j (Polynomial.C a), hmemE _⟩).mpr (hPE (Polynomial.C a)).1
      rwa [Polynomial.aeval_C] at h
    have hBm : ∀ a ∈ IsLocalRing.maximalIdeal A, algebraMap A ↥K a ∈ B.nonunits := by
      intro a ha
      have hnu : (⟨Polynomial.aeval j (Polynomial.C a), hmemE _⟩ : ↥Ej) ∈ OE.nonunits := by
        rw [(hPE (Polynomial.C a)).2, Polynomial.map_C, (IsLocalRing.residue_eq_zero_iff a).mpr ha, map_zero]
      rcases (ValuationSubring.mem_nonunits_iff_or OE).mp hnu with h0 | hinv
      · rw [ValuationSubring.mem_nonunits_iff_or]; left
        have := congrArg (fun e : ↥Ej => (e : ↥K)) h0
        simpa [Polynomial.aeval_C] using this
      · rw [ValuationSubring.mem_nonunits_iff_or]; right
        intro hmem
        apply hinv
        apply (hB' _).mp
        rw [IntermediateField.coe_inv]
        show (Polynomial.aeval j (Polynomial.C a))⁻¹ ∈ B
        rwa [Polynomial.aeval_C]
    have hBj : ∀ P : Polynomial A, P.map (IsLocalRing.residue A) ≠ 0 →
        Polynomial.aeval j P ∈ B ∧ (Polynomial.aeval j P)⁻¹ ∈ B := by
      intro P hP
      refine ⟨(hB' ⟨Polynomial.aeval j P, hmemE P⟩).mpr (hPE P).1, ?_⟩
      have hinv : (⟨Polynomial.aeval j P, hmemE P⟩ : ↥Ej)⁻¹ ∈ OE := by
        by_contra h
        exact hP ((hPE P).2.mp ((ValuationSubring.mem_nonunits_iff_or OE).mpr (Or.inr h)))
      have := (hB' _).mpr hinv
      rwa [IntermediateField.coe_inv] at this
    have hchar := ModularCurve.XOneP.mem_valuationSubring_iff_exists_powerSeries_of_x1 p M hM hpM L ζ hζ K hK A hAp hζA
      j hj B hBA hBm hBj
    ext f
    rw [hchar f, hW f]

  obtain ⟨-, -, hsum⟩ :=
    ValuationSubring.finsum_ramificationIdx_mul_inertiaDeg_eq_finrank (K := ↥Ej) (F := ↥K) OE
  rw [finsum_eq_single _ (⟨W, hWprop⟩ : {B : ValuationSubring ↥K // ∀ x : ↥Ej, algebraMap ↥Ej ↥K x ∈ B ↔ x ∈ OE})
    (fun B hB => absurd (Subtype.ext (huniq B.1 B.2)) hB)] at hsum
  let algOW : ↥OE →+* ↥W :=
    ((algebraMap ↥Ej ↥K).comp OE.subtype).codRestrict W (fun a => (hWprop a).mpr a.2)
  letI instOW : Algebra ↥OE ↥W := algOW.toAlgebra
  have hsum' : (IsLocalRing.maximalIdeal ↥OE).ramificationIdx' (IsLocalRing.maximalIdeal ↥W) *
      (IsLocalRing.maximalIdeal ↥OE).inertiaDeg' (IsLocalRing.maximalIdeal ↥W) = Module.finrank ↥Ej ↥K := hsum
  have halgOW : ∀ x : ↥OE, ((algebraMap ↥OE ↥W x : ↥W) : ↥K) = ((x : ↥Ej) : ↥K) := fun _ => rfl

  have hnuEW : ∀ x : ↥Ej, x ∈ OE.nonunits ↔ (x : ↥K) ∈ W.nonunits := by
    intro x
    rw [ValuationSubring.mem_nonunits_iff_or, ValuationSubring.mem_nonunits_iff_or, ← IntermediateField.coe_inv,
      ← hOEW]
    simp only [ZeroMemClass.coe_eq_zero]
  have hmaxOW : ∀ x : ↥OE, x ∈ IsLocalRing.maximalIdeal ↥OE ↔ algebraMap ↥OE ↥W x ∈ IsLocalRing.maximalIdeal ↥W := by
    intro x
    rw [← ValuationSubring.coe_mem_nonunits_iff, ← ValuationSubring.coe_mem_nonunits_iff, halgOW, hnuEW]
  haveI hover : (IsLocalRing.maximalIdeal ↥W).LiesOver (IsLocalRing.maximalIdeal ↥OE) :=
    ⟨Ideal.ext (fun x => by rw [Ideal.mem_comap]; exact hmaxOW x)⟩

  let ϖW : ↥W := ⟨algebraMap A ↥K ϖ, hWA ϖ⟩
  have hϖWnu : (ϖW : ↥K) ∈ W.nonunits := hWm ϖ hϖ𝔪
  have hϖW0 : (ϖW : ↥K) ≠ 0 := (map_ne_zero_iff _ hAKinj).mpr hϖirr.ne_zero
  have h𝔪W : IsLocalRing.maximalIdeal ↥W ≤ Ideal.span {ϖW} := by
    intro w hw
    have hwnu : (w : ↥K) ∈ W.nonunits := ValuationSubring.coe_mem_nonunits_iff.mpr hw
    obtain ⟨x, y, hy, hwxy⟩ := (hW w).mp w.2
    have hx0 : x.map (IsLocalRing.residue A) = 0 := (hWnu w x y hy hwxy).mp hwnu

    have hcoef : ∀ n, ∃ c, PowerSeries.coeff n x = ϖ * c := by
      intro n
      have h := congrArg (PowerSeries.coeff n) hx0
      rw [PowerSeries.coeff_map, map_zero, IsLocalRing.residue_eq_zero_iff, hϖ] at h
      obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp h
      exact ⟨c, by rw [← hc, mul_comm]⟩
    choose c hc using hcoef
    set x' : PowerSeries A := PowerSeries.mk c with hx'
    have hxx' : x = PowerSeries.C ϖ * x' := by
      ext n; rw [PowerSeries.coeff_C_mul, hx', PowerSeries.coeff_mk, hc]

    let g : ↥K := (w : ↥K) * (algebraMap A ↥K ϖ)⁻¹
    have hgpres : (g : LaurentSeries L) * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap A L))
        = HahnSeries.ofPowerSeries ℤ L (x'.map (algebraMap A L)) := by
      have hϖL : (algebraMap A L ϖ) ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective A L)).mpr hϖirr.ne_zero
      have hcoeϖ : ((algebraMap A ↥K ϖ : ↥K) : LaurentSeries L) = HahnSeries.C (algebraMap A L ϖ) := by
        rw [IsScalarTower.algebraMap_apply A L ↥K]
        show algebraMap L (LaurentSeries L) (algebraMap A L ϖ) = _
        rw [algebraMap_laurentSeries_eq_single, HahnSeries.C_apply]
      have hx1 : HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap A L)) =
          HahnSeries.C (algebraMap A L ϖ) * HahnSeries.ofPowerSeries ℤ L (x'.map (algebraMap A L)) := by
        rw [hxx', map_mul, PowerSeries.map_C, map_mul, HahnSeries.ofPowerSeries_C]
      show (((w : ↥K) * (algebraMap A ↥K ϖ)⁻¹ : ↥K) : LaurentSeries L) * _ = _
      rw [MulMemClass.coe_mul, IntermediateField.coe_inv, hcoeϖ, mul_right_comm, hwxy, hx1,
        mul_comm (HahnSeries.C _) _, mul_assoc, mul_inv_cancel₀ (HahnSeries.C_ne_zero hϖL), mul_one]
    have hgW : g ∈ W := (hW g).mpr ⟨x', y, hy, hgpres⟩
    refine Ideal.mem_span_singleton'.mpr ⟨⟨g, hgW⟩, Subtype.ext ?_⟩
    show (g : ↥K) * algebraMap A ↥K ϖ = (w : ↥K)
    exact inv_mul_cancel_right₀ hϖW0 _
  obtain ⟨ϖO, hϖOK, hϖOirr⟩ := hOEϖ ϖ hϖirr
  have hϖOW : algebraMap ↥OE ↥W ϖO = ϖW := Subtype.ext (by rw [halgOW, hϖOK])
  have he1 : (IsLocalRing.maximalIdeal ↥OE).ramificationIdx' (IsLocalRing.maximalIdeal ↥W) = 1 := by
    apply Ideal.ramificationIdx_spec
    · rw [pow_one, Ideal.map_le_iff_le_comap]
      intro x hx; rw [Ideal.mem_comap]; exact (hmaxOW x).mp hx
    · intro hle2
      have hϖO𝔪 : ϖO ∈ IsLocalRing.maximalIdeal ↥OE := (IsLocalRing.mem_maximalIdeal _).mpr hϖOirr.not_isUnit
      have h1 : ϖW ∈ IsLocalRing.maximalIdeal ↥W ^ (1 + 1) := by
        rw [← hϖOW]; exact hle2 (Ideal.mem_map_of_mem _ hϖO𝔪)
      have h2 : IsLocalRing.maximalIdeal ↥W ^ (1 + 1) ≤ Ideal.span {ϖW ^ 2} := by
        rw [show (1 + 1 : ℕ) = 2 from rfl, ← Ideal.span_singleton_pow]; exact Ideal.pow_right_mono h𝔪W 2
      obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp (h2 h1)
      have hunit : IsUnit ϖW := by
        refine isUnit_iff_exists_inv.mpr ⟨c, ?_⟩
        have h3 : c * ϖW * ϖW = 1 * ϖW := by
          rw [one_mul, mul_assoc, ← pow_two]; exact hc
        rw [mul_comm]
        exact mul_right_cancel₀ (fun h => hϖW0 (congrArg Subtype.val h)) h3
      exact ((ValuationSubring.coe_mem_nonunits_iff).mp hϖWnu |> (IsLocalRing.mem_maximalIdeal _).mp) hunit

  let redO : ↥OE →+* LaurentSeries (IsLocalRing.ResidueField A) := red.comp (algebraMap ↥OE ↥W)
  have hredO : ∀ x : ↥OE, redO x = red ⟨algebraMap ↥OE ↥K x, hOW x⟩ := fun _ => rfl
  have hredO_zero : ∀ x : ↥OE, redO x = 0 ↔ x ∈ IsLocalRing.maximalIdeal ↥OE := by
    intro x
    rw [hmaxOW, ← hker, RingHom.mem_ker]
    rfl
  have hredO_mem : ∀ x : ↥OE, redO x ∈ Kj := fun x => (hKj _).mpr ⟨x, (hredO x).symm⟩
  haveI : (IsLocalRing.maximalIdeal ↥W).IsMaximal := IsLocalRing.maximalIdeal.isMaximal ↥W
  letI : Field (↥W ⧸ IsLocalRing.maximalIdeal ↥W) := Ideal.Quotient.field _
  let ψO : ↥OE →+* ↥Kj := redO.codRestrict Kj hredO_mem
  let iO : ↥OE ⧸ IsLocalRing.maximalIdeal ↥OE →+* ↥Kj :=
    Ideal.Quotient.lift _ ψO (fun x hx => Subtype.ext ((hredO_zero x).mpr hx))
  have hiO_mk : ∀ x : ↥OE, ((iO (Ideal.Quotient.mk _ x) : ↥Kj) : LaurentSeries (IsLocalRing.ResidueField A)) = redO x :=
    fun _ => rfl
  have hiO_bij : Function.Bijective iO := by
    constructor
    · rw [RingHom.injective_iff_ker_eq_bot, eq_bot_iff]
      intro x hx
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
      rw [RingHom.mem_ker] at hx
      have : redO x = 0 := by rw [← hiO_mk, hx]; rfl
      rw [Ideal.mem_bot, Ideal.Quotient.eq_zero_iff_mem]
      exact (hredO_zero x).mp this
    · intro z
      obtain ⟨x, hx⟩ := (hKj (z : LaurentSeries (IsLocalRing.ResidueField A))).mp z.2
      exact ⟨Ideal.Quotient.mk _ x, Subtype.ext (by rw [hiO_mk, hredO]; exact hx)⟩
  let i : ↥OE ⧸ IsLocalRing.maximalIdeal ↥OE ≃+* ↥Kj := RingEquiv.ofBijective iO hiO_bij
  have hred_mem : ∀ w : ↥W, red w ∈ IntermediateField.extendScalars hle := fun w =>
    (IntermediateField.mem_extendScalars _).mpr ((hR₀rng _).mpr ⟨w, rfl⟩)
  let ψW : ↥W →+* ↥(IntermediateField.extendScalars hle) :=
    red.codRestrict (IntermediateField.extendScalars hle) hred_mem
  let jW : ↥W ⧸ IsLocalRing.maximalIdeal ↥W →+* ↥(IntermediateField.extendScalars hle) :=
    Ideal.Quotient.lift _ ψW (fun w hw => Subtype.ext (by
      show red w = 0
      rw [← RingHom.mem_ker, hker]; exact hw))
  have hjW_mk : ∀ w : ↥W, ((jW (Ideal.Quotient.mk _ w) : ↥(IntermediateField.extendScalars hle)) :
      LaurentSeries (IsLocalRing.ResidueField A)) = red w := fun _ => rfl
  have hjW_bij : Function.Bijective jW := by
    constructor
    · rw [RingHom.injective_iff_ker_eq_bot, eq_bot_iff]
      intro w hw
      obtain ⟨w, rfl⟩ := Ideal.Quotient.mk_surjective w
      rw [RingHom.mem_ker] at hw
      have : red w = 0 := by rw [← hjW_mk, hw]; rfl
      rw [Ideal.mem_bot, Ideal.Quotient.eq_zero_iff_mem, ← hker, RingHom.mem_ker]
      exact this
    · intro z
      have hz : (z : LaurentSeries (IsLocalRing.ResidueField A)) ∈ R₀ := (IntermediateField.mem_extendScalars _).mp z.2
      obtain ⟨w, hw⟩ := (hR₀rng _).mp hz
      exact ⟨Ideal.Quotient.mk _ w, Subtype.ext (by rw [hjW_mk]; exact hw)⟩
  let jj : ↥W ⧸ IsLocalRing.maximalIdeal ↥W ≃+* ↥(IntermediateField.extendScalars hle) :=
    RingEquiv.ofBijective jW hjW_bij
  have hc : (algebraMap ↥Kj ↥(IntermediateField.extendScalars hle)).comp i.toRingHom =
      jj.toRingHom.comp (algebraMap (↥OE ⧸ IsLocalRing.maximalIdeal ↥OE) (↥W ⧸ IsLocalRing.maximalIdeal ↥W)) := by
    apply RingHom.ext
    intro x
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    apply Subtype.ext
    show ((iO (Ideal.Quotient.mk _ x) : ↥Kj) : LaurentSeries (IsLocalRing.ResidueField A)) =
      ((jW (algebraMap (↥OE ⧸ IsLocalRing.maximalIdeal ↥OE) (↥W ⧸ IsLocalRing.maximalIdeal ↥W)
        (Ideal.Quotient.mk _ x)) : ↥(IntermediateField.extendScalars hle)) : LaurentSeries (IsLocalRing.ResidueField A))
    rw [hiO_mk]
    show redO x = ((jW (Ideal.Quotient.mk _ (algebraMap ↥OE ↥W x)) :
      ↥(IntermediateField.extendScalars hle)) : LaurentSeries (IsLocalRing.ResidueField A))
    rw [hjW_mk]
    rfl
  have hf : (IsLocalRing.maximalIdeal ↥OE).inertiaDeg' (IsLocalRing.maximalIdeal ↥W) =
      Module.finrank ↥Kj ↥(IntermediateField.extendScalars hle) := by
    rw [Ideal.inertiaDeg_algebraMap]
    exact Algebra.finrank_eq_of_equiv_equiv i jj hc

  rw [he1, one_mul, hf, ← IntermediateField.relfinrank_eq_finrank_of_le hle] at hsum'
  rw [← hsum', hKjdef, hjb, hR₀K₀]

end S_ModularCurve_XOneP_finrank_adjoin_j_eq_relfinrank_adjoin_jqModC_x1FunctionFieldC_of_x1
end P2MW
export P2MW.S_ModularCurve_XOneP_finrank_adjoin_j_eq_relfinrank_adjoin_jqModC_x1FunctionFieldC_of_x1 (solution)
