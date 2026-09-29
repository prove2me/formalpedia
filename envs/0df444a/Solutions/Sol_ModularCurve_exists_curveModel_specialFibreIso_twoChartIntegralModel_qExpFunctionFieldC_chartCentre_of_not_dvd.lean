-- Prove2me | solution 1 for ModularCurve.exists_curveModel_specialFibreIso_twoChartIntegralModel_qExpFunctionFieldC_chartCentre_of_not_dvd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/d655e658-68a4-55b9-87ea-46726986c7a1

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_LaurentCoeff
import Definitions.Def_GaloisRep_Flat
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_CurveModelConstruction
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_JacJ1_ChartAlgebra
import Definitions.Def_ModularCurve_ArithmeticGalois
import Theorems.Thm_ModularCurve_exists_algEquiv_residueField_tensor_chartAlg_twoChartIntegralModel_qExpFunctionFieldC_chartRing
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_exists_iso_glued_pullback_toBase_of_algEquiv_chartAlg_chartRing
import Theorems.Thm_ModularCurve_exists_coeffMap_eq_coe_of_mem_chartAlg_twoChartIntegralModel_qExpFunctionFieldC
import Theorems.Thm_AlgebraicCurve_CurveModel_isProper_smooth_places_affineCover_glued
import Theorems.Thm_AlgebraicCurve_CurveModel_coe_mem_and_sub_algebraMap_mem_nonunits_of_range_stalk_eq_iota0
import Theorems.Thm_AlgebraicCurve_CurveModel_coe_mem_and_sub_algebraMap_mem_nonunits_of_range_stalk_eq_iotaInf
import Theorems.Thm_ModularCurve_exists_transcendental_finiteDimensional_qExpFunctionFieldC_residueField
import Theorems.Thm_ModularCurve_isSeparable_adjoin_jqModC_of_isAlgebraic
import Theorems.Thm_ValuationSubring_charP_residueField_of_liesOverPrime
import Theorems.Thm_ValuationSubring_exists_ratLocalizedAt_ringHom_of_liesOverPrime
import Theorems.Thm_ValuationSubring_isAlgClosed_residueField_algebraicClosure_rat
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_curveModel_specialFibreIso_twoChartIntegralModel_qExpFunctionFieldC_chartCentre_of_not_dvd
p2m_attr_erase "instance" "CohCarrier.iotaDeg_range_finiteIndex CohCarrier.Gamma0Upper_finiteIndex TateModule.instModule TateModule.instSMul CohCarrier.HeckeData.V_isScalarTower CohCarrier.HeckeData.opSubalgebra_isMulCommutative CohCarrier.HeckeData.mTheta_isPrime ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom"
p2m_attr_erase "instance" "AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.instIsElliptic_tateBase ModularCurve.instIsElliptic_tateLaurent ModularCurve.KatzGamma0Form.instModule ModularCurve.KatzGamma0Form.instZero ModularCurve.KatzLevelPForm.instSMul ModularCurve.KatzGamma0Form.instAdd ModularCurve.KatzLevelPForm.instAddCommGroup ModularCurve.KatzGamma0Form.instNeg ModularCurve.KatzGamma0Form.instAddCommGroup ModularCurve.KatzLevelPForm.instAdd ModularCurve.KatzLevelPForm.instSub ModularCurve.KatzLevelPForm.instNeg ModularCurve.KatzGamma0Form.instSMul ModularCurve.KatzGamma0Form.instSub ModularCurve.KatzLevelPForm.instZero ModularCurve.KatzLevelPForm.instModule KatzModularForm.instAddCommGroup KatzModularForm.instSub KatzModularForm.instZero KatzModularForm.instModule KatzModularForm.instAdd KatzModularForm.instNeg KatzModularForm.instSMul WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular"
p2m_attr_erase "simp" "CohCarrier.conjUpperMat_apply_11 CohCarrier.conjUpperMat_apply_10 CohCarrier.mem_Gamma0Upper CohCarrier.val_gamma0Units AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap ModularCurve.JH.torsionGaloisRep_apply TateModule.smul_apply TateModule.coe_mulP TateModule.proj_apply TateModule.coe_add TateModule.coe_sub WeierstrassCurve.tateModuleRepOfBasis_V TateModule.coe_zero TateModule.rep_apply WeierstrassCurve.tateModuleRep_V WeierstrassCurve.tateModuleRepOfBasis_ρ_apply GaloisRep.padicIntToRingLevel_apply TateModule.coe_neg WeierstrassCurve.tateModuleRep_ρ_apply ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL CohCarrier.Gen.dia.sizeOf_spec CohCarrier.Gen.U.injEq CohCarrier.Gen.T.sizeOf_spec CohCarrier.Gen.U.sizeOf_spec CohCarrier.Gen.T.injEq"
p2m_attr_erase "simp" "CohCarrier.Gen.dia.injEq CohCarrier.HeckeData.mk.sizeOf_spec CohCarrier.HeckeData.opAlgHom_X CohCarrier.HeckeData.toMLₒ_apply CohCarrier.HeckeData.mk.injEq CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply ModularCurve.ProjectiveLine.map_mk ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_cuspidalDivisor₀ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk"
p2m_attr_erase "simp" "ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one"
p2m_attr_erase "simp" "AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule ModularCurve.LevelN.coe_jGen HahnSeries.ramScale_apply WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.cuspData_yP ModularCurve.qTwistAlgHom_apply ModularCurve.cuspData_yQ"
p2m_attr_erase "simp" "ModularCurve.cuspData_xP ModularCurve.cuspData_xQ ModularCurve.val_cyclZeta ModularCurve.cuspShift_one ModularCurve.cuspShift_zero ModularCurve.LevelPData.mk.sizeOf_spec ModularCurve.KatzLevelPForm.neg_toFun ModularCurve.LevelP.coe_swapW ModularCurve.KatzLevelPForm.swap_swap KatzModularForm.pullbackLevelP_toFun ModularCurve.LevelPData.swap_xQ KatzModularForm.pullbackLevelP_zero ModularCurve.LevelPData.map_yP ModularCurve.KatzLevelPForm.swap_neg ModularCurve.KatzGamma0Form.toKatzLevelPForm_sub ModularCurve.KatzLevelPForm.swap_add KatzModularForm.swap_pullbackLevelP ModularCurve.KatzGamma0Form.toKatzLevelPForm_add ModularCurve.KatzLevelPForm.swap_smul ModularCurve.LevelPData.map_yQ ModularCurve.KatzLevelPForm.mk.injEq ModularCurve.KatzLevelPForm.zero_toFun KatzModularForm.pullbackLevelP_smul ModularCurve.LevelPData.swap_xP ModularCurve.KatzGamma0Form.toKatzLevelPForm_mul ModularCurve.KatzGamma0Form.toKatzLevelPForm_neg ModularCurve.LevelPData.variableChange_xQ KatzModularForm.pullbackGamma0_toKatzLevelPForm ModularCurve.KatzLevelPForm.mk.sizeOf_spec ModularCurve.KatzLevelPForm.swap_zero ModularCurve.LevelP.coe_unipotentU ModularCurve.KatzLevelPForm.mul_toFun ModularCurve.LevelPData.variableChange_yP ModularCurve.LevelPData.mk.injEq ModularCurve.KatzLevelPForm.sub_toFun ModularCurve.LevelPData.variableChange_xP ModularCurve.KatzLevelPForm.smul_toFun ModularCurve.LevelPData.swap_yP ModularCurve.LevelPData.map_xP ModularCurve.LevelPData.swap_swap"
p2m_attr_erase "simp" "ModularCurve.LevelPData.swap_yQ ModularCurve.KatzGamma0Form.toKatzLevelPForm_zero ModularCurve.KatzGamma0Form.mk.injEq ModularCurve.KatzLevelPForm.swap_toFun KatzModularForm.pullbackLevelP_add ModularCurve.KatzGamma0Form.mk.sizeOf_spec ModularCurve.LevelPData.variableChange_yQ ModularCurve.KatzLevelPForm.swap_sub ModularCurve.KatzGamma0Form.toKatzLevelPForm_smul ModularCurve.LevelPData.map_xQ ModularCurve.KatzLevelPForm.add_toFun KatzModularForm.c₆_toFun KatzModularForm.neg_toFun KatzModularForm.mul_toFun KatzModularForm.qExpansion_neg KatzModularForm.discr_toFun KatzModularForm.qExpansion_sub KatzModularForm.qExpansion_add KatzModularForm.qExpansion_mul KatzModularForm.zero_toFun KatzModularForm.mk.injEq KatzModularForm.qExpansion_smul KatzModularForm.smul_toFun KatzModularForm.add_toFun KatzModularForm.sub_toFun KatzModularForm.c₄_toFun KatzModularForm.qExpansion_zero KatzModularForm.mk.sizeOf_spec TateCurve.tateTorsionPoint_zero_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero"
p2m_attr_erase "simp" "TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two"
p2m_attr_erase "simp" "compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty"
p2m_attr_erase "simp" "WeierstrassCurve.veluX_empty WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq"
p2m_attr_erase "simp" "AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff"

open scoped MatrixGroups TensorProduct
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve ModularCurve IsLocalRing

noncomputable section
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 6400000

namespace SPMH

theorem T_mem_Gamma1 (M : ℕ) : ModularGroup.T ∈ CongruenceSubgroup.Gamma1 M := by
  rw [CongruenceSubgroup.Gamma1_mem]
  refine ⟨?_, ?_, ?_⟩ <;> simp [ModularGroup.T]

theorem finiteIndex_of_gamma1_le (M : ℕ) [NeZero M] (Γ : Subgroup SL(2, ℤ)) (h : CongruenceSubgroup.Gamma1 M ≤ Γ) :
    Γ.FiniteIndex := by
  haveI : (CongruenceSubgroup.Gamma1 M).FiniteIndex := CongruenceSubgroup.instFiniteIndexGamma1 M
  exact Subgroup.finiteIndex_of_le h

theorem coeffMap_coeffMap {R S T : Type*} [CommRing R] [CommRing S] [CommRing T] (f : R →+* S) (g : S →+* T)
    (y : LaurentSeries R) : coeffMap g (coeffMap f y) = coeffMap (g.comp f) y := by
  ext n; rfl

theorem coeffEmb_coeffMap_algebraMap (L : Type*) [Field L] [Algebra ℚ L] (R : Type*) [CommRing R] [Algebra R ℚ]
    [Algebra R L] [IsScalarTower R ℚ L] (y : LaurentSeries R) :
    coeffMap (algebraMap R L) y = coeffEmb L (coeffMap (algebraMap R ℚ) y) := by
  ext n
  show algebraMap R L (y.coeff n) = algebraMap ℚ L (algebraMap R ℚ (y.coeff n))
  rw [← IsScalarTower.algebraMap_apply]

theorem coeffMap_jqModC {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) : coeffMap f (jqModC R) = jqModC S :=
  map_jqModC f

theorem coeffEmb_jqModC (L : Type*) [Field L] [Algebra ℚ L] : coeffEmb L (jqModC ℚ) = jqModC L :=
  map_jqModC (algebraMap ℚ L)

universe uK uL
namespace IgusaSide

variable {R : Type} [CommRing R] {F : Type} [Field F] [Algebra R F] {j : F} [Fact (j ≠ 0)]

theorem ιFin_eq_ιInf_iff (x₀ : TwoChartIntegralModel.XFin R F j) (xi : TwoChartIntegralModel.XInf R F j) :
    (TwoChartIntegralModel.ιFin R F j).base x₀ = (TwoChartIntegralModel.ιInf R F j).base xi ↔
      ∃ w : TwoChartIntegralModel.XMid R F j,
        (TwoChartIntegralModel.fFin R F j).base w = x₀ ∧ (TwoChartIntegralModel.fInf R F j).base w = xi := by
  constructor
  · intro h
    obtain ⟨k, fi, fj, w, h₁, h₂⟩ :=
      (Scheme.IsLocallyDirected.ι_eq_ι_iff
        (F := span (TwoChartIntegralModel.fFin R F j) (TwoChartIntegralModel.fInf R F j))
        (i := WalkingSpan.left) (j := WalkingSpan.right) (xi := x₀) (xj := xi)).mp h
    rcases k with (_ | _ | _)
    · exact match fi, fj, h₁, h₂ with
        | .init _, .init _, h₁, h₂ => ⟨w, h₁, h₂⟩
    · exact nomatch fj
    · exact nomatch fi
  · rintro ⟨w, rfl, rfl⟩
    change (TwoChartIntegralModel.fFin R F j ≫ TwoChartIntegralModel.ιFin R F j).base w =
      (TwoChartIntegralModel.fInf R F j ≫ TwoChartIntegralModel.ιInf R F j).base w
    rw [TwoChartIntegralModel.glue_condition]

set_option synthInstance.maxHeartbeats 1600000 in
theorem range_fInf : Set.range (TwoChartIntegralModel.fInf R F j).base =
    ((PrimeSpectrum.basicOpen (TwoChartIntegralModel.jInvChartInf R F j) :
        TopologicalSpace.Opens (PrimeSpectrum ↥(TwoChartIntegralModel.chartAlgInf R F j))) : Set (PrimeSpectrum ↥(TwoChartIntegralModel.chartAlgInf R F j))) := by
  letI := (TwoChartIntegralModel.inclInf R F j).toRingHom.toAlgebra
  haveI := TwoChartIntegralModel.isLocalization_away_inclInf R F j
  exact PrimeSpectrum.localization_away_comap_range ↥(TwoChartIntegralModel.chartAlgMid R F j) (TwoChartIntegralModel.jInvChartInf R F j)

theorem ιInf_mem_range_ιFin_iff (xi : TwoChartIntegralModel.XInf R F j) :
    (TwoChartIntegralModel.ιInf R F j).base xi ∈ Set.range (TwoChartIntegralModel.ιFin R F j).base ↔
      TwoChartIntegralModel.jInvChartInf R F j ∉ xi.asIdeal := by
  rw [← PrimeSpectrum.mem_basicOpen, ← SetLike.mem_coe, ← range_fInf, Set.mem_range]
  constructor
  · rintro ⟨x₀, h⟩
    obtain ⟨w, -, hw⟩ := (ιFin_eq_ιInf_iff x₀ xi).mp h
    exact ⟨w, hw⟩
  · rintro ⟨w, rfl⟩
    exact ⟨(TwoChartIntegralModel.fFin R F j).base w, (ιFin_eq_ιInf_iff _ _).mpr ⟨w, rfl, rfl⟩⟩

theorem exists_eq_comp_of_closedPoint_mem {X U : Scheme.{0}} {R : Type} [CommRing R] [IsLocalRing R]
    (ι : U ⟶ X) [IsOpenImmersion ι] (f : Spec (CommRingCat.of R) ⟶ X)
    (h : f.base (IsLocalRing.closedPoint R) ∈ Set.range ι.base) :
    ∃ g : Spec (CommRingCat.of R) ⟶ U, g ≫ ι = f := by
  have hrange : Set.range f.base ⊆ Set.range ι.base := by
    rintro _ ⟨q, rfl⟩
    have hs : f.base q ⤳ f.base (IsLocalRing.closedPoint R) :=
      (IsLocalRing.specializes_closedPoint q).map f.base.hom.continuous
    exact hs.mem_open ι.isOpenEmbedding.isOpen_range h
  exact ⟨IsOpenImmersion.lift ι f hrange, IsOpenImmersion.lift_fac ι f hrange⟩

theorem exists_eq_SpecMap_comp_of_closedPoint_mem {X : Scheme.{0}} {R B : Type} [CommRing R] [IsLocalRing R]
    [CommRing B] (ι : Spec (CommRingCat.of B) ⟶ X) [IsOpenImmersion ι] (f : Spec (CommRingCat.of R) ⟶ X)
    (h : f.base (IsLocalRing.closedPoint R) ∈ Set.range ι.base) :
    ∃ χ : B →+* R, Spec.map (CommRingCat.ofHom χ) ≫ ι = f := by
  obtain ⟨g, hg⟩ := exists_eq_comp_of_closedPoint_mem ι f h
  exact ⟨(Spec.preimage g).hom, by rw [CommRingCat.ofHom_hom, Spec.map_preimage, hg]⟩

theorem ringHom_eq_of_SpecMap_comp_eq {A B : Type} [CommRing A] [CommRing B] {X : Scheme.{0}}
    (ι : Spec (CommRingCat.of A) ⟶ X) [Mono ι] (ψ ψ' : A →+* B)
    (h : Spec.map (CommRingCat.ofHom ψ') ≫ ι = Spec.map (CommRingCat.ofHom ψ) ≫ ι) : ψ' = ψ := by
  have h1 : Spec.map (CommRingCat.ofHom ψ') = Spec.map (CommRingCat.ofHom ψ) := (cancel_mono ι).mp h
  exact congrArg CommRingCat.Hom.hom (Spec.map_injective h1)

theorem comp_algebraMap_eq_of_ιFin {R' : Type} [CommRing R'] (ρ : R →+* R')
    (χ : ↥(TwoChartIntegralModel.chartAlgFin R F j) →+* R')
    (h : (Spec.map (CommRingCat.ofHom χ) ≫ TwoChartIntegralModel.ιFin R F j) ≫ TwoChartIntegralModel.toBase R F j =
      Spec.map (CommRingCat.ofHom ρ)) :
    χ.comp (algebraMap R ↥(TwoChartIntegralModel.chartAlgFin R F j)) = ρ := by
  rw [Category.assoc, TwoChartIntegralModel.ιFin_toBase, ← Spec.map_comp, ← CommRingCat.ofHom_comp] at h
  exact congrArg CommRingCat.Hom.hom (Spec.map_injective h)

theorem comp_algebraMap_eq_of_ιInf {R' : Type} [CommRing R'] (ρ : R →+* R')
    (χ : ↥(TwoChartIntegralModel.chartAlgInf R F j) →+* R')
    (h : (Spec.map (CommRingCat.ofHom χ) ≫ TwoChartIntegralModel.ιInf R F j) ≫ TwoChartIntegralModel.toBase R F j =
      Spec.map (CommRingCat.ofHom ρ)) :
    χ.comp (algebraMap R ↥(TwoChartIntegralModel.chartAlgInf R F j)) = ρ := by
  rw [Category.assoc, TwoChartIntegralModel.ιInf_toBase, ← Spec.map_comp, ← CommRingCat.ofHom_comp] at h
  exact congrArg CommRingCat.Hom.hom (Spec.map_injective h)

theorem exists_mid_of_SpecMap_ιFin_eq_SpecMap_ιInf {F' : Type} [Field F']
    (α : ↥(TwoChartIntegralModel.chartAlgFin R F j) →+* F') (β : ↥(TwoChartIntegralModel.chartAlgInf R F j) →+* F')
    (h : Spec.map (CommRingCat.ofHom α) ≫ TwoChartIntegralModel.ιFin R F j =
      Spec.map (CommRingCat.ofHom β) ≫ TwoChartIntegralModel.ιInf R F j) :
    ∃ w : ↥(TwoChartIntegralModel.chartAlgMid R F j) →+* F',
      w.comp (TwoChartIntegralModel.inclFin R F j).toRingHom = α ∧
      w.comp (TwoChartIntegralModel.inclInf R F j).toRingHom = β := by

  have hpt : (TwoChartIntegralModel.ιFin R F j).base ((Spec.map (CommRingCat.ofHom α)).base (IsLocalRing.closedPoint F')) =
      (TwoChartIntegralModel.ιInf R F j).base ((Spec.map (CommRingCat.ofHom β)).base (IsLocalRing.closedPoint F')) := by
    have := congrArg (fun f : Spec (CommRingCat.of F') ⟶ AlgebraicCurve.TwoChartIntegralModel R F j =>
      f.base (IsLocalRing.closedPoint F')) h
    exact this
  obtain ⟨w0, hw0, -⟩ := (ιFin_eq_ιInf_iff _ _).mp hpt
  haveI : IsOpenImmersion (TwoChartIntegralModel.fFin R F j ≫ TwoChartIntegralModel.ιFin R F j) := inferInstance
  have hmem : (Spec.map (CommRingCat.ofHom α) ≫ TwoChartIntegralModel.ιFin R F j).base (IsLocalRing.closedPoint F') ∈
      Set.range (TwoChartIntegralModel.fFin R F j ≫ TwoChartIntegralModel.ιFin R F j).base :=
    ⟨w0, by
      show (TwoChartIntegralModel.ιFin R F j).base ((TwoChartIntegralModel.fFin R F j).base w0) =
        (TwoChartIntegralModel.ιFin R F j).base ((Spec.map (CommRingCat.ofHom α)).base (IsLocalRing.closedPoint F'))
      rw [hw0]⟩
  obtain ⟨w, hw⟩ := exists_eq_SpecMap_comp_of_closedPoint_mem
    (TwoChartIntegralModel.fFin R F j ≫ TwoChartIntegralModel.ιFin R F j)
    (Spec.map (CommRingCat.ofHom α) ≫ TwoChartIntegralModel.ιFin R F j) hmem
  refine ⟨w, ?_, ?_⟩
  · apply ringHom_eq_of_SpecMap_comp_eq (TwoChartIntegralModel.ιFin R F j)
    rw [CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]
    show Spec.map (CommRingCat.ofHom w) ≫ TwoChartIntegralModel.fFin R F j ≫ TwoChartIntegralModel.ιFin R F j = _
    exact hw
  · apply ringHom_eq_of_SpecMap_comp_eq (TwoChartIntegralModel.ιInf R F j)
    rw [CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]
    show Spec.map (CommRingCat.ofHom w) ≫ TwoChartIntegralModel.fInf R F j ≫ TwoChartIntegralModel.ιInf R F j = _
    rw [← TwoChartIntegralModel.glue_condition]
    exact hw.trans h

end IgusaSide

section Glued

variable (K : Type uK) [Field K] {L : Type uK} [Field L] [Algebra K L] (t : L)

private def _root_.SPMH.toAlgHom {R : Type uK} [CommRing R] [Algebra K R] (φ : R →+* K)
    (hφ : φ.comp (algebraMap K R) = RingHom.id K) : R →ₐ[K] K :=
  { φ with commutes' := fun c => RingHom.congr_fun hφ c }

p2m_export "SPMH" "toAlgHom"
@[scoped simp]
theorem toAlgHom_toRingHom {R : Type uK} [CommRing R] [Algebra K R] (φ : R →+* K)
    (hφ : φ.comp (algebraMap K R) = RingHom.id K) : (toAlgHom K φ hφ).toRingHom = φ :=
  rfl

variable [Fact (t ≠ 0)]

theorem exists_algHom_eq_SpecMap_comp_ι₀
    (x : Spec (CommRingCat.of K) ⟶ CurveModel.glued K t) (hx2 : x ≫ CurveModel.gluedToBase K t = 𝟙 _)
    (hx : x.base (IsLocalRing.closedPoint K) ∈ Set.range (CurveModel.ι₀ K t).base) :
    ∃ φ : ↥(CurveModel.chartRing K ({t} : Set L)) →ₐ[K] K,
      Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ CurveModel.ι₀ K t = x := by
  have hrange : Set.range x.base ⊆ Set.range (CurveModel.ι₀ K t).base := by
    rintro _ ⟨p, rfl⟩
    have hp : p = IsLocalRing.closedPoint K := Subsingleton.elim (α := PrimeSpectrum K) _ _
    rw [hp]
    exact hx
  have hfac := IsOpenImmersion.lift_fac (CurveModel.ι₀ K t) x hrange
  have h1 : IsOpenImmersion.lift (CurveModel.ι₀ K t) x hrange ≫
      (CurveModel.ι₀ K t ≫ CurveModel.gluedToBase K t) = 𝟙 _ := by
    rw [← Category.assoc, hfac]
    exact hx2
  rw [CurveModel.ι₀_gluedToBase, ← Spec.map_preimage (IsOpenImmersion.lift (CurveModel.ι₀ K t) x hrange),
    ← Spec.map_comp] at h1
  have h2 := congrArg CommRingCat.Hom.hom (Spec.map_injective (h1.trans (Spec.map_id _).symm))
  refine ⟨toAlgHom K (Spec.preimage (IsOpenImmersion.lift (CurveModel.ι₀ K t) x hrange)).hom h2, ?_⟩
  rw [toAlgHom_toRingHom, CommRingCat.ofHom_hom, Spec.map_preimage, IsOpenImmersion.lift_fac]

theorem exists_algHom_eq_SpecMap_comp_ιInf
    (x : Spec (CommRingCat.of K) ⟶ CurveModel.glued K t) (hx2 : x ≫ CurveModel.gluedToBase K t = 𝟙 _)
    (hx : x.base (IsLocalRing.closedPoint K) ∈ Set.range (CurveModel.ιInf K t).base) :
    ∃ φ : ↥(CurveModel.chartRing K ({t⁻¹} : Set L)) →ₐ[K] K,
      Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ CurveModel.ιInf K t = x := by
  have hrange : Set.range x.base ⊆ Set.range (CurveModel.ιInf K t).base := by
    rintro _ ⟨p, rfl⟩
    have hp : p = IsLocalRing.closedPoint K := Subsingleton.elim (α := PrimeSpectrum K) _ _
    rw [hp]
    exact hx
  have hfac := IsOpenImmersion.lift_fac (CurveModel.ιInf K t) x hrange
  have h1 : IsOpenImmersion.lift (CurveModel.ιInf K t) x hrange ≫
      (CurveModel.ιInf K t ≫ CurveModel.gluedToBase K t) = 𝟙 _ := by
    rw [← Category.assoc, hfac]
    exact hx2
  rw [CurveModel.ιInf_gluedToBase, ← Spec.map_preimage (IsOpenImmersion.lift (CurveModel.ιInf K t) x hrange),
    ← Spec.map_comp] at h1
  have h2 := congrArg CommRingCat.Hom.hom (Spec.map_injective (h1.trans (Spec.map_id _).symm))
  refine ⟨toAlgHom K (Spec.preimage (IsOpenImmersion.lift (CurveModel.ιInf K t) x hrange)).hom h2, ?_⟩
  rw [toAlgHom_toRingHom, CommRingCat.ofHom_hom, Spec.map_preimage, IsOpenImmersion.lift_fac]

theorem base_closedPoint_eq_of_eq_SpecMap_comp {R : Type uK} [CommRing R]
    (ι : Spec (CommRingCat.of R) ⟶ CurveModel.glued K t) (φ : R →+* K)
    (x : Spec (CommRingCat.of K) ⟶ CurveModel.glued K t) (hx : Spec.map (CommRingCat.ofHom φ) ≫ ι = x) :
    x.base (IsLocalRing.closedPoint K) = ι.base ((Spec.map (CommRingCat.ofHom φ)).base (IsLocalRing.closedPoint K)) ∧
    ((Spec.map (CommRingCat.ofHom φ)).base (IsLocalRing.closedPoint K)).asIdeal = RingHom.ker φ := by
  constructor
  · rw [← hx]; rfl
  · show Ideal.comap φ (IsLocalRing.maximalIdeal K) = RingHom.ker φ
    rw [IsLocalRing.maximalIdeal_eq_bot, ← RingHom.ker_eq_comap_bot]

end Glued

section GluedZero

variable (K : Type) [Field K] {L : Type} [Field L] [Algebra K L] (t : L) [Fact (t ≠ 0)]

theorem mem_range_ιFin_iff_of_pins {R : Type} [CommRing R] {F : Type} [Field F] [Algebra R F] {j : F} [Fact (j ≠ 0)]
    (g : CurveModel.glued K t ⟶ AlgebraicCurve.TwoChartIntegralModel R F j)
    (rF : ↥(TwoChartIntegralModel.chartAlgFin R F j) →+* ↥(CurveModel.chartRing K ({t} : Set L)))
    (rI : ↥(TwoChartIntegralModel.chartAlgInf R F j) →+* ↥(CurveModel.chartRing K ({t⁻¹} : Set L)))
    (hF : CurveModel.ι₀ K t ≫ g = Spec.map (CommRingCat.ofHom rF) ≫ TwoChartIntegralModel.ιFin R F j)
    (hI : CurveModel.ιInf K t ≫ g = Spec.map (CommRingCat.ofHom rI) ≫ TwoChartIntegralModel.ιInf R F j)
    (hjI : rI (TwoChartIntegralModel.jInvChartInf R F j) = CurveModel.tInvChart K t) (y : CurveModel.glued K t) :
    g.base y ∈ Set.range (TwoChartIntegralModel.ιFin R F j).base ↔ y ∈ Set.range (CurveModel.ι₀ K t).base := by
  rcases CurveModel.mem_range_ι₀_or_mem_range_ιInf K t y with ⟨x₀, rfl⟩ | ⟨z, rfl⟩
  · refine ⟨fun _ => ⟨x₀, rfl⟩, fun _ => ⟨(Spec.map (CommRingCat.ofHom rF)).base x₀, ?_⟩⟩
    change (Spec.map (CommRingCat.ofHom rF) ≫ TwoChartIntegralModel.ιFin R F j).base x₀ = (CurveModel.ι₀ K t ≫ g).base x₀
    rw [hF]
  · have hz : g.base ((CurveModel.ιInf K t).base z) =
        (TwoChartIntegralModel.ιInf R F j).base ((Spec.map (CommRingCat.ofHom rI)).base z) := by
      change (CurveModel.ιInf K t ≫ g).base z = (Spec.map (CommRingCat.ofHom rI) ≫ TwoChartIntegralModel.ιInf R F j).base z
      rw [hI]
    rw [hz, IgusaSide.ιInf_mem_range_ιFin_iff, CurveModel.ιInf_mem_range_ι₀_iff]
    show TwoChartIntegralModel.jInvChartInf R F j ∉ z.asIdeal.comap rI ↔ _
    rw [Ideal.mem_comap]
    exact not_congr (iff_of_eq (congrArg (· ∈ z.asIdeal) hjI))

end GluedZero

namespace IgusaSide

variable {R : Type} [CommRing R] {F : Type} [Field F] [Algebra R F] {j : F} [Fact (j ≠ 0)]

set_option synthInstance.maxHeartbeats 1600000 in
theorem range_fFin : Set.range (TwoChartIntegralModel.fFin R F j).base =
    ((PrimeSpectrum.basicOpen (TwoChartIntegralModel.jChartFin R F j) :
        TopologicalSpace.Opens (PrimeSpectrum ↥(TwoChartIntegralModel.chartAlgFin R F j))) : Set (PrimeSpectrum ↥(TwoChartIntegralModel.chartAlgFin R F j))) := by
  letI := (TwoChartIntegralModel.inclFin R F j).toRingHom.toAlgebra
  haveI := TwoChartIntegralModel.isLocalization_away_inclFin R F j
  exact PrimeSpectrum.localization_away_comap_range ↥(TwoChartIntegralModel.chartAlgMid R F j) (TwoChartIntegralModel.jChartFin R F j)

theorem ιFin_mem_range_ιInf_iff (x₀ : TwoChartIntegralModel.XFin R F j) :
    (TwoChartIntegralModel.ιFin R F j).base x₀ ∈ Set.range (TwoChartIntegralModel.ιInf R F j).base ↔
      TwoChartIntegralModel.jChartFin R F j ∉ x₀.asIdeal := by
  rw [← PrimeSpectrum.mem_basicOpen, ← SetLike.mem_coe, ← range_fFin, Set.mem_range]
  constructor
  · rintro ⟨xi, h⟩
    obtain ⟨w, hw, -⟩ := (ιFin_eq_ιInf_iff x₀ xi).mp h.symm
    exact ⟨w, hw⟩
  · rintro ⟨w, rfl⟩
    exact ⟨(TwoChartIntegralModel.fInf R F j).base w, ((ιFin_eq_ιInf_iff _ _).mpr ⟨w, rfl, rfl⟩).symm⟩

end IgusaSide

section GluedInf

variable (K : Type) [Field K] {L : Type} [Field L] [Algebra K L] (t : L) [Fact (t ≠ 0)]

theorem mem_range_ιInf_iff_of_pins {R : Type} [CommRing R] {F : Type} [Field F] [Algebra R F] {j : F} [Fact (j ≠ 0)]
    (g : CurveModel.glued K t ⟶ AlgebraicCurve.TwoChartIntegralModel R F j)
    (rF : ↥(TwoChartIntegralModel.chartAlgFin R F j) →+* ↥(CurveModel.chartRing K ({t} : Set L)))
    (rI : ↥(TwoChartIntegralModel.chartAlgInf R F j) →+* ↥(CurveModel.chartRing K ({t⁻¹} : Set L)))
    (hF : CurveModel.ι₀ K t ≫ g = Spec.map (CommRingCat.ofHom rF) ≫ TwoChartIntegralModel.ιFin R F j)
    (hI : CurveModel.ιInf K t ≫ g = Spec.map (CommRingCat.ofHom rI) ≫ TwoChartIntegralModel.ιInf R F j)
    (hjF : rF (TwoChartIntegralModel.jChartFin R F j) = CurveModel.tChart K t) (y : CurveModel.glued K t) :
    g.base y ∈ Set.range (TwoChartIntegralModel.ιInf R F j).base ↔ y ∈ Set.range (CurveModel.ιInf K t).base := by
  rcases CurveModel.mem_range_ι₀_or_mem_range_ιInf K t y with ⟨x₀, rfl⟩ | ⟨z, rfl⟩
  · have hx : g.base ((CurveModel.ι₀ K t).base x₀) =
        (TwoChartIntegralModel.ιFin R F j).base ((Spec.map (CommRingCat.ofHom rF)).base x₀) := by
      change (CurveModel.ι₀ K t ≫ g).base x₀ = (Spec.map (CommRingCat.ofHom rF) ≫ TwoChartIntegralModel.ιFin R F j).base x₀
      rw [hF]
    rw [hx, IgusaSide.ιFin_mem_range_ιInf_iff, CurveModel.ι₀_mem_range_ιInf_iff]
    show TwoChartIntegralModel.jChartFin R F j ∉ x₀.asIdeal.comap rF ↔ _
    rw [Ideal.mem_comap]
    exact not_congr (iff_of_eq (congrArg (· ∈ x₀.asIdeal) hjF))
  · refine ⟨fun _ => ⟨z, rfl⟩, fun _ => ⟨(Spec.map (CommRingCat.ofHom rI)).base z, ?_⟩⟩
    change (Spec.map (CommRingCat.ofHom rI) ≫ TwoChartIntegralModel.ιInf R F j).base z = (CurveModel.ιInf K t ≫ g).base z
    rw [hI]

end GluedInf

end SPMH
p2m_reactivate "P2MW.S_ModularCurve_exists_curveModel_specialFibreIso_twoChartIntegralModel_qExpFunctionFieldC_chartCentre_of_not_dvd.SPMH"

open SPMH in
set_option maxHeartbeats 12800000 in
set_option synthInstance.maxHeartbeats 1600000 in

theorem SPMH.perA
    (M : ℕ) [NeZero M] (Γ : Subgroup SL(2, ℤ))
    (hΓ₁ : CongruenceSubgroup.Gamma1 M ≤ Γ) (hΓ₀ : Γ ≤ CongruenceSubgroup.Gamma0 M)
    (p : ℕ) [Fact p.Prime] (hpM : ¬ p ∣ M)
    (j : ↥(qExpFunctionFieldC ℚ Γ)) [Fact (j ≠ 0)] (hj : (j : LaurentSeries ℚ) = jqModC ℚ)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (ρ : ↥(GaloisRep.ratLocalizedAt p) →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap ↥(GaloisRep.ratLocalizedAt p) (AlgebraicClosure ℚ)) :
    ∃ (Ms : CurveModel (ResidueField ↥A) ↥(qExpFunctionFieldC (ResidueField ↥A) Γ))
      (es : Ms.C ⟶ pullback (TwoChartIntegralModel.toBase ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ Γ) j)
        (Spec.map (CommRingCat.ofHom ((residue ↥A).comp ρ)))) (_ : IsIso es)
      (_ : es ≫ pullback.snd _ _ = Ms.toBase)
      (πFin : ↥(TwoChartIntegralModel.chartAlgFin ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ Γ) j) →+*
        ↥(qExpFunctionFieldC (ResidueField ↥A) Γ))
      (πInf : ↥(TwoChartIntegralModel.chartAlgInf ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ Γ) j) →+*
        ↥(qExpFunctionFieldC (ResidueField ↥A) Γ)),
      (∀ b : ↥(TwoChartIntegralModel.chartAlgFin ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ Γ) j),
        ∃ yb : LaurentSeries ↥A,
          coeffMap A.subtype yb = coeffEmb (AlgebraicClosure ℚ) ((b : ↥(qExpFunctionFieldC ℚ Γ)) : LaurentSeries ℚ) ∧
            ((πFin b : ↥(qExpFunctionFieldC (ResidueField ↥A) Γ)) : LaurentSeries (ResidueField ↥A)) = coeffMap (residue ↥A) yb) ∧
      (∀ b : ↥(TwoChartIntegralModel.chartAlgInf ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ Γ) j),
        ∃ yb : LaurentSeries ↥A,
          coeffMap A.subtype yb = coeffEmb (AlgebraicClosure ℚ) ((b : ↥(qExpFunctionFieldC ℚ Γ)) : LaurentSeries ℚ) ∧
            ((πInf b : ↥(qExpFunctionFieldC (ResidueField ↥A) Γ)) : LaurentSeries (ResidueField ↥A)) = coeffMap (residue ↥A) yb) ∧
      ∀ [IsAlgClosed (ResidueField ↥A)],
        (∀ (y : {q : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ Ms.C // q ≫ Ms.toBase = 𝟙 _})
          (β : ↥(TwoChartIntegralModel.chartAlgFin ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ Γ) j) →+* ResidueField ↥A),
          y.1 ≫ es ≫ pullback.fst _ _ =
            Spec.map (CommRingCat.ofHom β) ≫ TwoChartIntegralModel.ιFin ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ Γ) j →
          ∀ b : ↥(TwoChartIntegralModel.chartAlgFin ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ Γ) j),
            (πFin b : ↥(qExpFunctionFieldC (ResidueField ↥A) Γ)) -
                algebraMap (ResidueField ↥A) ↥(qExpFunctionFieldC (ResidueField ↥A) Γ) (β b) ∈
              (Ms.pointEquivPlace y).toValuationSubring.nonunits) ∧
        (∀ (y : {q : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ Ms.C // q ≫ Ms.toBase = 𝟙 _})
          (β : ↥(TwoChartIntegralModel.chartAlgInf ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ Γ) j) →+* ResidueField ↥A),
          y.1 ≫ es ≫ pullback.fst _ _ =
            Spec.map (CommRingCat.ofHom β) ≫ TwoChartIntegralModel.ιInf ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ Γ) j →
          ∀ b : ↥(TwoChartIntegralModel.chartAlgInf ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ Γ) j),
            (πInf b : ↥(qExpFunctionFieldC (ResidueField ↥A) Γ)) -
                algebraMap (ResidueField ↥A) ↥(qExpFunctionFieldC (ResidueField ↥A) Γ) (β b) ∈
              (Ms.pointEquivPlace y).toValuationSubring.nonunits) := by
  haveI hAC : IsAlgClosed (ResidueField ↥A) := ValuationSubring.isAlgClosed_residueField_algebraicClosure_rat A
  classical

  haveI hchar : CharP (ResidueField ↥A) p := ValuationSubring.charP_residueField_of_liesOverPrime p A hA
  letI instAlg : Algebra ↥(GaloisRep.ratLocalizedAt p) (ResidueField ↥A) := ((residue ↥A).comp ρ).toAlgebra

  have hT : ModularGroup.T ∈ Γ := hΓ₁ (SPMH.T_mem_Gamma1 M)
  haveI : Γ.FiniteIndex := SPMH.finiteIndex_of_gamma1_le M Γ hΓ₁
  obtain ⟨x, hx, htx, hfdx, -⟩ :=
    ModularCurve.exists_transcendental_finiteDimensional_qExpFunctionFieldC_residueField (AlgebraicClosure ℚ) A Γ hT
  haveI := hfdx
  have hx0 : x ≠ 0 := fun h0 => htx (by rw [h0]; exact isAlgebraic_zero)
  haveI : Fact (x ≠ 0) := ⟨hx0⟩
  have hxmem : jqModC (ResidueField ↥A) ∈ qExpFunctionFieldC (ResidueField ↥A) Γ := by rw [← hx]; exact x.2
  have hxe : (⟨jqModC (ResidueField ↥A), hxmem⟩ : ↥(qExpFunctionFieldC (ResidueField ↥A) Γ)) = x := Subtype.ext hx.symm
  haveI : Algebra.IsSeparable ↥(IntermediateField.adjoin (ResidueField ↥A) ({x} : Set ↥(qExpFunctionFieldC (ResidueField ↥A) Γ)))
      ↥(qExpFunctionFieldC (ResidueField ↥A) Γ) := by
    haveI : Algebra.IsAlgebraic
        ↥(IntermediateField.adjoin (ResidueField ↥A) ({(⟨jqModC (ResidueField ↥A), hxmem⟩ : ↥(qExpFunctionFieldC (ResidueField ↥A) Γ))} :
          Set ↥(qExpFunctionFieldC (ResidueField ↥A) Γ)))
        ↥(qExpFunctionFieldC (ResidueField ↥A) Γ) := by
      rw [hxe]; exact Algebra.IsAlgebraic.of_finite _ _
    have key := ModularCurve.isSeparable_adjoin_jqModC_of_isAlgebraic (ResidueField ↥A) (qExpFunctionFieldC (ResidueField ↥A) Γ) hxmem
    rw [hxe] at key
    exact key

  obtain ⟨⟨eFin, hjF, hreadF⟩, ⟨eInf, hjI, hreadI⟩⟩ :=
    ModularCurve.exists_algEquiv_residueField_tensor_chartAlg_twoChartIntegralModel_qExpFunctionFieldC_chartRing
      M Γ hΓ₁ hΓ₀ p hpM j hj A hA ρ hρ x hx

  obtain ⟨hliftF, hliftI⟩ :=
    ModularCurve.exists_coeffMap_eq_coe_of_mem_chartAlg_twoChartIntegralModel_qExpFunctionFieldC Γ p j hj
  have hcompat : ∀ (b : ↥(TwoChartIntegralModel.chartAlgFin ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ Γ) j))
      (b' : ↥(TwoChartIntegralModel.chartAlgInf ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ Γ) j)) (n : ℕ),
      (b : ↥(qExpFunctionFieldC ℚ Γ)) = (b' : ↥(qExpFunctionFieldC ℚ Γ)) * j ^ n →
      ((eFin ((1 : ResidueField ↥A) ⊗ₜ[↥(GaloisRep.ratLocalizedAt p)] b)) : ↥(qExpFunctionFieldC (ResidueField ↥A) Γ)) =
        ((eInf ((1 : ResidueField ↥A) ⊗ₜ[↥(GaloisRep.ratLocalizedAt p)] b')) : ↥(qExpFunctionFieldC (ResidueField ↥A) Γ)) * x ^ n := by
    intro b b' n h
    obtain ⟨y₀, hy₀⟩ := hliftI b'

    have hyA : coeffMap A.subtype (coeffMap ρ y₀) = coeffEmb (AlgebraicClosure ℚ) (((b' : ↥(qExpFunctionFieldC ℚ Γ)) : LaurentSeries ℚ)) := by
      rw [SPMH.coeffMap_coeffMap, hρ, ← hy₀, SPMH.coeffEmb_coeffMap_algebraMap]
    have hyB : coeffMap A.subtype (coeffMap ρ y₀ * jqModC ↥A ^ n) =
        coeffEmb (AlgebraicClosure ℚ) (((b : ↥(qExpFunctionFieldC ℚ Γ)) : LaurentSeries ℚ)) := by
      rw [map_mul, map_pow, hyA, SPMH.coeffMap_jqModC, h]
      show _ = coeffEmb (AlgebraicClosure ℚ) (((b' : ↥(qExpFunctionFieldC ℚ Γ)) : LaurentSeries ℚ) * ((j : ↥(qExpFunctionFieldC ℚ Γ)) : LaurentSeries ℚ) ^ n)
      rw [map_mul, map_pow, hj, SPMH.coeffEmb_jqModC]
    have h1 := hreadF b _ hyB
    have h2 := hreadI b' _ hyA
    apply Subtype.ext
    rw [h1, map_mul, map_pow, ← h2, SPMH.coeffMap_jqModC, MulMemClass.coe_mul, SubmonoidClass.coe_pow, hx]

  obtain ⟨hPr, hSm, ⟨P, hPbij, hPst⟩, hAff⟩ :=
    AlgebraicCurve.CurveModel.isProper_smooth_places_affineCover_glued (ResidueField ↥A)
      (L := ↥(qExpFunctionFieldC (ResidueField ↥A) Γ)) x htx
  obtain ⟨es, hes_iso, hes, hpinF, hpinI⟩ :=
    AlgebraicCurve.TwoChartIntegralModel.exists_iso_glued_pullback_toBase_of_algEquiv_chartAlg_chartRing
      ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ Γ) j (ResidueField ↥A) x eFin eInf
      hjF hjI hcompat
  let Ms : CurveModel (ResidueField ↥A) ↥(qExpFunctionFieldC (ResidueField ↥A) Γ) :=
    { C := CurveModel.glued (ResidueField ↥A) x
      toBase := CurveModel.gluedToBase (ResidueField ↥A) x
      isProper := hPr
      smooth := hSm
      ffEquiv := CurveModel.gluedFunctionFieldEquiv (ResidueField ↥A) x
      ffEquiv_algebraMap := CurveModel.gluedFunctionFieldEquiv_algebraMap (ResidueField ↥A) x
      placeOfPoint := P
      placeOfPoint_bijective := hPbij
      range_stalk_eq := hPst
      finset_subset_affineOpen := hAff }

  set rF : ↥(TwoChartIntegralModel.chartAlgFin ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ Γ) j) →+*
      ↥(CurveModel.chartRing (ResidueField ↥A) ({x} : Set ↥(qExpFunctionFieldC (ResidueField ↥A) Γ))) :=
    eFin.toAlgHom.toRingHom.comp (Algebra.TensorProduct.includeRight
      (R := ↥(GaloisRep.ratLocalizedAt p)) (A := ResidueField ↥A)
      (B := ↥(TwoChartIntegralModel.chartAlgFin ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ Γ) j))).toRingHom with hrF
  set rI : ↥(TwoChartIntegralModel.chartAlgInf ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ Γ) j) →+*
      ↥(CurveModel.chartRing (ResidueField ↥A) ({x⁻¹} : Set ↥(qExpFunctionFieldC (ResidueField ↥A) Γ))) :=
    eInf.toAlgHom.toRingHom.comp (Algebra.TensorProduct.includeRight
      (R := ↥(GaloisRep.ratLocalizedAt p)) (A := ResidueField ↥A)
      (B := ↥(TwoChartIntegralModel.chartAlgInf ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ Γ) j))).toRingHom with hrI
  have rF_apply : ∀ b, rF b = eFin ((1 : ResidueField ↥A) ⊗ₜ[↥(GaloisRep.ratLocalizedAt p)] b) := fun b => rfl
  have rI_apply : ∀ b, rI b = eInf ((1 : ResidueField ↥A) ⊗ₜ[↥(GaloisRep.ratLocalizedAt p)] b) := fun b => rfl
  have hjI' : rI (TwoChartIntegralModel.jInvChartInf ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ Γ) j) =
      CurveModel.tInvChart (ResidueField ↥A) x := by
    apply Subtype.ext
    rw [rI_apply, hjI]
    rfl
  have hjF' : rF (TwoChartIntegralModel.jChartFin ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ Γ) j) =
      CurveModel.tChart (ResidueField ↥A) x := by
    apply Subtype.ext
    rw [rF_apply, hjF]
    rfl
  have hF' : CurveModel.ι₀ (ResidueField ↥A) x ≫ (es ≫ pullback.fst _ _) =
      Spec.map (CommRingCat.ofHom rF) ≫ TwoChartIntegralModel.ιFin ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ Γ) j := hpinF
  have hI' : CurveModel.ιInf (ResidueField ↥A) x ≫ (es ≫ pullback.fst _ _) =
      Spec.map (CommRingCat.ofHom rI) ≫ TwoChartIntegralModel.ιInf ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ Γ) j := hpinI

  let πFin : ↥(TwoChartIntegralModel.chartAlgFin ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ Γ) j) →+*
      ↥(qExpFunctionFieldC (ResidueField ↥A) Γ) :=
    (CurveModel.chartRing (ResidueField ↥A) ({x} : Set ↥(qExpFunctionFieldC (ResidueField ↥A) Γ))).val.toRingHom.comp rF
  let πInf : ↥(TwoChartIntegralModel.chartAlgInf ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ Γ) j) →+*
      ↥(qExpFunctionFieldC (ResidueField ↥A) Γ) :=
    (CurveModel.chartRing (ResidueField ↥A) ({x⁻¹} : Set ↥(qExpFunctionFieldC (ResidueField ↥A) Γ))).val.toRingHom.comp rI
  have πFin_apply : ∀ b, πFin b = (eFin ((1 : ResidueField ↥A) ⊗ₜ[↥(GaloisRep.ratLocalizedAt p)] b)).1 := fun b => rfl
  have πInf_apply : ∀ b, πInf b = (eInf ((1 : ResidueField ↥A) ⊗ₜ[↥(GaloisRep.ratLocalizedAt p)] b)).1 := fun b => rfl
  refine ⟨Ms, es, hes_iso, hes, πFin, πInf, ?_, ?_, ?_⟩
  ·
    intro b
    obtain ⟨y₀, hy₀⟩ := hliftF b
    have hyA : coeffMap A.subtype (coeffMap ρ y₀) = coeffEmb (AlgebraicClosure ℚ) (((b : ↥(qExpFunctionFieldC ℚ Γ)) : LaurentSeries ℚ)) := by
      rw [SPMH.coeffMap_coeffMap, hρ, ← hy₀, SPMH.coeffEmb_coeffMap_algebraMap]
    exact ⟨coeffMap ρ y₀, hyA, by rw [πFin_apply]; exact hreadF b _ hyA⟩
  ·
    intro b
    obtain ⟨y₀, hy₀⟩ := hliftI b
    have hyA : coeffMap A.subtype (coeffMap ρ y₀) = coeffEmb (AlgebraicClosure ℚ) (((b : ↥(qExpFunctionFieldC ℚ Γ)) : LaurentSeries ℚ)) := by
      rw [SPMH.coeffMap_coeffMap, hρ, ← hy₀, SPMH.coeffEmb_coeffMap_algebraMap]
    exact ⟨coeffMap ρ y₀, hyA, by rw [πInf_apply]; exact hreadI b _ hyA⟩
  intro _
  constructor
  ·
    intro y β hy b
    have hy0 : (es ≫ pullback.fst _ _).base (y.1.base (IsLocalRing.closedPoint (ResidueField ↥A))) ∈
        Set.range (TwoChartIntegralModel.ιFin ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ Γ) j).base := by
      refine ⟨(Spec.map (CommRingCat.ofHom β)).base (IsLocalRing.closedPoint (ResidueField ↥A)), ?_⟩
      change (Spec.map (CommRingCat.ofHom β) ≫ TwoChartIntegralModel.ιFin _ _ _).base _ = (y.1 ≫ es ≫ pullback.fst _ _).base _
      rw [hy]
    have hy1 : y.1.base (IsLocalRing.closedPoint (ResidueField ↥A)) ∈ Set.range (CurveModel.ι₀ (ResidueField ↥A) x).base :=
      (mem_range_ιFin_iff_of_pins (ResidueField ↥A) x _ rF rI hF' hI' hjI' _).mp hy0
    obtain ⟨χ, hχ⟩ := exists_algHom_eq_SpecMap_comp_ι₀ (ResidueField ↥A) x y.1 y.2 hy1
    have hβ : β = χ.toRingHom.comp rF := by
      apply IgusaSide.ringHom_eq_of_SpecMap_comp_eq (TwoChartIntegralModel.ιFin ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ Γ) j)
      rw [← hy, ← hχ, Category.assoc, hF', ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    have hcl : y.1.base (IsLocalRing.closedPoint (ResidueField ↥A)) ∈ closedPoints (CurveModel.glued (ResidueField ↥A) x) :=
      (pointEquivClosedPoint Ms.toBase y).2
    let z : closedPoints (CurveModel.glued (ResidueField ↥A) x) := ⟨_, hcl⟩
    have hz : z.1 = (CurveModel.ι₀ (ResidueField ↥A) x).base
        ((Spec.map (CommRingCat.ofHom χ.toRingHom)).base (IsLocalRing.closedPoint (ResidueField ↥A))) :=
      (base_closedPoint_eq_of_eq_SpecMap_comp (ResidueField ↥A) x _ χ.toRingHom y.1 hχ).1
    have hplace : Ms.pointEquivPlace y = P z := rfl
    obtain ⟨hmem, hnon⟩ :=
      AlgebraicCurve.CurveModel.coe_mem_and_sub_algebraMap_mem_nonunits_of_range_stalk_eq_iota0 (ResidueField ↥A)
        x P hPst χ z hz (eFin ((1 : ResidueField ↥A) ⊗ₜ[↥(GaloisRep.ratLocalizedAt p)] b))
    have hχb : χ (eFin ((1 : ResidueField ↥A) ⊗ₜ[↥(GaloisRep.ratLocalizedAt p)] b)) = β b := by
      rw [hβ]; rfl
    show ((eFin ((1 : ResidueField ↥A) ⊗ₜ[↥(GaloisRep.ratLocalizedAt p)] b)).1 : ↥(qExpFunctionFieldC (ResidueField ↥A) Γ)) - _ ∈ _
    rw [hplace, ← hχb]
    exact hnon
  ·
    intro y β hy b
    have hy0 : (es ≫ pullback.fst _ _).base (y.1.base (IsLocalRing.closedPoint (ResidueField ↥A))) ∈
        Set.range (TwoChartIntegralModel.ιInf ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ Γ) j).base := by
      refine ⟨(Spec.map (CommRingCat.ofHom β)).base (IsLocalRing.closedPoint (ResidueField ↥A)), ?_⟩
      change (Spec.map (CommRingCat.ofHom β) ≫ TwoChartIntegralModel.ιInf _ _ _).base _ = (y.1 ≫ es ≫ pullback.fst _ _).base _
      rw [hy]
    have hy1 : y.1.base (IsLocalRing.closedPoint (ResidueField ↥A)) ∈ Set.range (CurveModel.ιInf (ResidueField ↥A) x).base :=
      (mem_range_ιInf_iff_of_pins (ResidueField ↥A) x _ rF rI hF' hI' hjF' _).mp hy0
    obtain ⟨χ, hχ⟩ := exists_algHom_eq_SpecMap_comp_ιInf (ResidueField ↥A) x y.1 y.2 hy1
    have hβ : β = χ.toRingHom.comp rI := by
      apply IgusaSide.ringHom_eq_of_SpecMap_comp_eq (TwoChartIntegralModel.ιInf ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ Γ) j)
      rw [← hy, ← hχ, Category.assoc, hI', ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    have hcl : y.1.base (IsLocalRing.closedPoint (ResidueField ↥A)) ∈ closedPoints (CurveModel.glued (ResidueField ↥A) x) :=
      (pointEquivClosedPoint Ms.toBase y).2
    let z : closedPoints (CurveModel.glued (ResidueField ↥A) x) := ⟨_, hcl⟩
    have hz : z.1 = (CurveModel.ιInf (ResidueField ↥A) x).base
        ((Spec.map (CommRingCat.ofHom χ.toRingHom)).base (IsLocalRing.closedPoint (ResidueField ↥A))) :=
      (base_closedPoint_eq_of_eq_SpecMap_comp (ResidueField ↥A) x _ χ.toRingHom y.1 hχ).1
    have hplace : Ms.pointEquivPlace y = P z := rfl
    obtain ⟨hmem, hnon⟩ :=
      AlgebraicCurve.CurveModel.coe_mem_and_sub_algebraMap_mem_nonunits_of_range_stalk_eq_iotaInf (ResidueField ↥A)
        x P hPst χ z hz (eInf ((1 : ResidueField ↥A) ⊗ₜ[↥(GaloisRep.ratLocalizedAt p)] b))
    have hχb : χ (eInf ((1 : ResidueField ↥A) ⊗ₜ[↥(GaloisRep.ratLocalizedAt p)] b)) = β b := by
      rw [hβ]; rfl
    show ((eInf ((1 : ResidueField ↥A) ⊗ₜ[↥(GaloisRep.ratLocalizedAt p)] b)).1 : ↥(qExpFunctionFieldC (ResidueField ↥A) Γ)) - _ ∈ _
    rw [hplace, ← hχb]
    exact hnon

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in
theorem solution
    (M : ℕ) [NeZero M] (Γ : Subgroup SL(2, ℤ))
    (hΓ₁ : CongruenceSubgroup.Gamma1 M ≤ Γ) (hΓ₀ : Γ ≤ CongruenceSubgroup.Gamma0 M)
    (p : ℕ) [Fact p.Prime] (hpM : ¬ p ∣ M)
    (j : ↥(qExpFunctionFieldC ℚ Γ)) [Fact (j ≠ 0)] (hj : (j : LaurentSeries ℚ) = jqModC ℚ) :
    ∃ (ρ : ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime p →
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
        es A hA ≫ pullback.snd _ _ = (Ms A hA).toBase)
      (πFin : ∀ (A : ValuationSubring (AlgebraicClosure ℚ)), A.LiesOverPrime p →
        (↥(TwoChartIntegralModel.chartAlgFin ↥(GaloisRep.ratLocalizedAt p)
            ↥(qExpFunctionFieldC ℚ Γ) j) →+* ↥(qExpFunctionFieldC (ResidueField ↥A) Γ)))
      (πInf : ∀ (A : ValuationSubring (AlgebraicClosure ℚ)), A.LiesOverPrime p →
        (↥(TwoChartIntegralModel.chartAlgInf ↥(GaloisRep.ratLocalizedAt p)
            ↥(qExpFunctionFieldC ℚ Γ) j) →+* ↥(qExpFunctionFieldC (ResidueField ↥A) Γ))),
    ∀ (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p),
      (∀ b : ↥(TwoChartIntegralModel.chartAlgFin ↥(GaloisRep.ratLocalizedAt p)
          ↥(qExpFunctionFieldC ℚ Γ) j),
        ∃ yb : LaurentSeries ↥A,
          coeffMap A.subtype yb =
              coeffEmb (AlgebraicClosure ℚ) ((b : ↥(qExpFunctionFieldC ℚ Γ)) : LaurentSeries ℚ) ∧
            ((πFin A hA b : ↥(qExpFunctionFieldC (ResidueField ↥A) Γ)) :
                LaurentSeries (ResidueField ↥A)) = coeffMap (residue ↥A) yb) ∧
      (∀ b : ↥(TwoChartIntegralModel.chartAlgInf ↥(GaloisRep.ratLocalizedAt p)
          ↥(qExpFunctionFieldC ℚ Γ) j),
        ∃ yb : LaurentSeries ↥A,
          coeffMap A.subtype yb =
              coeffEmb (AlgebraicClosure ℚ) ((b : ↥(qExpFunctionFieldC ℚ Γ)) : LaurentSeries ℚ) ∧
            ((πInf A hA b : ↥(qExpFunctionFieldC (ResidueField ↥A) Γ)) :
                LaurentSeries (ResidueField ↥A)) = coeffMap (residue ↥A) yb) ∧
      ∀ [IsAlgClosed (ResidueField ↥A)],
        (∀ (y : {q : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ (Ms A hA).C //
              q ≫ (Ms A hA).toBase = 𝟙 _})
          (β : ↥(TwoChartIntegralModel.chartAlgFin ↥(GaloisRep.ratLocalizedAt p)
              ↥(qExpFunctionFieldC ℚ Γ) j) →+* ResidueField ↥A),
          y.1 ≫ es A hA ≫ pullback.fst _ _ =
            Spec.map (CommRingCat.ofHom β) ≫
              TwoChartIntegralModel.ιFin ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ Γ) j →
          ∀ b : ↥(TwoChartIntegralModel.chartAlgFin ↥(GaloisRep.ratLocalizedAt p)
              ↥(qExpFunctionFieldC ℚ Γ) j),
            (πFin A hA b : ↥(qExpFunctionFieldC (ResidueField ↥A) Γ)) -
                algebraMap (ResidueField ↥A) ↥(qExpFunctionFieldC (ResidueField ↥A) Γ) (β b) ∈
              ((Ms A hA).pointEquivPlace y).toValuationSubring.nonunits) ∧
        (∀ (y : {q : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ (Ms A hA).C //
              q ≫ (Ms A hA).toBase = 𝟙 _})
          (β : ↥(TwoChartIntegralModel.chartAlgInf ↥(GaloisRep.ratLocalizedAt p)
              ↥(qExpFunctionFieldC ℚ Γ) j) →+* ResidueField ↥A),
          y.1 ≫ es A hA ≫ pullback.fst _ _ =
            Spec.map (CommRingCat.ofHom β) ≫
              TwoChartIntegralModel.ιInf ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ Γ) j →
          ∀ b : ↥(TwoChartIntegralModel.chartAlgInf ↥(GaloisRep.ratLocalizedAt p)
              ↥(qExpFunctionFieldC ℚ Γ) j),
            (πInf A hA b : ↥(qExpFunctionFieldC (ResidueField ↥A) Γ)) -
                algebraMap (ResidueField ↥A) ↥(qExpFunctionFieldC (ResidueField ↥A) Γ) (β b) ∈
              ((Ms A hA).pointEquivPlace y).toValuationSubring.nonunits) := by
  have hρex := fun (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p) =>
    ValuationSubring.exists_ratLocalizedAt_ringHom_of_liesOverPrime p A hA
  choose ρ hρ using hρex
  have h := fun (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p) =>
    SPMH.perA M Γ hΓ₁ hΓ₀ p hpM j hj A hA (ρ A hA) (hρ A hA)
  choose Ms es hiso hes πFin πInf hall using h
  exact ⟨ρ, hρ, Ms, es, hiso, hes, πFin, πInf, hall⟩

end
end S_ModularCurve_exists_curveModel_specialFibreIso_twoChartIntegralModel_qExpFunctionFieldC_chartCentre_of_not_dvd
end P2MW
export P2MW.S_ModularCurve_exists_curveModel_specialFibreIso_twoChartIntegralModel_qExpFunctionFieldC_chartCentre_of_not_dvd (solution)
