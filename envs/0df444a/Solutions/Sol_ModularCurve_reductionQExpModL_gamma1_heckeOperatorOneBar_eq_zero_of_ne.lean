-- Prove2me | solution 1 for ModularCurve.reductionQExpModL_gamma1_heckeOperatorOneBar_eq_zero_of_ne
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/ed9d91d5-d451-5d2d-ba47-2aabf8e7ec6c

import Mathlib
import Definitions.Def_ModularCurve_X1HeckeModule
import Definitions.Def_ModularCurve_QExpReductionModL
import Definitions.Def_EllipticCurve_FrobeniusTrace
import Definitions.Def_ModularCurve_XH
import Definitions.Def_ModularCurve_X0ModL
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_ConstantReduction
import Theorems.Thm_ModularCurve_finrankAlong_inclusion_qExpFunctionFieldC_residueField_eq_of_not_dvd
import Theorems.Thm_ModularCurve_exists_transcendental_and_reductionInputsQExpModL_gammaH_of_not_dvd
import Theorems.Thm_ModularCurve_exists_constantReduction_pic0Map_eq_reductionQExpModL
import Theorems.Thm_AlgebraicCurve_Divisor_mapDomain_pullbackAlong_eq_and_restrictAlong_eq_of_degZero
import Theorems.Thm_AlgebraicCurve_Pic0_exists_nsmul_eq
import Theorems.Thm_ModularCurve_JOneES_exists_transcendental_finiteDimensional_laurentBaseChange
import Theorems.Thm_ModularCurve_exists_transcendental_finiteDimensional_qExpFunctionFieldC_residueField
import Theorems.Thm_AlgebraicCurve_isCurveOver_of_transcendental_of_perfectField
import Theorems.Thm_AlgebraicCurve_fundamentalIdentityAlong
import Theorems.Thm_AlgebraicCurve_separableAlong_of_charZero
import Theorems.Thm_AlgebraicCurve_Place_mem_range_algebraMap_of_forall_ord_eq_zero_of_isAlgClosed
import Theorems.Thm_ModularCurve_jqModC_mem_intFormRatiosC
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_reductionQExpModL_gamma1_heckeOperatorOneBar_eq_zero_of_ne
p2m_attr_erase "instance" "ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation ModularCurve.PhiGen.instNeZeroPhiGenCosetA CohCarrier.HeckeData.V_isScalarTower CohCarrier.HeckeData.opSubalgebra_isMulCommutative CohCarrier.HeckeData.mTheta_isPrime ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.instIsElliptic_tateBase"
p2m_attr_erase "instance" "ModularCurve.instIsElliptic_tateLaurent ModularCurve.KatzGamma0Form.instModule ModularCurve.KatzGamma0Form.instZero ModularCurve.KatzLevelPForm.instSMul ModularCurve.KatzGamma0Form.instAdd ModularCurve.KatzLevelPForm.instAddCommGroup ModularCurve.KatzGamma0Form.instNeg ModularCurve.KatzGamma0Form.instAddCommGroup ModularCurve.KatzLevelPForm.instAdd ModularCurve.KatzLevelPForm.instSub ModularCurve.KatzLevelPForm.instNeg ModularCurve.KatzGamma0Form.instSMul ModularCurve.KatzGamma0Form.instSub ModularCurve.KatzLevelPForm.instZero ModularCurve.KatzLevelPForm.instModule KatzModularForm.instAddCommGroup KatzModularForm.instSub KatzModularForm.instZero KatzModularForm.instModule KatzModularForm.instAdd KatzModularForm.instNeg KatzModularForm.instSMul WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular AlgebraicCurve.CellDissection.fintypeV AlgebraicCurve.CellDissection.fintypeC AlgebraicCurve.CellDissection.fintypeE AlgebraicCurve.CellDissection.decEqV AlgebraicCurve.CellDissection.decEqC"
p2m_attr_erase "instance" "AlgebraicCurve.CellDissection.decEqE"
p2m_attr_erase "simp" "ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.coe_cuspidalDivisor₀ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal"
p2m_attr_erase "simp" "AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen"
p2m_attr_erase "simp" "ModularCurve.constantCoeff_dedekindEtaUnitQ CohCarrier.Gen.dia.sizeOf_spec CohCarrier.Gen.U.injEq CohCarrier.Gen.T.sizeOf_spec CohCarrier.Gen.U.sizeOf_spec CohCarrier.Gen.T.injEq CohCarrier.Gen.dia.injEq CohCarrier.HeckeData.mk.sizeOf_spec CohCarrier.HeckeData.opAlgHom_X CohCarrier.HeckeData.toMLₒ_apply CohCarrier.HeckeData.mk.injEq CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply ModularCurve.ProjectiveLine.map_mk ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd"
p2m_attr_erase "simp" "AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq"
p2m_attr_erase "simp" "AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule ModularCurve.LevelN.coe_jGen HahnSeries.ramScale_apply WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.cuspData_yP ModularCurve.qTwistAlgHom_apply ModularCurve.cuspData_yQ ModularCurve.cuspData_xP ModularCurve.cuspData_xQ ModularCurve.val_cyclZeta ModularCurve.cuspShift_one ModularCurve.cuspShift_zero ModularCurve.LevelPData.mk.sizeOf_spec"
p2m_attr_erase "simp" "ModularCurve.KatzLevelPForm.neg_toFun ModularCurve.LevelP.coe_swapW ModularCurve.KatzLevelPForm.swap_swap KatzModularForm.pullbackLevelP_toFun ModularCurve.LevelPData.swap_xQ KatzModularForm.pullbackLevelP_zero ModularCurve.LevelPData.map_yP ModularCurve.KatzLevelPForm.swap_neg ModularCurve.KatzGamma0Form.toKatzLevelPForm_sub ModularCurve.KatzLevelPForm.swap_add KatzModularForm.swap_pullbackLevelP ModularCurve.KatzGamma0Form.toKatzLevelPForm_add ModularCurve.KatzLevelPForm.swap_smul ModularCurve.LevelPData.map_yQ ModularCurve.KatzLevelPForm.mk.injEq ModularCurve.KatzLevelPForm.zero_toFun KatzModularForm.pullbackLevelP_smul ModularCurve.LevelPData.swap_xP ModularCurve.KatzGamma0Form.toKatzLevelPForm_mul ModularCurve.KatzGamma0Form.toKatzLevelPForm_neg ModularCurve.LevelPData.variableChange_xQ KatzModularForm.pullbackGamma0_toKatzLevelPForm ModularCurve.KatzLevelPForm.mk.sizeOf_spec ModularCurve.KatzLevelPForm.swap_zero ModularCurve.LevelP.coe_unipotentU ModularCurve.KatzLevelPForm.mul_toFun ModularCurve.LevelPData.variableChange_yP ModularCurve.LevelPData.mk.injEq ModularCurve.KatzLevelPForm.sub_toFun ModularCurve.LevelPData.variableChange_xP ModularCurve.KatzLevelPForm.smul_toFun ModularCurve.LevelPData.swap_yP ModularCurve.LevelPData.map_xP ModularCurve.LevelPData.swap_swap ModularCurve.LevelPData.swap_yQ ModularCurve.KatzGamma0Form.toKatzLevelPForm_zero ModularCurve.KatzGamma0Form.mk.injEq ModularCurve.KatzLevelPForm.swap_toFun KatzModularForm.pullbackLevelP_add ModularCurve.KatzGamma0Form.mk.sizeOf_spec"
p2m_attr_erase "simp" "ModularCurve.LevelPData.variableChange_yQ ModularCurve.KatzLevelPForm.swap_sub ModularCurve.KatzGamma0Form.toKatzLevelPForm_smul ModularCurve.LevelPData.map_xQ ModularCurve.KatzLevelPForm.add_toFun KatzModularForm.c₆_toFun KatzModularForm.neg_toFun KatzModularForm.mul_toFun KatzModularForm.qExpansion_neg KatzModularForm.discr_toFun KatzModularForm.qExpansion_sub KatzModularForm.qExpansion_add KatzModularForm.qExpansion_mul KatzModularForm.zero_toFun KatzModularForm.mk.injEq KatzModularForm.qExpansion_smul KatzModularForm.smul_toFun KatzModularForm.add_toFun KatzModularForm.sub_toFun KatzModularForm.c₄_toFun KatzModularForm.qExpansion_zero KatzModularForm.mk.sizeOf_spec TateCurve.tateTorsionPoint_zero_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero"
p2m_attr_erase "simp" "TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one"
p2m_attr_erase "simp" "WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx"
p2m_attr_erase "simp" "WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual"
p2m_attr_erase "simp" "AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff AlgebraicCurve.abelJacobiDiv_single AlgebraicCurve.AnalyticCoord.mk.injEq AlgebraicCurve.Cell.mk.sizeOf_spec AlgebraicCurve.RadialRegion.mk.sizeOf_spec AlgebraicCurve.RadialRegion.mk.injEq AlgebraicCurve.CellDissection.mk.sizeOf_spec AlgebraicCurve.Cell.mk.injEq AlgebraicCurve.CellDissection.mk.injEq AlgebraicCurve.AnalyticCoord.mk.sizeOf_spec"

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

noncomputable section

p2m_open "AlgebraicCurve ModularCurve P2MW.S_ModularCurve_reductionQExpModL_gamma1_heckeOperatorOneBar_eq_zero_of_ne.ModularCurve IntermediateField CongruenceSubgroup"

namespace ModularCurve
p2m_export "ModularCurve" "heckeOperatorOneBar heckeOperatorOneBar_apply heckeAlphaOneBar coe_heckeAlphaOneBar HeckeBetaOneDefined heckeBetaOneBar coe_heckeBetaOneBar HeckeInputsOneAlong heckeOperatorOneAlong heckeOperatorOneAlong_eq heckeOperatorOneAlong_of_not qExpFunctionFieldC intFormRatiosC_subset qExpFunctionFieldC_mono JOne qExpand qExpand_injective coeffMap coeffEmb laurentBaseChange coeffEmb_mem_laurentBaseChange IsLaurentPlaceReduction laurentIntegralPrincipalDivisors LaurentPrincipalGeneratedByIntegral coe_laurentReductionDegZero IsPlaceReductionQExpModL ReductionInputsQExpModL placeReductionQExpModL isPlaceReductionQExpModL_placeReductionQExpModL reductionQExpModL reductionQExpModL_mk reductionQExpModL_of_not coeffMap_jqModC jqModC_ne_zero_of_nontrivial jqModC coeffMap_qExpand finrankAlong_inclusion_qExpFunctionFieldC_residueField_eq_of_not_dvd exists_transcendental_and_reductionInputsQExpModL_gammaH_of_not_dvd exists_constantReduction_pic0Map_eq_reductionQExpModL JOneES.exists_transcendental_finiteDimensional_laurentBaseChange exists_transcendental_finiteDimensional_qExpFunctionFieldC_residueField jqModC_mem_intFormRatiosC"
namespace RedHeckeNe1
p2m_open "ModularCurve"

section ResidueAlgClosed

open IsLocalRing Polynomial

variable {L : Type*} [Field L] (A : ValuationSubring L)

theorem isAlgClosed_residueField [IsAlgClosed L] : IsAlgClosed (ResidueField A) := by
  refine IsAlgClosed.of_exists_root _ (fun f hf_monic hf_irr => ?_)
  have hf_lifts : f ∈ lifts (residue A) := by
    rw [lifts_iff_coeff_lifts]
    exact fun n => residue_surjective (f.coeff n)
  obtain ⟨g, hg_map, -, hg_monic⟩ := lifts_and_degree_eq_and_monic hf_lifts hf_monic
  have hgL_deg : (g.map (algebraMap A L)).degree ≠ 0 := by
    rw [hg_monic.degree_map]
    intro h0
    have hg_nat : g.natDegree = 0 := natDegree_eq_zero_iff_degree_le_zero.mpr (le_of_eq h0)
    have hf_deg : f.natDegree = 0 := by
      rw [← hg_map, hg_monic.natDegree_map]
      exact hg_nat
    have hf1 : f = 1 := (hf_monic.natDegree_eq_zero).mp hf_deg
    exact hf_irr.not_isUnit (by rw [hf1]; exact isUnit_one)
  obtain ⟨α, hα⟩ := IsAlgClosed.exists_root _ hgL_deg
  have hα_int : IsIntegral A α := by
    refine ⟨g, hg_monic, ?_⟩
    rwa [IsRoot.def, eval_map] at hα
  obtain ⟨a, ha⟩ := IsIntegrallyClosed.isIntegral_iff.mp hα_int
  refine ⟨residue A a, ?_⟩
  have hga : g.eval a = 0 := by
    have : algebraMap A L (g.eval a) = 0 := by
      have hcomm : algebraMap A L (g.eval a) = (g.map (algebraMap A L)).eval α := by
        rw [← ha, eval_map, eval₂_hom]
      rw [hcomm]
      exact hα
    exact (map_eq_zero_iff _ Subtype.coe_injective).mp this
  have : f.eval (residue A a) = residue A (g.eval a) := by
    rw [← hg_map, eval_map, eval₂_hom]
  rw [this, hga, map_zero]

end ResidueAlgClosed

section Generic

variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']

theorem pullbackAlong_apply_eq_ord [HasPrincipalDivisors K F'] (φ : F →ₐ[K] F')
    (hφ : φ.toRingHom.IsIntegral) {f : F} {D : Divisor K F} (hD : ∀ v, D v = v.ord f)
    (w : Place K F') : Divisor.pullbackAlong φ hφ D w = w.ord (φ f) := by
  letI := algebraAlong φ
  haveI := isScalarTower_along φ
  haveI := isIntegral_along φ hφ
  exact Divisor.pullback_apply_eq_ord hD w

theorem degZero_of_principal [HasPrincipalDivisors K F] {D : Divisor K F}
    (hD : D ∈ Divisor.principal (K := K) (F := F)) : D ∈ Divisor.degZero (K := K) (F := F) := by
  obtain ⟨f, hf0, hDf⟩ := hD
  obtain ⟨D', hD', hdeg⟩ := HasPrincipalDivisors.exists_divisor (K := K) f hf0
  have hDD' : D = D' := Finsupp.ext fun v => by rw [hDf v, hD' v]
  rw [Divisor.mem_degZero, hDD', hdeg]

theorem int_eq_zero_of_forall_dvd {a : ℤ} (h : ∀ n : ℕ, n ≠ 0 → (n : ℤ) ∣ a) : a = 0 :=
  Int.eq_zero_of_dvd_of_natAbs_lt_natAbs (h (a.natAbs + 1) (Nat.succ_ne_zero _))
    (by rw [Int.natAbs_natCast]; exact Nat.lt_succ_self _)

theorem agree_of_agree_on_generators {X : Type*} (S : Set (Divisor K F))
    (hgen : Divisor.principal (K := K) (F := F) ≤ AddSubgroup.closure S)
    (Φ₁ Φ₂ : Divisor K F →+ (X →₀ ℤ)) (hagree : ∀ D ∈ S, Φ₁ D = Φ₂ D)
    (hdiv : ∀ n : ℕ, n ≠ 0 → ∀ x : Pic0 K F, ∃ y : Pic0 K F, n • y = x)
    {D : Divisor K F} (hD : D ∈ Divisor.degZero (K := K) (F := F)) : Φ₁ D = Φ₂ D := by
  classical
  set δ : Divisor K F →+ (X →₀ ℤ) := Φ₁ - Φ₂ with hδ
  have hδapp : ∀ E, δ E = Φ₁ E - Φ₂ E := fun E => rfl
  have hδprin : ∀ E ∈ Divisor.principal (K := K) (F := F), δ E = 0 := by
    intro E hE
    have hE' := hgen hE
    clear hE
    induction hE' using AddSubgroup.closure_induction with
    | mem E hE => rw [hδapp, hagree E hE, sub_self]
    | zero => exact map_zero δ
    | add E E' _ _ hE hE' => rw [map_add, hE, hE', add_zero]
    | neg E _ hE => rw [map_neg, hE, neg_zero]
  suffices h0 : δ D = 0 by rwa [hδapp, sub_eq_zero] at h0
  ext Q
  rw [Finsupp.zero_apply]
  refine int_eq_zero_of_forall_dvd fun n hn => ?_
  obtain ⟨y, hy⟩ := hdiv n hn (Pic0.mk ⟨D, hD⟩)
  obtain ⟨E, rfl⟩ := Pic0.mk_surjective y
  have hmem : ((⟨D, hD⟩ : Divisor.degZero (K := K) (F := F)) - n • E :
      Divisor.degZero (K := K) (F := F)) ∈
        (Divisor.principal (K := K) (F := F)).addSubgroupOf (Divisor.degZero (K := K) (F := F)) := by
    rw [← QuotientAddGroup.eq_iff_sub_mem, QuotientAddGroup.mk_nsmul]
    exact hy.symm
  rw [AddSubgroup.mem_addSubgroupOf, AddSubgroupClass.coe_sub, AddSubgroupClass.coe_nsmul] at hmem
  have h0 := hδprin _ hmem
  rw [map_sub, map_nsmul, sub_eq_zero] at h0
  refine ⟨δ (E : Divisor K F) Q, ?_⟩
  rw [h0, Finsupp.smul_apply, nsmul_eq_mul]

end Generic

section ConstRed

variable {L : Type*} [Field L] {A : ValuationSubring L}
variable {F : Type*} [Field F] [Algebra L F]
variable {Fbar : Type*} [Field Fbar] [Algebra (IsLocalRing.ResidueField A) Fbar]

theorem exists_principal_mapDomain_eq [HasPrincipalDivisors L F] (R : ConstantReduction A F Fbar)
    {X : Divisor (IsLocalRing.ResidueField A) Fbar}
    (hX : X ∈ Divisor.principal (K := IsLocalRing.ResidueField A) (F := Fbar)) :
    ∃ D ∈ Divisor.principal (K := L) (F := F), Finsupp.mapDomain R.placeMap D = X := by
  obtain ⟨fb, hfb0, hXf⟩ := hX
  obtain ⟨u, hu⟩ := R.residue_surjective fb
  have hres : R.residue u ≠ 0 := by rw [hu]; exact hfb0
  have hu0 : (u : F) ≠ 0 := by
    intro h0
    apply hres
    have : u = 0 := Subtype.ext h0
    rw [this, map_zero]
  obtain ⟨D, hD, -⟩ := HasPrincipalDivisors.exists_divisor (K := L) (u : F) hu0
  refine ⟨D, ⟨(u : F), hu0, hD⟩, ?_⟩
  ext Q
  rw [R.mapDomain_placeMap u hres D hD Q, hXf Q, hu]

end ConstRed

section Groups

open scoped MatrixGroups

variable (M ℓ : ℕ)

theorem T_mem_Gamma1 : ModularGroup.T ∈ Gamma1 M := by
  simp [Gamma1_mem, ModularGroup.T]

theorem T_mem_inf : ModularGroup.T ∈ Gamma1 M ⊓ Gamma0 (M * ℓ) := by
  refine ⟨T_mem_Gamma1 M, ?_⟩
  simp [Gamma0_mem, ModularGroup.T]

scoped instance finiteIndex_inf [NeZero M] [NeZero ℓ] : (Gamma1 M ⊓ Gamma0 (M * ℓ)).FiniteIndex := by
  haveI : NeZero (M * ℓ) := ⟨mul_ne_zero (NeZero.ne M) (NeZero.ne ℓ)⟩
  infer_instance

def kerH : Subgroup (ZMod (M * ℓ))ˣ := (ZMod.unitsMap (dvd_mul_right M ℓ)).ker

theorem gammaH_kerH_eq [NeZero M] [NeZero ℓ] :
    CohCarrier.GammaH (M * ℓ) (kerH M ℓ) = Gamma1 M ⊓ Gamma0 (M * ℓ) := by
  haveI : NeZero (M * ℓ) := ⟨mul_ne_zero (NeZero.ne M) (NeZero.ne ℓ)⟩
  ext A
  rw [CohCarrier.mem_GammaH_iff, Subgroup.mem_inf]

  have hd : ∀ hA : A ∈ Gamma0 (M * ℓ),
      ((ZMod.unitsMap (dvd_mul_right M ℓ) (CohCarrier.gamma0Units (M * ℓ) ⟨A, hA⟩) : (ZMod M)ˣ) :
        ZMod M) = ((A 1 1 : ℤ) : ZMod M) := by
    intro hA
    rw [ZMod.unitsMap_def, Units.coe_map, MonoidHom.coe_coe, CohCarrier.val_gamma0Units]
    simp only [Gamma0Map, MonoidHom.coe_mk, OneHom.coe_mk]
    rw [ZMod.castHom_apply, ZMod.cast_intCast (dvd_mul_right M ℓ)]
  have hc : ∀ hA : A ∈ Gamma0 (M * ℓ), ((A 1 0 : ℤ) : ZMod M) = 0 := by
    intro hA
    have h := Gamma0_mem.mp hA
    have := congrArg (ZMod.castHom (dvd_mul_right M ℓ) (ZMod M)) h
    rwa [map_intCast, map_zero] at this
  constructor
  · rintro ⟨hA0, hAH⟩
    have h11 : ((A 1 1 : ℤ) : ZMod M) = 1 := by
      have h1 : ZMod.unitsMap (dvd_mul_right M ℓ) (CohCarrier.gamma0Units (M * ℓ) ⟨A, hA0⟩) = 1 := by
        have hAH' : CohCarrier.gamma0Units (M * ℓ) ⟨A, hA0⟩ ∈ (ZMod.unitsMap (dvd_mul_right M ℓ)).ker := hAH
        exact (MonoidHom.mem_ker).mp hAH'
      have := congrArg (fun u : (ZMod M)ˣ => (u : ZMod M)) h1
      simp only [Units.val_one] at this
      rwa [hd hA0] at this
    have h10 : ((A 1 0 : ℤ) : ZMod M) = 0 := hc hA0
    refine ⟨?_, hA0⟩
    rw [Gamma1_mem]
    refine ⟨?_, h11, h10⟩
    have hda := CohCarrier.Gamma0_d_mul_a M ⟨A, Gamma0_mem.mpr h10⟩
    simp only at hda
    rw [h11, one_mul] at hda
    exact hda
  · rintro ⟨hA1, hA0⟩
    refine ⟨hA0, ?_⟩
    show CohCarrier.gamma0Units (M * ℓ) ⟨A, hA0⟩ ∈ (ZMod.unitsMap (dvd_mul_right M ℓ)).ker
    rw [MonoidHom.mem_ker]
    ext
    rw [hd hA0, Units.val_one]
    exact ((Gamma1_mem M A).mp hA1).2.1

end Groups

section Modular

set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 6400000

variable (M ℓ : ℕ) [NeZero M] [NeZero ℓ]
variable (P : ValuationSubring (AlgebraicClosure ℚ))
variable {k : Type*} [Field k] (π : P →+* k)

local notation "ℚ̄" => AlgebraicClosure ℚ
local notation "Γ₁" => CongruenceSubgroup.Gamma1 M
local notation "Γ'" => CongruenceSubgroup.Gamma1 M ⊓ CongruenceSubgroup.Gamma0 (M * ℓ)
local notation "Fq" => laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma1 M))
local notation "Eq" => laurentBaseChange (AlgebraicClosure ℚ)
  (qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma1 M ⊓ CongruenceSubgroup.Gamma0 (M * ℓ)))

theorem inf_le : (Γ' : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)) ≤ Γ₁ := inf_le_left

def αq : Fq →ₐ[ℚ̄] Eq := heckeAlphaOneBar (AlgebraicClosure ℚ) M ℓ

def βq : Fq →ₐ[ℚ̄] Eq := heckeBetaOneBar (AlgebraicClosure ℚ) M ℓ

theorem coe_αq (x : Fq) : (αq M ℓ x : LaurentSeries ℚ̄) = (x : LaurentSeries ℚ̄) :=
  coe_heckeAlphaOneBar M ℓ x

theorem coe_βq (h0 : HeckeBetaOneDefined M ℓ) (x : Fq) :
    (βq M ℓ x : LaurentSeries ℚ̄) = qExpand ℚ̄ ℓ (x : LaurentSeries ℚ̄) :=
  coe_heckeBetaOneBar M ℓ h0 x

variable (k) in

def αb : qExpFunctionFieldC k Γ₁ →ₐ[k] qExpFunctionFieldC k Γ' :=
  IntermediateField.inclusion (qExpFunctionFieldC_mono k (inf_le M ℓ))

theorem coe_αb (x : qExpFunctionFieldC k Γ₁) : (αb M ℓ k x : LaurentSeries k) = (x : LaurentSeries k) :=
  IntermediateField.coe_inclusion _ x

variable {M ℓ P}

theorem gen_alpha
    {rF : Place ℚ̄ Fq → Place k (qExpFunctionFieldC k Γ₁)}
    (hrF : IsLaurentPlaceReduction P π (qExpFunctionFieldC ℚ Γ₁) (qExpFunctionFieldC k Γ₁) rF)
    {rE : Place ℚ̄ Eq → Place k (qExpFunctionFieldC k Γ')}
    (hrE : IsLaurentPlaceReduction P π (qExpFunctionFieldC ℚ Γ') (qExpFunctionFieldC k Γ') rE)
    (hα : (αq M ℓ).toRingHom.IsIntegral)
    [HasPrincipalDivisors ℚ̄ Eq] [HasPrincipalDivisors k (qExpFunctionFieldC k Γ')]
    (hαb : (αb M ℓ k).toRingHom.IsIntegral)
    (D : Divisor ℚ̄ Fq)
    (hDS : D ∈ laurentIntegralPrincipalDivisors P π (qExpFunctionFieldC ℚ Γ₁) (qExpFunctionFieldC k Γ₁)) :
    Finsupp.mapDomain rE (Divisor.pullbackAlong (αq M ℓ) hα D) =
      Divisor.pullbackAlong (αb M ℓ k) hαb (Finsupp.mapDomain rF D) := by
  obtain ⟨y, hy, hyk, hne, hD⟩ := hDS
  have hy' : coeffMap P.subtype y ∈ Eq := by
    have := (αq M ℓ ⟨coeffMap P.subtype y, hy⟩).2
    rwa [coe_αq] at this
  have hαy : αq M ℓ ⟨coeffMap P.subtype y, hy⟩ = ⟨coeffMap P.subtype y, hy'⟩ :=
    Subtype.ext (coe_αq M ℓ _)
  have hD' : ∀ W, Divisor.pullbackAlong (αq M ℓ) hα D W =
      W.ord (⟨coeffMap P.subtype y, hy'⟩ : Eq) := fun W => by
    rw [pullbackAlong_apply_eq_ord _ hα hD W, hαy]
  have hyk' : coeffMap π y ∈ qExpFunctionFieldC k Γ' := qExpFunctionFieldC_mono k (inf_le M ℓ) hyk
  have E1 : ∀ Q, Finsupp.mapDomain rE (Divisor.pullbackAlong (αq M ℓ) hα D) Q =
      Q.ord (⟨coeffMap π y, hyk'⟩ : qExpFunctionFieldC k Γ') :=
    hrE.2 y hy' hyk' hne _ hD'
  have E2 : ∀ Q, Finsupp.mapDomain rF D Q = Q.ord (⟨coeffMap π y, hyk⟩ : qExpFunctionFieldC k Γ₁) :=
    hrF.2 y hy hyk hne D hD
  have Rt : ∀ Y, Divisor.pullbackAlong (αb M ℓ k) hαb (Finsupp.mapDomain rF D) Y =
      Y.ord (αb M ℓ k ⟨coeffMap π y, hyk⟩) :=
    pullbackAlong_apply_eq_ord _ hαb E2
  have hel : αb M ℓ k ⟨coeffMap π y, hyk⟩ = ⟨coeffMap π y, hyk'⟩ := Subtype.ext (coe_αb M ℓ _)
  ext Y
  rw [E1, Rt, hel]

theorem gen_beta (h0 : HeckeBetaOneDefined M ℓ)
    {rF : Place ℚ̄ Fq → Place k (qExpFunctionFieldC k Γ₁)}
    (hrF : IsLaurentPlaceReduction P π (qExpFunctionFieldC ℚ Γ₁) (qExpFunctionFieldC k Γ₁) rF)
    {rE : Place ℚ̄ Eq → Place k (qExpFunctionFieldC k Γ')}
    (hrE : IsLaurentPlaceReduction P π (qExpFunctionFieldC ℚ Γ') (qExpFunctionFieldC k Γ') rE)
    (hβ : (βq M ℓ).toRingHom.IsIntegral)
    [HasPrincipalDivisors ℚ̄ Eq] [HasPrincipalDivisors k (qExpFunctionFieldC k Γ')]
    (βb : qExpFunctionFieldC k Γ₁ →ₐ[k] qExpFunctionFieldC k Γ')
    (hβbcoe : ∀ x : qExpFunctionFieldC k Γ₁, (βb x : LaurentSeries k) = qExpand k ℓ (x : LaurentSeries k))
    (hβb : βb.toRingHom.IsIntegral)
    (D : Divisor ℚ̄ Fq)
    (hDS : D ∈ laurentIntegralPrincipalDivisors P π (qExpFunctionFieldC ℚ Γ₁) (qExpFunctionFieldC k Γ₁)) :
    Finsupp.mapDomain rE (Divisor.pullbackAlong (βq M ℓ) hβ D) =
      Divisor.pullbackAlong βb hβb (Finsupp.mapDomain rF D) := by
  obtain ⟨y, hy, hyk, hne, hD⟩ := hDS
  set y₂ : LaurentSeries P := qExpand P ℓ y with hy₂def
  have hcoe : coeffMap P.subtype y₂ = qExpand ℚ̄ ℓ (coeffMap P.subtype y) := coeffMap_qExpand _ ℓ y
  have hy' : coeffMap P.subtype y₂ ∈ Eq := by
    have := (βq M ℓ ⟨coeffMap P.subtype y, hy⟩).2
    rwa [coe_βq M ℓ h0, ← hcoe] at this
  have hβy : βq M ℓ ⟨coeffMap P.subtype y, hy⟩ = ⟨coeffMap P.subtype y₂, hy'⟩ :=
    Subtype.ext (by rw [coe_βq M ℓ h0]; exact hcoe.symm)
  have hD' : ∀ W, Divisor.pullbackAlong (βq M ℓ) hβ D W =
      W.ord (⟨coeffMap P.subtype y₂, hy'⟩ : Eq) := fun W => by
    rw [pullbackAlong_apply_eq_ord _ hβ hD W, hβy]
  have hcoek : coeffMap π y₂ = qExpand k ℓ (coeffMap π y) := coeffMap_qExpand _ ℓ y
  have hyk' : coeffMap π y₂ ∈ qExpFunctionFieldC k Γ' := by
    rw [hcoek]
    have := (βb ⟨coeffMap π y, hyk⟩).2
    rwa [hβbcoe] at this
  have hne' : coeffMap π y₂ ≠ 0 := by
    rw [hcoek]
    intro h
    exact hne (qExpand_injective ℓ (by rw [h, map_zero]))
  have E1 : ∀ Q, Finsupp.mapDomain rE (Divisor.pullbackAlong (βq M ℓ) hβ D) Q =
      Q.ord (⟨coeffMap π y₂, hyk'⟩ : qExpFunctionFieldC k Γ') :=
    hrE.2 y₂ hy' hyk' hne' _ hD'
  have E2 : ∀ Q, Finsupp.mapDomain rF D Q = Q.ord (⟨coeffMap π y, hyk⟩ : qExpFunctionFieldC k Γ₁) :=
    hrF.2 y hy hyk hne D hD
  have Rt : ∀ Y, Divisor.pullbackAlong βb hβb (Finsupp.mapDomain rF D) Y =
      Y.ord (βb ⟨coeffMap π y, hyk⟩) :=
    pullbackAlong_apply_eq_ord _ hβb E2
  have hel : βb ⟨coeffMap π y, hyk⟩ = ⟨coeffMap π y₂, hyk'⟩ :=
    Subtype.ext (by rw [hβbcoe]; exact hcoek.symm)
  ext Y
  rw [E1, Rt, hel]

theorem not_const [IsAlgClosed k]
    {rF : Place ℚ̄ Fq → Place k (qExpFunctionFieldC k Γ₁)}
    (hrF : IsLaurentPlaceReduction P π (qExpFunctionFieldC ℚ Γ₁) (qExpFunctionFieldC k Γ₁) rF)
    [HasPrincipalDivisors ℚ̄ Fq] (h1F : ∀ v : Place ℚ̄ Fq, v.deg = 1)
    (x : qExpFunctionFieldC k Γ₁) (hx : (x : LaurentSeries k) = jqModC k) (htr : Transcendental k x)
    [FiniteDimensional (IntermediateField.adjoin k ({x} : Set (qExpFunctionFieldC k Γ₁)))
      (qExpFunctionFieldC k Γ₁)] :
    ∀ v : Place ℚ̄ Fq, ∃ v' : Place ℚ̄ Fq, rF v' ≠ rF v := by
  intro v
  by_contra hall
  push Not at hall

  obtain ⟨Q, hQ⟩ : ∃ Q : Place k (qExpFunctionFieldC k Γ₁), Q.ord x ≠ 0 := by
    by_contra hall'
    push Not at hall'
    obtain ⟨c, hc⟩ := Place.mem_range_algebraMap_of_forall_ord_eq_zero_of_isAlgClosed x htr hall'
    exact htr (hc ▸ isAlgebraic_algebraMap c)

  have hjq : jqModC ℚ ∈ qExpFunctionFieldC ℚ Γ₁ :=
    intFormRatiosC_subset ℚ _ (jqModC_mem_intFormRatiosC ℚ _)
  have hjmem : coeffMap P.subtype (jqModC P) ∈ Fq := by
    rw [coeffMap_jqModC]
    have : coeffEmb (AlgebraicClosure ℚ) (jqModC ℚ) = jqModC ℚ̄ := coeffMap_jqModC _
    rw [← this]
    exact coeffEmb_mem_laurentBaseChange _ hjq
  have hjk : coeffMap π (jqModC P) ∈ qExpFunctionFieldC k Γ₁ := by
    rw [coeffMap_jqModC]; exact hx ▸ x.2
  have hjne : coeffMap π (jqModC P) ≠ 0 := by
    rw [coeffMap_jqModC]; exact jqModC_ne_zero_of_nontrivial k
  have hj0 : (⟨coeffMap P.subtype (jqModC P), hjmem⟩ : Fq) ≠ 0 := by
    intro h0
    have hval : coeffMap P.subtype (jqModC P) = 0 := by
      simpa using congrArg Subtype.val h0
    rw [coeffMap_jqModC] at hval
    exact jqModC_ne_zero_of_nontrivial ℚ̄ hval
  obtain ⟨Dj, hDj, hDj0⟩ := HasPrincipalDivisors.exists_divisor (K := ℚ̄) _ hj0
  have E2 : ∀ Q', Finsupp.mapDomain rF Dj Q' =
      Q'.ord (⟨coeffMap π (jqModC P), hjk⟩ : qExpFunctionFieldC k Γ₁) :=
    hrF.2 (jqModC P) hjmem hjk hjne Dj hDj
  have hjx : (⟨coeffMap π (jqModC P), hjk⟩ : qExpFunctionFieldC k Γ₁) = x := by
    apply Subtype.ext
    show coeffMap π (jqModC P) = (x : LaurentSeries k)
    rw [coeffMap_jqModC]; exact hx.symm
  have hconst : ∀ D : Divisor ℚ̄ Fq,
      Finsupp.mapDomain rF D = Finsupp.single (rF v) (Divisor.degree D) := by
    intro D
    induction D using Finsupp.induction with
    | zero => simp
    | single_add R n D _ _ ih =>
      rw [Finsupp.mapDomain_add, ih, Finsupp.mapDomain_single, hall R, map_add,
        Divisor.degree_single, h1F, Nat.cast_one, mul_one, ← Finsupp.single_add, add_comm]
  have := E2 Q
  rw [hconst Dj, hDj0, Finsupp.single_zero, Finsupp.zero_apply, hjx] at this
  exact hQ this.symm

end Modular

section Main

set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 12800000

variable (M : ℕ) [NeZero M] {p : ℕ} [Fact p.Prime]
variable (P : ValuationSubring (AlgebraicClosure ℚ))
variable (ℓ : ℕ) [Fact ℓ.Prime]

local notation "ℚ̄" => AlgebraicClosure ℚ
local notation "kP" => IsLocalRing.ResidueField P
local notation "Γ₁" => CongruenceSubgroup.Gamma1 M
local notation "Γ'" => CongruenceSubgroup.Gamma1 M ⊓ CongruenceSubgroup.Gamma0 (M * ℓ)
local notation "Fq" => laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma1 M))
local notation "Eq" => laurentBaseChange (AlgebraicClosure ℚ)
  (qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma1 M ⊓ CongruenceSubgroup.Gamma0 (M * ℓ)))
local notation "Fb" => qExpFunctionFieldC (IsLocalRing.ResidueField P) (CongruenceSubgroup.Gamma1 M)
local notation "Eb" => qExpFunctionFieldC (IsLocalRing.ResidueField P)
  (CongruenceSubgroup.Gamma1 M ⊓ CongruenceSubgroup.Gamma0 (M * ℓ))

theorem main (hpM : ¬ p ∣ M) (hP : P.LiesOverPrime p) (hℓ : ℓ ≠ p) (z : Pic0 ℚ̄ Fq)
    (hz : reductionQExpModL P Γ₁ z = 0) :
    haveI : NeZero ℓ := ⟨(Fact.out : ℓ.Prime).ne_zero⟩
    reductionQExpModL P Γ₁ (heckeOperatorOneAlong (AlgebraicClosure ℚ) M ℓ z) = 0 := by
  haveI hℓ0 : NeZero ℓ := ⟨(Fact.out : ℓ.Prime).ne_zero⟩
  haveI : NeZero (M * ℓ) := ⟨mul_ne_zero (NeZero.ne M) (NeZero.ne ℓ)⟩
  classical

  by_cases hF : ReductionInputsQExpModL P Γ₁
  swap
  · rw [reductionQExpModL_of_not hF, AddMonoidHom.zero_apply]
  by_cases hT : HeckeInputsOneAlong (AlgebraicClosure ℚ) M ℓ
  swap
  · rw [heckeOperatorOneAlong_of_not hT, AddMonoidHom.zero_apply]; exact map_zero _
  obtain ⟨h0, hα, hβ, hPE, hfinα, hFIβ, hNα⟩ := hT
  haveI := hPE

  have hpMℓ : ¬ p ∣ M * ℓ := by
    intro hdvd
    rcases (Nat.Prime.dvd_mul (Fact.out : p.Prime)).mp hdvd with h1 | h2
    · exact hpM h1
    · exact hℓ ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) (Fact.out : ℓ.Prime)).mp h2).symm

  have hE : ReductionInputsQExpModL P Γ' := by
    have h := (ModularCurve.exists_transcendental_and_reductionInputsQExpModL_gammaH_of_not_dvd (M * ℓ)
      (kerH M ℓ) hpMℓ P hP).2
    rwa [gammaH_kerH_eq M ℓ] at h

  set rF := placeReductionQExpModL hF with hrFdef
  have hrF : IsPlaceReductionQExpModL P Γ₁ rF := isPlaceReductionQExpModL_placeReductionQExpModL hF
  have hgenF : LaurentPrincipalGeneratedByIntegral P (IsLocalRing.residue P) (qExpFunctionFieldC ℚ Γ₁) Fb :=
    hF.choose_spec.2
  set rE := placeReductionQExpModL hE with hrEdef
  have hrE : IsPlaceReductionQExpModL P Γ' rE := isPlaceReductionQExpModL_placeReductionQExpModL hE

  obtain ⟨RF, hRFr, -, -⟩ :=
    ModularCurve.exists_constantReduction_pic0Map_eq_reductionQExpModL Γ₁ (T_mem_Gamma1 M) P hF
  obtain ⟨RE, hREr, -, -⟩ :=
    ModularCurve.exists_constantReduction_pic0Map_eq_reductionQExpModL Γ' (T_mem_inf M ℓ) P hE

  obtain ⟨hfinαb, hsepαb, hdegEq, βb, hβbcoe, hfinβb⟩ :=
    ModularCurve.finrankAlong_inclusion_qExpFunctionFieldC_residueField_eq_of_not_dvd M p ℓ hpMℓ P hP
  have hfinαb' : FiniteAlong kP (αb M ℓ kP) := hfinαb
  have hsepαb' : SeparableAlong kP (αb M ℓ kP) := hsepαb
  have hαb : (αb M ℓ kP).toRingHom.IsIntegral := by
    letI := algebraAlong (αb M ℓ kP)
    haveI : Module.Finite Fb Eb := hfinαb'
    haveI : Algebra.IsIntegral Fb Eb := Algebra.IsIntegral.of_finite Fb Eb
    exact fun x => Algebra.IsIntegral.isIntegral x
  have hβb : βb.toRingHom.IsIntegral := by
    letI := algebraAlong βb
    haveI : Module.Finite Fb Eb := hfinβb
    haveI : Algebra.IsIntegral Fb Eb := Algebra.IsIntegral.of_finite Fb Eb
    exact fun x => Algebra.IsIntegral.isIntegral x

  haveI hPE' : HasPrincipalDivisors ℚ̄ Eq := hPE
  have hα' : (αq M ℓ).toRingHom.IsIntegral := hα
  have hβ' : (βq M ℓ).toRingHom.IsIntegral := hβ
  have hfinα' : FiniteAlong ℚ̄ (αq M ℓ) := hfinα
  have hFIβ' : FundamentalIdentityAlong ℚ̄ (βq M ℓ) hβ' := hFIβ
  have hNα' : NormFormulaAlong ℚ̄ (αq M ℓ) hfinα' := hNα

  haveI : IsAlgClosed kP := isAlgClosed_residueField P
  obtain ⟨xF, hxF, hfdF⟩ := ModularCurve.JOneES.exists_transcendental_finiteDimensional_laurentBaseChange
    (AlgebraicClosure ℚ) Γ₁ (T_mem_Gamma1 M)
  obtain ⟨xE, hxE, hfdE⟩ := ModularCurve.JOneES.exists_transcendental_finiteDimensional_laurentBaseChange
    (AlgebraicClosure ℚ) Γ' (T_mem_inf M ℓ)
  obtain ⟨xb, hxbj, hxb, hfdb, -⟩ :=
    ModularCurve.exists_transcendental_finiteDimensional_qExpFunctionFieldC_residueField
      (AlgebraicClosure ℚ) P Γ₁ (T_mem_Gamma1 M)
  obtain ⟨xe, hxej, hxe, hfde, -⟩ :=
    ModularCurve.exists_transcendental_finiteDimensional_qExpFunctionFieldC_residueField
      (AlgebraicClosure ℚ) P Γ' (T_mem_inf M ℓ)
  haveI hcF : IsCurveOver ℚ̄ Fq := isCurveOver_of_transcendental_of_perfectField hxF hfdF
  haveI hcE : IsCurveOver ℚ̄ Eq := isCurveOver_of_transcendental_of_perfectField hxE hfdE
  haveI hcb : IsCurveOver kP Fb := isCurveOver_of_transcendental_of_perfectField hxb hfdb
  haveI hce : IsCurveOver kP Eb := isCurveOver_of_transcendental_of_perfectField hxe hfde
  haveI : HasPrincipalDivisors ℚ̄ Fq := IsCurveOver.hasPrincipalDivisors
  haveI : HasPrincipalDivisors kP Fb := IsCurveOver.hasPrincipalDivisors
  haveI : HasPrincipalDivisors kP Eb := IsCurveOver.hasPrincipalDivisors
  have h1F : ∀ v : Place ℚ̄ Fq, v.deg = 1 := fun v => IsCurveOver.deg_eq_one_of_isAlgClosed (K := ℚ̄) v
  have h1E : ∀ v : Place ℚ̄ Eq, v.deg = 1 := fun v => IsCurveOver.deg_eq_one_of_isAlgClosed (K := ℚ̄) v
  have h1b : ∀ v : Place kP Fb, v.deg = 1 := fun v => IsCurveOver.deg_eq_one_of_isAlgClosed (K := kP) v
  have h1e : ∀ v : Place kP Eb, v.deg = 1 := fun v => IsCurveOver.deg_eq_one_of_isAlgClosed (K := kP) v

  haveI : CharZero Fq := charZero_of_injective_algebraMap (algebraMap ℚ̄ Fq).injective
  have hFIα : FundamentalIdentityAlong ℚ̄ (αq M ℓ) hα' :=
    fundamentalIdentityAlong _ hα' hfinα' (separableAlong_of_charZero _ hα')
  have hFIαb : FundamentalIdentityAlong kP (αb M ℓ kP) hαb :=
    fundamentalIdentityAlong _ hαb hfinαb' hsepαb'

  have hdiv : ∀ n : ℕ, n ≠ 0 → ∀ x : Pic0 ℚ̄ Fq, ∃ y : Pic0 ℚ̄ Fq, n • y = x :=
    fun n hn x => Pic0.exists_nsmul_eq ℚ̄ Fq ⟨xF, hxF, hfdF⟩ n hn x

  have hcompatα : ∀ D : Divisor ℚ̄ Fq, D ∈ Divisor.degZero (K := ℚ̄) (F := Fq) →
      Finsupp.mapDomain rE (Divisor.pullbackAlong (αq M ℓ) hα' D) =
        Divisor.pullbackAlong (αb M ℓ kP) hαb (Finsupp.mapDomain rF D) := by
    intro D hD
    have := agree_of_agree_on_generators
      (laurentIntegralPrincipalDivisors P (IsLocalRing.residue P) (qExpFunctionFieldC ℚ Γ₁) Fb) hgenF
      ((Finsupp.mapDomain.addMonoidHom rE).comp (Divisor.pullbackAlong (αq M ℓ) hα'))
      ((Divisor.pullbackAlong (αb M ℓ kP) hαb).comp (Finsupp.mapDomain.addMonoidHom rF))
      (fun D hDS => by
        simpa only [AddMonoidHom.coe_comp, Function.comp_apply, Finsupp.mapDomain.addMonoidHom_apply]
          using gen_alpha (IsLocalRing.residue P) hrF hrE hα' hαb D hDS)
      hdiv hD
    simpa only [AddMonoidHom.coe_comp, Function.comp_apply, Finsupp.mapDomain.addMonoidHom_apply]
      using this
  have hcompatβ : ∀ D : Divisor ℚ̄ Fq, D ∈ Divisor.degZero (K := ℚ̄) (F := Fq) →
      Finsupp.mapDomain rE (Divisor.pullbackAlong (βq M ℓ) hβ' D) =
        Divisor.pullbackAlong βb hβb (Finsupp.mapDomain rF D) := by
    intro D hD
    have := agree_of_agree_on_generators
      (laurentIntegralPrincipalDivisors P (IsLocalRing.residue P) (qExpFunctionFieldC ℚ Γ₁) Fb) hgenF
      ((Finsupp.mapDomain.addMonoidHom rE).comp (Divisor.pullbackAlong (βq M ℓ) hβ'))
      ((Divisor.pullbackAlong βb hβb).comp (Finsupp.mapDomain.addMonoidHom rF))
      (fun D hDS => by
        simpa only [AddMonoidHom.coe_comp, Function.comp_apply, Finsupp.mapDomain.addMonoidHom_apply]
          using gen_beta (IsLocalRing.residue P) h0 hrF hrE hβ' βb hβbcoe hβb D hDS)
      hdiv hD
    simpa only [AddMonoidHom.coe_comp, Function.comp_apply, Finsupp.mapDomain.addMonoidHom_apply]
      using this

  have hdegα : ∀ v : Place ℚ̄ Fq,
      Divisor.degree (Divisor.pullbackAlong (αq M ℓ) hα' (Finsupp.single v 1)) ≤
        Divisor.degree (Divisor.pullbackAlong (αb M ℓ kP) hαb (Finsupp.single (rF v) 1)) := by
    intro v
    rw [Divisor.degree_pullbackAlong _ hα' hFIα, Divisor.degree_pullbackAlong _ hαb hFIαb,
      Divisor.degree_single, Divisor.degree_single, h1F, h1b]
    have hdeg' : finrankAlong kP (αb M ℓ kP) = finrankAlong ℚ̄ (αq M ℓ) := hdegEq
    rw [hdeg']
  have hnc : ∀ v : Place ℚ̄ Fq, ∃ v' : Place ℚ̄ Fq, rF v' ≠ rF v := by
    haveI := hfdb
    exact not_const (IsLocalRing.residue P) hrF h1F xb hxbj hxb
  obtain ⟨-, -, hpushα⟩ :=
    Divisor.mapDomain_pullbackAlong_eq_and_restrictAlong_eq_of_degZero
      (αq M ℓ) hα' (αb M ℓ kP) hαb rF rE h1F h1E h1b h1e hcompatα hdegα hnc

  obtain ⟨D₀, rfl⟩ := Pic0.mk_surjective z
  have hz' : Finsupp.mapDomain rF (D₀ : Divisor ℚ̄ Fq) ∈
      Divisor.principal (K := kP) (F := Fb) := by
    rw [reductionQExpModL_mk hF] at hz
    have h := (QuotientAddGroup.eq_zero_iff _).mp hz
    rwa [AddSubgroup.mem_addSubgroupOf, coe_laurentReductionDegZero] at h

  obtain ⟨D₁, hD₁, hD₁eq⟩ := exists_principal_mapDomain_eq RF hz'
  rw [hRFr] at hD₁eq
  have hD₁0 : D₁ ∈ Divisor.degZero (K := ℚ̄) (F := Fq) := degZero_of_principal hD₁
  have hD'0 : (D₀ : Divisor ℚ̄ Fq) - D₁ ∈ Divisor.degZero (K := ℚ̄) (F := Fq) :=
    sub_mem D₀.2 hD₁0
  have hrD' : Finsupp.mapDomain rF ((D₀ : Divisor ℚ̄ Fq) - D₁) = 0 := by
    rw [Finsupp.mapDomain_sub, hD₁eq, sub_self]
  have step1 : Finsupp.mapDomain rE (Divisor.pullbackAlong (βq M ℓ) hβ' ((D₀ : Divisor ℚ̄ Fq) - D₁)) = 0 := by
    rw [hcompatβ _ hD'0, hrD', map_zero]
  have step2 : Finsupp.mapDomain rF
      (Divisor.correspondence (βq M ℓ) (αq M ℓ) hβ' hα' ((D₀ : Divisor ℚ̄ Fq) - D₁)) = 0 := by
    rw [Divisor.correspondence_apply, hpushα, step1, map_zero]

  rw [heckeOperatorOneAlong_eq h0 hα hβ hFIβ hfinα hNα]
  change reductionQExpModL P Γ₁
    (Pic0.mk (Pic0.degZeroCorrespondence (βq M ℓ) (αq M ℓ) hβ' hα' hFIβ' D₀)) = 0
  rw [reductionQExpModL_mk hF]
  refine (QuotientAddGroup.eq_zero_iff _).mpr ?_
  rw [AddSubgroup.mem_addSubgroupOf, coe_laurentReductionDegZero, Pic0.coe_degZeroCorrespondence]
  have hsplit : (D₀ : Divisor ℚ̄ Fq) = ((D₀ : Divisor ℚ̄ Fq) - D₁) + D₁ := (sub_add_cancel _ _).symm
  rw [hsplit, map_add, Finsupp.mapDomain_add, step2, zero_add]
  exact hrF.mapDomain_mem_principal hgenF
    (Divisor.correspondence_mem_principal (βq M ℓ) (αq M ℓ) hβ' hα' hfinα' hNα' hD₁)

end Main

end ModularCurve.RedHeckeNe1
p2m_reactivate "P2MW.S_ModularCurve_reductionQExpModL_gamma1_heckeOperatorOneBar_eq_zero_of_ne.ModularCurve P2MW.S_ModularCurve_reductionQExpModL_gamma1_heckeOperatorOneBar_eq_zero_of_ne.ModularCurve.RedHeckeNe1"
p2m_reactivate "P2MW.S_ModularCurve_reductionQExpModL_gamma1_heckeOperatorOneBar_eq_zero_of_ne.ModularCurve"

end
p2m_reactivate "P2MW.S_ModularCurve_reductionQExpModL_gamma1_heckeOperatorOneBar_eq_zero_of_ne.ModularCurve P2MW.S_ModularCurve_reductionQExpModL_gamma1_heckeOperatorOneBar_eq_zero_of_ne.ModularCurve.RedHeckeNe1"

open ModularCurve.RedHeckeNe1 in
set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 12800000 in
theorem solution
    (M p : ℕ) [NeZero M] [Fact p.Prime] (hpM : ¬ p ∣ M)
    (P : ValuationSubring (AlgebraicClosure ℚ)) (hP : P.LiesOverPrime p)
    (ℓ : Nat.Primes) (hℓ : (ℓ : ℕ) ≠ p) (z : ModularCurve.JOne M)
    (hz : ModularCurve.reductionQExpModL P (CongruenceSubgroup.Gamma1 M) z = 0) :
    ModularCurve.reductionQExpModL P (CongruenceSubgroup.Gamma1 M)
      (ModularCurve.heckeOperatorOneBar M ℓ z) = 0 := by
  haveI : Fact (ℓ : ℕ).Prime := ⟨ℓ.2⟩
  rw [ModularCurve.heckeOperatorOneBar_apply]
  exact main M P (ℓ : ℕ) hpM hP hℓ z hz

end S_ModularCurve_reductionQExpModL_gamma1_heckeOperatorOneBar_eq_zero_of_ne
end P2MW
export P2MW.S_ModularCurve_reductionQExpModL_gamma1_heckeOperatorOneBar_eq_zero_of_ne (solution)
