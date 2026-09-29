-- Prove2me | solution 1 for ModularCurve.twist_correspondence_heckeU_eq_genDiffModL_U_of_atkinLehnerPinAlong_of_ne
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/39a9dabe-c908-5aed-867a-5e431b00b15e

import Mathlib
import Definitions.Def_ModularCurve_XHDifferentialsModL
import Definitions.Def_AlgebraicCurve_RegularDifferentials
import Definitions.Def_ModularCurve_XH
import Definitions.Def_AlgebraicCurve_Repartitions
import Theorems.Thm_ModularCurve_diffQExp_qExpFunctionFieldC_injective
import Theorems.Thm_ModularCurve_IsInfReductionMap_comp_baseChange_genU_eq_genDiffModL_comp_of_ne
import Theorems.Thm_CuspForm_exists_GammaH_coe_eq_alSlash_of_forall_unitsMap_atkinLehnerFactor_eq_one
import Theorems.Thm_CuspForm_stableD
import Theorems.Thm_CuspForm_stableU
import Theorems.Thm_ModularFormClass_qExpansion_heckeU_eq_heckeU
import Theorems.Thm_ModularForm_heckeU_alSlash_eq_alSlash_sum_slash_transpose_of_dvd_div
import Theorems.Thm_ModularCurve_IsInfReductionMap_exists_smul_correspondence_heckeAlphaModLH_heckeBetaModLH_apply_eq_of_ne
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_twist_correspondence_heckeU_eq_genDiffModL_U_of_atkinLehnerPinAlong_of_ne
p2m_attr_erase "instance" "AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.instIsElliptic_tateBase ModularCurve.instIsElliptic_tateLaurent ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.KatzGamma0Form.instModule ModularCurve.KatzGamma0Form.instZero ModularCurve.KatzLevelPForm.instSMul ModularCurve.KatzGamma0Form.instAdd ModularCurve.KatzLevelPForm.instAddCommGroup ModularCurve.KatzGamma0Form.instNeg ModularCurve.KatzGamma0Form.instAddCommGroup ModularCurve.KatzLevelPForm.instAdd ModularCurve.KatzLevelPForm.instSub ModularCurve.KatzLevelPForm.instNeg ModularCurve.KatzGamma0Form.instSMul ModularCurve.KatzGamma0Form.instSub ModularCurve.KatzLevelPForm.instZero ModularCurve.KatzLevelPForm.instModule KatzModularForm.instAddCommGroup KatzModularForm.instSub KatzModularForm.instZero KatzModularForm.instModule KatzModularForm.instAdd KatzModularForm.instNeg KatzModularForm.instSMul WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly"
p2m_attr_erase "instance" "ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois FLT.HyperbolicMeasure.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatIntUpperHalfPlaneVolume_definitions FLT.HyperbolicMeasure.instIsOpenPosMeasureUpperHalfPlaneVolume_definitions FLT.Gamma0FundamentalSet.instContinuousConstSMulSpecialLinearGroupFinOfNatNatIntUpperHalfPlane_definitions FLT.L2ProductionInstance.isFiniteMeasure_gamma0 FLT.L2ProductionInstance.countable_SL2Z FLT.L2ProductionInstance.countable_quotient FLT.L2ProductionInstance.nontrivial_gamma0L2 Ihara.instGroupIharaAmalgam CuspForm.heckeAlgebra.instCommRing CuspForm.heckeAlgebra.instIsMulCommutative CuspForm.heckeAlgebra.instIsAddTorsionFree HeckeEis.instFiniteIndexHeckeUpper ModularCurve.Period.parabolicHoms_int_moduleFinite ModularCurve.Period.instGroupFG_SL2Z ModularCurve.Period.instIsNoetherian_addHom_int ModularCurve.Period.instGroupFG_Gamma0 AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions"
p2m_attr_erase "instance" "IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion CohCarrier.GammaHLower_finiteIndex"
p2m_attr_erase "simp" "WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd"
p2m_attr_erase "simp" "ModularCurve.eisensteinSystem_of_not_dvd AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.cuspData_yP ModularCurve.qTwistAlgHom_apply ModularCurve.cuspData_yQ ModularCurve.cuspData_xP ModularCurve.cuspData_xQ ModularCurve.val_cyclZeta ModularCurve.cuspShift_one ModularCurve.cuspShift_zero ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single"
p2m_attr_erase "simp" "ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.LevelPData.mk.sizeOf_spec ModularCurve.KatzLevelPForm.neg_toFun ModularCurve.LevelP.coe_swapW ModularCurve.KatzLevelPForm.swap_swap KatzModularForm.pullbackLevelP_toFun ModularCurve.LevelPData.swap_xQ KatzModularForm.pullbackLevelP_zero ModularCurve.LevelPData.map_yP ModularCurve.KatzLevelPForm.swap_neg ModularCurve.KatzGamma0Form.toKatzLevelPForm_sub ModularCurve.KatzLevelPForm.swap_add KatzModularForm.swap_pullbackLevelP ModularCurve.KatzGamma0Form.toKatzLevelPForm_add ModularCurve.KatzLevelPForm.swap_smul ModularCurve.LevelPData.map_yQ ModularCurve.KatzLevelPForm.mk.injEq ModularCurve.KatzLevelPForm.zero_toFun KatzModularForm.pullbackLevelP_smul ModularCurve.LevelPData.swap_xP ModularCurve.KatzGamma0Form.toKatzLevelPForm_mul ModularCurve.KatzGamma0Form.toKatzLevelPForm_neg ModularCurve.LevelPData.variableChange_xQ KatzModularForm.pullbackGamma0_toKatzLevelPForm ModularCurve.KatzLevelPForm.mk.sizeOf_spec ModularCurve.KatzLevelPForm.swap_zero ModularCurve.LevelP.coe_unipotentU ModularCurve.KatzLevelPForm.mul_toFun ModularCurve.LevelPData.variableChange_yP ModularCurve.LevelPData.mk.injEq ModularCurve.KatzLevelPForm.sub_toFun ModularCurve.LevelPData.variableChange_xP ModularCurve.KatzLevelPForm.smul_toFun ModularCurve.LevelPData.swap_yP ModularCurve.LevelPData.map_xP ModularCurve.LevelPData.swap_swap ModularCurve.LevelPData.swap_yQ ModularCurve.KatzGamma0Form.toKatzLevelPForm_zero"
p2m_attr_erase "simp" "ModularCurve.KatzGamma0Form.mk.injEq ModularCurve.KatzLevelPForm.swap_toFun KatzModularForm.pullbackLevelP_add ModularCurve.KatzGamma0Form.mk.sizeOf_spec ModularCurve.LevelPData.variableChange_yQ ModularCurve.KatzLevelPForm.swap_sub ModularCurve.KatzGamma0Form.toKatzLevelPForm_smul ModularCurve.LevelPData.map_xQ ModularCurve.KatzLevelPForm.add_toFun KatzModularForm.c₆_toFun KatzModularForm.neg_toFun KatzModularForm.mul_toFun KatzModularForm.qExpansion_neg KatzModularForm.discr_toFun KatzModularForm.qExpansion_sub KatzModularForm.qExpansion_add KatzModularForm.qExpansion_mul KatzModularForm.zero_toFun KatzModularForm.mk.injEq KatzModularForm.qExpansion_smul KatzModularForm.smul_toFun KatzModularForm.add_toFun KatzModularForm.sub_toFun KatzModularForm.c₄_toFun KatzModularForm.qExpansion_zero KatzModularForm.mk.sizeOf_spec TateCurve.tateTorsionPoint_zero_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ"
p2m_attr_erase "simp" "TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one"
p2m_attr_erase "simp" "WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty WeierstrassCurve.map_veluU"
p2m_attr_erase "simp" "WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply ModularCurve.ProjectiveLine.map_mk WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁"
p2m_attr_erase "simp" "PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_cuspidalDivisor₀ ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen"
p2m_attr_erase "simp" "ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeAlphaHBar ModularCurve.coe_heckeBetaHBarOf AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap ModularCurve.baseAut_x1ArithFrobC_apply ModularCurve.coe_qExpCoeffRingAut_apply ModularCurve.qExpCoeffSemilinearAutHom_apply ModularCurve.baseAut_x1x0ArithFrobC_apply ModularCurve.baseAut_qExpArithFrobC_apply ModularCurve.baseAut_qExpCoeffSemilinearAut ModularCurve.toRingAut_qExpCoeffSemilinearAut ModularCurve.toRingAut_coeffSemilinearAut ModularCurve.baseAut_arithFrobC_apply ModularCurve.coe_coeffRingAut_apply ModularCurve.baseAut_coeffSemilinearAut FreyPackage.ModMCarrier.coe_rescaleLin_apply FLT.TruncatedDomainPartition.unipotentDiagonalSum_zero"
p2m_attr_erase "simp" "Ihara.wConj_coe Ihara.wConj_symm_coe Ihara.coe_iota1 Ihara.coe_iota1SL Ihara.iota1Mat_apply_one_zero Ihara.iota1Mat_apply_zero_zero Ihara.iota1Mat_apply_zero_one Ihara.iota1Mat_apply_one_one Ihara.coe_iota0 Ihara.iharaEdge_one Ihara.pairFamily_zero Ihara.iharaEdge_zero Ihara.pairFamily_one Ihara.coe_amalgamToGamma0Away Ihara.coe_vertexZero Ihara.coe_slToAway CuspForm.Gamma1Hecke.redMatrix_apply_one_one CuspForm.Gamma1Hecke.redMatrix_apply_one_zero CuspForm.Gamma1Hecke.lift_infty CuspForm.Gamma1Hecke.heckeRep_infty CuspForm.Gamma1Hecke.heckeRep_coe CuspForm.Gamma1Hecke.wt_infty CuspForm.Gamma1Hecke.redMatrix_apply_zero_one CuspForm.coe_slashLinOfMemGamma0_apply CuspForm.Gamma1Hecke.wt_coe CuspForm.Gamma1Hecke.lift_coe CuspForm.Gamma1Hecke.redMatrix_apply_zero_zero CuspForm.coe_heckeTOne CuspForm.coe_heckeTLinOne_apply CuspForm.coe_slashOfMemGamma0 CuspForm.PeterssonCoset.mapGL_apply ModularCurve.dualHeckeRep_apply_apply ModularCurve.coe_segmentPath ModularCurve.cuspHeckeAeval_heckeGen ModularCurve.coe_periodLatticeRestrict_apply CuspForm.heckeAlgebra.coe_U CuspForm.heckeAlgebra.coe_T ModularForm.coe_heckeTLin_apply CuspForm.coe_heckeULin_apply CuspForm.coe_heckeTLin_apply"
p2m_attr_erase "simp" "ModularForm.coe_heckeULin_apply ModularCurve.Period.IsEquivariantPrimitive.periodHom_apply ModularCurve.Period.IsEquivariantPrimitive.period_one HeckeEis.heckeConjMat_apply_one_one HeckeEis.coe_heckeConjSL HeckeEis.mem_heckeUpperSL HeckeEis.resHom_apply HeckeEis.heckeConjMat_apply_zero_one HeckeEis.coe_transferAux HeckeEis.coe_heckeConj HeckeEis.alphaMat_apply_one_one HeckeEis.heckeConjMat_apply_one_zero HeckeEis.alphaMat_apply_zero_one HeckeEis.pullbackHom_apply HeckeEis.alphaMat_apply_one_zero HeckeEis.alphaMat_apply_zero_zero HeckeEis.heckeConjMat_apply_zero_zero ModularCurve.LevelN.coe_jGen AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule CohCarrier.uMat_apply_10 CohCarrier.rightQuotEquivOfDvd_apply CohCarrier.uMat_apply_11 CohCarrier.uMat_apply_01 CohCarrier.uMat_apply_00 CohCarrier.coe_uElt"

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 6400000

open scoped MatrixGroups ModularForm TensorProduct
open CongruenceSubgroup CohCarrier

noncomputable section

namespace TwistLawU

theorem T_mem_GammaH (N : ℕ) (H' : Subgroup (ZMod N)ˣ) : ModularGroup.T ∈ GammaH N H' := by
  rw [mem_GammaH_iff]
  have h0 : ModularGroup.T ∈ Gamma0 N := by
    rw [Gamma0_mem]
    simp [ModularGroup.coe_T]
  refine ⟨h0, ?_⟩
  have : gamma0Units N ⟨ModularGroup.T, h0⟩ = 1 := by
    ext
    rw [val_gamma0Units, Units.val_one]
    show (((ModularGroup.T : SL(2, ℤ)) 1 1 : ℤ) : ZMod N) = 1
    simp [ModularGroup.coe_T]
  rw [this]
  exact one_mem H'

theorem one_mem_strictPeriods_GammaH (N : ℕ) (H' : Subgroup (ZMod N)ˣ) :
    (1 : ℝ) ∈ ((GammaH N H' : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
  rw [Subgroup.mem_strictPeriods_iff]
  refine ⟨ModularGroup.T, T_mem_GammaH N H', ?_⟩
  refine Units.ext ?_
  rw [Matrix.GeneralLinearGroup.upperRightHom_apply]
  show ((ModularGroup.T : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).map (Int.castRingHom ℝ) = !![(1 : ℝ), 1; 0, 1]
  rw [ModularGroup.coe_T]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

scoped instance GammaH_finiteIndex' (N : ℕ) [NeZero N] (H' : Subgroup (ZMod N)ˣ) : (GammaH N H').FiniteIndex :=
  CuspForm.GammaH_finiteIndex N H'

theorem map_heckeU {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (ℓ : ℕ) (P : PowerSeries R) :
    (PowerSeries.heckeU ℓ P).map φ = PowerSeries.heckeU ℓ (P.map φ) := by
  ext n
  simp [PowerSeries.coeff_map, PowerSeries.heckeU]

theorem ofPowerSeries_heckeU {K : Type*} [Field K] (ℓ : ℕ) [NeZero ℓ] (P : PowerSeries K) :
    HahnSeries.ofPowerSeries ℤ K (PowerSeries.heckeU ℓ P) =
      ModularCurve.qDecimate K ℓ (HahnSeries.ofPowerSeries ℤ K P) := by
  ext n
  rw [ModularCurve.coeff_qDecimate, PowerSeries.coeff_coe, PowerSeries.coeff_coe]
  by_cases hn : n < 0
  · have : (ℓ : ℤ) * n < 0 ∨ (ℓ : ℤ) * n = 0 := by
      rcases Nat.eq_zero_or_pos ℓ with h | h
      · exact absurd h (NeZero.ne ℓ)
      · left; exact mul_neg_of_pos_of_neg (by exact_mod_cast h) hn
    rw [if_pos hn]
    rcases this with h | h
    · rw [if_pos h]
    · exfalso
      rcases mul_eq_zero.mp h with h' | h'
      · exact NeZero.ne ℓ (by exact_mod_cast h')
      · omega
  · rw [if_neg hn]
    have hn' : 0 ≤ n := le_of_not_gt hn
    have hln : ¬ (ℓ : ℤ) * n < 0 := not_lt.mpr (mul_nonneg (by positivity) hn')
    rw [if_neg hln]
    simp only [PowerSeries.heckeU, LinearMap.coe_mk, AddHom.coe_mk, PowerSeries.coeff_mk]
    congr 1
    have : ((ℓ : ℤ) * n).natAbs = ℓ * n.natAbs := by
      rw [Int.natAbs_mul, Int.natAbs_natCast]
    rw [this]

theorem intSeriesC_heckeU (K : Type*) [Field K] (ℓ : ℕ) [NeZero ℓ] (P : PowerSeries ℤ) :
    ModularCurve.intSeriesC K (PowerSeries.heckeU ℓ P) = ModularCurve.qDecimate K ℓ (ModularCurve.intSeriesC K P) := by
  rw [ModularCurve.intSeriesC, ModularCurve.intSeriesC, map_heckeU, ofPowerSeries_heckeU]

def alDatumAtP {p M : ℕ} (hp : p.Prime) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M) : ModularForm.AtkinLehnerDatum M p :=
  have hcop : Nat.Coprime p (M / p) := by
    rw [Nat.Prime.coprime_iff_not_dvd hp]
    intro h
    apply hpM2
    obtain ⟨c, hc⟩ := h
    refine ⟨c, ?_⟩
    calc M = p * (M / p) := (Nat.mul_div_cancel' hpM).symm
      _ = p ^ 2 * c := by rw [hc]; ring
  { R := M / p
    hM := (Nat.mul_div_cancel' hpM).symm
    a := Nat.gcdA p (M / p)
    b := -Nat.gcdB p (M / p)
    bezout := by
      have h := Nat.gcd_eq_gcd_ab p (M / p)
      rw [Nat.Coprime.gcd_eq_one hcop] at h
      simp only [Nat.cast_one] at h
      linear_combination -h }

section Integral

variable {M : ℕ} [NeZero M] {H : Subgroup (ZMod M)ˣ} {k : ℤ} {p : ℕ}

theorem exists_isIntegralQExp_of_mem (Wp : ModularForm.AtkinLehnerDatum M p) {f : CuspForm (GammaH M H) k}
    (hf : f ∈ CuspForm.twoCuspIntegralSet M H k p (⊥ : Subring ℂ)) :
    ∃ pf : PowerSeries ℤ, ModularCurve.IsIntegralQExp ⇑f pf := by
  have h : ∀ n : ℕ, ∃ z : ℤ, (z : ℂ) = ModularFormClass.qCoeff (⇑f) n := by
    intro n
    have := (hf 1 (Subring.one_mem _) Wp n).1
    rw [Module.End.one_apply] at this
    exact Subring.mem_bot.mp this
  choose z hz using h
  refine ⟨PowerSeries.mk z, ?_⟩
  rw [ModularCurve.isIntegralQExp_iff]
  intro n
  rw [PowerSeries.coeff_mk]
  exact hz n

end Integral

section Diamond

def X (M q j : ℕ) : GL (Fin 2) ℝ :=
  ModularForm.heckeDiagMatrix q *
    (Matrix.SpecialLinearGroup.mapGL ℝ (Matrix.SpecialLinearGroup.transpose (ModularGroup.T ^ (M * j))) :
      GL (Fin 2) ℝ)

theorem coe_transpose_T_pow (c : ℕ) :
    ((Matrix.SpecialLinearGroup.transpose (ModularGroup.T ^ c) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) =
      !![1, 0; (c : ℤ), 1] := by
  rw [Matrix.SpecialLinearGroup.coe_transpose, ← zpow_natCast, ModularGroup.coe_T_zpow]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem S_mul_T_zpow_neg_mul_S_inv_eq_transpose (c : ℕ) :
    ModularGroup.S * ModularGroup.T ^ (-((c : ℕ) : ℤ)) * ModularGroup.S⁻¹ =
      Matrix.SpecialLinearGroup.transpose (ModularGroup.T ^ c) := by
  refine Subtype.ext ?_
  rw [coe_transpose_T_pow, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.coe_inv, ModularGroup.coe_S, ModularGroup.coe_T_zpow]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.adjugate_fin_two]

lemma mapGL_coe_eq (s : SL(2, ℤ)) :
    ((Matrix.SpecialLinearGroup.mapGL ℝ s : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)
      = (s : Matrix (Fin 2) (Fin 2) ℤ).map (Int.castRingHom ℝ) := rfl

theorem val_X {M q : ℕ} (hq : q ≠ 0) (J : ℤ) (j : ℕ) (hJ : (j : ℤ) = J) :
    ((X M q j : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
      (!![(q : ℤ), 0; (M : ℤ) * J, 1] : Matrix (Fin 2) (Fin 2) ℤ).map (Int.castRingHom ℝ) := by
  rw [X, Units.val_mul, ModularForm.val_heckeDiagMatrix hq, mapGL_coe_eq, coe_transpose_T_pow]
  ext r c
  fin_cases r <;> fin_cases c <;> simp [Matrix.mul_apply, Fin.sum_univ_two, ← hJ]

variable {M q M1 : ℕ} [NeZero M]

def dmat (q M1 A B c0 D j n : ℤ) : Matrix (Fin 2) (Fin 2) ℤ :=
  !![A - (q*M1)*(A*(A*j + c0) - q*n)*B, q*B;
     M1*(j*A + c0 - (A*(A*j + c0) - q*n)*((q*M1)*j*B + D)), (q*M1)*j*B + D]

theorem det_dmat {q M1 A B c0 D j n : ℤ} (hdet : A * D - B * (q * M1 * c0) = 1) :
    (dmat q M1 A B c0 D j n).det = 1 := by
  rw [dmat, Matrix.det_fin_two_of]
  linear_combination hdet

theorem dmat_10 {q M1 A B c0 D j n : ℤ} (hdet : A * D - B * (q * M1 * c0) = 1) :
    dmat q M1 A B c0 D j n 1 0 =
      (q * M1) * (-A^2*B*M1*j^2 - 2*A*B*M1*c0*j - B*M1*c0^2 + B*M1*j*n*q + D*n) := by
  have : dmat q M1 A B c0 D j n 1 0 = M1*(j*A + c0 - (A*(A*j + c0) - q*n)*((q*M1)*j*B + D)) := by
    simp [dmat]
  rw [this]
  linear_combination (M1 * (-A*j - c0)) * hdet

theorem dmat_11 (q M1 A B c0 D j n : ℤ) : dmat q M1 A B c0 D j n 1 1 = (q*M1)*j*B + D := by
  simp [dmat]

theorem X_mul_sigma_int (q M1 A B c0 D j n : ℤ) :
    !![q, 0; (q*M1)*j, 1] * !![A, B; (q*M1)*c0, D] =
      dmat q M1 A B c0 D j n * !![q, 0; (q*M1)*(A*(A*j + c0) - q*n), 1] := by
  rw [dmat]
  simp only [Matrix.mul_fin_two]
  refine Matrix.ext fun r c => ?_
  fin_cases r <;> fin_cases c
  · simp only [Fin.zero_eta, Fin.mk_one, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.head_fin_const]
    ring
  · simp only [Fin.zero_eta, Fin.mk_one, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.head_fin_const]
    ring
  · simp only [Fin.zero_eta, Fin.mk_one, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.head_fin_const]
    ring
  · simp only [Fin.zero_eta, Fin.mk_one, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.head_fin_const]
    ring

theorem sum_range_eq_sum_zmod {α : Type*} [AddCommMonoid α] {q : ℕ} [NeZero q] (G : ℕ → α) :
    ∑ j ∈ Finset.range q, G j = ∑ x : ZMod q, G x.val := by
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne q)
  subst hn
  exact (Fin.sum_univ_eq_sum_range G (n + 1)).symm

theorem sum_range_comp_perm {α : Type*} [AddCommMonoid α] {q : ℕ} [NeZero q] (e : ZMod q ≃ ZMod q)
    (G : ℕ → α) :
    ∑ j ∈ Finset.range q, G (e (j : ZMod q)).val = ∑ i ∈ Finset.range q, G i := by
  rw [sum_range_eq_sum_zmod, sum_range_eq_sum_zmod]
  have : (fun x : ZMod q => G (e ((x.val : ℕ) : ZMod q)).val) = fun x => G (e x).val := by
    funext x
    rw [ZMod.natCast_zmod_val]
  rw [this]
  exact Equiv.sum_comp e (fun x => G x.val)

theorem sum_slash_X_slash_mapGL {H : Subgroup (ZMod M)ˣ} (σ : Gamma0 M) {q : ℕ} (hq : q ≠ 0) (hqM : q ∣ M)
    (k : ℤ) (F : UpperHalfPlane → ℂ) (hF : ∀ γ ∈ (GammaH M H : Subgroup (GL (Fin 2) ℝ)), F ∣[k] γ = F) :
    (∑ j ∈ Finset.range q, F ∣[k] X M q j) ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ (σ : SL(2, ℤ)) : GL (Fin 2) ℝ) =
      ∑ j ∈ Finset.range q, (F ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ (σ : SL(2, ℤ)) : GL (Fin 2) ℝ)) ∣[k] X M q j := by
  haveI : NeZero q := ⟨hq⟩
  obtain ⟨M1, hM1⟩ := hqM

  set A : ℤ := (σ : SL(2, ℤ)) 0 0 with hA
  set B : ℤ := (σ : SL(2, ℤ)) 0 1 with hB
  set C : ℤ := (σ : SL(2, ℤ)) 1 0 with hC
  set D : ℤ := (σ : SL(2, ℤ)) 1 1 with hD
  have hCM : (M : ℤ) ∣ C := by
    have := Gamma0_mem.mp σ.2
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp this
  obtain ⟨c0, hc0⟩ := hCM
  have hdetσ : A * D - B * C = 1 := by
    have := Matrix.SpecialLinearGroup.det_coe (σ : SL(2, ℤ))
    rw [Matrix.det_fin_two] at this
    linear_combination this
  have hdet : A * D - B * (q * M1 * c0) = 1 := by
    rw [hc0, hM1] at hdetσ
    push_cast at hdetσ
    linear_combination hdetσ
  have hqM1 : ((q : ℤ) * M1 : ℤ) = (M : ℤ) := by rw [hM1]; push_cast; ring
  have hσmat : ((σ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) = !![A, B; (q * M1) * c0, D] := by
    ext r c
    fin_cases r <;> fin_cases c
    · rfl
    · rfl
    · show C = _
      simp only [Fin.zero_eta, Fin.mk_one, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, Matrix.head_fin_const]
      rw [hc0, hM1]; push_cast; ring
    · rfl

  have hAq : (A : ZMod q) * (D : ZMod q) = 1 := by
    have h := congrArg (fun z : ℤ => (z : ZMod q)) hdet
    simp only [Int.cast_sub, Int.cast_mul, Int.cast_natCast, ZMod.natCast_self, zero_mul, mul_zero,
      sub_zero, Int.cast_one] at h
    exact h
  set uA : (ZMod q)ˣ := Units.mkOfMulEqOne _ _ hAq with huA
  set uA2 : (ZMod q)ˣ := uA * uA with huA2
  set e : ZMod q ≃ ZMod q := (uA2.mulLeft : ZMod q ≃ ZMod q).trans (Equiv.addRight ((A : ZMod q) * c0)) with he
  have he_apply : ∀ x : ZMod q, e x = (A : ZMod q) * A * x + A * c0 := fun x => rfl

  have hterm : ∀ j : ℕ, (F ∣[k] X M q j) ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ (σ : SL(2, ℤ)) : GL (Fin 2) ℝ) =
      (F ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ (σ : SL(2, ℤ)) : GL (Fin 2) ℝ)) ∣[k] X M q (e (j : ZMod q)).val := by
    intro j
    have hcong : (((e (j : ZMod q)).val : ℤ) : ZMod q) = ((A * (A * j + c0) : ℤ) : ZMod q) := by
      push_cast
      rw [ZMod.natCast_zmod_val, he_apply]
      ring
    obtain ⟨n, hn⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mp hcong
    have hj' : (((e (j : ZMod q)).val : ℕ) : ℤ) = A * (A * j + c0) - q * n := by
      linear_combination -hn

    set γ' : SL(2, ℤ) := ⟨dmat q M1 A B c0 D j n, det_dmat hdet⟩ with hγ'
    have hγ'0 : γ' ∈ Gamma0 M := by
      rw [Gamma0_mem]
      show ((dmat (q : ℤ) M1 A B c0 D j n 1 0 : ℤ) : ZMod M) = 0
      rw [dmat_10 hdet, hqM1]
      push_cast
      rw [ZMod.natCast_self, zero_mul]
    have hunits : gamma0Units M ⟨γ', hγ'0⟩ = gamma0Units M σ := by
      ext
      rw [val_gamma0Units, val_gamma0Units]
      show ((dmat (q : ℤ) M1 A B c0 D j n 1 1 : ℤ) : ZMod M) = ((D : ℤ) : ZMod M)
      rw [dmat_11, hqM1]
      push_cast
      rw [ZMod.natCast_self, zero_mul, zero_mul, zero_add]

    have hGL : X M q j * (Matrix.SpecialLinearGroup.mapGL ℝ (σ : SL(2, ℤ)) : GL (Fin 2) ℝ) =
        (Matrix.SpecialLinearGroup.mapGL ℝ γ' : GL (Fin 2) ℝ) * X M q (e (j : ZMod q)).val := by
      refine Units.ext ?_
      rw [Units.val_mul, Units.val_mul, val_X hq (j : ℤ) j rfl, val_X hq _ _ hj', mapGL_coe_eq, mapGL_coe_eq,
        hσmat]
      have hZ := X_mul_sigma_int (q : ℤ) M1 A B c0 D j n
      have hR := congrArg (Int.castRingHom ℝ).mapMatrix hZ
      rw [map_mul, map_mul] at hR
      simp only [RingHom.mapMatrix_apply] at hR
      have hMq : ((M : ℤ)) = (q : ℤ) * M1 := by rw [hM1]; push_cast; ring
      rw [hMq]
      exact hR
    rw [← SlashAction.slash_mul, hGL, SlashAction.slash_mul]
    have h1 := CuspForm.slash_mapGL_eq_of_gamma0Units_eq k hF ⟨γ', hγ'0⟩ σ hunits 1
    rw [mul_one, mul_one] at h1
    exact congrArg (fun G : UpperHalfPlane → ℂ => G ∣[k] X M q (e (j : ZMod q)).val) h1
  rw [SlashAction.sum_slash]
  simp_rw [hterm]
  exact sum_range_comp_perm e
    (fun i => (F ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ (σ : SL(2, ℤ)) : GL (Fin 2) ℝ)) ∣[k] X M q i)

end Diamond

section Pin

variable {p M : ℕ} [Fact p.Prime] [NeZero M] {H : Subgroup (ZMod M)ˣ} (hpM : p ∣ M)

theorem smul_slash_mapGL (k : ℤ) (c : ℂ) (γ : SL(2, ℤ)) (F : UpperHalfPlane → ℂ) :
    (c • F) ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ γ : GL (Fin 2) ℝ) =
      c • F ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ γ : GL (Fin 2) ℝ) :=
  ModularForm.SL_smul_slash k γ F c

theorem pin_transposeU (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (Wd : ModularForm.AtkinLehnerDatum M (M / p)) (e : (ZMod M)ˣ)
    {q : ℕ} (hq : q.Prime) (hqM : q ∣ M) (hqN : q ∣ M / p)
    (f g : CuspForm (GammaH M H) 2) (D' : ℕ)
    (hgf : ⇑g = (D' : ℂ) • ∑ j ∈ Finset.range q, (⇑f) ∣[(2 : ℤ)] X M q j)
    (D : ℕ) (pfW : PowerSeries ↥(integralClosure ℤ ℂ))
    (hpfW : pfW.map (algebraMap ↥(integralClosure ℤ ℂ) ℂ) =
      UpperHalfPlane.qExpansion 1 ((D : ℂ) • ModularForm.alSlash Wd 2 ⇑(CuspForm.diamondLinH 2 e f))) :
    (PowerSeries.C (D' : ↥(integralClosure ℤ ℂ)) * PowerSeries.heckeU q pfW).map
        (algebraMap ↥(integralClosure ℤ ℂ) ℂ) =
      UpperHalfPlane.qExpansion 1 ((D : ℂ) • ModularForm.alSlash Wd 2 ⇑(CuspForm.diamondLinH 2 e g)) := by
  have hq0 : q ≠ 0 := hq.ne_zero
  have hStD := CuspForm.stableD M H 2
  have hStU := CuspForm.stableU M H 2 hq hqM
  have hΓ1 := one_mem_strictPeriods_GammaH M H

  have h1 : ⇑(CuspForm.diamondLinH 2 e g) =
      (D' : ℂ) • ∑ j ∈ Finset.range q, ⇑(CuspForm.diamondLinH 2 e f) ∣[(2 : ℤ)] X M q j := by
    rw [CuspForm.coe_diamondLinH_apply 2 hStD e g, hgf, CuspForm.coe_diamondLinH_apply 2 hStD e f,
      smul_slash_mapGL,
      sum_slash_X_slash_mapGL (CuspForm.gammaLift M e) hq0 hqM 2 ⇑f
        (fun γ hγ => SlashInvariantFormClass.slash_action_eq f γ hγ)]

  have h2 : ModularForm.alSlash Wd 2 ⇑(CuspForm.diamondLinH 2 e g) =
      (D' : ℂ) • ModularForm.heckeU 2 q (ModularForm.alSlash Wd 2 ⇑(CuspForm.diamondLinH 2 e f)) := by
    rw [h1, ModularForm.alSlash_smul]
    congr 1

    rw [ModularForm.heckeU_alSlash_eq_alSlash_sum_slash_transpose_of_dvd_div M p hpM hpM2 H hHp Wd q hq hqN 2
      ⇑(CuspForm.diamondLinH 2 e f)
      (fun γ hγ => SlashInvariantFormClass.slash_action_eq (CuspForm.diamondLinH 2 e f) γ hγ)]
    simp only [X, S_mul_T_zpow_neg_mul_S_inv_eq_transpose]

  obtain ⟨Xf, hXf⟩ := CuspForm.exists_GammaH_coe_eq_alSlash_of_forall_unitsMap_atkinLehnerFactor_eq_one Wd H hHp 2
    (CuspForm.diamondLinH 2 e f)
  have h3 : (D : ℂ) • ModularForm.alSlash Wd 2 ⇑(CuspForm.diamondLinH 2 e f) = ⇑((D : ℂ) • Xf) := by
    rw [CuspForm.IsGLPos.coe_smul, hXf]
  have h4 : (D : ℂ) • ModularForm.alSlash Wd 2 ⇑(CuspForm.diamondLinH 2 e g) =
      (D' : ℂ) • ⇑(CuspForm.heckeULinH 2 q ((D : ℂ) • Xf)) := by
    rw [h2, smul_comm, ← ModularForm.heckeU_smul, h3, CuspForm.coe_heckeULinH_apply 2 hStU]
  rw [h4, ModularForm.qExpansion_smul one_pos hΓ1 (D' : ℂ) (CuspForm.heckeULinH 2 q ((D : ℂ) • Xf)),
    CuspForm.coe_heckeULinH_apply 2 hStU,
    ModularFormClass.qExpansion_heckeU_eq_heckeU ((D : ℂ) • Xf) hΓ1 hq0, ← h3, ← hpfW,
    map_mul, PowerSeries.map_C, map_natCast, map_heckeU, ← PowerSeries.smul_eq_C_mul]

end Pin

section CharP

variable (K : Type*) [Field K] [IsAlgClosed K] (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ)
  (hpM : p ∣ M) [Algebra (ZMod p) K]

theorem diffQExp_heckeDiff_reduce (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) (S : Set ℕ)
    {ρ : K ⊗[ZMod p] CuspForm.IntTwoCuspForms M H p →ₗ[K]
        Ω[ModularCurve.qExpFunctionFieldC K (GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))⁄K]}
    (hρ : ModularCurve.IsInfReductionMap K p M H hpM ρ)
    (q : ℕ) (hq : q.Prime) (hqM : q ∣ M) (hqp : q ≠ p)
    (f : CuspForm (GammaH M H) 2) (hf : f ∈ CuspForm.twoCuspIntegralSet M H 2 p (⊥ : Subring ℂ))
    (pf : PowerSeries ℤ) (hpf : ModularCurve.IsIntegralQExp ⇑f pf) :
    haveI : NeZero q := ⟨hq.ne_zero⟩
    ModularCurve.diffQExp (ModularCurve.qExpFunctionFieldC K (GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)))
        (ModularCurve.heckeDiffModLH K (M / p) (ModularCurve.infSubgroup p M H hpM) q
          (ρ ((1 : K) ⊗ₜ[ZMod p] CuspForm.intTwoCuspReduce M H p
            ⟨f, CuspForm.twoCuspIntegralSet_subset_twoCuspLattice M H 2 p ⊥ hf⟩))) =
      ModularCurve.qDecimate K q
        (ModularCurve.diffQExp (ModularCurve.qExpFunctionFieldC K (GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)))
          (ρ ((1 : K) ⊗ₜ[ZMod p] CuspForm.intTwoCuspReduce M H p
            ⟨f, CuspForm.twoCuspIntegralSet_subset_twoCuspLattice M H 2 p ⊥ hf⟩))) := by
  haveI : NeZero q := ⟨hq.ne_zero⟩
  have hq0 : q ≠ 0 := hq.ne_zero
  have hC := ModularCurve.IsInfReductionMap.comp_baseChange_genU_eq_genDiffModL_comp_of_ne p M hpM hpM2 H hHp K S hρ
    q hq hqM hqp
  have h1 := LinearMap.congr_fun hC ((1 : K) ⊗ₜ[ZMod p] CuspForm.intTwoCuspReduce M H p
    ⟨f, CuspForm.twoCuspIntegralSet_subset_twoCuspLattice M H 2 p ⊥ hf⟩)
  simp only [LinearMap.comp_apply, LinearMap.baseChange_tmul] at h1
  rw [ModularCurve.genDiffModL_U_of_ne K p M H hpM S q hq hqM hqp] at h1
  rw [← h1, CuspForm.intTwoCuspGenMod_reduce]
  have hUf : CuspForm.heckeULinH 2 q f ∈ CuspForm.twoCuspIntegralSet M H 2 p (⊥ : Subring ℂ) :=
    CuspForm.heckeRingH_apply_mem_twoCuspIntegralSet
      (CuspForm.heckeGenH_mem_heckeRingH S 2 (CohCarrier.Gen.U q hq hqM)) hf
  have hkey : CuspForm.twoCuspEnd (p := p) (A := (⊥ : Subring ℂ))
      ⟨CuspForm.heckeGenH S 2 (CohCarrier.Gen.U q hq hqM), CuspForm.heckeGenH_mem_heckeRingH S 2 _⟩
      ⟨f, CuspForm.twoCuspIntegralSet_subset_twoCuspLattice M H 2 p ⊥ hf⟩ =
      ⟨CuspForm.heckeULinH 2 q f, CuspForm.twoCuspIntegralSet_subset_twoCuspLattice M H 2 p ⊥ hUf⟩ :=
    Subtype.ext rfl
  have hint : ModularCurve.IsIntegralQExp ⇑(CuspForm.heckeULinH 2 q f) (PowerSeries.heckeU q pf) := by
    unfold ModularCurve.IsIntegralQExp
    rw [CuspForm.coe_heckeULinH_apply 2 (CuspForm.stableU M H 2 hq hqM),
      ModularFormClass.qExpansion_heckeU_eq_heckeU f (one_mem_strictPeriods_GammaH M H) hq0, map_heckeU]
    unfold ModularCurve.IsIntegralQExp at hpf
    rw [hpf]
  rw [hkey, hρ.diffQExp_apply hUf hint, hρ.diffQExp_apply hf hpf, intSeriesC_heckeU]

end CharP

section Main

variable (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) [NeZero (M / p)]
  (K : Type*) [Field K] [IsAlgClosed K] [CharP K p] [Algebra (ZMod p) K] (S : Set ℕ)

local notation "Γ'" => GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)
local notation "FF" => ModularCurve.qExpFunctionFieldC K Γ'
local notation "SS" => ModularCurve.ssPolarDifferentials K Γ' p

theorem main (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (ρinf : K ⊗[ZMod p] CuspForm.IntTwoCuspForms M H p →ₗ[K] Ω[FF⁄K])
    (hρinf : ModularCurve.IsInfReductionMap K p M H hpM ρinf)
    (hrange : LinearMap.range ρinf = SS)
    (Wd : ModularForm.AtkinLehnerDatum M (M / p))
    (e : (ZMod M)ˣ) (he : ((ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) e : (ZMod (M / p))ˣ) : ZMod (M / p)) * (p : ZMod (M / p)) = 1)
    (φ : ↥(integralClosure ℤ ℂ) →+* K) (hφ : φ (p : ↥(integralClosure ℤ ℂ)) = 0)
    (W : ↥SS ≃ₗ[K] ↥SS)
    (hW :
      ∀ (f : CuspForm (GammaH M H) 2)
          (hf : f ∈ CuspForm.twoCuspIntegralSet M H 2 p (⊥ : Subring ℂ))
          (D : ℕ) (_ : ¬ p ∣ D)
          (pfW : PowerSeries ↥(integralClosure ℤ ℂ)),
          pfW.map (algebraMap ↥(integralClosure ℤ ℂ) ℂ) =
            UpperHalfPlane.qExpansion 1 ((D : ℂ) • ModularForm.alSlash Wd 2 ⇑(CuspForm.diamondLinH 2 e f)) →
          ∀ ω : ↥SS, ((ω : ↥SS) : Ω[FF⁄K]) =
              ρinf ((1 : K) ⊗ₜ[ZMod p] CuspForm.intTwoCuspReduce M H p
                ⟨f, CuspForm.twoCuspIntegralSet_subset_twoCuspLattice M H 2 p ⊥ hf⟩) →
            (D : K) • ModularCurve.diffQExp FF ((W ω : ↥SS) : Ω[FF⁄K]) =
              HahnSeries.ofPowerSeries ℤ K (pfW.map φ))
    (hspan : Submodule.span K {ω : ↥SS |
        ∃ (f : CuspForm (GammaH M H) 2) (hf : f ∈ CuspForm.twoCuspIntegralSet M H 2 p (⊥ : Subring ℂ))
          (D : ℕ) (_ : ¬ p ∣ D) (pfW : PowerSeries ↥(integralClosure ℤ ℂ)),
          pfW.map (algebraMap ↥(integralClosure ℤ ℂ) ℂ) =
            UpperHalfPlane.qExpansion 1 ((D : ℂ) • ModularForm.alSlash Wd 2 ⇑(CuspForm.diamondLinH 2 e f)) ∧
          ((ω : ↥SS) : Ω[FF⁄K]) =
            ρinf ((1 : K) ⊗ₜ[ZMod p] CuspForm.intTwoCuspReduce M H p
              ⟨f, CuspForm.twoCuspIntegralSet_subset_twoCuspLattice M H 2 p ⊥ hf⟩)} = ⊤) :
    ∀ (q' : ℕ) (hq : q'.Prime) (hqM : q' ∣ M) (_ : q' ≠ p) (ω ω' : ↥SS),
      ((ω' : ↥SS) : Ω[FF⁄K]) = (haveI : NeZero (M / p) := ⟨Nat.pos_iff_ne_zero.mp (Nat.div_pos (Nat.le_of_dvd (NeZero.pos M) hpM) (Fact.out : p.Prime).pos)⟩;
          haveI : NeZero q' := ⟨hq.ne_zero⟩;
          AlgebraicCurve.Differential.correspondence (ModularCurve.heckeAlphaModLH K (M / p) (ModularCurve.infSubgroup p M H hpM) q') (ModularCurve.heckeBetaModLH K (M / p) (ModularCurve.infSubgroup p M H hpM) q')) ((ω : ↥SS) : Ω[FF⁄K]) →
        ((W ω' : ↥SS) : Ω[FF⁄K]) = ModularCurve.genDiffModL K p M H hpM S (CohCarrier.Gen.U q' hq hqM) ((W ω : ↥SS) : Ω[FF⁄K]) := by
  intro q' hq hqM hne ω ω' hω'
  haveI hqi : NeZero q' := ⟨hq.ne_zero⟩
  have hq0 : q' ≠ 0 := hq.ne_zero
  have hpp : p.Prime := Fact.out
  have hqN : q' ∣ M / p := by
    have hM : M = M / p * p := (Nat.div_mul_cancel hpM).symm
    rw [hM] at hqM
    rcases (Nat.Prime.dvd_mul hq).mp hqM with h | h
    · exact h
    · exact absurd ((Nat.prime_dvd_prime_iff_eq hq hpp).mp h) hne
  rw [ModularCurve.genDiffModL_U_of_ne K p M H hpM S q' hq hqM hne]

  set Θ := ModularCurve.diffQExp FF with hΘ
  set U := ModularCurve.heckeDiffModLH K (M / p) (ModularCurve.infSubgroup p M H hpM) q' with hU
  set Ut := AlgebraicCurve.Differential.correspondence
      (ModularCurve.heckeAlphaModLH K (M / p) (ModularCurve.infSubgroup p M H hpM) q')
      (ModularCurve.heckeBetaModLH K (M / p) (ModularCurve.infSubgroup p M H hpM) q') with hUt
  have hΘinj : Function.Injective Θ :=
    ModularCurve.diffQExp_qExpFunctionFieldC_injective K Γ' (T_mem_GammaH _ _)
  have Wp : ModularForm.AtkinLehnerDatum M p := alDatumAtP hpp hpM hpM2

  have hUΘ : ∀ ξ : ↥SS, Θ (U ((ξ : ↥SS) : Ω[FF⁄K])) = ModularCurve.qDecimate K q' (Θ ((ξ : ↥SS) : Ω[FF⁄K])) := by
    intro ξ
    have hξ : ξ ∈ (⊤ : Submodule K ↥SS) := Submodule.mem_top
    rw [← hspan] at hξ
    induction hξ using Submodule.span_induction with
    | mem x hx =>
        obtain ⟨f, hf, D, hD, pfW, hpfW, hx0⟩ := hx
        obtain ⟨pf, hpf⟩ := exists_isIntegralQExp_of_mem Wp hf
        rw [hx0]
        exact diffQExp_heckeDiff_reduce K p M H hpM hpM2 hHp S hρinf q' hq hqM hne f hf pf hpf
    | zero => simp
    | add x y _ _ hx hy =>
        rw [Submodule.coe_add, map_add, map_add, map_add, map_add, hx, hy]
    | smul c x _ hx =>
        rw [Submodule.coe_smul, map_smul, LinearMap.map_smul_of_tower, LinearMap.map_smul_of_tower, map_smul, hx]

  have hgood : ∀ ω₀ : ↥SS, ∃ ω₁ : ↥SS, ((ω₁ : ↥SS) : Ω[FF⁄K]) = Ut ((ω₀ : ↥SS) : Ω[FF⁄K]) ∧
      ((W ω₁ : ↥SS) : Ω[FF⁄K]) = U ((W ω₀ : ↥SS) : Ω[FF⁄K]) := by
    intro ω₀
    have hmem : ω₀ ∈ (⊤ : Submodule K ↥SS) := Submodule.mem_top
    rw [← hspan] at hmem
    induction hmem using Submodule.span_induction with
    | mem x hx =>
        obtain ⟨f, hf, D, hD, pfW, hpfW, hx0⟩ := hx
        obtain ⟨D', hD', g, hg, hgf, hB⟩ :=
          ModularCurve.IsInfReductionMap.exists_smul_correspondence_heckeAlphaModLH_heckeBetaModLH_apply_eq_of_ne
            p M hpM hpM2 H hHp K hρinf q' hq hqM hne f hf
        have hD'K : (D' : K) ≠ 0 := fun h => hD' ((CharP.cast_eq_zero_iff K p D').mp h)
        have hDK : (D : K) ≠ 0 := fun h => hD ((CharP.cast_eq_zero_iff K p D).mp h)
        have hUt0 : Ut ((x : ↥SS) : Ω[FF⁄K]) = (D' : K)⁻¹ •
            ρinf ((1 : K) ⊗ₜ[ZMod p] CuspForm.intTwoCuspReduce M H p
              ⟨g, CuspForm.twoCuspIntegralSet_subset_twoCuspLattice M H 2 p ⊥ hg⟩) := by
          rw [hx0, ← hB, smul_smul, inv_mul_cancel₀ hD'K, one_smul]
        have hmem1 : Ut ((x : ↥SS) : Ω[FF⁄K]) ∈ SS := by
          rw [hUt0, ← hrange]
          exact Submodule.smul_mem _ _ (LinearMap.mem_range_self ρinf _)
        refine ⟨⟨Ut ((x : ↥SS) : Ω[FF⁄K]), hmem1⟩, rfl, ?_⟩

        have hWf := hW f hf D hD pfW hpfW x hx0
        have hpfWg := pin_transposeU hpM hpM2 hHp Wd e hq hqM hqN f g D' (by rw [hgf]; rfl) D pfW hpfW
        have hωg : ((((D' : K) • (⟨Ut ((x : ↥SS) : Ω[FF⁄K]), hmem1⟩ : ↥SS)) : ↥SS) : Ω[FF⁄K]) =
            ρinf ((1 : K) ⊗ₜ[ZMod p] CuspForm.intTwoCuspReduce M H p
              ⟨g, CuspForm.twoCuspIntegralSet_subset_twoCuspLattice M H 2 p ⊥ hg⟩) := by
          rw [Submodule.coe_smul]
          show (D' : K) • Ut ((x : ↥SS) : Ω[FF⁄K]) = _
          rw [hUt0, smul_smul, mul_inv_cancel₀ hD'K, one_smul]
        have hWg := hW g hg D hD _ hpfWg ((D' : K) • ⟨Ut ((x : ↥SS) : Ω[FF⁄K]), hmem1⟩) hωg
        rw [map_smul, Submodule.coe_smul, LinearMap.map_smul_of_tower] at hWg
        have hR : HahnSeries.ofPowerSeries ℤ K
            ((PowerSeries.C (D' : ↥(integralClosure ℤ ℂ)) * PowerSeries.heckeU q' pfW).map φ) =
            (D' : K) • ModularCurve.qDecimate K q' (HahnSeries.ofPowerSeries ℤ K (pfW.map φ)) := by
          rw [map_mul, PowerSeries.map_C, map_natCast, map_heckeU, map_mul, HahnSeries.ofPowerSeries_C,
            HahnSeries.C_mul_eq_smul, ofPowerSeries_heckeU]
        rw [hR, ← hWf, LinearMap.map_smul, ← hUΘ (W x)] at hWg
        have h5 : Θ (((W ⟨Ut ((x : ↥SS) : Ω[FF⁄K]), hmem1⟩ : ↥SS) : Ω[FF⁄K])) = Θ (U ((W x : ↥SS) : Ω[FF⁄K])) := by
          have h := hWg
          rw [smul_smul, smul_smul, mul_comm (D' : K) (D : K)] at h
          exact smul_right_injective _ (mul_ne_zero hDK hD'K) h
        exact hΘinj h5
    | zero =>
        refine ⟨0, ?_, ?_⟩
        · rw [Submodule.coe_zero, map_zero]
        · rw [map_zero, Submodule.coe_zero, map_zero]
    | add x y _ _ hx hy =>
        obtain ⟨x1, hx1, hx1'⟩ := hx
        obtain ⟨y1, hy1, hy1'⟩ := hy
        refine ⟨x1 + y1, ?_, ?_⟩
        · rw [Submodule.coe_add, Submodule.coe_add, map_add, hx1, hy1]
        · rw [map_add, Submodule.coe_add, map_add, Submodule.coe_add, map_add, hx1', hy1']
    | smul c x _ hx =>
        obtain ⟨x1, hx1, hx1'⟩ := hx
        refine ⟨c • x1, ?_, ?_⟩
        · rw [Submodule.coe_smul, Submodule.coe_smul, map_smul, hx1]
        · rw [map_smul, Submodule.coe_smul, map_smul, Submodule.coe_smul, map_smul, hx1']
  obtain ⟨ω₁, h1, h2⟩ := hgood ω
  have h12 : ω₁ = ω' := Subtype.ext (h1.trans hω'.symm)
  subst h12
  exact h2

end Main

end TwistLawU
p2m_reactivate "P2MW.S_ModularCurve_twist_correspondence_heckeU_eq_genDiffModL_U_of_atkinLehnerPinAlong_of_ne.TwistLawU"

end
p2m_reactivate "P2MW.S_ModularCurve_twist_correspondence_heckeU_eq_genDiffModL_U_of_atkinLehnerPinAlong_of_ne.TwistLawU"

theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]
    (K : Type*) [Field K] [IsAlgClosed K] [CharP K p] [Algebra (ZMod p) K] (S : Set ℕ)

    (ρinf : K ⊗[ZMod p] CuspForm.IntTwoCuspForms M H p →ₗ[K] Ω[ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))⁄K])
    (hρinf : ModularCurve.IsInfReductionMap K p M H hpM ρinf)
    (hrange : LinearMap.range ρinf = ModularCurve.ssPolarDifferentials K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) p)

    (Wd : ModularForm.AtkinLehnerDatum M (M / p))
    (e : (ZMod M)ˣ) (he : ((ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) e : (ZMod (M / p))ˣ) : ZMod (M / p)) * (p : ZMod (M / p)) = 1)

    (φ : ↥(integralClosure ℤ ℂ) →+* K) (hφ : φ (p : ↥(integralClosure ℤ ℂ)) = 0)

    (W : ↥(ModularCurve.ssPolarDifferentials K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) p) ≃ₗ[K] ↥(ModularCurve.ssPolarDifferentials K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) p))
    (hW :
      ∀ (f : CuspForm (CohCarrier.GammaH M H) 2)
          (hf : f ∈ CuspForm.twoCuspIntegralSet M H 2 p (⊥ : Subring ℂ))
          (D : ℕ) (_ : ¬ p ∣ D)
          (pfW : PowerSeries ↥(integralClosure ℤ ℂ)),
          pfW.map (algebraMap ↥(integralClosure ℤ ℂ) ℂ) =
            UpperHalfPlane.qExpansion 1 ((D : ℂ) • ModularForm.alSlash Wd 2 ⇑(CuspForm.diamondLinH 2 e f)) →
          ∀ ω : ↥(ModularCurve.ssPolarDifferentials K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) p), ((ω : ↥(ModularCurve.ssPolarDifferentials K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) p)) : Ω[ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))⁄K]) =
              ρinf ((1 : K) ⊗ₜ[ZMod p] CuspForm.intTwoCuspReduce M H p
                ⟨f, CuspForm.twoCuspIntegralSet_subset_twoCuspLattice M H 2 p ⊥ hf⟩) →
            (D : K) • ModularCurve.diffQExp (ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))) ((W ω : ↥(ModularCurve.ssPolarDifferentials K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) p)) : Ω[ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))⁄K]) =
              HahnSeries.ofPowerSeries ℤ K (pfW.map φ))

    (hspan : Submodule.span K {ω : ↥(ModularCurve.ssPolarDifferentials K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) p) |
        ∃ (f : CuspForm (CohCarrier.GammaH M H) 2) (hf : f ∈ CuspForm.twoCuspIntegralSet M H 2 p (⊥ : Subring ℂ))
          (D : ℕ) (_ : ¬ p ∣ D) (pfW : PowerSeries ↥(integralClosure ℤ ℂ)),
          pfW.map (algebraMap ↥(integralClosure ℤ ℂ) ℂ) =
            UpperHalfPlane.qExpansion 1 ((D : ℂ) • ModularForm.alSlash Wd 2 ⇑(CuspForm.diamondLinH 2 e f)) ∧
          ((ω : ↥(ModularCurve.ssPolarDifferentials K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) p)) : Ω[ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))⁄K]) =
            ρinf ((1 : K) ⊗ₜ[ZMod p] CuspForm.intTwoCuspReduce M H p
              ⟨f, CuspForm.twoCuspIntegralSet_subset_twoCuspLattice M H 2 p ⊥ hf⟩)} = ⊤)
    :

      (∀ (q' : ℕ) (hq : q'.Prime) (hqM : q' ∣ M) (_ : q' ≠ p) (ω ω' : ↥(ModularCurve.ssPolarDifferentials K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) p)), ((ω' : ↥(ModularCurve.ssPolarDifferentials K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) p)) : Ω[ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))⁄K]) = (haveI : NeZero (M / p) := ⟨Nat.pos_iff_ne_zero.mp (Nat.div_pos (Nat.le_of_dvd (NeZero.pos M) hpM) (Fact.out : p.Prime).pos)⟩;
          haveI : NeZero q' := ⟨hq.ne_zero⟩;
          AlgebraicCurve.Differential.correspondence (ModularCurve.heckeAlphaModLH K (M / p) (ModularCurve.infSubgroup p M H hpM) q') (ModularCurve.heckeBetaModLH K (M / p) (ModularCurve.infSubgroup p M H hpM) q')) ((ω : ↥(ModularCurve.ssPolarDifferentials K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) p)) : Ω[ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))⁄K]) →
        ((W ω' : ↥(ModularCurve.ssPolarDifferentials K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) p)) : Ω[ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))⁄K]) = ModularCurve.genDiffModL K p M H hpM S (CohCarrier.Gen.U q' hq hqM) ((W ω : ↥(ModularCurve.ssPolarDifferentials K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) p)) : Ω[ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))⁄K])) :=
  TwistLawU.main p M H hpM K S hpM2 hHp ρinf hρinf hrange Wd e he φ hφ W hW hspan

end S_ModularCurve_twist_correspondence_heckeU_eq_genDiffModL_U_of_atkinLehnerPinAlong_of_ne
end P2MW
export P2MW.S_ModularCurve_twist_correspondence_heckeU_eq_genDiffModL_U_of_atkinLehnerPinAlong_of_ne (solution)
