-- Prove2me | solution 1 for ModularCurve.ssHeckeMatrixC_apply_eq_natCard_subgroup_dualPair_of_dvd_of_five_le_of_moduliPlace
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/fbe36b9b-1877-598a-8ee5-266facb346d2

import Mathlib
import Definitions.Def_WeierstrassCurve_RationalEnd
import Definitions.Def_ModularCurve_SSDegeneracyHecke
import Definitions.Def_ModularCurve_ModuliPlace
import Definitions.Def_WeierstrassCurve_VariableChangePointEquiv
import Theorems.Thm_ModularCurve_finsum_ramificationIndexAlong_heckeAlphaC_eq_natCard_overgroup_dualPair_of_moduliPlace
import Theorems.Thm_WeierstrassCurve_natCard_rationalAut_mul_natCard_overgroup_dualPair_eq_natCard_rationalAut_mul_natCard_subgroup_dualPair
import Theorems.Thm_ModularCurve_two_mul_placeWidth_eq_natCard_rationalAut_map_eq_of_toValuationSubring_eq_comap_moduliPlace
import Theorems.Thm_ModularCurve_ramificationIndexAlong_mul_placeWidth_eq_placeWidth_restrictAlong_of_five_le
import Theorems.Thm_ModularCurve_inertiaDegAlong_heckeAlphaC_eq_one
import Theorems.Thm_ModularCurve_moduliPlace_orbitClauses
import Theorems.Thm_ModularCurve_eq_of_isModuliPlaceOf
import Theorems.Thm_ModularCurve_isModuliPlaceOf_nonempty
import Theorems.Thm_ModularCurve_modularFunctionFieldC_eq_modularFunctionFieldFullC
import Theorems.Thm_ModularCurve_charLDegeneracyRoof_eq_modularFunctionFieldFullC_mul
import Theorems.Thm_WeierstrassCurve_natCard_fibre_dvd_jWidth_of_variableChange_orbitMap
import Theorems.Thm_WeierstrassCurve_finite_rationalHomSet_units
import Theorems.Thm_AlgebraicCurve_Place_evalAt_congr
import Theorems.Thm_AlgebraicCurve_Place_evalAt_algebraMap
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_ssHeckeMatrixC_apply_eq_natCard_subgroup_dualPair_of_dvd_of_five_le_of_moduliPlace
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.instIsElliptic_tateBase ModularCurve.instIsElliptic_tateLaurent ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 CyclotomicUniv.instCharZeroR₀ CyclotomicUniv.instIsDomain CyclotomicUniv.instIsDomainR₀ CyclotomicUniv.instCharZero ModularCurve.KatzGamma0Form.instModule ModularCurve.KatzGamma0Form.instZero ModularCurve.KatzLevelPForm.instSMul ModularCurve.KatzGamma0Form.instAdd ModularCurve.KatzLevelPForm.instAddCommGroup ModularCurve.KatzGamma0Form.instNeg ModularCurve.KatzGamma0Form.instAddCommGroup ModularCurve.KatzLevelPForm.instAdd ModularCurve.KatzLevelPForm.instSub ModularCurve.KatzLevelPForm.instNeg ModularCurve.KatzGamma0Form.instSMul ModularCurve.KatzGamma0Form.instSub ModularCurve.KatzLevelPForm.instZero"
p2m_attr_erase "instance" "ModularCurve.KatzLevelPForm.instModule KatzModularForm.instAddCommGroup KatzModularForm.instSub KatzModularForm.instZero KatzModularForm.instModule KatzModularForm.instAdd KatzModularForm.instNeg KatzModularForm.instSMul AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.instSMulAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instDistribMulActionAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange WeierstrassCurve.Affine.Point.instFinite GaloisRep.ratLocalizedAt.span_isPrime GaloisRep.instAlgebraRatLocalizedAtZMod GaloisRepAdic.instAddCommGroup GaloisRepAdic.instFree GaloisRepAdic.instFinite GaloisRepAdic.instModule ResidualGaloisRep.instModule ResidualGaloisRep.instModuleFinite ResidualGaloisRep.instAddCommGroup ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK"
p2m_attr_erase "instance" "AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.B3.instIsElliptic_goodModel ModularCurve.instIsScalarTowerJAdjoin"
p2m_attr_erase "simp" "WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right"
p2m_attr_erase "simp" "FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec"
p2m_attr_erase "simp" "WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero"
p2m_attr_erase "simp" "ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply ModularCurve.ProjectiveLine.map_mk WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm CyclotomicUniv.lift₀_ζ₀ CyclotomicUniv.lift_algebraMap CyclotomicUniv.val_ζUnit CyclotomicUniv.lift_ζ ModularCurve.cuspData_yP ModularCurve.qTwistAlgHom_apply ModularCurve.cuspData_yQ ModularCurve.cuspData_xP ModularCurve.cuspData_xQ ModularCurve.val_cyclZeta ModularCurve.cuspShift_one ModularCurve.cuspShift_zero"
p2m_attr_erase "simp" "ModularCurve.LevelPData.mk.sizeOf_spec ModularCurve.KatzLevelPForm.neg_toFun ModularCurve.LevelP.coe_swapW ModularCurve.KatzLevelPForm.swap_swap KatzModularForm.pullbackLevelP_toFun ModularCurve.LevelPData.swap_xQ KatzModularForm.pullbackLevelP_zero ModularCurve.LevelPData.map_yP ModularCurve.KatzLevelPForm.swap_neg ModularCurve.KatzGamma0Form.toKatzLevelPForm_sub ModularCurve.KatzLevelPForm.swap_add KatzModularForm.swap_pullbackLevelP ModularCurve.KatzGamma0Form.toKatzLevelPForm_add ModularCurve.KatzLevelPForm.swap_smul ModularCurve.LevelPData.map_yQ ModularCurve.KatzLevelPForm.mk.injEq ModularCurve.KatzLevelPForm.zero_toFun KatzModularForm.pullbackLevelP_smul ModularCurve.LevelPData.swap_xP ModularCurve.KatzGamma0Form.toKatzLevelPForm_mul ModularCurve.KatzGamma0Form.toKatzLevelPForm_neg ModularCurve.LevelPData.variableChange_xQ KatzModularForm.pullbackGamma0_toKatzLevelPForm ModularCurve.KatzLevelPForm.mk.sizeOf_spec ModularCurve.KatzLevelPForm.swap_zero ModularCurve.LevelP.coe_unipotentU ModularCurve.KatzLevelPForm.mul_toFun ModularCurve.LevelPData.variableChange_yP ModularCurve.LevelPData.mk.injEq ModularCurve.KatzLevelPForm.sub_toFun ModularCurve.LevelPData.variableChange_xP ModularCurve.KatzLevelPForm.smul_toFun ModularCurve.LevelPData.swap_yP ModularCurve.LevelPData.map_xP ModularCurve.LevelPData.swap_swap ModularCurve.LevelPData.swap_yQ ModularCurve.KatzGamma0Form.toKatzLevelPForm_zero ModularCurve.KatzGamma0Form.mk.injEq ModularCurve.KatzLevelPForm.swap_toFun KatzModularForm.pullbackLevelP_add"
p2m_attr_erase "simp" "ModularCurve.KatzGamma0Form.mk.sizeOf_spec ModularCurve.LevelPData.variableChange_yQ ModularCurve.KatzLevelPForm.swap_sub ModularCurve.KatzGamma0Form.toKatzLevelPForm_smul ModularCurve.LevelPData.map_xQ ModularCurve.KatzLevelPForm.add_toFun KatzModularForm.c₆_toFun KatzModularForm.neg_toFun KatzModularForm.mul_toFun KatzModularForm.qExpansion_neg KatzModularForm.discr_toFun KatzModularForm.qExpansion_sub KatzModularForm.qExpansion_add KatzModularForm.qExpansion_mul KatzModularForm.zero_toFun KatzModularForm.mk.injEq KatzModularForm.qExpansion_smul KatzModularForm.smul_toFun KatzModularForm.add_toFun KatzModularForm.sub_toFun KatzModularForm.c₄_toFun KatzModularForm.qExpansion_zero KatzModularForm.mk.sizeOf_spec TateCurve.tateTorsionPoint_zero_zero WeierstrassCurve.pointAddEquivOfEq_refl WeierstrassCurve.Universal.halveX_zero WeierstrassCurve.Universal.specialize_X_one WeierstrassCurve.Universal.coeff_halve WeierstrassCurve.Universal.specialize_X_two WeierstrassCurve.Universal.halveCoeff_zero WeierstrassCurve.Universal.specialize_X_four WeierstrassCurve.Universal.coeff_halveX WeierstrassCurve.Universal.specialize_X_three WeierstrassCurve.Universal.specialize_X_zero ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some"
p2m_attr_erase "simp" "AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularCurve.cuspCount_one ModularCurve.baseAut_arithmeticGalois ModularCurve.JZero.torsionGaloisRep_apply ModularCurve.coe_arithmeticRingAut_apply ModularCurve.toRingAut_arithmeticGalois HahnSeries.ramScale_apply AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar PowerSeries.coeff_heckeV PowerSeries.coeff_heckeU LaurentSeries.coeff_heckeV LaurentSeries.coeff_heckeU FreyPackage.ModMCarrier.coe_rescaleLin_apply ModularForm.AtkinLehnerDatum.mk.injEq ModularForm.AtkinLehnerDatum.alGL_coe ModularForm.AtkinLehnerDatum.mk.sizeOf_spec ModularForm.AtkinLehnerDatum.sqUnitSL_coe ModularForm.AtkinLehnerDatum.det_sqUnit ModularForm.AtkinLehnerDatum.det_mat ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong"
p2m_attr_erase "simp" "GaloisRepAdic.mk.injEq GaloisRepAdic.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.injEq ResidualGaloisRep.mk.sizeOf_spec ResidualGaloisRep.mk.injEq ResidualGaloisRep.Equiv.mk.sizeOf_spec ResidualGaloisRep.Equiv.mk.injEq ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.coe_cuspidalDivisor₀ AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq"
p2m_attr_erase "simp" "AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero"

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

p2m_open "AlgebraicCurve ModularCurve~CycSub P2MW.S_ModularCurve_ssHeckeMatrixC_apply_eq_natCard_subgroup_dualPair_of_dvd_of_five_le_of_moduliPlace.ModularCurve WeierstrassCurve~card WeierstrassCurve.Affine"
open scoped IntermediateField

noncomputable section

namespace ModularCurve
p2m_export "ModularCurve" "ssHeckeMatrixC charLDegeneracyRoof heckeAlphaC coe_heckeAlphaC heckeBetaC coe_heckeBetaC algebraMap_laurentSeries_apply_eq_single mem_restrictAlong_iff jqModC modularFunctionFieldC qExpand qExpand_single placeRamificationJ placeWidth ssPlaces jGeomGen coe_jGeomGen ModuliPoint jWidth ComapPlace.mem_iff_ord_nonneg IsModuliPlaceOf moduliPlace modularFunctionFieldFullC jqModC_mem_full modularFunctionFieldC_le_full full_degeneracyC_le full_degeneracyC_map_le finsum_ramificationIndexAlong_heckeAlphaC_eq_natCard_overgroup_dualPair_of_moduliPlace two_mul_placeWidth_eq_natCard_rationalAut_map_eq_of_toValuationSubring_eq_comap_moduliPlace ramificationIndexAlong_mul_placeWidth_eq_placeWidth_restrictAlong_of_five_le inertiaDegAlong_heckeAlphaC_eq_one moduliPlace_orbitClauses eq_of_isModuliPlaceOf isModuliPlaceOf_nonempty modularFunctionFieldC_eq_modularFunctionFieldFullC charLDegeneracyRoof_eq_modularFunctionFieldFullC_mul"
namespace UCurveLevelN
p2m_open "ModularCurve~CycSub"

section PlaceCalculus

variable {K F F' G G' : Type*} [Field K] [Field F] [Field F'] [Field G] [Field G']
  [Algebra K F] [Algebra K F'] [Algebra K G] [Algebra K G']

theorem mem_restrictAlong_iff (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (w : Place K F')
    (x : F) : x ∈ (w.restrictAlong φ hφ).toValuationSubring ↔ φ x ∈ w.toValuationSubring :=
  Iff.rfl

theorem algebraMap_comm (e : F ≃ₐ[K] G) (a : K) :
    e.toRingEquiv (algebraMap K F a) = algebraMap K G a :=
  e.commutes a

abbrev transport (e : F ≃ₐ[K] G) : Place K F → Place K G :=
  Place.congrRingEquiv e.toRingEquiv (algebraMap_comm e)

theorem mem_transport_iff (e : F ≃ₐ[K] G) (v : Place K F) (y : G) :
    y ∈ (transport e v).toValuationSubring ↔ e.symm y ∈ v.toValuationSubring :=
  Iff.rfl

theorem transport_injective (e : F ≃ₐ[K] G) : Function.Injective (transport e) :=
  (Place.congrEquiv e.toRingEquiv (algebraMap_comm e)).injective

theorem transport_bijective (e : F ≃ₐ[K] G) : Function.Bijective (transport e) :=
  (Place.congrEquiv e.toRingEquiv (algebraMap_comm e)).bijective

theorem ord_transport (e : F ≃ₐ[K] G) (v : Place K F) (f : F) :
    (transport e v).ord (e f) = v.ord f :=
  Place.ord_congrRingEquiv e.toRingEquiv (algebraMap_comm e) v f

theorem transport_transport_symm (e : F ≃ₐ[K] G) (P : Place K G) :
    transport e (transport e.symm P) = P := by
  ext1
  refine SetLike.ext fun y => ?_
  rw [mem_transport_iff, mem_transport_iff, AlgEquiv.symm_symm, AlgEquiv.apply_symm_apply]

theorem transport_symm_transport (e : F ≃ₐ[K] G) (P : Place K F) :
    transport e.symm (transport e P) = P := by
  have h := transport_transport_symm e.symm P
  rwa [AlgEquiv.symm_symm] at h

theorem ord_transport_symm (e : F ≃ₐ[K] G) (P : Place K G) (f : F) :
    (transport e.symm P).ord f = P.ord (e f) := by
  conv_rhs => rw [← transport_transport_symm e P]
  rw [ord_transport]

theorem restrictAlong_transport (e₁ : F ≃ₐ[K] G) (e₂ : F' ≃ₐ[K] G')
    (φ : G →ₐ[K] G') (φ' : F →ₐ[K] F') (hcomm : ∀ x, φ (e₁ x) = e₂ (φ' x))
    (hφ : φ.toRingHom.IsIntegral) (hφ' : φ'.toRingHom.IsIntegral) (v : Place K F') :
    (transport e₂ v).restrictAlong φ hφ = transport e₁ (v.restrictAlong φ' hφ') := by
  ext1
  refine SetLike.ext fun y => ?_
  rw [mem_restrictAlong_iff, mem_transport_iff, mem_transport_iff, mem_restrictAlong_iff]
  have hy : φ y = e₂ (φ' (e₁.symm y)) := by
    rw [← hcomm, AlgEquiv.apply_symm_apply]
  rw [hy, AlgEquiv.symm_apply_apply]

theorem ramificationIndexAlong_transport (e₁ : F ≃ₐ[K] G) (e₂ : F' ≃ₐ[K] G')
    (φ : G →ₐ[K] G') (φ' : F →ₐ[K] F') (hcomm : ∀ x, φ (e₁ x) = e₂ (φ' x)) (v : Place K F') :
    (transport e₂ v).ramificationIndexAlong φ = v.ramificationIndexAlong φ' := by
  show sInf {n : ℕ | 0 < n ∧ ∃ f : G, f ≠ 0 ∧ (transport e₂ v).ord (φ f) = n} =
    sInf {n : ℕ | 0 < n ∧ ∃ f : F, f ≠ 0 ∧ v.ord (φ' f) = n}
  congr 1
  ext n
  simp only [Set.mem_setOf_eq]
  refine and_congr_right fun _ => ⟨?_, ?_⟩
  · rintro ⟨f, hf, hn⟩
    refine ⟨e₁.symm f, by simpa using hf, ?_⟩
    rw [← ord_transport e₂, ← hcomm, AlgEquiv.apply_symm_apply]
    exact hn
  · rintro ⟨f, hf, hn⟩
    refine ⟨e₁ f, by simpa using hf, ?_⟩
    rw [hcomm, ord_transport]
    exact hn

theorem isIntegral_of_comm (e₁ : F ≃ₐ[K] G) (e₂ : F' ≃ₐ[K] G')
    (φ : G →ₐ[K] G') (φ' : F →ₐ[K] F') (hcomm : ∀ x, φ (e₁ x) = e₂ (φ' x))
    (hφ : φ.toRingHom.IsIntegral) : φ'.toRingHom.IsIntegral := by
  have h : φ'.toRingHom =
      (e₂.symm : G' →+* F').comp (φ.toRingHom.comp (e₁ : F →+* G)) := by
    ext x
    show φ' x = e₂.symm (φ (e₁ x))
    rw [hcomm, AlgEquiv.symm_apply_apply]
  rw [h]
  refine RingHom.IsIntegral.trans _ _ (RingHom.IsIntegral.trans _ _ ?_ hφ) ?_
  · exact RingHom.isIntegral_of_surjective _ e₁.surjective
  · exact RingHom.isIntegral_of_surjective _ e₂.symm.surjective

theorem natCard_fibre_comp {X : Type*} (ι : Place K F → Place K G) (hι : Function.Injective ι)
    (p : X → Place K F) (x : X) :
    Nat.card {x' : X // ι (p x') = ι (p x)} = Nat.card {x' : X // p x' = p x} :=
  Nat.card_congr (Equiv.subtypeEquivRight fun _ => hι.eq_iff)

variable {Z : Type*} [Field Z] [Algebra K Z]

theorem ord_along (φ : F →ₐ[K] Z) (hφ : φ.toRingHom.IsIntegral) (W : Place K Z) (t : F) :
    W.ord (φ t) = W.ramificationIndexAlong φ * (W.restrictAlong φ hφ).ord t := by
  rw [← Place.ord_restrictAlong]

theorem ramificationIndexAlong_pos (φ : F →ₐ[K] Z) (hφ : φ.toRingHom.IsIntegral) (W : Place K Z) :
    0 < W.ramificationIndexAlong φ := by
  letI := algebraAlong φ
  haveI := isIntegral_along φ hφ
  exact W.ramificationIndex_pos

end PlaceCalculus

section Tower

variable (K : Type*) [Field K] (M s : ℕ) [NeZero M] [NeZero s]

scoped instance neZero_mul : NeZero (M * s) := ⟨Nat.mul_ne_zero (NeZero.ne M) (NeZero.ne s)⟩

def jF (N : ℕ) [NeZero N] : modularFunctionFieldFullC K N := ⟨jqModC K, jqModC_mem_full K N⟩

@[scoped simp] theorem coe_jF (N : ℕ) [NeZero N] : ((jF K N : modularFunctionFieldFullC K N) :
    LaurentSeries K) = jqModC K := rfl

def inclMS : modularFunctionFieldFullC K M →ₐ[K] modularFunctionFieldFullC K (M * s) :=
  IntermediateField.inclusion (full_degeneracyC_le K (dvd_mul_right M s))

@[scoped simp] theorem coe_inclMS (x : modularFunctionFieldFullC K M) :
    ((inclMS K M s x : modularFunctionFieldFullC K (M * s)) : LaurentSeries K) = x :=
  IntermediateField.coe_inclusion _ x

def betaMSRingHom : modularFunctionFieldFullC K M →+* modularFunctionFieldFullC K (M * s) where
  toFun x := ⟨qExpand K s (x : LaurentSeries K), full_degeneracyC_map_le K M s ⟨x, x.2, rfl⟩⟩
  map_one' := Subtype.ext (map_one (qExpand K s))
  map_mul' _ _ := Subtype.ext (map_mul (qExpand K s) _ _)
  map_zero' := Subtype.ext (map_zero (qExpand K s))
  map_add' _ _ := Subtype.ext (map_add (qExpand K s) _ _)

def betaMS : modularFunctionFieldFullC K M →ₐ[K] modularFunctionFieldFullC K (M * s) :=
  { betaMSRingHom K M s with
    commutes' := fun a => Subtype.ext <| by
      show qExpand K s (algebraMap K (LaurentSeries K) a) = algebraMap K (LaurentSeries K) a
      rw [algebraMap_laurentSeries_apply_eq_single, qExpand_single, mul_zero] }

@[scoped simp] theorem coe_betaMS (x : modularFunctionFieldFullC K M) :
    ((betaMS K M s x : modularFunctionFieldFullC K (M * s)) : LaurentSeries K) =
      qExpand K s (x : LaurentSeries K) := rfl

theorem coe_equivOfEq {L : Type*} [Field L] [Algebra K L] {S T : IntermediateField K L}
    (h : S = T) (x : S) : ((IntermediateField.equivOfEq h x : T) : L) = x := rfl

variable {K M s} in
theorem not_dvd_of_cast_mul_ne_zero (hMs : ((M * s : ℕ) : K) ≠ 0) :
    ¬ ringChar K ∣ M * s ∧ ¬ ringChar K ∣ M := by
  have h1 : ¬ ringChar K ∣ M * s := fun h => hMs ((ringChar.spec K (M * s)).mpr h)
  exact ⟨h1, fun h => h1 (h.mul_right s)⟩

variable {K M s} in
theorem cast_ne_zero_of_cast_mul_ne_zero (hMs : ((M * s : ℕ) : K) ≠ 0) : (M : K) ≠ 0 := by
  intro h
  apply hMs
  rw [Nat.cast_mul, h, zero_mul]

variable {K M s} in
theorem cast_ne_zero_of_cast_mul_ne_zero' (hMs : ((M * s : ℕ) : K) ≠ 0) : (s : K) ≠ 0 := by
  intro h
  apply hMs
  rw [Nat.cast_mul, h, mul_zero]

variable {K M s} in

theorem fieldC_eq (hMs : ((M * s : ℕ) : K) ≠ 0) :
    modularFunctionFieldC K M = modularFunctionFieldFullC K M :=
  ModularCurve.modularFunctionFieldC_eq_modularFunctionFieldFullC K (ringChar K) M
    (not_dvd_of_cast_mul_ne_zero hMs).2

variable {K M s} in

theorem roof_eq (hMs : ((M * s : ℕ) : K) ≠ 0) :
    charLDegeneracyRoof K M s = modularFunctionFieldFullC K (M * s) :=
  ModularCurve.charLDegeneracyRoof_eq_modularFunctionFieldFullC_mul K (ringChar K) M s
    (not_dvd_of_cast_mul_ne_zero hMs).1

variable {K M s} in

def eC (hMs : ((M * s : ℕ) : K) ≠ 0) :
    modularFunctionFieldFullC K M ≃ₐ[K] modularFunctionFieldC K M :=
  IntermediateField.equivOfEq (fieldC_eq hMs).symm

variable {K M s} in

def eR (hMs : ((M * s : ℕ) : K) ≠ 0) :
    modularFunctionFieldFullC K (M * s) ≃ₐ[K] charLDegeneracyRoof K M s :=
  IntermediateField.equivOfEq (roof_eq hMs).symm

variable {K M s} (hMs : ((M * s : ℕ) : K) ≠ 0)

@[scoped simp] theorem coe_eC (x : modularFunctionFieldFullC K M) :
    ((eC hMs x : modularFunctionFieldC K M) : LaurentSeries K) = x :=
  coe_equivOfEq K (fieldC_eq hMs).symm x

theorem coe_eC_symm (x : modularFunctionFieldC K M) :
    (((eC hMs).symm x : modularFunctionFieldFullC K M) : LaurentSeries K) = x := by
  rw [← coe_eC hMs ((eC hMs).symm x), AlgEquiv.apply_symm_apply]

@[scoped simp] theorem coe_eR (x : modularFunctionFieldFullC K (M * s)) :
    ((eR hMs x : charLDegeneracyRoof K M s) : LaurentSeries K) = x :=
  coe_equivOfEq K (roof_eq hMs).symm x

theorem coe_eR_symm (x : charLDegeneracyRoof K M s) :
    (((eR hMs).symm x : modularFunctionFieldFullC K (M * s)) : LaurentSeries K) = x := by
  rw [← coe_eR hMs ((eR hMs).symm x), AlgEquiv.apply_symm_apply]

theorem eC_jF : eC hMs (jF K M) = jGeomGen K M :=
  Subtype.ext (coe_eC hMs (jF K M))

theorem eR_jF : eR hMs (jF K (M * s)) = heckeAlphaC K M s (jGeomGen K M) := by
  apply Subtype.ext
  rw [coe_eR, coe_heckeAlphaC, coe_jF, coe_jGeomGen]

theorem heckeAlphaC_eC (x : modularFunctionFieldFullC K M) :
    heckeAlphaC K M s (eC hMs x) = eR hMs (inclMS K M s x) := by
  apply Subtype.ext
  rw [coe_heckeAlphaC, coe_eC, coe_eR, coe_inclMS]

theorem heckeBetaC_eC (x : modularFunctionFieldFullC K M) :
    heckeBetaC K M s (eC hMs x) = eR hMs (betaMS K M s x) := by
  apply Subtype.ext
  rw [coe_heckeBetaC, coe_eC, coe_eR, coe_betaMS]

theorem eC_jF_sub (c : K) :
    eC hMs (jF K M - algebraMap K (modularFunctionFieldFullC K M) c) =
      jGeomGen K M - algebraMap K (modularFunctionFieldC K M) c := by
  rw [map_sub, AlgEquiv.commutes, eC_jF]

theorem eR_jF_sub (c : K) :
    eR hMs (jF K (M * s) - algebraMap K (modularFunctionFieldFullC K (M * s)) c) =
      heckeAlphaC K M s (jGeomGen K M) - algebraMap K (charLDegeneracyRoof K M s) c := by
  rw [map_sub, AlgEquiv.commutes, eR_jF]

theorem transport_eC_eq_iff (v : Place K (modularFunctionFieldFullC K M)) (x : Place K (modularFunctionFieldC K M)) :
    x = transport (eC hMs) v ↔
      x.toValuationSubring = v.toValuationSubring.comap
        (IntermediateField.inclusion (modularFunctionFieldC_le_full K M)).toRingHom := by
  constructor
  · rintro rfl
    refine SetLike.ext fun y => ?_
    rw [mem_transport_iff, ValuationSubring.mem_comap]
    exact Iff.of_eq (congrArg (· ∈ v.toValuationSubring) (Subtype.ext rfl))
  · intro h
    ext1
    rw [h]
    refine SetLike.ext fun y => ?_
    rw [mem_transport_iff, ValuationSubring.mem_comap]
    exact Iff.of_eq (congrArg (· ∈ v.toValuationSubring) (Subtype.ext rfl))

end Tower

section Clauses

variable {κ : Type} [Field κ] [IsAlgClosed κ] [DecidableEq κ] (N ℓ : ℕ) [NeZero N] [NeZero ℓ]

abbrev CycSub (E : WeierstrassCurve κ) (n : ℕ) : Type :=
  {C : AddSubgroup E.toAffine.Point // IsAddCyclic C ∧ Nat.card C = n}

variable {N ℓ} (hNℓ : ((N * ℓ : ℕ) : κ) ≠ 0)

def gPl (E : WeierstrassCurve κ) (C : AddSubgroup E.toAffine.Point) : Place κ (modularFunctionFieldC κ N) :=
  transport (eC hNℓ) (moduliPlace κ N E C)

def fPl (E : WeierstrassCurve κ) (C : AddSubgroup E.toAffine.Point) : Place κ (charLDegeneracyRoof κ N ℓ) :=
  transport (eR hNℓ) (moduliPlace κ (N * ℓ) E C)

include hNℓ in
theorem hN_of : (N : κ) ≠ 0 := cast_ne_zero_of_cast_mul_ne_zero hNℓ

theorem hex_of (M : ℕ) [NeZero M] (hM : (M : κ) ≠ 0) : ∀ x : ModuliPoint M κ, ∃ v, IsModuliPlaceOf κ M x v :=
  fun x => ModularCurve.isModuliPlaceOf_nonempty κ M hM x

theorem huniq_of (M : ℕ) [NeZero M] (hM : (M : κ) ≠ 0) :
    ∀ (x : ModuliPoint M κ) (v v' : Place κ (modularFunctionFieldFullC κ M)),
      IsModuliPlaceOf κ M x v → IsModuliPlaceOf κ M x v' → v = v' :=
  fun x v v' hv hv' => ModularCurve.eq_of_isModuliPlaceOf κ M hM x v v' hv hv'

theorem ordC (c : κ) (v : Place κ (modularFunctionFieldFullC κ N)) :
    (transport (eC hNℓ) v).ord (jGeomGen κ N - algebraMap κ (modularFunctionFieldC κ N) c) =
      v.ord (jF κ N - algebraMap κ (modularFunctionFieldFullC κ N) c) := by
  rw [← eC_jF_sub hNℓ, ord_transport]

theorem ordR (c : κ) (v : Place κ (modularFunctionFieldFullC κ (N * ℓ))) :
    (transport (eR hNℓ) v).ord (heckeAlphaC κ N ℓ (jGeomGen κ N) - algebraMap κ (charLDegeneracyRoof κ N ℓ) c) =
      v.ord (jF κ (N * ℓ) - algebraMap κ (modularFunctionFieldFullC κ (N * ℓ)) c) := by
  rw [← eR_jF_sub hNℓ, ord_transport]

theorem g1 (E : WeierstrassCurve κ) [E.IsElliptic] (C : CycSub E N) :
    0 < (gPl hNℓ E C.1).ord (jGeomGen κ N - algebraMap κ (modularFunctionFieldC κ N) E.j) := by
  rw [gPl, ordC]
  exact (ModularCurve.moduliPlace_orbitClauses κ N (hN_of hNℓ) (huniq_of N (hN_of hNℓ))).1 E C

theorem g3 (E E' : WeierstrassCurve κ) [E.IsElliptic] [E'.IsElliptic] (C : CycSub E N) (C' : CycSub E' N) :
    gPl hNℓ E C.1 = gPl hNℓ E' C'.1 ↔ ∃ γ : VariableChange κ, γ • E = E' ∧
      ∀ T ∈ C.1, ∃ T' ∈ C'.1, HEq (Point.vcInvFun γ E.toAffine T) T' := by
  rw [gPl, gPl, (transport_injective (eC hNℓ)).eq_iff]
  exact (ModularCurve.moduliPlace_orbitClauses κ N (hN_of hNℓ) (huniq_of N (hN_of hNℓ))).2.2.1 E E' C C'

theorem g4 (E : WeierstrassCurve κ) [E.IsElliptic] (C : CycSub E N) :
    (gPl hNℓ E C.1).ord (jGeomGen κ N - algebraMap κ (modularFunctionFieldC κ N) E.j) =
      (Nat.card {C' : CycSub E N // gPl hNℓ E C'.1 = gPl hNℓ E C.1} : ℤ) := by
  have h4 := (ModularCurve.moduliPlace_orbitClauses κ N (hN_of hNℓ) (huniq_of N (hN_of hNℓ))).2.2.2 E C
  have hfib := natCard_fibre_comp (transport (eC hNℓ)) (transport_injective (eC hNℓ))
    (fun C' : CycSub E N => moduliPlace κ N E C'.1) C
  show (transport (eC hNℓ) (moduliPlace κ N E C.1)).ord _ =
    (Nat.card {C' : CycSub E N //
      transport (eC hNℓ) (moduliPlace κ N E C'.1) = transport (eC hNℓ) (moduliPlace κ N E C.1)} : ℤ)
  rw [ordC, hfib]
  exact h4

theorem f2 (E : WeierstrassCurve κ) [E.IsElliptic] (P : Place κ (charLDegeneracyRoof κ N ℓ))
    (hP : 0 < P.ord (heckeAlphaC κ N ℓ (jGeomGen κ N) - algebraMap κ (charLDegeneracyRoof κ N ℓ) E.j)) :
    ∃ C : CycSub E (N * ℓ), fPl hNℓ E C.1 = P := by
  have hP' : 0 < (transport (eR hNℓ).symm P).ord
      (jF κ (N * ℓ) - algebraMap κ (modularFunctionFieldFullC κ (N * ℓ)) E.j) := by
    rwa [ord_transport_symm, eR_jF_sub]
  obtain ⟨C, hC⟩ := (ModularCurve.moduliPlace_orbitClauses κ (N * ℓ) hNℓ (huniq_of (N * ℓ) hNℓ)).2.1 E _ hP'
  exact ⟨C, by rw [fPl, hC, transport_transport_symm]⟩

theorem f3 (E : WeierstrassCurve κ) [E.IsElliptic] (C C' : CycSub E (N * ℓ)) :
    fPl hNℓ E C.1 = fPl hNℓ E C'.1 ↔ ∃ γ : VariableChange κ, γ • E = E ∧
      ∀ T ∈ C.1, ∃ T' ∈ C'.1, HEq (Point.vcInvFun γ E.toAffine T) T' := by
  rw [fPl, fPl, (transport_injective (eR hNℓ)).eq_iff]
  exact (ModularCurve.moduliPlace_orbitClauses κ (N * ℓ) hNℓ (huniq_of (N * ℓ) hNℓ)).2.2.1 E E C C'

theorem f4 (E : WeierstrassCurve κ) [E.IsElliptic] (C : CycSub E (N * ℓ)) :
    (fPl hNℓ E C.1).ord (heckeAlphaC κ N ℓ (jGeomGen κ N) - algebraMap κ (charLDegeneracyRoof κ N ℓ) E.j) =
      (Nat.card {C' : CycSub E (N * ℓ) // fPl hNℓ E C'.1 = fPl hNℓ E C.1} : ℤ) := by
  have h4 := (ModularCurve.moduliPlace_orbitClauses κ (N * ℓ) hNℓ (huniq_of (N * ℓ) hNℓ)).2.2.2 E C
  have hfib := natCard_fibre_comp (transport (eR hNℓ)) (transport_injective (eR hNℓ))
    (fun C' : CycSub E (N * ℓ) => moduliPlace κ (N * ℓ) E C'.1) C
  show (transport (eR hNℓ) (moduliPlace κ (N * ℓ) E C.1)).ord _ =
    (Nat.card {C' : CycSub E (N * ℓ) //
      transport (eR hNℓ) (moduliPlace κ (N * ℓ) E C'.1) = transport (eR hNℓ) (moduliPlace κ (N * ℓ) E C.1)} : ℤ)
  rw [ordR, hfib]
  exact h4

theorem f1 (E : WeierstrassCurve κ) [E.IsElliptic] (C : CycSub E (N * ℓ)) :
    0 < (fPl hNℓ E C.1).ord (heckeAlphaC κ N ℓ (jGeomGen κ N) - algebraMap κ (charLDegeneracyRoof κ N ℓ) E.j) := by
  rw [fPl, ordR]
  exact (ModularCurve.moduliPlace_orbitClauses κ (N * ℓ) hNℓ (huniq_of (N * ℓ) hNℓ)).1 E C

theorem ord_alpha_sub (hα : (heckeAlphaC κ N ℓ).toRingHom.IsIntegral) (E : WeierstrassCurve κ) [E.IsElliptic]
    (W : Place κ (charLDegeneracyRoof κ N ℓ)) :
    W.ord (heckeAlphaC κ N ℓ (jGeomGen κ N) - algebraMap κ (charLDegeneracyRoof κ N ℓ) E.j) =
      W.ramificationIndexAlong (heckeAlphaC κ N ℓ) *
        (W.restrictAlong (heckeAlphaC κ N ℓ) hα).ord (jGeomGen κ N - algebraMap κ (modularFunctionFieldC κ N) E.j) := by
  rw [← Place.ord_restrictAlong, map_sub, AlgHom.commutes]

theorem exists_of_restrictAlong_eq (hα : (heckeAlphaC κ N ℓ).toRingHom.IsIntegral) (E : WeierstrassCurve κ) [E.IsElliptic]
    (C : CycSub E N) (W : Place κ (charLDegeneracyRoof κ N ℓ))
    (hW : W.restrictAlong (heckeAlphaC κ N ℓ) hα = gPl hNℓ E C.1) : ∃ Cp : CycSub E (N * ℓ), fPl hNℓ E Cp.1 = W := by
  apply f2 hNℓ E W
  rw [ord_alpha_sub hα E W, hW]
  have h1 := ramificationIndexAlong_pos (heckeAlphaC κ N ℓ) hα W
  have h2 := g1 hNℓ E C
  positivity

end Clauses

section RoofC

variable {κ : Type} [Field κ] [IsAlgClosed κ] [DecidableEq κ] {N ℓ : ℕ} [NeZero N] [NeZero ℓ]
  (hNℓ : ((N * ℓ : ℕ) : κ) ≠ 0)

include hNℓ in

theorem fieldC_eq_top : modularFunctionFieldC κ (N * ℓ) = modularFunctionFieldFullC κ (N * ℓ) :=
  ModularCurve.modularFunctionFieldC_eq_modularFunctionFieldFullC κ (ringChar κ) (N * ℓ)
    (not_dvd_of_cast_mul_ne_zero hNℓ).1

def eT : charLDegeneracyRoof κ N ℓ ≃ₐ[κ] modularFunctionFieldC κ (N * ℓ) :=
  (eR hNℓ).symm.trans (IntermediateField.equivOfEq (fieldC_eq_top hNℓ).symm)

@[scoped simp] theorem coe_eT (x : charLDegeneracyRoof κ N ℓ) :
    ((eT hNℓ x : modularFunctionFieldC κ (N * ℓ)) : LaurentSeries κ) = x := by
  show ((IntermediateField.equivOfEq (fieldC_eq_top hNℓ).symm ((eR hNℓ).symm x) : modularFunctionFieldC κ (N * ℓ)) :
    LaurentSeries κ) = x
  rw [coe_equivOfEq, coe_eR_symm]

def legs : Fin 2 → (modularFunctionFieldC κ N →ₐ[κ] modularFunctionFieldC κ (N * ℓ)) :=
  ![(eT hNℓ).toAlgHom.comp (heckeAlphaC κ N ℓ), (eT hNℓ).toAlgHom.comp (heckeBetaC κ N ℓ)]

theorem legs_zero (x : modularFunctionFieldC κ N) : legs hNℓ 0 x = eT hNℓ (heckeAlphaC κ N ℓ x) := rfl
theorem legs_one (x : modularFunctionFieldC κ N) : legs hNℓ 1 x = eT hNℓ (heckeBetaC κ N ℓ x) := rfl

theorem coe_legs_zero (x : modularFunctionFieldC κ N) :
    ((legs hNℓ 0 x : modularFunctionFieldC κ (N * ℓ)) : LaurentSeries κ) = x := by
  rw [legs_zero, coe_eT, coe_heckeAlphaC]

theorem coe_legs_one (x : modularFunctionFieldC κ N) :
    ((legs hNℓ 1 x : modularFunctionFieldC κ (N * ℓ)) : LaurentSeries κ) = qExpand κ ℓ (x : LaurentSeries κ) := by
  rw [legs_one, coe_eT, coe_heckeBetaC]

theorem isIntegral_legs (hα : (heckeAlphaC κ N ℓ).toRingHom.IsIntegral) (hβ : (heckeBetaC κ N ℓ).toRingHom.IsIntegral) :
    ∀ i, (legs hNℓ i).toRingHom.IsIntegral := by
  have h0 : (legs hNℓ 0).toRingHom.IsIntegral := by
    have : (legs hNℓ 0).toRingHom = ((eT hNℓ : charLDegeneracyRoof κ N ℓ →+* _)).comp (heckeAlphaC κ N ℓ).toRingHom := rfl
    rw [this]
    exact RingHom.IsIntegral.trans _ _ hα (RingHom.isIntegral_of_surjective _ (eT hNℓ).surjective)
  have h1 : (legs hNℓ 1).toRingHom.IsIntegral := by
    have : (legs hNℓ 1).toRingHom = ((eT hNℓ : charLDegeneracyRoof κ N ℓ →+* _)).comp (heckeBetaC κ N ℓ).toRingHom := rfl
    rw [this]
    exact RingHom.IsIntegral.trans _ _ hβ (RingHom.isIntegral_of_surjective _ (eT hNℓ).surjective)
  intro i
  fin_cases i
  · exact h0
  · exact h1

theorem transport_refl {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F) :
    transport (AlgEquiv.refl : F ≃ₐ[K] F) v = v := by
  ext1
  exact SetLike.ext fun y => Iff.rfl

theorem ramificationIndexAlong_legs_zero (W : Place κ (charLDegeneracyRoof κ N ℓ)) :
    (transport (eT hNℓ) W).ramificationIndexAlong (legs hNℓ 0) = W.ramificationIndexAlong (heckeAlphaC κ N ℓ) :=
  ramificationIndexAlong_transport (AlgEquiv.refl) (eT hNℓ) (legs hNℓ 0) (heckeAlphaC κ N ℓ) (fun x => rfl) W

theorem ramificationIndexAlong_legs_one (W : Place κ (charLDegeneracyRoof κ N ℓ)) :
    (transport (eT hNℓ) W).ramificationIndexAlong (legs hNℓ 1) = W.ramificationIndexAlong (heckeBetaC κ N ℓ) :=
  ramificationIndexAlong_transport (AlgEquiv.refl) (eT hNℓ) (legs hNℓ 1) (heckeBetaC κ N ℓ) (fun x => rfl) W

theorem restrictAlong_legs_zero (hα : (heckeAlphaC κ N ℓ).toRingHom.IsIntegral) (h0 : (legs hNℓ 0).toRingHom.IsIntegral)
    (W : Place κ (charLDegeneracyRoof κ N ℓ)) :
    (transport (eT hNℓ) W).restrictAlong (legs hNℓ 0) h0 = W.restrictAlong (heckeAlphaC κ N ℓ) hα := by
  rw [restrictAlong_transport (AlgEquiv.refl) (eT hNℓ) (legs hNℓ 0) (heckeAlphaC κ N ℓ) (fun x => rfl) h0 hα,
    transport_refl]

theorem restrictAlong_legs_one (hβ : (heckeBetaC κ N ℓ).toRingHom.IsIntegral) (h1 : (legs hNℓ 1).toRingHom.IsIntegral)
    (W : Place κ (charLDegeneracyRoof κ N ℓ)) :
    (transport (eT hNℓ) W).restrictAlong (legs hNℓ 1) h1 = W.restrictAlong (heckeBetaC κ N ℓ) hβ := by
  rw [restrictAlong_transport (AlgEquiv.refl) (eT hNℓ) (legs hNℓ 1) (heckeBetaC κ N ℓ) (fun x => rfl) h1 hβ,
    transport_refl]

theorem jGeomGen_top : jGeomGen κ (N * ℓ) = eT hNℓ (heckeAlphaC κ N ℓ (jGeomGen κ N)) := by
  apply Subtype.ext
  rw [coe_eT, coe_heckeAlphaC, coe_jGeomGen, coe_jGeomGen]

theorem evalAt_eq_of_ord_sub_pos {K F : Type*} [Field K] [Field F] [Algebra K F]
    (v : Place K F) (f : F) (a : K) (h : 0 < v.ord (f - algebraMap K F a)) :
    v.evalAt f = a := by
  have hne : f - algebraMap K F a ≠ 0 := by
    intro h0
    rw [h0, AlgebraicCurve.Place.ord_zero] at h
    exact lt_irrefl _ h
  have hmem_sub : f - algebraMap K F a ∈ v.toValuationSubring :=
    (ModularCurve.ComapPlace.mem_iff_ord_nonneg v hne).mpr h.le
  have hmem_a : algebraMap K F a ∈ v.toValuationSubring := v.algebraMap_mem' a
  have hmem_f : f ∈ v.toValuationSubring := by
    have := add_mem hmem_sub hmem_a
    simpa using this
  rw [AlgebraicCurve.Place.evalAt_congr v hmem_f hmem_a (Or.inr h), AlgebraicCurve.Place.evalAt_algebraMap]

theorem placeRamificationJ_dvd (h2 : ringChar κ ≠ 2) (h3 : ringChar κ ≠ 3) (E : WeierstrassCurve κ) [E.IsElliptic]
    (Cp : CycSub E (N * ℓ)) :
    placeRamificationJ (N * ℓ) (transport (eT hNℓ) (fPl hNℓ E Cp.1)) ∣
      jWidth ((transport (eT hNℓ) (fPl hNℓ E Cp.1)).evalAt (jGeomGen κ (N * ℓ))) := by
  set V := transport (eT hNℓ) (fPl hNℓ E Cp.1) with hV
  have hord : V.ord (jGeomGen κ (N * ℓ) - algebraMap κ (modularFunctionFieldC κ (N * ℓ)) E.j) =
      (Nat.card {C' : CycSub E (N * ℓ) // fPl hNℓ E C'.1 = fPl hNℓ E Cp.1} : ℤ) := by
    rw [hV, jGeomGen_top hNℓ, ← (eT hNℓ).commutes E.j, ← map_sub, ord_transport]
    exact f4 hNℓ E Cp
  have hpos : 0 < V.ord (jGeomGen κ (N * ℓ) - algebraMap κ (modularFunctionFieldC κ (N * ℓ)) E.j) := by
    rw [hV, jGeomGen_top hNℓ, ← (eT hNℓ).commutes E.j, ← map_sub, ord_transport]
    exact f1 hNℓ E Cp
  have heval : V.evalAt (jGeomGen κ (N * ℓ)) = E.j := evalAt_eq_of_ord_sub_pos V _ _ hpos
  have hram : placeRamificationJ (N * ℓ) V = Nat.card {C' : CycSub E (N * ℓ) // fPl hNℓ E C'.1 = fPl hNℓ E Cp.1} := by
    unfold placeRamificationJ
    rw [heval, hord, Int.toNat_natCast]
  rw [hram, heval]
  exact WeierstrassCurve.natCard_fibre_dvd_jWidth_of_variableChange_orbitMap h2 h3 E (N * ℓ)
    (f := fun C => fPl hNℓ E C.1) (fun H H' => f3 hNℓ E H H') Cp

end RoofC

section Width

variable {κ : Type} [Field κ] [IsAlgClosed κ] [DecidableEq κ]
  (q' : ℕ) [Fact q'.Prime] [CharP κ q'] (hq5 : 5 ≤ q')
  (N ℓ : ℕ) [NeZero N] [NeZero ℓ] (hq'N : ¬ q' ∣ N) (hℓ : ℓ.Prime) (hℓq : ℓ ≠ q')
  (hNℓ : ((N * ℓ : ℕ) : κ) ≠ 0)
  (hα : (heckeAlphaC κ N ℓ).toRingHom.IsIntegral) (hβ : (heckeBetaC κ N ℓ).toRingHom.IsIntegral)

include hq5 hq'N hℓ hℓq in

theorem width_swap (E_y : WeierstrassCurve κ) [E_y.IsElliptic] (C_y : AddSubgroup E_y.toAffine.Point)
    (hCy : IsAddCyclic C_y ∧ Nat.card C_y = N)
    (x y : Place κ (modularFunctionFieldC κ N)) (hgy : gPl hNℓ E_y C_y = y)
    (W : Place κ (charLDegeneracyRoof κ N ℓ))
    (hWx : W.restrictAlong (heckeBetaC κ N ℓ) hβ = x) (hWy : W.restrictAlong (heckeAlphaC κ N ℓ) hα = y) :
    W.ramificationIndexAlong (heckeBetaC κ N ℓ) * placeWidth N y =
      W.ramificationIndexAlong (heckeAlphaC κ N ℓ) * placeWidth N x := by
  have hchar : ringChar κ ≠ 2 ∧ ringChar κ ≠ 3 := by
    have h := ringChar.eq κ q'
    omega

  obtain ⟨Cp, rfl⟩ := exists_of_restrictAlong_eq hNℓ hα E_y ⟨C_y, hCy⟩ W (hWy.trans hgy.symm)
  have hint := isIntegral_legs hNℓ hα hβ
  have hdiv := placeRamificationJ_dvd hNℓ hchar.1 hchar.2 E_y Cp
  have key := fun i => ModularCurve.ramificationIndexAlong_mul_placeWidth_eq_placeWidth_restrictAlong_of_five_le N ℓ q' hℓ
    hq5 hℓq hq'N (legs hNℓ) hint (coe_legs_zero hNℓ) (coe_legs_one hNℓ) i (transport (eT hNℓ) (fPl hNℓ E_y Cp.1)) hdiv
  have E0 := key 0
  have E1 := key 1
  rw [ramificationIndexAlong_legs_zero, restrictAlong_legs_zero hNℓ hα, hWy] at E0
  rw [ramificationIndexAlong_legs_one, restrictAlong_legs_one hNℓ hβ, hWx] at E1
  rw [← E0, ← E1]
  ring

end Width

end ModularCurve.UCurveLevelN
p2m_reactivate "P2MW.S_ModularCurve_ssHeckeMatrixC_apply_eq_natCard_subgroup_dualPair_of_dvd_of_five_le_of_moduliPlace.ModularCurve P2MW.S_ModularCurve_ssHeckeMatrixC_apply_eq_natCard_subgroup_dualPair_of_dvd_of_five_le_of_moduliPlace.ModularCurve.UCurveLevelN"
p2m_reactivate "P2MW.S_ModularCurve_ssHeckeMatrixC_apply_eq_natCard_subgroup_dualPair_of_dvd_of_five_le_of_moduliPlace.ModularCurve"

open ModularCurve.UCurveLevelN in
open Classical in

theorem solution
    {κ : Type} [Field κ] [IsAlgClosed κ] [DecidableEq κ]
    (q' : ℕ) [Fact q'.Prime] [CharP κ q'] (hq5 : 5 ≤ q')
    (N : ℕ) [NeZero N] (hq'N : ¬ q' ∣ N)
    (ℓ : ℕ) [NeZero ℓ] (hℓ : ℓ.Prime) (hℓq : ℓ ≠ q') (hℓN : ℓ ∣ N)
    (hα : (heckeAlphaC κ N ℓ).toRingHom.IsIntegral) (hβ : (heckeBetaC κ N ℓ).toRingHom.IsIntegral)
    (x y : ↥(ssPlaces q' N κ))
    (E_x E_y : WeierstrassCurve κ) [E_x.IsElliptic] [E_y.IsElliptic]
    (C_x : AddSubgroup E_x.toAffine.Point) (C_y : AddSubgroup E_y.toAffine.Point)
    (hCx : IsAddCyclic C_x ∧ Nat.card C_x = N) (hCy : IsAddCyclic C_y ∧ Nat.card C_y = N)
    (hx : (x.1).toValuationSubring = (moduliPlace κ N E_x C_x).toValuationSubring.comap
      (IntermediateField.inclusion (modularFunctionFieldC_le_full κ N)).toRingHom)
    (hy : (y.1).toValuationSubring = (moduliPlace κ N E_y C_y).toValuationSubring.comap
      (IntermediateField.inclusion (modularFunctionFieldC_le_full κ N)).toRingHom) :
    ssHeckeMatrixC q' κ N ℓ hα hβ y x =
      (Nat.card {D : AddSubgroup (E_x.baseChange κ).toAffine.Point //
        Nat.card D = ℓ ∧ ∃ ψ ∈ WeierstrassCurve.rationalHomSet κ E_x E_y, ∃ ψ' ∈ WeierstrassCurve.rationalHomSet κ E_y E_x,
          ψ.ker = D ∧ ψ'.comp ψ = ℓ • AddMonoidHom.id _ ∧ ψ.comp ψ' = ℓ • AddMonoidHom.id _ ∧
          (∀ T ∈ C_x, ψ T ∈ C_y) ∧ ∀ T ∈ C_x, ψ T = 0 → T = 0} : ℤ) := by
  have hq'ℓ : ¬ q' ∣ ℓ := fun h => hℓq ((Nat.prime_dvd_prime_iff_eq (Fact.out) hℓ).mp h).symm
  have hℓ0 : (ℓ : κ) ≠ 0 := fun h => hq'ℓ ((CharP.cast_eq_zero_iff κ q' ℓ).mp h)
  have hN0 : (N : κ) ≠ 0 := fun h => hq'N ((CharP.cast_eq_zero_iff κ q' N).mp h)
  have hNℓ : ((N * ℓ : ℕ) : κ) ≠ 0 := by rw [Nat.cast_mul]; exact mul_ne_zero hN0 hℓ0
  have hgy : gPl hNℓ E_y C_y = y.1 := ((transport_eC_eq_iff hNℓ (moduliPlace κ N E_y C_y) y.1).mpr hy).symm

  have hA := ModularCurve.finsum_ramificationIndexAlong_heckeAlphaC_eq_natCard_overgroup_dualPair_of_moduliPlace
    N ℓ hℓ hNℓ hα hβ x.1 y.1 E_x E_y C_x C_y hCx hCy hx hy

  have hB := WeierstrassCurve.natCard_rationalAut_mul_natCard_overgroup_dualPair_eq_natCard_rationalAut_mul_natCard_subgroup_dualPair
    E_x E_y N ℓ hℓ hℓ0 C_x C_y hCx hCy

  have hwx := ModularCurve.two_mul_placeWidth_eq_natCard_rationalAut_map_eq_of_toValuationSubring_eq_comap_moduliPlace
    q' hq5 N hq'N E_x C_x hCx.1 hCx.2 x.1 hx
  have hwy := ModularCurve.two_mul_placeWidth_eq_natCard_rationalAut_map_eq_of_toValuationSubring_eq_comap_moduliPlace
    q' hq5 N hq'N E_y C_y hCy.1 hCy.2 y.1 hy

  have hentry : ssHeckeMatrixC q' κ N ℓ hα hβ y x =
      ∑ᶠ W : Place κ (charLDegeneracyRoof κ N ℓ),
        if W.restrictAlong (heckeBetaC κ N ℓ) hβ = x.1 ∧ W.restrictAlong (heckeAlphaC κ N ℓ) hα = y.1 then
          (W.ramificationIndexAlong (heckeBetaC κ N ℓ) : ℤ) else 0 := by
    rw [ssHeckeMatrixC, Matrix.of_apply]
    refine finsum_congr fun W => ?_
    rw [inertiaDegAlong_heckeAlphaC_eq_one κ N ℓ hα, Nat.cast_one, mul_one]

  have hmul : (placeWidth N y.1 : ℤ) * ssHeckeMatrixC q' κ N ℓ hα hβ y x =
      (placeWidth N x.1 : ℤ) * ∑ᶠ W : Place κ (charLDegeneracyRoof κ N ℓ),
        if W.restrictAlong (heckeBetaC κ N ℓ) hβ = x.1 ∧ W.restrictAlong (heckeAlphaC κ N ℓ) hα = y.1 then
          (W.ramificationIndexAlong (heckeAlphaC κ N ℓ) : ℤ) else 0 := by
    rw [hentry, ← smul_eq_mul, ← smul_eq_mul, smul_finsum, smul_finsum]
    refine finsum_congr fun W => ?_
    by_cases hW : W.restrictAlong (heckeBetaC κ N ℓ) hβ = x.1 ∧ W.restrictAlong (heckeAlphaC κ N ℓ) hα = y.1
    · rw [if_pos hW, if_pos hW, smul_eq_mul, smul_eq_mul]
      have h := width_swap q' hq5 N ℓ hq'N hℓ hℓq hNℓ hα hβ E_y C_y hCy x.1 y.1 hgy W hW.1 hW.2
      have h' := congrArg (fun n : ℕ => (n : ℤ)) h
      push_cast at h'
      linarith [h']
    · rw [if_neg hW, if_neg hW, smul_zero, smul_zero]
  rw [hA] at hmul

  have hfin := WeierstrassCurve.finite_rationalHomSet_units (F := κ) κ E_y
  have hSypos : 0 < Nat.card {ι : E_y.toAffine.Point →+ E_y.toAffine.Point //
        ι ∈ WeierstrassCurve.rationalHomSet κ E_y E_y ∧
        (∃ ι' ∈ WeierstrassCurve.rationalHomSet κ E_y E_y, ι'.comp ι = AddMonoidHom.id _ ∧ ι.comp ι' = AddMonoidHom.id _) ∧
        C_y.map ι = C_y} := by
    haveI : Finite {u : E_y.toAffine.Point →+ E_y.toAffine.Point |
        u ∈ WeierstrassCurve.rationalHomSet κ E_y E_y ∧
        ∃ v ∈ WeierstrassCurve.rationalHomSet κ E_y E_y, u.comp v = AddMonoidHom.id _ ∧ v.comp u = AddMonoidHom.id _} :=
      hfin.to_subtype
    haveI : Finite {ι : E_y.toAffine.Point →+ E_y.toAffine.Point //
        ι ∈ WeierstrassCurve.rationalHomSet κ E_y E_y ∧
        (∃ ι' ∈ WeierstrassCurve.rationalHomSet κ E_y E_y, ι'.comp ι = AddMonoidHom.id _ ∧ ι.comp ι' = AddMonoidHom.id _) ∧
        C_y.map ι = C_y} := by
      refine Finite.of_injective (β := {u : E_y.toAffine.Point →+ E_y.toAffine.Point |
        u ∈ WeierstrassCurve.rationalHomSet κ E_y E_y ∧
        ∃ v ∈ WeierstrassCurve.rationalHomSet κ E_y E_y, u.comp v = AddMonoidHom.id _ ∧ v.comp u = AddMonoidHom.id _})
        (fun ι => ⟨ι.1, ι.2.1, by obtain ⟨ι', h1, h2, h3⟩ := ι.2.2.1; exact ⟨ι', h1, h3, h2⟩⟩) ?_
      intro a b h
      apply Subtype.ext
      have := congrArg Subtype.val h
      exact this
    haveI : Nonempty {ι : E_y.toAffine.Point →+ E_y.toAffine.Point //
        ι ∈ WeierstrassCurve.rationalHomSet κ E_y E_y ∧
        (∃ ι' ∈ WeierstrassCurve.rationalHomSet κ E_y E_y, ι'.comp ι = AddMonoidHom.id _ ∧ ι.comp ι' = AddMonoidHom.id _) ∧
        C_y.map ι = C_y} :=
      ⟨⟨AddMonoidHom.id _, WeierstrassCurve.id_mem_rationalHomSet κ E_y,
        ⟨AddMonoidHom.id _, WeierstrassCurve.id_mem_rationalHomSet κ E_y, rfl, rfl⟩, AddSubgroup.map_id C_y⟩⟩
    exact Nat.card_pos
  have hwy0 : (placeWidth N y.1 : ℤ) ≠ 0 := by
    have h2 : 2 * placeWidth N y.1 ≠ 0 := by rw [hwy]; exact hSypos.ne'
    exact_mod_cast fun h => h2 (by rw [h])

  have key : (2 * placeWidth N y.1 : ℤ) * ssHeckeMatrixC q' κ N ℓ hα hβ y x =
      (2 * placeWidth N y.1 : ℤ) * (Nat.card {D : AddSubgroup (E_x.baseChange κ).toAffine.Point //
        Nat.card D = ℓ ∧ ∃ ψ ∈ WeierstrassCurve.rationalHomSet κ E_x E_y, ∃ ψ' ∈ WeierstrassCurve.rationalHomSet κ E_y E_x,
          ψ.ker = D ∧ ψ'.comp ψ = ℓ • AddMonoidHom.id _ ∧ ψ.comp ψ' = ℓ • AddMonoidHom.id _ ∧
          (∀ T ∈ C_x, ψ T ∈ C_y) ∧ ∀ T ∈ C_x, ψ T = 0 → T = 0} : ℤ) := by
    have hBz := congrArg (fun n : ℕ => (n : ℤ)) hB
    have hwxz := congrArg (fun n : ℕ => (n : ℤ)) hwx
    have hwyz := congrArg (fun n : ℕ => (n : ℤ)) hwy
    push_cast at hBz hwxz hwyz
    rw [mul_assoc, hmul, ← mul_assoc, hwxz, hBz, ← hwyz]
  exact mul_left_cancel₀ (mul_ne_zero two_ne_zero hwy0) key

end
p2m_reactivate "P2MW.S_ModularCurve_ssHeckeMatrixC_apply_eq_natCard_subgroup_dualPair_of_dvd_of_five_le_of_moduliPlace.ModularCurve P2MW.S_ModularCurve_ssHeckeMatrixC_apply_eq_natCard_subgroup_dualPair_of_dvd_of_five_le_of_moduliPlace.ModularCurve.UCurveLevelN"

end S_ModularCurve_ssHeckeMatrixC_apply_eq_natCard_subgroup_dualPair_of_dvd_of_five_le_of_moduliPlace
end P2MW
export P2MW.S_ModularCurve_ssHeckeMatrixC_apply_eq_natCard_subgroup_dualPair_of_dvd_of_five_le_of_moduliPlace (solution)
