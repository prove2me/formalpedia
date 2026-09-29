-- Prove2me | solution 1 for ModularCurve.ramificationIndexAlong_heckeAlphaC_mul_placeRamificationJ_eq_jWidthChar_of_restrictAlong_ne_of_prime
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/5e549a28-57e3-507e-8e43-b3de99ff98a2

import Definitions.Def_ModularCurve_CharLDegeneracyHecke
import Definitions.Def_ModularCurve_PlaceWidthChar
import Definitions.Def_ModularCurve_CharLSpecialFibreLevelNDictionary
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Theorems.Thm_ModularCurve_charLDegeneracyRoof_eq_modularFunctionFieldFullC_mul
import Theorems.Thm_ModularCurve_modularFunctionFieldC_eq_modularFunctionFieldFullC
import Theorems.Thm_ModularCurve_ramificationIndexAlong_mul_placeWidthChar_eq_placeWidthChar_restrictAlong_degeneracyPair
import Theorems.Thm_ModularCurve_ramificationIndexAlong_mul_placeWidth_eq_placeWidth_restrictAlong
import Theorems.Thm_ModularCurve_degeneracyPair_finiteSeparableDeg_ssPlaces_preserved_reflected
import Theorems.Thm_ModularCurve_degeneracyPair_finrankAlong_and_place_transports
import Theorems.Thm_AlgebraicCurve_Place_isRational_iff_deg_eq_one
import Theorems.Thm_ModularCurve_place_deg_eq_one_of_isAlgClosed
import Theorems.Thm_ModularCurve_isAffineGeomPlace_or_ord_jGeomGen_lt_zero
import Theorems.Thm_ModularCurve_zero_mem_ssJSet_of_lt_five
import Theorems.Thm_ModularCurve_ord_jGeomGen_sub_algebraMap_eq_one_of_evalAt_eq
import Theorems.Thm_ModularCurve_placeRamificationJ_dvd_jWidth_of_ord_pos
import Theorems.Thm_ModularCurve_placeRamificationJ_dvd_jWidthChar_two_of_mem_ssPlaces
import Theorems.Thm_ModularCurve_placeRamificationJ_dvd_jWidthChar_three_of_mem_ssPlaces
import Theorems.Thm_ModularCurve_placeWidthChar_eq_one_of_restrictAlong_ne
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_ramificationIndexAlong_heckeAlphaC_mul_placeRamificationJ_eq_jWidthChar_of_restrictAlong_ne_of_prime
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular ModularCurve.instSMulAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instDistribMulActionAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent ModularCurve.B3.instIsElliptic_goodModel ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois WeierstrassCurve.Affine.instIsDiscreteValuationRingSubtypeFunctionFieldMemValuationSubringValuationSubringWithZeroMultiplicativeIntValuationInfty WeierstrassCurve.Affine.valuationInfty_isNontrivial WeierstrassCurve.veluQuotient2_isShortNF WeierstrassCurve.instIsShortNFMk ModularCurve.ModuliTestDatum.isElliptic_reduced ModularCurve.ModuliTestDatum.isElliptic_curve ModularCurve.ModuliTestDatum.isElliptic_generic ModularCurve.instIsElliptic_tateBase CyclotomicUniv.instCharZeroR₀ CyclotomicUniv.instIsDomain CyclotomicUniv.instIsDomainR₀"
p2m_attr_erase "instance" "CyclotomicUniv.instCharZero ModularCurve.KatzGamma0Form.instModule ModularCurve.KatzGamma0Form.instZero ModularCurve.KatzLevelPForm.instSMul ModularCurve.KatzGamma0Form.instAdd ModularCurve.KatzLevelPForm.instAddCommGroup ModularCurve.KatzGamma0Form.instNeg ModularCurve.KatzGamma0Form.instAddCommGroup ModularCurve.KatzLevelPForm.instAdd ModularCurve.KatzLevelPForm.instSub ModularCurve.KatzLevelPForm.instNeg ModularCurve.KatzGamma0Form.instSMul ModularCurve.KatzGamma0Form.instSub ModularCurve.KatzLevelPForm.instZero ModularCurve.KatzLevelPForm.instModule KatzModularForm.instAddCommGroup KatzModularForm.instSub KatzModularForm.instZero KatzModularForm.instModule KatzModularForm.instAdd KatzModularForm.instNeg KatzModularForm.instSMul"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty"
p2m_attr_erase "simp" "WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂"
p2m_attr_erase "simp" "Param.B.sizeOf_spec compl₂EDS_two ModularCurve.ProjectiveLine.map_mk WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂"
p2m_attr_erase "simp" "PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero"
p2m_attr_erase "simp" "TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar ModularCurve.baseAut_arithmeticGalois ModularCurve.JZero.torsionGaloisRep_apply ModularCurve.coe_arithmeticRingAut_apply ModularCurve.toRingAut_arithmeticGalois AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty"
p2m_attr_erase "simp" "AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularCurve.CharPReduction.coeffRed_coeff ModularCurve.CharPReduction.redLocHom_apply WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply ModularCurve.coe_cuspidalDivisor₀ ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.mapPointHom_apply WeierstrassCurve.mapPoint_zero WeierstrassCurve.Universal.halveX_zero WeierstrassCurve.Universal.specialize_X_one WeierstrassCurve.Universal.coeff_halve"
p2m_attr_erase "simp" "WeierstrassCurve.Universal.specialize_X_two WeierstrassCurve.Universal.halveCoeff_zero WeierstrassCurve.Universal.specialize_X_four WeierstrassCurve.Universal.coeff_halveX WeierstrassCurve.Universal.specialize_X_three WeierstrassCurve.Universal.specialize_X_zero ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ AddMonoid.End.dualEndDataOfSurjective_trace AddMonoid.End.dualEndDataOfSurjective_norm ModularCurve.ComapPlace.place_toValuationSubring ModularCurve.ModuliTestDatum.restrictLevel_emb ModularCurve.ModuliTestDatum.restrictLevel_res ModularCurve.ModuliTestDatum.mk.injEq ModularCurve.ModuliTestDatum.restrictLevel_W ModularCurve.ModuliTestDatum.place_toValuationSubring ModularCurve.ModuliTestDatum.restrictLevel_curve ModularCurve.ModuliTestDatum.resEquiv_apply ModularCurve.ModuliTestDatum.restrictLevel_gen ModularCurve.ModuliTestDatum.mk.sizeOf_spec ModularCurve.coe_jqNFull ModularCurve.Gamma0Pair.map_toCurve WeierstrassCurve.mapPoint_eq_ratPointMap ModularCurve.Gamma0Pair.map_gen ModularCurve.Gamma0Pair.map_eq_gamma0PairMap ModularCurve.ModuliPoint.map_eq_moduliPointMapRingHom ModularCurve.ModuliPoint.map_mk ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst"
p2m_attr_erase "simp" "ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst CyclotomicUniv.lift₀_ζ₀ CyclotomicUniv.lift_algebraMap CyclotomicUniv.val_ζUnit CyclotomicUniv.lift_ζ ModularCurve.cuspData_yP ModularCurve.qTwistAlgHom_apply ModularCurve.cuspData_yQ ModularCurve.cuspData_xP ModularCurve.cuspData_xQ ModularCurve.val_cyclZeta ModularCurve.cuspShift_one ModularCurve.cuspShift_zero ModularCurve.LevelPData.mk.sizeOf_spec ModularCurve.KatzLevelPForm.neg_toFun ModularCurve.LevelP.coe_swapW ModularCurve.KatzLevelPForm.swap_swap KatzModularForm.pullbackLevelP_toFun ModularCurve.LevelPData.swap_xQ KatzModularForm.pullbackLevelP_zero ModularCurve.LevelPData.map_yP ModularCurve.KatzLevelPForm.swap_neg ModularCurve.KatzGamma0Form.toKatzLevelPForm_sub ModularCurve.KatzLevelPForm.swap_add KatzModularForm.swap_pullbackLevelP ModularCurve.KatzGamma0Form.toKatzLevelPForm_add ModularCurve.KatzLevelPForm.swap_smul ModularCurve.LevelPData.map_yQ ModularCurve.KatzLevelPForm.mk.injEq ModularCurve.KatzLevelPForm.zero_toFun KatzModularForm.pullbackLevelP_smul ModularCurve.LevelPData.swap_xP ModularCurve.KatzGamma0Form.toKatzLevelPForm_mul ModularCurve.KatzGamma0Form.toKatzLevelPForm_neg ModularCurve.LevelPData.variableChange_xQ KatzModularForm.pullbackGamma0_toKatzLevelPForm"
p2m_attr_erase "simp" "ModularCurve.KatzLevelPForm.mk.sizeOf_spec ModularCurve.KatzLevelPForm.swap_zero ModularCurve.LevelP.coe_unipotentU ModularCurve.KatzLevelPForm.mul_toFun ModularCurve.LevelPData.variableChange_yP ModularCurve.LevelPData.mk.injEq ModularCurve.KatzLevelPForm.sub_toFun ModularCurve.LevelPData.variableChange_xP ModularCurve.KatzLevelPForm.smul_toFun ModularCurve.LevelPData.swap_yP ModularCurve.LevelPData.map_xP ModularCurve.LevelPData.swap_swap ModularCurve.LevelPData.swap_yQ ModularCurve.KatzGamma0Form.toKatzLevelPForm_zero ModularCurve.KatzGamma0Form.mk.injEq ModularCurve.KatzLevelPForm.swap_toFun KatzModularForm.pullbackLevelP_add ModularCurve.KatzGamma0Form.mk.sizeOf_spec ModularCurve.LevelPData.variableChange_yQ ModularCurve.KatzLevelPForm.swap_sub ModularCurve.KatzGamma0Form.toKatzLevelPForm_smul ModularCurve.LevelPData.map_xQ ModularCurve.KatzLevelPForm.add_toFun KatzModularForm.c₆_toFun KatzModularForm.neg_toFun KatzModularForm.mul_toFun KatzModularForm.qExpansion_neg KatzModularForm.discr_toFun KatzModularForm.qExpansion_sub KatzModularForm.qExpansion_add KatzModularForm.qExpansion_mul KatzModularForm.zero_toFun KatzModularForm.mk.injEq KatzModularForm.qExpansion_smul KatzModularForm.smul_toFun KatzModularForm.add_toFun KatzModularForm.sub_toFun KatzModularForm.c₄_toFun KatzModularForm.qExpansion_zero KatzModularForm.mk.sizeOf_spec"
p2m_attr_erase "simp" "TateCurve.tateTorsionPoint_zero_zero WeierstrassCurve.pointAddEquivOfEq_refl"
set_option autoImplicit false
open AlgebraicCurve ModularCurve

private theorem placeRamificationJ_eq_zero_of_not_isAffineGeomPlace
    {k : Type*} [Field k] (N : ℕ) [NeZero N]
    (p : Place k ↥(modularFunctionFieldC k N)) (hp : ¬ IsAffineGeomPlace k N p) :
    placeRamificationJ N p = 0 := by
  have hpole : p.ord (jGeomGen k N) < 0 :=
    (isAffineGeomPlace_or_ord_jGeomGen_lt_zero k N p).resolve_left hp
  have hneg : p.ord (jGeomGen k N - algebraMap k (modularFunctionFieldC k N) (p.evalAt (jGeomGen k N))) < 0 := by
    by_contra hcon
    push Not at hcon
    have hmem := p.mem_of_ord_nonneg (jGeomGen_sub_algebraMap_ne_zero k N _) hcon
    have hj : jGeomGen k N ∈ p.toValuationSubring := by
      have := add_mem hmem (p.algebraMap_mem' (p.evalAt (jGeomGen k N)))
      simpa using this
    exact absurd (p.ord_nonneg_of_mem hj) (not_le.mpr hpole)
  unfold placeRamificationJ
  omega

private theorem isRational_of_isAlgClosed
    {k : Type*} [Field k] [IsAlgClosed k] {N : ℕ} [NeZero N] (p : Place k ↥(modularFunctionFieldC k N)) :
    p.IsRational :=
  (Place.isRational_iff_deg_eq_one p).mpr (place_deg_eq_one_of_isAlgClosed k N p)

private theorem placeRamificationJ_pos_of_isAffineGeomPlace
    {k : Type*} [Field k] [IsAlgClosed k] (N : ℕ) [NeZero N]
    (p : Place k ↥(modularFunctionFieldC k N)) (hp : IsAffineGeomPlace k N p) :
    0 < placeRamificationJ N p := by
  have h := ord_sub_evalAt_pos_of_isRational (isRational_of_isAlgClosed p) hp.1
    (jGeomGen_sub_algebraMap_ne_zero k N _)
  unfold placeRamificationJ
  omega

private theorem wild_data_of_not_mem_ssPlaces
    (M s q' : ℕ) [NeZero M] [NeZero s] (hs : s.Prime) [Fact q'.Prime]
    (hsq' : s ≠ q') (hq'M : ¬ q' ∣ M) (hsM : ¬ s ∣ M) (hq5 : q' < 5)
    {k : Type*} [Field k] [CharP k q'] [IsAlgClosed k] [DecidableEq k]
    (hjw : ∀ j : k, j ≠ 0 → jWidthChar q' j = 1) (h1728 : (1728 : k) = 0)
    (φ : Fin 2 → (↥(modularFunctionFieldC k M) →ₐ[k] ↥(modularFunctionFieldC k (M * s))))
    (hφ : ∀ i, (φ i).toRingHom.IsIntegral)
    (hφα : ∀ x, ((φ 0 x : ↥(modularFunctionFieldC k (M * s))) : LaurentSeries k) = x)
    (hφβ : ∀ x, ((φ 1 x : ↥(modularFunctionFieldC k (M * s))) : LaurentSeries k) = qExpand k s x)
    (p : Place k ↥(modularFunctionFieldC k (M * s)))
    (haff : IsAffineGeomPlace k (M * s) p) (hss : p ∉ ssPlaces q' (M * s) k) :
    (∀ i : Fin 2, placeRamificationJ M (p.restrictAlong (φ i) (hφ i)) = 1) ∧
    (∀ i : Fin 2, jWidthChar q' ((p.restrictAlong (φ i) (hφ i)).evalAt (jGeomGen k M)) = 1) ∧
    (∀ i : Fin 2, p.ramificationIndexAlong (φ i) = 1) := by
  have hq : q'.Prime := Fact.out
  have hq'Ms : ¬ q' ∣ M * s := fun h =>
    ((Nat.Prime.dvd_mul hq).mp h).elim hq'M fun h' => hsq' ((Nat.prime_dvd_prime_iff_eq hq hs).mp h').symm

  have hrest_aff : ∀ i : Fin 2, IsAffineGeomPlace k M (p.restrictAlong (φ i) (hφ i)) := fun i =>
    ((degeneracyPair_finrankAlong_and_place_transports M s q' hs hsq' hq'M hsM φ hφ hφα hφβ).2.2.1 i p).mpr haff
  have hrest_nss : ∀ i : Fin 2, p.restrictAlong (φ i) (hφ i) ∉ ssPlaces q' M k := fun i h =>
    hss ((degeneracyPair_finiteSeparableDeg_ssPlaces_preserved_reflected M s q' hs hsq' hq'M hsM
      φ hφ hφα hφβ).2.2.2.2 i _ h p rfl)

  have hjne : ∀ {L : ℕ} [NeZero L] (w : Place k ↥(modularFunctionFieldC k L)),
      IsAffineGeomPlace k L w → w ∉ ssPlaces q' L k → w.evalAt (jGeomGen k L) ≠ 0 := by
    intro L _ w hw hwss hj
    apply hwss
    show IsSupersingularPlace q' L k w
    refine ⟨isRational_of_isAlgClosed w, hw, ?_⟩
    rw [hj]
    exact zero_mem_ssJSet_of_lt_five hq5

  have hindex : ∀ {L : ℕ} [NeZero L] (hL : ¬ q' ∣ L) (w : Place k ↥(modularFunctionFieldC k L)),
      IsAffineGeomPlace k L w → w ∉ ssPlaces q' L k → placeRamificationJ L w = 1 := by
    intro L _ hL w hw hwss
    have hne := hjne w hw hwss
    have h := ord_jGeomGen_sub_algebraMap_eq_one_of_evalAt_eq q' k L hL w _ rfl hne (by rw [h1728]; exact hne)
    unfold placeRamificationJ
    rw [h]
    rfl
  have hp1 := hindex hq'Ms p haff hss
  have hr1 : ∀ i : Fin 2, placeRamificationJ M (p.restrictAlong (φ i) (hφ i)) = 1 := fun i =>
    hindex hq'M _ (hrest_aff i) (hrest_nss i)

  have hjw' : ∀ {L : ℕ} [NeZero L] (w : Place k ↥(modularFunctionFieldC k L)),
      w.evalAt (jGeomGen k L) ≠ 0 → jWidth (w.evalAt (jGeomGen k L)) = 1 := by
    intro L _ w hw
    apply jWidth_of_ne hw
    rw [h1728]
    exact hw
  refine ⟨hr1, fun i => hjw _ (hjne _ (hrest_aff i) (hrest_nss i)), fun i => ?_⟩
  have h := ramificationIndexAlong_mul_placeWidth_eq_placeWidth_restrictAlong M s q' hs hsq' hq'M
    φ hφ hφα hφβ i p (by rw [hp1]; exact one_dvd _)
  unfold placeWidth at h
  rw [hp1, hr1 i, hjw' p (hjne p haff hss), hjw' _ (hjne _ (hrest_aff i) (hrest_nss i))] at h
  simpa using h

private theorem not_dvd_mul_of_pair {M s q' : ℕ} (hs : s.Prime) (hp : q'.Prime)
    (hsq' : s ≠ q') (hq'M : ¬ q' ∣ M) : ¬ q' ∣ M * s := by
  intro h
  rcases (Nat.Prime.dvd_mul hp).mp h with h | h
  · exact hq'M h
  · exact hsq' ((Nat.prime_dvd_prime_iff_eq hp hs).mp h).symm

private theorem tame_arm
    (M s q' : ℕ) [NeZero M] [NeZero s] (hs : s.Prime) [Fact q'.Prime]
    (hsq' : s ≠ q') (hq'M : ¬ q' ∣ M)
    {k : Type*} [Field k] [CharP k q'] [IsAlgClosed k] [DecidableEq k]
    (φ : Fin 2 → (↥(modularFunctionFieldC k M) →ₐ[k] ↥(modularFunctionFieldC k (M * s))))
    (hφ : ∀ i, (φ i).toRingHom.IsIntegral)
    (hA : ∀ x, ((φ 0 x : ↥(modularFunctionFieldC k (M * s))) : LaurentSeries k) = x)
    (hB : ∀ x, ((φ 1 x : ↥(modularFunctionFieldC k (M * s))) : LaurentSeries k) = qExpand k s x)
    (y : Place k ↥(modularFunctionFieldC k (M * s)))
    (hr : 0 < placeRamificationJ M (Place.restrictAlong (φ 0) (hφ 0) y))
    (hw1 : placeWidthChar q' (M * s) y = 1)
    (hyMs : 0 < placeRamificationJ (M * s) y) (hq5 : 5 ≤ q') :
    y.ramificationIndexAlong (φ 0) * placeRamificationJ M (Place.restrictAlong (φ 0) (hφ 0) y)
      = jWidthChar q' ((Place.restrictAlong (φ 0) (hφ 0) y).evalAt (jGeomGen k M)) := by
  have hq'Ms : ¬ q' ∣ M * s := not_dvd_mul_of_pair hs Fact.out hsq' hq'M
  have hdivMs : placeRamificationJ (M * s) y ∣ jWidth (y.evalAt (jGeomGen k (M * s))) :=
    placeRamificationJ_dvd_jWidth_of_ord_pos hq5 hq'Ms hyMs
  have h2 := ramificationIndexAlong_mul_placeWidth_eq_placeWidth_restrictAlong M s q' hs hsq' hq'M
    φ hφ hA hB 0 y hdivMs
  have hpw : placeWidth (M * s) y = 1 := by
    rw [← placeWidthChar_of_five_le hq5]
    exact hw1
  rw [hpw, mul_one] at h2
  have hdvdM : placeRamificationJ M (Place.restrictAlong (φ 0) (hφ 0) y)
      ∣ jWidth ((Place.restrictAlong (φ 0) (hφ 0) y).evalAt (jGeomGen k M)) :=
    placeRamificationJ_dvd_jWidth_of_ord_pos hq5 hq'M hr
  calc y.ramificationIndexAlong (φ 0) * placeRamificationJ M (Place.restrictAlong (φ 0) (hφ 0) y)
      = placeWidth M (Place.restrictAlong (φ 0) (hφ 0) y)
          * placeRamificationJ M (Place.restrictAlong (φ 0) (hφ 0) y) := by rw [h2]
    _ = jWidth ((Place.restrictAlong (φ 0) (hφ 0) y).evalAt (jGeomGen k M)) := Nat.div_mul_cancel hdvdM
    _ = jWidthChar q' ((Place.restrictAlong (φ 0) (hφ 0) y).evalAt (jGeomGen k M)) :=
          (jWidthChar_of_five_le hq5 _).symm

private theorem ss_arm
    (M s q' : ℕ) [NeZero M] [NeZero s] (hs : s.Prime) [Fact q'.Prime]
    (hsq' : s ≠ q') (hq'M : ¬ q' ∣ M) (hsM : ¬ s ∣ M)
    {k : Type*} [Field k] [CharP k q'] [IsAlgClosed k] [DecidableEq k]
    (φ : Fin 2 → (↥(modularFunctionFieldC k M) →ₐ[k] ↥(modularFunctionFieldC k (M * s))))
    (hφ : ∀ i, (φ i).toRingHom.IsIntegral)
    (hA : ∀ x, ((φ 0 x : ↥(modularFunctionFieldC k (M * s))) : LaurentSeries k) = x)
    (hB : ∀ x, ((φ 1 x : ↥(modularFunctionFieldC k (M * s))) : LaurentSeries k) = qExpand k s x)
    (y : Place k ↥(modularFunctionFieldC k (M * s)))
    (hw1 : placeWidthChar q' (M * s) y = 1)
    (hq5 : q' < 5) (hss : y ∈ ssPlaces q' (M * s) k) :
    y.ramificationIndexAlong (φ 0) * placeRamificationJ M (Place.restrictAlong (φ 0) (hφ 0) y)
      = jWidthChar q' ((Place.restrictAlong (φ 0) (hφ 0) y).evalAt (jGeomGen k M)) := by
  have hp : q'.Prime := Fact.out
  have hpres := (degeneracyPair_finiteSeparableDeg_ssPlaces_preserved_reflected M s q' hs hsq' hq'M hsM
    φ hφ hA hB).2.2.2.1
  have h8 := ramificationIndexAlong_mul_placeWidthChar_eq_placeWidthChar_restrictAlong_degeneracyPair
    M s q' hs hsq' hq'M
    (fun i (v : ↥(ssPlaces q' (M * s) k)) => ⟨Place.restrictAlong (φ i) (hφ i) v, hpres i v v.2⟩)
    (fun i (v : ↥(ssPlaces q' (M * s) k)) => Place.ramificationIndexAlong (φ i) v)
    φ hφ hA hB (fun _ _ => rfl) (fun _ _ => rfl)
  have h0 := h8 0 ⟨y, hss⟩
  dsimp only at h0
  rw [hw1, mul_one] at h0

  have hsst : Place.restrictAlong (φ 0) (hφ 0) y ∈ ssPlaces q' M k := hpres 0 y hss
  have hdvdM : placeRamificationJ M (Place.restrictAlong (φ 0) (hφ 0) y)
      ∣ jWidthChar q' ((Place.restrictAlong (φ 0) (hφ 0) y).evalAt (jGeomGen k M)) := by
    have h4 : q' ≠ 4 := fun h => by subst h; exact absurd hp (by decide)
    have h2 := hp.two_le
    obtain rfl | rfl : q' = 2 ∨ q' = 3 := by omega
    · exact placeRamificationJ_dvd_jWidthChar_two_of_mem_ssPlaces hq'M hsst
    · exact placeRamificationJ_dvd_jWidthChar_three_of_mem_ssPlaces hq'M hsst
  calc y.ramificationIndexAlong (φ 0) * placeRamificationJ M (Place.restrictAlong (φ 0) (hφ 0) y)
      = placeWidthChar q' M (Place.restrictAlong (φ 0) (hφ 0) y)
          * placeRamificationJ M (Place.restrictAlong (φ 0) (hφ 0) y) := by rw [h0]
    _ = jWidthChar q' ((Place.restrictAlong (φ 0) (hφ 0) y).evalAt (jGeomGen k M)) :=
          Nat.div_mul_cancel hdvdM

private theorem wild_arm
    (M s q' : ℕ) [NeZero M] [NeZero s] (hs : s.Prime) [Fact q'.Prime]
    (hsq' : s ≠ q') (hq'M : ¬ q' ∣ M) (hsM : ¬ s ∣ M)
    {k : Type*} [Field k] [CharP k q'] [IsAlgClosed k] [DecidableEq k]
    (φ : Fin 2 → (↥(modularFunctionFieldC k M) →ₐ[k] ↥(modularFunctionFieldC k (M * s))))
    (hφ : ∀ i, (φ i).toRingHom.IsIntegral)
    (hA : ∀ x, ((φ 0 x : ↥(modularFunctionFieldC k (M * s))) : LaurentSeries k) = x)
    (hB : ∀ x, ((φ 1 x : ↥(modularFunctionFieldC k (M * s))) : LaurentSeries k) = qExpand k s x)
    (y : Place k ↥(modularFunctionFieldC k (M * s)))
    (haff : IsAffineGeomPlace k (M * s) y) (hq5 : q' < 5) (hss : y ∉ ssPlaces q' (M * s) k) :
    y.ramificationIndexAlong (φ 0) * placeRamificationJ M (Place.restrictAlong (φ 0) (hφ 0) y)
      = jWidthChar q' ((Place.restrictAlong (φ 0) (hφ 0) y).evalAt (jGeomGen k M)) := by
  have hp : q'.Prime := Fact.out
  have hjw : ∀ j : k, j ≠ 0 → jWidthChar q' j = 1 := by
    have h4 : q' ≠ 4 := fun h => by subst h; exact absurd hp (by decide)
    have h2 := hp.two_le
    obtain rfl | rfl : q' = 2 ∨ q' = 3 := by omega
    · exact fun j hj => jWidthChar_two_of_ne_zero hj
    · exact fun j hj => jWidthChar_three_of_ne_zero hj
  have h1728 : (1728 : k) = 0 := by
    have h4 : q' ≠ 4 := fun h => by subst h; exact absurd hp (by decide)
    have h2 := hp.two_le
    obtain rfl | rfl : q' = 2 ∨ q' = 3 := by omega
    · exact_mod_cast (CharP.cast_eq_zero_iff k 2 1728).mpr (by norm_num)
    · exact_mod_cast (CharP.cast_eq_zero_iff k 3 1728).mpr (by norm_num)
  have hdata := wild_data_of_not_mem_ssPlaces M s q' hs hsq' hq'M hsM hq5 hjw h1728
    φ hφ hA hB y haff hss
  obtain ⟨hr1, hj1, he1⟩ := hdata
  rw [he1 0, hr1 0, hj1 0]

private theorem main_of_pair
    (M s q' : ℕ) [NeZero M] [NeZero s] (hs : s.Prime) [Fact q'.Prime]
    (hsq' : s ≠ q') (hq'M : ¬ q' ∣ M) (hsM : ¬ s ∣ M)
    {k : Type*} [Field k] [CharP k q'] [IsAlgClosed k] [DecidableEq k]
    (φ : Fin 2 → (↥(modularFunctionFieldC k M) →ₐ[k] ↥(modularFunctionFieldC k (M * s))))
    (hφ : ∀ i, (φ i).toRingHom.IsIntegral)
    (hA : ∀ x, ((φ 0 x : ↥(modularFunctionFieldC k (M * s))) : LaurentSeries k) = x)
    (hB : ∀ x, ((φ 1 x : ↥(modularFunctionFieldC k (M * s))) : LaurentSeries k) = qExpand k s x)
    (y : Place k ↥(modularFunctionFieldC k (M * s)))
    (hne : Place.restrictAlong (φ 1) (hφ 1) y ≠ Place.restrictAlong (φ 0) (hφ 0) y)
    (hr : 0 < placeRamificationJ M (Place.restrictAlong (φ 0) (hφ 0) y)) :
    y.ramificationIndexAlong (φ 0) * placeRamificationJ M (Place.restrictAlong (φ 0) (hφ 0) y)
      = jWidthChar q' ((Place.restrictAlong (φ 0) (hφ 0) y).evalAt (jGeomGen k M)) := by

  have htr := (degeneracyPair_finrankAlong_and_place_transports M s q' hs hsq' hq'M hsM φ hφ hA hB).2.2.1
  have hafft : IsAffineGeomPlace k M (Place.restrictAlong (φ 0) (hφ 0) y) := by
    by_contra h
    have h0 := placeRamificationJ_eq_zero_of_not_isAffineGeomPlace M _ h
    omega
  have haff : IsAffineGeomPlace k (M * s) y := (htr 0 y).mp hafft
  have hyMs : 0 < placeRamificationJ (M * s) y := placeRamificationJ_pos_of_isAffineGeomPlace (M * s) y haff

  have hw1 : placeWidthChar q' (M * s) y = 1 :=
    placeWidthChar_eq_one_of_restrictAlong_ne M s q' hs hsq' hq'M hsM φ hφ hA hB y hne hyMs
  by_cases hq5 : 5 ≤ q'
  · exact tame_arm M s q' hs hsq' hq'M φ hφ hA hB y hr hw1 hyMs hq5
  · have hq5' : q' < 5 := by omega
    by_cases hss : y ∈ ssPlaces q' (M * s) k
    · exact ss_arm M s q' hs hsq' hq'M hsM φ hφ hA hB y hw1 hq5' hss
    · exact wild_arm M s q' hs hsq' hq'M hsM φ hφ hA hB y haff hq5' hss

theorem solution
    (M s q' : ℕ) [NeZero M] [NeZero s] (hs : s.Prime) [Fact q'.Prime]
    (hsq' : s ≠ q') (hq'M : ¬ q' ∣ M) (hsM : ¬ s ∣ M)
    {k : Type*} [Field k] [CharP k q'] [IsAlgClosed k] [DecidableEq k]
    (hα : HeckeAlphaCIntegral k M s) (hβ : HeckeBetaCIntegral k M s)
    (y : Place k ↥(charLDegeneracyRoof k M s))
    (hne : y.restrictAlong (heckeBetaC k M s) hβ ≠ y.restrictAlong (heckeAlphaC k M s) hα)
    (hr : 0 < placeRamificationJ M (y.restrictAlong (heckeAlphaC k M s) hα)) :
    y.ramificationIndexAlong (heckeAlphaC k M s)
        * placeRamificationJ M (y.restrictAlong (heckeAlphaC k M s) hα)
      = jWidthChar q' ((y.restrictAlong (heckeAlphaC k M s) hα).evalAt (jGeomGen k M)) := by
  have hq'Ms : ¬ q' ∣ M * s := not_dvd_mul_of_pair hs Fact.out hsq' hq'M

  have hroof : charLDegeneracyRoof k M s = modularFunctionFieldC k (M * s) :=
    (charLDegeneracyRoof_eq_modularFunctionFieldFullC_mul k q' M s hq'Ms).trans
      (modularFunctionFieldC_eq_modularFunctionFieldFullC k q' (M * s) hq'Ms).symm

  unfold HeckeAlphaCIntegral at hα
  unfold HeckeBetaCIntegral at hβ
  have hA : ∀ x : ↥(modularFunctionFieldC k M),
      ((heckeAlphaC k M s x : ↥(charLDegeneracyRoof k M s)) : LaurentSeries k) = x := by
    intro x
    simp
  have hB : ∀ x : ↥(modularFunctionFieldC k M),
      ((heckeBetaC k M s x : ↥(charLDegeneracyRoof k M s)) : LaurentSeries k) = qExpand k s x := by
    intro x
    simp
  generalize heckeAlphaC k M s = α at hα hA hne hr ⊢
  generalize heckeBetaC k M s = β at hβ hB hne ⊢

  generalize charLDegeneracyRoof k M s = R at hroof y α β hα hβ hA hB hne hr ⊢
  subst hroof
  obtain ⟨φ, hφ0, hφ1⟩ : ∃ φ : Fin 2 → (↥(modularFunctionFieldC k M) →ₐ[k] ↥(modularFunctionFieldC k (M * s))),
      φ 0 = α ∧ φ 1 = β := ⟨![α, β], rfl, rfl⟩
  subst hφ0
  subst hφ1
  have hφ : ∀ i, (φ i).toRingHom.IsIntegral := by
    intro i
    fin_cases i
    · exact hα
    · exact hβ
  exact main_of_pair M s q' hs hsq' hq'M hsM φ hφ hA hB y hne hr

end S_ModularCurve_ramificationIndexAlong_heckeAlphaC_mul_placeRamificationJ_eq_jWidthChar_of_restrictAlong_ne_of_prime
end P2MW
export P2MW.S_ModularCurve_ramificationIndexAlong_heckeAlphaC_mul_placeRamificationJ_eq_jWidthChar_of_restrictAlong_ne_of_prime (solution)
