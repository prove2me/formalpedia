-- Prove2me | solution 1 for ModularCurve.isIntegral_adjoin_jqModC_coeffMap_residue_of_isIntegral_of_not_dvd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/4109d709-baf3-5c14-923d-8f09014e077d

import Mathlib
import Definitions.Def_ModularCurve_ReductionModL
import Definitions.Def_EllipticCurve_FrobeniusTrace
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_RatFuncPlaces
import Theorems.Thm_ModularCurve_finrank_adjoin_jqModC_modularFunctionFieldFullC_eq_dedekindPsi
import Theorems.Thm_ModularCurve_transcendental_jqModC
import Theorems.Thm_AlgebraicCurve_degree_poleDivisor_eq_finrank_adjoin_of_isAlgClosed_of_transcendental
import Theorems.Thm_ModularCurve_hasPrincipalDivisors_modularFunctionFieldBar_unconditional
import Theorems.Thm_ModularCurve_isCurveOver_modularFunctionFieldBar
import Theorems.Thm_ModularCurve_isCurveOver_modularFunctionFieldFullC
import Theorems.Thm_ModularCurve_coeffMap_residue_mem_modularFunctionFieldFullC_of_not_dvd
import Theorems.Thm_ModularCurve_exists_placeReductionModL_mapDomain_eq_ord_of_not_dvd
import Theorems.Thm_ModularCurve_laurentBaseChange_modularFunctionFieldFull_eq_modularFunctionFieldFullC
import Theorems.Thm_AlgebraicCurve_isIntegral_adjoin_intermediateField_mk
import Theorems.Thm_AlgebraicCurve_Place_mem_toValuationSubring_of_isIntegral_adjoin
import Theorems.Thm_AlgebraicCurve_isIntegral_adjoin_of_forall_mem_toValuationSubring
import Theorems.Thm_ModularCurve_isSeparable_adjoin_jqModC_of_isAlgebraic
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_isIntegral_adjoin_jqModC_coeffMap_residue_of_isIntegral_of_not_dvd
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.Gamma0Pair.isElliptic WeierstrassCurve.instIsEllipticBaseChange"
p2m_attr_erase "instance" "WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent ModularCurve.B3.instIsElliptic_goodModel ModularCurve.instIsScalarTowerJAdjoin WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring"
p2m_attr_erase "simp" "AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar"
p2m_attr_erase "simp" "ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.coe_cuspidalDivisor₀ ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap"
p2m_attr_erase "simp" "AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord ModularCurve.cuspCount_one ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule HahnSeries.ramScale_apply ModularCurve.gamma0PairMap_gen ModularCurve.moduliPointMapRingHom_mk ModularCurve.Gamma0Pair.mk.injEq ModularCurve.ModuliPoint.j_mk ModularCurve.Gamma0Pair.mk.sizeOf_spec ModularCurve.gamma0PairMap_toCurve WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero WeierstrassCurve.ratPointHom_apply WeierstrassCurve.ratPointMap_zero WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply"
p2m_attr_erase "simp" "compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm ModularCurve.ProjectiveLine.map_mk ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist"
p2m_attr_erase "simp" "ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero"
p2m_attr_erase "simp" "TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff"

set_option autoImplicit false

p2m_open "AlgebraicCurve ModularCurve~dedekindPsi_pos"

namespace RedInt

theorem isAlgClosed_residueField {L : Type*} [Field L] [IsAlgClosed L] (A : ValuationSubring L) :
    IsAlgClosed (IsLocalRing.ResidueField A) := by
  apply IsAlgClosed.of_exists_root
  intro p hpm hirr
  obtain ⟨P, hPmap, hdeg, hPm⟩ := Polynomial.lifts_and_degree_eq_and_monic (f := IsLocalRing.residue A)
    (p := p) (by rw [Polynomial.lifts_iff_coeff_lifts]; intro n; exact IsLocalRing.residue_surjective _) hpm
  subst hPmap
  have hdeg0 : (P.map (algebraMap A L)).degree ≠ 0 := by
    rw [hPm.degree_map, hdeg]; exact (Polynomial.degree_pos_of_irreducible hirr).ne'
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_root _ hdeg0
  rw [Polynomial.IsRoot.def, Polynomial.eval_map] at hz
  have hzint : IsIntegral A z := ⟨P, hPm, hz⟩
  obtain ⟨a, ha⟩ := (IsIntegrallyClosed.isIntegral_iff (R := A) (K := L)).mp hzint
  refine ⟨IsLocalRing.residue A a, ?_⟩
  have hPa : P.eval a = 0 := by
    apply FaithfulSMul.algebraMap_injective A L
    rw [map_zero, ← Polynomial.eval₂_hom, ha, hz]
  simp only [Polynomial.eval_map, Polynomial.eval₂_hom, hPa, map_zero]

section Coeff

variable (A : ValuationSubring (AlgebraicClosure ℚ))

local notation "ℚ̄" => AlgebraicClosure ℚ
local notation "kk" => IsLocalRing.ResidueField A

theorem coeffMap_subtype_jqModC : coeffMap A.subtype (jqModC A) = coeffEmb ℚ̄ jq := by
  ext n
  rw [coeffMap_coeff, coeffEmb_coeff, coeff_jqModC_eq_intCast, ← jqModC_rat, coeff_jqModC_eq_intCast (R := ℚ),
    map_intCast, map_intCast]

theorem coeffMap_residue_jqModC : coeffMap (IsLocalRing.residue A) (jqModC A) = jqModC kk := by
  ext n
  rw [coeffMap_coeff, coeff_jqModC_eq_intCast, coeff_jqModC_eq_intCast (R := kk), map_intCast]

theorem coeffEmb_jq_eq_jqModC : coeffEmb ℚ̄ jq = jqModC ℚ̄ := by
  ext n
  rw [coeffEmb_coeff, ← jqModC_rat, coeff_jqModC_eq_intCast, coeff_jqModC_eq_intCast (R := ℚ̄), map_intCast]

end Coeff

end RedInt

namespace RedInt

section Count

variable {ι κ : Type*} [DecidableEq κ]

theorem mapDomain_apply_eq_sum (D : ι →₀ ℤ) (r : ι → κ) (Q : κ) :
    Finsupp.mapDomain r D Q = ∑ P ∈ D.support with r P = Q, D P := by
  classical
  rw [Finsupp.mapDomain, Finsupp.sum_apply, Finsupp.sum, Finset.sum_filter]
  refine Finset.sum_congr rfl fun P _ => ?_
  rw [Finsupp.single_apply]

theorem neg_to_neg (D : ι →₀ ℤ) (r : ι → κ) (g : κ → ℤ) (S : Finset κ) (ψ : ℤ)
    (hD : ∀ Q, Finsupp.mapDomain r D Q = g Q)
    (hS : ∀ Q, Q ∈ S ↔ g Q < 0)
    (hup : ∑ P ∈ D.support with D P < 0, (-D P) = ψ)
    (hdown : ∑ Q ∈ S, (-g Q) = ψ) :
    (∀ P, D P < 0 → g (r P) < 0) ∧ (∀ P, 0 < D P → ¬ g (r P) < 0) := by
  classical
  set T := D.support.filter (fun P => D P < 0) with hT
  set Z := D.support.filter (fun P => 0 < D P) with hZ

  have h1 : ∑ Q ∈ S, (-g Q) = ∑ P ∈ D.support with r P ∈ S, (-D P) := by
    have : ∀ Q ∈ S, -g Q = ∑ P ∈ D.support with r P = Q, (-D P) := fun Q _ => by
      rw [← hD Q, mapDomain_apply_eq_sum, Finset.sum_neg_distrib]
    rw [Finset.sum_congr rfl this]
    rw [← Finset.sum_fiberwise_of_maps_to (s := D.support.filter (fun P => r P ∈ S)) (t := S) (g := r)
      (fun P hP => (Finset.mem_filter.mp hP).2)]
    refine Finset.sum_congr rfl fun Q hQ => Finset.sum_congr ?_ fun _ _ => rfl
    ext P
    simp only [Finset.mem_filter]
    exact ⟨fun ⟨hP, hPQ⟩ => ⟨⟨hP, hPQ ▸ hQ⟩, hPQ⟩, fun ⟨⟨hP, _⟩, hPQ⟩ => ⟨hP, hPQ⟩⟩

  have hsplit : ∑ P ∈ D.support with r P ∈ S, (-D P) =
      ∑ P ∈ T with r P ∈ S, (-D P) + ∑ P ∈ Z with r P ∈ S, (-D P) := by
    rw [← Finset.sum_union]
    · refine Finset.sum_congr ?_ fun _ _ => rfl
      ext P
      simp only [Finset.mem_union, Finset.mem_filter, hT, hZ, Finsupp.mem_support_iff]
      constructor
      · rintro ⟨hP, hr⟩
        rcases lt_trichotomy (D P) 0 with h | h | h
        · exact Or.inl ⟨⟨hP, h⟩, hr⟩
        · exact absurd h hP
        · exact Or.inr ⟨⟨hP, h⟩, hr⟩
      · rintro (⟨⟨hP, _⟩, hr⟩ | ⟨⟨hP, _⟩, hr⟩) <;> exact ⟨hP, hr⟩
    · rw [Finset.disjoint_left]
      intro P h1 h2
      have a := (Finset.mem_filter.mp (Finset.mem_filter.mp h1).1).2
      have b := (Finset.mem_filter.mp (Finset.mem_filter.mp h2).1).2
      omega

  have hZle : ∑ P ∈ Z with r P ∈ S, (-D P) ≤ 0 :=
    Finset.sum_nonpos fun P hP => by
      have := (Finset.mem_filter.mp (Finset.mem_filter.mp hP).1).2; omega
  have hTle : ∑ P ∈ T with r P ∈ S, (-D P) ≤ ∑ P ∈ T, (-D P) :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun P hP _ => by
      have := (Finset.mem_filter.mp hP).2; omega
  have hTeq : ∑ P ∈ T, (-D P) = ψ := hup

  have hchain : ψ ≤ ∑ P ∈ T with r P ∈ S, (-D P) := by
    have := hdown; rw [h1, hsplit] at this; omega
  have hZ0 : ∑ P ∈ Z with r P ∈ S, (-D P) = 0 := by
    have := hdown; rw [h1, hsplit] at this; omega
  have hT0 : ∑ P ∈ T with r P ∈ S, (-D P) = ∑ P ∈ T, (-D P) := by omega
  constructor
  ·
    intro P hP
    by_contra hcon
    have hPT : P ∈ T := Finset.mem_filter.mpr ⟨Finsupp.mem_support_iff.mpr hP.ne, hP⟩
    have hPS : r P ∉ S := fun h => hcon ((hS _).1 h)
    have hlt : ∑ Q ∈ T with r Q ∈ S, (-D Q) < ∑ Q ∈ T, (-D Q) := by
      apply Finset.sum_lt_sum_of_subset (Finset.filter_subset _ _) (i := P) hPT
        (by simp [Finset.mem_filter, hPS]) (by omega)
      intro Q hQ _
      have := (Finset.mem_filter.mp hQ).2; omega
    omega
  ·
    intro P hP hcon
    have hPZ : P ∈ Z.filter (fun P => r P ∈ S) :=
      Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finsupp.mem_support_iff.mpr hP.ne', hP⟩, (hS _).2 hcon⟩
    have hlt : ∑ Q ∈ Z with r Q ∈ S, (-D Q) < 0 := by
      rw [← Finset.add_sum_erase _ _ hPZ]
      have h2 : ∑ Q ∈ (Z.filter (fun P => r P ∈ S)).erase P, (-D Q) ≤ 0 :=
        Finset.sum_nonpos fun Q hQ => by
          have := (Finset.mem_filter.mp (Finset.mem_filter.mp (Finset.mem_of_mem_erase hQ)).1).2; omega
      omega
    omega

end Count

end RedInt

namespace RedInt

section Mass

variable {K F : Type*} [Field K] [IsAlgClosed K] [Field F] [Algebra K F] [IsCurveOver K F]

theorem pole_mass_eq (x : F) (hx : Transcendental K x)
    [FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F]
    (D : Divisor K F) (hD : ∀ v, D v = v.ord x) :
    ∑ P ∈ D.support with D P < 0, (-D P) =
      (Module.finrank (IntermediateField.adjoin K ({x} : Set F)) F : ℤ) := by
  classical
  set T := D.support.filter (fun P => D P < 0) with hTdef
  have hT : ∀ v, v ∈ T ↔ v.ord x < 0 := fun v => by
    rw [hTdef, Finset.mem_filter, Finsupp.mem_support_iff, hD v]
    exact ⟨And.right, fun h => ⟨ne_of_lt h, h⟩⟩
  have hdeg1 : ∀ v : Place K F, v.deg = 1 := IsCurveOver.forall_deg_eq_one_of_isAlgClosed
  let Pd : Divisor K F := ∑ v ∈ T, Finsupp.single v (-(v.ord x))
  have hP : ∀ v, Pd v = max 0 (-v.ord x) := by
    intro v
    simp only [Pd, Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.single_apply]
    rw [Finset.sum_ite_eq' T v]
    by_cases hv : v ∈ T
    · rw [if_pos hv, max_eq_right]; have := (hT v).1 hv; omega
    · rw [if_neg hv, max_eq_left]; have := (hT v).not.1 hv; omega
  have hPdeg := degree_poleDivisor_eq_finrank_adjoin_of_isAlgClosed_of_transcendental x hx Pd hP
  have hPdeg' : Divisor.degree Pd = ∑ v ∈ T, -(v.ord x) := by
    simp only [Pd, map_sum, Divisor.degree_single, hdeg1, Nat.cast_one, mul_one]
  rw [← hPdeg, hPdeg']
  exact Finset.sum_congr rfl fun v _ => by rw [hD v]

omit [IsAlgClosed K] [IsCurveOver K F] in
theorem degree_eq_sum (D : Divisor K F) (hdeg1 : ∀ v : Place K F, v.deg = 1) :
    Divisor.degree D = ∑ P ∈ D.support, D P := by
  classical
  have : D = ∑ P ∈ D.support, Finsupp.single P (D P) := (Finsupp.sum_single D).symm
  conv_lhs => rw [this]
  simp only [map_sum, Divisor.degree_single, hdeg1, Nat.cast_one, mul_one]

theorem zero_mass_eq (D : Divisor K F) (hdeg : Divisor.degree D = 0) :
    ∑ P ∈ D.support with 0 < D P, D P = ∑ P ∈ D.support with D P < 0, (-D P) := by
  classical
  have hdeg1 : ∀ v : Place K F, v.deg = 1 := IsCurveOver.forall_deg_eq_one_of_isAlgClosed
  rw [degree_eq_sum D hdeg1] at hdeg
  have hsplit : ∑ P ∈ D.support, D P =
      ∑ P ∈ D.support with 0 < D P, D P + ∑ P ∈ D.support with D P < 0, D P := by
    rw [← Finset.sum_union]
    · refine Finset.sum_congr ?_ fun _ _ => rfl
      ext P
      simp only [Finset.mem_union, Finset.mem_filter, Finsupp.mem_support_iff]
      constructor
      · intro hP
        rcases lt_trichotomy (D P) 0 with h | h | h
        · exact Or.inr ⟨hP, h⟩
        · exact absurd h hP
        · exact Or.inl ⟨hP, h⟩
      · rintro (⟨hP, _⟩ | ⟨hP, _⟩) <;> exact hP
    · rw [Finset.disjoint_left]
      intro P h1 h2
      have a := (Finset.mem_filter.mp h1).2
      have b := (Finset.mem_filter.mp h2).2
      omega
  rw [hsplit] at hdeg
  rw [Finset.sum_neg_distrib]
  omega

end Mass

end RedInt

namespace RedInt

section Ord

variable {K : Type*} {FF : Type*} [Field K] [Field FF] [Algebra K FF] (w : Place K FF)

theorem mem_iff_le_one {f : FF} : f ∈ w.toValuationSubring ↔ w.adicValuation f ≤ 1 :=
  Place.mem_iff_adicValuation_le_one w

theorem ord_nonneg_iff {f : FF} (hf : f ≠ 0) : 0 ≤ w.ord f ↔ w.adicValuation f ≤ 1 := by
  rw [Place.ord, neg_nonneg, WithZero.log_le_iff_le_exp (w.adicValuation_ne_zero hf), WithZero.exp_zero]

theorem ord_nonneg_of_mem {f : FF} (h : f ∈ w.toValuationSubring) : 0 ≤ w.ord f := by
  rcases eq_or_ne f 0 with rfl | hf
  · rw [Place.ord_zero]
  · exact (ord_nonneg_iff w hf).2 ((mem_iff_le_one w).1 h)

theorem mem_of_ord_nonneg {f : FF} (h : 0 ≤ w.ord f) : f ∈ w.toValuationSubring := by
  rcases eq_or_ne f 0 with rfl | hf
  · exact zero_mem _
  · exact (mem_iff_le_one w).2 ((ord_nonneg_iff w hf).1 h)

end Ord

theorem finrank_adjoin_eq_psi_of_eq (K : Type*) [Field K] (N : ℕ) [NeZero N] (hN : (N : K) ≠ 0)
    (E : IntermediateField K (LaurentSeries K)) (hE : modularFunctionFieldFullC K N = E) (hj : jqModC K ∈ E) :
    Module.finrank ↥(IntermediateField.adjoin K ({⟨jqModC K, hj⟩} : Set ↥E)) ↥E = dedekindPsi N := by
  subst hE
  exact finrank_adjoin_jqModC_modularFunctionFieldFullC_eq_dedekindPsi K N hN

theorem dedekindPsi_pos (N : ℕ) [NeZero N] : 0 < dedekindPsi N := by
  rw [dedekindPsi]
  have h1 : (1 : ℕ) ∈ N.divisors.filter Squarefree := by
    rw [Finset.mem_filter]; exact ⟨Nat.one_mem_divisors.2 (NeZero.ne N), squarefree_one⟩
  have := Finset.single_le_sum (f := fun d => N / d) (fun _ _ => Nat.zero_le _) h1
  simp only [Nat.div_one] at this
  exact lt_of_lt_of_le (Nat.pos_of_ne_zero (NeZero.ne N)) this

theorem jqModC_mem_bar (N : ℕ) [NeZero N] : jqModC (AlgebraicClosure ℚ) ∈ modularFunctionFieldBar N := by
  rw [← coeffEmb_jq_eq_jqModC]
  exact coeffEmb_mem_laurentBaseChange _ (modularFunctionField_le_full N (jq_mem N))

theorem transcendental_mk (K : Type*) [Field K] (E : IntermediateField K (LaurentSeries K)) (hj : jqModC K ∈ E) :
    Transcendental K (⟨jqModC K, hj⟩ : ↥E) := fun h =>
  (transcendental_jqModC K) (by simpa using h.algHom E.val)

theorem mk_ne_zero (K : Type*) [Field K] (E : IntermediateField K (LaurentSeries K)) (hj : jqModC K ∈ E) :
    (⟨jqModC K, hj⟩ : ↥E) ≠ 0 := fun h => by
  have : jqModC K = 0 := congrArg Subtype.val h
  exact (transcendental_jqModC K) (this ▸ isAlgebraic_zero)

theorem natCast_ne_zero_residueField {ℓ : ℕ} [Fact ℓ.Prime] {N : ℕ} (hℓN : ¬ ℓ ∣ N)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime ℓ) :
    ((N : ℕ) : IsLocalRing.ResidueField A) ≠ 0 := by
  intro hN
  have hNmax : ((N : ℕ) : A) ∈ IsLocalRing.maximalIdeal A := by
    rw [← IsLocalRing.residue_eq_zero_iff]; exact_mod_cast hN
  have hℓmax : ((ℓ : ℕ) : A) ∈ IsLocalRing.maximalIdeal A := by
    obtain ⟨hmem, hmax⟩ := (ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal).1 hA
    convert hmax <;> first | rfl | exact Subsingleton.elim _ _
  have hcop : IsCoprime ((ℓ : ℕ) : A) ((N : ℕ) : A) := by
    have : Nat.Coprime ℓ N := (Nat.Prime.coprime_iff_not_dvd (Fact.out)).2 hℓN
    simpa using (Nat.Coprime.isCoprime this).map (Int.castRingHom A)
  obtain ⟨a, b, hab⟩ := hcop
  have : (1 : A) ∈ IsLocalRing.maximalIdeal A := by
    rw [← hab]; exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hℓmax) (Ideal.mul_mem_left _ _ hNmax)
  exact (IsLocalRing.maximalIdeal.isMaximal A).ne_top (Ideal.eq_top_of_isUnit_mem _ this isUnit_one)

theorem isIntegral_adjoin_of_intermediateField {L M : Type*} [Field L] [Field M] [Algebra L M]
    (E : IntermediateField L M) {j x : M} (hj : j ∈ E) (hx : x ∈ E)
    (h : IsIntegral ↥(Algebra.adjoin L ({(⟨j, hj⟩ : ↥E)} : Set ↥E)) (⟨x, hx⟩ : ↥E)) :
    IsIntegral ↥(Algebra.adjoin L ({j} : Set M)) x := by
  set R₁ := Algebra.adjoin L ({(⟨j, hj⟩ : ↥E)} : Set ↥E)
  set R₂ := Algebra.adjoin L ({j} : Set M)
  have hmap : ∀ z : R₁, (E.val : ↥E →ₐ[L] M) z ∈ R₂ := by
    intro z
    have : (R₁.map (E.val : ↥E →ₐ[L] M)) = R₂ := by
      rw [← Algebra.adjoin_image, Set.image_singleton]; rfl
    rw [← this]; exact Subalgebra.mem_map.mpr ⟨z, z.2, rfl⟩
  let φ : ↥R₁ →ₐ[L] ↥R₂ := ((E.val : ↥E →ₐ[L] M).comp R₁.val).codRestrict R₂ (fun z => hmap z)
  obtain ⟨p, hp, hev⟩ := h
  refine ⟨p.map (φ : ↥R₁ →+* ↥R₂), hp.map _, ?_⟩
  have hcomp : (algebraMap ↥R₂ M).comp (φ : ↥R₁ →+* ↥R₂) =
      ((E.val : ↥E →ₐ[L] M) : ↥E →+* M).comp (algebraMap ↥R₁ ↥E) := by
    ext z; rfl
  rw [Polynomial.eval₂_map, hcomp]
  change Polynomial.eval₂ (((E.val : ↥E →ₐ[L] M) : ↥E →+* M).comp (algebraMap ↥R₁ ↥E))
    (((E.val : ↥E →ₐ[L] M) : ↥E →+* M) ⟨x, hx⟩) p = 0
  rw [← Polynomial.hom_eval₂, hev, map_zero]

end RedInt

namespace RedInt

section Main

open IsLocalRing

local notation "ℚ̄" => AlgebraicClosure ℚ

set_option maxHeartbeats 3200000 in
set_option synthInstance.maxHeartbeats 1600000 in
theorem main_j (N : ℕ) [NeZero N] {ℓ : ℕ} [Fact ℓ.Prime] (hℓN : ¬ ℓ ∣ N) (A : ValuationSubring ℚ̄)
    (hA : A.LiesOverPrime ℓ) (y : LaurentSeries A)
    (hy : coeffMap A.subtype y ∈ modularFunctionFieldBar N)
    (hint : IsIntegral (Algebra.adjoin ℚ̄ ({coeffEmb ℚ̄ jq} : Set (LaurentSeries ℚ̄))) (coeffMap A.subtype y)) :
    IsIntegral (Algebra.adjoin (ResidueField A) ({jqModC (ResidueField A)} : Set (LaurentSeries (ResidueField A))))
      (coeffMap (residue A) y) := by
  classical

  haveI hk : IsAlgClosed (ResidueField A) := isAlgClosed_residueField A
  haveI : HasPrincipalDivisors ℚ̄ ↥(modularFunctionFieldBar N) :=
    hasPrincipalDivisors_modularFunctionFieldBar_unconditional N
  haveI : IsCurveOver ℚ̄ ↥(modularFunctionFieldBar N) := isCurveOver_modularFunctionFieldBar N
  haveI : IsCurveOver (ResidueField A) ↥(modularFunctionFieldFullC (ResidueField A) N) :=
    isCurveOver_modularFunctionFieldFullC (ResidueField A) N
  have hNk : ((N : ℕ) : ResidueField A) ≠ 0 := natCast_ne_zero_residueField hℓN A hA

  have hyk : coeffMap (residue A) y ∈ modularFunctionFieldFullC (ResidueField A) N :=
    coeffMap_residue_mem_modularFunctionFieldFullC_of_not_dvd N hℓN A hA y hy
  by_cases hx0 : coeffMap (residue A) y = 0
  · rw [hx0]; exact isIntegral_zero

  set xF : ↥(modularFunctionFieldBar N) := ⟨coeffMap A.subtype y, hy⟩ with hxF
  set xk : ↥(modularFunctionFieldFullC (ResidueField A) N) := ⟨coeffMap (residue A) y, hyk⟩ with hxk
  have hjF_mem : jqModC ℚ̄ ∈ modularFunctionFieldBar N := jqModC_mem_bar N
  set jF : ↥(modularFunctionFieldBar N) := ⟨jqModC ℚ̄, hjF_mem⟩ with hjFdef
  set jk : ↥(modularFunctionFieldFullC (ResidueField A) N) :=
    ⟨jqModC (ResidueField A), jqModC_mem_full (ResidueField A) N⟩ with hjkdef
  have hxF0 : xF ≠ 0 := by
    intro h
    apply hx0
    have h' : coeffMap A.subtype y = 0 := congrArg Subtype.val h
    have : y = 0 := by
      ext n
      have h2 := congrArg (fun s => HahnSeries.coeff s n) h'
      simp only [coeffMap_coeff, HahnSeries.coeff_zero] at h2
      rw [HahnSeries.coeff_zero]
      simpa using h2
    rw [this, map_zero]

  obtain ⟨r, hr⟩ := exists_placeReductionModL_mapDomain_eq_ord_of_not_dvd N hℓN A hA

  have hjy : coeffMap A.subtype (jqModC A) ∈ modularFunctionFieldBar N := by
    rw [coeffMap_subtype_jqModC, coeffEmb_jq_eq_jqModC]; exact hjF_mem
  have hjyk : coeffMap (residue A) (jqModC A) ∈ modularFunctionFieldFullC (ResidueField A) N := by
    rw [coeffMap_residue_jqModC]; exact jqModC_mem_full _ N
  have hjyk0 : coeffMap (residue A) (jqModC A) ≠ 0 := by
    rw [coeffMap_residue_jqModC]; exact fun h => (transcendental_jqModC (ResidueField A)) (h ▸ isAlgebraic_zero)
  have hjF_eq : (⟨coeffMap A.subtype (jqModC A), hjy⟩ : ↥(modularFunctionFieldBar N)) = jF :=
    Subtype.ext ((coeffMap_subtype_jqModC A).trans coeffEmb_jq_eq_jqModC)
  have hjk_eq : (⟨coeffMap (residue A) (jqModC A), hjyk⟩ : ↥(modularFunctionFieldFullC (ResidueField A) N)) = jk :=
    Subtype.ext (coeffMap_residue_jqModC A)
  have hjF0 : jF ≠ 0 := mk_ne_zero ℚ̄ _ hjF_mem
  have hjk0 : jk ≠ 0 := mk_ne_zero (ResidueField A) _ _
  obtain ⟨Dj, hDj, hDjdeg⟩ :=
    HasPrincipalDivisors.exists_divisor (K := ℚ̄) (F := ↥(modularFunctionFieldBar N)) jF hjF0
  obtain ⟨Dx, hDx, -⟩ :=
    HasPrincipalDivisors.exists_divisor (K := ℚ̄) (F := ↥(modularFunctionFieldBar N)) xF hxF0
  have hrj : ∀ Q, Finsupp.mapDomain r Dj Q = Q.ord jk := by
    intro Q
    have := hr (jqModC A) hjy hjyk hjyk0 Dj (fun P => by rw [hDj P, hjF_eq]) Q
    rwa [hjk_eq] at this
  have hrx : ∀ Q, Finsupp.mapDomain r Dx Q = Q.ord xk := fun Q => hr y hy hyk hx0 Dx hDx Q

  haveI : FiniteDimensional ↥(IntermediateField.adjoin ℚ̄ ({jF} : Set ↥(modularFunctionFieldBar N)))
      ↥(modularFunctionFieldBar N) :=
    Module.finite_of_finrank_pos (by
      rw [hjFdef, finrank_adjoin_eq_psi_of_eq ℚ̄ N (NeZero.ne _) _
        (laurentBaseChange_modularFunctionFieldFull_eq_modularFunctionFieldFullC ℚ̄ N).symm hjF_mem]
      exact dedekindPsi_pos N)
  haveI hfk : FiniteDimensional ↥(IntermediateField.adjoin (ResidueField A)
      ({jk} : Set ↥(modularFunctionFieldFullC (ResidueField A) N))) ↥(modularFunctionFieldFullC (ResidueField A) N) :=
    Module.finite_of_finrank_pos (by
      rw [hjkdef, finrank_adjoin_jqModC_modularFunctionFieldFullC_eq_dedekindPsi (ResidueField A) N hNk]
      exact dedekindPsi_pos N)
  have hψF : ∑ P ∈ Dj.support with Dj P < 0, (-Dj P) = dedekindPsi N := by
    rw [pole_mass_eq jF (transcendental_mk ℚ̄ _ hjF_mem) Dj hDj, hjFdef,
      finrank_adjoin_eq_psi_of_eq ℚ̄ N (NeZero.ne _) _
        (laurentBaseChange_modularFunctionFieldFull_eq_modularFunctionFieldFullC ℚ̄ N).symm hjF_mem]
  obtain ⟨Djk, hDjk, -⟩ :=
    HasPrincipalDivisors.exists_divisor (K := ResidueField A) (F := ↥(modularFunctionFieldFullC (ResidueField A) N)) jk hjk0
  have hψk : ∑ Q ∈ Djk.support with Djk Q < 0, (-Djk Q) = dedekindPsi N := by
    rw [pole_mass_eq jk (transcendental_mk (ResidueField A) _ _) Djk hDjk, hjkdef,
      finrank_adjoin_jqModC_modularFunctionFieldFullC_eq_dedekindPsi (ResidueField A) N hNk]

  set S := Djk.support.filter (fun Q => Djk Q < 0) with hSdef
  have hS : ∀ Q, Q ∈ S ↔ Q.ord jk < 0 := fun Q => by
    rw [hSdef, Finset.mem_filter, Finsupp.mem_support_iff, hDjk Q]
    exact ⟨And.right, fun h => ⟨ne_of_lt h, h⟩⟩
  have hdown : ∑ Q ∈ S, (-(Q.ord jk)) = dedekindPsi N := by
    rw [← hψk]; exact Finset.sum_congr rfl fun Q _ => by rw [hDjk Q]
  obtain ⟨hcusp, -⟩ := neg_to_neg Dj r (fun Q => Q.ord jk) S (dedekindPsi N) hrj hS hψF hdown

  have hintF : IsIntegral ↥(Algebra.adjoin ℚ̄ ({jF} : Set ↥(modularFunctionFieldBar N))) xF := by
    rw [hjFdef, hxF]
    exact isIntegral_adjoin_intermediateField_mk (modularFunctionFieldBar N) hjF_mem hy
      (by rwa [coeffEmb_jq_eq_jqModC] at hint)

  have hplace : ∀ v : Place (ResidueField A) ↥(modularFunctionFieldFullC (ResidueField A) N),
      jk ∈ v.toValuationSubring → xk ∈ v.toValuationSubring := by
    intro v hv
    apply mem_of_ord_nonneg
    rw [← hrx v, mapDomain_apply_eq_sum]
    refine Finset.sum_nonneg fun P hP => ?_
    have hPv : r P = v := (Finset.mem_filter.mp hP).2
    rw [hDx P]
    have hPj : 0 ≤ P.ord jF := by
      by_contra hneg
      push Not at hneg
      have h1 := hcusp P (by rw [hDj P]; exact hneg)
      rw [hPv] at h1
      exact absurd (ord_nonneg_of_mem v hv) (not_le.mpr h1)
    exact ord_nonneg_of_mem P
      (Place.mem_toValuationSubring_of_isIntegral_adjoin P (mem_of_ord_nonneg P hPj) hintF)

  haveI : Algebra.IsSeparable ↥(IntermediateField.adjoin (ResidueField A)
      ({jk} : Set ↥(modularFunctionFieldFullC (ResidueField A) N))) ↥(modularFunctionFieldFullC (ResidueField A) N) :=
    isSeparable_adjoin_jqModC_of_isAlgebraic (ResidueField A) _ (jqModC_mem_full _ N)
  have hintk : IsIntegral ↥(Algebra.adjoin (ResidueField A)
      ({jk} : Set ↥(modularFunctionFieldFullC (ResidueField A) N))) xk :=
    isIntegral_adjoin_of_forall_mem_toValuationSubring jk jk xk hplace
  rw [hjkdef, hxk] at hintk
  exact isIntegral_adjoin_of_intermediateField (modularFunctionFieldFullC (ResidueField A) N)
    (jqModC_mem_full _ N) hyk hintk

end Main

end RedInt

theorem solution (N : ℕ) [NeZero N]
    {ℓ : ℕ} [Fact ℓ.Prime] (hℓN : ¬ ℓ ∣ N) (A : ValuationSubring (AlgebraicClosure ℚ))
    (hA : A.LiesOverPrime ℓ) (y : LaurentSeries A)
    (hy : ModularCurve.coeffMap A.subtype y ∈ ModularCurve.modularFunctionFieldBar N)
    (hint : IsIntegral (Algebra.adjoin (AlgebraicClosure ℚ)
        ({ModularCurve.coeffEmb (AlgebraicClosure ℚ) ModularCurve.jq} : Set (LaurentSeries (AlgebraicClosure ℚ))))
      (ModularCurve.coeffMap A.subtype y)) :
    IsIntegral (Algebra.adjoin (IsLocalRing.ResidueField A)
        ({ModularCurve.jqModC (IsLocalRing.ResidueField A)} : Set (LaurentSeries (IsLocalRing.ResidueField A))))
      (ModularCurve.coeffMap (IsLocalRing.residue A) y) :=
  RedInt.main_j N hℓN A hA y hy hint

end S_ModularCurve_isIntegral_adjoin_jqModC_coeffMap_residue_of_isIntegral_of_not_dvd
end P2MW
export P2MW.S_ModularCurve_isIntegral_adjoin_jqModC_coeffMap_residue_of_isIntegral_of_not_dvd (solution)
