-- Prove2me | solution 1 for ModularCurve.exists_placeReductionModL_mapDomain_eq_ord_of_not_dvd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/cb18a280-a132-567c-8f7b-36ab5f834c29

import Mathlib
import Definitions.Def_ModularCurve_ReductionModL
import Definitions.Def_EllipticCurve_FrobeniusTrace
import Theorems.Thm_ModularCurve_transcendental_jqModC
import Theorems.Thm_AlgebraicCurve_exists_placeMap_mapDomain_eq_ord_of_good_constantReduction
import Theorems.Thm_ModularCurve_finrank_adjoin_jqModC_modularFunctionFieldFullC_eq_dedekindPsi
import Theorems.Thm_ModularCurve_isCurveOver_modularFunctionFieldBar
import Theorems.Thm_ModularCurve_isCurveOver_modularFunctionFieldFullC
import Theorems.Thm_ModularCurve_genusFF_modularFunctionFieldFullC_eq_genusFF_modularFunctionFieldBar
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_placeReductionModL_mapDomain_eq_ord_of_not_dvd
p2m_attr_erase "instance" "AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion"
p2m_attr_erase "instance" "ModularCurve.Gamma0Pair.isElliptic WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent ModularCurve.B3.instIsElliptic_goodModel ModularCurve.instIsScalarTowerJAdjoin WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular"
p2m_attr_erase "simp" "AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom"
p2m_attr_erase "simp" "AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply"
p2m_attr_erase "simp" "AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL ModularCurve.cuspCount_one ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul"
p2m_attr_erase "simp" "ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_cuspidalDivisor₀ ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule HahnSeries.ramScale_apply ModularCurve.gamma0PairMap_gen ModularCurve.moduliPointMapRingHom_mk"
p2m_attr_erase "simp" "ModularCurve.Gamma0Pair.mk.injEq ModularCurve.ModuliPoint.j_mk ModularCurve.Gamma0Pair.mk.sizeOf_spec ModularCurve.gamma0PairMap_toCurve WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero WeierstrassCurve.ratPointHom_apply WeierstrassCurve.ratPointMap_zero WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one"
p2m_attr_erase "simp" "WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂"
p2m_attr_erase "simp" "PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm ModularCurve.ProjectiveLine.map_mk ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃"
p2m_attr_erase "simp" "WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq"
p2m_attr_erase "simp" "WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff"

set_option linter.unusedSectionVars false
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000

noncomputable section

open scoped Classical
p2m_open "IntermediateField AlgebraicCurve~genus ModularCurve~dedekindPsi_pos Polynomial"

namespace W7G3C1

section Coeff

variable {L : Type*} [Field L] (A : ValuationSubring L)

abbrev ι : LaurentSeries A →+* LaurentSeries L := coeffMap A.subtype

abbrev ϖ : LaurentSeries A →+* LaurentSeries (IsLocalRing.ResidueField A) :=
  coeffMap (IsLocalRing.residue A)

theorem ι_injective : Function.Injective (ι A) := by
  intro x y h
  ext n
  have h1 := congrArg (fun s : LaurentSeries L => s.coeff n) h
  simp only [coeffMap_coeff] at h1
  exact h1

theorem ι_eq_zero_iff (x : LaurentSeries A) : ι A x = 0 ↔ x = 0 := by
  rw [← map_zero (ι A)]; exact (ι_injective A).eq_iff

theorem ϖ_eq_zero_iff (y : LaurentSeries A) :
    ϖ A y = 0 ↔ ∀ n, y.coeff n ∈ IsLocalRing.maximalIdeal A := by
  constructor
  · intro h n
    have h1 := congrArg (fun s : LaurentSeries (IsLocalRing.ResidueField A) => s.coeff n) h
    simp only [coeffMap_coeff, HahnSeries.coeff_zero] at h1
    exact (IsLocalRing.residue_eq_zero_iff _).mp h1
  · intro h
    ext n
    simp only [coeffMap_coeff, HahnSeries.coeff_zero]
    exact (IsLocalRing.residue_eq_zero_iff _).mpr (h n)

theorem ι_C (a : A) : ι A (HahnSeries.C a) = algebraMap L (LaurentSeries L) (a : L) := by
  rw [HahnSeries.C_apply, coeffMap_single, algebraMap_laurentSeries_eq_single]; rfl

theorem ϖ_C (a : A) : ϖ A (HahnSeries.C a) =
    algebraMap (IsLocalRing.ResidueField A) (LaurentSeries (IsLocalRing.ResidueField A))
      (IsLocalRing.residue A a) := by
  rw [HahnSeries.C_apply, coeffMap_single, algebraMap_laurentSeries_eq_single]

def IsInt (f : LaurentSeries L) : Prop :=
  ∃ x y : LaurentSeries A, ϖ A y ≠ 0 ∧ f * ι A y = ι A x

variable {A}

theorem ϖ_ne_zero_ne_zero {y : LaurentSeries A} (hy : ϖ A y ≠ 0) : y ≠ 0 := by
  rintro rfl; exact hy (map_zero _)

theorem IsInt.zero : IsInt A (0 : LaurentSeries L) := ⟨0, 1, by simp, by simp⟩

theorem IsInt.one : IsInt A (1 : LaurentSeries L) := ⟨1, 1, by simp, by simp⟩

theorem IsInt.mul {f g : LaurentSeries L} (hf : IsInt A f) (hg : IsInt A g) : IsInt A (f * g) := by
  obtain ⟨x, y, hy, h⟩ := hf
  obtain ⟨x', y', hy', h'⟩ := hg
  refine ⟨x * x', y * y', by rw [map_mul]; exact mul_ne_zero hy hy', ?_⟩
  rw [map_mul, map_mul, ← h, ← h']; ring

theorem IsInt.add {f g : LaurentSeries L} (hf : IsInt A f) (hg : IsInt A g) : IsInt A (f + g) := by
  obtain ⟨x, y, hy, h⟩ := hf
  obtain ⟨x', y', hy', h'⟩ := hg
  refine ⟨x * y' + x' * y, y * y', by rw [map_mul]; exact mul_ne_zero hy hy', ?_⟩
  rw [map_mul, map_add, map_mul, map_mul, ← h, ← h']; ring

theorem IsInt.neg {f : LaurentSeries L} (hf : IsInt A f) : IsInt A (-f) := by
  obtain ⟨x, y, hy, h⟩ := hf
  exact ⟨-x, y, hy, by rw [map_neg, ← h]; ring⟩

theorem IsInt.cross {f : LaurentSeries L} {x y x' y' : LaurentSeries A}
    (h : f * ι A y = ι A x) (h' : f * ι A y' = ι A x') : x * y' = x' * y := by
  apply ι_injective A
  rw [map_mul, map_mul, ← h, ← h']; ring

theorem IsInt.inv_of {f : LaurentSeries L} {x y : LaurentSeries A} (hx : ϖ A x ≠ 0)
    (h : f * ι A y = ι A x) : f⁻¹ * ι A x = ι A y := by
  have hf : f ≠ 0 := by
    rintro rfl
    rw [zero_mul, eq_comm, ι_eq_zero_iff] at h
    exact hx (by rw [h, map_zero])
  rw [← h, ← mul_assoc, inv_mul_cancel₀ hf, one_mul]

end Coeff

section Scaling

variable {L : Type*} [Field L] (A : ValuationSubring L)

theorem exists_coeffMap_subtype_eq (x : LaurentSeries L) (hx : ∀ n, x.coeff n ∈ A) :
    ∃ y : LaurentSeries A, ι A y = x := by
  refine ⟨⟨fun n => ⟨x.coeff n, hx n⟩, ?_⟩, ?_⟩
  · convert x.isPWO_support' using 1
    ext n
    simp only [Function.mem_support, ne_eq, Subtype.ext_iff, ZeroMemClass.coe_zero]
  · ext n
    rfl

theorem valuation_le_of_mem_span (T : Finset L) (c : L) (hc : ∀ t ∈ T, A.valuation t ≤ A.valuation c)
    {x : L} (hx : x ∈ Submodule.span ℤ (T : Set L)) : A.valuation x ≤ A.valuation c := by
  induction hx using Submodule.span_induction with
  | mem x h => exact hc x h
  | zero => simp
  | add x y _ _ hx hy => exact (Valuation.map_add _ _ _).trans (max_le hx hy)
  | smul m x _ hx =>
      rw [zsmul_eq_mul, map_mul]
      calc A.valuation (m : L) * A.valuation x ≤ 1 * A.valuation c :=
            mul_le_mul' ((A.valuation_le_one_iff _).mpr (intCast_mem A m)) hx
        _ = A.valuation c := one_mul _

theorem exists_primitive_scaling {x : LaurentSeries L} (hx : x ≠ 0) (M : Submodule ℤ L) (hM : M.FG)
    (hxM : ∀ n, x.coeff n ∈ M) :
    ∃ c : L, c ≠ 0 ∧ (∀ n, c⁻¹ * x.coeff n ∈ A) ∧ ∃ n₀, c⁻¹ * x.coeff n₀ = 1 := by
  set N' : Submodule ℤ L := Submodule.span ℤ (Set.range x.coeff) with hN'
  have hle : N' ≤ M := Submodule.span_le.mpr (by rintro _ ⟨n, rfl⟩; exact hxM n)
  have hfg : N'.FG := (isNoetherian_submodule.mp (isNoetherian_of_fg_of_noetherian M hM)) N' hle
  obtain ⟨T, hTsub, hTspan⟩ : ∃ T : Finset L, (↑T ⊆ Set.range x.coeff) ∧
      Submodule.span ℤ (T : Set L) = N' := by
    obtain ⟨S, hS⟩ := hfg
    have hmem : ∀ s ∈ S, ∃ T : Finset L, ↑T ⊆ Set.range x.coeff ∧
        s ∈ Submodule.span ℤ (T : Set L) := fun s hs =>
      Submodule.mem_span_finite_of_mem_span (by rw [← hN', ← hS]; exact Submodule.subset_span hs)
    choose! Tf hTf₁ hTf₂ using hmem
    refine ⟨S.biUnion Tf, ?_, le_antisymm ?_ ?_⟩
    · simp only [Finset.coe_biUnion, Set.iUnion_subset_iff]
      exact fun s hs => hTf₁ s hs
    · exact Submodule.span_le.mpr fun t ht => by
        obtain ⟨s, hs, hts⟩ := Finset.mem_biUnion.mp ht
        exact Submodule.subset_span (hTf₁ s hs hts)
    · rw [← hS]
      refine Submodule.span_le.mpr fun s hs => ?_
      have h := hTf₂ s hs
      exact Submodule.span_mono (by
        intro t ht
        exact Finset.mem_biUnion.mpr ⟨s, hs, ht⟩) h
  obtain ⟨n₁, hn₁⟩ : ∃ n, x.coeff n ≠ 0 := by
    by_contra h
    push Not at h
    exact hx (by ext n; simpa using h n)
  have hcoeffN' : ∀ n, x.coeff n ∈ Submodule.span ℤ (T : Set L) := fun n => by
    rw [hTspan]; exact Submodule.subset_span ⟨n, rfl⟩
  have hTne : T.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    rintro rfl
    apply hn₁
    simpa using hcoeffN' n₁
  obtain ⟨c, hcT, hcmax⟩ := Finset.exists_max_image T A.valuation hTne
  have hvx : ∀ n, A.valuation (x.coeff n) ≤ A.valuation c := fun n =>
    valuation_le_of_mem_span A T c hcmax (hcoeffN' n)
  have hc0 : c ≠ 0 := by
    intro hc
    have h := hvx n₁
    rw [hc, map_zero, le_zero_iff, map_eq_zero] at h
    exact hn₁ h
  obtain ⟨n₀, hn₀⟩ := hTsub hcT
  refine ⟨c, hc0, fun n => ?_, n₀, by rw [hn₀, inv_mul_cancel₀ hc0]⟩
  rw [← A.valuation_le_one_iff, map_mul, map_inv₀]
  have hc' : A.valuation c ≠ 0 := by simpa using hc0
  rw [inv_mul_le_one₀ (zero_lt_iff.mpr hc')]
  exact hvx n

theorem exists_primitive_form {x : LaurentSeries L} (hx : x ≠ 0) (M : Submodule ℤ L) (hM : M.FG)
    (hxM : ∀ n, x.coeff n ∈ M) :
    ∃ c : L, c ≠ 0 ∧ ∃ x₀ : LaurentSeries A, ϖ A x₀ ≠ 0 ∧
      x = algebraMap L (LaurentSeries L) c * ι A x₀ := by
  obtain ⟨c, hc0, hcA, n₀, hn₀⟩ := exists_primitive_scaling A hx M hM hxM
  have hcoeff : ∀ n, (algebraMap L (LaurentSeries L) c⁻¹ * x).coeff n = c⁻¹ * x.coeff n := fun n => by
    rw [algebraMap_laurentSeries_eq_single, HahnSeries.coeff_single_zero_mul]
  obtain ⟨y, hy⟩ := exists_coeffMap_subtype_eq A (algebraMap L (LaurentSeries L) c⁻¹ * x) fun n => by
    rw [hcoeff]; exact hcA n
  refine ⟨c, hc0, y, ?_, ?_⟩
  · intro h
    have h1 := congrArg (fun s : LaurentSeries (IsLocalRing.ResidueField A) => s.coeff n₀) h
    simp only [coeffMap_coeff, HahnSeries.coeff_zero] at h1
    have h2 : (y.coeff n₀ : L) = 1 := by
      have := congrArg (fun s : LaurentSeries L => s.coeff n₀) hy
      simp only [coeffMap_coeff, hcoeff] at this
      rw [← hn₀]; exact this
    have h3 : y.coeff n₀ = 1 := Subtype.ext (by simpa using h2)
    rw [h3, map_one] at h1
    exact one_ne_zero h1
  · rw [hy, ← mul_assoc, ← map_mul, mul_inv_cancel₀ hc0, map_one, one_mul]

end Scaling

section Generators

variable (L : Type*) [Field L] [Algebra ℚ L] (N : ℕ) [NeZero N]

def gens : Set (LaurentSeries L) := ⇑(coeffEmb L) '' divisorExpansions N

theorem adjoin_gens_le : adjoin L (gens L N) ≤ laurentBaseChange L (modularFunctionFieldFull N) := by
  change adjoin L (gens L N) ≤ adjoin L _
  refine adjoin.mono L _ _ ?_
  rintro _ ⟨x, hx, rfl⟩
  exact ⟨x, IntermediateField.subset_adjoin ℚ _ hx, rfl⟩

theorem laurentBaseChange_le_adjoin_gens :
    laurentBaseChange L (modularFunctionFieldFull N) ≤ adjoin L (gens L N) := by
  change adjoin L _ ≤ adjoin L (gens L N)
  rw [adjoin_le_iff]
  rintro _ ⟨x, hx, rfl⟩
  have hx' : x ∈ Subfield.closure (Set.range (algebraMap ℚ (LaurentSeries ℚ)) ∪ divisorExpansions N) :=
    hx
  have hmap : coeffEmb L x ∈ (Subfield.closure
      (Set.range (algebraMap ℚ (LaurentSeries ℚ)) ∪ divisorExpansions N)).map (coeffEmb L) :=
    ⟨x, hx', rfl⟩
  rw [RingHom.map_field_closure] at hmap
  refine (Subfield.closure_le.mpr ?_) hmap
  rintro _ ⟨z, hz | hz, rfl⟩
  · obtain ⟨c, rfl⟩ := hz
    rw [algebraMap_apply_eq_single]
    change coeffMap (algebraMap ℚ L) (HahnSeries.single 0 c) ∈ adjoin L (gens L N)
    rw [coeffMap_single, ← algebraMap_laurentSeries_eq_single]
    exact (adjoin L (gens L N)).algebraMap_mem _
  · exact IntermediateField.subset_adjoin L _ ⟨z, hz, rfl⟩

theorem laurentBaseChange_eq_adjoin_gens :
    laurentBaseChange L (modularFunctionFieldFull N) = adjoin L (gens L N) :=
  le_antisymm (laurentBaseChange_le_adjoin_gens L N) (adjoin_gens_le L N)

theorem exists_fg_coeff_mem {x : LaurentSeries L} (hx : x ∈ Algebra.adjoin L (gens L N)) :
    ∃ M : Submodule ℤ L, M.FG ∧ ∀ n, x.coeff n ∈ M := by
  induction hx using Algebra.adjoin_induction with
  | mem x hx =>
      obtain ⟨_, ⟨d, hd, hdN, rfl⟩, rfl⟩ := hx
      refine ⟨Submodule.span ℤ {(1 : L)}, Submodule.fg_span (Set.finite_singleton _), fun n => ?_⟩
      obtain ⟨m, hm⟩ : ∃ m : ℤ, (coeffEmb L (qExpand ℚ d jq)).coeff n = (m : L) := by
        rw [coeffEmb_coeff]
        by_cases hdn : (d : ℤ) ∣ n
        · obtain ⟨n', rfl⟩ := hdn
          refine ⟨(jqModC ℤ).coeff n', ?_⟩
          rw [qExpand_coeff_mul, ← jqModC_rat, coeff_jqModC_eq_intCast, map_intCast]
        · exact ⟨0, by rw [qExpand_coeff_of_not_dvd _ _ hdn, map_zero, Int.cast_zero]⟩
      rw [hm, ← zsmul_one]
      exact Submodule.smul_mem _ _ (Submodule.subset_span rfl)
  | algebraMap a =>
      refine ⟨Submodule.span ℤ {a}, Submodule.fg_span (Set.finite_singleton _), fun n => ?_⟩
      rw [algebraMap_laurentSeries_eq_single, HahnSeries.coeff_single]
      split_ifs
      · exact Submodule.subset_span rfl
      · exact Submodule.zero_mem _
  | add x y _ _ hx hy =>
      obtain ⟨M₁, hM₁, h₁⟩ := hx
      obtain ⟨M₂, hM₂, h₂⟩ := hy
      refine ⟨M₁ ⊔ M₂, hM₁.sup hM₂, fun n => ?_⟩
      rw [HahnSeries.coeff_add]
      exact Submodule.add_mem _ (Submodule.mem_sup_left (h₁ n)) (Submodule.mem_sup_right (h₂ n))
  | mul x y _ _ hx hy =>
      obtain ⟨M₁, hM₁, h₁⟩ := hx
      obtain ⟨M₂, hM₂, h₂⟩ := hy
      refine ⟨M₁ * M₂, hM₁.mul hM₂, fun n => ?_⟩
      rw [HahnSeries.coeff_mul]
      exact Submodule.sum_mem _ fun ij _ => Submodule.mul_mem_mul (h₁ _) (h₂ _)

theorem coeffEmb_qExpand_jq (d : ℕ) [NeZero d] :
    coeffEmb L (qExpand ℚ d jq) = qExpand L d (jqModC L) := by
  rw [coeffEmb, ← jqModC_rat, coeffMap_qExpand, coeffMap_jqModC]

end Generators

section Gauss

variable {L : Type*} [Field L] [Algebra ℚ L] (A : ValuationSubring L) (N : ℕ) [NeZero N]

local notation "FF" => laurentBaseChange L (modularFunctionFieldFull N)
local notation "kk" => IsLocalRing.ResidueField A

theorem ι_qExpand_jqModC (d : ℕ) [NeZero d] :
    ι A (qExpand A d (jqModC A)) = qExpand L d (jqModC L) := by
  rw [coeffMap_qExpand, coeffMap_jqModC]

theorem ϖ_qExpand_jqModC (d : ℕ) [NeZero d] :
    ϖ A (qExpand A d (jqModC A)) = qExpand kk d (jqModC kk) := by
  rw [coeffMap_qExpand, coeffMap_jqModC]

theorem qExpand_jqModC_ne_zero (K : Type*) [Field K] (d : ℕ) [NeZero d] :
    qExpand K d (jqModC K) ≠ 0 := fun h =>
  jqModC_ne_zero_of_nontrivial K (qExpand_injective (R := K) (N := d) (by rw [h, map_zero]))

theorem exists_frac_form (f : FF) (hf : f ≠ 0) :
    ∃ c : L, c ≠ 0 ∧ ∃ x₀ y₀ : LaurentSeries A, ϖ A x₀ ≠ 0 ∧ ϖ A y₀ ≠ 0 ∧
      (f : LaurentSeries L) * ι A y₀ = algebraMap L (LaurentSeries L) c * ι A x₀ := by
  have hfF : (f : LaurentSeries L) ∈ adjoin L (gens L N) := laurentBaseChange_le_adjoin_gens L N f.2
  obtain ⟨r, hr, s, hs, hrs⟩ := (mem_adjoin_iff_div (F := L)).mp hfF
  have hf0' : (f : LaurentSeries L) ≠ 0 := fun h => hf (Subtype.ext h)
  have hr0 : r ≠ 0 := by rintro rfl; exact hf0' (by rw [hrs, zero_div])
  have hs0 : s ≠ 0 := by rintro rfl; exact hf0' (by rw [hrs, div_zero])
  obtain ⟨Mr, hMr, hrM⟩ := exists_fg_coeff_mem L N hr
  obtain ⟨Ms, hMs, hsM⟩ := exists_fg_coeff_mem L N hs
  obtain ⟨cr, hcr, r₀, hr₀, hr'⟩ := exists_primitive_form A hr0 Mr hMr hrM
  obtain ⟨cs, hcs, s₀, hs₀, hs'⟩ := exists_primitive_form A hs0 Ms hMs hsM
  have hιs : ι A s₀ ≠ 0 := by rw [Ne, ι_eq_zero_iff]; exact ϖ_ne_zero_ne_zero hs₀
  refine ⟨cr / cs, div_ne_zero hcr hcs, r₀, s₀, hr₀, hs₀, ?_⟩
  rw [hrs, hr', hs', map_div₀]
  field_simp

def gaussRing : ValuationSubring FF where
  carrier := {f | IsInt A (f : LaurentSeries L)}
  mul_mem' {f g} hf hg := by
    change IsInt A ((f * g : FF) : LaurentSeries L)
    rw [IntermediateField.coe_mul]; exact hf.mul hg
  one_mem' := by change IsInt A ((1 : FF) : LaurentSeries L); exact IsInt.one
  add_mem' {f g} hf hg := by
    change IsInt A ((f + g : FF) : LaurentSeries L)
    rw [IntermediateField.coe_add]; exact hf.add hg
  zero_mem' := by change IsInt A ((0 : FF) : LaurentSeries L); exact IsInt.zero
  neg_mem' {f} hf := by
    change IsInt A ((-f : FF) : LaurentSeries L)
    rw [IntermediateField.coe_neg]; exact hf.neg
  mem_or_inv_mem' f := by
    by_cases hf : f = 0
    · left; subst hf; change IsInt A ((0 : FF) : LaurentSeries L); exact IsInt.zero
    obtain ⟨c, hc0, x₀, y₀, hx₀, hy₀, h⟩ := exists_frac_form A N f hf
    rcases A.mem_or_inv_mem c with hc | hc
    · left
      refine ⟨HahnSeries.C ⟨c, hc⟩ * x₀, y₀, hy₀, ?_⟩
      rw [h, map_mul, ι_C]
    · right
      change IsInt A ((f⁻¹ : FF) : LaurentSeries L)
      refine ⟨HahnSeries.C ⟨c⁻¹, hc⟩ * y₀, x₀, hx₀, ?_⟩
      have hf' : (f : LaurentSeries L) ≠ 0 := fun h' => hf (Subtype.ext h')
      rw [IntermediateField.coe_inv, map_mul, ι_C]
      have hcC : algebraMap L (LaurentSeries L) c ≠ 0 := (_root_.map_ne_zero _).mpr hc0
      calc (f : LaurentSeries L)⁻¹ * ι A x₀
          = (f : LaurentSeries L)⁻¹ * (algebraMap L (LaurentSeries L) c)⁻¹ *
              ((f : LaurentSeries L) * ι A y₀) := by rw [h]; field_simp
        _ = algebraMap L (LaurentSeries L) (↑(⟨c⁻¹, hc⟩ : A) : L) * ι A y₀ := by
              rw [map_inv₀]; field_simp

theorem mem_gaussRing_iff (f : FF) : f ∈ gaussRing A N ↔ IsInt A (f : LaurentSeries L) := Iff.rfl

end Gauss

section Residue

variable {L : Type*} [Field L] [Algebra ℚ L] (A : ValuationSubring L) (N : ℕ) [NeZero N]

local notation "FF" => laurentBaseChange L (modularFunctionFieldFull N)
local notation "kk" => IsLocalRing.ResidueField A

theorem gens_eq_divisorExpansionsC : gens L N = divisorExpansionsC L N := by
  ext x
  constructor
  · rintro ⟨_, ⟨d, hd, hdN, rfl⟩, rfl⟩
    exact ⟨d, hd, hdN, coeffEmb_qExpand_jq L d⟩
  · rintro ⟨d, hd, hdN, rfl⟩
    exact ⟨_, ⟨d, hd, hdN, rfl⟩, coeffEmb_qExpand_jq L d⟩

theorem laurentBaseChange_eq_fullC :
    laurentBaseChange L (modularFunctionFieldFull N) = modularFunctionFieldFullC L N := by
  rw [laurentBaseChange_eq_adjoin_gens, gens_eq_divisorExpansionsC]; rfl

theorem exists_witness (f : gaussRing A N) :
    ∃ p : LaurentSeries A × LaurentSeries A,
      ϖ A p.2 ≠ 0 ∧ ((f : FF) : LaurentSeries L) * ι A p.2 = ι A p.1 := by
  obtain ⟨x, y, hy, h⟩ := f.2
  exact ⟨(x, y), hy, h⟩

def wit (f : gaussRing A N) : LaurentSeries A × LaurentSeries A :=
  Classical.choose (exists_witness A N f)

theorem wit_spec (f : gaussRing A N) :
    ϖ A (wit A N f).2 ≠ 0 ∧ ((f : FF) : LaurentSeries L) * ι A (wit A N f).2 = ι A (wit A N f).1 :=
  Classical.choose_spec (exists_witness A N f)

def resL (f : gaussRing A N) : LaurentSeries kk :=
  ϖ A (wit A N f).1 / ϖ A (wit A N f).2

theorem resL_eq {f : gaussRing A N} {x y : LaurentSeries A} (hy : ϖ A y ≠ 0)
    (h : ((f : FF) : LaurentSeries L) * ι A y = ι A x) : resL A N f = ϖ A x / ϖ A y := by
  obtain ⟨hy', h'⟩ := wit_spec A N f
  have hc := IsInt.cross (A := A) h' h
  rw [resL, div_eq_div_iff hy' hy, ← map_mul, ← map_mul, hc]

def resHom : gaussRing A N →+* LaurentSeries kk where
  toFun := resL A N
  map_one' := by
    rw [resL_eq A N (x := 1) (y := 1) (by simp) (by simp)]; simp
  map_mul' f g := by
    obtain ⟨hf, hf'⟩ := wit_spec A N f
    obtain ⟨hg, hg'⟩ := wit_spec A N g
    have h : (((f * g : gaussRing A N) : FF) : LaurentSeries L) * ι A ((wit A N f).2 * (wit A N g).2)
        = ι A ((wit A N f).1 * (wit A N g).1) := by
      rw [map_mul, map_mul, ← hf', ← hg']; push_cast; ring
    rw [resL_eq A N (by rw [map_mul]; exact mul_ne_zero hf hg) h]
    change _ = resL A N f * resL A N g
    rw [resL, resL, map_mul, map_mul, mul_div_mul_comm]
  map_zero' := by
    rw [resL_eq A N (x := 0) (y := 1) (by simp) (by simp)]; simp
  map_add' f g := by
    obtain ⟨hf, hf'⟩ := wit_spec A N f
    obtain ⟨hg, hg'⟩ := wit_spec A N g
    have h : (((f + g : gaussRing A N) : FF) : LaurentSeries L) * ι A ((wit A N f).2 * (wit A N g).2)
        = ι A ((wit A N f).1 * (wit A N g).2 + (wit A N g).1 * (wit A N f).2) := by
      rw [map_add, map_mul, map_mul, map_mul, ← hf', ← hg']; push_cast; ring
    rw [resL_eq A N (by rw [map_mul]; exact mul_ne_zero hf hg) h]
    change _ = resL A N f + resL A N g
    rw [resL, resL, div_add_div _ _ hf hg, map_add, map_mul, map_mul, map_mul]
    ring

theorem resHom_apply (f : gaussRing A N) : resHom A N f = resL A N f := rfl

theorem resHom_eq {f : gaussRing A N} {x y : LaurentSeries A} (hy : ϖ A y ≠ 0)
    (h : ((f : FF) : LaurentSeries L) * ι A y = ι A x) : resHom A N f = ϖ A x / ϖ A y :=
  resL_eq A N hy h

theorem ι_mem_gaussRing {y : LaurentSeries A} (hyF : ι A y ∈ FF) : (⟨ι A y, hyF⟩ : FF) ∈ gaussRing A N :=
  ⟨y, 1, by simp, by simp⟩

theorem resHom_ι {y : LaurentSeries A} (hyF : ι A y ∈ FF) :
    resHom A N ⟨⟨ι A y, hyF⟩, ι_mem_gaussRing A N hyF⟩ = ϖ A y := by
  rw [resHom_eq A N (x := y) (y := 1) (by simp) (by simp)]; simp

theorem resHom_eq_zero_iff (f : gaussRing A N) :
    resHom A N f = 0 ↔ f ∈ IsLocalRing.maximalIdeal (gaussRing A N) := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  obtain ⟨hy, h⟩ := wit_spec A N f
  constructor
  · rintro h0 ⟨u, rfl⟩
    have := congrArg (resHom A N) u.mul_inv
    rw [map_mul, h0, zero_mul, map_one] at this
    exact zero_ne_one this
  · intro hu
    by_contra h0
    apply hu
    rw [resHom_eq A N hy h, div_eq_zero_iff, or_iff_left hy] at h0
    have hf0 : ((f : FF) : LaurentSeries L) ≠ 0 := by
      intro hf
      rw [hf, zero_mul, eq_comm, ι_eq_zero_iff] at h
      exact h0 (by rw [h, map_zero])
    have hf0' : (f : FF) ≠ 0 := fun h' => hf0 (by rw [h']; rfl)
    have hinv : (f : FF)⁻¹ ∈ gaussRing A N := by
      refine ⟨(wit A N f).2, (wit A N f).1, h0, ?_⟩
      rw [IntermediateField.coe_inv]
      exact IsInt.inv_of (A := A) h0 h
    exact ⟨⟨f, ⟨(f : FF)⁻¹, hinv⟩, Subtype.ext (mul_inv_cancel₀ hf0'),
      Subtype.ext (inv_mul_cancel₀ hf0')⟩, rfl⟩

theorem coe_algebraMap (c : L) :
    ((algebraMap L FF c : FF) : LaurentSeries L) = algebraMap L (LaurentSeries L) c := rfl

theorem algebraMap_mem_gaussRing_iff (c : L) : algebraMap L FF c ∈ gaussRing A N ↔ c ∈ A := by
  constructor
  · rintro ⟨x, y, hy, h⟩
    rw [coe_algebraMap] at h
    by_contra hc
    have hc0 : c ≠ 0 := by rintro rfl; exact hc A.zero_mem
    have hci : c⁻¹ ∈ A := (A.mem_or_inv_mem c).resolve_left hc
    have hcm : (⟨c⁻¹, hci⟩ : A) ∈ IsLocalRing.maximalIdeal A := by
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      rintro ⟨u, hu⟩
      apply hc
      have h1 : ((↑(u⁻¹ : Aˣ) : A) : L) * c⁻¹ = 1 := by
        have := congrArg (fun a : A => (a : L)) u.inv_val
        simpa [hu] using this
      rw [mul_inv_eq_one₀ hc0] at h1
      rw [← h1]; exact SetLike.coe_mem _
    have hyx : y = HahnSeries.C ⟨c⁻¹, hci⟩ * x := by
      apply ι_injective A
      rw [map_mul, ι_C, ← h, ← mul_assoc, ← map_mul]
      simp [inv_mul_cancel₀ hc0]
    apply hy
    rw [ϖ_eq_zero_iff]
    intro n
    rw [hyx, HahnSeries.C_mul_eq_smul, HahnSeries.coeff_smul, smul_eq_mul]
    exact Ideal.mul_mem_right _ _ hcm
  · intro hc
    refine ⟨HahnSeries.C ⟨c, hc⟩, 1, by simp, ?_⟩
    rw [coe_algebraMap, ι_C, map_one, mul_one]

theorem resHom_algebraMap (a : A) (h : algebraMap L FF a ∈ gaussRing A N) :
    resHom A N ⟨algebraMap L FF a, h⟩ = algebraMap kk (LaurentSeries kk) (IsLocalRing.residue A a) := by
  rw [resHom_eq A N (x := HahnSeries.C a) (y := 1) (by simp)
    (by rw [map_one, mul_one]; change algebraMap L (LaurentSeries L) (a : L) = _; rw [ι_C]),
    ϖ_C, map_one, div_one]

theorem coe_smul' (c : L) (f : FF) :
    ((c • f : FF) : LaurentSeries L) = algebraMap L (LaurentSeries L) c * (f : LaurentSeries L) := by
  rw [IntermediateField.coe_smul, Algebra.smul_def]

theorem exists_smul_mem_gaussRing (f : FF) (hf : f ≠ 0) :
    ∃ c : L, ∃ h : c • f ∈ gaussRing A N, resHom A N ⟨c • f, h⟩ ≠ 0 := by
  obtain ⟨c, hc0, x₀, y₀, hx₀, hy₀, h⟩ := exists_frac_form A N f hf
  have key : ((c⁻¹ • f : FF) : LaurentSeries L) * ι A y₀ = ι A x₀ := by
    rw [coe_smul', mul_assoc, h, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hc0, map_one, one_mul]
  have hmem : c⁻¹ • f ∈ gaussRing A N := (mem_gaussRing_iff A N _).mpr ⟨x₀, y₀, hy₀, key⟩
  refine ⟨c⁻¹, hmem, ?_⟩
  rw [Ne, resHom_eq A N (f := ⟨_, hmem⟩) hy₀ key]
  exact div_ne_zero hx₀ hy₀

end Residue

section PolyJ

variable {L : Type*} [Field L] [Algebra ℚ L] (A : ValuationSubring L) (N : ℕ) [NeZero N]

local notation "FF" => laurentBaseChange L (modularFunctionFieldFull N)
local notation "kk" => IsLocalRing.ResidueField A

theorem exists_primitive_poly {r : L[X]} (hr : r ≠ 0) :
    ∃ c : L, c ≠ 0 ∧ ∃ r₀ : A[X], r = C c * r₀.map A.subtype ∧ r₀.map (IsLocalRing.residue A) ≠ 0 := by
  have hne : (r.support.image r.coeff).Nonempty := by
    rw [Finset.image_nonempty, Polynomial.nonempty_support_iff]; exact hr
  obtain ⟨c, hcT, hcmax⟩ := Finset.exists_max_image _ A.valuation hne
  obtain ⟨n₀, hn₀, rfl⟩ := Finset.mem_image.mp hcT
  have hc0 : r.coeff n₀ ≠ 0 := Polynomial.mem_support_iff.mp hn₀
  have hvx : ∀ n, A.valuation (r.coeff n) ≤ A.valuation (r.coeff n₀) := fun n => by
    by_cases hn : n ∈ r.support
    · exact hcmax _ (Finset.mem_image_of_mem _ hn)
    · rw [Polynomial.notMem_support_iff.mp hn, map_zero]; exact zero_le'
  have hcA : ∀ n, (r.coeff n₀)⁻¹ * r.coeff n ∈ A := fun n => by
    rw [← A.valuation_le_one_iff, map_mul, map_inv₀]
    have hc' : A.valuation (r.coeff n₀) ≠ 0 := by simpa using hc0
    rw [inv_mul_le_one₀ (zero_lt_iff.mpr hc')]
    exact hvx n
  obtain ⟨r₀, hr₀⟩ : ∃ r₀ : A[X], r₀.map A.subtype = C (r.coeff n₀)⁻¹ * r := by
    rw [← Polynomial.mem_lifts, Polynomial.lifts_iff_coeff_lifts]
    intro n
    rw [Polynomial.coeff_C_mul]
    exact ⟨⟨_, hcA n⟩, rfl⟩
  refine ⟨r.coeff n₀, hc0, r₀, ?_, ?_⟩
  · rw [hr₀, ← mul_assoc, ← map_mul, mul_inv_cancel₀ hc0, map_one, one_mul]
  · intro h
    have h1 := congrArg (fun p : (IsLocalRing.ResidueField A)[X] => p.coeff n₀) h
    simp only [Polynomial.coeff_map, Polynomial.coeff_zero] at h1
    have h2 : (r₀.coeff n₀ : L) = 1 := by
      have := congrArg (fun p : L[X] => p.coeff n₀) hr₀
      simp only [Polynomial.coeff_map, Polynomial.coeff_C_mul, inv_mul_cancel₀ hc0] at this
      exact this
    have h3 : r₀.coeff n₀ = 1 := Subtype.ext (by simpa using h2)
    rw [h3, map_one] at h1
    exact one_ne_zero h1

theorem algebraMap_laurentSeries_A (a : A) : algebraMap A (LaurentSeries A) a = HahnSeries.C a := by
  rw [HahnSeries.algebraMap_apply']
  have h1 : algebraMap A (PowerSeries A) a = PowerSeries.C a := by simp
  rw [h1, HahnSeries.ofPowerSeries_C]

theorem ι_aeval (p : A[X]) : ι A (aeval (jqModC A) p) = aeval (jqModC L) (p.map A.subtype) := by
  rw [aeval_def, aeval_def, hom_eval₂, eval₂_map, coeffMap_jqModC]
  congr 1
  refine RingHom.ext fun a => ?_
  change ι A (algebraMap A (LaurentSeries A) a) = algebraMap L (LaurentSeries L) (a : L)
  rw [algebraMap_laurentSeries_A]
  exact ι_C A a

theorem ϖ_aeval (p : A[X]) :
    ϖ A (aeval (jqModC A) p) = aeval (jqModC kk) (p.map (IsLocalRing.residue A)) := by
  rw [aeval_def, aeval_def, hom_eval₂, eval₂_map, coeffMap_jqModC]
  congr 1
  refine RingHom.ext fun a => ?_
  change ϖ A (algebraMap A (LaurentSeries A) a) =
    algebraMap kk (LaurentSeries kk) (IsLocalRing.residue A a)
  rw [algebraMap_laurentSeries_A]
  exact ϖ_C A a

theorem aeval_jqModC_ne_zero {K : Type*} [Field K] {p : K[X]} (hp : p ≠ 0) :
    aeval (jqModC K) p ≠ 0 := fun h =>
  hp ((transcendental_iff.mp (ModularCurve.transcendental_jqModC K)) p h)

def jF : FF := ⟨coeffEmb L jq, coeffEmb_mem_laurentBaseChange L (modularFunctionField_le_full N (jq_mem N))⟩

theorem coe_jF : ((jF N : FF) : LaurentSeries L) = jqModC L := coeffMap_jqModC _

theorem coe_jF' : ((jF N : FF) : LaurentSeries L) = ι A (jqModC A) := by
  rw [coe_jF, coeffMap_jqModC]

def jbar (K : Type*) [Field K] : modularFunctionFieldFullC K N := ⟨jqModC K, jqModC_mem_full K N⟩

theorem exists_resHom_eq {z : LaurentSeries kk} (hz : z ∈ modularFunctionFieldFullC kk N) :
    ∃ f : gaussRing A N, resHom A N f = z := by
  let S : Subfield (LaurentSeries kk) :=
    { carrier := Set.range (resHom A N)
      mul_mem' := by rintro _ _ ⟨f, rfl⟩ ⟨g, rfl⟩; exact ⟨f * g, map_mul _ _ _⟩
      one_mem' := ⟨1, map_one _⟩
      add_mem' := by rintro _ _ ⟨f, rfl⟩ ⟨g, rfl⟩; exact ⟨f + g, map_add _ _ _⟩
      zero_mem' := ⟨0, map_zero _⟩
      neg_mem' := by rintro _ ⟨f, rfl⟩; exact ⟨-f, map_neg _ _⟩
      inv_mem' := by
        rintro _ ⟨f, rfl⟩
        by_cases h0 : resHom A N f = 0
        · exact ⟨0, by rw [h0, inv_zero, map_zero]⟩
        · have hu : IsUnit f := by
            by_contra hu
            exact h0 ((resHom_eq_zero_iff A N f).mpr
              ((IsLocalRing.mem_maximalIdeal _).mpr (mem_nonunits_iff.mpr hu)))
          obtain ⟨u, rfl⟩ := hu
          refine ⟨↑u⁻¹, ?_⟩
          exact (inv_eq_of_mul_eq_one_left (by rw [← map_mul, Units.inv_mul, map_one])).symm }
  have hle : Subfield.closure (Set.range (algebraMap kk (LaurentSeries kk)) ∪ divisorExpansionsC kk N)
      ≤ S := by
    rw [Subfield.closure_le]
    rintro z (⟨t, rfl⟩ | ⟨d, hd, hdN, rfl⟩)
    · obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective t
      exact ⟨⟨_, (algebraMap_mem_gaussRing_iff A N (a : L)).mpr a.2⟩, resHom_algebraMap A N a _⟩
    · have hmem : ι A (qExpand A d (jqModC A)) ∈ FF := by
        rw [ι_qExpand_jqModC, ← coeffEmb_qExpand_jq]
        exact coeffEmb_mem_laurentBaseChange L (jqd_mem_full N hdN)
      exact ⟨_, (resHom_ι A N hmem).trans (ϖ_qExpand_jqModC A d)⟩
  obtain ⟨f, hf⟩ := hle (show z ∈ Subfield.closure _ from hz)
  exact ⟨f, hf⟩

end PolyJ

section Image

variable {L : Type*} [Field L] [Algebra ℚ L] (A : ValuationSubring L) (N : ℕ) [NeZero N]

local notation "FF" => laurentBaseChange L (modularFunctionFieldFull N)
local notation "kk" => IsLocalRing.ResidueField A
local notation "Fb" => modularFunctionFieldFullC (IsLocalRing.ResidueField A) N

theorem exists_inv_mem_maximalIdeal {c : L} (hc : c ∉ A) :
    ∃ h : c⁻¹ ∈ A, (⟨c⁻¹, h⟩ : A) ∈ IsLocalRing.maximalIdeal A := by
  have hc0 : c ≠ 0 := by rintro rfl; exact hc A.zero_mem
  have hci : c⁻¹ ∈ A := (A.mem_or_inv_mem c).resolve_left hc
  refine ⟨hci, ?_⟩
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  rintro ⟨u, hu⟩
  apply hc
  have h1 : ((↑(u⁻¹ : Aˣ) : A) : L) * c⁻¹ = 1 := by
    have := congrArg (fun a : A => (a : L)) u.inv_val
    simpa [hu] using this
  rw [mul_inv_eq_one₀ hc0] at h1
  rw [← h1]; exact SetLike.coe_mem _

set_option maxHeartbeats 6400000 in

theorem exists_adjoin_coe_eq_resHom {g : FF} (hgK : g ∈ IntermediateField.adjoin L {(jF N : FF)})
    (hgO : g ∈ gaussRing A N) :
    ∃ t : IntermediateField.adjoin kk {(jbar N kk : Fb)},
      (((t : Fb) : LaurentSeries kk)) = resHom A N ⟨g, hgO⟩ := by
  rw [mem_adjoin_simple_iff] at hgK
  obtain ⟨r, s, hrs⟩ := hgK
  by_cases hg0 : g = 0
  · refine ⟨0, ?_⟩
    have : (⟨g, hgO⟩ : gaussRing A N) = 0 := Subtype.ext hg0
    rw [this, map_zero]; rfl
  have hr0 : r ≠ 0 := by rintro rfl; apply hg0; rw [hrs, map_zero, zero_div]
  have hs0 : s ≠ 0 := by rintro rfl; apply hg0; rw [hrs, map_zero, div_zero]
  obtain ⟨cr, hcr, r₀, hr', hr₀⟩ := exists_primitive_poly A hr0
  obtain ⟨cs, hcs, s₀, hs', hs₀⟩ := exists_primitive_poly A hs0
  obtain ⟨R₀, hR₀def⟩ : ∃ R₀, R₀ = aeval (jqModC A) r₀ := ⟨_, rfl⟩
  obtain ⟨S₀, hS₀def⟩ : ∃ S₀, S₀ = aeval (jqModC A) s₀ := ⟨_, rfl⟩
  have hιR : aeval (jqModC L) (r₀.map A.subtype) = ι A R₀ := by rw [hR₀def, ι_aeval]
  have hιS : aeval (jqModC L) (s₀.map A.subtype) = ι A S₀ := by rw [hS₀def, ι_aeval]
  have hϖR : ϖ A R₀ = aeval (jqModC kk) (r₀.map (IsLocalRing.residue A)) := by rw [hR₀def, ϖ_aeval]
  have hϖS : ϖ A S₀ = aeval (jqModC kk) (s₀.map (IsLocalRing.residue A)) := by rw [hS₀def, ϖ_aeval]
  have hR₀ : ϖ A R₀ ≠ 0 := by rw [hϖR]; exact aeval_jqModC_ne_zero hr₀
  have hS₀ : ϖ A S₀ ≠ 0 := by rw [hϖS]; exact aeval_jqModC_ne_zero hs₀
  have hιS₀ : ι A S₀ ≠ 0 := by rw [Ne, ι_eq_zero_iff]; exact ϖ_ne_zero_ne_zero hS₀
  have hιR₀ : ι A R₀ ≠ 0 := by rw [Ne, ι_eq_zero_iff]; exact ϖ_ne_zero_ne_zero hR₀
  have e0 : ∀ p : L[X], ((aeval (jF N) p : FF) : LaurentSeries L) = aeval (jqModC L) p := fun p => by
    rw [← coe_jF (L := L) N]
    exact (aeval_algHom_apply (laurentBaseChange L (modularFunctionFieldFull N)).val (jF N) p).symm
  have e1 : (g : LaurentSeries L) = aeval (jqModC L) r / aeval (jqModC L) s := by
    rw [hrs, IntermediateField.coe_div, e0, e0]
  have hgcoe : (g : LaurentSeries L) * ι A S₀ = algebraMap L _ (cr / cs) * ι A R₀ := by
    rw [e1, hr', hs', map_mul, map_mul, aeval_C, aeval_C, hιR, hιS, map_div₀]
    have hcs' : algebraMap L (LaurentSeries L) cs ≠ 0 := (_root_.map_ne_zero _).mpr hcs
    field_simp
  by_cases he : cr / cs ∈ A
  · have hw : (g : LaurentSeries L) * ι A S₀ = ι A (HahnSeries.C ⟨cr / cs, he⟩ * R₀) := by
      rw [hgcoe, map_mul, ι_C]
    have e0k : ∀ p : kk[X], ((aeval (jbar N kk : Fb) p : Fb) : LaurentSeries kk) = aeval (jqModC kk) p :=
      fun p => (aeval_algHom_apply (modularFunctionFieldFullC kk N).val (jbar N kk) p).symm
    have hmemK : ∀ p : kk[X], aeval (jbar N kk : Fb) p ∈ IntermediateField.adjoin kk {(jbar N kk : Fb)} :=
      fun p => IntermediateField.algebra_adjoin_le_adjoin kk _ (Polynomial.aeval_mem_adjoin_singleton kk _)
    refine ⟨⟨aeval (jbar N kk : Fb) (C (IsLocalRing.residue A ⟨cr / cs, he⟩) * r₀.map (IsLocalRing.residue A)) /
      aeval (jbar N kk : Fb) (s₀.map (IsLocalRing.residue A)), div_mem (hmemK _) (hmemK _)⟩, ?_⟩
    change (((aeval (jbar N kk : Fb) (C (IsLocalRing.residue A ⟨cr / cs, he⟩) * r₀.map (IsLocalRing.residue A)) /
      aeval (jbar N kk : Fb) (s₀.map (IsLocalRing.residue A)) : Fb)) : LaurentSeries kk) = _
    rw [resHom_eq A N (f := ⟨g, hgO⟩) hS₀ hw, map_mul (ϖ A), ϖ_C, hϖR, hϖS,
      IntermediateField.coe_div, map_mul, IntermediateField.coe_mul, e0k, e0k, aeval_C]
    rw [e0k]
  · exfalso
    obtain ⟨hei, hem⟩ := exists_inv_mem_maximalIdeal A he
    have he0 : cr / cs ≠ 0 := div_ne_zero hcr hcs
    have hg0' : (g : LaurentSeries L) ≠ 0 := fun h => hg0 (Subtype.ext h)
    obtain ⟨g', hg'⟩ : ∃ g' : FF, (g' : LaurentSeries L) = (g : LaurentSeries L)⁻¹ := ⟨g⁻¹, rfl⟩
    obtain ⟨a, ha, hres0⟩ : ∃ a : A, (a : L) = (cr / cs)⁻¹ ∧ IsLocalRing.residue A a = 0 :=
      ⟨⟨_, hei⟩, rfl, Ideal.Quotient.eq_zero_iff_mem.mpr hem⟩
    have hw : (g' : LaurentSeries L) * ι A R₀ = ι A (HahnSeries.C a * S₀) := by
      rw [hg', map_mul, ι_C, ha]
      have hC : algebraMap L (LaurentSeries L) (cr / cs) ≠ 0 := (_root_.map_ne_zero _).mpr he0
      calc (g : LaurentSeries L)⁻¹ * ι A R₀
          = (g : LaurentSeries L)⁻¹ * (algebraMap L (LaurentSeries L) (cr / cs))⁻¹ *
              ((g : LaurentSeries L) * ι A S₀) := by rw [hgcoe]; field_simp
        _ = algebraMap L (LaurentSeries L) (cr / cs)⁻¹ * ι A S₀ := by
              rw [map_inv₀]; field_simp
    have hinvO : g' ∈ gaussRing A N := (mem_gaussRing_iff A N _).mpr ⟨_, _, hR₀, hw⟩
    have hϖx : ϖ A (HahnSeries.C a * S₀) = 0 := by
      simp only [map_mul (ϖ A), ϖ_C, hres0, map_zero, zero_mul]
    have hres : resHom A N ⟨g', hinvO⟩ = 0 := by
      simp only [resHom_eq A N (f := ⟨g', hinvO⟩) hR₀ hw, hϖx, zero_div]
    have h1 : (⟨g, hgO⟩ : gaussRing A N) * ⟨g', hinvO⟩ = 1 := by
      apply Subtype.ext; apply Subtype.ext
      change (g : LaurentSeries L) * (g' : LaurentSeries L) = 1
      rw [hg']; exact mul_inv_cancel₀ hg0'
    have h2 : resHom A N ⟨g, hgO⟩ * resHom A N ⟨g', hinvO⟩ = 1 := by
      rw [← map_mul (resHom A N), h1, map_one]
    rw [hres, mul_zero] at h2
    exact zero_ne_one h2

set_option maxHeartbeats 6400000 in

theorem resHom_mem_fullC
    (hfin : Module.finrank (IntermediateField.adjoin L {(jF N : FF)}) FF =
      Module.finrank (IntermediateField.adjoin kk {(jbar N kk : Fb)}) Fb)
    (hpos : 0 < Module.finrank (IntermediateField.adjoin kk {(jbar N kk : Fb)}) Fb)
    (f : gaussRing A N) : resHom A N f ∈ modularFunctionFieldFullC kk N := by
  set K0 := IntermediateField.adjoin L {(jF N : FF)} with hK0
  set K0' := IntermediateField.adjoin kk {(jbar N kk : Fb)} with hK0'
  set n := Module.finrank K0' Fb with hn
  haveI : Module.Finite K0' Fb := Module.finite_of_finrank_pos hpos
  haveI : Module.Finite K0 FF := Module.finite_of_finrank_pos (by rw [hfin]; exact hpos)
  let bbar := Module.finBasisOfFinrankEq K0' Fb hn.symm
  have hb : ∀ i, ∃ b : gaussRing A N, resHom A N b = ((bbar i : Fb) : LaurentSeries kk) :=
    fun i => exists_resHom_eq A N (bbar i).2
  choose b hb using hb
  let v : Option (Fin n) → FF := fun o => o.elim (f : FF) (fun i => (b i : FF))
  have hdep : ¬ LinearIndependent K0 v := by
    intro hli
    have h := hli.fintype_card_le_finrank
    rw [Fintype.card_option, Fintype.card_fin, hfin] at h
    omega
  obtain ⟨g, hg, i₁, hi₁⟩ := Fintype.not_linearIndependent_iff.mp hdep
  obtain ⟨i₀, -, hi₀⟩ := Finset.exists_max_image Finset.univ
    (fun o => (gaussRing A N).valuation ((g o : K0) : FF)) Finset.univ_nonempty
  have hgi₀ : ((g i₀ : K0) : FF) ≠ 0 := by
    intro h0
    apply hi₁
    have := hi₀ i₁ (Finset.mem_univ _)
    rw [h0, map_zero, le_zero_iff, Valuation.zero_iff] at this
    exact ZeroMemClass.coe_eq_zero.mp this
  have hvpos : 0 < (gaussRing A N).valuation ((g i₀ : K0) : FF) := (Valuation.pos_iff _).mpr hgi₀

  let c : Option (Fin n) → FF := fun o => ((g o : K0) : FF) / ((g i₀ : K0) : FF)
  have hcK : ∀ o, c o ∈ K0 := fun o => div_mem (g o).2 (g i₀).2
  have hcO : ∀ o, c o ∈ gaussRing A N := fun o => by
    rw [← (gaussRing A N).valuation_le_one_iff]
    show (gaussRing A N).valuation (_ / _) ≤ 1
    rw [map_div₀, div_le_one₀ hvpos]
    exact hi₀ o (Finset.mem_univ o)
  have hci₀ : c i₀ = 1 := div_self hgi₀
  have hrel : ∑ o, c o * v o = 0 := by
    have h1 : ∑ o, ((g o : K0) : FF) * v o = 0 := by
      simpa only [IntermediateField.smul_def, smul_eq_mul] using hg
    calc ∑ o, c o * v o = ((g i₀ : K0) : FF)⁻¹ * ∑ o, ((g o : K0) : FF) * v o := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun o _ => by simp only [c]; ring
      _ = 0 := by rw [h1, mul_zero]

  have ht : ∀ o, ∃ t : K0', ((t : Fb) : LaurentSeries kk) = resHom A N ⟨c o, hcO o⟩ :=
    fun o => exists_adjoin_coe_eq_resHom A N (hcK o) (hcO o)
  choose t ht using ht
  have hti₀ : t i₀ = 1 := by
    have h1 : (⟨c i₀, hcO i₀⟩ : gaussRing A N) = 1 := Subtype.ext hci₀
    have h2 : ((t i₀ : Fb) : LaurentSeries kk) = (((1 : K0') : Fb) : LaurentSeries kk) := by
      rw [ht i₀, h1, map_one]; simp
    exact Subtype.ext (Subtype.ext h2)

  let w : Option (Fin n) → gaussRing A N := fun o => o.elim f b
  have hvw : ∀ o, v o = (w o : FF) := by rintro (_ | _) <;> rfl
  have hrelO : ∑ o, (⟨c o, hcO o⟩ : gaussRing A N) * w o = 0 := by
    apply Subtype.ext
    rw [AddSubmonoidClass.coe_finsetSum]
    first | simpa only [hvw] using hrel | (simp only [hvw] at hrel; exact hrel) | exact hrel
  have hres : ∑ o, ((t o : Fb) : LaurentSeries kk) * resHom A N (w o) = 0 := by
    have := congrArg (resHom A N) hrelO
    simpa only [map_sum, map_mul, map_zero, ht] using this
  have hwn : resHom A N (w none) = resHom A N f := rfl
  have hws : ∀ i, resHom A N (w (some i)) = ((bbar i : Fb) : LaurentSeries kk) := fun i => hb i
  rw [Fintype.sum_option, hwn] at hres
  simp only [hws] at hres

  by_cases htn : t none = 0
  · exfalso
    have hsum : ∑ i, ((t (some i) : Fb) : LaurentSeries kk) * ((bbar i : Fb) : LaurentSeries kk) = 0 := by
      simpa only [htn, ZeroMemClass.coe_zero, zero_mul, zero_add] using hres
    have hsum' : (∑ i, t (some i) • bbar i : Fb) = 0 := by
      apply Subtype.ext
      rw [AddSubmonoidClass.coe_finsetSum]
      first | simpa only [IntermediateField.smul_def, smul_eq_mul, IntermediateField.coe_mul] using hsum | (simp only [IntermediateField.smul_def, smul_eq_mul, IntermediateField.coe_mul] at hsum; exact hsum) | exact hsum
    have hall := Fintype.linearIndependent_iff.mp bbar.linearIndependent (fun i => t (some i)) hsum'
    have : t i₀ = 0 := by
      rcases i₀ with _ | i
      · exact htn
      · exact hall i
    rw [hti₀] at this
    exact one_ne_zero this
  · have htn' : ((t none : Fb) : LaurentSeries kk) ≠ 0 := by
      intro h; apply htn
      exact Subtype.ext (Subtype.ext (by simpa using h))
    have key : resHom A N f =
        -(∑ i, ((t (some i) : Fb) : LaurentSeries kk) * ((bbar i : Fb) : LaurentSeries kk)) /
          ((t none : Fb) : LaurentSeries kk) := by
      rw [eq_div_iff htn', eq_neg_iff_add_eq_zero, mul_comm]
      exact hres
    rw [key]
    exact div_mem (neg_mem (sum_mem fun i _ => mul_mem (t (some i) : Fb).2 (bbar i).2)) (t none : Fb).2

end Image

section Assembly

variable {L : Type*} [Field L] [Algebra ℚ L] (A : ValuationSubring L) (N : ℕ) [NeZero N]

local notation "FF" => laurentBaseChange L (modularFunctionFieldFull N)
local notation "kk" => IsLocalRing.ResidueField A
local notation "Fb" => modularFunctionFieldFullC (IsLocalRing.ResidueField A) N

theorem dedekindPsi_pos : 0 < dedekindPsi N := by
  have h1 : (1 : ℕ) ∈ N.divisors.filter Squarefree := by
    simp [Nat.mem_divisors, NeZero.ne N]
  calc 0 < N / 1 := by simpa using Nat.pos_of_ne_zero (NeZero.ne N)
    _ ≤ dedekindPsi N := Finset.single_le_sum (f := fun d => N / d) (fun _ _ => Nat.zero_le _) h1

def resF (hmem : ∀ f : gaussRing A N, resHom A N f ∈ modularFunctionFieldFullC kk N) :
    gaussRing A N →+* Fb :=
  (resHom A N).codRestrict (modularFunctionFieldFullC kk N) hmem

theorem coe_resF (hmem : ∀ f : gaussRing A N, resHom A N f ∈ modularFunctionFieldFullC kk N) (f : gaussRing A N) : ((resF A N hmem f : Fb) : LaurentSeries kk) = resHom A N f := rfl

theorem resF_ne_zero_iff (hmem : ∀ f : gaussRing A N, resHom A N f ∈ modularFunctionFieldFullC kk N) (f : gaussRing A N) : resF A N hmem f ≠ 0 ↔ resHom A N f ≠ 0 := by
  rw [Ne, Ne, ← coe_resF A N hmem f, ZeroMemClass.coe_eq_zero]

theorem resF_surjective (hmem : ∀ f : gaussRing A N, resHom A N f ∈ modularFunctionFieldFullC kk N) : Function.Surjective (resF A N hmem) := fun z => by
  obtain ⟨f, hf⟩ := exists_resHom_eq A N z.2
  exact ⟨f, Subtype.ext hf⟩

theorem ker_resF (hmem : ∀ f : gaussRing A N, resHom A N f ∈ modularFunctionFieldFullC kk N) : RingHom.ker (resF A N hmem) = IsLocalRing.maximalIdeal (gaussRing A N) := by
  ext f
  rw [RingHom.mem_ker, ← resHom_eq_zero_iff, ← coe_resF A N hmem f, ZeroMemClass.coe_eq_zero]

theorem resF_algebraMap (hmem : ∀ f : gaussRing A N, resHom A N f ∈ modularFunctionFieldFullC kk N) (a : A) (h : algebraMap L FF a ∈ gaussRing A N) :
    resF A N hmem ⟨algebraMap L FF a, h⟩ = algebraMap kk Fb (IsLocalRing.residue A a) :=
  Subtype.ext (resHom_algebraMap A N a h)

theorem exists_smul_mem_resF (hmem : ∀ f : gaussRing A N, resHom A N f ∈ modularFunctionFieldFullC kk N) (f : FF) (hf : f ≠ 0) :
    ∃ c : L, ∃ h : c • f ∈ gaussRing A N, resF A N hmem ⟨c • f, h⟩ ≠ 0 := by
  obtain ⟨c, h, hne⟩ := exists_smul_mem_gaussRing A N f hf
  exact ⟨c, h, (resF_ne_zero_iff A N hmem _).mpr hne⟩

theorem jF_mem_gaussRing : (jF N : FF) ∈ gaussRing A N :=
  (mem_gaussRing_iff A N _).mpr ⟨jqModC A, 1, by rw [map_one]; exact one_ne_zero,
    by rw [map_one, mul_one, coe_jF']⟩

theorem resHom_jF : resHom A N ⟨jF N, jF_mem_gaussRing A N⟩ = jqModC kk := by
  rw [resHom_eq A N (f := ⟨jF N, jF_mem_gaussRing A N⟩) (x := jqModC A) (y := 1)
    (by rw [map_one]; exact one_ne_zero) (by rw [map_one, mul_one]; exact coe_jF' A N),
    map_one, div_one, coeffMap_jqModC]

theorem resF_jF (hmem : ∀ f : gaussRing A N, resHom A N f ∈ modularFunctionFieldFullC kk N) : resF A N hmem ⟨jF N, jF_mem_gaussRing A N⟩ = jbar N kk :=
  Subtype.ext (resHom_jF A N)

theorem transcendental_jbar (K : Type*) [Field K] : Transcendental K (jbar N K : modularFunctionFieldFullC K N) :=
  fun h => transcendental_jqModC K
    ((isAlgebraic_algHom_iff (modularFunctionFieldFullC K N).val Subtype.val_injective).mpr h)

theorem finrank_adjoin_transport {E E' : IntermediateField L (LaurentSeries L)} (h : E = E')
    {x : LaurentSeries L} (hx : x ∈ E) (hx' : x ∈ E') :
    Module.finrank (IntermediateField.adjoin L ({⟨x, hx⟩} : Set E)) E =
      Module.finrank (IntermediateField.adjoin L ({⟨x, hx'⟩} : Set E')) E' := by
  subst h; rfl

theorem finrank_adjoin_jF (hN : (N : L) ≠ 0) :
    Module.finrank (IntermediateField.adjoin L {(jF N : FF)}) FF = dedekindPsi N := by
  have hj : (jF N : FF) = ⟨jqModC L, (laurentBaseChange_eq_fullC (L := L) N) ▸ jqModC_mem_full L N⟩ :=
    Subtype.ext (coe_jF N)
  rw [hj, finrank_adjoin_transport (laurentBaseChange_eq_fullC (L := L) N) _ (jqModC_mem_full L N)]
  exact ModularCurve.finrank_adjoin_jqModC_modularFunctionFieldFullC_eq_dedekindPsi L N hN

theorem exists_placeMap (hmem : ∀ f : gaussRing A N, resHom A N f ∈ modularFunctionFieldFullC kk N) [IsAlgClosed L] [IsCurveOver L FF] [IsCurveOver kk Fb]
    (hfin : Module.finrank (IntermediateField.adjoin L {(jF N : FF)}) FF =
      Module.finrank (IntermediateField.adjoin kk {(jbar N kk : Fb)}) Fb)
    (hpos : 0 < Module.finrank (IntermediateField.adjoin kk {(jbar N kk : Fb)}) Fb)
    (hgood : genusFF kk Fb = genusFF L FF) :
    ∃ r : Place L FF → Place kk Fb,
      ∀ f : gaussRing A N, resF A N hmem f ≠ 0 → ∀ D : Divisor L FF, (∀ P, D P = P.ord (f : FF)) →
        ∀ Q, Finsupp.mapDomain r D Q = Q.ord (resF A N hmem f : Fb) :=
  AlgebraicCurve.exists_placeMap_mapDomain_eq_ord_of_good_constantReduction A
    (gaussRing A N) (resF A N hmem) (algebraMap_mem_gaussRing_iff A N) (resF_surjective A N hmem)
    (ker_resF A N hmem) (fun a => resF_algebraMap A N hmem a _) (exists_smul_mem_resF A N hmem)
    ⟨⟨jF N, jF_mem_gaussRing A N⟩, by
      rw [resF_jF]
      exact ⟨transcendental_jbar N kk, hpos, hfin⟩⟩
    hgood

end Assembly

section Modular

theorem isAlgClosed_residueField {L : Type*} [Field L] [IsAlgClosed L] (A : ValuationSubring L) :
    IsAlgClosed (IsLocalRing.ResidueField A) := by
  refine IsAlgClosed.of_exists_root _ fun p hp hirr => ?_
  have hsurj : Function.Surjective (IsLocalRing.residue A) := IsLocalRing.residue_surjective
  have hlifts : p ∈ Polynomial.lifts (IsLocalRing.residue A) := by
    obtain ⟨q, hq⟩ := Polynomial.map_surjective (IsLocalRing.residue A) hsurj p
    exact ⟨q, hq⟩
  obtain ⟨q, hqp, hdeg, hqmonic⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hlifts hp
  have hdegL : (q.map (algebraMap A L)).degree ≠ 0 := by
    rw [Polynomial.degree_map_eq_of_injective (IsFractionRing.injective A L),
      Polynomial.degree_eq_natDegree hqmonic.ne_zero, hdeg]
    exact_mod_cast (Polynomial.natDegree_pos_iff_degree_pos.mpr
      (Polynomial.degree_pos_of_irreducible hirr)).ne'
  obtain ⟨y, hy⟩ := IsAlgClosed.exists_root (q.map (algebraMap A L)) hdegL
  have hyint : IsIntegral A y :=
    ⟨q, hqmonic, by rwa [Polynomial.IsRoot.def, Polynomial.eval_map] at hy⟩
  obtain ⟨a, rfl⟩ : ∃ a : A, algebraMap A L a = y := IsIntegrallyClosed.isIntegral_iff.mp hyint
  refine ⟨IsLocalRing.residue A a, ?_⟩
  have hqa : q.eval a = 0 := by
    have h := hy
    rw [Polynomial.IsRoot.def, Polynomial.eval_map, Polynomial.eval₂_hom] at h
    exact (IsFractionRing.injective A L) (h.trans (map_zero _).symm)
  rw [← hqp, Polynomial.eval_map, Polynomial.eval₂_hom, hqa, map_zero]

theorem natCast_residueField_ne_zero {L : Type*} [Field L] (A : ValuationSubring L) {ℓ : ℕ}
    [Fact ℓ.Prime] (hA : A.LiesOverPrime ℓ) {m : ℕ} (hm : ¬ ℓ ∣ m) :
    (m : IsLocalRing.ResidueField A) ≠ 0 := by
  intro h0
  have hℓ : ((ℓ : A) : L) ∈ A.nonunits := by first | simpa using hA | exact hA
  rw [ValuationSubring.coe_mem_nonunits_iff] at hℓ
  have hmA : (m : A) ∈ IsLocalRing.maximalIdeal A := by
    rw [← IsLocalRing.residue_eq_zero_iff, map_natCast]; exact h0
  have hcop : IsCoprime (ℓ : A) (m : A) :=
    Nat.Coprime.cast ((Nat.Prime.coprime_iff_not_dvd Fact.out).mpr hm)
  obtain ⟨u, v, huv⟩ := hcop
  apply (IsLocalRing.maximalIdeal.isMaximal A).ne_top
  rw [Ideal.eq_top_iff_one, ← huv]
  exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hℓ) (Ideal.mul_mem_left _ _ hmA)

variable (N : ℕ) [NeZero N] {ℓ : ℕ} [Fact ℓ.Prime]
  (A : ValuationSubring (AlgebraicClosure ℚ))

local notation "ℚ̄" => AlgebraicClosure ℚ
local notation "kk" => IsLocalRing.ResidueField A
local notation "Fb" => modularFunctionFieldFullC (IsLocalRing.ResidueField A) N

theorem finrank_data (hℓN : ¬ ℓ ∣ N) (hA : A.LiesOverPrime ℓ) :
    Module.finrank (IntermediateField.adjoin ℚ̄ {(jF N : modularFunctionFieldBar N)})
        (modularFunctionFieldBar N) =
      Module.finrank (IntermediateField.adjoin kk {(jbar N kk : Fb)}) Fb ∧
    0 < Module.finrank (IntermediateField.adjoin kk {(jbar N kk : Fb)}) Fb := by
  have hk : Module.finrank (IntermediateField.adjoin kk {(jbar N kk : Fb)}) Fb = dedekindPsi N :=
    ModularCurve.finrank_adjoin_jqModC_modularFunctionFieldFullC_eq_dedekindPsi kk N
      (natCast_residueField_ne_zero A hA hℓN)
  have hL := finrank_adjoin_jF (L := ℚ̄) N (Nat.cast_ne_zero.mpr (NeZero.ne N))
  exact ⟨hL.trans hk.symm, hk ▸ dedekindPsi_pos N⟩

theorem resHom_mem (hℓN : ¬ ℓ ∣ N) (hA : A.LiesOverPrime ℓ) (f : gaussRing A N) :
    resHom A N f ∈ modularFunctionFieldFullC kk N :=
  resHom_mem_fullC A N (finrank_data N A hℓN hA).1 (finrank_data N A hℓN hA).2 f

theorem genus_good [IsAlgClosed kk] (hℓN : ¬ ℓ ∣ N) (hA : A.LiesOverPrime ℓ) :
    genusFF kk Fb = genusFF ℚ̄ (laurentBaseChange ℚ̄ (modularFunctionFieldFull N)) :=
  genusFF_modularFunctionFieldFullC_eq_genusFF_modularFunctionFieldBar kk N
    (natCast_residueField_ne_zero A hA hℓN)

theorem c1 (hℓN : ¬ ℓ ∣ N) (hA : A.LiesOverPrime ℓ) :
    ∃ r : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N) →
        Place (IsLocalRing.ResidueField A) (modularFunctionFieldFullC (IsLocalRing.ResidueField A) N),
      ∀ (y : LaurentSeries A) (hy : coeffMap A.subtype y ∈ modularFunctionFieldBar N)
        (hyk : coeffMap (IsLocalRing.residue A) y ∈
          modularFunctionFieldFullC (IsLocalRing.ResidueField A) N),
        coeffMap (IsLocalRing.residue A) y ≠ 0 →
          ∀ D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N),
            (∀ P, D P = P.ord (⟨coeffMap A.subtype y, hy⟩ : modularFunctionFieldBar N)) →
              ∀ Q, Finsupp.mapDomain r D Q =
                Q.ord (⟨coeffMap (IsLocalRing.residue A) y, hyk⟩ :
                  modularFunctionFieldFullC (IsLocalRing.ResidueField A) N) := by
  haveI : IsAlgClosed kk := isAlgClosed_residueField A
  haveI : PerfectField kk := IsAlgClosed.perfectField _
  haveI : IsCurveOver ℚ̄ (modularFunctionFieldBar N) := isCurveOver_modularFunctionFieldBar N
  haveI : IsCurveOver kk Fb := isCurveOver_modularFunctionFieldFullC kk N
  have hmem := resHom_mem N A hℓN hA
  obtain ⟨r, hr⟩ := exists_placeMap A N hmem (finrank_data N A hℓN hA).1 (finrank_data N A hℓN hA).2
    (genus_good N A hℓN hA)
  refine ⟨r, fun y hy hyk hne D hD Q => ?_⟩
  have hres : resF A N hmem ⟨⟨ι A y, hy⟩, ι_mem_gaussRing A N hy⟩ = ⟨ϖ A y, hyk⟩ :=
    Subtype.ext (resHom_ι A N hy)
  have := hr ⟨⟨ι A y, hy⟩, ι_mem_gaussRing A N hy⟩ (by rw [hres]; exact fun h => hne (congrArg Subtype.val h)) D hD Q
  rwa [hres] at this

end Modular

end W7G3C1

set_option synthInstance.maxHeartbeats 1600000 in
theorem solution (N : ℕ) [NeZero N]
    {ℓ : ℕ} [Fact ℓ.Prime] (hℓN : ¬ ℓ ∣ N) (A : ValuationSubring (AlgebraicClosure ℚ))
    (hA : A.LiesOverPrime ℓ) :
    ∃ r : AlgebraicCurve.Place (AlgebraicClosure ℚ) (ModularCurve.modularFunctionFieldBar N) →
        AlgebraicCurve.Place (IsLocalRing.ResidueField A)
          (ModularCurve.modularFunctionFieldFullC (IsLocalRing.ResidueField A) N),
      ∀ (y : LaurentSeries A)
        (hy : ModularCurve.coeffMap A.subtype y ∈ ModularCurve.modularFunctionFieldBar N)
        (hyk : ModularCurve.coeffMap (IsLocalRing.residue A) y ∈
          ModularCurve.modularFunctionFieldFullC (IsLocalRing.ResidueField A) N),
        ModularCurve.coeffMap (IsLocalRing.residue A) y ≠ 0 →
          ∀ D : AlgebraicCurve.Divisor (AlgebraicClosure ℚ) (ModularCurve.modularFunctionFieldBar N),
            (∀ P, D P = P.ord (⟨ModularCurve.coeffMap A.subtype y, hy⟩ :
                ModularCurve.modularFunctionFieldBar N)) →
              ∀ Q, Finsupp.mapDomain r D Q =
                Q.ord (⟨ModularCurve.coeffMap (IsLocalRing.residue A) y, hyk⟩ :
                  ModularCurve.modularFunctionFieldFullC (IsLocalRing.ResidueField A) N) :=
  W7G3C1.c1 N A hℓN hA

end

end S_ModularCurve_exists_placeReductionModL_mapDomain_eq_ord_of_not_dvd
end P2MW
export P2MW.S_ModularCurve_exists_placeReductionModL_mapDomain_eq_ord_of_not_dvd (solution)
