-- Prove2me | solution 1 for ModularCurve.JZero.jensen_good_primes
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/04897023-fa36-5d60-ab4e-96a53fdeecdb

import Definitions.Def_ModularCurve_JZeroHeightForm
import Definitions.Def_AlgebraicCurve_ChordalProximity
import Theorems.Thm_ModularCurve_JZero_jensen_good_at
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_JZero_jensen_good_primes
p2m_attr_erase "instance" "instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions"
p2m_attr_erase "instance" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.Gamma0Pair.isElliptic WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent ModularCurve.B3.instIsElliptic_goodModel ModularCurve.instIsScalarTowerJAdjoin WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular"
p2m_attr_erase "simp" "AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap ModularCurve.FinitePlaceLift.traceHom_coe ModularCurve.FinitePlaceLift.mk.injEq ModularCurve.FinitePlaceLift.mk.sizeOf_spec WeierstrassCurve.reducePoint_zero FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRep_apply WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.jqNModC_one AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk"
p2m_attr_erase "simp" "ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix"
p2m_attr_erase "simp" "ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq ModularCurve.qExpandAlgHomC_apply AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularCurve.cuspCount_one ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar ModularCurve.coe_cuspidalDivisor₀"
p2m_attr_erase "simp" "ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar HahnSeries.ramScale_apply ModularCurve.gamma0PairMap_gen ModularCurve.moduliPointMapRingHom_mk ModularCurve.Gamma0Pair.mk.injEq ModularCurve.ModuliPoint.j_mk ModularCurve.Gamma0Pair.mk.sizeOf_spec ModularCurve.gamma0PairMap_toCurve WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero WeierstrassCurve.ratPointHom_apply WeierstrassCurve.ratPointMap_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃"
p2m_attr_erase "simp" "WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm ModularCurve.ProjectiveLine.map_mk ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe"
p2m_attr_erase "simp" "ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero"
p2m_attr_erase "simp" "TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff"

set_option Elab.async false
set_option autoImplicit false

open Polynomial

namespace ErowsM8

open NumberField IsDedekindDomain

noncomputable def pullback {K K' : Type*} [Field K] [Field K'] (w : AbsoluteValue K' ℝ)
    (ι : K →+* K') : AbsoluteValue K ℝ where
  toFun x := w (ι x)
  map_mul' x y := by rw [map_mul]; exact w.map_mul _ _
  nonneg' _ := w.nonneg _
  eq_zero' x := w.eq_zero.trans (map_eq_zero_iff ι ι.injective)
  add_le' x y := by rw [map_add]; exact w.add_le _ _

theorem pullback_apply {K K' : Type*} [Field K] [Field K'] (w : AbsoluteValue K' ℝ)
    (ι : K →+* K') (x : K) : pullback w ι x = w (ι x) := rfl

theorem exists_finitePlace_rpow_eq {K K' : Type*} [Field K] [NumberField K] [Field K']
    [NumberField K'] (ι : K →+* K') (ν : FinitePlace K) :
    ∃ (ν' : FinitePlace K') (c : ℝ), 0 < c ∧ ∀ a : K, ν' (ι a) = ν a ^ c := by
  classical
  letI : Algebra K K' := ι.toAlgebra
  haveI : Algebra.IsIntegral (𝓞 K) (𝓞 K') :=
    IsIntegralClosure.isIntegral_algebra (R := 𝓞 K) (A := 𝓞 K') (B := K')

  have hcompat : ∀ x : 𝓞 K,
      algebraMap (𝓞 K') K' (algebraMap (𝓞 K) (𝓞 K') x) = ι (algebraMap (𝓞 K) K x) :=
    fun x => rfl
  have hinj : Function.Injective (algebraMap (𝓞 K) (𝓞 K')) := by
    intro x y hxy
    apply RingOfIntegers.coe_injective
    apply ι.injective
    have := congrArg (algebraMap (𝓞 K') K') hxy
    rwa [hcompat, hcompat] at this

  set v : HeightOneSpectrum (𝓞 K) := ν.maximalIdeal with hv
  haveI : v.asIdeal.IsMaximal := v.isPrime.isMaximal v.ne_bot
  have hker : RingHom.ker (algebraMap (𝓞 K) (𝓞 K')) ≤ v.asIdeal := by
    rw [(RingHom.injective_iff_ker_eq_bot _).mp hinj]
    exact bot_le
  obtain ⟨Q, hQmax, hQ⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral v.asIdeal hker
  have hQne : Q ≠ ⊥ := by
    intro hQ0
    apply v.ne_bot
    rw [← hQ, hQ0, Ideal.comap_bot_of_injective _ hinj]
  let w : HeightOneSpectrum (𝓞 K') := ⟨Q, hQmax.isPrime, hQne⟩
  have hmem : ∀ x : 𝓞 K, x ∈ v.asIdeal ↔ algebraMap (𝓞 K) (𝓞 K') x ∈ w.asIdeal :=
    fun x => by rw [← hQ, Ideal.mem_comap]

  have hν : ∀ y : K, ν y = ‖FinitePlace.embedding v y‖ :=
    fun y => (FinitePlace.norm_embedding_eq ν y).symm

  let g : AbsoluteValue K ℝ := pullback (FinitePlace.mk w).val ι
  have hg : ∀ x : K, g x = ‖FinitePlace.embedding w (ι x)‖ := fun x => rfl

  have key : ∀ x : K, ν.val x < 1 → g x < 1 := by
    intro x hx
    change ν x < 1 at hx
    obtain ⟨n, d, h | h⟩ := HeightOneSpectrum.exists_primeCompl_mul_eq_or_mul_eq v x
    ·
      have hd1 : ν (algebraMap (𝓞 K) K d) = 1 := by
        rw [hν]; exact (FinitePlace.norm_eq_one_iff_notMem K v (d : 𝓞 K)).mpr d.2
      have hn1 : ν (algebraMap (𝓞 K) K n) < 1 := by
        rw [← h, map_mul, hd1, mul_one]; exact hx
      have hnv : n ∈ v.asIdeal := by
        rw [hν] at hn1; exact (FinitePlace.norm_lt_one_iff_mem K v n).mp hn1
      have hnw : algebraMap (𝓞 K) (𝓞 K') n ∈ w.asIdeal := (hmem n).mp hnv
      have hdw : algebraMap (𝓞 K) (𝓞 K') (d : 𝓞 K) ∉ w.asIdeal := fun hd => d.2 ((hmem d).mpr hd)
      have gn : g (algebraMap (𝓞 K) K n) < 1 := by
        rw [hg, ← hcompat]
        exact (FinitePlace.norm_lt_one_iff_mem K' w (algebraMap (𝓞 K) (𝓞 K') n)).mpr hnw
      have gd : g (algebraMap (𝓞 K) K d) = 1 := by
        rw [hg, ← hcompat]
        exact (FinitePlace.norm_eq_one_iff_notMem K' w (algebraMap (𝓞 K) (𝓞 K') (d : 𝓞 K))).mpr
          hdw
      have hprod : g x * g (algebraMap (𝓞 K) K d) = g (algebraMap (𝓞 K) K n) := by
        rw [← g.map_mul, h]
      rw [gd, mul_one] at hprod
      rw [hprod]; exact gn
    ·
      exfalso
      have hd1 : ν (algebraMap (𝓞 K) K d) = 1 := by
        rw [hν]; exact (FinitePlace.norm_eq_one_iff_notMem K v (d : 𝓞 K)).mpr d.2
      have hn1 : ν (algebraMap (𝓞 K) K n) ≤ 1 := by
        rw [hν]; exact FinitePlace.norm_le_one K v n
      have hlt : ν x * ν (algebraMap (𝓞 K) K n) < 1 :=
        mul_lt_one_of_nonneg_of_lt_one_left (apply_nonneg ν x) hx hn1
      rw [← map_mul, h, hd1] at hlt
      exact lt_irrefl _ hlt

  have hnt : ν.val.IsNontrivial := by
    obtain ⟨π, hπ, hπ0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot v.ne_bot
    refine ⟨algebraMap (𝓞 K) K π, RingOfIntegers.coe_ne_zero_iff.mpr hπ0, ne_of_lt ?_⟩
    change ν (algebraMap (𝓞 K) K π) < 1
    rw [hν]; exact (FinitePlace.norm_lt_one_iff_mem K v π).mpr hπ
  obtain ⟨c, hc, hcg⟩ :=
    AbsoluteValue.isEquiv_iff_exists_rpow_eq.mp (AbsoluteValue.isEquiv_of_lt_one_imp hnt key)
  refine ⟨FinitePlace.mk w, c, hc, fun a => ?_⟩
  have h := congr_fun hcg a
  beta_reduce at h

  rw [FinitePlace.mk_apply, ← hg, ← h]
  rfl

theorem exists_finitePlace_log_eq_mul {K K' : Type*} [Field K] [NumberField K] [Field K']
    [NumberField K'] (ι : K →+* K') (ν : FinitePlace K) :
    ∃ (ν' : FinitePlace K') (c : ℝ), 0 < c ∧ (∀ a : K, ν' (ι a) = ν a ^ c) ∧
      (∀ a : K, Real.log (ν' (ι a)) = c * Real.log (ν a)) ∧
      (∀ p : ℕ, ν (p : K) = 1 → ν' (p : K') = 1) := by
  obtain ⟨ν', c, hc, h⟩ := exists_finitePlace_rpow_eq ι ν
  refine ⟨ν', c, hc, h, fun a => ?_, fun p hp => ?_⟩
  · rw [h]
    rcases eq_or_lt_of_le (apply_nonneg ν a) with h0 | hpos
    · rw [← h0, Real.zero_rpow hc.ne', Real.log_zero, mul_zero]
    · exact Real.log_rpow hpos c
  · rw [← map_natCast ι p, h, hp, Real.one_rpow]

example {K : Type*} [Field K] [NumberField K] (ν : FinitePlace K) :
    ∃ (ν' : FinitePlace K) (c : ℝ), 0 < c ∧ ∀ a : K, ν' (RingHom.id K a) = ν a ^ c :=
  exists_finitePlace_rpow_eq (RingHom.id K) ν

example (L L' : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField ↥L] [NumberField ↥L']
    (ι : ↥L →+* ↥L') (ν : FinitePlace ↥L) :
    ∃ (ν' : FinitePlace ↥L') (c : ℝ), 0 < c ∧ ∀ a : ↥L, ν' (ι a) = ν a ^ c :=
  exists_finitePlace_rpow_eq ι ν

private theorem log_rpow_of_nonneg {x c : ℝ} (hx : 0 ≤ x) (hc : 0 < c) :
    Real.log (x ^ c) = c * Real.log x := by
  rcases eq_or_lt_of_le hx with h0 | hpos
  · rw [← h0, Real.zero_rpow hc.ne', Real.log_zero, mul_zero]
  · exact Real.log_rpow hpos c

private theorem iSup_rpow_eq {K K' : Type*} [Field K] [NumberField K] [Field K'] [NumberField K']
    (ι : K →+* K') (ν : FinitePlace K) (ν' : FinitePlace K') (c : ℝ) (hc : 0 < c)
    (h : ∀ a : K, ν' (ι a) = ν a ^ c) {I : Type*} [Finite I] (x : I → K) :
    (⨆ i, ν' (ι (x i))) = (⨆ i, ν (x i)) ^ c := by
  cases isEmpty_or_nonempty I with
  | inl hI =>
      rw [Real.iSup_of_isEmpty, Real.iSup_of_isEmpty, Real.zero_rpow hc.ne']
  | inr hI =>
      obtain ⟨i₀, hi₀⟩ := Finite.exists_max fun i => ν (x i)
      have hsup : (⨆ i, ν (x i)) = ν (x i₀) :=
        le_antisymm (ciSup_le fun i => hi₀ i)
          (le_ciSup (Set.finite_range fun i => ν (x i)).bddAbove i₀)
      have hsup' : (⨆ i, ν' (ι (x i))) = ν' (ι (x i₀)) := by
        refine le_antisymm (ciSup_le fun i => ?_)
          (le_ciSup (Set.finite_range fun i => ν' (ι (x i))).bddAbove i₀)
        rw [h, h]
        exact Real.rpow_le_rpow (apply_nonneg ν _) (hi₀ i) hc.le
      rw [hsup, hsup', h]

theorem log_iSup_transfer {K K' : Type*} [Field K] [NumberField K] [Field K'] [NumberField K']
    (ι : K →+* K') (ν : FinitePlace K) (ν' : FinitePlace K') (c : ℝ) (hc : 0 < c)
    (h : ∀ a : K, ν' (ι a) = ν a ^ c) {I : Type*} [Finite I] (x : I → K) :
    Real.log (⨆ i, ν' (ι (x i))) = c * Real.log (⨆ i, ν (x i)) := by
  rw [iSup_rpow_eq ι ν ν' c hc h x]
  exact log_rpow_of_nonneg (Real.iSup_nonneg fun i => apply_nonneg ν _) hc

theorem prox_transfer {K K' : Type*} [Field K] [NumberField K] [Field K'] [NumberField K']
    (ι : K →+* K') (ν : FinitePlace K) (ν' : FinitePlace K') (c : ℝ) (hc : 0 < c)
    (h : ∀ a : K, ν' (ι a) = ν a ^ c) {I : Type*} [Finite I] (x y : I → K) :
    AlgebraicCurve.prox (⇑ν') (fun i => ι (x i)) (fun i => ι (y i))
      = c * AlgebraicCurve.prox (⇑ν) x y := by
  unfold AlgebraicCurve.prox
  have hm : (fun p : I × I => ν' (ι (x p.1) * ι (y p.2) - ι (x p.2) * ι (y p.1)))
      = fun p : I × I => ν' (ι (x p.1 * y p.2 - x p.2 * y p.1)) := by
    funext p
    rw [← RingHom.map_mul, ← RingHom.map_mul, ← RingHom.map_sub]
  rw [show (⨆ p : I × I, ν' (ι (x p.1) * ι (y p.2) - ι (x p.2) * ι (y p.1)))
      = ⨆ p : I × I, ν' (ι (x p.1 * y p.2 - x p.2 * y p.1)) from congrArg iSup hm,
    log_iSup_transfer ι ν ν' c hc h x, log_iSup_transfer ι ν ν' c hc h y,
    log_iSup_transfer ι ν ν' c hc h fun p : I × I => x p.1 * y p.2 - x p.2 * y p.1]
  ring

theorem exists_finitePlace_transfer {K K' : Type*} [Field K] [NumberField K] [Field K']
    [NumberField K'] (ι : K →+* K') (ν : FinitePlace K) :
    ∃ (ν' : FinitePlace K') (c : ℝ), 0 < c ∧
      (∀ a : K, Real.log (ν' (ι a)) = c * Real.log (ν a)) ∧
      (∀ p : ℕ, ν ((p : ℕ) : K) = 1 → ν' ((p : ℕ) : K') = 1) ∧
      (∀ (r' : ℕ) (xx : Fin r' → K),
        Real.log (⨆ i, ν' (ι (xx i))) = c * Real.log (⨆ i, ν (xx i))) ∧
      (∀ (r' : ℕ) (xx yy : Fin r' → K),
        AlgebraicCurve.prox ⇑ν' (fun i => ι (xx i)) (fun i => ι (yy i))
          = c * AlgebraicCurve.prox ⇑ν xx yy) := by
  obtain ⟨ν', c, hc, h, hlog, hp⟩ := exists_finitePlace_log_eq_mul ι ν
  exact ⟨ν', c, hc, hlog, hp, fun r' xx => log_iSup_transfer ι ν ν' c hc h xx,
    fun r' xx yy => prox_transfer ι ν ν' c hc h xx yy⟩

end ErowsM8

namespace ErowsDock

def incl {L L' : IntermediateField ℚ (AlgebraicClosure ℚ)} (hle : L ≤ L') : ↥L →+* ↥L' where
  toFun a := ⟨(a : AlgebraicClosure ℚ), hle a.2⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

@[scoped simp] lemma incl_coe {L L' : IntermediateField ℚ (AlgebraicClosure ℚ)} (hle : L ≤ L')
    (a : ↥L) : ((incl hle a : ↥L') : AlgebraicClosure ℚ) = (a : AlgebraicClosure ℚ) := rfl

variable {K : Type*} [Field K] [NumberField K] (ν : NumberField.FinitePlace K)

private lemma nu_neg (a : K) : ν (-a) = ν a :=
  ν.val.map_neg a

private lemma nu_natCast_le_one (n : ℕ) : ν ((n : ℕ) : K) ≤ 1 := by
  induction n with
  | zero => rw [Nat.cast_zero, map_zero]; exact zero_le_one
  | succ n ih =>
    rw [Nat.cast_succ]
    exact (ν.add_le _ _).trans (max_le ih (le_of_eq (map_one ν)))

private lemma nu_intCast_le_one (m : ℤ) : ν ((m : ℤ) : K) ≤ 1 := by
  obtain ⟨n, rfl | rfl⟩ := m.eq_nat_or_neg
  · rw [Int.cast_natCast]; exact nu_natCast_le_one ν n
  · rw [Int.cast_neg, Int.cast_natCast, nu_neg]; exact nu_natCast_le_one ν n

private lemma nu_natCast_eq_one {n : ℕ}
    (hp : ∀ p : ℕ, p.Prime → p ∣ n → ν (p : K) = 1) (hn : n ≠ 0) : ν ((n : ℕ) : K) = 1 := by
  conv_lhs => rw [← Nat.prod_primeFactorsList hn]
  rw [Nat.cast_list_prod, map_list_prod]
  apply List.prod_eq_one
  intro y hy
  rw [List.mem_map] at hy
  obtain ⟨z, hz, rfl⟩ := hy
  rw [List.mem_map] at hz
  obtain ⟨p, hpmem, rfl⟩ := hz
  exact hp p (Nat.prime_of_mem_primeFactorsList hpmem) (Nat.dvd_of_mem_primeFactorsList hpmem)

private lemma nu_intCast_eq_one {m : ℤ} (hm : m ≠ 0)
    (hp : ∀ p : ℕ, p.Prime → p ∣ m.natAbs → ν (p : K) = 1) : ν ((m : ℤ) : K) = 1 := by
  have habs : ν ((m.natAbs : ℕ) : K) = 1 :=
    nu_natCast_eq_one ν hp (Int.natAbs_ne_zero.mpr hm)
  obtain ⟨n, rfl | rfl⟩ := m.eq_nat_or_neg
  · rw [Int.natAbs_natCast] at habs
    rw [Int.cast_natCast]
    exact habs
  · rw [Int.natAbs_neg, Int.natAbs_natCast] at habs
    rw [Int.cast_neg, Int.cast_natCast, nu_neg]
    exact habs

private lemma nu_ratCast_le_one {q : ℚ}
    (hden : ∀ p : ℕ, p.Prime → p ∣ q.den → ν (p : K) = 1) : ν ((q : ℚ) : K) ≤ 1 := by
  rw [Rat.cast_def, map_div₀]
  have h2 : ν ((q.den : ℕ) : K) = 1 := nu_natCast_eq_one ν hden q.den_pos.ne'
  rw [h2, div_one]
  exact nu_intCast_le_one ν q.num

private lemma nu_ratCast_eq_one {q : ℚ}
    (hden : ∀ p : ℕ, p.Prime → p ∣ q.den → ν (p : K) = 1)
    (hnum : ∀ p : ℕ, p.Prime → p ∣ q.num.natAbs → ν (p : K) = 1)
    (hq : q ≠ 0) : ν ((q : ℚ) : K) = 1 := by
  rw [Rat.cast_def, map_div₀]
  have h1 : ν ((q.num : ℤ) : K) = 1 := nu_intCast_eq_one ν (Rat.num_ne_zero.mpr hq) hnum
  have h2 : ν ((q.den : ℕ) : K) = 1 := nu_natCast_eq_one ν hden q.den_pos.ne'
  rw [h1, h2]
  norm_num

private theorem nu_eq_one_of_good {x : K} (hx0 : x ≠ 0)
    (hgood : ∀ p : ℕ, p.Prime →
      ((∃ i, p ∣ ((minpoly ℚ x).coeff i).den) ∨ p ∣ ((minpoly ℚ x).coeff 0).num.natAbs) →
      ν (p : K) = 1) :
    ν x = 1 := by
  have hint : IsIntegral ℚ x := IsIntegral.of_finite ℚ x
  have hmonic : (minpoly ℚ x).Monic := minpoly.monic hint
  have hdegpos : 0 < (minpoly ℚ x).natDegree := minpoly.natDegree_pos hint
  have haev : Polynomial.aeval x (minpoly ℚ x) = 0 := minpoly.aeval ℚ x
  have hsum : ∑ i ∈ Finset.range ((minpoly ℚ x).natDegree + 1),
      (minpoly ℚ x).coeff i • x ^ i = 0 := by
    rw [← Polynomial.aeval_eq_sum_range, haev]
  have hna : IsNonarchimedean ⇑ν := fun a b => ν.add_le a b
  have hxpos : 0 < ν x := NumberField.FinitePlace.pos_iff.mpr hx0
  have hcle : ∀ i, ν (((minpoly ℚ x).coeff i : ℚ) : K) ≤ 1 := fun i =>
    nu_ratCast_le_one ν fun p hp hpd => hgood p hp (Or.inl ⟨i, hpd⟩)
  have hc0 : ν (((minpoly ℚ x).coeff 0 : ℚ) : K) = 1 :=
    nu_ratCast_eq_one ν (fun p hp hpd => hgood p hp (Or.inl ⟨0, hpd⟩))
      (fun p hp hpd => hgood p hp (Or.inr hpd))
      (minpoly.coeff_zero_ne_zero hint hx0)
  have hterm : ∀ i, ν ((minpoly ℚ x).coeff i • x ^ i)
      = ν (((minpoly ℚ x).coeff i : ℚ) : K) * ν x ^ i := by
    intro i
    rw [Algebra.smul_def, map_mul, map_pow]
    congr 2
  have hA : ¬ 1 < ν x := by
    intro hgt
    have hmax : ∀ j ∈ Finset.range ((minpoly ℚ x).natDegree + 1),
        j ≠ (minpoly ℚ x).natDegree →
        ν ((minpoly ℚ x).coeff j • x ^ j)
          < ν ((minpoly ℚ x).coeff (minpoly ℚ x).natDegree • x ^ (minpoly ℚ x).natDegree) := by
      intro j hj hjne
      rw [hterm j, hterm (minpoly ℚ x).natDegree, hmonic.coeff_natDegree, Rat.cast_one,
        map_one, one_mul]
      have hjlt : j < (minpoly ℚ x).natDegree :=
        lt_of_le_of_ne (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)) hjne
      calc ν (((minpoly ℚ x).coeff j : ℚ) : K) * ν x ^ j ≤ 1 * ν x ^ j :=
            mul_le_mul_of_nonneg_right (hcle j) (pow_nonneg hxpos.le j)
        _ = ν x ^ j := one_mul _
        _ < ν x ^ (minpoly ℚ x).natDegree := pow_lt_pow_right₀ hgt hjlt
    have hkey := hna.apply_sum_eq_of_lt (fun a => (ν.1.map_neg a).symm)
      (Finset.self_mem_range_succ (minpoly ℚ x).natDegree) hmax
    rw [hsum, map_zero] at hkey
    rw [hterm, hmonic.coeff_natDegree, Rat.cast_one, map_one, one_mul] at hkey
    have hpow : 0 < ν x ^ (minpoly ℚ x).natDegree := pow_pos hxpos _
    rw [← hkey] at hpow
    exact lt_irrefl 0 hpow
  have hB : ¬ ν x < 1 := by
    intro hlt
    have hmax : ∀ j ∈ Finset.range ((minpoly ℚ x).natDegree + 1), j ≠ 0 →
        ν ((minpoly ℚ x).coeff j • x ^ j) < ν ((minpoly ℚ x).coeff 0 • x ^ 0) := by
      intro j hj hjne
      rw [hterm j, hterm 0, pow_zero, mul_one, hc0]
      calc ν (((minpoly ℚ x).coeff j : ℚ) : K) * ν x ^ j ≤ 1 * ν x ^ j :=
            mul_le_mul_of_nonneg_right (hcle j) (pow_nonneg hxpos.le j)
        _ = ν x ^ j := one_mul _
        _ ≤ ν x := pow_le_of_le_one hxpos.le hlt.le hjne
        _ < 1 := hlt
    have hkey := hna.apply_sum_eq_of_lt (fun a => (ν.1.map_neg a).symm)
      (Finset.mem_range.mpr (Nat.succ_pos (minpoly ℚ x).natDegree)) hmax
    rw [hsum, map_zero] at hkey
    rw [hterm, pow_zero, mul_one, hc0] at hkey
    exact one_ne_zero hkey.symm
  rcases lt_trichotomy (ν x) 1 with h | h | h
  · exact absurd h hB
  · exact h
  · exact absurd h hA

private noncomputable def badPrimes (γ : AlgebraicClosure ℚ) : Finset ℕ :=
  ((Finset.range ((minpoly ℚ γ).natDegree + 1)).biUnion
    fun i => ((minpoly ℚ γ).coeff i).den.primeFactors)
    ∪ ((minpoly ℚ γ).coeff 0).num.natAbs.primeFactors

theorem h3_primes (T : Finset (AlgebraicClosure ℚ)) (hT : (0 : AlgebraicClosure ℚ) ∉ T) :
    ∃ S : Finset ℕ, (∀ p ∈ S, p.Prime) ∧
      ∀ (L : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField ↥L]
      (ν : NumberField.FinitePlace ↥L), (∀ p ∈ S, ν (p : ↥L) = 1) →
      ∀ γ ∈ T, ∀ x : ↥L, (x : AlgebraicClosure ℚ) = γ → ν x = 1 := by
  classical
  refine ⟨T.biUnion badPrimes, ?_, ?_⟩
  · intro p hp
    rw [Finset.mem_biUnion] at hp
    obtain ⟨γ, _, hpB⟩ := hp
    rw [badPrimes, Finset.mem_union] at hpB
    rcases hpB with h | h
    · rw [Finset.mem_biUnion] at h
      obtain ⟨i, _, hpf⟩ := h
      exact (Nat.mem_primeFactors.mp hpf).1
    · exact (Nat.mem_primeFactors.mp h).1
  intro L _ ν hν γ hγ x hxγ
  have hγ0 : γ ≠ 0 := fun h => hT (h ▸ hγ)
  have hγint : IsIntegral ℚ γ := ((AlgebraicClosure.isAlgebraic ℚ).isAlgebraic γ).isIntegral
  have hx0 : x ≠ 0 := by
    intro h
    apply hγ0
    rw [← hxγ, h]
    simp
  letI : IsScalarTower ℚ ↥L (AlgebraicClosure ℚ) :=
    IsScalarTower.of_algebraMap_eq' (by apply RingHom.ext_rat)
  have hmpeq : minpoly ℚ γ = minpoly ℚ x := by
    rw [← hxγ, ← IntermediateField.algebraMap_apply]
    exact minpoly.algebraMap_eq (A := ℚ) (B' := AlgebraicClosure ℚ)
      (algebraMap ↥L (AlgebraicClosure ℚ)).injective x
  refine nu_eq_one_of_good ν hx0 ?_
  intro p hp hcase
  rw [← hmpeq] at hcase
  refine hν p (Finset.mem_biUnion.mpr ⟨γ, hγ, ?_⟩)
  rcases hcase with ⟨i, hi⟩ | h0
  · by_cases hile : i < (minpoly ℚ γ).natDegree + 1
    · exact Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨i, Finset.mem_range.mpr hile,
        Nat.mem_primeFactors.mpr ⟨hp, hi, ((minpoly ℚ γ).coeff i).den_pos.ne'⟩⟩)
    · exfalso
      have hz : (minpoly ℚ γ).coeff i = 0 :=
        Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
      rw [hz] at hi
      have hone : (0 : ℚ).den = 1 := rfl
      rw [hone] at hi
      exact hp.one_lt.ne' (Nat.dvd_one.mp hi)
  · refine Finset.mem_union_right _ (Nat.mem_primeFactors.mpr ⟨hp, h0, ?_⟩)
    exact Int.natAbs_ne_zero.mpr (Rat.num_ne_zero.mpr (minpoly.coeff_zero_ne_zero hγint hγ0))

theorem exists_finitePlace_ext (L L' : IntermediateField ℚ (AlgebraicClosure ℚ))
    [NumberField ↥L] [NumberField ↥L'] (hle : L ≤ L') (ν : NumberField.FinitePlace ↥L) :
    ∃ (ν' : NumberField.FinitePlace ↥L') (c : ℝ), 0 < c ∧
      (∀ a : ↥L, Real.log (ν' (incl hle a)) = c * Real.log (ν a)) ∧
      (∀ p : ℕ, ν ((p : ℕ) : ↥L) = 1 → ν' ((p : ℕ) : ↥L') = 1) ∧
      (∀ (r' : ℕ) (xx : Fin r' → ↥L),
        Real.log (⨆ i, ν' (incl hle (xx i))) = c * Real.log (⨆ i, ν (xx i))) ∧
      (∀ (r' : ℕ) (xx yy : Fin r' → ↥L),
        AlgebraicCurve.prox ⇑ν' (fun i => incl hle (xx i)) (fun i => incl hle (yy i))
          = c * AlgebraicCurve.prox ⇑ν xx yy) :=
  ErowsM8.exists_finitePlace_transfer (incl hle) ν

noncomputable section

namespace E2DockLprime

variable (L : IntermediateField ℚ (AlgebraicClosure ℚ)) (T : Finset (AlgebraicClosure ℚ))

abbrev Lprime : IntermediateField ℚ (AlgebraicClosure ℚ) :=
  L ⊔ IntermediateField.adjoin ℚ (↑T : Set (AlgebraicClosure ℚ))

scoped instance : FiniteDimensional ℚ
    ↥(IntermediateField.adjoin ℚ (↑T : Set (AlgebraicClosure ℚ))) := by
  have : Finite (↑T : Set (AlgebraicClosure ℚ)) := T.finite_toSet.to_subtype
  exact IntermediateField.finiteDimensional_adjoin fun y _ =>
    ((AlgebraicClosure.isAlgebraic ℚ).isAlgebraic y).isIntegral

scoped instance [NumberField ↥L] : FiniteDimensional ℚ ↥(Lprime L T) := by
  haveI : FiniteDimensional ℚ ↥L := NumberField.to_finiteDimensional
  exact IntermediateField.finiteDimensional_sup L _

theorem L_le_Lprime : L ≤ Lprime L T := le_sup_left

theorem adjoinT_le_Lprime :
    IntermediateField.adjoin ℚ (↑T : Set (AlgebraicClosure ℚ)) ≤ Lprime L T := le_sup_right

theorem mem_Lprime_of_mem_T {z : AlgebraicClosure ℚ} (hz : z ∈ T) : z ∈ Lprime L T := by
  apply adjoinT_le_Lprime
  exact IntermediateField.subset_adjoin ℚ (↑T : Set (AlgebraicClosure ℚ)) hz

end E2DockLprime
p2m_reactivate "P2MW.S_ModularCurve_JZero_jensen_good_primes.ErowsDock.E2DockLprime"

end
p2m_reactivate "P2MW.S_ModularCurve_JZero_jensen_good_primes.ErowsDock.E2DockLprime"

open E2DockLprime in
theorem exists_numberField_ext (L : IntermediateField ℚ (AlgebraicClosure ℚ))
    [NumberField ↥L] (T : Finset (AlgebraicClosure ℚ)) :
    ∃ L' : IntermediateField ℚ (AlgebraicClosure ℚ), L ≤ L' ∧ (∀ γ ∈ T, γ ∈ L') ∧
      Nonempty (NumberField ↥L') :=
  ⟨Lprime L T, L_le_Lprime L T, fun _ hγ => mem_Lprime_of_mem_T L T hγ, ⟨inferInstance⟩⟩

private lemma log_iSup_eq_zero_of_01 {ι : Type*} [Finite ι] (f : ι → ℝ)
    (hf : ∀ i, f i = 0 ∨ f i = 1) : Real.log (⨆ i, f i) = 0 := by
  cases isEmpty_or_nonempty ι with
  | inl h =>
    rw [show (⨆ i, f i) = sSup (Set.range f) from rfl, Set.range_eq_empty, Real.sSup_empty,
      Real.log_zero]
  | inr h =>
    haveI := h
    by_cases h1 : ∃ i, f i = 1
    · obtain ⟨i₁, hi₁⟩ := h1
      have hsup : (⨆ i, f i) = 1 :=
        le_antisymm (ciSup_le fun i => by rcases hf i with h' | h' <;> simp [h'])
          (hi₁ ▸ le_ciSup (Set.finite_range f).bddAbove i₁)
      rw [hsup, Real.log_one]
    · have hall : ∀ i, f i = 0 := fun i => (hf i).resolve_right fun h' => h1 ⟨i, h'⟩
      obtain ⟨i₀⟩ := h
      have hsup : (⨆ i, f i) = 0 :=
        le_antisymm (ciSup_le fun i => (hall i).le)
          ((hall i₀) ▸ le_ciSup (Set.finite_range f).bddAbove i₀)
      rw [hsup, Real.log_zero]

private lemma finsupp_erase_eq_self {α M : Type*} [Zero M] (f : α →₀ M) (a : α) (h : f a = 0) :
    f.erase a = f := by
  ext b
  rcases eq_or_ne b a with rfl | hne
  · rw [Finsupp.erase_same, h]
  · rw [Finsupp.erase_ne hne]

private lemma regVal_zero_eq_secVal {F : Type} [Field F]
    [Algebra (AlgebraicClosure ℚ) F] {r' : ℕ} (s' : Fin r' → F)
    (v : AlgebraicCurve.Place (AlgebraicClosure ℚ) F) (t' : F) (k : ℕ) (u : F) :
    AlgebraicCurve.regVal s' v t' k 0 u = AlgebraicCurve.secVal s' v k u := by
  unfold AlgebraicCurve.regVal AlgebraicCurve.secVal
  split_ifs with hr
  · congr 1
    rw [pow_zero, mul_one]
  · rfl

end ErowsDock
p2m_reactivate "P2MW.S_ModularCurve_JZero_jensen_good_primes.ErowsDock.E2DockLprime P2MW.S_ModularCurve_JZero_jensen_good_primes.ErowsDock"

open AlgebraicCurve ModularCurve ErowsDock

theorem solution (N : ℕ) [NeZero N] {r : ℕ}
    (s : Fin r → modularFunctionFieldBar N) (hs : IsEmbBasis N s)
    (t : modularFunctionFieldBar N) (ht : (cuspInftyBar N).ord t = 1) :
    ∃ S : Finset ℕ, (∀ p ∈ S, p.Prime) ∧ ∀ (k : ℕ) (u : modularFunctionFieldBar N), u ≠ 0 →
      u ∈ riemannRochSpace ((k : ℤ) • embDivisor N) →
      ∀ B : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N),
      (∀ w, B w = w.ord u + ((k : ℤ) • embDivisor N) w) →
      ∀ (L : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField ↥L]
        (ν : NumberField.FinitePlace ↥L), (∀ p ∈ S, ν (p : ↥L) = 1) →
      ∀ x : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N) → Fin r → ↥L,
      (∀ w ∈ B.support, ∀ i, ((x w i : ↥L) : AlgebraicClosure ℚ) = evalVec s w i) →
      (∀ i, ((x (cuspInftyBar N) i : ↥L) : AlgebraicClosure ℚ) = evalVec s (cuspInftyBar N) i) →
      ∀ c : ↥L, (c : AlgebraicClosure ℚ) = regVal s (cuspInftyBar N) t k (B (cuspInftyBar N)).toNat u →
      ∃ m : ℝ,
        ((B.erase (cuspInftyBar N)).sum fun w n => (n : ℝ) * prox ν (x (cuspInftyBar N)) (x w))
          = (k : ℝ) * Real.log (⨆ i, ν (x (cuspInftyBar N) i)) - Real.log (ν c) - m ∧
        ∀ v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N), B v = 0 →
          (∀ i, ((x v i : ↥L) : AlgebraicClosure ℚ) = evalVec s v i) →
          ∀ a : ↥L, (a : AlgebraicClosure ℚ) = secVal s v k u →
          (B.sum fun w n => (n : ℝ) * prox ν (x v) (x w))
            = (k : ℝ) * Real.log (⨆ i, ν (x v i)) - Real.log (ν a) - m := by
  classical
  obtain ⟨S₁, hS₁p, hmain⟩ := ModularCurve.JZero.jensen_good_at N s hs

  have hT0 : (0 : AlgebraicClosure ℚ) ∉
      ((Finset.univ.image fun p : Fin r × Fin r =>
          regVal s (cuspInftyBar N) t 1 1 (evalVec s (cuspInftyBar N) p.1 • s p.2
            - evalVec s (cuspInftyBar N) p.2 • s p.1))
        ∪ (Finset.univ.image fun i => evalVec s (cuspInftyBar N) i)).filter (· ≠ 0) :=
    fun h => (Finset.mem_filter.mp h).2 rfl
  obtain ⟨S₂, hS₂p, hH3⟩ := h3_primes _ hT0
  refine ⟨S₁ ∪ S₂,
    fun p hp => (Finset.mem_union.mp hp).elim (hS₁p p) (hS₂p p), ?_⟩
  intro k u hu humem B hB L _ ν hν x hx hinf c hc

  obtain ⟨L', hle, hTL', ⟨hNF'⟩⟩ := exists_numberField_ext L
    ((((Finset.univ.image fun p : Fin r × Fin r =>
        regVal s (cuspInftyBar N) t 1 1 (evalVec s (cuspInftyBar N) p.1 • s p.2
          - evalVec s (cuspInftyBar N) p.2 • s p.1))
      ∪ (Finset.univ.image fun i => evalVec s (cuspInftyBar N) i)).filter (· ≠ 0)))
  haveI := hNF'

  obtain ⟨ν', c', hc', hlog, hnat, hsuplog, hproxc⟩ := exists_finitePlace_ext L L' hle ν

  have hν' : ∀ p ∈ S₁, ν' ((p : ℕ) : ↥L') = 1 :=
    fun p hp => hnat p (hν p (Finset.mem_union_left _ hp))

  obtain ⟨m', hm'⟩ := hmain k u hu humem B hB L' ν'
    hν' (fun w i => incl hle (x w i)) (fun w hw i => hx w hw i)
  refine ⟨m' / c', ?_, ?_⟩
  ·

    have hbase := hm' (cuspInftyBar N) t (fun _ => ht) (fun i => hinf i) (incl hle c)
      (by rw [incl_coe]; exact hc)
      (fun p => if h : regVal s (cuspInftyBar N) t 1 1 (evalVec s (cuspInftyBar N) p.1 • s p.2
          - evalVec s (cuspInftyBar N) p.2 • s p.1) = 0 then 0
        else ⟨regVal s (cuspInftyBar N) t 1 1 (evalVec s (cuspInftyBar N) p.1 • s p.2
          - evalVec s (cuspInftyBar N) p.2 • s p.1),
          hTL' _ (Finset.mem_filter.mpr ⟨Finset.mem_union_left _
            (Finset.mem_image_of_mem _ (Finset.mem_univ p)), h⟩)⟩)
      (by
        intro _ p
        beta_reduce
        split_ifs with h
        · rw [h]; rfl
        · rfl)

    have hsum : ((B.erase (cuspInftyBar N)).sum fun w n =>
          (n : ℝ) * prox ⇑ν' ((fun w i => incl hle (x w i)) (cuspInftyBar N))
            ((fun w i => incl hle (x w i)) w))
        = c' * ((B.erase (cuspInftyBar N)).sum fun w n =>
          (n : ℝ) * prox ⇑ν (x (cuspInftyBar N)) (x w)) := by
      rw [Finsupp.mul_sum]
      exact Finsupp.sum_congr fun w _ => by
        rw [hproxc r (x (cuspInftyBar N)) (x w)]; ring
    have hsupx : Real.log (⨆ i, ν' (incl hle (x (cuspInftyBar N) i)))
        = c' * Real.log (⨆ i, ν (x (cuspInftyBar N) i)) := hsuplog r (x (cuspInftyBar N))
    have hcc : Real.log (ν' (incl hle c)) = c' * Real.log (ν c) := hlog c

    have hA0 : Real.log (⨆ i, ν (x (cuspInftyBar N) i)) = 0 := by
      refine log_iSup_eq_zero_of_01 _ fun i => ?_
      rcases eq_or_ne (evalVec s (cuspInftyBar N) i) 0 with h0 | hne
      · left
        have hxz : x (cuspInftyBar N) i = 0 := by
          have : ((x (cuspInftyBar N) i : ↥L) : AlgebraicClosure ℚ) = ((0 : ↥L) : AlgebraicClosure ℚ) := by
            rw [hinf i, h0]; rfl
          exact Subtype.coe_injective this
        rw [hxz, map_zero]
      · right
        exact hH3 L ν (fun p hp => hν p (Finset.mem_union_right _ hp)) _
          (Finset.mem_filter.mpr ⟨Finset.mem_union_right _
            (Finset.mem_image_of_mem _ (Finset.mem_univ i)), hne⟩) _ (hinf i)

    have hν'S₂ : ∀ p ∈ S₂, ν' ((p : ℕ) : ↥L') = 1 :=
      fun p hp => hnat p (hν p (Finset.mem_union_right _ hp))
    have hY0 : Real.log (⨆ p : Fin r × Fin r, ν'
        ((fun p => if h : regVal s (cuspInftyBar N) t 1 1 (evalVec s (cuspInftyBar N) p.1 • s p.2
            - evalVec s (cuspInftyBar N) p.2 • s p.1) = 0 then 0
          else ⟨regVal s (cuspInftyBar N) t 1 1 (evalVec s (cuspInftyBar N) p.1 • s p.2
            - evalVec s (cuspInftyBar N) p.2 • s p.1),
            hTL' _ (Finset.mem_filter.mpr ⟨Finset.mem_union_left _
              (Finset.mem_image_of_mem _ (Finset.mem_univ p)), h⟩)⟩) p)) = 0 := by
      refine log_iSup_eq_zero_of_01 _ fun p => ?_
      dsimp only
      split_ifs with h
      · left; exact map_zero ν'
      · right
        refine hH3 L' ν' hν'S₂ _
          (Finset.mem_filter.mpr ⟨Finset.mem_union_left _
            (Finset.mem_image_of_mem _ (Finset.mem_univ p)), h⟩) _ ?_
        rfl
    rw [hsum, hsupx, hcc, hY0, hA0] at hbase
    rw [hA0]
    refine mul_left_cancel₀ hc'.ne' ?_
    rw [hbase]
    field_simp
    ring
  ·
    intro v hBv hxv a ha
    have hpt := hm' v t
      (fun h0 => by rw [hBv] at h0; exact absurd h0 (lt_irrefl 0))
      (fun i => hxv i) (incl hle a)
      (by
        have h1 : (B v).toNat = 0 := by rw [hBv]; rfl
        rw [incl_coe, h1, regVal_zero_eq_secVal]
        exact ha)
      0 (fun h0 => by rw [hBv] at h0; exact absurd h0 (lt_irrefl 0))
    rw [finsupp_erase_eq_self B v hBv] at hpt
    have hsum : (B.sum fun w n =>
          (n : ℝ) * prox ⇑ν' ((fun w i => incl hle (x w i)) v)
            ((fun w i => incl hle (x w i)) w))
        = c' * (B.sum fun w n => (n : ℝ) * prox ⇑ν (x v) (x w)) := by
      rw [Finsupp.mul_sum]
      exact Finsupp.sum_congr fun w _ => by
        rw [hproxc r (x v) (x w)]; ring
    have hsupx : Real.log (⨆ i, ν' (incl hle (x v i)))
        = c' * Real.log (⨆ i, ν (x v i)) := hsuplog r (x v)
    have ha' : Real.log (ν' (incl hle a)) = c' * Real.log (ν a) := hlog a
    rw [hsum, hsupx, ha', hBv] at hpt
    refine mul_left_cancel₀ hc'.ne' ?_
    rw [hpt]
    push_cast
    field_simp
    ring

end S_ModularCurve_JZero_jensen_good_primes
end P2MW
export P2MW.S_ModularCurve_JZero_jensen_good_primes (solution)
