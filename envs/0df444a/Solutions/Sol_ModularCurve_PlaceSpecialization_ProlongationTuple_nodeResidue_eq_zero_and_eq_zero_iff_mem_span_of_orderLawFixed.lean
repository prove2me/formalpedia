-- Prove2me | solution 1 for ModularCurve.PlaceSpecialization.ProlongationTuple.nodeResidue_eq_zero_and_eq_zero_iff_mem_span_of_orderLawFixed
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/2168830b-ca13-5a24-9de9-f2d8075d774e

import Definitions.Def_ModularCurve_NodeLocalizedPlaces
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_nodeIntegersOver_fibreProduct_of_orderLawFixed_of_range_redRestrict
import Theorems.Thm_ModularCurve_NodeLocalized_exists_coeffSubring_inertQuadratic_cubeRoot
import Theorems.Thm_ValuationSubring_eq_bot_of_isPrime_of_ne_maximalIdeal_of_liesOverPrime
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_nodeResidue_eq_zero_and_eq_zero_iff_mem_span_of_orderLawFixed
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.instIsElliptic_tateLaurent ModularCurve.instIsElliptic_tateBase ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular ModularCurve.NodeLocalized.isLocalization_nodeDenominators ModularCurve.NodeLocalized.algebraEvalRange ModularCurve.NodeLocalized.isLocalRing_modularLocalizedAtPoint instTopologicallyFGOfFiniteType AdicCompletion.instIsLocalRingMaximalIdeal AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.B3.instIsElliptic_goodModel ModularCurve.NodeLocalized.isScalarTower_K_fieldOver_bar ModularCurve.NodeLocalized.algebraFieldOverBar ModularCurve.NodeLocalized.algebra_isIntegral_fieldOver_bar ModularCurve.NodeLocalized.isScalarTower_fieldOver_bar_laurent ModularCurve.NodeLocalized.charZero_fieldOver ModularCurve.NodeLocalized.algebraFieldOver ModularCurve.NodeLocalized.charZero_laurentSeries_algClosure ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar"
p2m_attr_erase "instance" "AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.instIsScalarTowerJAdjoin GaloisRepAdic.instAddCommGroup GaloisRepAdic.instFree GaloisRepAdic.instFinite GaloisRepAdic.instModule ResidualGaloisRep.instModule ResidualGaloisRep.instModuleFinite ResidualGaloisRep.instAddCommGroup WeierstrassCurve.Affine.Point.instFinite AlgebraicCurve.CurveModel.isProper AlgebraicCurve.CurveModel.isIntegral AlgebraicCurve.CurveModel.smooth ModularCurve.IgusaScheme.isOpenImmersion_fInf ModularCurve.IgusaScheme.isOpenImmersion_ιInf ModularCurve.IgusaScheme.fact_jFull_ne_zero ModularCurve.IgusaScheme.isOpenImmersion_ιFin ModularCurve.IgusaScheme.isOpenImmersion_fFin"
p2m_attr_erase "instance" "AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin AlgebraicCurve.CurveModel.chartRing_finitePresentation ValuationSubring.instIsAlgClosedResidueField"
p2m_attr_erase "simp" "compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero"
p2m_attr_erase "simp" "ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd"
p2m_attr_erase "simp" "ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂"
p2m_attr_erase "simp" "WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply ModularCurve.ProjectiveLine.map_mk WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff ModularCurve.coe_nodeEquiv_symm_apply ModularCurve.frobNodePair_jOfNode ModularCurve.jOfNode_mk ModularCurve.widthOf_mk ModularCurve.frobNodePairEmb_apply ModularCurve.card_nodePairsOf ModularCurve.frobNodePair_snd ModularCurve.coe_nodeEquiv_apply ModularCurve.frobNodePair_fst ModularCurve.NodeLocalized.coe_modularEvalAt AdicCompletion.evalₐ_mapₐ AdicCompletion.mapAlgEquivOfBijective_apply AdicCompletion.levelMapₐ_mk AdicCompletion.mapₐ_of AdicCompletion.mapAlgEquiv_symm_apply AdicCompletion.mapAlgEquiv_apply AdicCompletion.evalₐ_ofLevelwiseEquiv AdicCompletion.evalₐ_levelwiseHom AdicCompletion.localizationEquiv_of AdicCompletion.evalₐ_ofLevelwiseEquiv_symm Localization.AtPrime.quotientPowEquiv_mk ModularCurve.LambdaModularPolynomialData.mk.sizeOf_spec ModularCurve.LambdaModularPolynomialData.mk.injEq AdicCompletion.transportOf_of AdicCompletion.selfCompletion_smul_of"
p2m_attr_erase "simp" "AdicCompletion.tensorRingEquiv_tmul AdicCompletion.completionOfAlgHom_apply AdicCompletion.completionBaseChangeHom_of AdicCompletion.tensorRingHom_tmul AdicCompletion.stabilizerToCompletionAut_of ModularCurve.Gamma0Pair.map_toCurve WeierstrassCurve.mapPoint_eq_ratPointMap ModularCurve.Gamma0Pair.map_gen ModularCurve.Gamma0Pair.map_eq_gamma0PairMap ModularCurve.ModuliPoint.map_eq_moduliPointMapRingHom ModularCurve.ModuliPoint.map_mk WeierstrassCurve.mapPointHom_apply WeierstrassCurve.mapPoint_zero AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero ModularCurve.cuspCount_one WeierstrassCurve.Universal.halveX_zero"
p2m_attr_erase "simp" "WeierstrassCurve.Universal.specialize_X_one WeierstrassCurve.Universal.coeff_halve WeierstrassCurve.Universal.specialize_X_two WeierstrassCurve.Universal.halveCoeff_zero WeierstrassCurve.Universal.specialize_X_four WeierstrassCurve.Universal.coeff_halveX WeierstrassCurve.Universal.specialize_X_three WeierstrassCurve.Universal.specialize_X_zero HahnSeries.ramScale_apply AlgebraicCurve.Pic.baseChange_mk AlgebraicCurve.Place.forgetConstants_toValuationSubring AlgebraicCurve.Place.constantFieldEquiv_symm_apply AlgebraicCurve.Place.ord_forgetConstants AlgebraicCurve.Place.extendConstants_toValuationSubring AlgebraicCurve.Place.constantFieldEquiv_apply_toValuationSubring AlgebraicCurve.Place.mem_fiberConstants AlgebraicCurve.Place.restrictConstants_toValuationSubring AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq"
p2m_attr_erase "simp" "AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL GoodReductionJacobian.RelativePic0Designation.mk.sizeOf_spec GoodReductionJacobian.AvatarSchemeBridge.mk.injEq MilneJVScheme.JacobianSchemeData.mk.injEq GoodReductionJacobian.AvatarSchemeBridge.mk.sizeOf_spec MilneJVScheme.JacobianSchemeData.mk.sizeOf_spec GoodReductionJacobian.RelativePic0Designation.mk.injEq NeronModelInfra.specGenericFibreInclusion_eq NeronModelInfra.genericFibreRestrict_coe_comp_snd NeronModelInfra.genericFibreRestrict_coe_comp_fst GoodReductionJacobian.schemeHomOverComp_coe NeronModelInfra.schemeHomOverEquivOverHom_apply GoodReductionJacobian.RelativeGroupLaw.mk.sizeOf_spec NeronModelInfra.schemeHomOverEquivOverHom_symm_apply NeronModelInfra.overHomToSchemeHomOver_coe GoodReductionJacobian.RelativeGroupLaw.mk.injEq NeronModelInfra.overHomToSchemeHomOver_schemeHomOverToOverHom NeronModelInfra.schemeHomOverToOverHom_left NeronModelInfra.schemeHomOverToOverHom_overHomToSchemeHomOver NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe"
p2m_attr_erase "simp" "GaloisRepAdic.mk.injEq GaloisRepAdic.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.injEq ResidualGaloisRep.mk.sizeOf_spec ResidualGaloisRep.mk.injEq ResidualGaloisRep.Equiv.mk.sizeOf_spec ResidualGaloisRep.Equiv.mk.injEq AlgebraicCurve.CurveModel.mk.injEq AlgebraicCurve.CurveModel.mk.sizeOf_spec ModularCurve.CharPModel.FibreModel.mk.injEq ModularCurve.CharPModel.FibreModel.mk.sizeOf_spec ModularCurve.IgusaScheme.ιInf_igusaTo_assoc ModularCurve.IgusaScheme.coe_jFull ModularCurve.IgusaScheme.coe_jInvChartInf ModularCurve.IgusaScheme.coe_jChartFin ModularCurve.IgusaScheme.ιFin_igusaTo ModularCurve.IgusaScheme.ιInf_igusaTo ModularCurve.IgusaScheme.ιFin_igusaTo_assoc AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces ModularCurve.crossingCoord_apply ValuationSubring.reduceAt_coe ValuationSubring.reduceAt_one ValuationSubring.reduceAt_natCast ValuationSubring.reduceAt_intCast ValuationSubring.reduceAt_zero"
set_option autoImplicit false

p2m_open "AlgebraicCurve IsLocalRing ModularCurve P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_nodeResidue_eq_zero_and_eq_zero_iff_mem_span_of_orderLawFixed.ModularCurve"
open ModularCurve.PlaceSpecialization ModularCurve.PlaceSpecialization.ProlongationTuple

namespace KWallAux

variable {q : ℕ} [Fact q.Prime] {k : Type*} [Field k] [CharP k q]

omit [CharP k q] in

private theorem castHom_pow_card_sq (ι : ZMod q →+* k) (u : ZMod q) : ι u ^ (q ^ 2) = ι u := by
  rw [← map_pow, sq, pow_mul, ZMod.pow_card, ZMod.pow_card]

private theorem castHom_eq_map_natCast {R : Type*} [CommRing R] (φ : R →+* k) (u : ZMod q) :
    ZMod.castHom (dvd_refl q) k u = φ ((u.val : ℕ) : R) := by
  haveI : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
  rw [map_natCast, ZMod.castHom_apply, ZMod.natCast_val]

omit [CharP k q] in

private theorem mem_rootSet_iff [DecidableEq k] (a : k) :
    a ∈ (Polynomial.X ^ (q ^ 2) - Polynomial.X : Polynomial k).roots.toFinset ↔ a ^ (q ^ 2) = a := by
  have hne : (Polynomial.X ^ (q ^ 2) - Polynomial.X : Polynomial k) ≠ 0 :=
    FiniteField.X_pow_card_pow_sub_X_ne_zero k two_ne_zero (Fact.out : q.Prime).one_lt
  rw [Multiset.mem_toFinset, Polynomial.mem_roots hne, Polynomial.IsRoot.def, Polynomial.eval_sub,
    Polynomial.eval_pow, Polynomial.eval_X, sub_eq_zero]

omit [CharP k q] in

private theorem card_rootSet_le [DecidableEq k] :
    (Polynomial.X ^ (q ^ 2) - Polynomial.X : Polynomial k).roots.toFinset.card ≤ q ^ 2 := by
  refine (Multiset.toFinset_card_le _).trans ((Polynomial.card_roots' _).trans ?_)
  rw [FiniteField.X_pow_card_pow_sub_X_natDegree_eq k two_ne_zero (Fact.out : q.Prime).one_lt]

private theorem forall_mem_range_of_pow_eq_of_notMem_range {R : Type*} [CommRing R] (φ : R →+* k) (ζ : R)
    (hζ : φ ζ ^ (q ^ 2) = φ ζ) (hout : φ ζ ∉ Set.range (ZMod.castHom (dvd_refl q) k)) :
    ∀ a : k, a ^ (q ^ 2) = a → a ∈ Set.range φ := by
  classical
  haveI : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
  intro a ha
  let ι : ZMod q →+* k := ZMod.castHom (dvd_refl q) k
  have hinj : Function.Injective ι := ι.injective
  let f : ZMod q × ZMod q → k := fun p => ι p.1 + ι p.2 * φ ζ
  have hf : Function.Injective f := by
    rintro ⟨u, v⟩ ⟨u', v'⟩ h
    change ι u + ι v * φ ζ = ι u' + ι v' * φ ζ at h
    by_cases hv : v = v'
    · subst hv
      have hu : ι u = ι u' := add_right_cancel h
      rw [hinj hu]
    · exfalso
      apply hout
      have hv' : ι (v - v') ≠ 0 := by
        intro h0
        apply hv
        apply sub_eq_zero.mp
        apply hinj
        rw [h0, map_zero]
      refine ⟨(u' - u) / (v - v'), ?_⟩
      change ι ((u' - u) / (v - v')) = φ ζ
      rw [map_div₀, div_eq_iff hv', map_sub, map_sub]
      linear_combination (-1 : k) * h
  have himage : (Finset.univ : Finset (ZMod q × ZMod q)).image f
      ⊆ (Polynomial.X ^ (q ^ 2) - Polynomial.X : Polynomial k).roots.toFinset := by
    intro x hx
    obtain ⟨⟨u, v⟩, -, rfl⟩ := Finset.mem_image.mp hx
    rw [mem_rootSet_iff (q := q) (k := k)]
    change (ZMod.castHom (dvd_refl q) k u + ZMod.castHom (dvd_refl q) k v * φ ζ) ^ (q ^ 2)
      = ZMod.castHom (dvd_refl q) k u + ZMod.castHom (dvd_refl q) k v * φ ζ
    rw [add_pow_char_pow, mul_pow, castHom_pow_card_sq, castHom_pow_card_sq, hζ]
  have hcard : ((Finset.univ : Finset (ZMod q × ZMod q)).image f).card = q ^ 2 := by
    rw [Finset.card_image_of_injective _ hf, Finset.card_univ, Fintype.card_prod, ZMod.card, sq]
  have heq := Finset.eq_of_subset_of_card_le himage ((card_rootSet_le (q := q) (k := k)).trans hcard.symm.le)
  have ha' : a ∈ (Finset.univ : Finset (ZMod q × ZMod q)).image f := by
    rw [heq, mem_rootSet_iff (q := q) (k := k)]
    exact ha
  obtain ⟨⟨u, v⟩, -, rfl⟩ := Finset.mem_image.mp ha'
  refine ⟨((u.val : ℕ) : R) + ((v.val : ℕ) : R) * ζ, ?_⟩
  change φ _ = ZMod.castHom (dvd_refl q) k u + ZMod.castHom (dvd_refl q) k v * φ ζ
  rw [map_add, map_mul, castHom_eq_map_natCast φ u, castHom_eq_map_natCast φ v]

private theorem pow_card_sq_eq_of_sq_eq_natCast (r : k) (m : ℕ) (h : r ^ 2 = (m : k)) : r ^ (q ^ 2) = r := by
  have hF : ∀ x : k, frobenius k q x = x ^ q := fun _ => rfl
  have h2 : frobenius k q r ^ 2 = r ^ 2 := by
    rw [← map_pow, h, map_natCast]
  have h3 : (frobenius k q r - r) * (frobenius k q r + r) = 0 := by linear_combination h2
  have h4 : r ^ (q ^ 2) = frobenius k q (frobenius k q r) := by
    rw [hF, hF, ← pow_mul, sq]
  rw [h4]
  rcases mul_eq_zero.mp h3 with h5 | h5
  · have h6 : frobenius k q r = r := sub_eq_zero.mp h5
    rw [h6, h6]
  · have h6 : frobenius k q r = -r := eq_neg_of_add_eq_zero_left h5
    rw [h6, map_neg, h6, neg_neg]

private theorem notMem_range_of_sq_eq_natCast (m : ℕ) (hm : ∀ u : ZMod q, u ^ 2 ≠ (m : ZMod q)) (r : k)
    (h : r ^ 2 = (m : k)) : r ∉ Set.range (ZMod.castHom (dvd_refl q) k) := by
  rintro ⟨u, rfl⟩
  apply hm u
  apply (ZMod.castHom (dvd_refl q) k).injective
  rw [map_pow, h, map_natCast]

omit [CharP k q] in

private theorem pow_card_sq_eq_of_quad (hq : q = 2) (r : k) (h : r ^ 2 + r + 1 = 0) : r ^ (q ^ 2) = r := by
  subst hq
  have h3 : r ^ 3 = 1 := by linear_combination (r - 1) * h
  calc r ^ (2 ^ 2) = r ^ 3 * r := by ring
    _ = r := by rw [h3, one_mul]

private theorem zmod_two_quad_ne_zero : ∀ u : ZMod 2, u ^ 2 + u + 1 ≠ 0 := by decide

private theorem notMem_range_of_quad (hq : q = 2) (r : k) (h : r ^ 2 + r + 1 = 0) :
    r ∉ Set.range (ZMod.castHom (dvd_refl q) k) := by
  subst hq
  rintro ⟨u, rfl⟩
  have hu : u ^ 2 + u + 1 = 0 := by
    apply (ZMod.castHom (dvd_refl 2) k).injective
    rw [map_add, map_add, map_pow, map_one, map_zero]
    exact h
  exact zmod_two_quad_ne_zero u hu

private theorem exists_natCast_nonsquare (hq2 : q ≠ 2) : ∃ m : ℕ, ∀ u : ZMod q, u ^ 2 ≠ (m : ZMod q) := by
  haveI : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
  obtain ⟨a, ha⟩ := FiniteField.exists_nonsquare (F := ZMod q) (by rw [ZMod.ringChar_zmod_n]; exact hq2)
  refine ⟨a.val, fun u hu => ha ⟨u, ?_⟩⟩
  rw [ZMod.natCast_zmod_val] at hu
  rw [← hu, sq]

private theorem map_quad_eq_zero {R : Type*} [CommRing R] (φ : R →+* k) (c : R) (h : φ (c ^ 2 + c + 1) = 0) :
    φ c ^ 2 + φ c + 1 = 0 := by
  rw [← h, map_add, map_add, map_pow, map_one]

private theorem map_quad_eq_zero' {R : Type*} [CommRing R] (φ : R →+* k) (c : R) (h : c ^ 2 + c + 1 = 0) :
    φ c ^ 2 + φ c + 1 = 0 := by
  rw [← map_pow, ← map_add, ← map_one φ, ← map_add, h, map_zero]

private theorem map_sq_eq_natCast {R : Type*} [CommRing R] (φ : R →+* k) (c : R) (m : ℕ)
    (h : φ (c ^ 2 - (m : R)) = 0) : φ c ^ 2 = (m : k) := by
  have h' : φ (c ^ 2) - φ (m : R) = 0 := by rw [← map_sub]; exact h
  rw [map_pow, map_natCast] at h'
  exact sub_eq_zero.mp h'

private theorem map_sq_eq_natCast' {R : Type*} [CommRing R] (φ : R →+* k) (c : R) (m : ℕ) (h : c ^ 2 = (m : R)) :
    φ c ^ 2 = (m : k) := by
  rw [← map_pow, h, map_natCast]

private theorem le_of_coeffSubring_le (A : ValuationSubring (AlgebraicClosure ℚ))
    {K K' : IntermediateField ℚ (AlgebraicClosure ℚ)}
    (h : ModularCurve.NodeLocalized.coeffSubring A K ≤ ModularCurve.NodeLocalized.coeffSubring A K') : K ≤ K' := by
  intro x hx
  rcases A.mem_or_inv_mem x with hxA | hxA
  · exact (Subring.mem_inf.mp (h (show x ∈ ModularCurve.NodeLocalized.coeffSubring A K from
      Subring.mem_inf.mpr ⟨hxA, hx⟩))).2
  · have hx' : x⁻¹ ∈ K := K.inv_mem hx
    have hmem : x⁻¹ ∈ K' := (Subring.mem_inf.mp (h (show x⁻¹ ∈ ModularCurve.NodeLocalized.coeffSubring A K from
      Subring.mem_inf.mpr ⟨hxA, hx'⟩))).2
    have hmem' := K'.inv_mem hmem
    rwa [inv_inv] at hmem'

end KWallAux

section Beta1
p2m_open "ModularCurve.NodeLocalized P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_nodeResidue_eq_zero_and_eq_zero_iff_mem_span_of_orderLawFixed.ModularCurve.NodeLocalized"
open Polynomial
open scoped IntermediateField

namespace SqrtAux

private theorem sq_red_eq_zero_of_not_isUnit (q : ℕ) [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] (red : A →+* k) (a : A) (ha : ¬ IsUnit a) : red a = 0 := by
  haveI : CharZero (AlgebraicClosure ℚ) :=
    charZero_of_injective_algebraMap (algebraMap ℚ (AlgebraicClosure ℚ)).injective
  have hq : q.Prime := Fact.out
  have hq0 : ((q : ℕ) : AlgebraicClosure ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hq.ne_zero
  have hcq : (((q : ℕ) : A) : AlgebraicClosure ℚ) = ((q : ℕ) : AlgebraicClosure ℚ) := map_natCast A.subtype q
  have hredq : red ((q : ℕ) : A) = 0 := by
    rw [map_natCast]
    exact CharP.cast_eq_zero k q
  have hA : A.LiesOverPrime q := by
    show ((q : ℕ) : AlgebraicClosure ℚ) ∈ A.nonunits
    rw [ValuationSubring.mem_nonunits_iff_or]
    right
    intro hinv
    have h1 : ((q : ℕ) : A) * ⟨((q : ℕ) : AlgebraicClosure ℚ)⁻¹, hinv⟩ = 1 := by
      apply Subtype.ext
      show (((q : ℕ) : A) : AlgebraicClosure ℚ) * ((q : ℕ) : AlgebraicClosure ℚ)⁻¹ = 1
      rw [hcq]
      exact mul_inv_cancel₀ hq0
    have h2 := congrArg red h1
    rw [map_mul, hredq, zero_mul, map_one] at h2
    exact zero_ne_one h2
  haveI : (RingHom.ker red).IsPrime := RingHom.ker_isPrime red
  have hne : RingHom.ker red ≠ ⊥ := by
    intro hbot
    have hmem : ((q : ℕ) : A) ∈ RingHom.ker red := RingHom.mem_ker.mpr hredq
    rw [hbot, Ideal.mem_bot] at hmem
    have h3 := congrArg A.subtype hmem
    rw [map_natCast, map_zero] at h3
    exact hq0 h3
  have hk : RingHom.ker red = IsLocalRing.maximalIdeal A := by
    by_contra h
    exact hne (ValuationSubring.eq_bot_of_isPrime_of_ne_maximalIdeal_of_liesOverPrime hq A hA (RingHom.ker red) h)
  have hmax : a ∈ IsLocalRing.maximalIdeal A := (IsLocalRing.mem_maximalIdeal a).mpr (mem_nonunits_iff.mpr ha)
  rw [← hk] at hmax
  exact RingHom.mem_ker.mp hmax

private theorem sq_red_inv_eq_zero (q : ℕ) [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] (red : A →+* k) (z : AlgebraicClosure ℚ) (hz : z ∉ A) (h : z⁻¹ ∈ A) :
    red ⟨z⁻¹, h⟩ = 0 := by
  apply sq_red_eq_zero_of_not_isUnit q red
  intro hu
  obtain ⟨b, hb⟩ := hu.exists_right_inv
  have h1 : z⁻¹ * (b : AlgebraicClosure ℚ) = 1 := congrArg Subtype.val hb
  have h2 : (b : AlgebraicClosure ℚ) = z := by
    rw [eq_inv_of_mul_eq_one_right h1, inv_inv]
  exact hz (h2 ▸ b.2)

private theorem sq_exists_mul_eq_one (q : ℕ) [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] (red : A →+* k) (K : IntermediateField ℚ (AlgebraicClosure ℚ))
    (v : ↥(coeffSubring A K)) (hv : redRestrict red K v ≠ 0) : ∃ w, v * w = 1 := by
  have hvA : ((v : AlgebraicClosure ℚ)) ∈ A := (Subring.mem_inf.mp v.2).1
  have hvK : ((v : AlgebraicClosure ℚ)) ∈ K := (Subring.mem_inf.mp v.2).2
  have hu : IsUnit (⟨v, hvA⟩ : A) := by
    by_contra hnu
    exact hv (sq_red_eq_zero_of_not_isUnit q red _ hnu)
  obtain ⟨b, hb⟩ := hu.exists_right_inv
  have h1 : (v : AlgebraicClosure ℚ) * (b : AlgebraicClosure ℚ) = 1 := congrArg Subtype.val hb
  have hbK : (b : AlgebraicClosure ℚ) ∈ K := by
    rw [eq_inv_of_mul_eq_one_right h1]
    exact K.inv_mem hvK
  refine ⟨⟨b, Subring.mem_inf.mpr ⟨b.2, hbK⟩⟩, Subtype.ext ?_⟩
  exact h1

private theorem sq_engine {R : Type*} [CommRing R] {k : Type*} [Field k] (f : R →+* k) (nn : k)
    (hirr : ∀ c : R, f c ^ 2 ≠ nn) (hlift : ∀ v : R, f v ≠ 0 → ∃ w, v * w = 1) (r : k) (hr : r ^ 2 = nn)
    (u v : R) (h : f u + r * f v = 0) : f v = 0 ∧ f u = 0 := by
  by_cases hv : f v = 0
  · refine ⟨hv, ?_⟩
    rwa [hv, mul_zero, add_zero] at h
  · exfalso
    obtain ⟨w, hw⟩ := hlift v hv
    have hw' : f v * f w = 1 := by
      rw [← map_mul, hw, map_one]
    apply hirr (-(u * w))
    have hu : f u = -(r * f v) := eq_neg_of_add_eq_zero_left h
    rw [map_neg, map_mul, hu, neg_mul, neg_neg, mul_assoc, hw', mul_one, hr]

private theorem sq_exists_add_mul (K : IntermediateField ℚ (AlgebraicClosure ℚ)) (n : ℕ) (α : AlgebraicClosure ℚ)
    (hα : α ^ 2 = ((n : ℕ) : AlgebraicClosure ℚ)) (hαalg : IsAlgebraic ℚ α) [FiniteDimensional ℚ K]
    (c : AlgebraicClosure ℚ)
    (hc : c ∈ K ⊔ ℚ⟮α⟯) : ∃ x y : AlgebraicClosure ℚ, x ∈ K ∧ y ∈ K ∧ c = x + α * y := by
  let S : Subalgebra ℚ (AlgebraicClosure ℚ) :=
    { carrier := {z | ∃ x y : AlgebraicClosure ℚ, x ∈ K ∧ y ∈ K ∧ z = x + α * y}
      mul_mem' := by
        rintro _ _ ⟨x, y, hx, hy, rfl⟩ ⟨x', y', hx', hy', rfl⟩
        refine ⟨x * x' + ((n : ℕ) : AlgebraicClosure ℚ) * (y * y'), x * y' + x' * y, ?_, ?_, ?_⟩
        · exact add_mem (mul_mem hx hx') (mul_mem (natCast_mem K n) (mul_mem hy hy'))
        · exact add_mem (mul_mem hx hy') (mul_mem hx' hy)
        · linear_combination (y * y') * hα
      one_mem' := ⟨1, 0, one_mem K, zero_mem K, by ring⟩
      add_mem' := by
        rintro _ _ ⟨x, y, hx, hy, rfl⟩ ⟨x', y', hx', hy', rfl⟩
        exact ⟨x + x', y + y', add_mem hx hx', add_mem hy hy', by ring⟩
      zero_mem' := ⟨0, 0, zero_mem K, zero_mem K, by ring⟩
      algebraMap_mem' := fun r => ⟨algebraMap ℚ (AlgebraicClosure ℚ) r, 0, K.algebraMap_mem r, zero_mem K, by ring⟩ }
  have hS : (K ⊔ ℚ⟮α⟯).toSubalgebra ≤ S := by
    rw [IntermediateField.sup_toSubalgebra_of_left]
    refine sup_le ?_ ?_
    · intro z hz
      exact ⟨z, 0, hz, zero_mem K, by ring⟩
    · rw [IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hαalg]
      refine Algebra.adjoin_le ?_
      intro z hz
      rw [Set.mem_singleton_iff] at hz
      exact ⟨0, 1, zero_mem K, one_mem K, by rw [hz]; ring⟩
  exact hS hc

private theorem sq_mem_and_mem {A : ValuationSubring (AlgebraicClosure ℚ)} {k : Type*} [Field k] (red : A →+* k)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) (α : AlgebraicClosure ℚ) (hαA : α ∈ A)
    (hD : ∀ z : AlgebraicClosure ℚ, z ∉ A → ∀ h : z⁻¹ ∈ A, red ⟨z⁻¹, h⟩ = 0)
    (hQ : ∀ (u : AlgebraicClosure ℚ) (huA : u ∈ A), u ∈ K → red ⟨u, huA⟩ + red ⟨α, hαA⟩ ≠ 0)
    (x y : AlgebraicClosure ℚ) (hxK : x ∈ K) (hyK : y ∈ K) (hc : x + α * y ∈ A) : x ∈ A ∧ y ∈ A := by
  by_cases hy : y ∈ A
  · refine ⟨?_, hy⟩
    by_contra hx
    have hx0 : x ≠ 0 := fun h => hx (h ▸ zero_mem A)
    have hxi : x⁻¹ ∈ A := (A.mem_or_inv_mem x).resolve_left hx
    have h1 : red (⟨x + α * y, hc⟩ * ⟨x⁻¹, hxi⟩) = 0 := by
      rw [map_mul, hD x hx hxi, mul_zero]
    have h2 : (⟨x + α * y, hc⟩ * ⟨x⁻¹, hxi⟩ : A) = 1 + ⟨α, hαA⟩ * (⟨y, hy⟩ * ⟨x⁻¹, hxi⟩) := by
      apply Subtype.ext
      show (x + α * y) * x⁻¹ = 1 + α * (y * x⁻¹)
      field_simp
    rw [h2, map_add, map_one, map_mul, map_mul, hD x hx hxi, mul_zero, mul_zero, add_zero] at h1
    exact one_ne_zero h1
  · exfalso
    have hy0 : y ≠ 0 := fun h => hy (h ▸ zero_mem A)
    have hyi : y⁻¹ ∈ A := (A.mem_or_inv_mem y).resolve_left hy
    have h1 : red (⟨x + α * y, hc⟩ * ⟨y⁻¹, hyi⟩) = 0 := by
      rw [map_mul, hD y hy hyi, mul_zero]
    by_cases ht : x * y⁻¹ ∈ A
    · have h2 : (⟨x + α * y, hc⟩ * ⟨y⁻¹, hyi⟩ : A) = ⟨x * y⁻¹, ht⟩ + ⟨α, hαA⟩ := by
        apply Subtype.ext
        show (x + α * y) * y⁻¹ = x * y⁻¹ + α
        field_simp
      rw [h2, map_add] at h1
      exact hQ (x * y⁻¹) ht (K.mul_mem hxK (K.inv_mem hyK)) h1
    · have hx : x ∉ A := fun hxA => ht (mul_mem hxA hyi)
      have hx0 : x ≠ 0 := fun h => hx (h ▸ zero_mem A)
      have hxi : x⁻¹ ∈ A := (A.mem_or_inv_mem x).resolve_left hx
      have hti : (x * y⁻¹)⁻¹ ∈ A := (A.mem_or_inv_mem _).resolve_left ht
      have h3 : red (⟨x + α * y, hc⟩ * ⟨x⁻¹, hxi⟩) = 0 := by
        rw [map_mul, hD x hx hxi, mul_zero]
      have h4 : (⟨x + α * y, hc⟩ * ⟨x⁻¹, hxi⟩ : A) = 1 + ⟨α, hαA⟩ * ⟨(x * y⁻¹)⁻¹, hti⟩ := by
        apply Subtype.ext
        show (x + α * y) * x⁻¹ = 1 + α * (x * y⁻¹)⁻¹
        field_simp
      rw [h4, map_add, map_one, map_mul, hD (x * y⁻¹) ht hti, mul_zero, add_zero] at h3
      exact one_ne_zero h3

private theorem sq_redRestrict_inclusion {A : ValuationSubring (AlgebraicClosure ℚ)} {k : Type*} [Field k]
    (red : A →+* k) {K K' : IntermediateField ℚ (AlgebraicClosure ℚ)} (hle : coeffSubring A K ≤ coeffSubring A K')
    (c : ↥(coeffSubring A K)) :
    redRestrict red K' (Subring.inclusion hle c) = redRestrict red K c := rfl

end SqrtAux

namespace ModularCurve p2m_export "ModularCurve" "PlaceSpecialization.ProlongationTuple modularFunctionFieldBar ModularPolynomialData modularFunctionFieldC PlaceSpecialization HeckeAlphaBarIntegral HeckeBetaBarIntegral KroneckerCongruence ssPlaces NodeLocalized.coeffSubring NodeLocalized.redRestrict NodeLocalized.fieldOver NodeLocalized.exists_coeffSubring_inertQuadratic_cubeRoot" namespace NodeLocalized p2m_export "ModularCurve.NodeLocalized" "coeffSubring redRestrict fieldOver exists_coeffSubring_inertQuadratic_cubeRoot" end ModularCurve.NodeLocalized
p2m_open_scoped "ModularCurve ModularCurve.NodeLocalized" in

private theorem ModularCurve.NodeLocalized.exists_coeffSubring_inertQuadratic_sqrt
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] (red : A →+* k)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
    (ϖ : ↥(coeffSubring A K)) (hϖ : ∀ c : ↥(coeffSubring A K), redRestrict red K c = 0 ↔ ∃ d, c = ϖ * d)
    (n : ℕ) (hirr : ∀ c : ↥(coeffSubring A K), redRestrict red K (c ^ 2 - (n : ↥(coeffSubring A K))) ≠ 0) :
    ∃ (K' : IntermediateField ℚ (AlgebraicClosure ℚ)) (_ : FiniteDimensional ℚ K')
      (hle : coeffSubring A K ≤ coeffSubring A K') (α : ↥(coeffSubring A K')),
      α ^ 2 = (n : ↥(coeffSubring A K')) ∧
      (∀ c : ↥(coeffSubring A K'), ∃ c₀ c₁ : ↥(coeffSubring A K),
        c = Subring.inclusion hle c₀ + α * Subring.inclusion hle c₁) ∧
      (∀ c : ↥(coeffSubring A K'), redRestrict red K' c = 0 ↔ ∃ d, c = Subring.inclusion hle ϖ * d) := by
  have hirr' : ∀ c : ↥(coeffSubring A K), redRestrict red K c ^ 2 ≠ ((n : ℕ) : k) := by
    intro c h
    apply hirr c
    rw [map_sub, map_pow, map_natCast, h, sub_self]
  have hD : ∀ z : AlgebraicClosure ℚ, z ∉ A → ∀ h : z⁻¹ ∈ A, red ⟨z⁻¹, h⟩ = 0 :=
    fun z hz h => SqrtAux.sq_red_inv_eq_zero q red z hz h
  have hlift : ∀ v : ↥(coeffSubring A K), redRestrict red K v ≠ 0 → ∃ w, v * w = 1 :=
    fun v hv => SqrtAux.sq_exists_mul_eq_one q red K v hv
  obtain ⟨α, hα⟩ := IsAlgClosed.exists_pow_nat_eq ((n : ℕ) : AlgebraicClosure ℚ) two_pos
  have hαA : α ∈ A := by
    rcases A.mem_or_inv_mem α with h | h
    · exact h
    · by_cases hα0 : α = 0
      · rw [hα0]
        exact zero_mem A
      · have hαn : α = ((n : ℕ) : AlgebraicClosure ℚ) * α⁻¹ := by
          rw [← hα]
          field_simp
        rw [hαn]
        exact mul_mem (natCast_mem A n) h
  have hαalg : IsAlgebraic ℚ α :=
    ⟨X ^ 2 - C ((n : ℕ) : ℚ), (monic_X_pow_sub_C _ two_ne_zero).ne_zero, by simp [hα]⟩
  haveI : FiniteDimensional ℚ ℚ⟮α⟯ := IntermediateField.adjoin.finiteDimensional hαalg.isIntegral
  have hKK' : K ≤ K ⊔ ℚ⟮α⟯ := le_sup_left
  have hαK' : α ∈ K ⊔ ℚ⟮α⟯ := (le_sup_right : ℚ⟮α⟯ ≤ K ⊔ ℚ⟮α⟯) (IntermediateField.mem_adjoin_simple_self ℚ α)
  have hle : coeffSubring A K ≤ coeffSubring A (K ⊔ ℚ⟮α⟯) := fun z hz =>
    Subring.mem_inf.mpr ⟨(Subring.mem_inf.mp hz).1, hKK' (Subring.mem_inf.mp hz).2⟩
  let αK : ↥(coeffSubring A (K ⊔ ℚ⟮α⟯)) := ⟨α, Subring.mem_inf.mpr ⟨hαA, hαK'⟩⟩
  have hr : red ⟨α, hαA⟩ ^ 2 = ((n : ℕ) : k) := by
    have hsq : (⟨α, hαA⟩ : A) ^ 2 = ((n : ℕ) : A) := by
      apply Subtype.ext
      show α ^ 2 = (((n : ℕ) : A) : AlgebraicClosure ℚ)
      rw [hα]
      exact (map_natCast A.subtype n).symm
    rw [← map_pow, hsq, map_natCast]
  have hQ : ∀ (u : AlgebraicClosure ℚ) (huA : u ∈ A), u ∈ K → red ⟨u, huA⟩ + red ⟨α, hαA⟩ ≠ 0 := by
    intro u huA huK h
    have h1 := SqrtAux.sq_engine (redRestrict red K) ((n : ℕ) : k) hirr' hlift (red ⟨α, hαA⟩) hr
      ⟨u, Subring.mem_inf.mpr ⟨huA, huK⟩⟩ 1 (by rw [map_one, mul_one]; exact h)
    exact one_ne_zero ((map_one (redRestrict red K)).symm.trans h1.1)
  have hbasis : ∀ c : ↥(coeffSubring A (K ⊔ ℚ⟮α⟯)), ∃ c₀ c₁ : ↥(coeffSubring A K),
      c = Subring.inclusion hle c₀ + αK * Subring.inclusion hle c₁ := by
    intro c
    obtain ⟨x, y, hxK, hyK, hcxy⟩ :=
      SqrtAux.sq_exists_add_mul K n α hα hαalg (c : AlgebraicClosure ℚ) (Subring.mem_inf.mp c.2).2
    have hcA : x + α * y ∈ A := hcxy ▸ (Subring.mem_inf.mp c.2).1
    obtain ⟨hxA, hyA⟩ := SqrtAux.sq_mem_and_mem red K α hαA hD hQ x y hxK hyK hcA
    refine ⟨⟨x, Subring.mem_inf.mpr ⟨hxA, hxK⟩⟩, ⟨y, Subring.mem_inf.mpr ⟨hyA, hyK⟩⟩, Subtype.ext ?_⟩
    exact hcxy
  refine ⟨K ⊔ ℚ⟮α⟯, inferInstance, hle, αK, ?_, hbasis, ?_⟩
  · apply Subtype.ext
    show α ^ 2 = (((n : ℕ) : ↥(coeffSubring A (K ⊔ ℚ⟮α⟯))) : AlgebraicClosure ℚ)
    rw [hα]
    exact (map_natCast (coeffSubring A (K ⊔ ℚ⟮α⟯)).subtype n).symm
  · intro c
    constructor
    · intro h0
      obtain ⟨c₀, c₁, rfl⟩ := hbasis c
      rw [map_add, map_mul, SqrtAux.sq_redRestrict_inclusion, SqrtAux.sq_redRestrict_inclusion] at h0
      obtain ⟨h1, h2⟩ := SqrtAux.sq_engine (redRestrict red K) ((n : ℕ) : k) hirr' hlift (red ⟨α, hαA⟩) hr c₀ c₁ h0
      obtain ⟨d₀, hd₀⟩ := (hϖ c₀).mp h2
      obtain ⟨d₁, hd₁⟩ := (hϖ c₁).mp h1
      refine ⟨Subring.inclusion hle d₀ + αK * Subring.inclusion hle d₁, ?_⟩
      rw [hd₀, hd₁, map_mul, map_mul]
      ring
    · rintro ⟨d, rfl⟩
      rw [map_mul, SqrtAux.sq_redRestrict_inclusion, (hϖ ϖ).mpr ⟨1, (mul_one ϖ).symm⟩, zero_mul]

end Beta1

p2m_open_scoped "ModularCurve ModularCurve.NodeLocalized" in

private theorem
    ModularCurve.NodeLocalized.exists_le_range_redRestrict_and_exists_generator_of_redRestrict_eq_zero_iff
    (q : ℕ) [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {k : Type*} [Field k] [CharP k q]
    (red : A →+* k)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
    (ϖ : ↥(NodeLocalized.coeffSubring A K))
    (hϖ : ∀ d : ↥(NodeLocalized.coeffSubring A K), NodeLocalized.redRestrict red K d = 0 ↔ ∃ d', d = ϖ * d') :
    ∃ (K' : IntermediateField ℚ (AlgebraicClosure ℚ)) (_ : FiniteDimensional ℚ ↥K'), K ≤ K' ∧
      (∀ a : k, a ^ (q ^ 2) = a → a ∈ Set.range (NodeLocalized.redRestrict red K')) ∧
      ∃ ϖ' : ↥(NodeLocalized.coeffSubring A K'), (ϖ' : AlgebraicClosure ℚ) = (ϖ : AlgebraicClosure ℚ) ∧
        ∀ d : ↥(NodeLocalized.coeffSubring A K'), NodeLocalized.redRestrict red K' d = 0 ↔ ∃ d', d = ϖ' * d' := by
  by_cases hk : ∀ a : k, a ^ (q ^ 2) = a → a ∈ Set.range (NodeLocalized.redRestrict red K)
  · exact ⟨K, inferInstance, le_rfl, hk, ϖ, rfl, hϖ⟩
  by_cases hq2 : q = 2
  · have hirr : ∀ c : ↥(NodeLocalized.coeffSubring A K), NodeLocalized.redRestrict red K (c ^ 2 + c + 1) ≠ 0 := by
      intro c hc
      apply hk
      have hr := KWallAux.map_quad_eq_zero (NodeLocalized.redRestrict red K) c hc
      exact KWallAux.forall_mem_range_of_pow_eq_of_notMem_range (NodeLocalized.redRestrict red K) c
        (KWallAux.pow_card_sq_eq_of_quad hq2 _ hr) (KWallAux.notMem_range_of_quad hq2 _ hr)
    obtain ⟨K', hK', hle, ζ, hζ, -, hgen⟩ := NodeLocalized.exists_coeffSubring_inertQuadratic_cubeRoot red K ϖ hϖ hirr
    refine ⟨K', hK', KWallAux.le_of_coeffSubring_le A hle, ?_, Subring.inclusion hle ϖ, rfl, hgen⟩
    have hr := KWallAux.map_quad_eq_zero' (NodeLocalized.redRestrict red K') ζ hζ
    exact KWallAux.forall_mem_range_of_pow_eq_of_notMem_range (NodeLocalized.redRestrict red K') ζ
      (KWallAux.pow_card_sq_eq_of_quad hq2 _ hr) (KWallAux.notMem_range_of_quad hq2 _ hr)
  · obtain ⟨m, hm⟩ := KWallAux.exists_natCast_nonsquare hq2
    have hirr : ∀ c : ↥(NodeLocalized.coeffSubring A K),
        NodeLocalized.redRestrict red K (c ^ 2 - (m : ↥(NodeLocalized.coeffSubring A K))) ≠ 0 := by
      intro c hc
      apply hk
      have hr := KWallAux.map_sq_eq_natCast (NodeLocalized.redRestrict red K) c m hc
      exact KWallAux.forall_mem_range_of_pow_eq_of_notMem_range (NodeLocalized.redRestrict red K) c
        (KWallAux.pow_card_sq_eq_of_sq_eq_natCast _ m hr) (KWallAux.notMem_range_of_sq_eq_natCast m hm _ hr)
    obtain ⟨K', hK', hle, α, hα, -, hgen⟩ := NodeLocalized.exists_coeffSubring_inertQuadratic_sqrt red K ϖ hϖ m hirr
    refine ⟨K', hK', KWallAux.le_of_coeffSubring_le A hle, ?_, Subring.inclusion hle ϖ, rfl, hgen⟩
    have hr := KWallAux.map_sq_eq_natCast' (NodeLocalized.redRestrict red K') α m hα
    exact KWallAux.forall_mem_range_of_pow_eq_of_notMem_range (NodeLocalized.redRestrict red K') α
      (KWallAux.pow_card_sq_eq_of_sq_eq_natCast _ m hr) (KWallAux.notMem_range_of_sq_eq_natCast m hm _ hr)

theorem solution
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    {P : PlaceSpecialization A q N data hKr k red hα hβ}
    (R : ProlongationTuple P) [IsAlgClosed k] [DecidableEq k] (hqN : ¬ q ∣ N)
    (hmodel : R.IsModel) (hO : R.OrderLawFixed)
    (W : Finset (Place k (modularFunctionFieldC k N))) (hW : ∀ w ∈ W, w ∈ ssPlaces q N k)
    (hreg : R.RegularityLaw W) (hval : R.NodeValueLaw W)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
    (w : Place k (modularFunctionFieldC k N)) (hw : w ∈ W) (c : R.NodeCoordinates K w)
    (ϖ : ↥(NodeLocalized.coeffSubring A K))
    (hϖ : ∀ d : ↥(NodeLocalized.coeffSubring A K), NodeLocalized.redRestrict red K d = 0 ↔ ∃ d', d = ϖ * d') :
    (∀ g : ↥(R.nodeIntegersOver K w),
      (R.nodeResidue₁ w ⟨g, g.2.1⟩ = 0 ∧ R.nodeResidue₂ w ⟨g, g.2.1⟩ = 0) ↔ g ∈ Ideal.span {R.nodeConst K w ϖ}) := by
  obtain ⟨K'', hfin, hle, hk₀'', ϖ'', hϖ'', hϖ''gen⟩ :=
    NodeLocalized.exists_le_range_redRestrict_and_exists_generator_of_redRestrict_eq_zero_iff q red K ϖ hϖ
  haveI : FiniteDimensional ℚ K'' := hfin

  have hfield : NodeLocalized.fieldOver (N * q) K ≤ NodeLocalized.fieldOver (N * q) K'' := by
    apply Subfield.closure_mono
    apply Set.union_subset_union_left
    rintro _ ⟨⟨z, hz⟩, rfl⟩
    exact ⟨⟨z, hle hz⟩, rfl⟩
  have hmono : ∀ f : ↥(modularFunctionFieldBar (N * q)), f ∈ R.nodeIntegersOver K w → f ∈ R.nodeIntegersOver K'' w :=
    fun f hf => ⟨hf.1, hfield hf.2⟩

  have h84 := nodeIntegersOver_fibreProduct_of_orderLawFixed_of_range_redRestrict R hqN hmodel hO W hW hreg hval
    K'' hk₀'' w hw
    { x := ⟨c.x, hmono c.x c.x.2⟩, y := ⟨c.y, hmono c.y c.y.2⟩,
      x_fst := c.x_fst, x_snd := c.x_snd, y_snd := c.y_snd, y_fst := c.y_fst }
    ϖ'' hϖ''gen
  have hK'' := h84.1

  have hϖne : (ϖ : AlgebraicClosure ℚ) ≠ 0 := by
    intro h0
    have hq : NodeLocalized.redRestrict red K ((q : ℕ) : ↥(NodeLocalized.coeffSubring A K)) = 0 := by
      rw [map_natCast]; exact CharP.cast_eq_zero k q
    obtain ⟨d', hd'⟩ := (hϖ _).mp hq
    have hq' : ((q : ℕ) : AlgebraicClosure ℚ) = 0 := by
      have := congrArg (fun t : ↥(NodeLocalized.coeffSubring A K) => (t : AlgebraicClosure ℚ)) hd'
      simpa [h0] using this
    exact (Fact.out : q.Prime).ne_zero (by exact_mod_cast hq')
  have hconstK : ((algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (ϖ : AlgebraicClosure ℚ)
        : ↥(modularFunctionFieldBar (N * q))) : LaurentSeries (AlgebraicClosure ℚ))
      ∈ NodeLocalized.fieldOver (N * q) K :=
    Subfield.subset_closure (Or.inl ⟨⟨(ϖ : AlgebraicClosure ℚ), ϖ.2.2⟩, rfl⟩)
  have hconstne : ((algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (ϖ : AlgebraicClosure ℚ)
        : ↥(modularFunctionFieldBar (N * q))) : LaurentSeries (AlgebraicClosure ℚ)) ≠ 0 := by
    intro h0
    apply hϖne
    have h1 : (algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (ϖ : AlgebraicClosure ℚ)) = 0 :=
      Subtype.ext h0
    exact (map_eq_zero _).mp h1
  intro g
  have hg'' : (g : ↥(modularFunctionFieldBar (N * q))) ∈ R.nodeIntegersOver K'' w := hmono g g.2
  have hiff := hK'' ⟨g, hg''⟩
  constructor
  · intro hres
    have hmem := hiff.mp hres
    obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.mp hmem

    have hamb : ((a : ↥(R.nodeIntegersOver K'' w)) : ↥(modularFunctionFieldBar (N * q)))
        * algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (ϖ : AlgebraicClosure ℚ)
        = (g : ↥(modularFunctionFieldBar (N * q))) := by
      have h1 : ((a * R.nodeConst K'' w ϖ'' : ↥(R.nodeIntegersOver K'' w)) : ↥(modularFunctionFieldBar (N * q)))
          = (g : ↥(modularFunctionFieldBar (N * q))) := congrArg Subtype.val ha
      have h2 : ((a * R.nodeConst K'' w ϖ'' : ↥(R.nodeIntegersOver K'' w)) : ↥(modularFunctionFieldBar (N * q)))
          = (a : ↥(modularFunctionFieldBar (N * q)))
            * ((R.nodeConst K'' w ϖ'' : ↥(R.nodeIntegersOver K'' w)) : ↥(modularFunctionFieldBar (N * q))) :=
        rfl
      have h3 := R.coe_nodeConst K'' w ϖ''
      rw [hϖ''] at h3
      rw [h2, h3] at h1
      exact h1

    have hrat : (((a : ↥(R.nodeIntegersOver K'' w)) : ↥(modularFunctionFieldBar (N * q)))
        : LaurentSeries (AlgebraicClosure ℚ)) ∈ NodeLocalized.fieldOver (N * q) K := by
      have h1 : (((a : ↥(modularFunctionFieldBar (N * q)))
            * algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (ϖ : AlgebraicClosure ℚ)
            : ↥(modularFunctionFieldBar (N * q))) : LaurentSeries (AlgebraicClosure ℚ))
          = ((g : ↥(modularFunctionFieldBar (N * q))) : LaurentSeries (AlgebraicClosure ℚ)) :=
        congrArg Subtype.val hamb
      have h2 : (((a : ↥(modularFunctionFieldBar (N * q)))
            * algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (ϖ : AlgebraicClosure ℚ)
            : ↥(modularFunctionFieldBar (N * q))) : LaurentSeries (AlgebraicClosure ℚ))
          = (((a : ↥(modularFunctionFieldBar (N * q))) : LaurentSeries (AlgebraicClosure ℚ))
            * ((algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (ϖ : AlgebraicClosure ℚ)
              : ↥(modularFunctionFieldBar (N * q))) : LaurentSeries (AlgebraicClosure ℚ))) := rfl
      rw [h2] at h1
      rw [(eq_mul_inv_iff_mul_eq₀ hconstne).mpr h1]
      exact (NodeLocalized.fieldOver (N * q) K).mul_mem g.2.2 ((NodeLocalized.fieldOver (N * q) K).inv_mem hconstK)
    refine Ideal.mem_span_singleton'.mpr ⟨⟨a, a.2.1, hrat⟩, Subtype.ext ?_⟩
    have h2 : (((⟨a, a.2.1, hrat⟩ * R.nodeConst K w ϖ : ↥(R.nodeIntegersOver K w)))
          : ↥(modularFunctionFieldBar (N * q)))
        = (a : ↥(modularFunctionFieldBar (N * q)))
          * ((R.nodeConst K w ϖ : ↥(R.nodeIntegersOver K w)) : ↥(modularFunctionFieldBar (N * q))) :=
      rfl
    rw [h2, R.coe_nodeConst K w ϖ]
    exact hamb
  · intro hg
    obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.mp hg
    have hbamb : ((b : ↥(R.nodeIntegersOver K w)) : ↥(modularFunctionFieldBar (N * q)))
        * algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (ϖ : AlgebraicClosure ℚ)
        = (g : ↥(modularFunctionFieldBar (N * q))) := by
      have h1 : ((b * R.nodeConst K w ϖ : ↥(R.nodeIntegersOver K w)) : ↥(modularFunctionFieldBar (N * q)))
          = (g : ↥(modularFunctionFieldBar (N * q))) := congrArg Subtype.val hb
      have h2 : ((b * R.nodeConst K w ϖ : ↥(R.nodeIntegersOver K w)) : ↥(modularFunctionFieldBar (N * q)))
          = (b : ↥(modularFunctionFieldBar (N * q)))
            * ((R.nodeConst K w ϖ : ↥(R.nodeIntegersOver K w)) : ↥(modularFunctionFieldBar (N * q))) :=
        rfl
      rw [h2, R.coe_nodeConst K w ϖ] at h1
      exact h1
    apply hiff.mpr
    refine Ideal.mem_span_singleton'.mpr ⟨⟨b, hmono b b.2⟩, Subtype.ext ?_⟩
    have h2 : (((⟨b, hmono b b.2⟩ * R.nodeConst K'' w ϖ'' : ↥(R.nodeIntegersOver K'' w)))
          : ↥(modularFunctionFieldBar (N * q)))
        = (b : ↥(modularFunctionFieldBar (N * q)))
          * ((R.nodeConst K'' w ϖ'' : ↥(R.nodeIntegersOver K'' w)) : ↥(modularFunctionFieldBar (N * q))) :=
      rfl
    have h3 := R.coe_nodeConst K'' w ϖ''
    rw [hϖ''] at h3
    rw [h2, h3]
    exact hbamb

end S_ModularCurve_PlaceSpecialization_ProlongationTuple_nodeResidue_eq_zero_and_eq_zero_iff_mem_span_of_orderLawFixed
end P2MW
export P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_nodeResidue_eq_zero_and_eq_zero_iff_mem_span_of_orderLawFixed (solution)
