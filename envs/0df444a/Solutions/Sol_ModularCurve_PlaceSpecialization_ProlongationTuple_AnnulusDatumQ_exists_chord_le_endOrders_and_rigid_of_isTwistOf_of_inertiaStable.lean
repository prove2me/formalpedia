-- Prove2me | solution 1 for ModularCurve.PlaceSpecialization.ProlongationTuple.AnnulusDatumQ.exists_chord_le_endOrders_and_rigid_of_isTwistOf_of_inertiaStable
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/67bcd32e-0eaf-5cb5-8396-a696230cf11e

import Mathlib
import Definitions.Def_ModularCurve_ProlongationTuple
import Definitions.Def_ModularCurve_LevelOneAnnulusSpecializationOrbit
import Definitions.Def_ModularCurve_JWidth
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_valuation_pow_le_mul_prod_and_rigid_of_twist_levelOne
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_smul_mem_integers_and_residue_ne_zero_iff_valuation_eq
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_AnnulusDatumQ_den_circleDeg_eq_one_and_den_depthMoment_eq_one_of_inertiaStable
import Theorems.Thm_ModularCurve_NodeLocalized_isDiscreteValuationRing_coeffSubring
import Theorems.Thm_ModularCurve_arithFrobC_smul_arithFrobC_smul_eq_self_of_mem_ssPlaces
import Theorems.Thm_ModularCurve_arithFrobC_smul_eq_frobOnPlacesGeomLevel
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_AnnulusDatumQ_exists_chord_le_endOrders_and_rigid_of_isTwistOf_of_inertiaStable
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ValuationSubring.instIsAlgClosedResidueField ModularCurve.instIsElliptic_tateLaurent ModularCurve.instIsElliptic_tateBase WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.NodeLocalized.isLocalization_nodeDenominators ModularCurve.NodeLocalized.algebraEvalRange ModularCurve.NodeLocalized.isLocalRing_modularLocalizedAtPoint ModularCurve.NodeLocalized.isScalarTower_K_fieldOver_bar ModularCurve.NodeLocalized.algebraFieldOverBar ModularCurve.NodeLocalized.algebra_isIntegral_fieldOver_bar ModularCurve.NodeLocalized.isScalarTower_fieldOver_bar_laurent ModularCurve.NodeLocalized.charZero_fieldOver ModularCurve.NodeLocalized.algebraFieldOver ModularCurve.NodeLocalized.charZero_laurentSeries_algClosure ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid instTopologicallyFGOfFiniteType AdicCompletion.instIsLocalRingMaximalIdeal ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.B3.instIsElliptic_goodModel WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral instFieldLaurentSeriesAlgClosureRat instAlgebraModularFunctionFieldBar"
p2m_attr_erase "instance" "ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instAlgebraResidueFieldSubtypeMemValuationSubringGaussBaseResOne ModularCurve.PlaceSpecialization.LevelOneProlongationPair.algGaussBase instAlgebraModularFunctionFieldFullC ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instAlgebraSubtypeMemValuationSubringGaussBaseResOne ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instAlgebraSubtypeMemValuationSubringGaussBaseResTwo instFieldModularFunctionFieldC ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isScalarTower_resOne instFieldLaurentSeries' ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isScalarTower_resTwo instModuleModularFunctionFieldBar ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isLocalHom_resBase₁ instAlgebraModularFunctionFieldC ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isLocalHom_constToGaussBase ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instFieldResOne instFieldModularFunctionFieldBar ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instAlgebraResidueFieldSubtypeMemValuationSubringGaussBaseResTwo ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instFieldResTwo instFieldModularFunctionFieldFullC ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isScalarTower_gaussBase instAlgebraLaurentSeriesAlgClosureRat ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isLocalHom_resBase₂ ModularCurve.PlaceSpecialization.LevelOneProlongationPair.algResidueConst instCommRingModularFunctionFieldBar AlgebraicCurve.GaussReduction.isLocalHom_constToGauss ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar ModularCurve.numberField_of_finiteDimensional AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions"
p2m_attr_erase "instance" "IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.instIsScalarTowerJAdjoin WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4"
p2m_attr_erase "simp" "AlgebraicCurve.ComponentChart.ofConstantReduction_integers AlgebraicCurve.ComponentChart.mk.sizeOf_spec AlgebraicCurve.ComponentChart.ofConstantReduction_placeMap AlgebraicCurve.ComponentChart.ofConstantReduction_nodes AlgebraicCurve.ComponentChart.mk.injEq AlgebraicCurve.ComponentChart.ofConstantReduction_dom AlgebraicCurve.Annulus.mk.sizeOf_spec AlgebraicCurve.Annulus.mk.injEq ModularCurve.FinitePlaceLift.traceHom_coe ModularCurve.FinitePlaceLift.mk.injEq ModularCurve.FinitePlaceLift.mk.sizeOf_spec WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one ModularCurve.coe_nodeEquiv_symm_apply ModularCurve.frobNodePair_jOfNode ModularCurve.jOfNode_mk ModularCurve.widthOf_mk ModularCurve.frobNodePairEmb_apply ModularCurve.card_nodePairsOf ModularCurve.frobNodePair_snd ModularCurve.coe_nodeEquiv_apply ModularCurve.frobNodePair_fst ModularCurve.PlaceSpecialization.LevelOneProlongationPair.mk.sizeOf_spec ModularCurve.PlaceSpecialization.LevelOneProlongationPair.residue₂_apply ModularCurve.PlaceSpecialization.LevelOneProlongationPair.residue₁_apply ModularCurve.PlaceSpecialization.LevelOneProlongationPair.mk.injEq ModularCurve.PlaceSpecialization.LevelOneProlongationPair.chartFst_integers ModularCurve.PlaceSpecialization.LevelOneProlongationPair.chartFst_nodes ModularCurve.PlaceSpecialization.LevelOneProlongationPair.chartFst_residue ModularCurve.PlaceSpecialization.LevelOneProlongationPair.chartFst_dom ModularCurve.PlaceSpecialization.LevelOneProlongationPair.chartFst_placeMap ModularCurve.evalAtJqN_X"
p2m_attr_erase "simp" "ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ValuationSubring.reduceAt_coe ValuationSubring.reduceAt_one ValuationSubring.reduceAt_natCast ValuationSubring.reduceAt_intCast ValuationSubring.reduceAt_zero ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen"
p2m_attr_erase "simp" "ModularCurve.constantCoeff_dedekindEtaUnitQ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.xCoeffFull_succ"
p2m_attr_erase "simp" "TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg"
p2m_attr_erase "simp" "WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two ModularCurve.NodeLocalized.coe_modularEvalAt ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL AlgebraicCurve.Pic.baseChange_mk AlgebraicCurve.Place.forgetConstants_toValuationSubring AlgebraicCurve.Place.constantFieldEquiv_symm_apply AlgebraicCurve.Place.ord_forgetConstants AlgebraicCurve.Place.extendConstants_toValuationSubring AlgebraicCurve.Place.constantFieldEquiv_apply_toValuationSubring AlgebraicCurve.Place.mem_fiberConstants AlgebraicCurve.Place.restrictConstants_toValuationSubring AdicCompletion.evalₐ_mapₐ AdicCompletion.mapAlgEquivOfBijective_apply AdicCompletion.levelMapₐ_mk AdicCompletion.mapₐ_of AdicCompletion.mapAlgEquiv_symm_apply AdicCompletion.mapAlgEquiv_apply AdicCompletion.evalₐ_ofLevelwiseEquiv AdicCompletion.evalₐ_levelwiseHom AdicCompletion.localizationEquiv_of AdicCompletion.evalₐ_ofLevelwiseEquiv_symm Localization.AtPrime.quotientPowEquiv_mk ModularCurve.LambdaModularPolynomialData.mk.sizeOf_spec ModularCurve.LambdaModularPolynomialData.mk.injEq ModularCurve.ProjectiveLine.map_mk"
p2m_attr_erase "simp" "AdicCompletion.transportOf_of AdicCompletion.selfCompletion_smul_of AdicCompletion.tensorRingEquiv_tmul AdicCompletion.completionOfAlgHom_apply AdicCompletion.completionBaseChangeHom_of AdicCompletion.tensorRingHom_tmul AdicCompletion.stabilizerToCompletionAut_of ModularCurve.Gamma0Pair.map_toCurve WeierstrassCurve.mapPoint_eq_ratPointMap ModularCurve.Gamma0Pair.map_gen ModularCurve.Gamma0Pair.map_eq_gamma0PairMap ModularCurve.ModuliPoint.map_eq_moduliPointMapRingHom ModularCurve.ModuliPoint.map_mk WeierstrassCurve.mapPointHom_apply WeierstrassCurve.mapPoint_zero WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff WeierstrassCurve.veluX_empty WeierstrassCurve.vcInvEmbedding_apply"
p2m_attr_erase "simp" "ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.veluY_empty WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂"
p2m_attr_erase "simp" "PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT"
p2m_attr_erase "simp" "WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero ModularCurve.cuspCount_one WeierstrassCurve.Universal.halveX_zero WeierstrassCurve.Universal.specialize_X_one WeierstrassCurve.Universal.coeff_halve WeierstrassCurve.Universal.specialize_X_two WeierstrassCurve.Universal.halveCoeff_zero WeierstrassCurve.Universal.specialize_X_four WeierstrassCurve.Universal.coeff_halveX WeierstrassCurve.Universal.specialize_X_three WeierstrassCurve.Universal.specialize_X_zero HahnSeries.ramScale_apply ModularCurve.CharPModel.FibreModel.mk.injEq ModularCurve.CharPModel.FibreModel.mk.sizeOf_spec ModularCurve.PlaceSpecialization.LevelOneProlongationPair.coe_gaussOrderToIntegers₂ ModularCurve.PlaceSpecialization.LevelOneProlongationPair.coe_gaussOrderToIntegers₁ ModularCurve.PlaceSpecialization.LevelOneProlongationPair.coe_toIntegers₁ ModularCurve.PlaceSpecialization.LevelOneProlongationPair.coe_constToGaussBase ModularCurve.PlaceSpecialization.LevelOneProlongationPair.coe_toIntegers₂ AlgebraicCurve.GaussReduction.constToGauss_coe AlgebraicCurve.ComponentChart.ofConstantReductionNodes_dom AlgebraicCurve.ComponentChart.ofConstantReductionNodes_placeMap AlgebraicCurve.ComponentChart.ofConstantReductionNodes_nodes AlgebraicCurve.ComponentChart.ofConstantReductionNodes_residue AlgebraicCurve.ComponentChart.ofConstantReductionNodes_integers ModularCurve.frobeniusPullbackGeomLevelUnconditional_single ModularCurve.frobeniusPushforwardGeomLevelUnconditional_single ModularCurve.frobeniusGeomLevelUnconditional_apply_coe ModularCurve.symPoly_zero AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁"
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.deprecated false
set_option linter.unusedVariables false

open AlgebraicCurve ModularCurve ModularCurve.PlaceSpecialization

namespace CvqNT
open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.NodeLocalized ModularCurve.PlaceSpecialization ModularCurve.PlaceSpecialization.ProlongationTuple
open Classical

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}

local notation "Qb" => AlgebraicClosure ℚ

theorem not_strict_of_reduceFst_mem (P : PlaceSpecialization A q 1 data hKr k red hα hβ)
    {W : Finset (Place k ↥(modularFunctionFieldC k 1))} (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q 1 k)
    (V : Place Qb ↥(modularFunctionFieldBar (1 * q))) {w : Place k ↥(modularFunctionFieldC k 1)} (hw : w ∈ W) (hV : P.reduceFst V = w) :
    ¬ P.IsStrictFst V ∧ ¬ P.IsStrictSnd V := by
  have hq1 : ¬ q ∣ 1 := fun h => (Fact.out : q.Prime).one_lt.ne' (Nat.dvd_one.mp h)
  have hφ : ∀ v : Place k ↥(modularFunctionFieldC k 1), frobOnPlacesGeomLevel k 1 data hKr v = arithFrobC q k 1 • v :=
    fun v => (ModularCurve.arithFrobC_smul_eq_frobOnPlacesGeomLevel q k 1 data hKr v).symm
  have hfix2 : ∀ v ∈ W, arithFrobC q k 1 • (arithFrobC q k 1 • v) = v := fun v hv =>
    ModularCurve.arithFrobC_smul_arithFrobC_smul_eq_self_of_mem_ssPlaces q 1 hq1 k v ((hW v).mp hv)
  constructor
  · rintro ⟨-, h2⟩
    apply h2
    rw [hφ, hφ, hV]
    exact hfix2 w hw
  · rintro ⟨h1, h2⟩
    apply h2
    rw [hφ] at h1
    rw [hφ, hφ]
    have h3 : arithFrobC q k 1 • P.reduceSnd V = w := h1.symm.trans hV
    have hinj : Function.Injective fun v : Place k ↥(modularFunctionFieldC k 1) => arithFrobC q k 1 • v := MulAction.injective _
    have h4 : P.reduceSnd V = arithFrobC q k 1 • w := hinj (by simp only; rw [h3, hfix2 w hw])
    rw [h3, h4]

theorem divf_eq_neg_over (P : PlaceSpecialization A q 1 data hKr k red hα hβ)
    {W : Finset (Place k ↥(modularFunctionFieldC k 1))} (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q 1 k)
    {d₁ d₂ : ℕ} (Q₁ : Fin d₁ → Place Qb ↥(modularFunctionFieldBar (1 * q))) (Q₂ : Fin d₂ → Place Qb ↥(modularFunctionFieldBar (1 * q)))
    (hQ₁ : ∀ i, P.IsStrictFst (Q₁ i)) (hQ₂ : ∀ j, P.IsStrictSnd (Q₂ j))
    (E D : Divisor Qb ↥(modularFunctionFieldBar (1 * q))) {w : Place k ↥(modularFunctionFieldC k 1)} (hw : w ∈ W)
    (hEw : ∀ V : Place Qb ↥(modularFunctionFieldBar (1 * q)), P.reduceFst V = w → E V = 0)
    (V : Place Qb ↥(modularFunctionFieldBar (1 * q))) (hV : P.reduceFst V = w) :
    (E - (∑ i, Finsupp.single (Q₁ i) (1 : ℤ) + ∑ j, Finsupp.single (Q₂ j) (1 : ℤ)) - D) V = -(D V) := by
  have hns := not_strict_of_reduceFst_mem P hW V hw hV
  have h1 : (∑ i, Finsupp.single (Q₁ i) (1 : ℤ)) V = 0 := by
    rw [Finsupp.finset_sum_apply]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [Finsupp.single_apply, if_neg]
    rintro rfl; exact hns.1 (hQ₁ i)
  have h2 : (∑ j, Finsupp.single (Q₂ j) (1 : ℤ)) V = 0 := by
    rw [Finsupp.finset_sum_apply]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [Finsupp.single_apply, if_neg]
    rintro rfl; exact hns.2 (hQ₂ j)
  rw [Finsupp.sub_apply, Finsupp.sub_apply, Finsupp.add_apply, h1, h2, hEw V hV]
  ring

theorem sum_second_diff (a : ℕ → ℤ) (n : ℕ) :
    ∑ d ∈ Finset.Ico 1 (n + 1), (a (d - 1) - 2 * a d + a (d + 1)) = a 0 - a 1 - a n + a (n + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_Ico_succ_top (by omega), ih]
      simp only [Nat.add_sub_cancel]
      ring

theorem sum_mul_neg_laplacian (c : ℕ → ℤ) (e : ℕ) (he : 1 ≤ e) :
    ∑ d ∈ Finset.Ico 1 e, (d : ℤ) * (-(c (d - 1) - 2 * c d + c (d + 1))) =
      (e : ℤ) * (c (e - 1) - c e) + (c e - c 0) := by
  induction e with
  | zero => omega
  | succ n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · rw [Finset.sum_Ico_succ_top (by omega : 1 ≤ n), ih hn]
      have h1 : n + 1 - 1 = n := by omega
      rw [h1]
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      simp only [Nat.add_sub_cancel]
      push_cast
      ring

end CvqNT

namespace CvqTent

theorem tent_eval (δ : ℚ) (h0 : 0 ≤ δ) (d : ℕ) :
    max 0 (1 - |δ - (d : ℚ)|) =
      (if d = ⌊δ⌋₊ then 1 - (δ - ⌊δ⌋₊) else 0) + (if d = ⌊δ⌋₊ + 1 then δ - ⌊δ⌋₊ else 0) := by
  have hfl : (⌊δ⌋₊ : ℚ) ≤ δ := Nat.floor_le h0
  have hlt : δ < ⌊δ⌋₊ + 1 := Nat.lt_floor_add_one δ
  by_cases h1 : d = ⌊δ⌋₊
  · subst h1
    have h2 : ¬ (⌊δ⌋₊ = ⌊δ⌋₊ + 1) := by omega
    rw [if_pos rfl, if_neg h2, add_zero, abs_of_nonneg (by linarith)]
    exact max_eq_right (by linarith)
  · rw [if_neg h1, zero_add]
    by_cases h2 : d = ⌊δ⌋₊ + 1
    · subst h2
      rw [if_pos rfl, abs_of_nonpos (by push_cast; linarith)]
      push_cast
      rw [max_eq_right (by linarith)]
      ring
    · rw [if_neg h2]
      apply max_eq_left
      rcases Nat.lt_or_gt_of_ne h1 with h | h
      · have : (d : ℚ) + 1 ≤ ⌊δ⌋₊ := by exact_mod_cast h
        rw [abs_of_nonneg (by linarith)]
        linarith
      · have : (⌊δ⌋₊ : ℚ) + 2 ≤ d := by exact_mod_cast (show ⌊δ⌋₊ + 2 ≤ d by omega)
        rw [abs_of_nonpos (by linarith)]
        linarith

theorem tent_sum (n : ℕ) (δ : ℚ) (h0 : 0 ≤ δ) (hn : δ ≤ n) :
    ∑ d ∈ Finset.range (n + 1), max 0 (1 - |δ - (d : ℚ)|) = 1 := by
  have hfl : (⌊δ⌋₊ : ℚ) ≤ δ := Nat.floor_le h0
  have hmn : ⌊δ⌋₊ ≤ n := Nat.floor_le_of_le (by exact_mod_cast hn)
  rw [Finset.sum_congr rfl (fun d _ => tent_eval δ h0 d), Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq']
  have hm : ⌊δ⌋₊ ∈ Finset.range (n + 1) := Finset.mem_range.mpr (by omega)
  rw [if_pos hm]
  by_cases hm1 : ⌊δ⌋₊ + 1 ∈ Finset.range (n + 1)
  · rw [if_pos hm1]; ring
  · rw [if_neg hm1, add_zero]
    have h3 : ⌊δ⌋₊ = n := by rw [Finset.mem_range] at hm1; omega
    have h4 : δ = n := le_antisymm hn (by rw [← h3]; exact hfl)
    rw [h4]; simp

theorem tent_sum_mul (n : ℕ) (δ : ℚ) (h0 : 0 ≤ δ) (hn : δ ≤ n) :
    ∑ d ∈ Finset.range (n + 1), (d : ℚ) * max 0 (1 - |δ - (d : ℚ)|) = δ := by
  have hfl : (⌊δ⌋₊ : ℚ) ≤ δ := Nat.floor_le h0
  have hmn : ⌊δ⌋₊ ≤ n := Nat.floor_le_of_le (by exact_mod_cast hn)
  have hre : ∀ d ∈ Finset.range (n + 1), (d : ℚ) * max 0 (1 - |δ - (d : ℚ)|) =
      (if d = ⌊δ⌋₊ then (⌊δ⌋₊ : ℚ) * (1 - (δ - ⌊δ⌋₊)) else 0) +
        (if d = ⌊δ⌋₊ + 1 then ((⌊δ⌋₊ : ℚ) + 1) * (δ - ⌊δ⌋₊) else 0) := by
    intro d _
    rw [tent_eval δ h0 d, mul_add]
    congr 1
    · split_ifs with h
      · subst h; rfl
      · rw [mul_zero]
    · split_ifs with h
      · subst h; push_cast; rfl
      · rw [mul_zero]
  rw [Finset.sum_congr rfl hre, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq']
  have hm : ⌊δ⌋₊ ∈ Finset.range (n + 1) := Finset.mem_range.mpr (by omega)
  rw [if_pos hm]
  by_cases hm1 : ⌊δ⌋₊ + 1 ∈ Finset.range (n + 1)
  · rw [if_pos hm1]; ring
  · rw [if_neg hm1, add_zero]
    have h3 : ⌊δ⌋₊ = n := by rw [Finset.mem_range] at hm1; omega
    have h4 : δ = n := le_antisymm hn (by rw [← h3]; exact hfl)
    rw [h3, h4]; ring

end CvqTent

namespace CvqOrbit
open AlgebraicCurve ModularCurve ModularCurve.PlaceSpecialization ModularCurve.PlaceSpecialization.ProlongationTuple
open Classical

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
  {k : Type*} [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q}
  {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}

local notation "Qb" => AlgebraicClosure ℚ

theorem chainVal_zero {P : PlaceSpecialization A q 1 data hKr k red hα hβ} {R : ProlongationTuple P}
    {W : Finset (Place k ↥(modularFunctionFieldC k 1))} (dat : R.AnnulusDatumQ W) (a : TwistVector (k := k) W)
    (w : Place k ↥(modularFunctionFieldC k 1)) : dat.chainVal a w 0 = a.aZ := by
  unfold AnnulusDatumQ.chainVal; simp

theorem chainVal_width {P : PlaceSpecialization A q 1 data hKr k red hα hβ} {R : ProlongationTuple P}
    {W : Finset (Place k ↥(modularFunctionFieldC k 1))} (dat : R.AnnulusDatumQ W) (a : TwistVector (k := k) W)
    (w : Place k ↥(modularFunctionFieldC k 1)) (hw : 1 ≤ dat.width w) : dat.chainVal a w (dat.width w) = a.aZ' := by
  unfold AnnulusDatumQ.chainVal
  rw [if_neg (by omega), if_pos le_rfl]

theorem sum_annulus_eq_sum_circleDeg {P : PlaceSpecialization A q 1 data hKr k red hα hβ} {R : ProlongationTuple P}
    {W : Finset (Place k ↥(modularFunctionFieldC k 1))} (dat : R.AnnulusDatumQ W)
    (D : Divisor Qb ↥(modularFunctionFieldBar (1 * q))) (w : Place k ↥(modularFunctionFieldC k 1))
    (hdep : ∀ V ∈ D.support, P.reduceFst V = w → ¬ P.IsStrictFst V → ¬ P.IsStrictSnd V →
      0 ≤ dat.depthQ V ∧ dat.depthQ V ≤ dat.width w) :
    ∑ V ∈ D.support with (P.reduceFst V = w ∧ ¬ P.IsStrictFst V ∧ ¬ P.IsStrictSnd V), (D V : ℚ) =
      ∑ d ∈ Finset.range (dat.width w + 1), dat.circleDeg D w d := by
  unfold AnnulusDatumQ.circleDeg
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun V hV => ?_
  rw [Finset.mem_filter] at hV
  obtain ⟨hVs, hVw, h1, h2⟩ := hV
  rw [← Finset.mul_sum, CvqTent.tent_sum _ _ (hdep V hVs hVw h1 h2).1 (hdep V hVs hVw h1 h2).2, mul_one]

theorem depthMoment_eq_sum_mul_circleDeg {P : PlaceSpecialization A q 1 data hKr k red hα hβ} {R : ProlongationTuple P}
    {W : Finset (Place k ↥(modularFunctionFieldC k 1))} (dat : R.AnnulusDatumQ W)
    (D : Divisor Qb ↥(modularFunctionFieldBar (1 * q))) (w : Place k ↥(modularFunctionFieldC k 1))
    (hdep : ∀ V ∈ D.support, P.reduceFst V = w → ¬ P.IsStrictFst V → ¬ P.IsStrictSnd V →
      0 ≤ dat.depthQ V ∧ dat.depthQ V ≤ dat.width w) :
    dat.depthMoment D w = ∑ d ∈ Finset.range (dat.width w + 1), (d : ℚ) * dat.circleDeg D w d := by
  unfold AnnulusDatumQ.depthMoment AnnulusDatumQ.circleDeg
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun V hV => ?_
  rw [Finset.mem_filter] at hV
  obtain ⟨hVs, hVw, h1, h2⟩ := hV
  have hre : ∑ d ∈ Finset.range (dat.width w + 1), (d : ℚ) * ((D V : ℚ) * max 0 (1 - |dat.depthQ V - d|)) =
      (D V : ℚ) * ∑ d ∈ Finset.range (dat.width w + 1), (d : ℚ) * max 0 (1 - |dat.depthQ V - d|) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun d _ => by ring)
  rw [hre, CvqTent.tent_sum_mul _ _ (hdep V hVs hVw h1 h2).1 (hdep V hVs hVw h1 h2).2]

theorem sum_range_circleDeg_eq {P : PlaceSpecialization A q 1 data hKr k red hα hβ} {R : ProlongationTuple P}
    {W : Finset (Place k ↥(modularFunctionFieldC k 1))} (dat : R.AnnulusDatumQ W)
    (D : Divisor Qb ↥(modularFunctionFieldBar (1 * q))) (a : TwistVector (k := k) W) (ha : dat.IsTwistOf a D)
    {w : Place k ↥(modularFunctionFieldC k 1)} (hw : w ∈ W) (hwidth : 1 ≤ dat.width w)
    (hint0 : (dat.circleDeg D w 0).den = 1) (hintw : (dat.circleDeg D w (dat.width w)).den = 1) :
    ∑ d ∈ Finset.range (dat.width w + 1), dat.circleDeg D w d =
      ((dat.endOrderFst a D w + dat.endOrderSnd a D w : ℤ) : ℚ) := by
  have h0 : dat.circleDeg D w 0 = ((dat.endShareFst D w : ℤ) : ℚ) := by
    unfold AnnulusDatumQ.endShareFst
    rw [if_pos hint0]
    exact (Rat.coe_int_num_of_den_eq_one hint0).symm
  have hE : dat.circleDeg D w (dat.width w) = ((dat.endShareSnd D w : ℤ) : ℚ) := by
    unfold AnnulusDatumQ.endShareSnd
    rw [if_pos hintw]
    exact (Rat.coe_int_num_of_den_eq_one hintw).symm
  have hmid : ∑ d ∈ Finset.Ico 1 (dat.width w), dat.circleDeg D w d =
      ((dat.endSlopeFst a w + dat.endSlopeSnd a w : ℤ) : ℚ) := by
    obtain ⟨n, hn⟩ : ∃ n, dat.width w = n + 1 := ⟨dat.width w - 1, by omega⟩
    rw [Finset.sum_congr rfl (fun d hd => ha.2.2 w hw d (Finset.mem_Ico.mp hd).1
      (by have := (Finset.mem_Ico.mp hd).2; omega)), Finset.sum_neg_distrib, ← Int.cast_sum, hn,
      CvqNT.sum_second_diff]
    unfold AnnulusDatumQ.endSlopeFst AnnulusDatumQ.endSlopeSnd
    rw [hn, Nat.add_sub_cancel]
    push_cast
    ring
  rw [Finset.sum_range_succ, Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (by omega), zero_add, hmid, h0, hE]
  unfold AnnulusDatumQ.endOrderFst AnnulusDatumQ.endOrderSnd
  push_cast
  ring

theorem sum_range_mul_circleDeg_eq {P : PlaceSpecialization A q 1 data hKr k red hα hβ} {R : ProlongationTuple P}
    {W : Finset (Place k ↥(modularFunctionFieldC k 1))} (dat : R.AnnulusDatumQ W)
    (D : Divisor Qb ↥(modularFunctionFieldBar (1 * q))) (a : TwistVector (k := k) W) (ha : dat.IsTwistOf a D)
    {w : Place k ↥(modularFunctionFieldC k 1)} (hw : w ∈ W) (hwidth : 1 ≤ dat.width w)
    (hintw : (dat.circleDeg D w (dat.width w)).den = 1) :
    ∑ d ∈ Finset.range (dat.width w + 1), (d : ℚ) * dat.circleDeg D w d =
      ((dat.width w * dat.endOrderSnd a D w + (a.aZ' - a.aZ) : ℤ) : ℚ) := by
  have hE : dat.circleDeg D w (dat.width w) = ((dat.endShareSnd D w : ℤ) : ℚ) := by
    unfold AnnulusDatumQ.endShareSnd
    rw [if_pos hintw]
    exact (Rat.coe_int_num_of_den_eq_one hintw).symm
  have hmid : ∑ d ∈ Finset.Ico 1 (dat.width w), (d : ℚ) * dat.circleDeg D w d =
      ((dat.width w * dat.endSlopeSnd a w + (a.aZ' - a.aZ) : ℤ) : ℚ) := by
    have hre : ∀ d ∈ Finset.Ico 1 (dat.width w), (d : ℚ) * dat.circleDeg D w d =
        (((d : ℤ) * (-(dat.chainVal a w (d - 1) - 2 * dat.chainVal a w d + dat.chainVal a w (d + 1))) : ℤ) : ℚ) := by
      intro d hd
      rw [ha.2.2 w hw d (Finset.mem_Ico.mp hd).1 (by have := (Finset.mem_Ico.mp hd).2; omega)]
      push_cast
      ring
    rw [Finset.sum_congr rfl hre, ← Int.cast_sum, CvqNT.sum_mul_neg_laplacian _ _ hwidth, chainVal_zero,
      chainVal_width dat a w hwidth]
    unfold AnnulusDatumQ.endSlopeSnd
    rw [chainVal_width dat a w hwidth]
  rw [Finset.sum_range_succ, Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (by omega), Nat.cast_zero, zero_mul,
    zero_add, hmid, hE]
  unfold AnnulusDatumQ.endOrderSnd
  push_cast
  ring

theorem sum_annulus_eq_endOrders {P : PlaceSpecialization A q 1 data hKr k red hα hβ} {R : ProlongationTuple P}
    {W : Finset (Place k ↥(modularFunctionFieldC k 1))} (dat : R.AnnulusDatumQ W)
    (D : Divisor Qb ↥(modularFunctionFieldBar (1 * q))) (a : TwistVector (k := k) W) (ha : dat.IsTwistOf a D)
    {w : Place k ↥(modularFunctionFieldC k 1)} (hw : w ∈ W) (hwidth : 1 ≤ dat.width w)
    (hdep : ∀ V ∈ D.support, P.reduceFst V = w → ¬ P.IsStrictFst V → ¬ P.IsStrictSnd V →
      0 ≤ dat.depthQ V ∧ dat.depthQ V ≤ dat.width w)
    (hint : ∀ d : ℕ, (dat.circleDeg D w d).den = 1) :
    ∑ V ∈ D.support with (P.reduceFst V = w ∧ ¬ P.IsStrictFst V ∧ ¬ P.IsStrictSnd V), D V =
      dat.endOrderFst a D w + dat.endOrderSnd a D w := by
  have h := sum_annulus_eq_sum_circleDeg dat D w hdep
  rw [sum_range_circleDeg_eq dat D a ha hw hwidth (hint 0) (hint _), ← Int.cast_sum] at h
  exact_mod_cast h

theorem depthMoment_eq {P : PlaceSpecialization A q 1 data hKr k red hα hβ} {R : ProlongationTuple P}
    {W : Finset (Place k ↥(modularFunctionFieldC k 1))} (dat : R.AnnulusDatumQ W)
    (D : Divisor Qb ↥(modularFunctionFieldBar (1 * q))) (a : TwistVector (k := k) W) (ha : dat.IsTwistOf a D)
    {w : Place k ↥(modularFunctionFieldC k 1)} (hw : w ∈ W) (hwidth : 1 ≤ dat.width w)
    (hdep : ∀ V ∈ D.support, P.reduceFst V = w → ¬ P.IsStrictFst V → ¬ P.IsStrictSnd V →
      0 ≤ dat.depthQ V ∧ dat.depthQ V ≤ dat.width w)
    (hint : ∀ d : ℕ, (dat.circleDeg D w d).den = 1) :
    dat.depthMoment D w = ((dat.width w * dat.endOrderSnd a D w + (a.aZ' - a.aZ) : ℤ) : ℚ) := by
  rw [depthMoment_eq_sum_mul_circleDeg dat D w hdep, sum_range_mul_circleDeg_eq dat D a ha hw hwidth (hint _)]

end CvqOrbit

namespace CasqPkg
open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.NodeLocalized ModularCurve.PlaceSpecialization ModularCurve.PlaceSpecialization.ProlongationTuple

local notation "Qb" => AlgebraicClosure ℚ

theorem fieldOver_mono (N : ℕ) [NeZero N] {K K' : IntermediateField ℚ Qb} (h : K ≤ K') :
    fieldOver N K ≤ fieldOver N K' := by
  unfold fieldOver
  refine Subfield.closure_mono (Set.union_subset_union_left _ ?_)
  rintro _ ⟨c, rfl⟩
  exact ⟨⟨(c : Qb), h c.2⟩, rfl⟩

theorem coeffSubring_mono (A : ValuationSubring Qb) {K K' : IntermediateField ℚ Qb} (h : K ≤ K') :
    coeffSubring A K ≤ coeffSubring A K' := by
  intro c hc
  exact ⟨hc.1, h hc.2⟩

theorem redRestrict_inclusion (A : ValuationSubring Qb) {k : Type*} [Field k] (red : A →+* k)
    {K K' : IntermediateField ℚ Qb} (h : K ≤ K') (c : ↥(coeffSubring A K)) :
    redRestrict red K' (Subring.inclusion (coeffSubring_mono A h) c) = redRestrict red K c := rfl

theorem redRestrict_eq_zero_iff_not_isUnit (A : ValuationSubring Qb) {k : Type*} [Field k] (red : A →+* k)
    (hker : ∀ c : A, red c = 0 ↔ c ∈ IsLocalRing.maximalIdeal A)
    (K : IntermediateField ℚ Qb) (c : ↥(coeffSubring A K)) :
    redRestrict red K c = 0 ↔ ¬ IsUnit c := by
  show red ⟨(c : Qb), c.2.1⟩ = 0 ↔ _
  rw [hker, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_iff_not]
  constructor
  · intro hu
    obtain ⟨v, hv⟩ := hu.exists_right_inv
    have hvK : (v : Qb) ∈ K := by
      have h1 : (c : Qb) * (v : Qb) = 1 := congrArg Subtype.val hv
      have hc0 : (c : Qb) ≠ 0 := fun h0 => by rw [h0, zero_mul] at h1; exact zero_ne_one h1
      have : (v : Qb) = (c : Qb)⁻¹ := by field_simp; linear_combination h1
      rw [this]; exact inv_mem c.2.2
    exact isUnit_iff_exists_inv.mpr ⟨⟨(v : Qb), v.2, hvK⟩, Subtype.ext (show (c : Qb) * (v : Qb) = 1 from congrArg Subtype.val hv)⟩
  · intro hu
    obtain ⟨v, hv⟩ := hu.exists_right_inv
    exact isUnit_iff_exists_inv.mpr ⟨⟨(v : Qb), v.2.1⟩, Subtype.ext (show (c : Qb) * (v : Qb) = 1 from congrArg Subtype.val hv)⟩

theorem exists_uniformiser (A : ValuationSubring Qb) {q : ℕ} [Fact q.Prime] {k : Type*} [Field k] [CharP k q]
    (red : A →+* k) (hker : ∀ c : A, red c = 0 ↔ c ∈ IsLocalRing.maximalIdeal A)
    (K : IntermediateField ℚ Qb) [FiniteDimensional ℚ K] :
    ∃ ϖ : ↥(coeffSubring A K), Irreducible ϖ ∧
      ∀ d : ↥(coeffSubring A K), redRestrict red K d = 0 ↔ ∃ d', d = ϖ * d' := by
  haveI := isDiscreteValuationRing_coeffSubring red hker K
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible ↥(coeffSubring A K)
  refine ⟨ϖ, hϖ, fun d => ?_⟩
  rw [redRestrict_eq_zero_iff_not_isUnit A red hker K d, ← mem_nonunits_iff, ← IsLocalRing.mem_maximalIdeal,
    (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ, Ideal.mem_span_singleton]
  exact ⟨fun ⟨d', h⟩ => ⟨d', h⟩, fun ⟨d', h⟩ => ⟨d', h⟩⟩

theorem exists_zpow_mul_unit (A : ValuationSubring Qb) {q : ℕ} [Fact q.Prime] {k : Type*} [Field k] [CharP k q]
    (red : A →+* k) (hker : ∀ c : A, red c = 0 ↔ c ∈ IsLocalRing.maximalIdeal A)
    (K : IntermediateField ℚ Qb) [FiniteDimensional ℚ K]
    (ϖ : ↥(coeffSubring A K)) (hϖ : Irreducible ϖ) {c : Qb} (hcK : c ∈ K) (hc0 : c ≠ 0) :
    ∃ (m : ℤ) (η : ↥(coeffSubring A K)), IsUnit η ∧ c = ((ϖ : ↥(coeffSubring A K)) : Qb) ^ m * ((η : ↥(coeffSubring A K)) : Qb) := by
  haveI := isDiscreteValuationRing_coeffSubring red hker K
  have hϖ0 : ((ϖ : ↥(coeffSubring A K)) : Qb) ≠ 0 := fun h => hϖ.ne_zero (Subtype.ext h)
  rcases A.mem_or_inv_mem c with hcA | hcA
  · have hc : (⟨c, hcA, hcK⟩ : ↥(coeffSubring A K)) ≠ 0 := fun h => hc0 (congrArg Subtype.val h)
    obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hc hϖ
    refine ⟨n, u, u.isUnit, ?_⟩
    have := congrArg Subtype.val hu
    simp only [Subring.coe_mul, SubmonoidClass.coe_pow] at this
    rw [zpow_natCast, mul_comm]; exact this
  · have hcK' : c⁻¹ ∈ K := inv_mem hcK
    have hc : (⟨c⁻¹, hcA, hcK'⟩ : ↥(coeffSubring A K)) ≠ 0 := fun h => inv_ne_zero hc0 (congrArg Subtype.val h)
    obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hc hϖ
    refine ⟨-(n : ℤ), ↑(u⁻¹), (u⁻¹).isUnit, ?_⟩
    have h1 : c⁻¹ = ((u : ↥(coeffSubring A K)) : Qb) * ((ϖ : ↥(coeffSubring A K)) : Qb) ^ n := by
      have := congrArg Subtype.val hu
      simpa only [Subring.coe_mul, SubmonoidClass.coe_pow] using this
    have hu0 : ((u : ↥(coeffSubring A K)) : Qb) ≠ 0 := fun h => by
      rw [h, zero_mul] at h1; exact inv_ne_zero hc0 h1
    have huinv : (((u⁻¹ : (↥(coeffSubring A K))ˣ) : ↥(coeffSubring A K)) : Qb) = (((u : ↥(coeffSubring A K)) : Qb))⁻¹ := by
      exact eq_inv_of_mul_eq_one_left (by rw [← Subring.coe_mul, Units.inv_mul, Subring.coe_one])
    rw [zpow_neg, zpow_natCast, huinv, ← mul_inv, mul_comm, ← h1, inv_inv]

end CasqPkg

namespace CvqVal

variable {Γ : Type*} [LinearOrderedCommGroupWithZero Γ]

theorem eq_one_of_pow_eq_one {x : Γ} {n : ℕ} (hn : n ≠ 0) (h : x ^ n = 1) : x = 1 := by
  have hx0 : x ≠ 0 := by rintro rfl; rw [zero_pow hn] at h; exact zero_ne_one h
  set u : Γˣ := Units.mk0 x hx0 with hu
  have hun : u ^ n = 1 := Units.ext (by rw [Units.val_pow_eq_pow_val, hu, Units.val_mk0, h, Units.val_one])
  have hu1 : u = 1 := by
    rcases lt_trichotomy u 1 with hlt | heq | hgt
    · exact absurd hun (pow_lt_one' hlt hn).ne
    · exact heq
    · exact absurd hun (one_lt_pow' hgt hn).ne'
  have := congrArg (fun v : Γˣ => (v : Γ)) hu1
  simpa [hu] using this

theorem prod_zpow_eq_zpow_sum₀ {Γ : Type*} [CommGroupWithZero Γ] {ι : Type*} (s : Finset ι) (γ : Γ) (hγ : γ ≠ 0)
    (f : ι → ℤ) : ∏ i ∈ s, γ ^ f i = γ ^ (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, zpow_add₀ hγ]

theorem prod_zpow_mul_zpow_eq_one {ι : Type*} (s : Finset ι) (y : ι → Γ) (g : Γ) (hg : g ≠ 0)
    (e : ι → ℤ) (δ : ι → ℚ) (hδ : ∀ i ∈ s, 0 ≤ δ i)
    (hy : ∀ i ∈ s, y i ^ (δ i).den = g ^ (δ i).num.toNat)
    (m : ℤ) (hm : ∑ i ∈ s, (e i : ℚ) * δ i = m) :
    (∏ i ∈ s, y i ^ (-(e i))) * g ^ m = 1 := by
  classical
  set N : ℕ := ∏ i ∈ s, (δ i).den with hN
  have hNpos : 0 < N := Finset.prod_pos fun i _ => (δ i).den_pos
  have hdvd : ∀ i ∈ s, (δ i).den ∣ N := fun i hi => Finset.dvd_prod_of_mem _ hi

  have hterm : ∀ i ∈ s, (y i ^ (-(e i))) ^ N = g ^ ((((δ i).num.toNat * (N / (δ i).den) : ℕ) : ℤ) * (-(e i))) := by
    intro i hi
    obtain ⟨c, hc⟩ := hdvd i hi
    have hNd : N / (δ i).den = c := by rw [hc, Nat.mul_div_cancel_left _ (δ i).den_pos]
    rw [hNd]
    calc (y i ^ (-(e i))) ^ N = ((y i) ^ N) ^ (-(e i)) := by
            rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast]
      _ = (g ^ ((δ i).num.toNat * c)) ^ (-(e i)) := by rw [hc, pow_mul, hy i hi, ← pow_mul]
      _ = g ^ ((((δ i).num.toNat * c : ℕ) : ℤ) * (-(e i))) := by rw [← zpow_natCast, ← zpow_mul]

  have hexp : (∑ i ∈ s, (((δ i).num.toNat * (N / (δ i).den) : ℕ) : ℤ) * (-(e i))) + m * N = 0 := by
    have hi : ∀ i ∈ s, ((((δ i).num.toNat * (N / (δ i).den) : ℕ) : ℤ) : ℚ) * (-(e i : ℚ)) =
        (N : ℚ) * (-((e i : ℚ) * δ i)) := by
      intro i hi
      obtain ⟨c, hc⟩ := hdvd i hi
      have hNd : N / (δ i).den = c := by rw [hc, Nat.mul_div_cancel_left _ (δ i).den_pos]
      have hnum' : ((δ i).num.toNat : ℚ) = (δ i).num := by
        have : ((δ i).num.toNat : ℤ) = (δ i).num := Int.toNat_of_nonneg (Rat.num_nonneg.mpr (hδ i hi))
        exact_mod_cast this
      have hδeq : ((δ i).num : ℚ) = δ i * (δ i).den := (Rat.mul_den_eq_num (δ i)).symm
      rw [hNd, Int.cast_natCast, Nat.cast_mul, hnum', hδeq, hc, Nat.cast_mul]
      ring
    have hq : (((∑ i ∈ s, (((δ i).num.toNat * (N / (δ i).den) : ℕ) : ℤ) * (-(e i))) + m * N : ℤ) : ℚ) = 0 := by
      rw [Int.cast_add, Int.cast_mul, Int.cast_sum, Int.cast_natCast,
        Finset.sum_congr rfl (fun i hi' => by rw [Int.cast_mul, Int.cast_neg, hi i hi']), ← Finset.mul_sum,
        Finset.sum_neg_distrib, hm]
      ring
    exact_mod_cast hq
  apply eq_one_of_pow_eq_one hNpos.ne'
  rw [mul_pow, ← Finset.prod_pow, Finset.prod_congr rfl hterm, prod_zpow_eq_zpow_sum₀ s g hg, ← zpow_natCast (g ^ m),
    ← zpow_mul, ← zpow_add₀ hg, hexp, zpow_zero]

end CvqVal

namespace CvqAng
open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.NodeLocalized ModularCurve.PlaceSpecialization ModularCurve.PlaceSpecialization.ProlongationTuple
open Classical

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}

local notation "Qb" => AlgebraicClosure ℚ

theorem valuation_prod_mul_eq_one {P : PlaceSpecialization A q 1 data hKr k red hα hβ} {R : ProlongationTuple P}
    {W : Finset (Place k ↥(modularFunctionFieldC k 1))} (dat : R.AnnulusDatumQ W)
    {w : Place k ↥(modularFunctionFieldC k 1)} (hw : w ∈ W)
    (hdepthQ : ∀ (V : Place Qb ↥(modularFunctionFieldBar (1 * q))),
        P.reduceFst V = w → ¬ P.IsStrictFst V → ¬ P.IsStrictSnd V →
          0 < dat.depthQ V ∧ dat.depthQ V < dat.width w ∧ (dat.coord w hw).yDepth V ^ (dat.depthQ V).den =
            A.valuation (((q : ℕ) : Qb)) ^ (dat.depthQ V).num.toNat)
    (S : Finset (Place Qb ↥(modularFunctionFieldBar (1 * q))))
    (hS : ∀ V ∈ S, P.reduceFst V = w ∧ ¬ P.IsStrictFst V ∧ ¬ P.IsStrictSnd V)
    (e : Place Qb ↥(modularFunctionFieldBar (1 * q)) → ℤ) (m : ℤ) (hm : ∑ V ∈ S, (e V : ℚ) * dat.depthQ V = m) :
    A.valuation ((∏ V ∈ S, V.evalAt (((dat.coord w hw).y : ↥(modularFunctionFieldBar (1 * q)))) ^ (-(e V))) *
      ((q : ℕ) : Qb) ^ m) = 1 := by
  have hq0 : ((q : ℕ) : Qb) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : q.Prime).ne_zero
  have hvq0 : A.valuation ((q : ℕ) : Qb) ≠ 0 := (Valuation.ne_zero_iff _).mpr hq0
  rw [map_mul, map_zpow₀, map_prod]
  simp_rw [map_zpow₀]
  exact CvqVal.prod_zpow_mul_zpow_eq_one S
    (fun V => A.valuation (V.evalAt (((dat.coord w hw).y : ↥(modularFunctionFieldBar (1 * q)))))) _ hvq0 e dat.depthQ
    (fun V hV => (hdepthQ V (hS V hV).1 (hS V hV).2.1 (hS V hV).2.2).1.le)
    (fun V hV => (hdepthQ V (hS V hV).1 (hS V hV).2.1 (hS V hV).2.2).2.2) m hm

theorem exists_mem_red_ne_zero {P : PlaceSpecialization A q 1 data hKr k red hα hβ} {R : ProlongationTuple P}
    {W : Finset (Place k ↥(modularFunctionFieldC k 1))} (dat : R.AnnulusDatumQ W)
    (hker : ∀ c : A, red c = 0 ↔ c ∈ IsLocalRing.maximalIdeal A)
    {w : Place k ↥(modularFunctionFieldC k 1)} (hw : w ∈ W)
    (hdepthQ : ∀ (V : Place Qb ↥(modularFunctionFieldBar (1 * q))),
        P.reduceFst V = w → ¬ P.IsStrictFst V → ¬ P.IsStrictSnd V →
          0 < dat.depthQ V ∧ dat.depthQ V < dat.width w ∧ (dat.coord w hw).yDepth V ^ (dat.depthQ V).den =
            A.valuation (((q : ℕ) : Qb)) ^ (dat.depthQ V).num.toNat)
    (S : Finset (Place Qb ↥(modularFunctionFieldBar (1 * q))))
    (hS : ∀ V ∈ S, P.reduceFst V = w ∧ ¬ P.IsStrictFst V ∧ ¬ P.IsStrictSnd V)
    (e : Place Qb ↥(modularFunctionFieldBar (1 * q)) → ℤ) (m : ℤ) (hm : ∑ V ∈ S, (e V : ℚ) * dat.depthQ V = m) :
    ∃ hmem : (∏ V ∈ S, V.evalAt (((dat.coord w hw).y : ↥(modularFunctionFieldBar (1 * q)))) ^ (-(e V))) *
        ((q : ℕ) : Qb) ^ m ∈ A, red ⟨_, hmem⟩ ≠ 0 := by
  have hval := valuation_prod_mul_eq_one dat hw hdepthQ S hS e m hm
  have hmem : (∏ V ∈ S, V.evalAt (((dat.coord w hw).y : ↥(modularFunctionFieldBar (1 * q)))) ^ (-(e V))) *
      ((q : ℕ) : Qb) ^ m ∈ A := (A.valuation_le_one_iff _).mp hval.le
  have hunit : IsUnit (⟨_, hmem⟩ : A) := (A.valuation_eq_one_iff _).mpr hval
  exact ⟨hmem, fun h0 => (IsLocalRing.mem_maximalIdeal _ |>.mp ((hker _).mp h0)) hunit⟩

theorem angFactor_spec {P : PlaceSpecialization A q 1 data hKr k red hα hβ} {R : ProlongationTuple P}
    {W : Finset (Place k ↥(modularFunctionFieldC k 1))} (dat : R.AnnulusDatumQ W)
    (hker : ∀ c : A, red c = 0 ↔ c ∈ IsLocalRing.maximalIdeal A)
    {w : Place k ↥(modularFunctionFieldC k 1)} (hw : w ∈ W)
    (hdepthQ : ∀ (V : Place Qb ↥(modularFunctionFieldBar (1 * q))),
        P.reduceFst V = w → ¬ P.IsStrictFst V → ¬ P.IsStrictSnd V →
          0 < dat.depthQ V ∧ dat.depthQ V < dat.width w ∧ (dat.coord w hw).yDepth V ^ (dat.depthQ V).den =
            A.valuation (((q : ℕ) : Qb)) ^ (dat.depthQ V).num.toNat)
    (D : Divisor Qb ↥(modularFunctionFieldBar (1 * q))) (hdm : (dat.depthMoment D w).den = 1) :
    ∃ hmem : (∏ V ∈ D.support with (P.reduceFst V = w ∧ ¬ P.IsStrictFst V ∧ ¬ P.IsStrictSnd V),
          V.evalAt (((dat.coord w hw).y : ↥(modularFunctionFieldBar (1 * q)))) ^ (-(D V))) *
        ((q : ℕ) : Qb) ^ (dat.depthMoment D w).num ∈ A,
      red ⟨_, hmem⟩ ≠ 0 ∧ (dat.angFactor w hw D : k) = red ⟨_, hmem⟩ := by
  have hm : ∑ V ∈ D.support with (P.reduceFst V = w ∧ ¬ P.IsStrictFst V ∧ ¬ P.IsStrictSnd V),
      ((D V : ℤ) : ℚ) * dat.depthQ V = (dat.depthMoment D w).num := by
    rw [Rat.coe_int_num_of_den_eq_one hdm]
    unfold AnnulusDatumQ.depthMoment
    rfl
  obtain ⟨hmem, hred0⟩ := exists_mem_red_ne_zero dat hker hw hdepthQ _ (fun V hV => (Finset.mem_filter.mp hV).2)
    (fun V => D V) _ hm
  refine ⟨hmem, hred0, ?_⟩
  unfold AnnulusDatumQ.angFactor
  rw [dif_pos ⟨hdm, hmem, hred0⟩]
  rfl

end CvqAng

namespace CvqOrbit
open AlgebraicCurve ModularCurve ModularCurve.PlaceSpecialization ModularCurve.PlaceSpecialization.ProlongationTuple

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
  {k : Type*} [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q}
  {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}

@[reducible] def toAnnulusDatum {P : PlaceSpecialization A q 1 data hKr k red hα hβ} {R : ProlongationTuple P}
    {W : Finset (Place k ↥(modularFunctionFieldC k 1))} (dat : R.AnnulusDatumQ W) : R.AnnulusDatum W where
  K := dat.K
  coord := dat.coord
  width := dat.width
  depth := fun _ => 0
  cusp := dat.cusp
  unifFst := dat.unifFst
  unifSnd := dat.unifSnd
  u0 := dat.u0
  lam := dat.lam
  mu := dat.mu

end CvqOrbit

namespace CasqLog
open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.NodeLocalized

variable {Γ : Type*} [LinearOrderedCommGroupWithZero Γ]

theorem zpow_le_zpow_iff_of_lt_one {γ : Γ} (h0 : γ ≠ 0) (h1 : γ < 1) (a b : ℤ) : γ ^ a ≤ γ ^ b ↔ b ≤ a := by
  set u : Γˣ := Units.mk0 γ h0 with hu
  have hu1 : u < 1 := by rw [← Units.val_lt_val, hu, Units.val_mk0, Units.val_one]; exact h1
  have hum : ∀ k : ℤ, ((u ^ k : Γˣ) : Γ) = γ ^ k := fun k => by rw [Units.val_zpow_eq_zpow_val, hu, Units.val_mk0]
  have hinv : 1 < u⁻¹ := one_lt_inv'.mpr hu1
  have hsm : StrictMono fun k : ℤ => (u⁻¹) ^ k := zpow_right_strictMono hinv
  rw [← hum, ← hum, Units.val_le_val]
  have ha : u ^ a = (u⁻¹) ^ (-a) := by rw [inv_zpow', neg_neg]
  have hb : u ^ b = (u⁻¹) ^ (-b) := by rw [inv_zpow', neg_neg]
  rw [ha, hb, hsm.le_iff_le]
  omega

theorem zpow_eq_zpow_iff_of_lt_one {γ : Γ} (h0 : γ ≠ 0) (h1 : γ < 1) (a b : ℤ) : γ ^ a = γ ^ b ↔ a = b := by
  constructor
  · intro h
    have h₁ := (zpow_le_zpow_iff_of_lt_one h0 h1 a b).mp h.le
    have h₂ := (zpow_le_zpow_iff_of_lt_one h0 h1 b a).mp h.ge
    omega
  · rintro rfl; rfl

local notation "Qb" => AlgebraicClosure ℚ

theorem exists_valuation_eq_pow (A : ValuationSubring Qb) {q : ℕ} [Fact q.Prime] {k : Type*} [Field k] [CharP k q]
    (red : A →+* k) (hker : ∀ c : A, red c = 0 ↔ c ∈ IsLocalRing.maximalIdeal A) (c : Qb) (hc0 : c ≠ 0) :
    ∃ (γ : A.ValueGroup) (e₀ : ℕ) (n₀ : ℤ), γ ≠ 0 ∧ γ < 1 ∧ 1 ≤ e₀ ∧
      A.valuation ((q : ℕ) : Qb) = γ ^ e₀ ∧ A.valuation c = γ ^ n₀ := by
  set K₀ : IntermediateField ℚ Qb := IntermediateField.adjoin ℚ ({c} : Set Qb) with hK₀
  have hint : IsIntegral ℚ c := (Algebra.IsAlgebraic.isAlgebraic (R := ℚ) c).isIntegral
  haveI : FiniteDimensional ℚ ↥K₀ := IntermediateField.adjoin.finiteDimensional hint
  obtain ⟨ϖ₀, hirr, hϖ₀⟩ := CasqPkg.exists_uniformiser A red hker K₀
  have hcK : c ∈ K₀ := IntermediateField.mem_adjoin_simple_self ℚ c
  have hq0 : ((q : ℕ) : Qb) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : q.Prime).ne_zero
  have hqK : ((q : ℕ) : Qb) ∈ K₀ := natCast_mem K₀ q
  obtain ⟨n₀, η, hη, hcfac⟩ := CasqPkg.exists_zpow_mul_unit A red hker K₀ ϖ₀ hirr hcK hc0
  obtain ⟨nq, ηq, hηq, hqfac⟩ := CasqPkg.exists_zpow_mul_unit A red hker K₀ ϖ₀ hirr hqK hq0

  have hvunit : ∀ z : ↥(coeffSubring A K₀), IsUnit z → A.valuation ((z : ↥(coeffSubring A K₀)) : Qb) = 1 := by
    intro z hz
    have : IsUnit (⟨(z : Qb), z.2.1⟩ : A) := by
      obtain ⟨v, hv⟩ := hz.exists_right_inv
      exact isUnit_iff_exists_inv.mpr ⟨⟨(v : Qb), v.2.1⟩, Subtype.ext (show (z : Qb) * (v : Qb) = 1 from congrArg Subtype.val hv)⟩
    exact (A.valuation_eq_one_iff _).mp this
  set γ := A.valuation ((ϖ₀ : ↥(coeffSubring A K₀)) : Qb) with hγ
  have hϖ0' : ((ϖ₀ : ↥(coeffSubring A K₀)) : Qb) ≠ 0 := fun h => hirr.ne_zero (Subtype.ext h)
  have hγ0 : γ ≠ 0 := (Valuation.ne_zero_iff _).mpr hϖ0'
  have hγ1 : γ < 1 := by
    have hnu : ¬ IsUnit ϖ₀ := hirr.not_isUnit
    rw [← CasqPkg.redRestrict_eq_zero_iff_not_isUnit A red hker K₀ ϖ₀] at hnu
    have hmem : (⟨((ϖ₀ : ↥(coeffSubring A K₀)) : Qb), ϖ₀.2.1⟩ : A) ∈ IsLocalRing.maximalIdeal A := (hker _).mp hnu
    exact (A.valuation_lt_one_iff _).mp hmem
  have hvq : A.valuation ((q : ℕ) : Qb) = γ ^ nq := by
    rw [hqfac, map_mul, map_zpow₀, hvunit ηq hηq, mul_one]
  have hvc : A.valuation c = γ ^ n₀ := by
    rw [hcfac, map_mul, map_zpow₀, hvunit η hη, mul_one]

  have hq1 : A.valuation ((q : ℕ) : Qb) < 1 := by
    have hqA : ((q : ℕ) : Qb) ∈ A := natCast_mem A q
    have hred : red ⟨_, hqA⟩ = 0 := by
      have : (⟨((q : ℕ) : Qb), hqA⟩ : A) = ((q : ℕ) : A) := Subtype.ext (by simp)
      rw [this, map_natCast, CharP.cast_eq_zero]
    exact (A.valuation_lt_one_iff _).mp ((hker _).mp hred)
  have hnq : 1 ≤ nq := by
    by_contra hlt
    push Not at hlt
    have : γ ^ (0 : ℤ) ≤ γ ^ nq := (zpow_le_zpow_iff_of_lt_one hγ0 hγ1 0 nq).mpr (by omega)
    rw [zpow_zero, ← hvq] at this
    exact absurd hq1 (not_lt.mpr this)
  refine ⟨γ, nq.toNat, n₀, hγ0, hγ1, by omega, ?_, hvc⟩
  rw [hvq, ← zpow_natCast, Int.toNat_of_nonneg (by omega)]

end CasqLog

set_option maxHeartbeats 32000000 in
open ModularCurve.PlaceSpecialization.ProlongationTuple in

theorem solution
    {q : ℕ} [Fact q.Prime] (hq5 : 5 ≤ q) {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
    (P : PlaceSpecialization A q 1 data hKr k red hα hβ)
    {W : Finset (Place k (modularFunctionFieldC k 1))}
    (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q 1 k)
    (R : ProlongationTuple P) (hR : R.IsModel) (hRL : R.RegularityLaw W) (hNV : R.NodeValueLaw W)
    (hO : R.OrderLawFixed)
    (dat : R.AnnulusDatumQ W)
    (hwidth : ∀ w ∈ W, 1 ≤ dat.width w)
    (hwidthj : ∀ w ∈ W, dat.width w = jWidth (w.evalAt (jGeomGen k 1)))
    (hdepthQ : ∀ (w : Place k (modularFunctionFieldC k 1)) (hw : w ∈ W)
        (V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))),
        P.reduceFst V = w → ¬ P.IsStrictFst V → ¬ P.IsStrictSnd V →
          0 < dat.depthQ V ∧ dat.depthQ V < dat.width w ∧ (dat.coord w hw).yDepth V ^ (dat.depthQ V).den =
            A.valuation (((q : ℕ) : AlgebraicClosure ℚ)) ^ (dat.depthQ V).num.toNat)
    (hdepthσ : ∀ σ ∈ A.inertiaSubgroupIn ℚ, ∀ V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)),
        dat.depthQ (arithmeticGalois (modularFunctionFieldFull (1 * q)) σ • V) = dat.depthQ V)
    (hcusp : dat.cusp ∉ W) (hcuspφ : arithFrobC q k 1 • dat.cusp = dat.cusp)
    (hunif : ∀ w ∈ W,
      (∀ v : Place k (modularFunctionFieldC k 1),
          ((Finsupp.single w (1 : ℤ) - Finsupp.single dat.cusp 1 :
              Divisor k ↥(modularFunctionFieldC k 1)) v) = v.ord (dat.unifFst w)) ∧
      (∀ v : Place k (modularFunctionFieldC k 1),
          ((Finsupp.single (arithFrobC q k 1 • w) (1 : ℤ) - Finsupp.single dat.cusp 1 :
              Divisor k ↥(modularFunctionFieldC k 1)) v) = v.ord (dat.unifSnd w)))
    (hKfix : ∀ w ∈ W, ∀ σ ∈ A.inertiaSubgroupIn ℚ, ∀ z ∈ dat.K w, σ z = z)
    [hK : ∀ w : Place k (modularFunctionFieldC k 1), FiniteDimensional ℚ ↥(dat.K w)]
    (ϖ : ∀ w : Place k (modularFunctionFieldC k 1), ↥(NodeLocalized.coeffSubring A (dat.K w)))
    (hϖ : ∀ w ∈ W, ∀ d : ↥(NodeLocalized.coeffSubring A (dat.K w)),
      NodeLocalized.redRestrict red (dat.K w) d = 0 ↔ ∃ d', d = ϖ w * d')
    (eK : Place k (modularFunctionFieldC k 1) → ℕ) (heK : ∀ w ∈ W, 1 ≤ eK w)
    (ε : ∀ w : Place k (modularFunctionFieldC k 1), ↥(NodeLocalized.coeffSubring A (dat.K w)))
    (hε : ∀ w ∈ W, IsUnit (ε w))
    (hqϖ : ∀ w ∈ W, ((q : ℕ) : ↥(NodeLocalized.coeffSubring A (dat.K w))) = ϖ w ^ eK w * ε w)
    (hε1 : ∀ w ∈ W, NodeLocalized.redRestrict red (dat.K w) (ε w) = 1)
    (u : ∀ (w : Place k (modularFunctionFieldC k 1)) (hw : w ∈ W), ↥(R.nodeIntegersOver (dat.K w) w))
    (hu : ∀ (w : Place k (modularFunctionFieldC k 1)) (hw : w ∈ W), IsUnit (u w hw) ∧
        (dat.coord w hw).x * (dat.coord w hw).y = R.nodeConst (dat.K w) w (ϖ w) ^ (dat.width w * eK w) * u w hw)
    (hmax : ∀ (w : Place k (modularFunctionFieldC k 1)) (hw : w ∈ W),
        (Ideal.span {R.nodeConst (dat.K w) w (ϖ w), (dat.coord w hw).x, (dat.coord w hw).y}).IsMaximal ∧
        ∀ M : Ideal ↥(R.nodeIntegersOver (dat.K w) w), M.IsMaximal →
          M = Ideal.span {R.nodeConst (dat.K w) w (ϖ w), (dat.coord w hw).x, (dat.coord w hw).y})
    (hbr : ∀ (w : Place k (modularFunctionFieldC k 1)) (hw : w ∈ W),
        (Ideal.span {R.nodeConst (dat.K w) w (ϖ w), (dat.coord w hw).x}).IsPrime ∧
        (Ideal.span {R.nodeConst (dat.K w) w (ϖ w), (dat.coord w hw).y}).IsPrime ∧
        (dat.coord w hw).y ∉ Ideal.span {R.nodeConst (dat.K w) w (ϖ w), (dat.coord w hw).x} ∧
        (dat.coord w hw).x ∉ Ideal.span {R.nodeConst (dat.K w) w (ϖ w), (dat.coord w hw).y})
    (hnoeth : ∀ w ∈ W, IsNoetherianRing ↥(R.nodeIntegersOver (dat.K w) w))
    (hres : ∀ w ∈ W, ∀ g : ↥(R.nodeIntegersOver (dat.K w) w),
        ∃ o : ↥(NodeLocalized.coeffSubring A (dat.K w)), ¬ IsUnit (g - R.nodeConst (dat.K w) w o))
    (hVI : ∀ w ∈ W, R.ValueIntegralityLaw w)
    (hu0 : ∀ (w : Place k (modularFunctionFieldC k 1)) (hw : w ∈ W),
      w.HasValue (R.nodeResidue₁ w ⟨(u w hw : ↥(modularFunctionFieldBar (1 * q))), (u w hw).2.1⟩) ((dat.u0 w : kˣ) : k))
    (hlam : ∀ (w : Place k (modularFunctionFieldC k 1)) (hw : w ∈ W),
      w.HasValue (R.nodeResidue₁ w ⟨((dat.coord w hw).y : ↥(modularFunctionFieldBar (1 * q))), (dat.coord w hw).y.2.1⟩
        / dat.unifFst w) ((dat.lam w : kˣ) : k))
    (hmu : ∀ (w : Place k (modularFunctionFieldC k 1)) (hw : w ∈ W),
      (arithFrobC q k 1 • w).HasValue
        (R.nodeResidue₂ w ⟨((dat.coord w hw).x : ↥(modularFunctionFieldBar (1 * q))), (dat.coord w hw).x.2.1⟩
          / dat.unifSnd w) ((dat.mu w : kˣ) : k))
    (D : ↥(Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar (1 * q)))))
    (hDstab : ∀ σ ∈ A.inertiaSubgroupIn ℚ,
        arithmeticGalois (modularFunctionFieldFull (1 * q)) σ • (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))) = D)
    (hDsupp : ∀ V ∈ (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))).support,
      P.IsStrictFst V ∨ P.IsStrictSnd V ∨ P.reduceFst V ∈ W)
    (a : ProlongationTuple.TwistVector (k := k) W)
    (ha : dat.IsTwistOf a (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))))
    (hadm : dat.spData a (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)))
      ∈ GluingData.admissible (nodePairsOfPlaces (arithFrobC q k 1) W))
    (hsp : GluedPic0.mk (nodePairsOfPlaces (arithFrobC q k 1) W)
      ⟨dat.spData a (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))), hadm⟩ = 0)

    {d₁ d₂ : ℕ}
    (Q₁ : Fin d₁ → Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)))
    (Q₂ : Fin d₂ → Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)))
    (hQ₁ : ∀ i, P.IsStrictFst (Q₁ i)) (hQ₂ : ∀ j, P.IsStrictSnd (Q₂ j))
    (E : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))) (hE0 : 0 ≤ E)
    (f : ↥(modularFunctionFieldBar (1 * q))) (hf0 : f ≠ 0)
    (hdivf : ∀ V, (E - (∑ i, Finsupp.single (Q₁ i) (1 : ℤ) + ∑ j, Finsupp.single (Q₂ j) (1 : ℤ))
      - (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)))) V = V.ord f)

    (hker : ∀ c : A, red c = 0 ↔ c ∈ IsLocalRing.maximalIdeal A)
    :
    ∃ δ : ℚ,

      (∀ (c : AlgebraicClosure ℚ) (h : c • f ∈ R.R₁.integers), R.R₁.residue ⟨c • f, h⟩ ≠ 0 →
        ∀ w ∈ W, δ ≤ (dat.width w : ℚ) * ((w.ord (R.residue₁ ⟨c • f, h⟩) : ℚ) + (dat.endOrderFst a (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))) w : ℚ))) ∧

      (∀ (c : AlgebraicClosure ℚ) (h : c • f ∈ R.R₂.integers), R.R₂.residue ⟨c • f, h⟩ ≠ 0 →
        ∀ w ∈ W, -((dat.width w : ℚ) * (((arithFrobC q k 1 • w).ord (R.residue₂ ⟨c • f, h⟩) : ℚ)
          + (dat.endOrderSnd a (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))) w : ℚ))) ≤ δ) ∧

      (δ = 0 → ∀ (c₁ : AlgebraicClosure ℚ) (h₁ : c₁ • f ∈ R.R₁.integers) (c₂ : AlgebraicClosure ℚ) (h₂ : c₂ • f ∈ R.R₂.integers),
        R.R₁.residue ⟨c₁ • f, h₁⟩ ≠ 0 → R.R₂.residue ⟨c₂ • f, h₂⟩ ≠ 0 →
        ∀ w ∈ W, (arithFrobC q k 1 • w).ord (R.residue₂ ⟨c₂ • f, h₂⟩) + dat.endOrderSnd a (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))) w = 0 →
          w.ord (R.residue₁ ⟨c₁ • f, h₁⟩) + dat.endOrderFst a (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))) w = 0 ∧
          ∀ V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)), P.reduceFst V = w → E V = 0) ∧

      (δ = 0 ↔ ∀ (c₁ : AlgebraicClosure ℚ) (h₁ : c₁ • f ∈ R.R₁.integers), R.R₁.residue ⟨c₁ • f, h₁⟩ ≠ 0 →
        ∃ h₂ : (c₁ * (q : AlgebraicClosure ℚ) ^ (a.aZ' - a.aZ)) • f ∈ R.R₂.integers,
          R.R₂.residue ⟨(c₁ * (q : AlgebraicClosure ℚ) ^ (a.aZ' - a.aZ)) • f, h₂⟩ ≠ 0) := by
  classical
  have hq1 : ¬ q ∣ 1 := fun h => (Fact.out : q.Prime).one_lt.ne' (Nat.dvd_one.mp h)
  have hq0 : ((q : ℕ) : AlgebraicClosure ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : q.Prime).ne_zero

  have hne₁ : ∀ (c : AlgebraicClosure ℚ) (h : c • f ∈ R.R₁.integers), R.R₁.residue ⟨c • f, h⟩ ≠ 0 → c ≠ 0 := by
    intro c h hr hc; subst hc; apply hr
    have : (⟨(0 : AlgebraicClosure ℚ) • f, h⟩ : R.R₁.integers) = 0 :=
      Subtype.ext (show ((0 : AlgebraicClosure ℚ) • f) = ((0 : R.R₁.integers) : ↥(modularFunctionFieldBar (1 * q))) by rw [zero_smul]; rfl)
    rw [this, map_zero]
  have hne₂ : ∀ (c : AlgebraicClosure ℚ) (h : c • f ∈ R.R₂.integers), R.R₂.residue ⟨c • f, h⟩ ≠ 0 → c ≠ 0 := by
    intro c h hr hc; subst hc; apply hr
    have : (⟨(0 : AlgebraicClosure ℚ) • f, h⟩ : R.R₂.integers) = 0 :=
      Subtype.ext (show ((0 : AlgebraicClosure ℚ) • f) = ((0 : R.R₂.integers) : ↥(modularFunctionFieldBar (1 * q))) by rw [zero_smul]; rfl)
    rw [this, map_zero]

  obtain ⟨c₁o, h₁o, hr₁o⟩ := R.R₁.exists_smul_mem f hf0
  obtain ⟨c₂o, h₂o, hr₂o⟩ := R.R₂.exists_smul_mem f hf0
  have hc₁o0 := hne₁ c₁o h₁o hr₁o
  have hc₂o0 := hne₂ c₂o h₂o hr₂o
  have hS₁ : ∀ c' : AlgebraicClosure ℚ,
      (∃ h : c' • f ∈ R.R₁.integers, R.R₁.residue ⟨c' • f, h⟩ ≠ 0) ↔ A.valuation c' = A.valuation c₁o := fun c' =>
    (ProlongationTuple.smul_mem_integers_and_residue_ne_zero_iff_valuation_eq R hR f hf0 c₁o h₁o hr₁o c').1
  have hS₂ : ∀ d' : AlgebraicClosure ℚ,
      (∃ h : d' • f ∈ R.R₂.integers, R.R₂.residue ⟨d' • f, h⟩ ≠ 0) ↔ A.valuation d' = A.valuation c₂o := fun d' =>
    (ProlongationTuple.smul_mem_integers_and_residue_ne_zero_iff_valuation_eq R hR f hf0 c₁o h₁o hr₁o c₁o).2 c₂o h₂o hr₂o d'

  obtain ⟨γ, e₀, n₀, hγ0, hγ1, he₀, hvq, hvc⟩ :=
    CasqLog.exists_valuation_eq_pow A red hker (c₁o * (c₂o)⁻¹) (mul_ne_zero hc₁o0 (inv_ne_zero hc₂o0))
  have hvqz : ∀ z : ℤ, A.valuation ((q : ℕ) : AlgebraicClosure ℚ) ^ z = γ ^ ((e₀ : ℤ) * z) := fun z => by
    rw [hvq, ← zpow_natCast, ← zpow_mul]

  have hrat : ∀ (c₁ : AlgebraicClosure ℚ) (h₁ : c₁ • f ∈ R.R₁.integers), R.R₁.residue ⟨c₁ • f, h₁⟩ ≠ 0 →
      ∀ (c₂ : AlgebraicClosure ℚ) (h₂ : c₂ • f ∈ R.R₂.integers), R.R₂.residue ⟨c₂ • f, h₂⟩ ≠ 0 →
        A.valuation (c₁ * c₂⁻¹) = γ ^ n₀ := by
    intro c₁ h₁ hr₁ c₂ h₂ hr₂
    rw [← hvc, map_mul, map_inv₀, map_mul, map_inv₀, (hS₁ c₁).mp ⟨h₁, hr₁⟩, (hS₂ c₂).mp ⟨h₂, hr₂⟩]

  obtain ⟨hintC, hintM⟩ := AnnulusDatumQ.den_circleDeg_eq_one_and_den_depthMoment_eq_one_of_inertiaStable hq5 P hW R hR hRL hNV hO
    dat hwidth hwidthj hVI hKfix hdepthQ hdepthσ D hDstab hDsupp

  have hordf : ∀ w ∈ W, ∀ V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)), P.reduceFst V = w →
      V.ord f = E V - (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))) V := by
    intro w hw V hV
    have hns := CvqNT.not_strict_of_reduceFst_mem P hW V hw hV
    have h1 : (∑ i, Finsupp.single (Q₁ i) (1 : ℤ)) V = 0 := by
      rw [Finsupp.finset_sum_apply]
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [Finsupp.single_apply, if_neg]
      rintro rfl; exact hns.1 (hQ₁ i)
    have h2 : (∑ j, Finsupp.single (Q₂ j) (1 : ℤ)) V = 0 := by
      rw [Finsupp.finset_sum_apply]
      refine Finset.sum_eq_zero fun j _ => ?_
      rw [Finsupp.single_apply, if_neg]
      rintro rfl; exact hns.2 (hQ₂ j)
    rw [← hdivf V, Finsupp.sub_apply, Finsupp.sub_apply, Finsupp.add_apply, h1, h2, add_zero, sub_zero]

  have hnode : ∀ w ∈ W, ∀ (c₁ : AlgebraicClosure ℚ) (h₁ : c₁ • f ∈ R.R₁.integers), R.R₁.residue ⟨c₁ • f, h₁⟩ ≠ 0 →
      ∀ (c₂ : AlgebraicClosure ℚ) (h₂ : c₂ • f ∈ R.R₂.integers), R.R₂.residue ⟨c₂ • f, h₂⟩ ≠ 0 →
      (n₀ + e₀ * (dat.depthMoment (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))) w).num ≤
          e₀ * (dat.width w * (w.ord (R.residue₁ ⟨c₁ • f, h₁⟩) +
            (dat.endOrderFst a (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))) w +
             dat.endOrderSnd a (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))) w)))) ∧
      (0 ≤ n₀ + e₀ * (dat.depthMoment (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))) w).num +
          e₀ * (dat.width w * (arithFrobC q k 1 • w).ord (R.residue₂ ⟨c₂ • f, h₂⟩))) ∧
      (n₀ + e₀ * (dat.depthMoment (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))) w).num +
          e₀ * (dat.width w * (arithFrobC q k 1 • w).ord (R.residue₂ ⟨c₂ • f, h₂⟩)) = 0 →
        (∀ V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)), P.reduceFst V = w → E V = 0) ∧
        w.ord (R.residue₁ ⟨c₁ • f, h₁⟩) +
          (dat.endOrderFst a (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))) w +
           dat.endOrderSnd a (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))) w) +
          (arithFrobC q k 1 • w).ord (R.residue₂ ⟨c₂ • f, h₂⟩) = 0) ∧
      ((dat.depthMoment (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))) w).num =
          dat.width w * dat.endOrderSnd a (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))) w + (a.aZ' - a.aZ)) := by
    intro w hw c₁ h₁ hr₁ c₂ h₂ hr₂

    set e : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) →₀ ℤ :=
      Finsupp.filter (fun V => P.reduceFst V = w ∧ ¬ P.IsStrictFst V ∧ ¬ P.IsStrictSnd V)
        (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))) with hedef
    have heV : ∀ V, e V = if (P.reduceFst V = w ∧ ¬ P.IsStrictFst V ∧ ¬ P.IsStrictSnd V) then
        (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))) V else 0 := fun V => by
      rw [hedef, Finsupp.filter_apply]
    set S := (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))).support.filter
      (fun V => P.reduceFst V = w ∧ ¬ P.IsStrictFst V ∧ ¬ P.IsStrictSnd V) with hSdef
    have hesupp : e.support = S := by rw [hedef, Finsupp.support_filter, hSdef]
    have hSw : ∀ V ∈ S, P.reduceFst V = w ∧ ¬ P.IsStrictFst V ∧ ¬ P.IsStrictSnd V := fun V hV => (Finset.mem_filter.mp hV).2
    have he' : ∀ V, e V ≠ 0 → P.reduceFst V = w ∧ ¬ P.IsStrictFst V ∧ ¬ P.IsStrictSnd V := by
      intro V hV
      by_contra hpV
      rw [heV, if_neg hpV] at hV
      exact hV rfl
    have hpole : ∀ V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)),
        P.reduceFst V = w → ¬ P.IsStrictFst V → ¬ P.IsStrictSnd V → 0 ≤ V.ord f + e V := by
      intro V hV hs1 hs2
      rw [hordf w hw V hV, heV, if_pos ⟨hV, hs1, hs2⟩]
      have hEV : 0 ≤ E V := by simpa using Finsupp.le_def.mp hE0 V
      linarith
    have hdep : ∀ V ∈ (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))).support, P.reduceFst V = w →
        ¬ P.IsStrictFst V → ¬ P.IsStrictSnd V → 0 ≤ dat.depthQ V ∧ dat.depthQ V ≤ dat.width w := fun V _ hh1 hh2 hh3 =>
      ⟨(hdepthQ w hw V hh1 hh2 hh3).1.le, by exact_mod_cast (hdepthQ w hw V hh1 hh2 hh3).2.1.le⟩

    haveI := hnoeth w hw
    obtain ⟨h1le, h2le, h3⟩ := ProlongationTuple.valuation_pow_le_mul_prod_and_rigid_of_twist_levelOne hq5 P hW R hR hRL hNV hO hker
      (dat.K w) w hw (hVI w hw) (ϖ w) (hϖ w hw) (eK w) (heK w hw) (ε w) (hε w hw) (hqϖ w hw) (dat.coord w hw) (dat.width w) (hwidth w hw)
      (u w hw) (hu w hw).1 (hu w hw).2 (hmax w hw) (hbr w hw) (hnoeth w hw) (hres w hw) f hf0 c₁ c₂ h₁ hr₁ h₂ hr₂ e he' hpole
    set Λp := ∏ V ∈ e.support, A.valuation (V.evalAt (((dat.coord w hw).y : ↥(modularFunctionFieldBar (1 * q))))) ^ e V with hΛpdef
    set dm := (dat.depthMoment (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))) w).num with hdmdef

    have hM : ∑ V ∈ e.support, e V =
        dat.endOrderFst a (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))) w +
          dat.endOrderSnd a (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))) w := by
      rw [hesupp, Finset.sum_congr rfl (fun V hV => by rw [heV, if_pos (hSw V hV)])]
      exact CvqOrbit.sum_annulus_eq_endOrders dat _ a ha hw (hwidth w hw) hdep (hintC w hw)

    have hΛ : Λp = A.valuation ((q : ℕ) : AlgebraicClosure ℚ) ^ dm := by
      rw [hΛpdef, hesupp, Finset.prod_congr rfl (fun V hV => by rw [heV, if_pos (hSw V hV)])]
      have hm : ∑ V ∈ S, (((D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))) V : ℤ) : ℚ) * dat.depthQ V = dm := by
        rw [hdmdef, Rat.coe_int_num_of_den_eq_one (hintM w hw)]
        unfold AnnulusDatumQ.depthMoment
        rw [hSdef]
      have hval := CvqAng.valuation_prod_mul_eq_one dat hw (hdepthQ w hw) S hSw
        (fun V => (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))) V) dm hm
      rw [map_mul, map_zpow₀, map_prod] at hval
      simp_rw [map_zpow₀, zpow_neg] at hval
      rw [Finset.prod_inv_distrib] at hval
      have hX0 : ∏ V ∈ S, A.valuation (V.evalAt (((dat.coord w hw).y : ↥(modularFunctionFieldBar (1 * q))))) ^
          ((D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))) V) ≠ 0 := by
        intro h0; rw [h0, inv_zero, zero_mul] at hval; exact zero_ne_one hval
      exact (inv_mul_eq_one₀ hX0).mp hval

    have hdw := CvqOrbit.depthMoment_eq dat (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))) a ha hw (hwidth w hw) hdep (hintC w hw)
    have hdm : dm = dat.width w * dat.endOrderSnd a (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))) w + (a.aZ' - a.aZ) := by
      rw [hdmdef, hdw, Rat.num_intCast]

    have hL : A.valuation ((q : ℕ) : AlgebraicClosure ℚ) ^
        ((dat.width w : ℤ) * (w.ord (R.residue₁ ⟨c₁ • f, h₁⟩) + ∑ V ∈ e.support, e V)) =
        γ ^ ((e₀ : ℤ) * ((dat.width w : ℤ) * (w.ord (R.residue₁ ⟨c₁ • f, h₁⟩) +
          (dat.endOrderFst a (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))) w +
           dat.endOrderSnd a (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))) w)))) := by
      rw [hM, hvqz]
    have hRt : A.valuation (c₁ * c₂⁻¹) * Λp = γ ^ (n₀ + e₀ * dm) := by
      rw [hΛ, hrat c₁ h₁ hr₁ c₂ h₂ hr₂, hvqz, ← zpow_add₀ hγ0]
    have h2form : A.valuation (c₁ * c₂⁻¹) * Λp *
        A.valuation ((q : ℕ) : AlgebraicClosure ℚ) ^ ((dat.width w : ℤ) * (arithFrobC q k 1 • w).ord (R.residue₂ ⟨c₂ • f, h₂⟩)) =
        γ ^ (n₀ + e₀ * dm + e₀ * (dat.width w * (arithFrobC q k 1 • w).ord (R.residue₂ ⟨c₂ • f, h₂⟩))) := by
      rw [hRt, hvqz, ← zpow_add₀ hγ0]
    rw [hL, hRt] at h1le
    rw [h2form] at h2le
    refine ⟨(CasqLog.zpow_le_zpow_iff_of_lt_one hγ0 hγ1 _ _).mp h1le, ?_, ?_, hdm⟩
    · exact (CasqLog.zpow_le_zpow_iff_of_lt_one hγ0 hγ1
        (n₀ + e₀ * dm + e₀ * (dat.width w * (arithFrobC q k 1 • w).ord (R.residue₂ ⟨c₂ • f, h₂⟩))) 0).mp
        (by rw [zpow_zero]; exact h2le)
    · intro hX
      obtain ⟨hzero, hsum⟩ := h3 (Or.inr (h2form.trans (by rw [hX, zpow_zero])))
      rw [hM] at hsum
      refine ⟨fun V hV => ?_, hsum⟩
      have hns := CvqNT.not_strict_of_reduceFst_mem P hW V hw hV
      have hz := hzero V hV hns.1 hns.2
      rw [hordf w hw V hV, heV, if_pos ⟨hV, hns.1, hns.2⟩] at hz
      linarith

  have he₀pos : (0 : ℚ) < e₀ := by exact_mod_cast he₀
  refine ⟨(n₀ : ℚ) / e₀ + ((a.aZ' - a.aZ : ℤ) : ℚ), ?_, ?_, ?_, ?_⟩
  ·
    intro c h hr w hw
    obtain ⟨hi, -, -, hdm⟩ := hnode w hw c h hr c₂o h₂o hr₂o
    rw [hdm] at hi
    have hi' : (n₀ : ℚ) + e₀ * (dat.width w * dat.endOrderSnd a (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))) w
        + (a.aZ' - a.aZ)) ≤ e₀ * (dat.width w * (w.ord (R.residue₁ ⟨c • f, h⟩) +
          (dat.endOrderFst a (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))) w +
           dat.endOrderSnd a (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))) w))) := by
      exact_mod_cast hi
    rw [div_add' _ _ _ he₀pos.ne', div_le_iff₀ he₀pos]
    push_cast
    nlinarith [hi', he₀pos]
  ·
    intro c h hr w hw
    obtain ⟨-, hii, -, hdm⟩ := hnode w hw c₁o h₁o hr₁o c h hr
    rw [hdm] at hii
    have hii' : (0 : ℚ) ≤ n₀ + e₀ * (dat.width w * dat.endOrderSnd a (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))) w
        + (a.aZ' - a.aZ)) + e₀ * (dat.width w * (arithFrobC q k 1 • w).ord (R.residue₂ ⟨c • f, h⟩)) := by
      exact_mod_cast hii
    rw [div_add' _ _ _ he₀pos.ne', le_div_iff₀ he₀pos]
    push_cast
    nlinarith [hii', he₀pos]
  ·
    intro hδ c₁ h₁ c₂ h₂ hr₁ hr₂ w hw hflat₂
    obtain ⟨-, -, hiii, hdm⟩ := hnode w hw c₁ h₁ hr₁ c₂ h₂ hr₂
    have hn₀ : n₀ + e₀ * (a.aZ' - a.aZ) = 0 := by
      rw [div_add' _ _ _ he₀pos.ne', div_eq_zero_iff] at hδ
      rcases hδ with h | h
      · have h' : ((n₀ + e₀ * (a.aZ' - a.aZ) : ℤ) : ℚ) = 0 := by push_cast at h ⊢; linarith
        exact_mod_cast h'
      · exact absurd h he₀pos.ne'
    have hX : n₀ + e₀ * (dat.depthMoment (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))) w).num +
        e₀ * (dat.width w * (arithFrobC q k 1 • w).ord (R.residue₂ ⟨c₂ • f, h₂⟩)) = 0 := by
      rw [hdm]
      have ho₂ : (arithFrobC q k 1 • w).ord (R.residue₂ ⟨c₂ • f, h₂⟩) =
          -dat.endOrderSnd a (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))) w := by linarith
      rw [ho₂]
      linear_combination hn₀
    obtain ⟨hE, hsum⟩ := hiii hX
    exact ⟨by linarith, hE⟩
  ·
    have hv₂0 : A.valuation c₂o ≠ 0 := (Valuation.ne_zero_iff _).mpr hc₂o0
    have hv₁o : A.valuation c₁o = γ ^ n₀ * A.valuation c₂o := by
      have h := hvc
      rw [map_mul, map_inv₀, ← div_eq_mul_inv, div_eq_iff hv₂0] at h
      exact h
    have hshift : ∀ (c₁ : AlgebraicClosure ℚ) (h₁ : c₁ • f ∈ R.R₁.integers), R.R₁.residue ⟨c₁ • f, h₁⟩ ≠ 0 →
        A.valuation (c₁ * (q : AlgebraicClosure ℚ) ^ (a.aZ' - a.aZ)) = γ ^ (n₀ + e₀ * (a.aZ' - a.aZ)) * A.valuation c₂o := by
      intro c₁ h₁ hr₁
      rw [map_mul, (hS₁ c₁).mp ⟨h₁, hr₁⟩, hv₁o, map_zpow₀]
      rw [hvqz (a.aZ' - a.aZ), zpow_add₀ hγ0]
      ac_rfl
    constructor
    · intro hδ c₁ h₁ hr₁
      have hn₀ : n₀ + e₀ * (a.aZ' - a.aZ) = 0 := by
        rw [div_add' _ _ _ he₀pos.ne', div_eq_zero_iff] at hδ
        rcases hδ with h | h
        · have h' : ((n₀ + e₀ * (a.aZ' - a.aZ) : ℤ) : ℚ) = 0 := by push_cast at h ⊢; linarith
          exact_mod_cast h'
        · exact absurd h he₀pos.ne'
      apply (hS₂ _).mpr
      rw [hshift c₁ h₁ hr₁, hn₀, zpow_zero, one_mul]
    · intro H
      obtain ⟨h₂, hr₂⟩ := H c₁o h₁o hr₁o
      have h := (hS₂ _).mp ⟨h₂, hr₂⟩
      rw [hshift c₁o h₁o hr₁o] at h
      have h1 : γ ^ (n₀ + e₀ * (a.aZ' - a.aZ)) = γ ^ (0 : ℤ) := by
        rw [zpow_zero]
        exact (mul_eq_right₀ hv₂0).mp h
      have hn₀ := (CasqLog.zpow_eq_zpow_iff_of_lt_one hγ0 hγ1 _ _).mp h1
      rw [div_add' _ _ _ he₀pos.ne', div_eq_zero_iff]
      left
      have : ((n₀ + e₀ * (a.aZ' - a.aZ) : ℤ) : ℚ) = 0 := by exact_mod_cast hn₀
      push_cast at this ⊢
      linarith

end S_ModularCurve_PlaceSpecialization_ProlongationTuple_AnnulusDatumQ_exists_chord_le_endOrders_and_rigid_of_isTwistOf_of_inertiaStable
end P2MW
export P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_AnnulusDatumQ_exists_chord_le_endOrders_and_rigid_of_isTwistOf_of_inertiaStable (solution)
