-- Prove2me | solution 1 for ModularCurve.PlaceSpecialization.ProlongationTuple.AnnulusDatumQ.exists_endOrder_ineq_and_coupledScalings_hasValue_of_isTwistOf_of_mk_spData_eq_zero_of_inertiaStable
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/0fa5d15f-0b8c-5f82-b2e8-1a66b64e92ec

import Mathlib
import Definitions.Def_ModularCurve_ProlongationTuple
import Definitions.Def_ModularCurve_LevelOneAnnulusSpecializationOrbit
import Definitions.Def_ModularCurve_JWidth
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_AnnulusDatumQ_exists_chord_le_endOrders_and_rigid_of_isTwistOf_of_inertiaStable
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_AnnulusDatumQ_den_circleDeg_eq_one_and_den_depthMoment_eq_one_of_inertiaStable
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_hasValue_residueFst_div_pow_and_residueSnd_div_pow_and_div_eq_angFactor_of_inertiaStable
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_AnnulusDatum_exists_nodePackage_over
import Theorems.Thm_ModularCurve_PlaceSpecialization_reduceFst_arithmeticGalois_smul
import Theorems.Thm_ModularCurve_arithFrobC_smul_mem_ssPlaces_univ
import Theorems.Thm_ModularCurve_NodeLocalized_isDiscreteValuationRing_coeffSubring
import Theorems.Thm_ModularCurve_isCurveOver_modularFunctionFieldC_of_perfectField
import Theorems.Thm_ModularCurve_arithFrobC_smul_arithFrobC_smul_eq_self_of_mem_ssPlaces
import Theorems.Thm_ModularCurve_arithFrobC_smul_eq_frobOnPlacesGeomLevel
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_AnnulusDatumQ_exists_endOrder_ineq_and_coupledScalings_hasValue_of_isTwistOf_of_mk_spData_eq_zero_of_inertiaStable
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

p2m_open "AlgebraicCurve P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_AnnulusDatumQ_exists_endOrder_ineq_and_coupledScalings_hasValue_of_isTwistOf_of_mk_spData_eq_zero_of_inertiaStable.AlgebraicCurve ModularCurve ModularCurve.PlaceSpecialization"

namespace CvqNT
p2m_open "AlgebraicCurve P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_AnnulusDatumQ_exists_endOrder_ineq_and_coupledScalings_hasValue_of_isTwistOf_of_mk_spData_eq_zero_of_inertiaStable.AlgebraicCurve IsLocalRing ModularCurve ModularCurve.NodeLocalized ModularCurve.PlaceSpecialization ModularCurve.PlaceSpecialization.ProlongationTuple"
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
p2m_open "AlgebraicCurve P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_AnnulusDatumQ_exists_endOrder_ineq_and_coupledScalings_hasValue_of_isTwistOf_of_mk_spData_eq_zero_of_inertiaStable.AlgebraicCurve ModularCurve ModularCurve.PlaceSpecialization ModularCurve.PlaceSpecialization.ProlongationTuple"
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

namespace CvqPkg
p2m_open "AlgebraicCurve P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_AnnulusDatumQ_exists_endOrder_ineq_and_coupledScalings_hasValue_of_isTwistOf_of_mk_spData_eq_zero_of_inertiaStable.AlgebraicCurve IsLocalRing ModularCurve ModularCurve.NodeLocalized ModularCurve.PlaceSpecialization ModularCurve.PlaceSpecialization.ProlongationTuple"

local notation "Qb" => AlgebraicClosure ℚ

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

end CvqPkg

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
p2m_open "AlgebraicCurve P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_AnnulusDatumQ_exists_endOrder_ineq_and_coupledScalings_hasValue_of_isTwistOf_of_mk_spData_eq_zero_of_inertiaStable.AlgebraicCurve IsLocalRing ModularCurve ModularCurve.NodeLocalized ModularCurve.PlaceSpecialization ModularCurve.PlaceSpecialization.ProlongationTuple"
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
p2m_open "AlgebraicCurve P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_AnnulusDatumQ_exists_endOrder_ineq_and_coupledScalings_hasValue_of_isTwistOf_of_mk_spData_eq_zero_of_inertiaStable.AlgebraicCurve ModularCurve ModularCurve.PlaceSpecialization ModularCurve.PlaceSpecialization.ProlongationTuple"

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

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place.HasValue GluingData GluingData.admissible GluedPic0 GluedPic0.mk Place Place.ord_zero Divisor Divisor.degZero SemilinearAut SemilinearAut.divisor_smul_apply_smul IsCurveOver IsCurveOver.finiteResidue Place.evalAt_ne_zero"
namespace Place
p2m_export "AlgebraicCurve.Place" "HasValue hasValue_one ext ResidueField ord ord_zero toValuationSubring mk mem_of_ord_nonneg IsRational evalAt algebraMap_evalAt evalAt_ne_zero"
p2m_open "AlgebraicCurve.Place AlgebraicCurve"

open Classical

set_option autoImplicit false

variable {K F : Type*} [Field K] [Field F] [Algebra K F] {v : Place K F}

namespace HasValue p2m_export "AlgebraicCurve.Place.HasValue" "mul ne_zero inv" end HasValue
namespace HasValue
p2m_open_scoped "AlgebraicCurve.Place.HasValue" in
private theorem _root_.AlgebraicCurve.Place.HasValue.pow' {g : F} {a : K} (h : v.HasValue g a) (n : ℕ) : v.HasValue (g ^ n) (a ^ n) := by
  induction n with
  | zero => simpa using v.hasValue_one
  | succ n ih => rw [pow_succ, pow_succ]; exact ih.mul h

end HasValue
p2m_export "AlgebraicCurve.Place" "HasValue.pow'"
namespace HasValue
p2m_open_scoped "AlgebraicCurve.Place.HasValue" in
private theorem _root_.AlgebraicCurve.Place.HasValue.zpow' {g : F} {a : K} (h : v.HasValue g a) (ha : a ≠ 0) (n : ℤ) : v.HasValue (g ^ n) (a ^ n) := by
  rcases n with (n | n)
  · simpa using h.pow' n
  · rw [zpow_negSucc, zpow_negSucc]
    exact (h.pow' (n + 1)).inv (pow_ne_zero _ ha)

end HasValue
p2m_export "AlgebraicCurve.Place" "HasValue.zpow'"
p2m_open_scoped "AlgebraicCurve.Place.HasValue" in
theorem HasValue.prod' {ι : Type*} (s : Finset ι) {g : ι → F} {a : ι → K}
    (h : ∀ i ∈ s, v.HasValue (g i) (a i)) : v.HasValue (∏ i ∈ s, g i) (∏ i ∈ s, a i) := by
  induction s using Finset.induction_on with
  | empty => simpa using v.hasValue_one
  | insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.prod_insert hi]
    exact (h i (Finset.mem_insert_self i s)).mul (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

p2m_open_scoped "AlgebraicCurve.Place.HasValue" in
theorem HasValue.prod_zpow' {ι : Type*} (s : Finset ι) {g : ι → F} {a : ι → K} (n : ι → ℤ)
    (h : ∀ i ∈ s, v.HasValue (g i) (a i)) (ha : ∀ i ∈ s, a i ≠ 0) :
    v.HasValue (∏ i ∈ s, g i ^ n i) (∏ i ∈ s, a i ^ n i) :=
  HasValue.prod' s fun i hi => (h i hi).zpow' (ha i hi) (n i)

end AlgebraicCurve.Place

namespace CvqBeta

p2m_open "AlgebraicCurve P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_AnnulusDatumQ_exists_endOrder_ineq_and_coupledScalings_hasValue_of_isTwistOf_of_mk_spData_eq_zero_of_inertiaStable.AlgebraicCurve"
open Classical

set_option autoImplicit false

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem prod_zpow_eq_mul_prod_erase (W : Finset (Place K F)) (π : Place K F → F) (n : Place K F → ℤ)
    (w : Place K F) (hw : w ∈ W) :
    ∏ w' ∈ W, π w' ^ n w' = π w ^ n w * ∏ w' ∈ W.erase w, π w' ^ n w' := by
  rw [← Finset.mul_prod_erase W (fun w' => π w' ^ n w') hw]

theorem hasValue_corrected_of_flat (v : Place K F) (W : Finset (Place K F)) (w : Place K F) (hw : w ∈ W)
    (ρ g ybar : F) (π : Place K F → F) (n : Place K F → ℤ) (o : ℤ)
    (hybar : ybar ≠ 0) (hπw : π w ≠ 0)
    (α lam c : K) (cross : Place K F → K)
    (hα : v.HasValue (ρ / ybar ^ o) α) (hlam : v.HasValue (ybar / π w) lam) (hlam0 : lam ≠ 0)
    (hg : v.HasValue g c)
    (hcross : ∀ w' ∈ W.erase w, v.HasValue (π w') (cross w')) (hcross0 : ∀ w' ∈ W.erase w, cross w' ≠ 0)
    (hflat : o + n w = 0) :
    v.HasValue (ρ * g * ∏ w' ∈ W, π w' ^ n w') (α * lam ^ o * c * ∏ w' ∈ W.erase w, cross w' ^ n w') := by

  have hρ : ρ = (ρ / ybar ^ o) * (ybar / π w) ^ o * π w ^ o := by
    rw [div_zpow]
    field_simp
  have hnw : n w = -o := by omega
  rw [prod_zpow_eq_mul_prod_erase W π n w hw, hnw, hρ]
  have key : (ρ / ybar ^ o) * (ybar / π w) ^ o * π w ^ o * g * (π w ^ (-o) * ∏ w' ∈ W.erase w, π w' ^ n w')
      = (ρ / ybar ^ o) * (ybar / π w) ^ o * g * ∏ w' ∈ W.erase w, π w' ^ n w' := by
    rw [zpow_neg]
    field_simp
  rw [key]
  exact ((hα.mul (hlam.zpow' hlam0 o)).mul hg).mul (Place.HasValue.prod_zpow' (W.erase w) n hcross hcross0)

end CvqBeta

namespace CvqO4

p2m_open "AlgebraicCurve P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_AnnulusDatumQ_exists_endOrder_ineq_and_coupledScalings_hasValue_of_isTwistOf_of_mk_spData_eq_zero_of_inertiaStable.AlgebraicCurve ModularCurve"
open Classical

set_option autoImplicit false

section Unif
variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem ne_zero_of_ord_ne_zero {v : Place K F} {g : F} (h : v.ord g ≠ 0) : g ≠ 0 := by
  rintro rfl; exact h (Place.ord_zero v)

theorem prod_zpow_ne_zero (W : Finset (Place K F)) (f : Place K F → F) (n : Place K F → ℤ)
    (hf : ∀ w ∈ W, f w ≠ 0) : ∏ w ∈ W, f w ^ n w ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun w hw => zpow_ne_zero _ (hf w hw)

theorem unifFst_facts (W : Finset (Place K F)) (cusp : Place K F) (hcusp : cusp ∉ W)
    (π : Place K F → F)
    (hunif : ∀ w' ∈ W, ∀ v : Place K F,
      v.ord (π w') = (Finsupp.single w' 1 - Finsupp.single cusp 1 : Place K F →₀ ℤ) v) :
    (∀ w' ∈ W, π w' ≠ 0) ∧
    (∀ w ∈ W, ∀ w' ∈ W, w.ord (π w') = if w' = w then 1 else 0) := by
  refine ⟨fun w' hw' => ne_zero_of_ord_ne_zero (v := w') ?_, fun w hw w' hw' => ?_⟩
  · rw [hunif w' hw' w', Finsupp.sub_apply, Finsupp.single_apply, Finsupp.single_apply, if_pos rfl,
      if_neg (fun h : cusp = w' => hcusp (by rw [h]; exact hw'))]
    norm_num
  · rw [hunif w' hw' w, Finsupp.sub_apply, Finsupp.single_apply, Finsupp.single_apply,
      if_neg (fun h : cusp = w => hcusp (by rw [h]; exact hw))]
    simp

theorem unifSnd_facts (W : Finset (Place K F)) (cusp : Place K F) (hcusp : cusp ∉ W)
    (φ : Place K F → Place K F) (hφ : Function.Injective φ) (hφcusp : φ cusp = cusp)
    (π' : Place K F → F)
    (hunif : ∀ w' ∈ W, ∀ v : Place K F,
      v.ord (π' w') = (Finsupp.single (φ w') 1 - Finsupp.single cusp 1 : Place K F →₀ ℤ) v) :
    (∀ w' ∈ W, π' w' ≠ 0) ∧
    (∀ w ∈ W, ∀ w' ∈ W, (φ w).ord (π' w') = if w' = w then 1 else 0) := by
  have hne : ∀ w ∈ W, cusp ≠ φ w := by
    intro w hw h
    have : φ cusp = φ w := by rw [hφcusp]; exact h
    exact hcusp (hφ this ▸ hw)
  refine ⟨fun w' hw' => ne_zero_of_ord_ne_zero (v := φ w') ?_, fun w hw w' hw' => ?_⟩
  · rw [hunif w' hw' (φ w'), Finsupp.sub_apply, Finsupp.single_apply, Finsupp.single_apply, if_pos rfl,
      if_neg (hne w' hw')]
    norm_num
  · rw [hunif w' hw' (φ w), Finsupp.sub_apply, Finsupp.single_apply, Finsupp.single_apply, if_neg (hne w hw)]
    by_cases h : w' = w
    · subst h; simp
    · rw [if_neg (fun h' => h (hφ h')), if_neg h]; simp

end Unif

end CvqO4

namespace CvqChild

p2m_open "AlgebraicCurve P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_AnnulusDatumQ_exists_endOrder_ineq_and_coupledScalings_hasValue_of_isTwistOf_of_mk_spData_eq_zero_of_inertiaStable.AlgebraicCurve ModularCurve ModularCurve.PlaceSpecialization ModularCurve.PlaceSpecialization.ProlongationTuple"
open Classical

set_option autoImplicit false

theorem surjective_algebraMap_residueField {K F : Type*} [Field K] [Field F] [Algebra K F] [IsAlgClosed K] [IsCurveOver K F]
    (v : Place K F) : Function.Surjective (algebraMap K v.ResidueField) := by
  haveI : Module.Finite K v.ResidueField := IsCurveOver.finiteResidue v
  haveI : Algebra.IsIntegral K v.ResidueField := Algebra.IsIntegral.of_finite K v.ResidueField
  exact (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := K) (K := v.ResidueField)).2

end CvqChild

namespace CvqKey

set_option autoImplicit false

theorem zpow_exponent_eq_zero_of_isUnit {L : Type*} [Field L] (S : Subring L) (p : ↥S) (hp : ¬ IsUnit p) (hp0 : (p : L) ≠ 0)
    (z : ↥S) (hz : IsUnit z) (n : ℤ) (h : (z : L) = (p : L) ^ n) : n = 0 := by
  by_contra hn
  obtain ⟨m, hm | hm⟩ := Int.eq_nat_or_neg n
  ·
    have hm0 : m ≠ 0 := by rintro rfl; simp at hm; exact hn hm
    have hzS : z = p ^ m := Subtype.ext (by rw [h, hm, zpow_natCast]; rfl)
    apply hp
    rw [hzS] at hz
    exact (isUnit_pow_iff hm0).mp hz
  ·
    have hm0 : m ≠ 0 := by rintro rfl; simp at hm; exact hn hm
    have hzS : z * p ^ m = 1 := Subtype.ext (by
      push_cast
      rw [h, hm, zpow_neg, zpow_natCast, inv_mul_cancel₀ (pow_ne_zero _ hp0)])
    apply hp
    have hu : IsUnit (p ^ m) := IsUnit.of_mul_eq_one _ (by rw [mul_comm]; exact hzS)
    exact (isUnit_pow_iff hm0).mp hu

theorem unitPart_eq_of_coupled {L : Type*} [Field L] (S : Subring L) (p e y₁ y₂ : ↥S)
    (hp : ¬ IsUnit p) (hp0 : (p : L) ≠ 0) (he : IsUnit e) (hy₁ : IsUnit y₁) (hy₂ : IsUnit y₂)
    (Q : L) (N : ℕ) (hQ : Q = (p : L) ^ N * (e : L))
    (c₁ c₂ : L) (m₁ m₂ j : ℤ)
    (hc₁ : c₁ = (p : L) ^ m₁ * (y₁ : L)) (hc₂ : c₂ = (p : L) ^ m₂ * (y₂ : L)) (hcouple : c₂ = c₁ * Q ^ j) :
    (y₂ : L) = (y₁ : L) * (e : L) ^ j := by
  have hne : ∀ w : ↥S, IsUnit w → (w : L) ≠ 0 := fun w hw h0 => hw.ne_zero (Subtype.ext h0)
  have he0 := hne e he
  have hy₁0 := hne y₁ hy₁
  obtain ⟨ue, hue⟩ := he
  obtain ⟨u₁, hu₁⟩ := hy₁
  obtain ⟨u₂, hu₂⟩ := hy₂

  set z : ↥S := ↑(u₂ * u₁⁻¹ * (ue ^ j)⁻¹) with hz
  have hzval : (z : L) = (y₂ : L) * (y₁ : L)⁻¹ * ((e : L) ^ j)⁻¹ := by
    have : (z : L) = ((Units.map (S.subtype : ↥S →* L) (u₂ * u₁⁻¹ * (ue ^ j)⁻¹) : Lˣ) : L) := by
      rw [Units.coe_map, hz]; rfl
    rw [this, map_mul, map_mul, map_inv, map_inv, map_zpow, Units.val_mul, Units.val_mul, Units.val_inv_eq_inv_val,
      Units.val_inv_eq_inv_val, Units.val_zpow_eq_zpow_val, Units.coe_map, Units.coe_map, Units.coe_map,
      MonoidHom.coe_coe, Subring.coe_subtype, hu₁, hu₂, hue]
  have hp0' := hp0
  have key : (z : L) = (p : L) ^ (m₁ + (N : ℤ) * j - m₂) := by
    rw [hzval]
    have h : (p : L) ^ m₂ * (y₂ : L) = (p : L) ^ m₁ * (y₁ : L) * ((p : L) ^ N * (e : L)) ^ j := by
      rw [← hc₂, ← hQ, ← hc₁]; exact hcouple
    rw [mul_zpow, ← zpow_natCast, ← zpow_mul] at h
    rw [zpow_sub₀ hp0, zpow_add₀ hp0]
    field_simp
    linear_combination h
  have hexp := zpow_exponent_eq_zero_of_isUnit S p hp hp0 z ⟨_, rfl⟩ _ key
  have h1 : (z : L) = 1 := by rw [key, hexp, zpow_zero]
  rw [hzval] at h1
  field_simp at h1
  linear_combination h1

end CvqKey

namespace CvqKey

set_option autoImplicit false

theorem map_unitPart_eq_of_coupled {L : Type*} [Field L] (S : Subring L) (p e y₁ y₂ : ↥S)
    (hp : ¬ IsUnit p) (hp0 : (p : L) ≠ 0) (he : IsUnit e) (hy₁ : IsUnit y₁) (hy₂ : IsUnit y₂)
    (Q : L) (N : ℕ) (hQ : Q = (p : L) ^ N * (e : L))
    (c₁ c₂ : L) (m₁ m₂ j : ℤ)
    (hc₁ : c₁ = (p : L) ^ m₁ * (y₁ : L)) (hc₂ : c₂ = (p : L) ^ m₂ * (y₂ : L)) (hcouple : c₂ = c₁ * Q ^ j)
    {k : Type*} [Field k] (φ : ↥S →+* k) :
    φ y₂ = φ y₁ * φ e ^ j := by
  have hL := unitPart_eq_of_coupled S p e y₁ y₂ hp hp0 he hy₁ hy₂ Q N hQ c₁ c₂ m₁ m₂ j hc₁ hc₂ hcouple
  obtain ⟨ue, hue⟩ := he

  have hS : y₂ = y₁ * ↑(ue ^ j) := by
    apply Subtype.ext
    change (y₂ : L) = (y₁ : L) * ((↑(ue ^ j) : ↥S) : L)
    rw [hL]
    congr 1
    have : ((↑(ue ^ j) : ↥S) : L) = ((Units.map (S.subtype : ↥S →* L) (ue ^ j) : Lˣ) : L) := by
      rw [Units.coe_map]; rfl
    rw [this, map_zpow, Units.val_zpow_eq_zpow_val, Units.coe_map, MonoidHom.coe_coe, Subring.coe_subtype, hue]
  rw [hS, map_mul]
  congr 1
  have : φ (↑(ue ^ j) : ↥S) = ((Units.map (φ : ↥S →* k) (ue ^ j) : kˣ) : k) := by rw [Units.coe_map]; rfl
  rw [this, map_zpow, Units.val_zpow_eq_zpow_val, Units.coe_map, MonoidHom.coe_coe, hue]

end CvqKey

namespace CvqChildKey
p2m_open "AlgebraicCurve P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_AnnulusDatumQ_exists_endOrder_ineq_and_coupledScalings_hasValue_of_isTwistOf_of_mk_spData_eq_zero_of_inertiaStable.AlgebraicCurve IsLocalRing ModularCurve ModularCurve.NodeLocalized ModularCurve.PlaceSpecialization ModularCurve.PlaceSpecialization.ProlongationTuple"
open Classical

set_option maxHeartbeats 32000000 in

theorem nodeTel_at
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
    (c₁ : AlgebraicClosure ℚ) (h₁ : c₁ • f ∈ R.R₁.integers) (c₂ : AlgebraicClosure ℚ) (h₂ : c₂ • f ∈ R.R₂.integers)
    (hr₁ : R.R₁.residue ⟨c₁ • f, h₁⟩ ≠ 0) (hr₂ : R.R₂.residue ⟨c₂ • f, h₂⟩ ≠ 0)
    (g₁ g₂ : ↥(modularFunctionFieldC k 1))
    (av bv : ↥(nodePairsOfPlaces (arithFrobC q k 1) W) → kˣ)
    (hdivg₁ : ∀ v, (dat.spData a (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)))).1 v = v.ord g₁)
    (hdivg₂ : ∀ v, (dat.spData a (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)))).2.1 v = v.ord g₂)
    (hgvals : ∀ s : ↥(nodePairsOfPlaces (arithFrobC q k 1) W),
      (s : Place k ↥(modularFunctionFieldC k 1) × Place k ↥(modularFunctionFieldC k 1)).1.HasValue g₁ (av s) ∧
      (s : Place k ↥(modularFunctionFieldC k 1) × Place k ↥(modularFunctionFieldC k 1)).2.HasValue g₂ (bv s))
    (hgratio : (dat.spData a (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)))).2.2 = fun s => Additive.ofMul (av s / bv s))
    (w : Place k ↥(modularFunctionFieldC k 1)) (hw : w ∈ W)

    (hflat₁ : w.ord (R.residue₁ ⟨c₁ • f, h₁⟩) + dat.endOrderFst a (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))) w = 0)
    (hflat₂ : (arithFrobC q k 1 • w).ord (R.residue₂ ⟨c₂ • f, h₂⟩) + dat.endOrderSnd a (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))) w = 0)
    (hEw : ∀ V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)), P.reduceFst V = w → E V = 0)
    :
    ∃ (K' : IntermediateField ℚ (AlgebraicClosure ℚ)) (_ : dat.K w ≤ K') (_ : FiniteDimensional ℚ ↥K')
      (ϖ' : ↥(NodeLocalized.coeffSubring A K')) (r : ℕ) (ν ε' : ↥(NodeLocalized.coeffSubring A K'))
      (m₁ m₂ : ℤ) (η₁ η₂ : ↥(NodeLocalized.coeffSubring A K'))
      (ηbar₁ ηbar₂ εbar' u0' t α₁ α₂ Θ : kˣ),
      Irreducible ϖ' ∧ (∀ d : ↥(NodeLocalized.coeffSubring A K'), NodeLocalized.redRestrict red K' d = 0 ↔ ∃ d', d = ϖ' * d') ∧
      1 ≤ r ∧ IsUnit ν ∧ IsUnit η₁ ∧ IsUnit η₂ ∧
      ((q : ℕ) : ↥(NodeLocalized.coeffSubring A K')) = ϖ' ^ (r * eK w) * ε' ∧
      ((ϖ w : ↥(NodeLocalized.coeffSubring A (dat.K w))) : AlgebraicClosure ℚ) =
        ((ϖ' : ↥(NodeLocalized.coeffSubring A K')) : AlgebraicClosure ℚ) ^ r * ((ν : ↥(NodeLocalized.coeffSubring A K')) : AlgebraicClosure ℚ) ∧
      ((ε' : ↥(NodeLocalized.coeffSubring A K')) : AlgebraicClosure ℚ) =
        ((ν : ↥(NodeLocalized.coeffSubring A K')) : AlgebraicClosure ℚ) ^ eK w * ((ε w : ↥(NodeLocalized.coeffSubring A (dat.K w))) : AlgebraicClosure ℚ) ∧
      c₁ = ((ϖ' : ↥(NodeLocalized.coeffSubring A K')) : AlgebraicClosure ℚ) ^ m₁ * ((η₁ : ↥(NodeLocalized.coeffSubring A K')) : AlgebraicClosure ℚ) ∧
      c₂ = ((ϖ' : ↥(NodeLocalized.coeffSubring A K')) : AlgebraicClosure ℚ) ^ m₂ * ((η₂ : ↥(NodeLocalized.coeffSubring A K')) : AlgebraicClosure ℚ) ∧
      NodeLocalized.redRestrict red K' η₁ = (ηbar₁ : k) ∧ NodeLocalized.redRestrict red K' η₂ = (ηbar₂ : k) ∧
      NodeLocalized.redRestrict red K' ε' = (εbar' : k) ∧ NodeLocalized.redRestrict red K' ν = (t : k) ∧
      (εbar' : k) = (t : k) ^ (eK w) * NodeLocalized.redRestrict red (dat.K w) (ε w) ∧
      (u0' : k) = (dat.u0 w : k) * (t : k) ^ (dat.width w * eK w) ∧

      (∀ V ∈ (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))).support, P.reduceFst V = w →
        ¬ P.IsStrictFst V ∧ ¬ P.IsStrictSnd V) ∧

      (∀ V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)), P.reduceFst V = w →
        (E - (∑ i, Finsupp.single (Q₁ i) (1 : ℤ) + ∑ j, Finsupp.single (Q₂ j) (1 : ℤ))
          - (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)))) V =
          -((D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))) V)) ∧

      w.HasValue
        ((R.residue₁ ⟨c₁ • f, h₁⟩ : ↥(modularFunctionFieldC k 1)) /
          (R.nodeResidue₁ w ⟨((dat.coord w hw).y : ↥(modularFunctionFieldBar (1 * q))), (dat.coord w hw).y.2.1⟩ :
            ↥(modularFunctionFieldC k 1)) ^ (w.ord (R.residue₁ ⟨c₁ • f, h₁⟩)))
        (α₁ : k) ∧
      (arithFrobC q k 1 • w).HasValue
        ((R.residue₂ ⟨c₂ • f, h₂⟩ : ↥(modularFunctionFieldC k 1)) /
          (R.nodeResidue₂ w ⟨((dat.coord w hw).x : ↥(modularFunctionFieldBar (1 * q))), (dat.coord w hw).x.2.1⟩ :
            ↥(modularFunctionFieldC k 1)) ^ ((arithFrobC q k 1 • w).ord (R.residue₂ ⟨c₂ • f, h₂⟩)))
        (α₂ : k) ∧
      α₁ / α₂ =
        (ηbar₁ / ηbar₂) *
        (-1 : kˣ) ^ (∑ V ∈ (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))).support with
            (P.reduceFst V = w ∧ ¬ P.IsStrictFst V ∧ ¬ P.IsStrictSnd V),
            -((D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))) V)) *
        u0' ^ ((arithFrobC q k 1 • w).ord (R.residue₂ ⟨c₂ • f, h₂⟩)) *
        εbar' ^ (-(-(dat.depthMoment (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))) w).num)) * Θ ∧

      Θ * dat.angFactor w hw (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))) = 1 ∧

      (dat.depthMoment (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))) w).den = 1 ∧
      (∀ d : ℕ, (dat.circleDeg (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))) w d).den = 1) ∧

      (∀ V ∈ (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))).support, P.reduceFst V = w →
        ¬ P.IsStrictFst V → ¬ P.IsStrictSnd V → 0 ≤ dat.depthQ V ∧ dat.depthQ V ≤ dat.width w) ∧
      IsUnit ε' := by
  classical
  have hq1 : ¬ q ∣ 1 := fun h => (Fact.out : q.Prime).one_lt.ne' (Nat.dvd_one.mp h)
  have hW' : ∀ v ∈ W, v ∈ ssPlaces q 1 k := fun v hv => (hW v).mp hv

  have hc₁0 : c₁ ≠ 0 := by
    rintro rfl; apply hr₁
    have : (⟨(0 : AlgebraicClosure ℚ) • f, h₁⟩ : R.R₁.integers) = 0 :=
      Subtype.ext (show ((0 : AlgebraicClosure ℚ) • f) = ((0 : R.R₁.integers) : ↥(modularFunctionFieldBar (1 * q))) by rw [zero_smul]; rfl)
    rw [this, map_zero]
  have hc₂0 : c₂ ≠ 0 := by
    rintro rfl; apply hr₂
    have : (⟨(0 : AlgebraicClosure ℚ) • f, h₂⟩ : R.R₂.integers) = 0 :=
      Subtype.ext (show ((0 : AlgebraicClosure ℚ) • f) = ((0 : R.R₂.integers) : ↥(modularFunctionFieldBar (1 * q))) by rw [zero_smul]; rfl)
    rw [this, map_zero]

  obtain ⟨K', hKK', hfd', hBB', ϖ', hϖ', eK', heK', ε', hε', hqϖ', u', hu', hxy', hmaxK, hloc, hnoe, hmax', hbr', hres',
    hfK, hfrac, hc₁K, hc₂K, m₁, m₂, η₁, η₂, hη₁, hη₂, hc₁η, hc₂η, u0', t, εbar', hu0', hu0rel, hεbar', hp1, r, ν, hν,
    heK'r, hfacQ, hεQ, ht⟩ :=
    AnnulusDatum.exists_nodePackage_over P hW R hR hRL hNV (CvqOrbit.toAnnulusDatum dat) hwidth ϖ hϖ eK heK ε hε hqϖ u hu
      hmax hbr hnoeth hres hu0 hker hq5 w hw f hf0 c₁ c₂ hc₁0 hc₂0
  haveI := hfd'
  haveI := hloc
  haveI := hnoe

  haveI hdvr : IsDiscreteValuationRing ↥(NodeLocalized.coeffSubring A K') :=
    ModularCurve.NodeLocalized.isDiscreteValuationRing_coeffSubring red hker K'
  have hne0 : ∀ z : ↥(NodeLocalized.coeffSubring A K'), IsUnit z → NodeLocalized.redRestrict red K' z ≠ 0 := fun z hz h0 =>
    ((CvqPkg.redRestrict_eq_zero_iff_not_isUnit A red hker K' z).mp h0) hz
  have hirr : Irreducible ϖ' := by
    rw [IsDiscreteValuationRing.irreducible_iff_uniformizer]
    ext d
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, ← CvqPkg.redRestrict_eq_zero_iff_not_isUnit A red hker K' d, hϖ' d,
      Ideal.mem_span_singleton]
    exact ⟨fun ⟨d', h⟩ => ⟨d', h⟩, fun ⟨d', h⟩ => ⟨d', h⟩⟩
  have hr1 : 1 ≤ r := by
    rcases Nat.eq_zero_or_pos r with h0 | h
    · rw [h0, zero_mul] at heK'r; omega
    · exact h

  set Df : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) :=
    E - (∑ i, Finsupp.single (Q₁ i) (1 : ℤ) + ∑ j, Finsupp.single (Q₂ j) (1 : ℤ))
      - (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))) with hDfdef
  have hneg : ∀ V, P.reduceFst V = w → Df V = -((D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))) V) :=
    fun V hV => CvqNT.divf_eq_neg_over P hW Q₁ Q₂ hQ₁ hQ₂ E _ hw hEw V hV
  have hsuppw : ∀ V, P.reduceFst V = w →
      (V ∈ Df.support ↔ V ∈ (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))).support) := by
    intro V hV
    rw [Finsupp.mem_support_iff, Finsupp.mem_support_iff, hneg V hV, neg_ne_zero]
  have hnostrict : ∀ V ∈ (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))).support, P.reduceFst V = w →
      ¬ P.IsStrictFst V ∧ ¬ P.IsStrictSnd V := fun V _ hVw => CvqNT.not_strict_of_reduceFst_mem P hW V hw hVw
  have hdep : ∀ V ∈ (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))).support, P.reduceFst V = w →
      ¬ P.IsStrictFst V → ¬ P.IsStrictSnd V → 0 ≤ dat.depthQ V ∧ dat.depthQ V ≤ dat.width w := fun V _ h1 h2 h3 =>
    ⟨(hdepthQ w hw V h1 h2 h3).1.le, by exact_mod_cast (hdepthQ w hw V h1 h2 h3).2.1.le⟩

  obtain ⟨hintC, hintM⟩ := AnnulusDatumQ.den_circleDeg_eq_one_and_den_depthMoment_eq_one_of_inertiaStable hq5 P hW R hR hRL hNV hO
    dat hwidth hwidthj hVI hKfix hdepthQ hdepthσ D hDstab hDsupp

  set S := (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))).support.filter
    (fun V => P.reduceFst V = w ∧ ¬ P.IsStrictFst V ∧ ¬ P.IsStrictSnd V) with hSdef
  have hfilt : Df.support.filter (fun V => P.reduceFst V = w ∧ ¬ P.IsStrictFst V ∧ ¬ P.IsStrictSnd V) = S := by
    ext V
    simp only [hSdef, Finset.mem_filter]
    constructor
    · rintro ⟨h, hw', hns⟩; exact ⟨(hsuppw V hw').mp h, hw', hns⟩
    · rintro ⟨h, hw', hns⟩; exact ⟨(hsuppw V hw').mpr h, hw', hns⟩
  have hSw : ∀ V ∈ S, P.reduceFst V = w ∧ ¬ P.IsStrictFst V ∧ ¬ P.IsStrictSnd V := fun V hV => (Finset.mem_filter.mp hV).2

  have hsumD : ∑ V ∈ S, (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))) V =
      dat.endOrderFst a (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))) w +
        dat.endOrderSnd a (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))) w :=
    CvqOrbit.sum_annulus_eq_endOrders dat _ a ha hw (hwidth w hw) hdep (hintC w hw)
  have hN : (∑ V ∈ Df.support with (P.reduceFst V = w ∧ ¬ P.IsStrictFst V ∧ ¬ P.IsStrictSnd V), Df V) =
      w.ord (R.residue₁ ⟨c₁ • f, h₁⟩) + (arithFrobC q k 1 • w).ord (R.residue₂ ⟨c₂ • f, h₂⟩) := by
    rw [hfilt, Finset.sum_congr rfl (fun V hV => hneg V (hSw V hV).1), Finset.sum_neg_distrib, hsumD]
    linarith

  have hstab : ∀ σ ∈ A.inertiaSubgroupIn ℚ, ∀ V ∈ Df.support, P.reduceFst V = w →
      Df (arithmeticGalois (modularFunctionFieldFull (1 * q)) σ • V) = Df V := by
    intro σ hσ V _ hVw
    have hσw : P.reduceFst (arithmeticGalois (modularFunctionFieldFull (1 * q)) σ • V) = w := by
      rw [P.reduceFst_arithmeticGalois_smul σ hσ V]; exact hVw
    rw [hneg _ hσw, hneg _ hVw]
    congr 1
    calc (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))) (arithmeticGalois (modularFunctionFieldFull (1 * q)) σ • V)
        = (arithmeticGalois (modularFunctionFieldFull (1 * q)) σ • (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))))
            (arithmeticGalois (modularFunctionFieldFull (1 * q)) σ • V) := by rw [hDstab σ hσ]
      _ = (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))) V := SemilinearAut.divisor_smul_apply_smul _ _ _

  have hm' : (∑ V ∈ Df.support with (P.reduceFst V = w ∧ ¬ P.IsStrictFst V ∧ ¬ P.IsStrictSnd V), (Df V : ℚ) * dat.depthQ V) =
      ((-(dat.depthMoment (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))) w).num : ℤ) : ℚ) := by
    rw [hfilt, Finset.sum_congr rfl (fun V hV => show (Df V : ℚ) * dat.depthQ V =
        -(((D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))) V : ℚ) * dat.depthQ V) by
          rw [hneg V (hSw V hV).1]; push_cast; ring),
      Finset.sum_neg_distrib, Int.cast_neg, Rat.coe_int_num_of_den_eq_one (hintM w hw)]
    unfold AnnulusDatumQ.depthMoment
    rw [hSdef]

  obtain ⟨hmemΘ, hΘ0⟩ := CvqAng.exists_mem_red_ne_zero dat hker hw (hdepthQ w hw) _
    (fun V hV => by rw [hfilt] at hV; exact hSw V hV) (fun V => Df V) _ hm'
  obtain ⟨hmemA, hA0, hAF⟩ := CvqAng.angFactor_spec dat hker hw (hdepthQ w hw)
    (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))) (hintM w hw)
  set Θ : kˣ := Units.mk0 _ hΘ0 with hΘdef
  have hy0 : ∀ V ∈ S, V.evalAt (((dat.coord w hw).y : ↥(modularFunctionFieldBar (1 * q)))) ≠ 0 := by
    intro V hV h0
    have h := (hdepthQ w hw V (hSw V hV).1 (hSw V hV).2.1 (hSw V hV).2.2).2.2
    have hq0 : ((q : ℕ) : AlgebraicClosure ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : q.Prime).ne_zero
    unfold NodeCoordinates.yDepth at h
    rw [h0, map_zero, zero_pow (dat.depthQ V).den_pos.ne'] at h
    exact pow_ne_zero _ ((Valuation.ne_zero_iff _).mpr hq0) h.symm
  have hΘAF : Θ * dat.angFactor w hw (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))) = 1 := by
    apply Units.ext
    rw [Units.val_mul, hΘdef, Units.val_mk0, hAF, Units.val_one, ← map_mul, ← map_one red]
    congr 1
    apply Subtype.ext
    rw [Subring.coe_mul]
    show ((∏ V ∈ Df.support with (P.reduceFst V = w ∧ ¬ P.IsStrictFst V ∧ ¬ P.IsStrictSnd V),
        V.evalAt (((dat.coord w hw).y : ↥(modularFunctionFieldBar (1 * q)))) ^ (-(Df V))) *
        ((q : ℕ) : AlgebraicClosure ℚ) ^ (-(dat.depthMoment (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))) w).num)) *
      ((∏ V ∈ S, V.evalAt (((dat.coord w hw).y : ↥(modularFunctionFieldBar (1 * q)))) ^
          (-((D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))) V))) *
        ((q : ℕ) : AlgebraicClosure ℚ) ^ (dat.depthMoment (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))) w).num) = 1
    have hq0 : ((q : ℕ) : AlgebraicClosure ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : q.Prime).ne_zero
    rw [hfilt, Finset.prod_congr rfl (fun V hV => show V.evalAt (((dat.coord w hw).y : ↥(modularFunctionFieldBar (1 * q)))) ^ (-(Df V)) =
        V.evalAt (((dat.coord w hw).y : ↥(modularFunctionFieldBar (1 * q)))) ^ ((D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))) V)
        by rw [hneg V (hSw V hV).1, neg_neg])]
    calc _ = (∏ V ∈ S, (V.evalAt (((dat.coord w hw).y : ↥(modularFunctionFieldBar (1 * q)))) ^ ((D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))) V) *
              V.evalAt (((dat.coord w hw).y : ↥(modularFunctionFieldBar (1 * q)))) ^ (-((D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))) V)))) *
            (((q : ℕ) : AlgebraicClosure ℚ) ^ (-(dat.depthMoment (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))) w).num) *
              ((q : ℕ) : AlgebraicClosure ℚ) ^ (dat.depthMoment (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))) w).num) := by
          rw [Finset.prod_mul_distrib]; ring
      _ = 1 := by
          rw [← zpow_add₀ hq0, neg_add_cancel, zpow_zero, mul_one]
          exact Finset.prod_eq_one fun V hV => by rw [← zpow_add₀ (hy0 V hV), add_neg_cancel, zpow_zero]

  have hwφ : arithFrobC q k 1 • w ∈ W :=
    (hW _).mpr (ModularCurve.arithFrobC_smul_mem_ssPlaces_univ q 1 k w (hW' w hw))

  obtain ⟨α₁, α₂, hv₁, hv₂, hratio⟩ :=
    exists_hasValue_residueFst_div_pow_and_residueSnd_div_pow_and_div_eq_angFactor_of_inertiaStable R hq1 hR hO W hW' hRL hNV
      (dat.K w) K' hKK' w hw hwφ (hVI w hw) hBB' ϖ' hϖ' eK' heK' ε' hε' hqϖ' (dat.coord w hw) (dat.width w) (hwidth w hw)
      u' hu' hxy' hmaxK hmax' hbr' hres' dat.depthQ
      (fun V h1 h2 h3 => ⟨(hdepthQ w hw V h1 h2 h3).1, (hdepthQ w hw V h1 h2 h3).2.2⟩)
      f hf0 hfK hfrac c₁ c₂ h₁ hr₁ h₂ hr₂ hc₁K hc₂K hc₁0 hc₂0
      Df hdivf hstab _ hm' hN m₁ m₂ η₁ η₂ hη₁ hη₂ hc₁η hc₂η
      (Units.mk0 _ (hne0 _ hη₁)) (Units.mk0 _ (hne0 _ hη₂)) εbar' u0' rfl rfl hεbar' hu0' Θ ⟨hmemΘ, rfl⟩

  rw [hfilt, Finset.sum_congr rfl (fun V hV => hneg V (hSw V hV).1)] at hratio
  refine ⟨K', hKK', hfd', ϖ', r, ν, ε', m₁, m₂, η₁, η₂, Units.mk0 _ (hne0 _ hη₁), Units.mk0 _ (hne0 _ hη₂), εbar', u0', t, α₁, α₂, Θ,
    hirr, hϖ', hr1, hν, hη₁, hη₂, heK'r ▸ hqϖ', hfacQ, hεQ, hc₁η, hc₂η, rfl, rfl, hεbar', ht, ?_, hu0rel,
    hnostrict, hneg, hv₁, hv₂, hratio, hΘAF, hintM w hw, hintC w hw, hdep, hε'⟩
  rw [← hεbar', hp1]

end CvqChildKey

namespace CvqKmain

open Finset

theorem key_of_ratio {k : Type*} [Field k] {ι κ : Type*} (S : Finset ι) (T : Finset κ)
    (Dv : ι → ℤ) (AF Θ : kˣ) (cr₁ cr₂ : κ → kˣ) (e₁ e₂ : κ → ℤ)
    (α₁ α₂ ηbar₁ ηbar₂ εbar' u0' t u0 lam mu av bv : kˣ) (o₁ o₂ n₁ n₂ j dm : ℤ) (width eK : ℕ)
    (hratio : α₁ / α₂ = (ηbar₁ / ηbar₂) * (-1) ^ (∑ V ∈ S, -Dv V) * u0' ^ o₂ * εbar' ^ (-(-dm)) * Θ)
    (hν : av / bv = (-1) ^ (∑ V ∈ S, Dv V) * u0 ^ n₂ * lam ^ n₁ * (mu ^ n₂)⁻¹ * AF *
        ∏ w' ∈ T, ((cr₁ w') ^ (e₁ w'))⁻¹ * (cr₂ w') ^ (e₂ w'))
    (hΘ : Θ * AF = 1)
    (hflat₁ : o₁ + n₁ = 0) (hflat₂ : o₂ + n₂ = 0)
    (hu0 : (u0' : k) = u0 * t ^ (width * eK)) (hε : (εbar' : k) = t ^ eK)
    (hη : (ηbar₂ : k) = ηbar₁ * εbar' ^ j)
    (hdw : dm = width * n₂ + j) :
    (α₁ : k) * (lam : k) ^ o₁ * (av : k) * ∏ w' ∈ T, (cr₁ w' : k) ^ (e₁ w') =
      (α₂ : k) * (mu : k) ^ o₂ * (bv : k) * ∏ w' ∈ T, (cr₂ w' : k) ^ (e₂ w') := by

  have hu0' : u0' = u0 * t ^ (width * eK) := Units.ext (by push_cast; exact hu0)
  have hε' : εbar' = t ^ eK := Units.ext (by push_cast; exact hε)
  have hη' : ηbar₂ = ηbar₁ * εbar' ^ j := Units.ext (by push_cast; exact hη)
  have ho₁ : o₁ = -n₁ := by omega
  have ho₂ : o₂ = -n₂ := by omega

  suffices H : α₁ * lam ^ o₁ * av * ∏ w' ∈ T, (cr₁ w') ^ (e₁ w') = α₂ * mu ^ o₂ * bv * ∏ w' ∈ T, (cr₂ w') ^ (e₂ w') by
    have := congrArg (fun u : kˣ => (u : k)) H
    push_cast at this
    exact this
  have hsum1 : (∑ V ∈ S, -Dv V) = -(∑ V ∈ S, Dv V) := by rw [Finset.sum_neg_distrib]
  have hT : (∏ w' ∈ T, ((cr₁ w') ^ (e₁ w'))⁻¹ * (cr₂ w') ^ (e₂ w')) * ∏ w' ∈ T, (cr₁ w') ^ (e₁ w') =
      ∏ w' ∈ T, (cr₂ w') ^ (e₂ w') := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun w' _ => ?_
    rw [mul_comm, ← mul_assoc, mul_inv_cancel, one_mul]
  have hsign : ((-1 : kˣ) ^ (-(∑ V ∈ S, Dv V))) * (-1) ^ (∑ V ∈ S, Dv V) = 1 := by
    rw [← zpow_add, neg_add_cancel, zpow_zero]
  have hlam : lam ^ (-n₁) * lam ^ n₁ = 1 := by rw [← zpow_add, neg_add_cancel, zpow_zero]

  have hres : (ηbar₁ / ηbar₂) * u0' ^ o₂ * εbar' ^ dm * u0 ^ n₂ = 1 := by
    rw [hη', hu0', hε', hdw, ho₂]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_div, ofMul_zpow, ofMul_pow, ofMul_one]
    module

  have hα : α₁ = α₂ * ((ηbar₁ / ηbar₂) * (-1) ^ (∑ V ∈ S, -Dv V) * u0' ^ o₂ * εbar' ^ (-(-dm)) * Θ) := by
    rw [← hratio, mul_div_cancel]
  have hav : av = bv * ((-1) ^ (∑ V ∈ S, Dv V) * u0 ^ n₂ * lam ^ n₁ * (mu ^ n₂)⁻¹ * AF *
      ∏ w' ∈ T, ((cr₁ w') ^ (e₁ w'))⁻¹ * (cr₂ w') ^ (e₂ w')) := by
    rw [← hν, mul_div_cancel]
  rw [hα, hav, hsum1, neg_neg, ho₁]

  set Rη := ηbar₁ / ηbar₂
  set Sgm := (-1 : kˣ) ^ (-(∑ V ∈ S, Dv V))
  set Sgp := (-1 : kˣ) ^ (∑ V ∈ S, Dv V)
  set U' := u0' ^ o₂
  set Eb := εbar' ^ dm
  set U0 := u0 ^ n₂
  set L := lam ^ n₁
  set Lm := lam ^ (-n₁)
  set M := mu ^ n₂
  set C := ∏ w' ∈ T, ((cr₁ w') ^ (e₁ w'))⁻¹ * (cr₂ w') ^ (e₂ w')
  set P₁ := ∏ w' ∈ T, (cr₁ w') ^ (e₁ w')
  set P₂ := ∏ w' ∈ T, (cr₂ w') ^ (e₂ w')
  have hM : mu ^ o₂ = M⁻¹ := by rw [ho₂, zpow_neg]
  calc α₂ * (Rη * Sgm * U' * Eb * Θ) * Lm * (bv * (Sgp * U0 * L * M⁻¹ * AF * C)) * P₁
      = α₂ * bv * M⁻¹ * (Rη * U' * Eb * U0) * (Sgm * Sgp) * (Θ * AF) * (Lm * L) * (C * P₁) := by ac_rfl
    _ = α₂ * bv * M⁻¹ * P₂ := by rw [hres, hsign, hΘ, hlam, hT]; simp only [mul_one]
    _ = α₂ * mu ^ o₂ * bv * P₂ := by rw [hM]; ac_rfl

end CvqKmain

namespace CvqChildKey
p2m_open "AlgebraicCurve P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_AnnulusDatumQ_exists_endOrder_ineq_and_coupledScalings_hasValue_of_isTwistOf_of_mk_spData_eq_zero_of_inertiaStable.AlgebraicCurve ModularCurve ModularCurve.PlaceSpecialization ModularCurve.PlaceSpecialization.ProlongationTuple"
open Classical
set_option autoImplicit false

set_option maxHeartbeats 32000000 in
theorem key_values
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
    (c₁ : AlgebraicClosure ℚ) (h₁ : c₁ • f ∈ R.R₁.integers) (c₂ : AlgebraicClosure ℚ) (h₂ : c₂ • f ∈ R.R₂.integers)
    (hr₁ : R.R₁.residue ⟨c₁ • f, h₁⟩ ≠ 0) (hr₂ : R.R₂.residue ⟨c₂ • f, h₂⟩ ≠ 0)
    (g₁ g₂ : ↥(modularFunctionFieldC k 1))
    (av bv : ↥(nodePairsOfPlaces (arithFrobC q k 1) W) → kˣ)
    (hdivg₁ : ∀ v, (dat.spData a (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)))).1 v = v.ord g₁)
    (hdivg₂ : ∀ v, (dat.spData a (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)))).2.1 v = v.ord g₂)
    (hgvals : ∀ s : ↥(nodePairsOfPlaces (arithFrobC q k 1) W),
      (s : Place k ↥(modularFunctionFieldC k 1) × Place k ↥(modularFunctionFieldC k 1)).1.HasValue g₁ (av s) ∧
      (s : Place k ↥(modularFunctionFieldC k 1) × Place k ↥(modularFunctionFieldC k 1)).2.HasValue g₂ (bv s))
    (hgratio : (dat.spData a (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)))).2.2 = fun s => Additive.ofMul (av s / bv s))
    (w : Place k ↥(modularFunctionFieldC k 1)) (hw : w ∈ W)

    (hflat₁ : w.ord (R.residue₁ ⟨c₁ • f, h₁⟩) + dat.endOrderFst a (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))) w = 0)
    (hflat₂ : (arithFrobC q k 1 • w).ord (R.residue₂ ⟨c₂ • f, h₂⟩) + dat.endOrderSnd a (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))) w = 0)
    (hEw : ∀ V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)), P.reduceFst V = w → E V = 0)

    (hcouple : c₂ = c₁ * ((q : ℕ) : AlgebraicClosure ℚ) ^ (a.aZ' - a.aZ)) :
    ∃ c : kˣ, w.HasValue (R.residue₁ ⟨c₁ • f, h₁⟩ * g₁ * ∏ w' ∈ W, dat.unifFst w' ^ dat.endOrderFst a (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))) w') (c : k) ∧
      (arithFrobC q k 1 • w).HasValue (R.residue₂ ⟨c₂ • f, h₂⟩ * g₂ * ∏ w' ∈ W, dat.unifSnd w' ^ dat.endOrderSnd a (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))) w') (c : k) := by
  classical
  haveI : IsCurveOver k ↥(modularFunctionFieldC k 1) := ModularCurve.isCurveOver_modularFunctionFieldC_of_perfectField k 1

  obtain ⟨K', hKK', hfd', ϖ', r, ν, ε', m₁, m₂, η₁, η₂, ηbar₁, ηbar₂, εbar', u0', t, α₁, α₂, Θ, hirr, hϖ', hr, hν, hη₁, hη₂,
    hqϖ', hfacQ, hεQ, hc₁η, hc₂η, hηbar₁, hηbar₂, hεbar', ht, hp1, hu0rel, hnostrict, hneg, hv₁, hv₂, hratio, hΘAF, hintM, hintC,
    hdep, hε'⟩ :=
    nodeTel_at hq5 P hW R hR hRL hNV hO dat hwidth hwidthj hdepthQ hdepthσ hcusp hcuspφ hunif hKfix ϖ hϖ eK heK ε hε hqϖ hε1 u hu hmax hbr hnoeth hres hVI hu0 hlam hmu D hDstab hDsupp a ha hadm hsp Q₁ Q₂ hQ₁ hQ₂ E hE0 f hf0 hdivf hker c₁ h₁ c₂ h₂ hr₁ hr₂ g₁ g₂ av bv hdivg₁ hdivg₂ hgvals
      hgratio w hw hflat₁ hflat₂ hEw

  have hsW : (w, arithFrobC q k 1 • w) ∈ nodePairsOfPlaces (arithFrobC q k 1) W :=
    smulNodePair_mem_nodePairsOfPlaces (arithFrobC q k 1) hw
  set s : ↥(nodePairsOfPlaces (arithFrobC q k 1) W) := ⟨(w, arithFrobC q k 1 • w), hsW⟩ with hs
  set ρ₁ : ↥(modularFunctionFieldC k 1) := R.residue₁ ⟨c₁ • f, h₁⟩ with hρ₁
  set ρ₂ : ↥(modularFunctionFieldC k 1) := R.residue₂ ⟨c₂ • f, h₂⟩ with hρ₂
  set ybar : ↥(modularFunctionFieldC k 1) := R.nodeResidue₁ w
    ⟨((dat.coord w hw).y : ↥(modularFunctionFieldBar (1 * q))), (dat.coord w hw).y.2.1⟩ with hybar
  set xbar : ↥(modularFunctionFieldC k 1) := R.nodeResidue₂ w
    ⟨((dat.coord w hw).x : ↥(modularFunctionFieldBar (1 * q))), (dat.coord w hw).x.2.1⟩ with hxbar

  have hg₁ : w.HasValue g₁ (av s : k) := (hgvals s).1
  have hg₂ : (arithFrobC q k 1 • w).HasValue g₂ (bv s : k) := (hgvals s).2

  obtain ⟨hπ₁0, hπ₁ord⟩ := CvqO4.unifFst_facts W dat.cusp hcusp dat.unifFst (fun w' hw' v => ((hunif w' hw').1 v).symm)
  have hφinj : Function.Injective (fun v : Place k ↥(modularFunctionFieldC k 1) => arithFrobC q k 1 • v) :=
    MulAction.injective (arithFrobC q k 1)
  obtain ⟨hπ₂0, hπ₂ord⟩ := CvqO4.unifSnd_facts W dat.cusp hcusp (fun v => arithFrobC q k 1 • v) hφinj hcuspφ dat.unifSnd
    (fun w' hw' v => ((hunif w' hw').2 v).symm)

  have hrat : ∀ v : Place k ↥(modularFunctionFieldC k 1), v.IsRational := fun v =>
    CvqChild.surjective_algebraMap_residueField v
  have hasValue_evalAt : ∀ (v : Place k ↥(modularFunctionFieldC k 1)) (g : ↥(modularFunctionFieldC k 1)),
      g ≠ 0 → v.ord g = 0 → v.HasValue g (v.evalAt g) ∧ v.evalAt g ≠ 0 := by
    intro v g hg0 hord
    have hmem : g ∈ v.toValuationSubring := v.mem_of_ord_nonneg hg0 hord.ge
    exact ⟨⟨hmem, (v.algebraMap_evalAt (hrat v) hmem).symm⟩, Place.evalAt_ne_zero v (hrat v) hg0 hord⟩
  set cross₁ : Place k ↥(modularFunctionFieldC k 1) → k := fun w' => (dat.crossFst w' w : k) with hcross₁def
  set cross₂ : Place k ↥(modularFunctionFieldC k 1) → k := fun w' => (dat.crossSnd w' w : k) with hcross₂def
  have hcross₁ : ∀ w' ∈ W.erase w, w.HasValue (dat.unifFst w') (cross₁ w') := by
    intro w' hw'
    obtain ⟨hne, hw'W⟩ := Finset.mem_erase.mp hw'
    obtain ⟨hval, hne0⟩ := hasValue_evalAt w (dat.unifFst w') (hπ₁0 w' hw'W) (by rw [hπ₁ord w hw w' hw'W, if_neg hne])
    have : cross₁ w' = w.evalAt (dat.unifFst w') := by
      rw [hcross₁def]; change ((dat.crossFst w' w : kˣ) : k) = _
      unfold AnnulusDatumQ.crossFst; rw [dif_pos hne0]; rfl
    rw [this]; exact hval
  have hcross₂ : ∀ w' ∈ W.erase w, (arithFrobC q k 1 • w).HasValue (dat.unifSnd w') (cross₂ w') := by
    intro w' hw'
    obtain ⟨hne, hw'W⟩ := Finset.mem_erase.mp hw'
    obtain ⟨hval, hne0⟩ := hasValue_evalAt (arithFrobC q k 1 • w) (dat.unifSnd w') (hπ₂0 w' hw'W)
      (by rw [hπ₂ord w hw w' hw'W, if_neg hne])
    have : cross₂ w' = (arithFrobC q k 1 • w).evalAt (dat.unifSnd w') := by
      rw [hcross₂def]; change ((dat.crossSnd w' w : kˣ) : k) = _
      unfold AnnulusDatumQ.crossSnd; rw [dif_pos hne0]; rfl
    rw [this]; exact hval
  have hcross₁0 : ∀ w' ∈ W.erase w, cross₁ w' ≠ 0 := fun w' _ => Units.ne_zero _
  have hcross₂0 : ∀ w' ∈ W.erase w, cross₂ w' ≠ 0 := fun w' _ => Units.ne_zero _

  have hlam' := hlam w hw
  have hmu' := hmu w hw
  have hybar0 : ybar ≠ 0 := by
    intro h0; apply hlam'.ne_zero (Units.ne_zero _); change ybar / dat.unifFst w = 0; rw [h0, zero_div]
  have hxbar0 : xbar ≠ 0 := by
    intro h0; apply hmu'.ne_zero (Units.ne_zero _); change xbar / dat.unifSnd w = 0; rw [h0, zero_div]

  have hη : (ηbar₂ : k) = (ηbar₁ : k) * (εbar' : k) ^ (a.aZ' - a.aZ) := by
    have hε'unit : IsUnit ε' := hε'
    rw [← hηbar₂, ← hηbar₁, ← hεbar']
    exact CvqKey.map_unitPart_eq_of_coupled (NodeLocalized.coeffSubring A K') ϖ' ε' η₁ η₂ hirr.not_isUnit
      (fun h => hirr.ne_zero (Subtype.ext h)) hε'unit hη₁ hη₂ ((q : ℕ) : AlgebraicClosure ℚ) (r * eK w)
      (by have h := congrArg Subtype.val hqϖ'; simpa using h) c₁ c₂ m₁ m₂ (a.aZ' - a.aZ) hc₁η hc₂η hcouple
      (NodeLocalized.redRestrict red K')

  have hdw := CvqOrbit.depthMoment_eq dat (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))) a ha hw (hwidth w hw) hdep hintC
  have hdw' : (dat.depthMoment (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))) w).num =
      dat.width w * dat.endOrderSnd a (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))) w + (a.aZ' - a.aZ) := by
    rw [hdw, Rat.num_intCast]

  set S := (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))).support.filter
    (fun V => P.reduceFst V = w ∧ ¬ P.IsStrictFst V ∧ ¬ P.IsStrictSnd V) with hSdef
  have hν : av s / bv s = (-1) ^ (∑ V ∈ S, (D : Divisor _ _) V) * dat.u0 w ^ dat.endOrderSnd a (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))) w *
      dat.lam w ^ dat.endOrderFst a (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))) w * (dat.mu w ^ dat.endOrderSnd a (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))) w)⁻¹ *
      dat.angFactor w hw (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))) *
      ∏ w' ∈ W.erase w, ((dat.crossFst w' w) ^ (dat.endOrderFst a (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))) w'))⁻¹ * (dat.crossSnd w' w) ^ (dat.endOrderSnd a (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))) w') := by
    have h1 : dat.nodeUnitOf a (D : Divisor _ _) s = Additive.ofMul (av s / bv s) := by
      have := congrFun hgratio s; exact this
    have h2 : av s / bv s = Additive.toMul (dat.nodeUnitOf a (D : Divisor _ _) s) := by rw [h1]; rfl
    rw [h2]
    unfold AnnulusDatumQ.nodeUnitOf
    simp only [toMul_ofMul]
    rw [dif_pos hw]
    unfold AnnulusDatum.annulusDeg
    rw [hSdef]

  have hkey : (α₁ : k) * ((dat.lam w : kˣ) : k) ^ (w.ord ρ₁) * (av s : k) * ∏ w' ∈ W.erase w, cross₁ w' ^ dat.endOrderFst a (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))) w'
      = (α₂ : k) * ((dat.mu w : kˣ) : k) ^ ((arithFrobC q k 1 • w).ord ρ₂) * (bv s : k)
        * ∏ w' ∈ W.erase w, cross₂ w' ^ dat.endOrderSnd a (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))) w' :=
    CvqKmain.key_of_ratio S (W.erase w) (fun V => (D : Divisor _ _) V) (dat.angFactor w hw (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)))) Θ
      (fun w' => dat.crossFst w' w) (fun w' => dat.crossSnd w' w) (dat.endOrderFst a (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)))) (dat.endOrderSnd a (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))))
      α₁ α₂ ηbar₁ ηbar₂ εbar' u0' t (dat.u0 w) (dat.lam w) (dat.mu w) (av s) (bv s)
      (w.ord ρ₁) ((arithFrobC q k 1 • w).ord ρ₂) (dat.endOrderFst a (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))) w) (dat.endOrderSnd a (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))) w) (a.aZ' - a.aZ)
      (dat.depthMoment (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))) w).num (dat.width w) (eK w) hratio hν hΘAF hflat₁ hflat₂ hu0rel (by rw [hp1, hε1 w hw, mul_one]) hη hdw'

  have hval₁ := CvqBeta.hasValue_corrected_of_flat w W w hw ρ₁ g₁ ybar dat.unifFst (dat.endOrderFst a (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)))) (w.ord ρ₁)
    hybar0 (hπ₁0 w hw) (α₁ : k) ((dat.lam w : kˣ) : k) (av s : k) cross₁ hv₁ hlam' (Units.ne_zero _) hg₁ hcross₁ hcross₁0 hflat₁
  have hval₂ := CvqBeta.hasValue_corrected_of_flat (arithFrobC q k 1 • w) W w hw ρ₂ g₂ xbar dat.unifSnd (dat.endOrderSnd a (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))))
    ((arithFrobC q k 1 • w).ord ρ₂) hxbar0 (hπ₂0 w hw) (α₂ : k) ((dat.mu w : kˣ) : k) (bv s : k) cross₂ hv₂ hmu' (Units.ne_zero _)
    hg₂ hcross₂ hcross₂0 hflat₂
  have hc0 : (α₁ : k) * ((dat.lam w : kˣ) : k) ^ (w.ord ρ₁) * (av s : k) * ∏ w' ∈ W.erase w, cross₁ w' ^ dat.endOrderFst a (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))) w' ≠ 0 := by
    refine mul_ne_zero (mul_ne_zero (mul_ne_zero (Units.ne_zero _) (zpow_ne_zero _ (Units.ne_zero _))) (Units.ne_zero _)) ?_
    exact Finset.prod_ne_zero_iff.mpr fun w' hw' => zpow_ne_zero _ (hcross₁0 w' hw')
  refine ⟨Units.mk0 _ hc0, ?_, ?_⟩
  · exact hval₁
  · rw [Units.val_mk0, hkey]; exact hval₂

end CvqChildKey

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

      (∃ (c₁ : AlgebraicClosure ℚ) (h₁ : c₁ • f ∈ R.R₁.integers) (c₂ : AlgebraicClosure ℚ) (h₂ : c₂ • f ∈ R.R₂.integers),
        R.R₁.residue ⟨c₁ • f, h₁⟩ ≠ 0 ∧ R.R₂.residue ⟨c₂ • f, h₂⟩ ≠ 0 ∧
        ∀ (g₁ g₂ : ↥(modularFunctionFieldC k 1))
          (av bv : ↥(nodePairsOfPlaces (arithFrobC q k 1) W) → kˣ),
          (∀ v, (dat.spData a (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)))).1 v = v.ord g₁) →
          (∀ v, (dat.spData a (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)))).2.1 v = v.ord g₂) →
          (∀ s : ↥(nodePairsOfPlaces (arithFrobC q k 1) W),
            (s : Place k ↥(modularFunctionFieldC k 1) × Place k ↥(modularFunctionFieldC k 1)).1.HasValue g₁ (av s) ∧
            (s : Place k ↥(modularFunctionFieldC k 1) × Place k ↥(modularFunctionFieldC k 1)).2.HasValue g₂ (bv s)) →
          ((dat.spData a (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)))).2.2 = fun s => Additive.ofMul (av s / bv s)) →
          ∀ w ∈ W, δ = 0 →
            (arithFrobC q k 1 • w).ord (R.residue₂ ⟨c₂ • f, h₂⟩) + dat.endOrderSnd a (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))) w = 0 →
            (w.ord (R.residue₁ ⟨c₁ • f, h₁⟩) + dat.endOrderFst a (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))) w = 0 ∧
             ∃ c : kˣ, w.HasValue (R.residue₁ ⟨c₁ • f, h₁⟩ * g₁ * ∏ w' ∈ W, dat.unifFst w' ^ dat.endOrderFst a (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))) w') (c : k) ∧
               (arithFrobC q k 1 • w).HasValue
                 (R.residue₂ ⟨c₂ • f, h₂⟩ * g₂ * ∏ w' ∈ W, dat.unifSnd w' ^ dat.endOrderSnd a (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))) w') (c : k))) := by
  classical
  obtain ⟨δ, hA₁, hA₂, hA₃, hA₄⟩ :=
    ModularCurve.PlaceSpecialization.ProlongationTuple.AnnulusDatumQ.exists_chord_le_endOrders_and_rigid_of_isTwistOf_of_inertiaStable
      hq5 P hW R hR hRL hNV hO dat hwidth hwidthj hdepthQ hdepthσ hcusp hcuspφ hunif hKfix ϖ hϖ eK heK ε hε hqϖ hε1 u hu hmax hbr hnoeth hres hVI hu0 hlam hmu D hDstab hDsupp a ha hadm hsp Q₁ Q₂ hQ₁ hQ₂ E hE0 f hf0 hdivf hker

  obtain ⟨c₁, h₁, hr₁⟩ := R.R₁.exists_smul_mem f hf0
  by_cases hδ0 : δ = 0
  · obtain ⟨h₂, hr₂⟩ := hA₄.mp hδ0 c₁ h₁ hr₁
    refine ⟨δ, hA₁, hA₂, c₁, h₁, _, h₂, hr₁, hr₂, ?_⟩
    intro g₁ g₂ av bv hdivg₁ hdivg₂ hgvals hgratio w hw hδ hflat₂
    obtain ⟨hflat₁, hEw⟩ := hA₃ hδ c₁ h₁ _ h₂ hr₁ hr₂ w hw hflat₂
    exact ⟨hflat₁, CvqChildKey.key_values hq5 P hW R hR hRL hNV hO dat hwidth hwidthj hdepthQ hdepthσ hcusp hcuspφ hunif hKfix ϖ hϖ eK heK ε hε hqϖ hε1 u hu hmax hbr hnoeth hres hVI hu0 hlam hmu D hDstab hDsupp a ha hadm hsp Q₁ Q₂ hQ₁ hQ₂ E hE0 f hf0 hdivf hker
      c₁ h₁ _ h₂ hr₁ hr₂ g₁ g₂ av bv hdivg₁ hdivg₂ hgvals hgratio w hw hflat₁ hflat₂ hEw rfl⟩
  · obtain ⟨c₂, h₂, hr₂⟩ := R.R₂.exists_smul_mem f hf0
    refine ⟨δ, hA₁, hA₂, c₁, h₁, c₂, h₂, hr₁, hr₂, ?_⟩
    intro g₁ g₂ av bv hdivg₁ hdivg₂ hgvals hgratio w hw hδ hflat₂
    exact absurd hδ hδ0

end S_ModularCurve_PlaceSpecialization_ProlongationTuple_AnnulusDatumQ_exists_endOrder_ineq_and_coupledScalings_hasValue_of_isTwistOf_of_mk_spData_eq_zero_of_inertiaStable
end P2MW
export P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_AnnulusDatumQ_exists_endOrder_ineq_and_coupledScalings_hasValue_of_isTwistOf_of_mk_spData_eq_zero_of_inertiaStable (solution)
