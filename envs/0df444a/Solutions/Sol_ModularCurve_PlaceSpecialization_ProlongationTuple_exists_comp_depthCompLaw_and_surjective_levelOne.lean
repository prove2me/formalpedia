-- Prove2me | solution 1 for ModularCurve.PlaceSpecialization.ProlongationTuple.exists_comp_depthCompLaw_and_surjective_levelOne
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/a131c2c8-1d8a-5a00-b308-1b53bf8cf951

import Definitions.Def_ModularCurve_NodeDepth
import Definitions.Def_ModularCurve_LevelOneGlueData
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_ModularCurve_JWidth
import Definitions.Def_ModularCurve_ModularUnit
import Theorems.Thm_ModularCurve_PlaceSpecialization_componentGroupProj_depthDual_add_degree_sndDiv_smul_eq_zero_of_div_levelOne_of_five_le
import Theorems.Thm_ModularCurve_PlaceSpecialization_depthDual_add_degree_sndDiv_smul_eq_branchDegrees_snd_smul_of_isGoodDivisor
import Theorems.Thm_ModularCurve_zmultiples_componentGroupProj_smul_coord_eq_top_of_width_eq_jWidth
import Theorems.Thm_ModularCurve_exists_finset_forall_mem_iff_mem_ssPlaces_equiv_evalAt_jGeomGen_eq
import Theorems.Thm_ModularCurve_ssJSet_finite
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_isStrictFst_and_smul_eq_self
import Theorems.Thm_ModularCurve_PlaceSpecialization_exists_isStrictSnd_restrictAlong_eq_forall_inertia_smul_eq
import Theorems.Thm_ModularCurve_PlaceSpecialization_exists_finset_forall_exists_sp_eq_forall_inertia_smul_eq
import Theorems.Thm_ModularCurve_PlaceSpecialization_exists_families_isStrictFst_isStrictSnd_notMem
import Theorems.Thm_ModularCurve_frobOnPlacesGeomLevel_frobOnPlacesGeomLevel_eq_self_of_mem_ssPlaces_of_isAlgClosed
import Theorems.Thm_ModularCurve_deg_eq_one_modularFunctionFieldBar
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_comp_depthCompLaw_and_surjective_levelOne
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.instIsElliptic_tateLaurent ModularCurve.instIsElliptic_tateBase WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.NodeLocalized.isLocalization_nodeDenominators ModularCurve.NodeLocalized.algebraEvalRange ModularCurve.NodeLocalized.isLocalRing_modularLocalizedAtPoint ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.B3.instIsElliptic_goodModel WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral ModularCurve.NodeLocalized.isScalarTower_K_fieldOver_bar ModularCurve.NodeLocalized.algebraFieldOverBar ModularCurve.NodeLocalized.algebra_isIntegral_fieldOver_bar ModularCurve.NodeLocalized.isScalarTower_fieldOver_bar_laurent ModularCurve.NodeLocalized.charZero_fieldOver ModularCurve.NodeLocalized.algebraFieldOver ModularCurve.NodeLocalized.charZero_laurentSeries_algClosure instTopologicallyFGOfFiniteType AdicCompletion.instIsLocalRingMaximalIdeal instFieldLaurentSeriesAlgClosureRat instAlgebraModularFunctionFieldBar ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instAlgebraResidueFieldSubtypeMemValuationSubringGaussBaseResOne"
p2m_attr_erase "instance" "ModularCurve.PlaceSpecialization.LevelOneProlongationPair.algGaussBase instAlgebraModularFunctionFieldFullC ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instAlgebraSubtypeMemValuationSubringGaussBaseResOne ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instAlgebraSubtypeMemValuationSubringGaussBaseResTwo instFieldModularFunctionFieldC ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isScalarTower_resOne instFieldLaurentSeries' ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isScalarTower_resTwo instModuleModularFunctionFieldBar ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isLocalHom_resBase₁ instAlgebraModularFunctionFieldC ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isLocalHom_constToGaussBase ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instFieldResOne instFieldModularFunctionFieldBar ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instAlgebraResidueFieldSubtypeMemValuationSubringGaussBaseResTwo ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instFieldResTwo instFieldModularFunctionFieldFullC ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isScalarTower_gaussBase instAlgebraLaurentSeriesAlgClosureRat ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isLocalHom_resBase₂ ModularCurve.PlaceSpecialization.LevelOneProlongationPair.algResidueConst instCommRingModularFunctionFieldBar AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue"
p2m_attr_erase "instance" "AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar ModularCurve.LevelOnePhi.instAddCommGroup AlgebraicCurve.GaussReduction.isLocalHom_constToGauss ValuationSubring.instIsAlgClosedResidueField"
p2m_attr_erase "simp" "ModularCurve.PlaceSpecialization.LevelOneProlongationPair.mk.sizeOf_spec ModularCurve.PlaceSpecialization.LevelOneProlongationPair.residue₂_apply ModularCurve.PlaceSpecialization.LevelOneProlongationPair.residue₁_apply ModularCurve.PlaceSpecialization.LevelOneProlongationPair.mk.injEq ModularCurve.coe_nodeEquiv_symm_apply ModularCurve.frobNodePair_jOfNode ModularCurve.jOfNode_mk ModularCurve.widthOf_mk ModularCurve.frobNodePairEmb_apply ModularCurve.card_nodePairsOf ModularCurve.frobNodePair_snd ModularCurve.coe_nodeEquiv_apply ModularCurve.frobNodePair_fst AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe"
p2m_attr_erase "simp" "AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆"
p2m_attr_erase "simp" "TateCurve.curve_a₄ TateCurve.curve_a₃ TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one"
p2m_attr_erase "simp" "WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two ModularCurve.NodeLocalized.coe_modularEvalAt ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL ModularCurve.Gamma0Pair.map_toCurve WeierstrassCurve.mapPoint_eq_ratPointMap ModularCurve.Gamma0Pair.map_gen ModularCurve.Gamma0Pair.map_eq_gamma0PairMap ModularCurve.ModuliPoint.map_eq_moduliPointMapRingHom ModularCurve.ModuliPoint.map_mk WeierstrassCurve.mapPointHom_apply WeierstrassCurve.mapPoint_zero WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁"
p2m_attr_erase "simp" "WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff ModularCurve.ProjectiveLine.map_mk WeierstrassCurve.veluX_empty WeierstrassCurve.vcInvEmbedding_apply ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.veluY_empty WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec"
p2m_attr_erase "simp" "AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero ModularCurve.cuspCount_one WeierstrassCurve.Universal.halveX_zero WeierstrassCurve.Universal.specialize_X_one WeierstrassCurve.Universal.coeff_halve WeierstrassCurve.Universal.specialize_X_two WeierstrassCurve.Universal.halveCoeff_zero WeierstrassCurve.Universal.specialize_X_four WeierstrassCurve.Universal.coeff_halveX WeierstrassCurve.Universal.specialize_X_three WeierstrassCurve.Universal.specialize_X_zero HahnSeries.ramScale_apply AlgebraicCurve.Pic.baseChange_mk AlgebraicCurve.Place.forgetConstants_toValuationSubring"
p2m_attr_erase "simp" "AlgebraicCurve.Place.constantFieldEquiv_symm_apply AlgebraicCurve.Place.ord_forgetConstants AlgebraicCurve.Place.extendConstants_toValuationSubring AlgebraicCurve.Place.constantFieldEquiv_apply_toValuationSubring AlgebraicCurve.Place.mem_fiberConstants AlgebraicCurve.Place.restrictConstants_toValuationSubring AdicCompletion.evalₐ_mapₐ AdicCompletion.mapAlgEquivOfBijective_apply AdicCompletion.levelMapₐ_mk AdicCompletion.mapₐ_of AdicCompletion.mapAlgEquiv_symm_apply AdicCompletion.mapAlgEquiv_apply AdicCompletion.evalₐ_ofLevelwiseEquiv AdicCompletion.evalₐ_levelwiseHom AdicCompletion.localizationEquiv_of AdicCompletion.evalₐ_ofLevelwiseEquiv_symm Localization.AtPrime.quotientPowEquiv_mk ModularCurve.LambdaModularPolynomialData.mk.sizeOf_spec ModularCurve.LambdaModularPolynomialData.mk.injEq AdicCompletion.transportOf_of AdicCompletion.selfCompletion_smul_of AdicCompletion.tensorRingEquiv_tmul AdicCompletion.completionOfAlgHom_apply AdicCompletion.completionBaseChangeHom_of AdicCompletion.tensorRingHom_tmul AdicCompletion.stabilizerToCompletionAut_of ModularCurve.PlaceSpecialization.LevelOneProlongationPair.coe_gaussOrderToIntegers₂ ModularCurve.PlaceSpecialization.LevelOneProlongationPair.coe_gaussOrderToIntegers₁ ModularCurve.PlaceSpecialization.LevelOneProlongationPair.coe_toIntegers₁ ModularCurve.PlaceSpecialization.LevelOneProlongationPair.coe_constToGaussBase ModularCurve.PlaceSpecialization.LevelOneProlongationPair.coe_toIntegers₂ AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe"
p2m_attr_erase "simp" "AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule ModularCurve.frobeniusPullbackGeomLevelUnconditional_single ModularCurve.frobeniusPushforwardGeomLevelUnconditional_single ModularCurve.frobeniusGeomLevelUnconditional_apply_coe AlgebraicCurve.GaussReduction.constToGauss_coe AlgebraicCurve.ComponentChart.ofConstantReductionNodes_dom AlgebraicCurve.ComponentChart.ofConstantReductionNodes_placeMap AlgebraicCurve.ComponentChart.ofConstantReductionNodes_nodes AlgebraicCurve.ComponentChart.ofConstantReductionNodes_residue AlgebraicCurve.ComponentChart.ofConstantReductionNodes_integers ModularCurve.FinitePlaceLift.traceHom_coe ModularCurve.FinitePlaceLift.mk.injEq ModularCurve.FinitePlaceLift.mk.sizeOf_spec AlgebraicCurve.ComponentChart.ofConstantReduction_integers AlgebraicCurve.ComponentChart.mk.sizeOf_spec AlgebraicCurve.ComponentChart.ofConstantReduction_placeMap AlgebraicCurve.ComponentChart.ofConstantReduction_nodes AlgebraicCurve.ComponentChart.mk.injEq AlgebraicCurve.ComponentChart.ofConstantReduction_dom AlgebraicCurve.Annulus.mk.sizeOf_spec AlgebraicCurve.Annulus.mk.injEq ValuationSubring.reduceAt_coe ValuationSubring.reduceAt_one ValuationSubring.reduceAt_natCast ValuationSubring.reduceAt_intCast ValuationSubring.reduceAt_zero"
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option synthInstance.maxHeartbeats 1600000
noncomputable section
open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.PlaceSpecialization
namespace CompL1
variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
  {k : Type*} [Field k] [CharP k q] [PerfectField k] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q}
  {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
  (P : PlaceSpecialization A q 1 data hKr k red hα hβ)
  (g : SemilinearAut k (modularFunctionFieldC k 1))
  (W : Finset (Place k (modularFunctionFieldC k 1)))
  (e : Place k (modularFunctionFieldC k 1) → ℕ)
  (depth : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) → ℕ)

def cls (s₀ : ↥(nodePairsOfPlaces g W))
    (D : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))) :
    componentGroup (widthOfPlaces g W e) :=
  componentGroupProj (widthOfPlaces g W e)
    (P.depthDual g W depth D +
      Divisor.degree (P.sndDiv D) •
        (((e (s₀ : Place k (modularFunctionFieldC k 1) × Place k (modularFunctionFieldC k 1)).1 : ℕ) : ℤ) •
          crossingCoord s₀))

theorem depthDiv_add (D D' : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))) :
    P.depthDiv depth (D + D') = P.depthDiv depth D + P.depthDiv depth D' := by
  unfold PlaceSpecialization.depthDiv
  refine Finsupp.sum_add_index' (fun V => by rw [zero_mul, Finsupp.single_zero]) ?_
  intro V a b
  rw [add_mul, Finsupp.single_add]

theorem depthDual_add (D D' : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))) :
    P.depthDual g W depth (D + D')
      = P.depthDual g W depth D + P.depthDual g W depth D' := by
  unfold PlaceSpecialization.depthDual
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [depthDiv_add, Finsupp.add_apply, add_smul]

theorem sndDiv_add (D D' : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))) :
    P.sndDiv (D + D') = P.sndDiv D + P.sndDiv D' := by
  classical
  unfold PlaceSpecialization.sndDiv
  exact Finsupp.filter_add

theorem cls_add (s₀ : ↥(nodePairsOfPlaces g W))
    (D D' : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))) :
    cls P g W e depth s₀ (D + D') = cls P g W e depth s₀ D + cls P g W e depth s₀ D' := by
  have h : P.depthDual g W depth (D + D') +
      Divisor.degree (P.sndDiv (D + D')) •
        (((e (s₀ : Place k (modularFunctionFieldC k 1) × Place k (modularFunctionFieldC k 1)).1 : ℕ) : ℤ) •
          crossingCoord s₀)
    = (P.depthDual g W depth D +
      Divisor.degree (P.sndDiv D) •
        (((e (s₀ : Place k (modularFunctionFieldC k 1) × Place k (modularFunctionFieldC k 1)).1 : ℕ) : ℤ) •
          crossingCoord s₀)) +
      (P.depthDual g W depth D' +
      Divisor.degree (P.sndDiv D') •
        (((e (s₀ : Place k (modularFunctionFieldC k 1) × Place k (modularFunctionFieldC k 1)).1 : ℕ) : ℤ) •
          crossingCoord s₀)) := by
    rw [depthDual_add, sndDiv_add, map_add, add_smul]
    abel
  unfold cls
  rw [h, map_add]

theorem proj_vertex_sub_eq_zero {ι : Type*} [Fintype ι] [DecidableEq ι] (w : ι → ℕ) (s₀ s₁ : ι) :
    componentGroupProj w (((w s₀ : ℕ) : ℤ) • crossingCoord s₀ - ((w s₁ : ℕ) : ℤ) • crossingCoord s₁) = 0 := by
  have hmem : (Pi.single s₀ (1 : ℤ) - Pi.single s₁ 1) ∈ characterLattice ι := by
    rw [mem_characterLattice]
    simp [Finset.sum_sub_distrib]
  have hgram : ((w s₀ : ℕ) : ℤ) • crossingCoord s₀ - ((w s₁ : ℕ) : ℤ) • crossingCoord s₁
      = gramMap w ⟨_, hmem⟩ := by
    apply LinearMap.ext
    intro γ
    rw [gramMap_apply, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.smul_apply,
      crossingCoord_apply, crossingCoord_apply]
    have key : ∀ (t : ι) (γ' : ι → ℤ),
        ∑ x, ((w x : ℕ) : ℤ) * ((Pi.single t (1 : ℤ) : ι → ℤ) x * γ' x) = w t * γ' t := by
      intro t γ'
      rw [Finset.sum_eq_single t]
      · simp
      · intro b _ hb
        simp [hb]
      · simp
    simp only [Pi.sub_apply, sub_mul, mul_sub, Finset.sum_sub_distrib, key, smul_eq_mul]
  rw [hgram]
  exact (Submodule.Quotient.mk_eq_zero _).mpr (LinearMap.mem_range_self _ _)

theorem cls_indep (s₀ s₁ : ↥(nodePairsOfPlaces g W))
    (D : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))) :
    cls P g W e depth s₀ D = cls P g W e depth s₁ D := by
  classical
  unfold cls
  rw [← sub_eq_zero, ← map_sub, add_sub_add_left_eq_sub, ← smul_sub, LinearMap.map_smul_of_tower]
  have h0 := proj_vertex_sub_eq_zero (widthOfPlaces g W e) s₀ s₁
  rw [widthOfPlaces_apply, widthOfPlaces_apply] at h0
  rw [h0]
  exact smul_zero _

theorem subsingleton_componentGroup {ι : Type*} [Fintype ι] [IsEmpty ι] (w : ι → ℕ) :
    Subsingleton (componentGroup w) := by
  infer_instance

def Adm (D : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))) : Prop :=
  ∀ V ∈ D.support,
    (∀ σ ∈ A.inertiaSubgroupIn ℚ, arithmeticGalois (modularFunctionFieldFull (1 * q)) σ • V = V) ∧
      (P.IsStrictFst V ∨ P.IsStrictSnd V ∨ P.reduceFst V ∈ W)

theorem adm_add [DecidableEq (Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)))] {D D' : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))}
    (h : Adm P W D) (h' : Adm P W D') : Adm P W (D + D') := by
  intro V hV
  rcases Finset.mem_union.mp (Finsupp.support_add hV) with h1 | h1
  · exact h V h1
  · exact h' V h1

theorem adm_neg {D : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))}
    (h : Adm P W D) : Adm P W (-D) := by
  intro V hV
  rw [Finsupp.support_neg] at hV
  exact h V hV

theorem adm_sub {D D' : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))}
    (h : Adm P W D) (h' : Adm P W D') : Adm P W (D - D') := by
  classical
  rw [sub_eq_add_neg]; exact adm_add P W h (adm_neg P W h')

theorem adm_zero : Adm P W (0 : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))) := by
  intro V hV
  simp at hV

theorem cls_zero (s₀ : ↥(nodePairsOfPlaces g W)) :
    cls P g W e depth s₀ 0 = 0 := by
  have h := cls_add P g W e depth s₀ 0 0
  rw [add_zero] at h
  exact left_eq_add.mp h

theorem cls_sub (s₀ : ↥(nodePairsOfPlaces g W))
    (D D' : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))) :
    cls P g W e depth s₀ (D - D') = cls P g W e depth s₀ D - cls P g W e depth s₀ D' := by
  have h := cls_add P g W e depth s₀ (D - D') D'
  rw [sub_add_cancel] at h
  exact eq_sub_of_add_eq h.symm

omit [PerfectField k] in
theorem not_isStrictSnd_of_isStrictFst {V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))}
    (h1 : P.IsStrictFst V) : ¬ P.IsStrictSnd V := fun h2 =>
  h1.2 (by rw [h1.1, ← h2.1])

omit [PerfectField k] in

theorem sndPart_pair {V₁ V₂ : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))}
    (h2 : P.IsStrictTypeTwo V₂) (h1 : ¬ P.IsStrictTypeTwo V₁) :
    P.sndPart (Finsupp.single V₂ 1 - Finsupp.single V₁ 1) = Finsupp.single V₂ 1 := by
  classical
  unfold PlaceSpecialization.sndPart
  rw [Finsupp.filter_sub, Finsupp.filter_single_of_pos _ h2, Finsupp.filter_single_of_neg _ h1, sub_zero]

omit [PerfectField k] in
theorem branchDegrees_pair_snd {V₁ V₂ : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))}
    (h2 : P.IsStrictTypeTwo V₂) (h1 : ¬ P.IsStrictTypeTwo V₁) :
    (P.branchDegrees (Finsupp.single V₂ 1 - Finsupp.single V₁ 1)).2 = 1 := by
  show Divisor.degree (P.sndPart _) = 1
  rw [sndPart_pair P h2 h1, Divisor.degree_single, deg_eq_one_modularFunctionFieldBar]
  simp

omit [PerfectField k] in

theorem pair_mem_degZero (V₁ V₂ : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))) :
    (Finsupp.single V₂ (1 : ℤ) - Finsupp.single V₁ 1 :
        Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))) ∈
      Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar (1 * q))) := by
  rw [Divisor.mem_degZero, map_sub, Divisor.degree_single, Divisor.degree_single,
    deg_eq_one_modularFunctionFieldBar, deg_eq_one_modularFunctionFieldBar]
  simp

omit [PerfectField k] in

theorem mk_mem_inertiaInvariants
    (D : ↥(Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar (1 * q)))))
    (hD : ∀ σ ∈ A.inertiaSubgroupIn ℚ,
        arithmeticGalois (modularFunctionFieldFull (1 * q)) σ •
          (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))) = D) :
    Pic0.mk D ∈ inertiaInvariants A (1 * q) := by
  rw [mem_inertiaInvariants]
  intro σ hσ
  rw [galois_smul_pic0_def, SemilinearAut.pic0_smul_mk]
  congr 1
  apply Subtype.ext
  rw [SemilinearAut.coe_degZeroSMulHom]
  exact hD σ hσ

omit [PerfectField k] in
theorem support_pair_subset {V₁ V₂ V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))}
    (hV : V ∈ (Finsupp.single V₂ (1 : ℤ) - Finsupp.single V₁ 1 :
        Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))).support) :
    V = V₂ ∨ V = V₁ := by
  classical
  rw [sub_eq_add_neg] at hV
  rcases Finset.mem_union.mp (Finsupp.support_add hV) with h | h
  · exact Or.inl (Finset.mem_singleton.mp (Finsupp.support_single_subset h))
  · rw [Finsupp.support_neg] at h
    exact Or.inr (Finset.mem_singleton.mp (Finsupp.support_single_subset h))

theorem exists_strict_pair [IsAlgClosed k] [DecidableEq k] (R : ProlongationTuple P) (hqN : ¬ q ∣ 1)
    (hR : R.IsModel) (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q 1 k) :
    ∃ V₁ V₂ : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)),
      P.IsStrictFst V₁ ∧
      (∀ σ ∈ A.inertiaSubgroupIn ℚ, arithmeticGalois (modularFunctionFieldFull (1 * q)) σ • V₁ = V₁) ∧
      P.IsStrictSnd V₂ ∧
      (∀ σ ∈ A.inertiaSubgroupIn ℚ, arithmeticGalois (modularFunctionFieldFull (1 * q)) σ • V₂ = V₂) := by
  haveI : NeZero (1 : ℕ) := ⟨one_ne_zero⟩
  obtain ⟨V₁, hV₁s, hV₁fix, -⟩ :=
    ProlongationTuple.exists_isStrictFst_and_smul_eq_self R hqN hR W (fun w hw => (hW w).mp hw)
  obtain ⟨X, hX⟩ := exists_finset_forall_exists_sp_eq_forall_inertia_smul_eq P hqN
  obtain ⟨-, Q₂, -, hQ₂s, -, -, -, hQ₂X⟩ := exists_families_isStrictFst_isStrictSnd_notMem P hqN X 0 1
  obtain ⟨u, hu, hufix⟩ := hX (P.reduceSnd (Q₂ 0)) (hQ₂X 0)
  obtain ⟨V₂, hV₂s, -, -, hV₂fix⟩ :=
    exists_isStrictSnd_restrictAlong_eq_forall_inertia_smul_eq P u (by rw [hu]; exact (hQ₂s 0).2) hufix
  exact ⟨V₁, V₂, hV₁s, hV₁fix, hV₂s, hV₂fix⟩

theorem vertex_generates [IsAlgClosed k] [DecidableEq k]
    (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q 1 k)
    (hwidth : ∀ w ∈ W, e w = jWidth (w.evalAt (jGeomGen k 1)))
    (s₀ : ↥(nodePairsOfPlaces g W)) :
    AddSubgroup.zmultiples (componentGroupProj (widthOfPlaces g W e)
        (((widthOfPlaces g W e s₀ : ℕ) : ℤ) • crossingCoord s₀)) = ⊤ := by
  have hpairW : ∀ s : ↥(nodePairsOfPlaces g W),
      (s : Place k (modularFunctionFieldC k 1) × Place k (modularFunctionFieldC k 1)).1 ∈ W := by
    intro s
    obtain ⟨w, hw, hs⟩ := (mem_nodePairsOfPlaces_iff g W s.1).mp s.2
    rw [← hs, smulNodePair_fst]
    exact hw
  have hinjW : ∀ w₁ ∈ W, ∀ w₂ ∈ W,
      w₁.evalAt (jGeomGen k 1) = w₂.evalAt (jGeomGen k 1) → w₁ = w₂ := by
    obtain ⟨W', τ, hW', hτ⟩ := exists_finset_forall_mem_iff_mem_ssPlaces_equiv_evalAt_jGeomGen_eq q k
      (ssJSet_finite q k).toFinset (fun j => Set.Finite.mem_toFinset _)
    have hWW : W' = W := Finset.ext fun w => (hW' w).trans (hW w).symm
    subst hWW
    intro w₁ hw₁ w₂ hw₂ h12
    obtain ⟨a₁, ha₁⟩ := τ.surjective ⟨w₁, hw₁⟩
    obtain ⟨a₂, ha₂⟩ := τ.surjective ⟨w₂, hw₂⟩
    have h1 := hτ a₁
    have h2 := hτ a₂
    rw [ha₁] at h1
    rw [ha₂] at h2
    have ha : a₁ = a₂ := by
      apply Subtype.ext
      rw [← h1, ← h2]
      exact h12
    subst ha
    exact Subtype.ext_iff.mp (ha₁.symm.trans ha₂)
  refine zmultiples_componentGroupProj_smul_coord_eq_top_of_width_eq_jWidth (K := k)
    (widthOfPlaces g W e)
    (fun s => (s : Place k (modularFunctionFieldC k 1) × Place k (modularFunctionFieldC k 1)).1.evalAt
      (jGeomGen k 1)) ?_ ?_ s₀
  · intro s t hst
    dsimp only at hst
    apply Subtype.ext
    obtain ⟨ws, hws, hs⟩ := (mem_nodePairsOfPlaces_iff g W s.1).mp s.2
    obtain ⟨wt, hwt, ht⟩ := (mem_nodePairsOfPlaces_iff g W t.1).mp t.2
    rw [← hs, ← ht] at hst ⊢
    simp only [smulNodePair_fst] at hst
    rw [hinjW ws hws wt hwt hst]
  · intro s
    rw [widthOfPlaces_apply]
    exact hwidth _ (hpairW s)

theorem cls_pair [IsAlgClosed k] [DecidableEq k] (hqN : ¬ q ∣ 1)
    (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q 1 k)
    {V₁ V₂ : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))}
    (hV₁ : P.IsStrictFst V₁) (hV₂ : P.IsStrictSnd V₂)
    (s₀ : ↥(nodePairsOfPlaces (arithFrobC q k 1) W)) :
    cls P (arithFrobC q k 1) W e depth s₀ (Finsupp.single V₂ 1 - Finsupp.single V₁ 1)
      = componentGroupProj (widthOfPlaces (arithFrobC q k 1) W e)
          (((widthOfPlaces (arithFrobC q k 1) W e s₀ : ℕ) : ℤ) • crossingCoord s₀) := by
  haveI : NeZero (1 : ℕ) := ⟨one_ne_zero⟩
  have hgood : P.IsGoodDivisor (Finsupp.single V₂ 1 - Finsupp.single V₁ 1) := by
    intro V hV
    rcases support_pair_subset (q := q) hV with rfl | rfl
    · exact Or.inr hV₂
    · exact Or.inl hV₁
  have hWφ : ∀ w ∈ W,
      frobOnPlacesGeomLevel k 1 data hKr (frobOnPlacesGeomLevel k 1 data hKr w) = w :=
    fun w hw => frobOnPlacesGeomLevel_frobOnPlacesGeomLevel_eq_self_of_mem_ssPlaces_of_isAlgClosed
      k 1 hqN data hKr w ((hW w).mp hw)
  have hTG := depthDual_add_degree_sndDiv_smul_eq_branchDegrees_snd_smul_of_isGoodDivisor P
    (arithFrobC q k 1) W hWφ e depth s₀ (Finsupp.single V₂ 1 - Finsupp.single V₁ 1) hgood
  rw [branchDegrees_pair_snd P hV₂ (not_isStrictSnd_of_isStrictFst P hV₁), one_smul] at hTG
  unfold cls
  rw [hTG]
  rfl

end CompL1

set_option maxHeartbeats 32000000 in

theorem solution
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] [PerfectField k] [IsAlgClosed k] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
    (P : PlaceSpecialization A q 1 data hKr k red hα hβ)
    (R : ProlongationTuple P) [DecidableEq k] (hqN : ¬ q ∣ 1)
    (hR : R.IsModel) (hO : R.OrderLawFixed)
    (W : Finset (Place k (modularFunctionFieldC k 1)))
    (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q 1 k)
    (hreg : R.RegularityLaw W) (hval : R.NodeValueLaw W)
    (e : Place k (modularFunctionFieldC k 1) → ℕ) (he : ∀ w ∈ W, 1 ≤ e w)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
    (ϖ : ↥(NodeLocalized.coeffSubring A K))
    (hϖ : ∀ d : ↥(NodeLocalized.coeffSubring A K), NodeLocalized.redRestrict red K d = 0 ↔ ∃ d', d = ϖ * d')
    (eK : ℕ) (heK : 1 ≤ eK) (ε : ↥(NodeLocalized.coeffSubring A K)) (hε : IsUnit ε)
    (hqϖ : ((q : ℕ) : ↥(NodeLocalized.coeffSubring A K)) = ϖ ^ eK * ε)
    (cs : ∀ w ∈ W, R.NodeCoordinates K w)
    (hxy : ∀ w (hw : w ∈ W), ∃ u : ↥(R.nodeIntegersOver K w), IsUnit u ∧
        (cs w hw).x * (cs w hw).y = R.nodeConst K w ϖ ^ (e w * eK) * u)
    (hmax : ∀ w (hw : w ∈ W),
        (Ideal.span {R.nodeConst K w ϖ, (cs w hw).x, (cs w hw).y}).IsMaximal ∧
        ∀ M : Ideal ↥(R.nodeIntegersOver K w), M.IsMaximal → M = Ideal.span {R.nodeConst K w ϖ, (cs w hw).x, (cs w hw).y})
    (hbr : ∀ w (hw : w ∈ W),
        (Ideal.span {R.nodeConst K w ϖ, (cs w hw).x}).IsPrime ∧ (Ideal.span {R.nodeConst K w ϖ, (cs w hw).y}).IsPrime ∧
        (cs w hw).y ∉ Ideal.span {R.nodeConst K w ϖ, (cs w hw).x} ∧ (cs w hw).x ∉ Ideal.span {R.nodeConst K w ϖ, (cs w hw).y})
    (hnoeth : ∀ w ∈ W, IsNoetherianRing ↥(R.nodeIntegersOver K w))
    (hres : ∀ w ∈ W, ∀ g : ↥(R.nodeIntegersOver K w),
        ∃ o : ↥(NodeLocalized.coeffSubring A K), ¬ IsUnit (g - R.nodeConst K w o))
    (hVI : ∀ w ∈ W, R.ValueIntegralityLaw w)
    (depth : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) → ℕ)
    (hdepth : ∀ w (hw : w ∈ W), (cs w hw).DepthValueLaw depth)
    (hq : 5 ≤ q)
    (hwidth : ∀ w ∈ W, e w = jWidth (w.evalAt (jGeomGen k 1)))
    (hrep : ∀ x : ↥(inertiaInvariants A (1 * q)),
      ∃ D : ↥(Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar (1 * q)))),
        Pic0.mk D = (x : JZero (1 * q)) ∧
        ∀ V ∈ (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))).support,
          (∀ σ ∈ A.inertiaSubgroupIn ℚ, arithmeticGalois (modularFunctionFieldFull (1 * q)) σ • V = V) ∧
            (P.IsStrictFst V ∨ P.IsStrictSnd V ∨ P.reduceFst V ∈ W)) :
    ∃ comp : ↥(inertiaInvariants A (1 * q)) →+ componentGroup (widthOfPlaces (arithFrobC q k 1) W e),
      P.DepthCompLaw (arithFrobC q k 1) W e depth comp ∧ Function.Surjective comp := by
  classical

  have hR1 := fun (f : ↥(modularFunctionFieldBar (1 * q))) (hf : f ≠ 0)
      (D : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))) (hDf : ∀ V, D V = V.ord f)
      (hsupp : ∀ V ∈ D.support,
        P.IsStrictFst V ∨ P.IsStrictSnd V ∨
          (P.reduceFst V ∈ W ∧
            ∀ σ ∈ A.inertiaSubgroupIn ℚ, arithmeticGalois (modularFunctionFieldFull (1 * q)) σ • V = V))
      (s₀ : ↥(nodePairsOfPlaces (arithFrobC q k 1) W)) =>
    componentGroupProj_depthDual_add_degree_sndDiv_smul_eq_zero_of_div_levelOne_of_five_le P R hqN hq hR hO W hW hreg
      hval e he K ϖ hϖ eK heK ε hε hqϖ cs hxy hmax hbr hnoeth hres hVI depth hdepth f hf D hDf hsupp s₀

  have hadm_supp : ∀ {D : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))},
      CompL1.Adm P W D → ∀ V ∈ D.support,
        P.IsStrictFst V ∨ P.IsStrictSnd V ∨
          (P.reduceFst V ∈ W ∧
            ∀ σ ∈ A.inertiaSubgroupIn ℚ, arithmeticGalois (modularFunctionFieldFull (1 * q)) σ • V = V) := by
    intro D hD V hV
    obtain ⟨hfix, h⟩ := hD V hV
    rcases h with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr ⟨h, hfix⟩)

  have hcls_div : ∀ (s₀ : ↥(nodePairsOfPlaces (arithFrobC q k 1) W))
      (D : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))),
      CompL1.Adm P W D → D.IsPrincipal → CompL1.cls P (arithFrobC q k 1) W e depth s₀ D = 0 := by
    intro s₀ D hD ⟨f, hf, hDf⟩
    exact hR1 f hf D hDf (hadm_supp hD) s₀

  have hwd : ∀ (s₀ : ↥(nodePairsOfPlaces (arithFrobC q k 1) W))
      (D₁ D₂ : ↥(Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar (1 * q))))),
      Pic0.mk D₁ = Pic0.mk D₂ →
      CompL1.Adm P W (D₁ : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))) →
      CompL1.Adm P W (D₂ : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))) →
      CompL1.cls P (arithFrobC q k 1) W e depth s₀ (D₁ : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)))
        = CompL1.cls P (arithFrobC q k 1) W e depth s₀ (D₂ : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))) := by
    intro s₀ D₁ D₂ h h1 h2
    have hpr : ((D₁ : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))) - D₂).IsPrincipal := by
      have h' := QuotientAddGroup.eq_iff_sub_mem.mp h
      rw [AddSubgroup.mem_addSubgroupOf, AddSubgroupClass.coe_sub] at h'
      exact h'
    have h0 := hcls_div s₀ _ (CompL1.adm_sub P W h1 h2) hpr
    rw [CompL1.cls_sub] at h0
    exact sub_eq_zero.mp h0

  by_cases hne : (nodePairsOfPlaces (arithFrobC q k 1) W).Nonempty
  swap
  · refine ⟨0, ?_, ?_⟩
    · intro D hH hD s₀ hs₀
      exact absurd ⟨s₀, hs₀⟩ hne
    · haveI : IsEmpty ↥(nodePairsOfPlaces (arithFrobC q k 1) W) :=
        ⟨fun s => hne ⟨s.1, s.2⟩⟩
      haveI : Subsingleton (componentGroup (widthOfPlaces (arithFrobC q k 1) W e)) :=
        CompL1.subsingleton_componentGroup _
      exact fun y => ⟨0, Subsingleton.elim _ _⟩
  obtain ⟨s₀v, hs₀v⟩ := hne
  obtain ⟨s₀⟩ : Nonempty ↥(nodePairsOfPlaces (arithFrobC q k 1) W) := ⟨⟨s₀v, hs₀v⟩⟩

  choose rep hrep_mk hrep_adm using hrep
  have hadm_rep : ∀ x, CompL1.Adm P W (rep x : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))) :=
    fun x => hrep_adm x

  have hcompD : ∀ (x : ↥(inertiaInvariants A (1 * q)))
      (D : ↥(Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar (1 * q))))),
      Pic0.mk D = (x : JZero (1 * q)) →
      CompL1.Adm P W (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))) →
      CompL1.cls P (arithFrobC q k 1) W e depth s₀ (rep x : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)))
        = CompL1.cls P (arithFrobC q k 1) W e depth s₀ (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))) :=
    fun x D hD hD' => hwd s₀ (rep x) D ((hrep_mk x).trans hD.symm) (hadm_rep x) hD'
  let comp : ↥(inertiaInvariants A (1 * q)) →+ componentGroup (widthOfPlaces (arithFrobC q k 1) W e) :=
    { toFun := fun x =>
        CompL1.cls P (arithFrobC q k 1) W e depth s₀ (rep x : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)))
      map_zero' := by
        show CompL1.cls P (arithFrobC q k 1) W e depth s₀ (rep 0 : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))) = 0
        rw [hcompD 0 0 (by rw [Pic0.mk_zero, ZeroMemClass.coe_zero]) (CompL1.adm_zero P W)]
        exact CompL1.cls_zero P (arithFrobC q k 1) W e depth s₀
      map_add' := fun x y => by
        show CompL1.cls P (arithFrobC q k 1) W e depth s₀ (rep (x + y) : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)))
          = CompL1.cls P (arithFrobC q k 1) W e depth s₀ (rep x : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)))
            + CompL1.cls P (arithFrobC q k 1) W e depth s₀ (rep y : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)))
        rw [hcompD (x + y) (rep x + rep y) (by
              rw [Pic0.mk_add, hrep_mk, hrep_mk, AddMemClass.coe_add])
            (CompL1.adm_add P W (hadm_rep x) (hadm_rep y))]
        exact CompL1.cls_add P (arithFrobC q k 1) W e depth s₀ _ _ }
  have hcomp_apply : ∀ x, comp x
      = CompL1.cls P (arithFrobC q k 1) W e depth s₀ (rep x : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))) :=
    fun x => rfl
  refine ⟨comp, ?_, ?_⟩
  ·
    intro D hH hD s₁ hs₁
    rw [hcomp_apply, hcompD ⟨Pic0.mk D, hH⟩ D rfl hD, CompL1.cls_indep P (arithFrobC q k 1) W e depth s₀ ⟨s₁, hs₁⟩]
    rfl
  ·
    have hgen := CompL1.vertex_generates (q := q) (arithFrobC q k 1) W e hW hwidth s₀
    obtain ⟨V₁, V₂, hV₁s, hV₁fix, hV₂s, hV₂fix⟩ := CompL1.exists_strict_pair P W R hqN hR hW
    obtain ⟨D₀, hD₀⟩ : ∃ D₀ : ↥(Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar (1 * q)))),
        (D₀ : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)))
          = Finsupp.single V₂ 1 - Finsupp.single V₁ 1 := ⟨⟨_, CompL1.pair_mem_degZero V₁ V₂⟩, rfl⟩
    have hfixD : ∀ σ ∈ A.inertiaSubgroupIn ℚ,
        arithmeticGalois (modularFunctionFieldFull (1 * q)) σ •
          (D₀ : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))) = D₀ := by
      intro σ hσ
      rw [hD₀, smul_sub, SemilinearAut.smul_single, SemilinearAut.smul_single, hV₂fix σ hσ, hV₁fix σ hσ]
    have hH₀ : Pic0.mk D₀ ∈ inertiaInvariants A (1 * q) := CompL1.mk_mem_inertiaInvariants D₀ hfixD
    have hadm₀ : CompL1.Adm P W (D₀ : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))) := by
      intro V hV
      rw [hD₀] at hV
      rcases CompL1.support_pair_subset (q := q) hV with rfl | rfl
      · exact ⟨hV₂fix, Or.inr (Or.inl hV₂s)⟩
      · exact ⟨hV₁fix, Or.inl hV₁s⟩
    have hx₀ : comp ⟨Pic0.mk D₀, hH₀⟩ = componentGroupProj (widthOfPlaces (arithFrobC q k 1) W e)
        (((widthOfPlaces (arithFrobC q k 1) W e s₀ : ℕ) : ℤ) • crossingCoord s₀) := by
      rw [hcomp_apply, hcompD ⟨Pic0.mk D₀, hH₀⟩ D₀ rfl hadm₀, hD₀]
      exact CompL1.cls_pair P W e depth hqN hW hV₁s hV₂s s₀
    intro y
    have hy : y ∈ AddSubgroup.zmultiples (componentGroupProj (widthOfPlaces (arithFrobC q k 1) W e)
        (((widthOfPlaces (arithFrobC q k 1) W e s₀ : ℕ) : ℤ) • crossingCoord s₀)) := by
      rw [hgen]; trivial
    obtain ⟨n, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp hy
    exact ⟨n • ⟨Pic0.mk D₀, hH₀⟩, (map_zsmul comp n _).trans (congrArg (fun z => n • z) hx₀)⟩

end
end S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_comp_depthCompLaw_and_surjective_levelOne
end P2MW
export P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_comp_depthCompLaw_and_surjective_levelOne (solution)
