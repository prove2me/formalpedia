-- Prove2me | solution 1 for ModularCurve.PlaceSpecialization.componentGroupProj_depthDual_add_degree_sndDiv_smul_eq_zero_of_div_levelOne_of_five_le
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/b8237dac-05f4-55e1-99db-38f30f63f7fa

import Definitions.Def_ModularCurve_NodeDepth
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_cuspLawInfty_oneSided_levelOne
import Theorems.Thm_AnnulusSlope_sum_sum_mul_slopeDrop_smul_add_sum_slope_smul_eq_zero
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_divisorLawFst_oneSided_levelOne
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_divisorLawSnd_oneSided_levelOne
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_cuspLawZero_oneSided_levelOne
import Theorems.Thm_ModularCurve_frobOnPlacesGeomLevel_frobOnPlacesGeomLevel_eq_self_of_mem_ssPlaces_of_isAlgClosed
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_isLocalRing_and_isNoetherianRing_nodeIntegersOver_levelOne
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_not_isUnit_sub_nodeConst_of_evalAt_mem_range_redRestrict_levelOne_of_five_le
import Theorems.Thm_AlgebraicCurve_Place_restrictAlong_surjective
import Theorems.Thm_ModularCurve_finiteAlong_heckeAlphaBar_of_prime
import Theorems.Thm_AlgebraicCurve_separableAlong_of_charZero
import Theorems.Thm_ModularCurve_NodeLocalized_exists_finiteDimensional_forall_inertia_apply_eq_and_mem_range_redRestrict
import Theorems.Thm_ModularCurve_pow_q_sq_eq_self_of_mem_ssJSet
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_crossingPresentation_nodeIntegersOver_levelOne
import Theorems.Thm_ModularCurve_PlaceSpecialization_not_fixed_reduceFst_of_isStrictSnd
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_nodeDepths_lt_one_and_partition_of_nodeEquation_of_orderLawFixed
import Theorems.Thm_ModularCurve_exists_finiteDimensional_mem_fieldOver_and_redRestrict_eq
import Theorems.Thm_ModularCurve_NodeLocalized_exists_forall_redRestrict_eq_zero_iff_and_natCast_eq_pow_mul
import Theorems.Thm_AlgebraicCurve_Place_ord_smul_of_ne_zero
import Theorems.Thm_ModularCurve_isCurveOver_modularFunctionFieldC_of_good
import Theorems.Thm_ModularCurve_isCurveOver_laurentBaseChange_modularFunctionFieldFull
import Theorems.Thm_ModularCurve_arithFrobC_smul_eq_frobOnPlacesGeomLevel
import Theorems.Thm_ModularCurve_arithFrobC_smul_mem_ssPlaces_univ
import Theorems.Thm_ModularCurve_PlaceSpecialization_exists_isInftySide_reduceFst_eq_and_isZeroSide_reduceSnd_eq_of_not_isAffineGeomPlace
import Theorems.Thm_ModularCurve_PlaceSpecialization_exists_ord_jQFun_sub_pos_of_isAffineGeomPlace_reduceSnd
import Theorems.Thm_ModularCurve_CharPModel_frobOnPlacesGeomLevel_eq_self_of_ord_jqModC_neg
import Theorems.Thm_ModularCurve_modularUnitSeries_mem_modularFunctionFieldFull
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_mapDomain_reduceSnd_filter_sheetTwo_eq_ord_residueSnd_levelOne
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_mapDomain_reduceFst_filter_sheetOne_eq_ord_residueFst_levelOne_univ
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_not_isAffineGeomPlace_reduceFst_of_isCuspidal
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_mul_eq_of_mem_fieldOver_nodeIntegersOver_levelOne
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_sum_div_reduceFst_le_ord_residueFst_add_ord_residueSnd
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_slopeDrop_eq_sum_div_depth_of_sum_div_reduceFst_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_PlaceSpecialization_componentGroupProj_depthDual_add_degree_sndDiv_smul_eq_zero_of_div_levelOne_of_five_le
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
set_option synthInstance.maxHeartbeats 1600000

p2m_open "AlgebraicCurve IsLocalRing ModularCurve ModularCurve.PlaceSpecialization~IsZeroSide"
open Finset BigOperators

namespace R1Skel

section Lattice
variable {ι : Type*} [Fintype ι]

theorem sum_crossingCoord : ∑ s : ι, (crossingCoord s : Module.Dual ℤ (characterLattice ι)) = 0 := by
  ext γ
  simp only [LinearMap.coe_sum, Finset.sum_apply, crossingCoord_apply, LinearMap.zero_apply]
  exact mem_characterLattice.mp γ.2

theorem componentGroupProj_smul_crossingCoord_eq [DecidableEq ι] (e : ι → ℕ) (s s₀ : ι) :
    componentGroupProj e ((e s : ℤ) • crossingCoord s) = componentGroupProj e ((e s₀ : ℤ) • crossingCoord s₀) := by
  rw [← sub_eq_zero, ← map_sub]
  change (LinearMap.range (gramMap e)).mkQ _ = 0
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  by_cases hss : s = s₀
  · subst hss; simp
  refine ⟨⟨Pi.single s 1 - Pi.single s₀ 1, ?_⟩, ?_⟩
  · rw [mem_characterLattice]
    simp [Finset.sum_sub_distrib]
  · ext γ
    simp only [gramMap_apply, LinearMap.sub_apply, LinearMap.smul_apply, crossingCoord_apply, smul_eq_mul, Pi.sub_apply]
    simp only [Pi.single_apply, sub_mul, ite_mul, one_mul, zero_mul, mul_sub, mul_ite, mul_zero,
      Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]

theorem smul_componentGroupProj_crossingCoord_eq [DecidableEq ι] (e : ι → ℕ) (s s₀ : ι) :
    (e s : ℤ) • componentGroupProj e (crossingCoord s) = componentGroupProj e ((e s₀ : ℤ) • crossingCoord s₀) := by
  rw [← map_zsmul]
  exact componentGroupProj_smul_crossingCoord_eq e s s₀

theorem sum_componentGroupProj_crossingCoord (e : ι → ℕ) :
    ∑ s : ι, componentGroupProj e (crossingCoord s) = 0 := by
  rw [← map_sum, sum_crossingCoord, map_zero]

end Lattice

section DepthDiv
variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
  {k : Type*} [Field k] [CharP k q] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
  {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
  (P : PlaceSpecialization A q N data hKr k red hα hβ)

open Classical in

theorem depthDiv_apply_eq_sum_Ico
    (depth : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) → ℕ)
    (D : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)))
    (w : Place k (modularFunctionFieldC k N)) (n : ℕ) (hn : 1 ≤ n)
    (hbound : ∀ V ∈ D.support, P.reduceFst V = w → depth V < n) :
    P.depthDiv depth D w =
      ∑ d ∈ Finset.Ico 1 n, (d : ℤ) * ∑ V ∈ D.support with (P.reduceFst V = w ∧ depth V = d), D V := by
  have h1 : P.depthDiv depth D w = ∑ V ∈ D.support with P.reduceFst V = w, D V * (depth V : ℤ) := by
    simp only [depthDiv, Finsupp.sum, Finsupp.finset_sum_apply, Finsupp.single_apply, Finset.sum_filter]
  refine h1.trans ?_
  have h2 : ∑ V ∈ D.support with P.reduceFst V = w, D V * (depth V : ℤ) =
      ∑ d ∈ Finset.Ico 0 n, ∑ V ∈ (D.support.filter fun V => P.reduceFst V = w) with depth V = d, D V * (depth V : ℤ) := by
    symm
    apply Finset.sum_fiberwise_of_maps_to
    intro V hV
    rw [Finset.mem_filter] at hV
    exact Finset.mem_Ico.mpr ⟨Nat.zero_le _, hbound V hV.1 hV.2⟩
  refine h2.trans ?_
  refine (Finset.sum_eq_sum_Ico_succ_bot hn
    (fun d => ∑ V ∈ (D.support.filter fun V => P.reduceFst V = w) with depth V = d, D V * (depth V : ℤ))).trans ?_
  have h0 : ∑ V ∈ (D.support.filter fun V => P.reduceFst V = w) with depth V = 0, D V * (depth V : ℤ) = 0 := by
    refine Finset.sum_eq_zero fun V hV => ?_
    rw [Finset.mem_filter] at hV
    simp [hV.2]
  rw [h0, zero_add]
  refine Finset.sum_congr rfl fun d hd => ?_
  rw [Finset.mul_sum]
  simp only [Finset.filter_filter]
  refine Finset.sum_congr rfl fun V hV => ?_
  rw [Finset.mem_filter] at hV
  rw [hV.2.2, mul_comm]

end DepthDiv

section Fixed
variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
  {k : Type*} [Field k] [CharP k q] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
  {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
  (P : PlaceSpecialization A q N data hKr k red hα hβ)

theorem fixed_of_strict_or_strict_or_fixed [DecidableEq k] [IsAlgClosed k] (hqN : ¬ q ∣ N)
    (W : Finset (Place k (modularFunctionFieldC k N))) (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q N k)
    (V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)))
    (h : P.IsStrictFst V ∨ P.IsStrictSnd V ∨
      (P.reduceFst V ∈ W ∧ ∀ σ ∈ A.inertiaSubgroupIn ℚ, arithmeticGalois (modularFunctionFieldFull (N * q)) σ • V = V))
    (hVW : P.reduceFst V ∈ W) :
    ∀ σ ∈ A.inertiaSubgroupIn ℚ, arithmeticGalois (modularFunctionFieldFull (N * q)) σ • V = V := by
  have hss := ModularCurve.frobOnPlacesGeomLevel_frobOnPlacesGeomLevel_eq_self_of_mem_ssPlaces_of_isAlgClosed
    k N hqN data hKr (P.reduceFst V) ((hW _).mp hVW)
  rcases h with h | h | h
  · exact absurd hss h.2
  · exact absurd hss (ModularCurve.PlaceSpecialization.not_fixed_reduceFst_of_isStrictSnd P V h)
  · exact h.2

end Fixed

section Window

theorem depth_window {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀] {x y vϖ vq vε : Γ₀} {eK ew d : ℕ}
    (hx1 : x < 1) (hy1 : y < 1) (hprod : x * y = vϖ ^ (ew * eK)) (hy : y = vq ^ d)
    (hvq : vq = vϖ ^ eK * vε) (hvε : vε = 1) (hle : vϖ ≤ 1) (hne : vϖ ≠ 0) : 0 < d ∧ d < ew := by
  rw [hvε, mul_one] at hvq
  rw [hvq, ← pow_mul] at hy
  refine ⟨Nat.pos_of_ne_zero fun hd => ?_, lt_of_not_ge fun hd => ?_⟩
  · rw [hd, mul_zero, pow_zero] at hy
    exact (lt_irrefl (1 : Γ₀)) (hy ▸ hy1)
  · have hy0 : y ≠ 0 := by rw [hy]; exact pow_ne_zero _ hne
    have h1 : x * y < y := by
      calc x * y < 1 * y := mul_lt_mul_of_pos_right hx1 (zero_lt_iff.mpr hy0)
        _ = y := one_mul y
    have h2 : y ≤ vϖ ^ (ew * eK) := by
      rw [hy]
      exact pow_le_pow_right_of_le_one' hle (by rw [Nat.mul_comm ew eK]; exact Nat.mul_le_mul_left eK hd)
    exact (lt_irrefl _) (lt_of_lt_of_le (hprod ▸ h1) h2)

theorem eq_one_of_mul_eq_one_of_le_one {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀] {a b : Γ₀}
    (ha : a ≤ 1) (hb : b ≤ 1) (hab : a * b = 1) : a = 1 :=
  le_antisymm ha (by calc (1 : Γ₀) = a * b := hab.symm
    _ ≤ a * 1 := mul_le_mul_right hb a
    _ = a := mul_one a)

end Window

section CoeffValuation

theorem coeff_valuation (A : ValuationSubring (AlgebraicClosure ℚ)) (K : IntermediateField ℚ (AlgebraicClosure ℚ))
    (q : ℕ) (hq : q ≠ 0) (ϖ ε : ↥(NodeLocalized.coeffSubring A K)) (eK : ℕ) (heK : 1 ≤ eK) (hε : IsUnit ε)
    (hqϖ : ((q : ℕ) : ↥(NodeLocalized.coeffSubring A K)) = ϖ ^ eK * ε) :
    A.valuation (((q : ℕ) : AlgebraicClosure ℚ)) =
        A.valuation (ϖ : AlgebraicClosure ℚ) ^ eK * A.valuation (ε : AlgebraicClosure ℚ) ∧
      A.valuation (ε : AlgebraicClosure ℚ) = 1 ∧
      A.valuation (ϖ : AlgebraicClosure ℚ) ≤ 1 ∧ A.valuation (ϖ : AlgebraicClosure ℚ) ≠ 0 := by
  have hSA : ∀ z : ↥(NodeLocalized.coeffSubring A K), (z : AlgebraicClosure ℚ) ∈ A := fun z => z.2.1
  have hvq : A.valuation (((q : ℕ) : AlgebraicClosure ℚ)) =
      A.valuation (ϖ : AlgebraicClosure ℚ) ^ eK * A.valuation (ε : AlgebraicClosure ℚ) := by
    have h := congrArg (fun z : ↥(NodeLocalized.coeffSubring A K) => (z : AlgebraicClosure ℚ)) hqϖ
    simp only [Subring.coe_natCast, Subring.coe_mul, Subring.coe_pow] at h
    rw [h, map_mul, map_pow]
  refine ⟨hvq, ?_, (A.valuation_le_one_iff _).mpr (hSA ϖ), ?_⟩
  · obtain ⟨b, hb⟩ := hε.exists_right_inv
    have h := congrArg (fun z : ↥(NodeLocalized.coeffSubring A K) => (z : AlgebraicClosure ℚ)) hb
    simp only [Subring.coe_mul, Subring.coe_one] at h
    have h' := congrArg A.valuation h
    rw [map_mul, map_one] at h'
    exact eq_one_of_mul_eq_one_of_le_one ((A.valuation_le_one_iff _).mpr (hSA ε))
      ((A.valuation_le_one_iff _).mpr (hSA b)) h'
  · intro h0
    rw [h0, zero_pow (by omega), zero_mul, map_eq_zero] at hvq
    exact (Nat.cast_ne_zero.mpr hq) hvq

end CoeffValuation

section Wiring
variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
  {k : Type*} [Field k] [CharP k q] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
  {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
  {P : PlaceSpecialization A q N data hKr k red hα hβ}

theorem red_eq_zero_iff (R : ProlongationTuple P) (c : A) : red c = 0 ↔ c ∈ maximalIdeal A := by
  rw [← R.redBar_residue, map_eq_zero_iff _ R.redBar.injective, IsLocalRing.residue_eq_zero_iff]

omit [Fact q.Prime] in

theorem fieldOver_mono (M : ℕ) [NeZero M] {K K' : IntermediateField ℚ (AlgebraicClosure ℚ)} (hKK' : K ≤ K') :
    NodeLocalized.fieldOver M K ≤ NodeLocalized.fieldOver M K' := by
  unfold NodeLocalized.fieldOver
  apply Subfield.closure_mono
  apply Set.union_subset_union_left
  rintro _ ⟨x, rfl⟩
  exact ⟨⟨x.1, hKK' x.2⟩, rfl⟩

theorem exists_finiteDimensional_sup (K Kf : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K] [FiniteDimensional ℚ Kf]
    (c₁ c₂ : AlgebraicClosure ℚ) :
    ∃ K' : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ K' ∧ K ≤ K' ∧ Kf ≤ K' ∧ c₁ ∈ K' ∧ c₂ ∈ K' := by
  haveI : FiniteDimensional ℚ ↥(IntermediateField.adjoin ℚ ({c₁, c₂} : Set (AlgebraicClosure ℚ))) :=
    IntermediateField.finiteDimensional_adjoin fun x _ => (Algebra.IsAlgebraic.isAlgebraic x).isIntegral
  haveI : FiniteDimensional ℚ ↥(K ⊔ Kf) := IntermediateField.finiteDimensional_sup K Kf
  have hle : IntermediateField.adjoin ℚ ({c₁, c₂} : Set (AlgebraicClosure ℚ)) ≤ K ⊔ Kf ⊔ IntermediateField.adjoin ℚ {c₁, c₂} :=
    le_sup_right
  exact ⟨K ⊔ Kf ⊔ IntermediateField.adjoin ℚ {c₁, c₂}, IntermediateField.finiteDimensional_sup (K ⊔ Kf) _,
    le_sup_left.trans le_sup_left, le_sup_right.trans le_sup_left,
    hle (IntermediateField.subset_adjoin ℚ _ (by simp)), hle (IntermediateField.subset_adjoin ℚ _ (by simp))⟩

theorem exists_finiteDimensional_sup₃ (K Kf K₀ : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K] [FiniteDimensional ℚ Kf]
    [FiniteDimensional ℚ K₀] (c₁ c₂ : AlgebraicClosure ℚ) :
    ∃ K' : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ K' ∧ K ≤ K' ∧ Kf ≤ K' ∧ K₀ ≤ K' ∧ c₁ ∈ K' ∧ c₂ ∈ K' := by
  obtain ⟨K₁, h₁, hK, hKf, hc₁, hc₂⟩ := exists_finiteDimensional_sup K Kf c₁ c₂
  haveI := h₁
  exact ⟨K₁ ⊔ K₀, IntermediateField.finiteDimensional_sup K₁ K₀, hK.trans le_sup_left, hKf.trans le_sup_left, le_sup_right,
    (le_sup_left : K₁ ≤ K₁ ⊔ K₀) hc₁, (le_sup_left : K₁ ≤ K₁ ⊔ K₀) hc₂⟩

theorem range_redRestrict_mono {K K' : IntermediateField ℚ (AlgebraicClosure ℚ)} (hKK' : K ≤ K') {a : k}
    (ha : a ∈ Set.range (NodeLocalized.redRestrict red K)) : a ∈ Set.range (NodeLocalized.redRestrict red K') := by
  obtain ⟨z, rfl⟩ := ha
  exact ⟨⟨(z : AlgebraicClosure ℚ), z.2.1, hKK' z.2.2⟩, rfl⟩

end Wiring

section Enlarge
variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
  {k : Type*} [Field k] [CharP k q] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
  {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
  {P : PlaceSpecialization A q N data hKr k red hα hβ}

theorem nodeIntegersOver_mono (R : ProlongationTuple P) {K K' : IntermediateField ℚ (AlgebraicClosure ℚ)} (hKK' : K ≤ K')
    (w : Place k (modularFunctionFieldC k N)) : R.nodeIntegersOver K w ≤ R.nodeIntegersOver K' w :=
  fun _ hf => ⟨hf.1, fieldOver_mono (N * q) hKK' hf.2⟩

def enlargeCoordinates (R : ProlongationTuple P) [PerfectField k] {K K' : IntermediateField ℚ (AlgebraicClosure ℚ)} (hKK' : K ≤ K')
    {w : Place k (modularFunctionFieldC k N)} (c : R.NodeCoordinates K w) : R.NodeCoordinates K' w where
  x := ⟨c.x.1, nodeIntegersOver_mono R hKK' w c.x.2⟩
  y := ⟨c.y.1, nodeIntegersOver_mono R hKK' w c.y.2⟩
  x_fst := c.x_fst
  x_snd := c.x_snd
  y_snd := c.y_snd
  y_fst := c.y_fst

end Enlarge

section UnifTransfer
variable {k : Type*} [Field k]

theorem isUnit_coeffSubring_of_red_ne_zero (A : ValuationSubring (AlgebraicClosure ℚ)) (red : A →+* k)
    (hker : ∀ c : A, red c = 0 ↔ c ∈ maximalIdeal A) (K : IntermediateField ℚ (AlgebraicClosure ℚ))
    (z : ↥(NodeLocalized.coeffSubring A K)) (hz : NodeLocalized.redRestrict red K z ≠ 0) : IsUnit z := by
  have hzA : (⟨(z : AlgebraicClosure ℚ), z.2.1⟩ : ↥A) ∉ maximalIdeal ↥A := fun h => hz ((hker _).mpr h)
  have hv1 : A.valuation (z : AlgebraicClosure ℚ) = 1 := by
    have hle := (A.valuation_le_one_iff _).mpr z.2.1
    have hnlt : ¬ A.valuation (z : AlgebraicClosure ℚ) < 1 := fun h => hzA ((A.valuation_lt_one_iff ⟨_, z.2.1⟩).mpr h)
    exact le_antisymm hle (not_lt.mp hnlt)
  have hz0 : (z : AlgebraicClosure ℚ) ≠ 0 := fun h => by rw [h, map_zero] at hv1; exact zero_ne_one hv1
  have hinvA : (z : AlgebraicClosure ℚ)⁻¹ ∈ A := (A.valuation_le_one_iff _).mp (by rw [map_inv₀, hv1, inv_one])
  have hinvK : (z : AlgebraicClosure ℚ)⁻¹ ∈ K := inv_mem (show (z : AlgebraicClosure ℚ) ∈ K from z.2.2)
  exact isUnit_iff_exists_inv.mpr ⟨⟨(z : AlgebraicClosure ℚ)⁻¹, hinvA, hinvK⟩, Subtype.ext (mul_inv_cancel₀ hz0)⟩

theorem exists_eq_pow_mul_unit_of_mul_eq (A : ValuationSubring (AlgebraicClosure ℚ)) (red : A →+* k)
    (hker : ∀ c : A, red c = 0 ↔ c ∈ maximalIdeal A) (K : IntermediateField ℚ (AlgebraicClosure ℚ))
    (ϖ : ↥(NodeLocalized.coeffSubring A K)) (hϖ : ∀ d : ↥(NodeLocalized.coeffSubring A K), NodeLocalized.redRestrict red K d = 0 ↔ ∃ d', d = ϖ * d')
    (hϖ0 : ϖ ≠ 0) :
    ∀ (m : ℕ) (z w η : ↥(NodeLocalized.coeffSubring A K)), IsUnit η → z * w = ϖ ^ m * η →
      ∃ (n : ℕ) (θ : ↥(NodeLocalized.coeffSubring A K)), IsUnit θ ∧ z = ϖ ^ n * θ := by
  intro m
  induction m with
  | zero =>
    intro z w η hη h
    rw [pow_zero, one_mul] at h
    exact ⟨0, z, isUnit_of_mul_isUnit_left (h ▸ hη), by rw [pow_zero, one_mul]⟩
  | succ m ih =>
    intro z w η hη h
    by_cases hz : NodeLocalized.redRestrict red K z = 0
    · obtain ⟨z₁, rfl⟩ := (hϖ z).mp hz
      have h' : z₁ * w = ϖ ^ m * η := by
        apply mul_left_cancel₀ hϖ0
        calc ϖ * (z₁ * w) = ϖ * z₁ * w := by ring
          _ = ϖ ^ (m + 1) * η := h
          _ = ϖ * (ϖ ^ m * η) := by ring
      obtain ⟨n, θ, hθ, rfl⟩ := ih z₁ w η hη h'
      exact ⟨n + 1, θ, hθ, by ring⟩
    · exact ⟨0, z, isUnit_coeffSubring_of_red_ne_zero A red hker K z hz, by rw [pow_zero, one_mul]⟩

theorem unif_transfer (A : ValuationSubring (AlgebraicClosure ℚ)) (red : A →+* k)
    (hker : ∀ c : A, red c = 0 ↔ c ∈ maximalIdeal A)
    {K K' : IntermediateField ℚ (AlgebraicClosure ℚ)} (hle : NodeLocalized.coeffSubring A K ≤ NodeLocalized.coeffSubring A K')
    (q : ℕ) (hq : q ≠ 0)
    (ϖ : ↥(NodeLocalized.coeffSubring A K)) (eK : ℕ) (heK : 1 ≤ eK) (ε : ↥(NodeLocalized.coeffSubring A K)) (hε : IsUnit ε)
    (hqϖ : ((q : ℕ) : ↥(NodeLocalized.coeffSubring A K)) = ϖ ^ eK * ε)
    (ϖ' : ↥(NodeLocalized.coeffSubring A K'))
    (hϖ' : ∀ d : ↥(NodeLocalized.coeffSubring A K'), NodeLocalized.redRestrict red K' d = 0 ↔ ∃ d', d = ϖ' * d')
    (eK' : ℕ) (heK' : 1 ≤ eK') (ε' : ↥(NodeLocalized.coeffSubring A K')) (hε' : IsUnit ε')
    (hqϖ' : ((q : ℕ) : ↥(NodeLocalized.coeffSubring A K')) = ϖ' ^ eK' * ε') :
    ∃ (a : ℕ) (θ : ↥(NodeLocalized.coeffSubring A K')), IsUnit θ ∧ Subring.inclusion hle ϖ = ϖ' ^ a * θ ∧ a * eK = eK' := by
  have hϖ'0 : ϖ' ≠ 0 := by
    intro h0
    have h := congrArg (fun z : ↥(NodeLocalized.coeffSubring A K') => (z : AlgebraicClosure ℚ)) hqϖ'
    simp only [Subring.coe_natCast, h0, ZeroMemClass.coe_zero,
      zero_pow (Nat.one_le_iff_ne_zero.mp heK'), zero_mul] at h
    exact (Nat.cast_ne_zero.mpr hq) h
  obtain ⟨a, θ, hθ, ha⟩ := exists_eq_pow_mul_unit_of_mul_eq A red hker K' ϖ' hϖ' hϖ'0 eK'
    (Subring.inclusion hle ϖ) (Subring.inclusion hle (ϖ ^ (eK - 1) * ε)) ε' hε' (by
      rw [← map_mul, ← mul_assoc, ← pow_succ', Nat.sub_add_cancel heK, ← hqϖ, map_natCast, hqϖ'])
  refine ⟨a, θ, hθ, ha, ?_⟩
  have hvu : ∀ η : ↥(NodeLocalized.coeffSubring A K'), IsUnit η → A.valuation (η : AlgebraicClosure ℚ) = 1 := by
    intro η hη
    obtain ⟨b, hb⟩ := hη.exists_right_inv
    have h := congrArg (fun z : ↥(NodeLocalized.coeffSubring A K') => A.valuation (z : AlgebraicClosure ℚ)) hb
    simp only [Subring.coe_mul, Subring.coe_one, map_mul, map_one] at h
    exact eq_one_of_mul_eq_one_of_le_one ((A.valuation_le_one_iff _).mpr η.2.1) ((A.valuation_le_one_iff _).mpr b.2.1) h
  have hv1 : A.valuation (ϖ' : AlgebraicClosure ℚ) < 1 := by
    have hred : NodeLocalized.redRestrict red K' ϖ' = 0 := (hϖ' ϖ').mpr ⟨1, (mul_one _).symm⟩
    have hmem := (hker _).mp hred
    exact (A.valuation_lt_one_iff _).mp hmem
  have hv0 : A.valuation (ϖ' : AlgebraicClosure ℚ) ≠ 0 := (map_ne_zero _).mpr fun h => hϖ'0 (Subtype.ext h)
  have hvε : A.valuation (ε : AlgebraicClosure ℚ) = 1 := by
    simpa only [Subring.coe_inclusion] using hvu (Subring.inclusion hle ε) (hε.map _)
  have hq2 : (ϖ' : AlgebraicClosure ℚ) ^ (a * eK) * ((θ : AlgebraicClosure ℚ) ^ eK * (ε : AlgebraicClosure ℚ)) =
      (ϖ' : AlgebraicClosure ℚ) ^ eK' * (ε' : AlgebraicClosure ℚ) := by
    have h1 := congrArg (fun z : ↥(NodeLocalized.coeffSubring A K) => (z : AlgebraicClosure ℚ)) hqϖ
    have h2 := congrArg (fun z : ↥(NodeLocalized.coeffSubring A K') => (z : AlgebraicClosure ℚ)) hqϖ'
    have h3 := congrArg (fun z : ↥(NodeLocalized.coeffSubring A K') => (z : AlgebraicClosure ℚ)) ha
    simp only [Subring.coe_natCast, Subring.coe_mul, Subring.coe_pow, Subring.coe_inclusion] at h1 h2 h3
    rw [← h2, h1, h3]; ring
  have hv := congrArg A.valuation hq2
  rw [map_mul, map_mul, map_mul, map_pow, map_pow, map_pow, hvu θ hθ, hvε, hvu ε' hε', one_pow, one_mul,
    mul_one, mul_one] at hv
  have hinj := zpow_right_injective₀ (zero_lt_iff.mpr hv0) hv1.ne
  have : ((a * eK : ℕ) : ℤ) = ((eK' : ℕ) : ℤ) := hinj (by simp only [zpow_natCast]; exact hv)
  exact_mod_cast this

end UnifTransfer

section Pres
variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
  {k : Type*} [Field k] [CharP k q] [PerfectField k] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
  {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
  {P : PlaceSpecialization A q N data hKr k red hα hβ}

set_option maxHeartbeats 3200000 in

theorem presentation_over (R : ProlongationTuple P) [IsAlgClosed k] [DecidableEq k] (hqN : ¬ q ∣ N) (hmodel : R.IsModel)
    (W₀ : Finset (Place k (modularFunctionFieldC k N))) (hW₀ : ∀ v ∈ W₀, v ∈ ssPlaces q N k)
    (hreg : R.RegularityLaw W₀) (hval : R.NodeValueLaw W₀)
    (hker : ∀ c : A, red c = 0 ↔ c ∈ maximalIdeal A)
    (K K' : IntermediateField ℚ (AlgebraicClosure ℚ)) (hKK' : K ≤ K') [FiniteDimensional ℚ K']
    (w : Place k (modularFunctionFieldC k N)) (hw : w ∈ W₀)
    [hloc : IsLocalRing ↥(R.nodeIntegersOver K' w)] [hnoe : IsNoetherianRing ↥(R.nodeIntegersOver K' w)]
    (hres : ∀ g : ↥(R.nodeIntegersOver K' w), ∃ o : ↥(NodeLocalized.coeffSubring A K'), ¬ IsUnit (g - R.nodeConst K' w o))
    (ϖ : ↥(NodeLocalized.coeffSubring A K)) (eK : ℕ) (heK : 1 ≤ eK) (ε : ↥(NodeLocalized.coeffSubring A K)) (hε : IsUnit ε)
    (hqϖ : ((q : ℕ) : ↥(NodeLocalized.coeffSubring A K)) = ϖ ^ eK * ε)
    (ϖ' : ↥(NodeLocalized.coeffSubring A K'))
    (hϖ' : ∀ d : ↥(NodeLocalized.coeffSubring A K'), NodeLocalized.redRestrict red K' d = 0 ↔ ∃ d', d = ϖ' * d')
    (eK' : ℕ) (heK' : 1 ≤ eK') (ε' : ↥(NodeLocalized.coeffSubring A K')) (hε' : IsUnit ε')
    (hqϖ' : ((q : ℕ) : ↥(NodeLocalized.coeffSubring A K')) = ϖ' ^ eK' * ε')
    (c : R.NodeCoordinates K w) (ew : ℕ)
    (u : ↥(R.nodeIntegersOver K w)) (hu : IsUnit u) (hxy : c.x * c.y = R.nodeConst K w ϖ ^ (ew * eK) * u)
    (hcp : ∃ c'' : R.NodeCoordinates K' w,
            Ideal.span {R.nodeConst K' w ϖ', c''.x} = Ideal.span {R.nodeConst K' w ϖ', (enlargeCoordinates R hKK' c).x} ∧
            Ideal.span {R.nodeConst K' w ϖ', c''.y} = Ideal.span {R.nodeConst K' w ϖ', (enlargeCoordinates R hKK' c).y} ∧
          ∃ (eK : ℕ) (ε : ↥(NodeLocalized.coeffSubring A K')), 1 ≤ eK ∧ IsUnit ε ∧
            ((q : ℕ) : ↥(NodeLocalized.coeffSubring A K')) = ϖ' ^ eK * ε ∧
          ∃ (E : ℕ) (u : ↥(R.nodeIntegersOver K' w)), 1 ≤ E ∧ IsUnit u ∧ c''.x * c''.y = R.nodeConst K' w ϖ' ^ E * u ∧
            (Ideal.span {R.nodeConst K' w ϖ', c''.x, c''.y}).IsMaximal ∧
            (∀ M : Ideal ↥(R.nodeIntegersOver K' w), M.IsMaximal → M = Ideal.span {R.nodeConst K' w ϖ', c''.x, c''.y}) ∧
            (Ideal.span {R.nodeConst K' w ϖ', c''.x}).IsPrime ∧ (Ideal.span {R.nodeConst K' w ϖ', c''.y}).IsPrime ∧
            c''.y ∉ Ideal.span {R.nodeConst K' w ϖ', c''.x} ∧ c''.x ∉ Ideal.span {R.nodeConst K' w ϖ', c''.y}) :
    ∃ (u' : ↥(R.nodeIntegersOver K' w)) (_ : IsUnit u')
      (_ : (c.x : ↥(modularFunctionFieldBar (N * q))) * c.y =
        (R.nodeConst K' w ϖ' : ↥(modularFunctionFieldBar (N * q))) ^ (ew * eK') * u')
      (_ : (Ideal.span {R.nodeConst K' w ϖ',
            Subring.inclusion (nodeIntegersOver_mono R hKK' w) c.x,
            Subring.inclusion (nodeIntegersOver_mono R hKK' w) c.y}).IsMaximal ∧
        ∀ M : Ideal ↥(R.nodeIntegersOver K' w), M.IsMaximal →
          M = Ideal.span {R.nodeConst K' w ϖ',
            Subring.inclusion (nodeIntegersOver_mono R hKK' w) c.x,
            Subring.inclusion (nodeIntegersOver_mono R hKK' w) c.y})
      (_ : (Ideal.span {R.nodeConst K' w ϖ',
            Subring.inclusion (nodeIntegersOver_mono R hKK' w) c.x}).IsPrime ∧
        (Ideal.span {R.nodeConst K' w ϖ',
            Subring.inclusion (nodeIntegersOver_mono R hKK' w) c.y}).IsPrime ∧
        (Subring.inclusion (nodeIntegersOver_mono R hKK' w) c.y : ↥(R.nodeIntegersOver K' w)) ∉
          Ideal.span {R.nodeConst K' w ϖ', Subring.inclusion (nodeIntegersOver_mono R hKK' w) c.x} ∧
        (Subring.inclusion (nodeIntegersOver_mono R hKK' w) c.x : ↥(R.nodeIntegersOver K' w)) ∉
          Ideal.span {R.nodeConst K' w ϖ', Subring.inclusion (nodeIntegersOver_mono R hKK' w) c.y})
      (_ : IsLocalRing ↥(R.nodeIntegersOver K' w)) (_ : IsNoetherianRing ↥(R.nodeIntegersOver K' w)),
      ∀ g : ↥(R.nodeIntegersOver K' w), ∃ o : ↥(NodeLocalized.coeffSubring A K'),
        ¬ IsUnit (g - R.nodeConst K' w o)  := by
  have hq0 : q ≠ 0 := (Fact.out : q.Prime).ne_zero
  have hle : NodeLocalized.coeffSubring A K ≤ NodeLocalized.coeffSubring A K' := fun z hz => ⟨hz.1, hKK' hz.2⟩

  obtain ⟨c'', hbx, hby, -, -, -, -, -, -, -, -, -, -, hmax, hmaxu, hpx, hpy, hyx, hxy2⟩ := hcp
  simp only [enlargeCoordinates] at hbx hby
  rw [show Subring.inclusion (nodeIntegersOver_mono R hKK' w) c.x = ⟨c.x, nodeIntegersOver_mono R hKK' w c.x.2⟩ from rfl,
    show Subring.inclusion (nodeIntegersOver_mono R hKK' w) c.y = ⟨c.y, nodeIntegersOver_mono R hKK' w c.y.2⟩ from rfl]

  obtain ⟨a, θ, hθ, ha, haK⟩ :=
    unif_transfer A red hker hle q hq0 ϖ eK heK ε hε hqϖ ϖ' hϖ' eK' heK' ε' hε' hqϖ'
  refine ⟨R.nodeConst K' w θ ^ (ew * eK) * Subring.inclusion (nodeIntegersOver_mono R hKK' w) u,
    ((hθ.map _).pow _).mul (hu.map _), ?_, ?_, ?_, hloc, hnoe, hres⟩
  ·
    have h1 := congrArg (fun z : ↥(R.nodeIntegersOver K w) => (z : ↥(modularFunctionFieldBar (N * q)))) hxy
    have h2 := congrArg (fun z : ↥(NodeLocalized.coeffSubring A K') => (z : AlgebraicClosure ℚ)) ha
    simp only [Subring.coe_mul, Subring.coe_pow, ProlongationTuple.coe_nodeConst, Subring.coe_inclusion] at h1 h2 ⊢
    rw [h1, h2, ← haK, map_mul, map_pow]; ring
  ·
    have h3 : ∀ a X Y : ↥(R.nodeIntegersOver K' w), Ideal.span {a, X, Y} = Ideal.span {a, X} ⊔ Ideal.span {a, Y} := by
      intro a X Y; simp only [Ideal.span_insert]; rw [sup_sup_sup_comm, sup_idem]
    rw [h3, ← hbx, ← hby, ← h3]; exact ⟨hmax, hmaxu⟩
  ·
    rw [← hbx, ← hby]
    refine ⟨hpx, hpy, fun hY => hyx ?_, fun hX => hxy2 ?_⟩
    · have hle' : Ideal.span {R.nodeConst K' w ϖ', c''.y} ≤ Ideal.span {R.nodeConst K' w ϖ', c''.x} := by
        rw [hby, Ideal.span_le]
        intro z hz
        rcases hz with rfl | rfl
        · exact Ideal.subset_span (Set.mem_insert _ _)
        · exact hY
      exact hle' (Ideal.subset_span (by simp))
    · have hle' : Ideal.span {R.nodeConst K' w ϖ', c''.x} ≤ Ideal.span {R.nodeConst K' w ϖ', c''.y} := by
        rw [hbx, Ideal.span_le]
        intro z hz
        rcases hz with rfl | rfl
        · exact Ideal.subset_span (Set.mem_insert _ _)
        · exact hX
      exact hle' (Ideal.subset_span (by simp))

end Pres

section Iface
variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
  {k : Type*} [Field k] [CharP k q] [PerfectField k] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
  {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
  {P : PlaceSpecialization A q N data hKr k red hα hβ}

omit [PerfectField k] in

theorem valuation_natCast_zpow_injective (R : ProlongationTuple P) :
    Function.Injective fun n : ℤ => A.valuation (((q : ℕ) : AlgebraicClosure ℚ)) ^ n := by
  have hq0 : A.valuation (((q : ℕ) : AlgebraicClosure ℚ)) ≠ 0 :=
    (map_ne_zero _).mpr (Nat.cast_ne_zero.mpr (Fact.out : q.Prime).ne_zero)
  have hq1 : A.valuation (((q : ℕ) : AlgebraicClosure ℚ)) < 1 := by
    have hmem : ((q : ℕ) : ↥A) ∈ maximalIdeal ↥A := (red_eq_zero_iff R _).mp (by rw [map_natCast, CharP.cast_eq_zero])
    have := (A.valuation_lt_one_iff _).mp hmem
    simpa using this
  exact zpow_right_injective₀ (zero_lt_iff.mpr hq0) hq1.ne

end Iface

section BookB
variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
  {k : Type*} [Field k] [CharP k q] [PerfectField k] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q}
  {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
  {P : PlaceSpecialization A q 1 data hKr k red hα hβ}

theorem degree_eq_sum_of_deg_eq_one {K F : Type*} [Field K] [Field F] [Algebra K F]
    (h1 : ∀ v : Place K F, v.deg = 1) (D : Divisor K F) : Divisor.degree D = D.sum fun _ n => n := by
  simp only [Divisor.degree, Finsupp.liftAddHom_apply, AddMonoidHom.coe_mulRight, h1, Nat.cast_one, mul_one]

set_option maxHeartbeats 3200000 in

theorem bookA (R : ProlongationTuple P) [IsAlgClosed k] [DecidableEq k] (hq1 : ¬ q ∣ 1) (hmodel : R.IsModel) (hO : R.OrderLawFixed)
    (W : Finset (Place k (modularFunctionFieldC k 1))) (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q 1 k)
    (f : ↥(modularFunctionFieldBar (1 * q))) (hf : f ≠ 0)
    (c₁ : AlgebraicClosure ℚ) (h₁ : c₁ • f ∈ R.R₁.integers) (hu₁ : R.R₁.residue ⟨c₁ • f, h₁⟩ ≠ 0)
    (D : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))) (hDf : ∀ V, D V = V.ord f)
    (hsupp : ∀ V ∈ D.support,
        P.IsStrictFst V ∨ P.IsStrictSnd V ∨
          (P.reduceFst V ∈ W ∧
            ∀ σ ∈ A.inertiaSubgroupIn ℚ, arithmeticGalois (modularFunctionFieldFull (1 * q)) σ • V = V)) :
    Divisor.degree (P.fstDiv D) =
      ∑ s : ↥(nodePairsOfPlaces (arithFrobC q k 1) W),
        -(((s : Place k (modularFunctionFieldC k 1) × Place k (modularFunctionFieldC k 1)).1).ord (R.residue₁ ⟨c₁ • f, h₁⟩)) := by
  classical
  have hc₁ : c₁ ≠ 0 := by
    rintro rfl
    exact hu₁ (by rw [show (⟨(0 : AlgebraicClosure ℚ) • f, h₁⟩ : ↥R.R₁.integers) = 0 from Subtype.ext (zero_smul _ f), map_zero])
  have hDf' : ∀ V, D V = V.ord (c₁ • f) := fun V => by rw [hDf V, Place.ord_smul_of_ne_zero V hc₁]
  have hg : (R.residue₁ ⟨c₁ • f, h₁⟩) ≠ 0 := by
    rw [ProlongationTuple.residue₁_apply]; exact (map_ne_zero R.ι).mpr hu₁
  haveI hCurve : IsCurveOver k ↥(modularFunctionFieldC k 1) := isCurveOver_modularFunctionFieldC_of_good k 1 q hq1
  haveI hCurveBar : IsCurveOver (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) :=
    isCurveOver_laurentBaseChange_modularFunctionFieldFull (AlgebraicClosure ℚ) (1 * q)
  have hdeg1 : ∀ v : Place k ↥(modularFunctionFieldC k 1), v.deg = 1 := IsCurveOver.deg_eq_one_of_isAlgClosed
  have hdeg1' : ∀ V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)), V.deg = 1 := IsCurveOver.deg_eq_one_of_isAlgClosed
  obtain ⟨Dg, hDg, hdeg⟩ := HasPrincipalDivisors.exists_divisor (K := k) (R.residue₁ ⟨c₁ • f, h₁⟩) hg

  have hna_fix : ∀ v : Place k ↥(modularFunctionFieldC k 1), ¬ IsAffineGeomPlace k 1 v → (frobOnPlacesGeomLevel k 1 data hKr) v = v := by
    intro v hv
    apply ModularCurve.CharPModel.frobOnPlacesGeomLevel_eq_self_of_ord_jqModC_neg k 1 data hKr squarefree_one hq1 v
    have hj : (jGeomGen k 1 : ↥(modularFunctionFieldC k 1)) ∉ v.toValuationSubring := fun h =>
      hv (by unfold IsAffineGeomPlace; exact ⟨h, by rw [jNGeomGen_one]; exact h⟩)
    exact (v.not_adicValuation_le_one_iff).mp fun hle => hj (v.mem_iff_adicValuation_le_one.mpr hle)
  have hss_aff : ∀ v ∈ ssPlaces q 1 k, IsAffineGeomPlace k 1 v := fun v hv => (show IsSupersingularPlace q 1 k v from hv).2.1

  have hexc : ∀ V ∈ D.support, (frobOnPlacesGeomLevel k 1 data hKr) ((frobOnPlacesGeomLevel k 1 data hKr) (P.reduceFst V)) = P.reduceFst V → P.reduceFst V ∈ ssPlaces q 1 k := by
    intro V hV hfix
    rcases hsupp V hV with hS | hS | ⟨hVW, -⟩
    · exact absurd hfix hS.2
    · exact absurd hfix (ModularCurve.PlaceSpecialization.not_fixed_reduceFst_of_isStrictSnd P V hS)
    · exact (hW _).mp hVW
  have hexc' : ∀ V, (frobOnPlacesGeomLevel k 1 data hKr) ((frobOnPlacesGeomLevel k 1 data hKr) (P.reduceFst V)) = P.reduceFst V → P.reduceFst V ∉ ssPlaces q 1 k → D V = 0 :=
    fun V h1 h2 => by_contra fun hD => h2 (hexc V (Finsupp.mem_support_iff.mpr hD) h1)

  have hfix0 : ∀ v : Place k ↥(modularFunctionFieldC k 1), (frobOnPlacesGeomLevel k 1 data hKr) ((frobOnPlacesGeomLevel k 1 data hKr) v) = v → v ∉ W → v.ord (R.residue₁ ⟨c₁ • f, h₁⟩) = 0 := by
    intro v hv hvW
    by_cases haff : IsAffineGeomPlace k 1 v
    · have hvss : v ∉ ssPlaces q 1 k := fun h => hvW ((hW v).mpr h)
      have hu1 : ∀ {M : ℕ} [NeZero M], q = M → modularUnitSeries q ∈ modularFunctionFieldFull M := by
        rintro M _ rfl; exact modularUnitSeries_mem_modularFunctionFieldFull q
      have key := ProlongationTuple.mapDomain_reduceFst_filter_sheetOne_eq_ord_residueFst_levelOne_univ P R hmodel hO
        ⟨coeffEmb (AlgebraicClosure ℚ) (modularUnitSeries q), coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (hu1 (Nat.one_mul q).symm)⟩ rfl
        (c₁ • f) h₁ hu₁ D hDf' v hv haff hvss
      rw [(Finsupp.filter_eq_zero_iff _ _).mpr ?_, Finsupp.mapDomain_zero, Finsupp.zero_apply] at key
      · exact key.symm
      · intro V hV; exact hexc' V hV.1.1 hV.1.2.2
    · obtain ⟨⟨C, hC, hCv⟩, -⟩ :=
        ModularCurve.PlaceSpecialization.exists_isInftySide_reduceFst_eq_and_isZeroSide_reduceSnd_eq_of_not_isAffineGeomPlace hq1 P v haff
      have key := ProlongationTuple.cuspLawInfty_oneSided_levelOne P R hmodel (c₁ • f) h₁ hu₁ D hDf' C hC
      rw [(Finsupp.filter_eq_zero_iff _ _).mpr ?_, Finsupp.mapDomain_zero, Finsupp.zero_apply, hCv] at key
      · exact key.symm
      · intro V hV
        have hna := ModularCurve.PlaceSpecialization.ProlongationTuple.not_isAffineGeomPlace_reduceFst_of_isCuspidal P V hV.1
        exact hexc' V (by rw [hna_fix _ hna, hna_fix _ hna]) fun h => hna (hss_aff _ h)

  have hE : Finsupp.mapDomain P.reduceFst (P.fstDiv D) = Dg.filter (fun v => (frobOnPlacesGeomLevel k 1 data hKr) ((frobOnPlacesGeomLevel k 1 data hKr) v) ≠ v) := by
    ext v
    rw [Finsupp.filter_apply]
    split_ifs with hv
    · rw [hDg v]; exact ProlongationTuple.divisorLawFst_oneSided_levelOne P R hmodel (c₁ • f) h₁ hu₁ D hDf' v hv
    · by_contra hne
      obtain ⟨V, hVS, hVv⟩ := Finset.mem_image.mp (Finsupp.mapDomain_support (Finsupp.mem_support_iff.mpr hne))
      simp only [PlaceSpecialization.fstDiv, Finsupp.support_filter, Finset.mem_filter] at hVS
      exact hv (by rw [← hVv]; exact hVS.2.2)

  rw [degree_eq_sum_of_deg_eq_one hdeg1' (P.fstDiv D),
    show (P.fstDiv D).sum (fun _ n => n) = (Finsupp.mapDomain P.reduceFst (P.fstDiv D)).sum (fun _ n => n) from
      (Finsupp.sum_mapDomain_index (h := fun _ n => n) (fun _ => rfl) (fun _ _ _ => rfl)).symm, hE]

  have h0 : Dg.sum (fun _ n => n) = 0 := by rw [← degree_eq_sum_of_deg_eq_one hdeg1 Dg]; exact hdeg
  have hsplit : Dg.sum (fun _ n => n) =
      (Dg.filter (fun v => (frobOnPlacesGeomLevel k 1 data hKr) ((frobOnPlacesGeomLevel k 1 data hKr) v) ≠ v)).sum (fun _ n => n) +
        (Dg.filter (fun v => ¬ ((frobOnPlacesGeomLevel k 1 data hKr) ((frobOnPlacesGeomLevel k 1 data hKr) v) ≠ v))).sum (fun _ n => n) := by
    conv_lhs => rw [← Finsupp.filter_add_filter_not Dg (fun v => (frobOnPlacesGeomLevel k 1 data hKr) ((frobOnPlacesGeomLevel k 1 data hKr) v) ≠ v)]
    exact Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl)
  have hfixW : (Dg.filter (fun v => ¬ ((frobOnPlacesGeomLevel k 1 data hKr) ((frobOnPlacesGeomLevel k 1 data hKr) v) ≠ v))).sum (fun _ n => n) = ∑ w ∈ W, w.ord (R.residue₁ ⟨c₁ • f, h₁⟩) := by
    have hS : (Dg.filter (fun v => ¬ ((frobOnPlacesGeomLevel k 1 data hKr) ((frobOnPlacesGeomLevel k 1 data hKr) v) ≠ v))).support = W.filter (fun w => Dg w ≠ 0) := by
      ext v
      rw [Finsupp.support_filter, Finset.mem_filter, Finset.mem_filter, Finsupp.mem_support_iff, not_not]
      constructor
      · rintro ⟨hD, hv⟩
        refine ⟨by_contra fun hvW => hD ?_, hD⟩
        rw [hDg]; exact hfix0 v hv hvW
      · rintro ⟨hvW, hD⟩
        exact ⟨hD, frobOnPlacesGeomLevel_frobOnPlacesGeomLevel_eq_self_of_mem_ssPlaces_of_isAlgClosed k 1 hq1 data hKr v ((hW v).mp hvW)⟩
    rw [Finsupp.sum, hS]
    calc ∑ v ∈ W.filter (fun w => Dg w ≠ 0), (Dg.filter (fun v => ¬ ((frobOnPlacesGeomLevel k 1 data hKr) ((frobOnPlacesGeomLevel k 1 data hKr) v) ≠ v))) v
        = ∑ v ∈ W.filter (fun w => Dg w ≠ 0), Dg v := Finset.sum_congr rfl fun v hv => by
            rw [Finsupp.filter_apply, if_pos]
            exact not_not.mpr (frobOnPlacesGeomLevel_frobOnPlacesGeomLevel_eq_self_of_mem_ssPlaces_of_isAlgClosed
              k 1 hq1 data hKr v ((hW v).mp (Finset.mem_filter.mp hv).1))
      _ = ∑ v ∈ W, Dg v := by rw [Finset.sum_filter_ne_zero]
      _ = ∑ w ∈ W, w.ord (R.residue₁ ⟨c₁ • f, h₁⟩) := Finset.sum_congr rfl fun v _ => hDg v
  have hnf : (Dg.filter (fun v => (frobOnPlacesGeomLevel k 1 data hKr) ((frobOnPlacesGeomLevel k 1 data hKr) v) ≠ v)).sum (fun _ n => n) = -∑ w ∈ W, w.ord (R.residue₁ ⟨c₁ • f, h₁⟩) := by
    rw [← hfixW]; linarith [h0, hsplit]
  rw [hnf, ← Finset.sum_neg_distrib]

  symm
  calc ∑ s : ↥(nodePairsOfPlaces (arithFrobC q k 1) W),
        -(((s : Place k ↥(modularFunctionFieldC k 1) × Place k ↥(modularFunctionFieldC k 1)).1).ord (R.residue₁ ⟨c₁ • f, h₁⟩))
      = ∑ w : ↥W, -((w : Place k ↥(modularFunctionFieldC k 1)).ord (R.residue₁ ⟨c₁ • f, h₁⟩)) := by
        refine (Fintype.sum_equiv (nodeEquivOfPlaces (arithFrobC q k 1) W) _ _ fun w => ?_).symm
        simp only [coe_nodeEquivOfPlaces_apply, smulNodePair_fst]
    _ = ∑ w ∈ W, -(w.ord (R.residue₁ ⟨c₁ • f, h₁⟩)) := Finset.sum_coe_sort W (fun w => -(w.ord (R.residue₁ ⟨c₁ • f, h₁⟩)))

set_option maxHeartbeats 3200000 in

theorem bookB (R : ProlongationTuple P) [IsAlgClosed k] [DecidableEq k] (hq1 : ¬ q ∣ 1) (hmodel : R.IsModel) (hO : R.OrderLawFixed)
    (W : Finset (Place k (modularFunctionFieldC k 1))) (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q 1 k)
    (f : ↥(modularFunctionFieldBar (1 * q))) (hf : f ≠ 0)
    (c₂ : AlgebraicClosure ℚ) (h₂ : c₂ • f ∈ R.R₂.integers) (hu₂ : R.R₂.residue ⟨c₂ • f, h₂⟩ ≠ 0)
    (D : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))) (hDf : ∀ V, D V = V.ord f)
    (hsupp : ∀ V ∈ D.support,
        P.IsStrictFst V ∨ P.IsStrictSnd V ∨
          (P.reduceFst V ∈ W ∧
            ∀ σ ∈ A.inertiaSubgroupIn ℚ, arithmeticGalois (modularFunctionFieldFull (1 * q)) σ • V = V)) :
    Divisor.degree (P.sndDiv D) =
      ∑ s : ↥(nodePairsOfPlaces (arithFrobC q k 1) W),
        -((arithFrobC q k 1 • (s : Place k (modularFunctionFieldC k 1) × Place k (modularFunctionFieldC k 1)).1).ord
            (R.residue₂ ⟨c₂ • f, h₂⟩)) := by
  classical

  have hc₂ : c₂ ≠ 0 := by
    rintro rfl
    exact hu₂ (by rw [show (⟨(0 : AlgebraicClosure ℚ) • f, h₂⟩ : ↥R.R₂.integers) = 0 from Subtype.ext (zero_smul _ f), map_zero])
  have hDf' : ∀ V, D V = V.ord (c₂ • f) := fun V => by rw [hDf V, Place.ord_smul_of_ne_zero V hc₂]
  have hg : (R.residue₂ ⟨c₂ • f, h₂⟩) ≠ 0 := by
    rw [ProlongationTuple.residue₂_apply]; exact (map_ne_zero R.ι).mpr hu₂

  haveI hCurve : IsCurveOver k ↥(modularFunctionFieldC k 1) := isCurveOver_modularFunctionFieldC_of_good k 1 q hq1
  haveI hCurveBar : IsCurveOver (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) :=
    isCurveOver_laurentBaseChange_modularFunctionFieldFull (AlgebraicClosure ℚ) (1 * q)
  have hdeg1 : ∀ v : Place k ↥(modularFunctionFieldC k 1), v.deg = 1 := IsCurveOver.deg_eq_one_of_isAlgClosed
  have hdeg1' : ∀ V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)), V.deg = 1 := IsCurveOver.deg_eq_one_of_isAlgClosed
  obtain ⟨Dg, hDg, hdeg⟩ := HasPrincipalDivisors.exists_divisor (K := k) (R.residue₂ ⟨c₂ • f, h₂⟩) hg
  have φinj := frobOnPlacesGeomLevel_injective k 1 data hKr

  have hna_fix : ∀ v : Place k ↥(modularFunctionFieldC k 1), ¬ IsAffineGeomPlace k 1 v → (frobOnPlacesGeomLevel k 1 data hKr) v = v := by
    intro v hv
    apply ModularCurve.CharPModel.frobOnPlacesGeomLevel_eq_self_of_ord_jqModC_neg k 1 data hKr squarefree_one hq1 v
    have hj : (jGeomGen k 1 : ↥(modularFunctionFieldC k 1)) ∉ v.toValuationSubring := fun h =>
      hv (by unfold IsAffineGeomPlace; exact ⟨h, by rw [jNGeomGen_one]; exact h⟩)
    exact (v.not_adicValuation_le_one_iff).mp fun hle => hj (v.mem_iff_adicValuation_le_one.mpr hle)

  have hzs_na : ∀ V, ProlongationTuple.IsZeroSide P V → ¬ IsAffineGeomPlace k 1 (P.reduceSnd V) := by
    intro V hV haff
    obtain ⟨a, ha, -⟩ := ModularCurve.PlaceSpecialization.exists_ord_jQFun_sub_pos_of_isAffineGeomPlace_reduceSnd P V haff
    exact (lt_irrefl _) (lt_of_lt_of_le ha (hV.1 a))

  have hss_aff : ∀ v ∈ ssPlaces q 1 k, IsAffineGeomPlace k 1 v := fun v hv => (show IsSupersingularPlace q 1 k v from hv).2.1
  have hmaps : ∀ w ∈ W, arithFrobC q k 1 • w ∈ W := fun w hw =>
    (hW _).mpr (arithFrobC_smul_mem_ssPlaces_univ q 1 k _ ((hW w).mp hw))

  have hexc : ∀ V ∈ D.support, (frobOnPlacesGeomLevel k 1 data hKr) ((frobOnPlacesGeomLevel k 1 data hKr) (P.reduceSnd V)) = P.reduceSnd V → P.reduceSnd V ∈ ssPlaces q 1 k := by
    intro V hV hfix
    rcases hsupp V hV with hS | hS | ⟨hVW, -⟩
    · exfalso
      apply hS.2
      apply φinj
      rw [hS.1]; exact hfix
    · exact absurd hfix hS.2
    · have hss : P.reduceFst V ∈ ssPlaces q 1 k := (hW _).mp hVW
      have hφss : (frobOnPlacesGeomLevel k 1 data hKr) (P.reduceFst V) ∈ ssPlaces q 1 k := by
        rw [← arithFrobC_smul_eq_frobOnPlacesGeomLevel q k 1 data hKr]
        exact arithFrobC_smul_mem_ssPlaces_univ q 1 k _ hss
      rcases P.d1 V with h | h
      · change P.reduceFst V = (frobOnPlacesGeomLevel k 1 data hKr) (P.reduceSnd V) at h
        rw [show P.reduceSnd V = (frobOnPlacesGeomLevel k 1 data hKr) (P.reduceFst V) by rw [h, hfix]]
        exact hφss
      · change (frobOnPlacesGeomLevel k 1 data hKr) (P.reduceFst V) = P.reduceSnd V at h
        rw [← h]; exact hφss
  have hexc' : ∀ V, (frobOnPlacesGeomLevel k 1 data hKr) ((frobOnPlacesGeomLevel k 1 data hKr) (P.reduceSnd V)) = P.reduceSnd V → P.reduceSnd V ∉ ssPlaces q 1 k → D V = 0 :=
    fun V h1 h2 => by_contra fun hD => h2 (hexc V (Finsupp.mem_support_iff.mpr hD) h1)

  have hfix0 : ∀ v : Place k ↥(modularFunctionFieldC k 1), (frobOnPlacesGeomLevel k 1 data hKr) ((frobOnPlacesGeomLevel k 1 data hKr) v) = v → v ∉ W → v.ord (R.residue₂ ⟨c₂ • f, h₂⟩) = 0 := by
    intro v hv hvW
    by_cases haff : IsAffineGeomPlace k 1 v
    · have hvss : v ∉ ssPlaces q 1 k := fun h => hvW ((hW v).mpr h)
      have hu1 : ∀ {M : ℕ} [NeZero M], q = M → modularUnitSeries q ∈ modularFunctionFieldFull M := by
        rintro M _ rfl; exact modularUnitSeries_mem_modularFunctionFieldFull q
      have key := ProlongationTuple.mapDomain_reduceSnd_filter_sheetTwo_eq_ord_residueSnd_levelOne P R hmodel hO
        ⟨coeffEmb (AlgebraicClosure ℚ) (modularUnitSeries q), coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (hu1 (Nat.one_mul q).symm)⟩ rfl
        (c₂ • f) h₂ hu₂ D hDf' v hv haff hvss
      rw [(Finsupp.filter_eq_zero_iff _ _).mpr ?_, Finsupp.mapDomain_zero, Finsupp.zero_apply] at key
      · exact key.symm
      · intro V hV; exact hexc' V hV.1.1 hV.1.2.2
    · obtain ⟨-, C, hC, hCv⟩ :=
        ModularCurve.PlaceSpecialization.exists_isInftySide_reduceFst_eq_and_isZeroSide_reduceSnd_eq_of_not_isAffineGeomPlace hq1 P v haff
      have key := ProlongationTuple.cuspLawZero_oneSided_levelOne P R hmodel (c₂ • f) h₂ hu₂ D hDf' C hC
      rw [(Finsupp.filter_eq_zero_iff _ _).mpr ?_, Finsupp.mapDomain_zero, Finsupp.zero_apply, hCv] at key
      · exact key.symm
      · intro V hV
        have hna := hzs_na V hV
        exact hexc' V (by rw [hna_fix _ hna, hna_fix _ hna]) fun h => hna (hss_aff _ h)

  have hE : Finsupp.mapDomain P.reduceSnd (P.sndDiv D) = Dg.filter (fun v => (frobOnPlacesGeomLevel k 1 data hKr) ((frobOnPlacesGeomLevel k 1 data hKr) v) ≠ v) := by
    ext v
    rw [Finsupp.filter_apply]
    split_ifs with hv
    · rw [hDg v]; exact ProlongationTuple.divisorLawSnd_oneSided_levelOne P R hmodel (c₂ • f) h₂ hu₂ D hDf' v hv
    · by_contra hne
      obtain ⟨V, hVS, hVv⟩ := Finset.mem_image.mp (Finsupp.mapDomain_support (Finsupp.mem_support_iff.mpr hne))
      simp only [PlaceSpecialization.sndDiv, Finsupp.support_filter, Finset.mem_filter] at hVS
      exact hv (by rw [← hVv]; exact hVS.2.2)

  rw [degree_eq_sum_of_deg_eq_one hdeg1' (P.sndDiv D),
    show (P.sndDiv D).sum (fun _ n => n) = (Finsupp.mapDomain P.reduceSnd (P.sndDiv D)).sum (fun _ n => n) from
      (Finsupp.sum_mapDomain_index (h := fun _ n => n) (fun _ => rfl) (fun _ _ _ => rfl)).symm, hE]

  have h0 : Dg.sum (fun _ n => n) = 0 := by rw [← degree_eq_sum_of_deg_eq_one hdeg1 Dg]; exact hdeg
  have hsplit : Dg.sum (fun _ n => n) =
      (Dg.filter (fun v => (frobOnPlacesGeomLevel k 1 data hKr) ((frobOnPlacesGeomLevel k 1 data hKr) v) ≠ v)).sum (fun _ n => n) +
        (Dg.filter (fun v => ¬ ((frobOnPlacesGeomLevel k 1 data hKr) ((frobOnPlacesGeomLevel k 1 data hKr) v) ≠ v))).sum (fun _ n => n) := by
    conv_lhs => rw [← Finsupp.filter_add_filter_not Dg (fun v => (frobOnPlacesGeomLevel k 1 data hKr) ((frobOnPlacesGeomLevel k 1 data hKr) v) ≠ v)]
    exact Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl)
  have hfixW : (Dg.filter (fun v => ¬ ((frobOnPlacesGeomLevel k 1 data hKr) ((frobOnPlacesGeomLevel k 1 data hKr) v) ≠ v))).sum (fun _ n => n) = ∑ w ∈ W, w.ord (R.residue₂ ⟨c₂ • f, h₂⟩) := by
    have hS : (Dg.filter (fun v => ¬ ((frobOnPlacesGeomLevel k 1 data hKr) ((frobOnPlacesGeomLevel k 1 data hKr) v) ≠ v))).support = W.filter (fun w => Dg w ≠ 0) := by
      ext v
      rw [Finsupp.support_filter, Finset.mem_filter, Finset.mem_filter, Finsupp.mem_support_iff, not_not]
      constructor
      · rintro ⟨hD, hv⟩
        refine ⟨by_contra fun hvW => hD ?_, hD⟩
        rw [hDg]; exact hfix0 v hv hvW
      · rintro ⟨hvW, hD⟩
        exact ⟨hD, frobOnPlacesGeomLevel_frobOnPlacesGeomLevel_eq_self_of_mem_ssPlaces_of_isAlgClosed k 1 hq1 data hKr v ((hW v).mp hvW)⟩
    rw [Finsupp.sum, hS]
    calc ∑ v ∈ W.filter (fun w => Dg w ≠ 0), (Dg.filter (fun v => ¬ ((frobOnPlacesGeomLevel k 1 data hKr) ((frobOnPlacesGeomLevel k 1 data hKr) v) ≠ v))) v
        = ∑ v ∈ W.filter (fun w => Dg w ≠ 0), Dg v := Finset.sum_congr rfl fun v hv => by
            rw [Finsupp.filter_apply, if_pos]
            exact not_not.mpr (frobOnPlacesGeomLevel_frobOnPlacesGeomLevel_eq_self_of_mem_ssPlaces_of_isAlgClosed
              k 1 hq1 data hKr v ((hW v).mp (Finset.mem_filter.mp hv).1))
      _ = ∑ v ∈ W, Dg v := by rw [Finset.sum_filter_ne_zero]
      _ = ∑ w ∈ W, w.ord (R.residue₂ ⟨c₂ • f, h₂⟩) := Finset.sum_congr rfl fun v _ => hDg v
  have hnf : (Dg.filter (fun v => (frobOnPlacesGeomLevel k 1 data hKr) ((frobOnPlacesGeomLevel k 1 data hKr) v) ≠ v)).sum (fun _ n => n) = -∑ w ∈ W, w.ord (R.residue₂ ⟨c₂ • f, h₂⟩) := by
    rw [← hfixW]; linarith [h0, hsplit]
  rw [hnf, ← Finset.sum_neg_distrib]

  let eWf : ↥W → ↥W := fun w => ⟨arithFrobC q k 1 • (w : Place k ↥(modularFunctionFieldC k 1)), hmaps _ w.2⟩
  have heinj : Function.Injective eWf := fun a b h =>
    Subtype.ext (MulAction.injective (arithFrobC q k 1) (congrArg Subtype.val h))
  let eW : ↥W ≃ ↥W := Equiv.ofBijective eWf (Finite.injective_iff_bijective.mp heinj)
  symm
  calc ∑ s : ↥(nodePairsOfPlaces (arithFrobC q k 1) W),
        -((arithFrobC q k 1 • (s : Place k ↥(modularFunctionFieldC k 1) × Place k ↥(modularFunctionFieldC k 1)).1).ord (R.residue₂ ⟨c₂ • f, h₂⟩))
      = ∑ w : ↥W, -((arithFrobC q k 1 • (w : Place k ↥(modularFunctionFieldC k 1))).ord (R.residue₂ ⟨c₂ • f, h₂⟩)) := by
        refine (Fintype.sum_equiv (nodeEquivOfPlaces (arithFrobC q k 1) W) _ _ fun w => ?_).symm
        simp only [coe_nodeEquivOfPlaces_apply, smulNodePair_fst]
    _ = ∑ w : ↥W, -(((eW w : ↥W) : Place k ↥(modularFunctionFieldC k 1)).ord (R.residue₂ ⟨c₂ • f, h₂⟩)) := rfl
    _ = ∑ w : ↥W, -((w : Place k ↥(modularFunctionFieldC k 1)).ord (R.residue₂ ⟨c₂ • f, h₂⟩)) := Equiv.sum_comp eW (fun w : ↥W => -((w : Place k ↥(modularFunctionFieldC k 1)).ord (R.residue₂ ⟨c₂ • f, h₂⟩)))
    _ = ∑ w ∈ W, -(w.ord (R.residue₂ ⟨c₂ • f, h₂⟩)) := Finset.sum_coe_sort W (fun w => -(w.ord (R.residue₂ ⟨c₂ • f, h₂⟩)))

open Classical in
set_option maxHeartbeats 3200000 in

theorem squeeze (R : ProlongationTuple P) [IsAlgClosed k] [DecidableEq k] (hq1 : ¬ q ∣ 1) (hmodel : R.IsModel) (hO : R.OrderLawFixed)
    (W : Finset (Place k (modularFunctionFieldC k 1))) (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q 1 k)
    (f : ↥(modularFunctionFieldBar (1 * q))) (hf : f ≠ 0)
    (c₁ : AlgebraicClosure ℚ) (h₁ : c₁ • f ∈ R.R₁.integers) (hu₁ : R.R₁.residue ⟨c₁ • f, h₁⟩ ≠ 0)
    (c₂ : AlgebraicClosure ℚ) (h₂ : c₂ • f ∈ R.R₂.integers) (hu₂ : R.R₂.residue ⟨c₂ • f, h₂⟩ ≠ 0)
    (D : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))) (hDf : ∀ V, D V = V.ord f)
    (hsupp : ∀ V ∈ D.support,
        P.IsStrictFst V ∨ P.IsStrictSnd V ∨
          (P.reduceFst V ∈ W ∧
            ∀ σ ∈ A.inertiaSubgroupIn ℚ, arithmeticGalois (modularFunctionFieldFull (1 * q)) σ • V = V))
    (hle : ∀ s : ↥(nodePairsOfPlaces (arithFrobC q k 1) W), (∑ V ∈ D.support with P.reduceFst V = (s : Place k (modularFunctionFieldC k 1) × Place k (modularFunctionFieldC k 1)).1, D V) ≤ ((s : Place k (modularFunctionFieldC k 1) × Place k (modularFunctionFieldC k 1)).1).ord (R.residue₁ ⟨c₁ • f, h₁⟩) + (arithFrobC q k 1 • (s : Place k (modularFunctionFieldC k 1) × Place k (modularFunctionFieldC k 1)).1).ord (R.residue₂ ⟨c₂ • f, h₂⟩)) :
    ∀ s : ↥(nodePairsOfPlaces (arithFrobC q k 1) W), (∑ V ∈ D.support with P.reduceFst V = (s : Place k (modularFunctionFieldC k 1) × Place k (modularFunctionFieldC k 1)).1, D V) = ((s : Place k (modularFunctionFieldC k 1) × Place k (modularFunctionFieldC k 1)).1).ord (R.residue₁ ⟨c₁ • f, h₁⟩) + (arithFrobC q k 1 • (s : Place k (modularFunctionFieldC k 1) × Place k (modularFunctionFieldC k 1)).1).ord (R.residue₂ ⟨c₂ • f, h₂⟩) := by
  classical

  suffices htot : ∑ s : ↥(nodePairsOfPlaces (arithFrobC q k 1) W), (∑ V ∈ D.support with P.reduceFst V = (s : Place k (modularFunctionFieldC k 1) × Place k (modularFunctionFieldC k 1)).1, D V) =
      ∑ s : ↥(nodePairsOfPlaces (arithFrobC q k 1) W), (((s : Place k (modularFunctionFieldC k 1) × Place k (modularFunctionFieldC k 1)).1).ord (R.residue₁ ⟨c₁ • f, h₁⟩) + (arithFrobC q k 1 • (s : Place k (modularFunctionFieldC k 1) × Place k (modularFunctionFieldC k 1)).1).ord (R.residue₂ ⟨c₂ • f, h₂⟩)) by
    have := (Finset.sum_eq_sum_iff_of_le (fun s _ => hle s)).mp htot
    exact fun s => this s (Finset.mem_univ s)

  have hA := bookA R hq1 hmodel hO W hW f hf c₁ h₁ hu₁ D hDf hsupp
  have hB := bookB R hq1 hmodel hO W hW f hf c₂ h₂ hu₂ D hDf hsupp
  rw [Finset.sum_add_distrib,
    show ∑ s : ↥(nodePairsOfPlaces (arithFrobC q k 1) W), ((s : Place k (modularFunctionFieldC k 1) × Place k (modularFunctionFieldC k 1)).1).ord (R.residue₁ ⟨c₁ • f, h₁⟩) = -Divisor.degree (P.fstDiv D) by
      rw [hA, Finset.sum_neg_distrib, neg_neg],
    show ∑ s : ↥(nodePairsOfPlaces (arithFrobC q k 1) W), (arithFrobC q k 1 • (s : Place k (modularFunctionFieldC k 1) × Place k (modularFunctionFieldC k 1)).1).ord (R.residue₂ ⟨c₂ • f, h₂⟩) =
        -Divisor.degree (P.sndDiv D) by
      rw [hB, Finset.sum_neg_distrib, neg_neg]]

  haveI hCurveBar : IsCurveOver (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) :=
    isCurveOver_laurentBaseChange_modularFunctionFieldFull (AlgebraicClosure ℚ) (1 * q)
  have hdeg1' : ∀ V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)), V.deg = 1 := IsCurveOver.deg_eq_one_of_isAlgClosed
  have hsumS : ∀ (p : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) → Prop) {_ : DecidablePred p},
      Divisor.degree (D.filter p) = ∑ V ∈ D.support with p V, D V := by
    intro p _
    rw [degree_eq_sum_of_deg_eq_one hdeg1', Finsupp.sum, Finsupp.support_filter]
    exact Finset.sum_congr rfl fun V hV => by rw [Finsupp.filter_apply, if_pos (Finset.mem_filter.mp hV).2]
  have hdeg0 : ∑ V ∈ D.support, D V = 0 := by
    obtain ⟨D', hD', hdeg'⟩ := HasPrincipalDivisors.exists_divisor (K := AlgebraicClosure ℚ) f hf
    have hDD' : D = D' := Finsupp.ext fun V => by rw [hDf V, hD' V]
    rw [← hdeg', ← hDD', degree_eq_sum_of_deg_eq_one hdeg1', Finsupp.sum]

  have h21 : ∀ V, P.IsStrictSnd V → ¬ P.IsStrictFst V := by
    intro V h2 h1
    apply h2.2
    have e1 : (frobOnPlacesGeomLevel k 1 data hKr) (P.reduceFst V) = P.reduceSnd V := h1.1
    have e2 : P.reduceFst V = (frobOnPlacesGeomLevel k 1 data hKr) (P.reduceSnd V) := h2.1
    rw [e2] at e1; exact e1
  have h31 : ∀ V, P.reduceFst V ∈ W → ¬ P.IsStrictFst V := fun V h3 h1 =>
    h1.2 (frobOnPlacesGeomLevel_frobOnPlacesGeomLevel_eq_self_of_mem_ssPlaces_of_isAlgClosed k 1 hq1 data hKr _ ((hW _).mp h3))
  have h32 : ∀ V, P.reduceFst V ∈ W → ¬ P.IsStrictSnd V := fun V h3 h2 =>
    (ModularCurve.PlaceSpecialization.not_fixed_reduceFst_of_isStrictSnd P V h2)
      (frobOnPlacesGeomLevel_frobOnPlacesGeomLevel_eq_self_of_mem_ssPlaces_of_isAlgClosed k 1 hq1 data hKr _ ((hW _).mp h3))
  have hsplit : ∑ V ∈ D.support, D V =
      (∑ V ∈ D.support with P.IsStrictFst V, D V) + (∑ V ∈ D.support with P.IsStrictSnd V, D V) +
        ∑ V ∈ D.support with P.reduceFst V ∈ W, D V := by
    rw [← Finset.sum_filter_add_sum_filter_not D.support P.IsStrictFst,
      ← Finset.sum_filter_add_sum_filter_not (D.support.filter fun V => ¬ P.IsStrictFst V) P.IsStrictSnd,
      Finset.filter_filter, Finset.filter_filter, add_assoc]
    congr 2
    · exact Finset.sum_congr (Finset.filter_congr fun V _ => ⟨fun h => h.2, fun h => ⟨h21 V h, h⟩⟩) fun _ _ => rfl
    · exact Finset.sum_congr (Finset.filter_congr fun V hV =>
        ⟨fun h => ((hsupp V hV).resolve_left h.1).resolve_left h.2 |>.1, fun h => ⟨h31 V h, h32 V h⟩⟩) fun _ _ => rfl
  have hnodal : ∑ s : ↥(nodePairsOfPlaces (arithFrobC q k 1) W), (∑ V ∈ D.support with P.reduceFst V = (s : Place k (modularFunctionFieldC k 1) × Place k (modularFunctionFieldC k 1)).1, D V) =
      ∑ V ∈ D.support with P.reduceFst V ∈ W, D V := by
    calc ∑ s : ↥(nodePairsOfPlaces (arithFrobC q k 1) W), (∑ V ∈ D.support with P.reduceFst V = (s : Place k (modularFunctionFieldC k 1) × Place k (modularFunctionFieldC k 1)).1, D V)
        = ∑ w : ↥W, ∑ V ∈ D.support with P.reduceFst V = (w : Place k ↥(modularFunctionFieldC k 1)), D V := by
          refine (Fintype.sum_equiv (nodeEquivOfPlaces (arithFrobC q k 1) W) _ _ fun w => ?_).symm
          simp only [coe_nodeEquivOfPlaces_apply, smulNodePair_fst]
      _ = ∑ w ∈ W, ∑ V ∈ D.support with P.reduceFst V = w, D V :=
          Finset.sum_coe_sort W (fun w => ∑ V ∈ D.support with P.reduceFst V = w, D V)
      _ = ∑ w ∈ W, ∑ V ∈ (D.support.filter fun V => P.reduceFst V ∈ W) with P.reduceFst V = w, D V := by
          refine Finset.sum_congr rfl fun w hw => Finset.sum_congr ?_ fun _ _ => rfl
          rw [Finset.filter_filter]
          exact Finset.filter_congr fun V _ => ⟨fun h => ⟨h ▸ hw, h⟩, fun h => h.2⟩
      _ = ∑ V ∈ D.support with P.reduceFst V ∈ W, D V :=
          Finset.sum_fiberwise_of_maps_to (fun V hV => (Finset.mem_filter.mp hV).2) _
  rw [hnodal]
  have e1 : Divisor.degree (P.fstDiv D) = ∑ V ∈ D.support with P.IsStrictFst V, D V := hsumS _
  have e2 : Divisor.degree (P.sndDiv D) = ∑ V ∈ D.support with P.IsStrictSnd V, D V := hsumS _
  rw [e1, e2]; linarith [hsplit, hdeg0]

end BookB

end R1Skel

set_option maxHeartbeats 12800000 in
theorem solution
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] [PerfectField k] [IsAlgClosed k] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
    (P : PlaceSpecialization A q 1 data hKr k red hα hβ)
    (R : ProlongationTuple P) [DecidableEq k] (hqN : ¬ q ∣ 1) (hq : 5 ≤ q)
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
    (f : ↥(modularFunctionFieldBar (1 * q))) (hf : f ≠ 0)
    (D : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))) (hDf : ∀ V, D V = V.ord f)

    (hsupp : ∀ V ∈ D.support,
        P.IsStrictFst V ∨ P.IsStrictSnd V ∨
          (P.reduceFst V ∈ W ∧
            ∀ σ ∈ A.inertiaSubgroupIn ℚ, arithmeticGalois (modularFunctionFieldFull (1 * q)) σ • V = V))
    (s₀ : ↥(nodePairsOfPlaces (arithFrobC q k 1) W)) :
    componentGroupProj (widthOfPlaces (arithFrobC q k 1) W e)
        (P.depthDual (arithFrobC q k 1) W depth D +
          Divisor.degree (P.sndDiv D) •
            (((e (s₀ : Place k (modularFunctionFieldC k 1) × Place k (modularFunctionFieldC k 1)).1 : ℕ) : ℤ) •
              crossingCoord s₀)) = 0 := by
  classical

  let Z : ↥(nodePairsOfPlaces (arithFrobC q k 1) W) → ℕ → ℤ := fun s d =>
    ∑ V ∈ D.support with (P.reduceFst V =
        (s : Place k (modularFunctionFieldC k 1) × Place k (modularFunctionFieldC k 1)).1 ∧ depth V = d), D V

  have hwidth : ∀ s : ↥(nodePairsOfPlaces (arithFrobC q k 1) W),
      widthOfPlaces (arithFrobC q k 1) W e s =
        e (s : Place k (modularFunctionFieldC k 1) × Place k (modularFunctionFieldC k 1)).1 := fun s => rfl
  have he' : ∀ s : ↥(nodePairsOfPlaces (arithFrobC q k 1) W), 1 ≤ widthOfPlaces (arithFrobC q k 1) W e s :=
    fun s => he _ (fst_mem_of_mem_nodePairsOfPlaces s.2)

  have hGauss : ∃ (G : ↥(nodePairsOfPlaces (arithFrobC q k 1) W) → ℕ → ℤ) (δ : ℤ),
      (∀ s, G s (widthOfPlaces (arithFrobC q k 1) W e s) - G s 0 = δ) ∧
      (∀ s, ∀ d ∈ Finset.Ico 1 (widthOfPlaces (arithFrobC q k 1) W e s),
          (G s d - G s (d - 1)) - (G s (d + 1) - G s d) = Z s d) ∧
      (∑ s, (G s (widthOfPlaces (arithFrobC q k 1) W e s) - G s (widthOfPlaces (arithFrobC q k 1) W e s - 1))) =
        Divisor.degree (P.sndDiv D) := by

    have hker := R1Skel.red_eq_zero_iff R
    obtain ⟨c₁, h₁, hu₁⟩ := R.R₁.exists_smul_mem f hf
    obtain ⟨c₂, h₂, hu₂⟩ := R.R₂.exists_smul_mem f hf
    have hc₁0 : c₁ ≠ 0 := by
      rintro rfl
      exact hu₁ (by rw [show (⟨(0 : AlgebraicClosure ℚ) • f, h₁⟩ : ↥R.R₁.integers) = 0 from Subtype.ext (zero_smul _ f), map_zero])
    have hc₂0 : c₂ ≠ 0 := by
      rintro rfl
      exact hu₂ (by rw [show (⟨(0 : AlgebraicClosure ℚ) • f, h₂⟩ : ↥R.R₂.integers) = 0 from Subtype.ext (zero_smul _ f), map_zero])
    have hwφ : ∀ s : ↥(nodePairsOfPlaces (arithFrobC q k 1) W), ∀ hw : (s : Place k (modularFunctionFieldC k 1) × Place k (modularFunctionFieldC k 1)).1 ∈ W, arithFrobC q k 1 • (s : Place k (modularFunctionFieldC k 1) × Place k (modularFunctionFieldC k 1)).1 ∈ W :=
      fun s hw => (hW _).mpr (ModularCurve.arithFrobC_smul_mem_ssPlaces_univ q 1 k _ ((hW _).mp hw))
    obtain ⟨Kf, hKf, hfKf, -⟩ :=
      ModularCurve.exists_finiteDimensional_mem_fieldOver_and_redRestrict_eq A red (red 0) ⟨0, rfl⟩ f
    haveI := hKf

    obtain ⟨K₀, hK₀fd, -, hK₀⟩ :=
      ModularCurve.NodeLocalized.exists_finiteDimensional_forall_inertia_apply_eq_and_mem_range_redRestrict q A k red
        (W.image fun w => w.evalAt (jGeomGen k 1)) (by
          intro a ha
          obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp ha
          exact ModularCurve.pow_q_sq_eq_self_of_mem_ssJSet q (show IsSupersingularPlace q 1 k w from (hW w).mp hw).2.2)
    haveI := hK₀fd
    obtain ⟨K', hK'fd, hKK', hKfK', hK₀K', hc₁, hc₂⟩ := R1Skel.exists_finiteDimensional_sup₃ K Kf K₀ c₁ c₂
    haveI := hK'fd
    have hKres : ∀ w ∈ W, w.evalAt (jGeomGen k 1) ∈ Set.range (NodeLocalized.redRestrict red K') := fun w hw =>
      R1Skel.range_redRestrict_mono hK₀K' (hK₀ _ (Finset.mem_image_of_mem _ hw))
    have hKresN : ∀ w ∈ W, w.evalAt (jNGeomGen k 1) ∈ Set.range (NodeLocalized.redRestrict red K') := fun w hw => by
      rw [jNGeomGen_one]; exact hKres w hw
    have hfK' := R1Skel.fieldOver_mono (1 * q) hKfK' hfKf
    obtain ⟨ϖ', hϖ', eK', ε', heK', hε', hqϖ'⟩ :=
      ModularCurve.NodeLocalized.exists_forall_redRestrict_eq_zero_iff_and_natCast_eq_pow_mul red hker K'

    have hpres : ∀ s : ↥(nodePairsOfPlaces (arithFrobC q k 1) W), ∀ hw : (s : Place k (modularFunctionFieldC k 1) × Place k (modularFunctionFieldC k 1)).1 ∈ W,
        ∃ (u' : ↥(R.nodeIntegersOver K' (s : Place k (modularFunctionFieldC k 1) × Place k (modularFunctionFieldC k 1)).1)) (_ : IsUnit u')
          (_ : ((cs _ hw).x : ↥(modularFunctionFieldBar (1 * q))) * (cs _ hw).y =
            (R.nodeConst K' (s : Place k (modularFunctionFieldC k 1) × Place k (modularFunctionFieldC k 1)).1 ϖ' : ↥(modularFunctionFieldBar (1 * q))) ^ (e (s : Place k (modularFunctionFieldC k 1) × Place k (modularFunctionFieldC k 1)).1 * eK') * u')
          (_ : (Ideal.span {R.nodeConst K' (s : Place k (modularFunctionFieldC k 1) × Place k (modularFunctionFieldC k 1)).1 ϖ',
                Subring.inclusion (R1Skel.nodeIntegersOver_mono R hKK' (s : Place k (modularFunctionFieldC k 1) × Place k (modularFunctionFieldC k 1)).1) (cs _ hw).x,
                Subring.inclusion (R1Skel.nodeIntegersOver_mono R hKK' (s : Place k (modularFunctionFieldC k 1) × Place k (modularFunctionFieldC k 1)).1) (cs _ hw).y}).IsMaximal ∧
            ∀ M : Ideal ↥(R.nodeIntegersOver K' (s : Place k (modularFunctionFieldC k 1) × Place k (modularFunctionFieldC k 1)).1), M.IsMaximal →
              M = Ideal.span {R.nodeConst K' (s : Place k (modularFunctionFieldC k 1) × Place k (modularFunctionFieldC k 1)).1 ϖ',
                Subring.inclusion (R1Skel.nodeIntegersOver_mono R hKK' (s : Place k (modularFunctionFieldC k 1) × Place k (modularFunctionFieldC k 1)).1) (cs _ hw).x,
                Subring.inclusion (R1Skel.nodeIntegersOver_mono R hKK' (s : Place k (modularFunctionFieldC k 1) × Place k (modularFunctionFieldC k 1)).1) (cs _ hw).y})
          (_ : (Ideal.span {R.nodeConst K' (s : Place k (modularFunctionFieldC k 1) × Place k (modularFunctionFieldC k 1)).1 ϖ',
                Subring.inclusion (R1Skel.nodeIntegersOver_mono R hKK' (s : Place k (modularFunctionFieldC k 1) × Place k (modularFunctionFieldC k 1)).1) (cs _ hw).x}).IsPrime ∧
            (Ideal.span {R.nodeConst K' (s : Place k (modularFunctionFieldC k 1) × Place k (modularFunctionFieldC k 1)).1 ϖ',
                Subring.inclusion (R1Skel.nodeIntegersOver_mono R hKK' (s : Place k (modularFunctionFieldC k 1) × Place k (modularFunctionFieldC k 1)).1) (cs _ hw).y}).IsPrime ∧
            (Subring.inclusion (R1Skel.nodeIntegersOver_mono R hKK' (s : Place k (modularFunctionFieldC k 1) × Place k (modularFunctionFieldC k 1)).1) (cs _ hw).y : ↥(R.nodeIntegersOver K' (s : Place k (modularFunctionFieldC k 1) × Place k (modularFunctionFieldC k 1)).1)) ∉
              Ideal.span {R.nodeConst K' (s : Place k (modularFunctionFieldC k 1) × Place k (modularFunctionFieldC k 1)).1 ϖ', Subring.inclusion (R1Skel.nodeIntegersOver_mono R hKK' (s : Place k (modularFunctionFieldC k 1) × Place k (modularFunctionFieldC k 1)).1) (cs _ hw).x} ∧
            (Subring.inclusion (R1Skel.nodeIntegersOver_mono R hKK' (s : Place k (modularFunctionFieldC k 1) × Place k (modularFunctionFieldC k 1)).1) (cs _ hw).x : ↥(R.nodeIntegersOver K' (s : Place k (modularFunctionFieldC k 1) × Place k (modularFunctionFieldC k 1)).1)) ∉
              Ideal.span {R.nodeConst K' (s : Place k (modularFunctionFieldC k 1) × Place k (modularFunctionFieldC k 1)).1 ϖ', Subring.inclusion (R1Skel.nodeIntegersOver_mono R hKK' (s : Place k (modularFunctionFieldC k 1) × Place k (modularFunctionFieldC k 1)).1) (cs _ hw).y})
          (_ : IsLocalRing ↥(R.nodeIntegersOver K' (s : Place k (modularFunctionFieldC k 1) × Place k (modularFunctionFieldC k 1)).1)) (_ : IsNoetherianRing ↥(R.nodeIntegersOver K' (s : Place k (modularFunctionFieldC k 1) × Place k (modularFunctionFieldC k 1)).1)),
          ∀ g : ↥(R.nodeIntegersOver K' (s : Place k (modularFunctionFieldC k 1) × Place k (modularFunctionFieldC k 1)).1), ∃ o : ↥(NodeLocalized.coeffSubring A K'),
            ¬ IsUnit (g - R.nodeConst K' (s : Place k (modularFunctionFieldC k 1) × Place k (modularFunctionFieldC k 1)).1 o) := by
      intro s hw
      obtain ⟨u, hu, hxy0⟩ := hxy _ hw
      obtain ⟨xK, hxK⟩ := hKres _ hw
      obtain ⟨hloc, hnoe⟩ := ModularCurve.PlaceSpecialization.ProlongationTuple.isLocalRing_and_isNoetherianRing_nodeIntegersOver_levelOne
        R hR W (fun w hw => (hW w).mp hw) hreg K' (s : Place k (modularFunctionFieldC k 1) × Place k (modularFunctionFieldC k 1)).1 hw _ rfl xK hxK
      haveI := hloc
      haveI := hnoe

      obtain ⟨v₁, hv₁⟩ := P.d4 (s : Place k (modularFunctionFieldC k 1) × Place k (modularFunctionFieldC k 1)).1
      obtain ⟨V, hV⟩ := AlgebraicCurve.Place.restrictAlong_surjective (heckeAlphaBar (AlgebraicClosure ℚ) 1 q) hα
        (ModularCurve.finiteAlong_heckeAlphaBar_of_prime (AlgebraicClosure ℚ) 1 q)
        (AlgebraicCurve.separableAlong_of_charZero _ hα) v₁
      have hVw : P.reduceFst V = (s : Place k (modularFunctionFieldC k 1) × Place k (modularFunctionFieldC k 1)).1 := (congrArg P.sp hV).trans hv₁
      have hres' := ModularCurve.PlaceSpecialization.ProlongationTuple.exists_not_isUnit_sub_nodeConst_of_evalAt_mem_range_redRestrict_levelOne_of_five_le
        R hq hO W (fun w hw => (hW w).mp hw) hreg K' (s : Place k (modularFunctionFieldC k 1) × Place k (modularFunctionFieldC k 1)).1 hw V hVw (hKres _ hw)
      exact R1Skel.presentation_over R hqN hR W (fun w hw => (hW w).mp hw) hreg hval hker K K' hKK'
        (s : Place k (modularFunctionFieldC k 1) × Place k (modularFunctionFieldC k 1)).1 hw hres' ϖ eK heK ε hε hqϖ ϖ' hϖ' eK' heK' ε' hε' hqϖ' (cs _ hw) (e (s : Place k (modularFunctionFieldC k 1) × Place k (modularFunctionFieldC k 1)).1) u hu hxy0
        (ModularCurve.PlaceSpecialization.ProlongationTuple.exists_crossingPresentation_nodeIntegersOver_levelOne
          R hq hR W (fun w hw => (hW w).mp hw) hreg hval K' (s : Place k (modularFunctionFieldC k 1) × Place k (modularFunctionFieldC k 1)).1 hw _ rfl xK hxK
          (R1Skel.enlargeCoordinates R hKK' (cs _ hw)) ϖ' hϖ')

    have hfrac : ∀ s : ↥(nodePairsOfPlaces (arithFrobC q k 1) W), ∀ hw : (s : Place k (modularFunctionFieldC k 1) × Place k (modularFunctionFieldC k 1)).1 ∈ W,
        ∀ z ∈ NodeLocalized.fieldOver (1 * q) K', ∃ x y : ↥(modularFunctionFieldBar (1 * q)),
          x ∈ R.nodeIntegersOver K' (s : Place k (modularFunctionFieldC k 1) × Place k (modularFunctionFieldC k 1)).1 ∧ y ∈ R.nodeIntegersOver K' (s : Place k (modularFunctionFieldC k 1) × Place k (modularFunctionFieldC k 1)).1 ∧ y ≠ 0 ∧
            z * ((y : ↥(modularFunctionFieldBar (1 * q))) : LaurentSeries (AlgebraicClosure ℚ)) =
              ((x : ↥(modularFunctionFieldBar (1 * q))) : LaurentSeries (AlgebraicClosure ℚ)) :=
      fun s hw z hz => ModularCurve.PlaceSpecialization.ProlongationTuple.exists_mul_eq_of_mem_fieldOver_nodeIntegersOver_levelOne
        R hqN K' (s : Place k (modularFunctionFieldC k 1) × Place k (modularFunctionFieldC k 1)).1 ((hW _).mp hw) z hz
    have hineq : ∀ s : ↥(nodePairsOfPlaces (arithFrobC q k 1) W),
        (∑ V ∈ D.support with P.reduceFst V = (s : Place k (modularFunctionFieldC k 1) × Place k (modularFunctionFieldC k 1)).1, D V) ≤
          ((s : Place k (modularFunctionFieldC k 1) × Place k (modularFunctionFieldC k 1)).1).ord (R.residue₁ ⟨c₁ • f, h₁⟩) + (arithFrobC q k 1 • (s : Place k (modularFunctionFieldC k 1) × Place k (modularFunctionFieldC k 1)).1).ord (R.residue₂ ⟨c₂ • f, h₂⟩) := by
      intro s
      have hw : (s : Place k (modularFunctionFieldC k 1) × Place k (modularFunctionFieldC k 1)).1 ∈ W := fst_mem_of_mem_nodePairsOfPlaces s.2
      obtain ⟨u', hu', hxy', hmax', hbr', hloc, hnoe, hres'⟩ := hpres s hw
      haveI := hloc
      haveI := hnoe
      exact ModularCurve.PlaceSpecialization.ProlongationTuple.sum_div_reduceFst_le_ord_residueFst_add_ord_residueSnd
        R hqN hR hO W (fun w hw => (hW w).mp hw) hreg hval K K' hKK' (s : Place k (modularFunctionFieldC k 1) × Place k (modularFunctionFieldC k 1)).1 hw (hwφ s hw) (hVI _ hw)
        (R1Skel.nodeIntegersOver_mono R hKK' (s : Place k (modularFunctionFieldC k 1) × Place k (modularFunctionFieldC k 1)).1)
        ϖ' hϖ' eK' heK' ε' hε' hqϖ' (cs _ hw) (widthOfPlaces (arithFrobC q k 1) W e s) (he _ hw) u' hu' hxy' hmax'
        (hmax'.2 _ (IsLocalRing.maximalIdeal.isMaximal _)) hbr' hres' depth (hdepth _ hw)
        f hf hfK' (hfrac s hw) c₁ c₂ h₁ hu₁ h₂ hu₂ hc₁ hc₂ hc₁0 hc₂0 D hDf
        (fun V hV hVw => R1Skel.fixed_of_strict_or_strict_or_fixed P hqN W hW V (hsupp V hV) (hVw ▸ hw))
    have hN := R1Skel.squeeze R hqN hR hO W hW f hf c₁ h₁ hu₁ c₂ h₂ hu₂ D hDf hsupp hineq

    have hnode : ∀ s : ↥(nodePairsOfPlaces (arithFrobC q k 1) W), ∃ G : ℕ → ℤ,
        (∀ d ∈ Finset.Ico 1 (widthOfPlaces (arithFrobC q k 1) W e s), (G d - G (d - 1)) - (G (d + 1) - G d) = Z s d) ∧
        G 1 - G 0 = ((s : Place k (modularFunctionFieldC k 1) × Place k (modularFunctionFieldC k 1)).1).ord (R.residue₁ ⟨c₁ • f, h₁⟩) ∧
        G (widthOfPlaces (arithFrobC q k 1) W e s) - G (widthOfPlaces (arithFrobC q k 1) W e s - 1) = -((arithFrobC q k 1 • (s : Place k (modularFunctionFieldC k 1) × Place k (modularFunctionFieldC k 1)).1).ord (R.residue₂ ⟨c₂ • f, h₂⟩)) ∧
        A.valuation (c₁ / c₂) = A.valuation (((q : ℕ) : AlgebraicClosure ℚ)) ^ (G (widthOfPlaces (arithFrobC q k 1) W e s) - G 0) := by
      intro s
      have hw : (s : Place k (modularFunctionFieldC k 1) × Place k (modularFunctionFieldC k 1)).1 ∈ W := fst_mem_of_mem_nodePairsOfPlaces s.2
      obtain ⟨u', hu', hxy', hmax', hbr', hloc, hnoe, hres'⟩ := hpres s hw
      haveI := hloc
      haveI := hnoe
      exact ModularCurve.PlaceSpecialization.ProlongationTuple.exists_slopeDrop_eq_sum_div_depth_of_sum_div_reduceFst_eq
        R hqN hR hO W (fun w hw => (hW w).mp hw) hreg hval K K' hKK' (s : Place k (modularFunctionFieldC k 1) × Place k (modularFunctionFieldC k 1)).1 hw (hwφ s hw) (hVI _ hw)
        (R1Skel.nodeIntegersOver_mono R hKK' (s : Place k (modularFunctionFieldC k 1) × Place k (modularFunctionFieldC k 1)).1)
        ϖ' hϖ' eK' heK' ε' hε' hqϖ' (cs _ hw) (widthOfPlaces (arithFrobC q k 1) W e s) (he _ hw) u' hu' hxy' hmax'
        (hmax'.2 _ (IsLocalRing.maximalIdeal.isMaximal _)) hbr' hres' depth (hdepth _ hw)
        f hf hfK' (hfrac s hw) c₁ c₂ h₁ hu₁ h₂ hu₂ hc₁ hc₂ hc₁0 hc₂0 D hDf
        (fun V hV hVw => R1Skel.fixed_of_strict_or_strict_or_fixed P hqN W hW V (hsupp V hV) (hVw ▸ hw)) (hN s)
    choose G hG using hnode

    have hδ : ∀ s, G s (widthOfPlaces (arithFrobC q k 1) W e s) - G s 0 = G s₀ (widthOfPlaces (arithFrobC q k 1) W e s₀) - G s₀ 0 := fun s =>
      R1Skel.valuation_natCast_zpow_injective R (((hG s).2.2.2).symm.trans (hG s₀).2.2.2)

    have hB := R1Skel.bookB R hqN hR hO W hW f hf c₂ h₂ hu₂ D hDf hsupp
    refine ⟨G, G s₀ (widthOfPlaces (arithFrobC q k 1) W e s₀) - G s₀ 0, hδ, fun s d hd => (hG s).1 d hd, ?_⟩
    rw [hB]
    exact Finset.sum_congr rfl fun s _ => (hG s).2.2.1

  have hA : ∀ s : ↥(nodePairsOfPlaces (arithFrobC q k 1) W),
      P.depthDiv depth D (s : Place k (modularFunctionFieldC k 1) × Place k (modularFunctionFieldC k 1)).1 =
        ∑ d ∈ Finset.Ico 1 (widthOfPlaces (arithFrobC q k 1) W e s), (d : ℤ) * Z s d := by
    intro s
    have hwW : (s : Place k (modularFunctionFieldC k 1) × Place k (modularFunctionFieldC k 1)).1 ∈ W := fst_mem_of_mem_nodePairsOfPlaces s.2
    obtain ⟨u, hu, hxy'⟩ := hxy _ hwW
    obtain ⟨hvq, hvε, hle, hne⟩ := R1Skel.coeff_valuation A K q (Fact.out : q.Prime).ne_zero ϖ ε eK heK hε hqϖ
    have hbound : ∀ V ∈ D.support, P.reduceFst V = (s : Place k (modularFunctionFieldC k 1) × Place k (modularFunctionFieldC k 1)).1 → depth V < e (s : Place k (modularFunctionFieldC k 1) × Place k (modularFunctionFieldC k 1)).1 := by
      intro V hV hVw
      have hfix := R1Skel.fixed_of_strict_or_strict_or_fixed P hqN W hW V (hsupp V hV) (hVw ▸ hwW)
      have h64 := ModularCurve.PlaceSpecialization.ProlongationTuple.nodeDepths_lt_one_and_partition_of_nodeEquation_of_orderLawFixed
        R hqN hR hO W (fun w hw => (hW w).mp hw) hreg hval K (s : Place k (modularFunctionFieldC k 1) × Place k (modularFunctionFieldC k 1)).1 hwW (hVI _ hwW) ϖ (cs _ hwW) (e (s : Place k (modularFunctionFieldC k 1) × Place k (modularFunctionFieldC k 1)).1 * eK) u hu hxy' V hVw
      exact (R1Skel.depth_window h64.1 h64.2.1 h64.2.2 (hdepth _ hwW V hVw hfix) hvq hvε hle hne).2
    exact R1Skel.depthDiv_apply_eq_sum_Ico P depth D (s : Place k (modularFunctionFieldC k 1) × Place k (modularFunctionFieldC k 1)).1 (e (s : Place k (modularFunctionFieldC k 1) × Place k (modularFunctionFieldC k 1)).1) (he _ hwW) hbound

  obtain ⟨G, δ, hδ, hdrop, hB⟩ := hGauss
  have L1 : ∑ s : ↥(nodePairsOfPlaces (arithFrobC q k 1) W),
      componentGroupProj (widthOfPlaces (arithFrobC q k 1) W e) (crossingCoord s) = 0 := by
    exact R1Skel.sum_componentGroupProj_crossingCoord _
  have L2 : ∀ s : ↥(nodePairsOfPlaces (arithFrobC q k 1) W),
      ((widthOfPlaces (arithFrobC q k 1) W e s : ℕ) : ℤ) •
          componentGroupProj (widthOfPlaces (arithFrobC q k 1) W e) (crossingCoord s) =
        componentGroupProj (widthOfPlaces (arithFrobC q k 1) W e)
          (((e (s₀ : Place k (modularFunctionFieldC k 1) × Place k (modularFunctionFieldC k 1)).1 : ℕ) : ℤ) •
            crossingCoord s₀) := by
    intro s
    exact R1Skel.smul_componentGroupProj_crossingCoord_eq _ s s₀
  have S4 := AnnulusSlope.sum_sum_mul_slopeDrop_smul_add_sum_slope_smul_eq_zero
    (fun s => componentGroupProj (widthOfPlaces (arithFrobC q k 1) W e) (crossingCoord s))
    (componentGroupProj (widthOfPlaces (arithFrobC q k 1) W e)
      (((e (s₀ : Place k (modularFunctionFieldC k 1) × Place k (modularFunctionFieldC k 1)).1 : ℕ) : ℤ) •
        crossingCoord s₀))
    (widthOfPlaces (arithFrobC q k 1) W e) he' L2 L1 G δ hδ

  have hdual : componentGroupProj (widthOfPlaces (arithFrobC q k 1) W e) (P.depthDual (arithFrobC q k 1) W depth D) =
      ∑ s, (∑ d ∈ Finset.Ico 1 (widthOfPlaces (arithFrobC q k 1) W e s),
        (d : ℤ) * ((G s d - G s (d - 1)) - (G s (d + 1) - G s d))) •
          componentGroupProj (widthOfPlaces (arithFrobC q k 1) W e) (crossingCoord s) := by
    simp only [depthDual, map_sum, map_zsmul]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [hA s]
    congr 1
    exact Finset.sum_congr rfl fun d hd => by rw [hdrop s d hd]
  rw [map_add, map_zsmul]
  exact (congrArg₂ (fun a (b : ℤ) => a + b • componentGroupProj (widthOfPlaces (arithFrobC q k 1) W e)
      (((e (s₀ : Place k (modularFunctionFieldC k 1) × Place k (modularFunctionFieldC k 1)).1 : ℕ) : ℤ) • crossingCoord s₀))
    hdual hB.symm).trans S4

end S_ModularCurve_PlaceSpecialization_componentGroupProj_depthDual_add_degree_sndDiv_smul_eq_zero_of_div_levelOne_of_five_le
end P2MW
export P2MW.S_ModularCurve_PlaceSpecialization_componentGroupProj_depthDual_add_degree_sndDiv_smul_eq_zero_of_div_levelOne_of_five_le (solution)
