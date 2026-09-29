-- Prove2me | solution 1 for ModularCurve.PlaceSpecialization.ProlongationTuple.AnnulusDatumLevel.exists_nodePackage_over_of_orderLawFixed
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/5e7b0341-dc1d-5c3d-82b8-afc6c3b0c987

import Mathlib
import Definitions.Def_ModularCurve_AnnulusSpecializationLevel
import Theorems.Thm_ModularCurve_NodeLocalized_isDiscreteValuationRing_coeffSubring
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_crossingPresentation_nodeIntegersOver_of_orderLawFixed_of_saturated
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_nodeResidue_saturated_of_orderLawFixed_of_isNoetherianRing
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_isLocalRing_and_isNoetherianRing_nodeIntegersOver_of_nodeCoordinates_of_orderLawFixed_of_range_redRestrict
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_not_isUnit_sub_nodeConst_of_evalAt_mem_range_redRestrict_of_orderLawFixed
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_mul_eq_of_mem_fieldOver_nodeIntegersOver
import Theorems.Thm_ModularCurve_NodeLocalized_exists_finiteDimensional_forall_inertia_apply_eq_and_mem_range_redRestrict
import Theorems.Thm_ModularCurve_exists_numberField_presentation_level
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_AnnulusDatumLevel_exists_nodePackage_over_of_orderLawFixed
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
p2m_attr_erase "simp" "GaloisRepAdic.mk.injEq GaloisRepAdic.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.injEq ResidualGaloisRep.mk.sizeOf_spec ResidualGaloisRep.mk.injEq ResidualGaloisRep.Equiv.mk.sizeOf_spec ResidualGaloisRep.Equiv.mk.injEq AlgebraicCurve.CurveModel.mk.injEq AlgebraicCurve.CurveModel.mk.sizeOf_spec ModularCurve.CharPModel.FibreModel.mk.injEq ModularCurve.CharPModel.FibreModel.mk.sizeOf_spec ModularCurve.IgusaScheme.ιInf_igusaTo_assoc ModularCurve.IgusaScheme.coe_jFull ModularCurve.IgusaScheme.coe_jInvChartInf ModularCurve.IgusaScheme.coe_jChartFin ModularCurve.IgusaScheme.ιFin_igusaTo ModularCurve.IgusaScheme.ιInf_igusaTo ModularCurve.IgusaScheme.ιFin_igusaTo_assoc AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces ValuationSubring.reduceAt_coe ValuationSubring.reduceAt_one ValuationSubring.reduceAt_natCast ValuationSubring.reduceAt_intCast ValuationSubring.reduceAt_zero"
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000
set_option autoImplicit false
set_option linter.unusedVariables false

open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.PlaceSpecialization ModularCurve.PlaceSpecialization.ProlongationTuple

namespace ChartOkPkg
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

end ChartOkPkg

namespace ChartOkPkg
open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.NodeLocalized ModularCurve.PlaceSpecialization ModularCurve.PlaceSpecialization.ProlongationTuple

local notation "Qb" => AlgebraicClosure ℚ

theorem modularEval_mem_fieldOver (M : ℕ) [NeZero M] (A : ValuationSubring Qb) (K : IntermediateField ℚ Qb)
    (p : MvPolynomial (Fin 2) ↥(coeffSubring A K)) : modularEval M (coeffSubring A K) p ∈ fieldOver M K := by
  induction p using MvPolynomial.induction_on with
  | C a =>
      unfold modularEval
      rw [MvPolynomial.eval₂Hom_C]
      apply Subfield.subset_closure
      left
      exact ⟨⟨(a : Qb), a.2.2⟩, rfl⟩
  | add p₁ p₂ hp₁ hp₂ => rw [map_add]; exact add_mem hp₁ hp₂
  | mul_X p i hp =>
      rw [map_mul]
      refine mul_mem hp ?_
      unfold modularEval
      rw [MvPolynomial.eval₂Hom_X']
      apply Subfield.subset_closure
      right
      fin_cases i
      · show jqModC Qb ∈ _
        exact Set.mem_insert _ _
      · show jqNModC Qb M ∈ _
        exact Set.mem_insert_of_mem _ (Set.mem_singleton _)

theorem exists_coeffField {q : ℕ} [Fact q.Prime] {N : ℕ} [NeZero N] (A : ValuationSubring Qb)
    {k : Type*} [Field k] [CharP k q] [DecidableEq k] (red : A →+* k)
    (K₀ : IntermediateField ℚ Qb) [FiniteDimensional ℚ K₀] (f : ↥(modularFunctionFieldBar (N * q)))
    (c₁ c₂ : Qb) :
    ∃ (K' : IntermediateField ℚ Qb) (_ : FiniteDimensional ℚ K') (_ : K₀ ≤ K')
      (_ : (f : LaurentSeries Qb) ∈ fieldOver (N * q) K') (_ : c₁ ∈ K') (_ : c₂ ∈ K'),
      ∀ a : k, a ^ (q ^ 2) = a → a ∈ Set.range (redRestrict red K') := by

  obtain ⟨K₁, hfd₁, Pf, Qf, hQf, hfPQ⟩ := ModularCurve.exists_numberField_presentation_level A f
  haveI := hfd₁
  have hfK₁ : (f : LaurentSeries Qb) ∈ fieldOver (N * q) K₁ := by
    have h : (f : LaurentSeries Qb) =
        modularEval (N * q) (coeffSubring A K₁) Pf * (modularEval (N * q) (coeffSubring A K₁) Qf)⁻¹ := by
      rw [← hfPQ, mul_assoc, mul_inv_cancel₀ hQf, mul_one]
    rw [h]
    exact mul_mem (modularEval_mem_fieldOver _ A K₁ Pf) (inv_mem (modularEval_mem_fieldOver _ A K₁ Qf))

  have hq2 : 1 < q ^ 2 := Nat.one_lt_pow two_ne_zero (Fact.out : q.Prime).one_lt
  have hXne : (Polynomial.X ^ (q ^ 2) - Polynomial.X : Polynomial k) ≠ 0 := FiniteField.X_pow_card_sub_X_ne_zero k hq2
  have hroots : ∀ a ∈ ((Polynomial.X ^ (q ^ 2) - Polynomial.X : Polynomial k).roots.toFinset), a ^ (q ^ 2) = a := by
    intro a ha
    rwa [Multiset.mem_toFinset, Polynomial.mem_roots hXne, Polynomial.IsRoot.def, Polynomial.eval_sub,
      Polynomial.eval_pow, Polynomial.eval_X, sub_eq_zero] at ha
  obtain ⟨K₂, hfd₂, -, hT⟩ :=
    ModularCurve.NodeLocalized.exists_finiteDimensional_forall_inertia_apply_eq_and_mem_range_redRestrict q A k red
      ((Polynomial.X ^ (q ^ 2) - Polynomial.X : Polynomial k).roots.toFinset) hroots
  haveI := hfd₂

  have hci : ∀ c ∈ ({c₁, c₂} : Set Qb), IsIntegral ℚ c := fun c _ => Algebra.IsIntegral.isIntegral c
  haveI : FiniteDimensional ℚ ↥(IntermediateField.adjoin ℚ ({c₁, c₂} : Set Qb)) :=
    IntermediateField.finiteDimensional_adjoin hci
  haveI : FiniteDimensional ℚ ↥(K₀ ⊔ K₁) := IntermediateField.finiteDimensional_sup K₀ K₁
  haveI : FiniteDimensional ℚ ↥((K₀ ⊔ K₁) ⊔ K₂) := IntermediateField.finiteDimensional_sup _ _
  have h1 : K₁ ≤ ((K₀ ⊔ K₁) ⊔ K₂) ⊔ IntermediateField.adjoin ℚ ({c₁, c₂} : Set Qb) :=
    le_sup_right.trans (le_sup_left.trans le_sup_left)
  have h2 : K₂ ≤ ((K₀ ⊔ K₁) ⊔ K₂) ⊔ IntermediateField.adjoin ℚ ({c₁, c₂} : Set Qb) :=
    le_sup_right.trans le_sup_left
  refine ⟨((K₀ ⊔ K₁) ⊔ K₂) ⊔ IntermediateField.adjoin ℚ ({c₁, c₂} : Set Qb), IntermediateField.finiteDimensional_sup _ _,
    le_sup_left.trans (le_sup_left.trans le_sup_left), fieldOver_mono (N * q) h1 hfK₁,
    (le_sup_right : _ ≤ ((K₀ ⊔ K₁) ⊔ K₂) ⊔ _) (IntermediateField.subset_adjoin ℚ _ (Set.mem_insert _ _)),
    (le_sup_right : _ ≤ ((K₀ ⊔ K₁) ⊔ K₂) ⊔ _) (IntermediateField.subset_adjoin ℚ _ (Set.mem_insert_of_mem _ (Set.mem_singleton _))),
    ?_⟩
  intro a ha
  have hmem : a ∈ ((Polynomial.X ^ (q ^ 2) - Polynomial.X : Polynomial k).roots.toFinset) := by
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hXne, Polynomial.IsRoot.def, Polynomial.eval_sub,
      Polynomial.eval_pow, Polynomial.eval_X, ha, sub_self]
  obtain ⟨x, hx⟩ := hT a hmem
  exact ⟨Subring.inclusion (coeffSubring_mono A h2) x, (redRestrict_inclusion A red h2 x).trans hx⟩

theorem exists_uniformiser_ramification {q : ℕ} [Fact q.Prime] (A : ValuationSubring Qb) {k : Type*} [Field k] [CharP k q]
    (red : A →+* k) (hker : ∀ c : A, red c = 0 ↔ c ∈ IsLocalRing.maximalIdeal A)
    {K₀ K' : IntermediateField ℚ Qb} (hKK' : K₀ ≤ K') [FiniteDimensional ℚ K']
    (ϖ : ↥(coeffSubring A K₀)) (hϖ : ∀ d : ↥(coeffSubring A K₀), redRestrict red K₀ d = 0 ↔ ∃ d', d = ϖ * d')
    (eK : ℕ) (heK : 1 ≤ eK) (ε : ↥(coeffSubring A K₀)) (hε : IsUnit ε)
    (hqϖ : ((q : ℕ) : ↥(coeffSubring A K₀)) = ϖ ^ eK * ε) :
    ∃ (ϖ' : ↥(coeffSubring A K')) (_ : Irreducible ϖ')
      (_ : ∀ d : ↥(coeffSubring A K'), redRestrict red K' d = 0 ↔ ∃ d', d = ϖ' * d')
      (r : ℕ) (_ : 1 ≤ r) (ν : ↥(coeffSubring A K')) (_ : IsUnit ν)
      (_ : Subring.inclusion (coeffSubring_mono A hKK') ϖ = ν * ϖ' ^ r)
      (_ : ((q : ℕ) : ↥(coeffSubring A K')) = ϖ' ^ (r * eK) * (ν ^ eK * Subring.inclusion (coeffSubring_mono A hKK') ε))
      (_ : IsUnit (ν ^ eK * Subring.inclusion (coeffSubring_mono A hKK') ε)),
      redRestrict red K' ν ≠ 0 ∧ redRestrict red K' (ν ^ eK * Subring.inclusion (coeffSubring_mono A hKK') ε) ≠ 0 := by
  set ι := Subring.inclusion (coeffSubring_mono A hKK') with hι
  obtain ⟨ϖ', hϖ'irr, hϖ'⟩ := exists_uniformiser A red hker K'
  haveI hdvr : IsDiscreteValuationRing ↥(coeffSubring A K') := isDiscreteValuationRing_coeffSubring red hker K'
  have hϖ0 : ι ϖ ≠ 0 := by
    intro h0
    have h1 := congrArg ι hqϖ
    rw [map_natCast, map_mul, map_pow, h0, zero_pow (by omega), zero_mul] at h1
    have h2 : ((q : ℕ) : Qb) = 0 := by simpa using congrArg Subtype.val h1
    exact (Fact.out : q.Prime).ne_zero (by exact_mod_cast h2)
  have hϖnu : ¬ IsUnit (ι ϖ) := by
    rw [← redRestrict_eq_zero_iff_not_isUnit A red hker K']
    show redRestrict red K₀ ϖ = 0
    exact (hϖ ϖ).mpr ⟨1, (mul_one _).symm⟩
  obtain ⟨r, νu, hfac⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hϖ0 hϖ'irr
  have hr : 1 ≤ r := by
    rcases Nat.eq_zero_or_pos r with rfl | h
    · rw [pow_zero, mul_one] at hfac; exact absurd (hfac ▸ νu.isUnit) hϖnu
    · exact h
  have hqϖ' : ((q : ℕ) : ↥(coeffSubring A K')) = ϖ' ^ (r * eK) * ((νu : ↥(coeffSubring A K')) ^ eK * ι ε) := by
    have h1 := congrArg ι hqϖ
    rw [map_natCast, map_mul, map_pow, hfac] at h1
    rw [h1]; ring
  have hε' : IsUnit ((νu : ↥(coeffSubring A K')) ^ eK * ι ε) := (νu.isUnit.pow _).mul (hε.map ι)
  have hne0 : ∀ z : ↥(coeffSubring A K'), IsUnit z → redRestrict red K' z ≠ 0 := fun z hz h0 =>
    ((redRestrict_eq_zero_iff_not_isUnit A red hker K' z).mp h0) hz
  exact ⟨ϖ', hϖ'irr, hϖ', r, hr, νu, νu.isUnit, hfac, hqϖ', hε', hne0 _ νu.isUnit, hne0 _ hε'⟩

end ChartOkPkg

namespace ChartOkPkg
open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.NodeLocalized ModularCurve.PlaceSpecialization ModularCurve.PlaceSpecialization.ProlongationTuple

section L3
variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
  {k : Type*} [Field k] [CharP k q] {red : A →+* k} {data : ModularPolynomialData q}
  {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
  {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}

theorem iota_algebraMap' {P : PlaceSpecialization A q N data hKr k red hα hβ} (R : ProlongationTuple P)
    (x : IsLocalRing.ResidueField A) :
    R.ι (algebraMap (IsLocalRing.ResidueField A) ↥(modularFunctionFieldFullC (IsLocalRing.ResidueField A) N) x)
      = algebraMap k ↥(modularFunctionFieldC k N) (R.redBar x) := by
  apply Subtype.ext
  rw [R.ι_coe]
  change coeffMap R.redBar (algebraMap (IsLocalRing.ResidueField A) (LaurentSeries (IsLocalRing.ResidueField A)) x)
    = algebraMap k (LaurentSeries k) (R.redBar x)
  rw [algebraMap_laurentSeries_eq_single, algebraMap_laurentSeries_eq_single, coeffMap_single]

theorem residue₁_algebraMap' {P : PlaceSpecialization A q N data hKr k red hα hβ} (R : ProlongationTuple P) (a : A) :
    R.residue₁ ⟨algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) a, (R.R₁.algebraMap_mem_iff a).mpr a.2⟩
      = algebraMap k ↥(modularFunctionFieldC k N) (red a) := by
  rw [residue₁_apply, R.R₁.residue_algebraMap a, iota_algebraMap', R.redBar_residue]

theorem hasValue_pow {K F : Type*} [Field K] [Field F] [Algebra K F] {v : Place K F} {g : F} {a : K}
    (h : v.HasValue g a) (n : ℕ) : v.HasValue (g ^ n) (a ^ n) := by
  induction n with
  | zero => simpa using v.hasValue_one
  | succ n ih => rw [pow_succ, pow_succ]; exact ih.mul h

set_option maxHeartbeats 16000000 in

theorem nodeEq_over {P : PlaceSpecialization A q N data hKr k red hα hβ} (R : ProlongationTuple P) [IsAlgClosed k]
    {K₀ K' : IntermediateField ℚ (AlgebraicClosure ℚ)} [FiniteDimensional ℚ K₀] [FiniteDimensional ℚ K'] (hKK' : K₀ ≤ K')
    (w : Place k ↥(modularFunctionFieldC k N)) (hBB' : R.nodeIntegersOver K₀ w ≤ R.nodeIntegersOver K' w)
    (c : R.NodeCoordinates K₀ w) (ϖ : ↥(coeffSubring A K₀)) (wd eK : ℕ) (u : ↥(R.nodeIntegersOver K₀ w)) (hu : IsUnit u)
    (hxy : c.x * c.y = R.nodeConst K₀ w ϖ ^ (wd * eK) * u)
    (u0 : k) (hu0 : w.HasValue (R.nodeResidue₁ w ⟨(u : ↥(modularFunctionFieldBar (N * q))), u.2.1⟩ : ↥(modularFunctionFieldC k N)) u0)
    (ϖ' ν : ↥(coeffSubring A K')) (r : ℕ) (hν : IsUnit ν)
    (hfac : Subring.inclusion (coeffSubring_mono A hKK') ϖ = ν * ϖ' ^ r) :
    IsUnit (R.nodeConst K' w ν ^ (wd * eK) * Subring.inclusion hBB' u) ∧
    ((c.x : ↥(modularFunctionFieldBar (N * q))) * c.y =
      (R.nodeConst K' w ϖ' : ↥(modularFunctionFieldBar (N * q))) ^ (wd * (r * eK)) *
        (R.nodeConst K' w ν ^ (wd * eK) * Subring.inclusion hBB' u : ↥(R.nodeIntegersOver K' w))) ∧
    w.HasValue (R.nodeResidue₁ w ⟨((R.nodeConst K' w ν ^ (wd * eK) * Subring.inclusion hBB' u : ↥(R.nodeIntegersOver K' w)) :
        ↥(modularFunctionFieldBar (N * q))), (R.nodeConst K' w ν ^ (wd * eK) * Subring.inclusion hBB' u).2.1⟩ :
        ↥(modularFunctionFieldC k N)) (u0 * (redRestrict red K' ν) ^ (wd * eK)) := by
  refine ⟨((hν.map (R.nodeConst K' w)).pow _).mul (hu.map _), ?_, ?_⟩
  ·
    have h1 := congrArg (fun z : ↥(R.nodeIntegersOver K₀ w) => (z : ↥(modularFunctionFieldBar (N * q)))) hxy
    simp only [Subring.coe_mul, SubmonoidClass.coe_pow] at h1
    have hϖF : (R.nodeConst K₀ w ϖ : ↥(modularFunctionFieldBar (N * q))) =
        (R.nodeConst K' w ν : ↥(modularFunctionFieldBar (N * q))) * (R.nodeConst K' w ϖ' : ↥(modularFunctionFieldBar (N * q))) ^ r := by
      have h2 : ((ϖ : ↥(coeffSubring A K₀)) : AlgebraicClosure ℚ) =
          ((ν : ↥(coeffSubring A K')) : AlgebraicClosure ℚ) * ((ϖ' : ↥(coeffSubring A K')) : AlgebraicClosure ℚ) ^ r := by
        have := congrArg Subtype.val hfac
        simpa only [Subring.coe_mul, SubmonoidClass.coe_pow, Subring.coe_inclusion] using this
      rw [coe_nodeConst, coe_nodeConst, coe_nodeConst, h2, map_mul, map_pow]
    rw [h1, hϖF]
    simp only [Subring.coe_mul, SubmonoidClass.coe_pow, Subring.coe_inclusion]
    ring
  ·
    have hconst : R.nodeResidue₁ w ⟨(R.nodeConst K' w ν : ↥(modularFunctionFieldBar (N * q))), (R.nodeConst K' w ν).2.1⟩ =
        algebraMap k ↥(modularFunctionFieldC k N) (redRestrict red K' ν) := by
      rw [nodeResidue₁_apply]
      have : (⟨(R.nodeConst K' w ν : ↥(modularFunctionFieldBar (N * q))), (R.nodeConst K' w ν).2.1.1⟩ : R.R₁.integers) =
          ⟨algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) ((⟨(ν : AlgebraicClosure ℚ), ν.2.1⟩ : A) : AlgebraicClosure ℚ),
            (R.R₁.algebraMap_mem_iff _).mpr (⟨(ν : AlgebraicClosure ℚ), ν.2.1⟩ : A).2⟩ := Subtype.ext (coe_nodeConst R K' w ν)
      rw [this, residue₁_algebraMap']
      rfl
    have hmul : R.nodeResidue₁ w ⟨((R.nodeConst K' w ν ^ (wd * eK) * Subring.inclusion hBB' u : ↥(R.nodeIntegersOver K' w)) :
          ↥(modularFunctionFieldBar (N * q))), (R.nodeConst K' w ν ^ (wd * eK) * Subring.inclusion hBB' u).2.1⟩ =
        R.nodeResidue₁ w ⟨(R.nodeConst K' w ν : ↥(modularFunctionFieldBar (N * q))), (R.nodeConst K' w ν).2.1⟩ ^ (wd * eK) *
          R.nodeResidue₁ w ⟨(u : ↥(modularFunctionFieldBar (N * q))), u.2.1⟩ := by
      have hsub : (⟨((R.nodeConst K' w ν ^ (wd * eK) * Subring.inclusion hBB' u : ↥(R.nodeIntegersOver K' w)) :
            ↥(modularFunctionFieldBar (N * q))), (R.nodeConst K' w ν ^ (wd * eK) * Subring.inclusion hBB' u).2.1⟩ : ↥(R.nodeIntegers w)) =
          (⟨(R.nodeConst K' w ν : ↥(modularFunctionFieldBar (N * q))), (R.nodeConst K' w ν).2.1⟩ : ↥(R.nodeIntegers w)) ^ (wd * eK) *
            ⟨(u : ↥(modularFunctionFieldBar (N * q))), u.2.1⟩ :=
        Subtype.ext (by simp only [Subring.coe_mul, SubmonoidClass.coe_pow, Subring.coe_inclusion])
      rw [hsub, map_mul, map_pow]
    rw [hmul, hconst, mul_comm]
    exact hu0.mul (hasValue_pow (w.hasValue_algebraMap _) _)

end L3
end ChartOkPkg

namespace ChartOkPkg
open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.NodeLocalized ModularCurve.PlaceSpecialization ModularCurve.PlaceSpecialization.ProlongationTuple

section L4
variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα₁ : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q} {hβ₁ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    {P₁ : PlaceSpecialization A q N data hKr k red hα₁ hβ₁}

local notation "LQ" => LaurentSeries (AlgebraicClosure ℚ)

theorem exists_inclCoord (R : ProlongationTuple P₁) [IsAlgClosed k] {K K' : IntermediateField ℚ (AlgebraicClosure ℚ)}
    {w : Place k ↥(modularFunctionFieldC k N)} (hBB' : R.nodeIntegersOver K w ≤ R.nodeIntegersOver K' w)
    (c : R.NodeCoordinates K w) :
    ∃ c₀ : R.NodeCoordinates K' w, c₀.x = Subring.inclusion hBB' c.x ∧ c₀.y = Subring.inclusion hBB' c.y := by
  have e1 : (⟨((Subring.inclusion hBB' c.x : ↥(R.nodeIntegersOver K' w)) : ↥(modularFunctionFieldBar (N * q))),
      (Subring.inclusion hBB' c.x).2.1⟩ : ↥(R.nodeIntegers w)) = ⟨(c.x : ↥(modularFunctionFieldBar (N * q))), c.x.2.1⟩ :=
    Subtype.ext (Subring.coe_inclusion hBB' c.x)
  have e2 : (⟨((Subring.inclusion hBB' c.y : ↥(R.nodeIntegersOver K' w)) : ↥(modularFunctionFieldBar (N * q))),
      (Subring.inclusion hBB' c.y).2.1⟩ : ↥(R.nodeIntegers w)) = ⟨(c.y : ↥(modularFunctionFieldBar (N * q))), c.y.2.1⟩ :=
    Subtype.ext (Subring.coe_inclusion hBB' c.y)
  refine ⟨{ x := Subring.inclusion hBB' c.x, y := Subring.inclusion hBB' c.y,
            x_fst := ?_, x_snd := ?_, y_snd := ?_, y_fst := ?_ }, rfl, rfl⟩
  · rw [e1]; exact c.x_fst
  · rw [e1]; exact c.x_snd
  · rw [e2]; exact c.y_snd
  · rw [e2]; exact c.y_fst

set_option maxHeartbeats 16000000 in

theorem nodeBlock_over (R : ProlongationTuple P₁) [IsAlgClosed k] [DecidableEq k] (hqN : ¬ q ∣ N) (hmodel : R.IsModel)
    (hO : R.OrderLawFixed)
    (W : Finset (Place k (modularFunctionFieldC k N))) (hW : ∀ w ∈ W, w ∈ ssPlaces q N k)
    (hreg : R.RegularityLaw W) (hval : R.NodeValueLaw W)
    {K K' : IntermediateField ℚ (AlgebraicClosure ℚ)} [FiniteDimensional ℚ K']
    (w : Place k (modularFunctionFieldC k N)) (hw : w ∈ W)
    (hk₀ : ∀ a : k, a ^ (q ^ 2) = a → a ∈ Set.range (NodeLocalized.redRestrict red K'))
    (hBB' : R.nodeIntegersOver K w ≤ R.nodeIntegersOver K' w) (c : R.NodeCoordinates K w)
    (ϖ' : ↥(NodeLocalized.coeffSubring A K'))
    (hϖ' : ∀ d : ↥(NodeLocalized.coeffSubring A K'), NodeLocalized.redRestrict red K' d = 0 ↔ ∃ d', d = ϖ' * d') :
    ∃ (_ : (Ideal.span {R.nodeConst K' w ϖ', Subring.inclusion hBB' c.x, Subring.inclusion hBB' c.y}).IsMaximal ∧
          ∀ M : Ideal ↥(R.nodeIntegersOver K' w), M.IsMaximal →
            M = Ideal.span {R.nodeConst K' w ϖ', Subring.inclusion hBB' c.x, Subring.inclusion hBB' c.y})
      (_ : IsLocalRing ↥(R.nodeIntegersOver K' w)) (_ : IsNoetherianRing ↥(R.nodeIntegersOver K' w))
      (_ : maximalIdeal ↥(R.nodeIntegersOver K' w) =
          Ideal.span {R.nodeConst K' w ϖ', Subring.inclusion hBB' c.x, Subring.inclusion hBB' c.y}),
      (Ideal.span {R.nodeConst K' w ϖ', Subring.inclusion hBB' c.x}).IsPrime ∧
        (Ideal.span {R.nodeConst K' w ϖ', Subring.inclusion hBB' c.y}).IsPrime ∧
        Subring.inclusion hBB' c.y ∉ Ideal.span {R.nodeConst K' w ϖ', Subring.inclusion hBB' c.x} ∧
        Subring.inclusion hBB' c.x ∉ Ideal.span {R.nodeConst K' w ϖ', Subring.inclusion hBB' c.y} := by
  obtain ⟨c₀, hc₀x, hc₀y⟩ := exists_inclCoord R hBB' c

  have hLN := isLocalRing_and_isNoetherianRing_nodeIntegersOver_of_nodeCoordinates_of_orderLawFixed_of_range_redRestrict R hqN hmodel hO W hW
    hreg hval K' hk₀ w hw c₀
  haveI : IsLocalRing ↥(R.nodeIntegersOver K' w) := hLN.1
  haveI : IsNoetherianRing ↥(R.nodeIntegersOver K' w) := hLN.2
  have hsat := nodeResidue_saturated_of_orderLawFixed_of_isNoetherianRing R hqN hmodel hO W hW hreg hval K' w hw
  obtain ⟨hsat₁, hsat₂⟩ := hsat

  have hpres := exists_crossingPresentation_nodeIntegersOver_of_orderLawFixed_of_saturated R hqN hmodel hO W hW hreg hval
    K' w hw hsat₁ hsat₂ c₀ ϖ' hϖ'
  obtain ⟨c', hspx, hspy, rest⟩ := hpres
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hmax, huniq, hpr1, hpr2, hnm1, hnm2⟩ := rest
  rw [hc₀x] at hspx
  rw [hc₀y] at hspy
  set ϖS := R.nodeConst K' w ϖ'
  set xS := Subring.inclusion hBB' c.x
  set yS := Subring.inclusion hBB' c.y

  have htri : Ideal.span {ϖS, c'.x, c'.y} = Ideal.span {ϖS, xS, yS} := by
    have h3 : ∀ u v : ↥(R.nodeIntegersOver K' w), Ideal.span {ϖS, u, v} = Ideal.span {ϖS, u} ⊔ Ideal.span {ϖS, v} := by
      intro u v
      apply le_antisymm
      · rw [Ideal.span_le]
        rintro z (rfl | rfl | rfl)
        · exact Ideal.mem_sup_left (Ideal.subset_span (Set.mem_insert _ _))
        · exact Ideal.mem_sup_left (Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _)))
        · exact Ideal.mem_sup_right (Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _)))
      · refine sup_le (Ideal.span_mono ?_) (Ideal.span_mono ?_)
        · exact Set.insert_subset_insert (Set.singleton_subset_iff.mpr (Set.mem_insert _ _))
        · exact Set.insert_subset_insert (Set.singleton_subset_iff.mpr (Set.mem_insert_of_mem _ (Set.mem_singleton _)))
    rw [h3, h3, hspx, hspy]
  have hmax' : (Ideal.span {ϖS, xS, yS}).IsMaximal := htri ▸ hmax
  have huniq' : ∀ M : Ideal ↥(R.nodeIntegersOver K' w), M.IsMaximal → M = Ideal.span {ϖS, xS, yS} :=
    fun M hM => (huniq M hM).trans htri
  haveI hloc : IsLocalRing ↥(R.nodeIntegersOver K' w) :=
    IsLocalRing.of_unique_max_ideal ⟨_, hmax', fun M hM => huniq' M hM⟩
  have hmaxI : maximalIdeal ↥(R.nodeIntegersOver K' w) = Ideal.span {ϖS, xS, yS} :=
    huniq' _ (IsLocalRing.maximalIdeal.isMaximal _)

  have hnoe : IsNoetherianRing ↥(R.nodeIntegersOver K' w) := hLN.2

  refine ⟨⟨hmax', huniq'⟩, hloc, hnoe, hmaxI, hspx ▸ hpr1, hspy ▸ hpr2, ?_, ?_⟩
  · intro hy
    apply hnm1
    have h1 : c'.y ∈ Ideal.span {ϖS, yS} := hspy ▸ Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _))
    have h2 : Ideal.span {ϖS, yS} ≤ Ideal.span {ϖS, xS} := by
      rw [Ideal.span_le]
      rintro z (rfl | rfl)
      · exact Ideal.subset_span (Set.mem_insert _ _)
      · exact hy
    exact hspx.symm ▸ h2 h1
  · intro hx
    apply hnm2
    have h1 : c'.x ∈ Ideal.span {ϖS, xS} := hspx ▸ Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _))
    have h2 : Ideal.span {ϖS, xS} ≤ Ideal.span {ϖS, yS} := by
      rw [Ideal.span_le]
      rintro z (rfl | rfl)
      · exact Ideal.subset_span (Set.mem_insert _ _)
      · exact hx
    exact hspy.symm ▸ h2 h1

end L4
end ChartOkPkg

open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.PlaceSpecialization ModularCurve.PlaceSpecialization.ProlongationTuple

set_option maxHeartbeats 16000000 in

theorem solution
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    (P : PlaceSpecialization A q N data hKr k red hα hβ) (hqN : ¬ q ∣ N)
    {W : Finset (Place k (modularFunctionFieldC k N))}
    (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q N k)
    (R : ProlongationTuple P) (hR : R.IsModel) (hRL : R.RegularityLaw W) (hNV : R.NodeValueLaw W) (hO : R.OrderLawFixed)
    (dat : R.AnnulusDatumLevel W)
    (hwidth : ∀ w ∈ W, 1 ≤ dat.width w)
    (hK : ∀ w : Place k (modularFunctionFieldC k N), FiniteDimensional ℚ ↥(dat.K w))
    (ϖ : ∀ w : Place k (modularFunctionFieldC k N), ↥(NodeLocalized.coeffSubring A (dat.K w)))
      (eK : Place k (modularFunctionFieldC k N) → ℕ)
      (ε : ∀ w : Place k (modularFunctionFieldC k N), ↥(NodeLocalized.coeffSubring A (dat.K w)))
      (u : ∀ (w : Place k (modularFunctionFieldC k N)) (hw : w ∈ W), ↥(R.nodeIntegersOver (dat.K w) w))
    (hϖ : ∀ w ∈ W, ∀ d : ↥(NodeLocalized.coeffSubring A (dat.K w)),
      NodeLocalized.redRestrict red (dat.K w) d = 0 ↔ ∃ d', d = ϖ w * d')
    (heK : ∀ w ∈ W, 1 ≤ eK w)
    (hε : ∀ w ∈ W, IsUnit (ε w))
    (hqϖ : ∀ w ∈ W, ((q : ℕ) : ↥(NodeLocalized.coeffSubring A (dat.K w))) = ϖ w ^ eK w * ε w)
    (hu : ∀ (w : Place k (modularFunctionFieldC k N)) (hw : w ∈ W), IsUnit (u w hw) ∧
      (dat.coord w hw).x * (dat.coord w hw).y = R.nodeConst (dat.K w) w (ϖ w) ^ (dat.width w * eK w) * u w hw)
    (hmax : ∀ (w : Place k (modularFunctionFieldC k N)) (hw : w ∈ W),
      (Ideal.span {R.nodeConst (dat.K w) w (ϖ w), (dat.coord w hw).x, (dat.coord w hw).y}).IsMaximal ∧
      ∀ M : Ideal ↥(R.nodeIntegersOver (dat.K w) w), M.IsMaximal →
      M = Ideal.span {R.nodeConst (dat.K w) w (ϖ w), (dat.coord w hw).x, (dat.coord w hw).y})
    (hbr : ∀ (w : Place k (modularFunctionFieldC k N)) (hw : w ∈ W),
      (Ideal.span {R.nodeConst (dat.K w) w (ϖ w), (dat.coord w hw).x}).IsPrime ∧
      (Ideal.span {R.nodeConst (dat.K w) w (ϖ w), (dat.coord w hw).y}).IsPrime ∧
      (dat.coord w hw).y ∉ Ideal.span {R.nodeConst (dat.K w) w (ϖ w), (dat.coord w hw).x} ∧
      (dat.coord w hw).x ∉ Ideal.span {R.nodeConst (dat.K w) w (ϖ w), (dat.coord w hw).y})
    (hnoeth : ∀ w ∈ W, IsNoetherianRing ↥(R.nodeIntegersOver (dat.K w) w))
    (hres : ∀ w ∈ W, ∀ g : ↥(R.nodeIntegersOver (dat.K w) w),
      ∃ o : ↥(NodeLocalized.coeffSubring A (dat.K w)), ¬ IsUnit (g - R.nodeConst (dat.K w) w o))
    (hu0 : ∀ (w : Place k (modularFunctionFieldC k N)) (hw : w ∈ W),
      w.HasValue (R.nodeResidue₁ w ⟨(u w hw : ↥(modularFunctionFieldBar (N * q))), (u w hw).2.1⟩) ((dat.u0 w : kˣ) : k))
    (hker : ∀ c : A, red c = 0 ↔ c ∈ IsLocalRing.maximalIdeal A)

    (w : Place k (modularFunctionFieldC k N)) (hw : w ∈ W)
    (f : ↥(modularFunctionFieldBar (N * q))) (hf0 : f ≠ 0)
    (c₁ c₂ : AlgebraicClosure ℚ) (hc₁0 : c₁ ≠ 0) (hc₂0 : c₂ ≠ 0) :
    ∃ (K' : IntermediateField ℚ (AlgebraicClosure ℚ)) (hKK' : dat.K w ≤ K') (_ : FiniteDimensional ℚ ↥K')
      (hBB' : R.nodeIntegersOver (dat.K w) w ≤ R.nodeIntegersOver K' w)
      (ϖ' : ↥(NodeLocalized.coeffSubring A K'))
      (_ : ∀ d : ↥(NodeLocalized.coeffSubring A K'), NodeLocalized.redRestrict red K' d = 0 ↔ ∃ d', d = ϖ' * d')
      (eK' : ℕ) (_ : 1 ≤ eK') (ε' : ↥(NodeLocalized.coeffSubring A K')) (_ : IsUnit ε')
      (_ : ((q : ℕ) : ↥(NodeLocalized.coeffSubring A K')) = ϖ' ^ eK' * ε')
      (u' : ↥(R.nodeIntegersOver K' w)) (_ : IsUnit u')
      (_ : ((dat.coord w hw).x : ↥(modularFunctionFieldBar (N * q))) * (dat.coord w hw).y =
        (R.nodeConst K' w ϖ' : ↥(modularFunctionFieldBar (N * q))) ^ (dat.width w * eK') * u')
      (_ : (Ideal.span {R.nodeConst K' w ϖ', Subring.inclusion hBB' (dat.coord w hw).x, Subring.inclusion hBB' (dat.coord w hw).y}).IsMaximal ∧
        ∀ M : Ideal ↥(R.nodeIntegersOver K' w), M.IsMaximal →
          M = Ideal.span {R.nodeConst K' w ϖ', Subring.inclusion hBB' (dat.coord w hw).x, Subring.inclusion hBB' (dat.coord w hw).y})
      (_ : IsLocalRing ↥(R.nodeIntegersOver K' w)) (_ : IsNoetherianRing ↥(R.nodeIntegersOver K' w))
      (_ : maximalIdeal ↥(R.nodeIntegersOver K' w) =
        Ideal.span {R.nodeConst K' w ϖ', Subring.inclusion hBB' (dat.coord w hw).x, Subring.inclusion hBB' (dat.coord w hw).y})
      (_ : (Ideal.span {R.nodeConst K' w ϖ', Subring.inclusion hBB' (dat.coord w hw).x}).IsPrime ∧
        (Ideal.span {R.nodeConst K' w ϖ', Subring.inclusion hBB' (dat.coord w hw).y}).IsPrime ∧
        Subring.inclusion hBB' (dat.coord w hw).y ∉ Ideal.span {R.nodeConst K' w ϖ', Subring.inclusion hBB' (dat.coord w hw).x} ∧
        Subring.inclusion hBB' (dat.coord w hw).x ∉ Ideal.span {R.nodeConst K' w ϖ', Subring.inclusion hBB' (dat.coord w hw).y})
      (_ : ∀ g : ↥(R.nodeIntegersOver K' w), ∃ o : ↥(NodeLocalized.coeffSubring A K'), ¬ IsUnit (g - R.nodeConst K' w o))
      (_ : (f : LaurentSeries (AlgebraicClosure ℚ)) ∈ NodeLocalized.fieldOver (N * q) K')
      (_ : ∀ z ∈ NodeLocalized.fieldOver (N * q) K', ∃ x y : ↥(modularFunctionFieldBar (N * q)),
        x ∈ R.nodeIntegersOver K' w ∧ y ∈ R.nodeIntegersOver K' w ∧ y ≠ 0 ∧
          z * ((y : ↥(modularFunctionFieldBar (N * q))) : LaurentSeries (AlgebraicClosure ℚ)) =
            ((x : ↥(modularFunctionFieldBar (N * q))) : LaurentSeries (AlgebraicClosure ℚ)))
      (_ : c₁ ∈ K') (_ : c₂ ∈ K')
      (m₁ m₂ : ℤ) (η₁ η₂ : ↥(NodeLocalized.coeffSubring A K')) (_ : IsUnit η₁) (_ : IsUnit η₂)
      (_ : c₁ = ((ϖ' : ↥(NodeLocalized.coeffSubring A K')) : AlgebraicClosure ℚ) ^ m₁ *
        ((η₁ : ↥(NodeLocalized.coeffSubring A K')) : AlgebraicClosure ℚ))
      (_ : c₂ = ((ϖ' : ↥(NodeLocalized.coeffSubring A K')) : AlgebraicClosure ℚ) ^ m₂ *
        ((η₂ : ↥(NodeLocalized.coeffSubring A K')) : AlgebraicClosure ℚ))

      (u0' t εbar' : kˣ)
      (_ : w.HasValue ((R.nodeResidue₁ w ⟨(u' : ↥(modularFunctionFieldBar (N * q))), u'.2.1⟩ :
          ↥(modularFunctionFieldC k N))) (u0' : k))
      (_ : (u0' : k) = (dat.u0 w : k) * (t : k) ^ (dat.width w * eK w))
      (_ : NodeLocalized.redRestrict red K' ε' = (εbar' : k))
      (_ : NodeLocalized.redRestrict red K' ε' = (t : k) ^ (eK w) * NodeLocalized.redRestrict red (dat.K w) (ε w))

      (r : ℕ) (ν : ↥(NodeLocalized.coeffSubring A K')) (_ : IsUnit ν) (_ : eK' = r * eK w)
      (_ : ((ϖ w : ↥(NodeLocalized.coeffSubring A (dat.K w))) : AlgebraicClosure ℚ) =
        ((ϖ' : ↥(NodeLocalized.coeffSubring A K')) : AlgebraicClosure ℚ) ^ r * ((ν : ↥(NodeLocalized.coeffSubring A K')) : AlgebraicClosure ℚ))
      (_ : ((ε' : ↥(NodeLocalized.coeffSubring A K')) : AlgebraicClosure ℚ) =
        ((ν : ↥(NodeLocalized.coeffSubring A K')) : AlgebraicClosure ℚ) ^ eK w * ((ε w : ↥(NodeLocalized.coeffSubring A (dat.K w))) : AlgebraicClosure ℚ)),
      NodeLocalized.redRestrict red K' ν = (t : k) := by

  classical
  haveI : ∀ v : Place k (modularFunctionFieldC k N), FiniteDimensional ℚ ↥(dat.K v) := hK

  have hwss : w ∈ ssPlaces q N k := (hW w).mp hw

  obtain ⟨K', hfd', hKK', hfK, hc₁, hc₂, hk₀'⟩ :=
    ChartOkPkg.exists_coeffField A red (dat.K w) f c₁ c₂
  haveI := hfd'

  obtain ⟨ϖ', hϖ'irr, hϖ', r, hr, ν, hν, hfac, hqϖ', hε', ht0, hεbar0⟩ :=
    ChartOkPkg.exists_uniformiser_ramification A red hker hKK' (ϖ w) (hϖ w hw) (eK w) (heK w hw) (ε w) (hε w hw) (hqϖ w hw)

  have hBB' : R.nodeIntegersOver (dat.K w) w ≤ R.nodeIntegersOver K' w := fun g hg =>
    ⟨hg.1, ChartOkPkg.fieldOver_mono (N * q) hKK' hg.2⟩

  obtain ⟨hu', hxy', hu0'⟩ := ChartOkPkg.nodeEq_over R hKK' w hBB' (dat.coord w hw) (ϖ w) (dat.width w) (eK w)
    (u w hw) (hu w hw).1 (hu w hw).2 _ (hu0 w hw) ϖ' ν r hν hfac

  obtain ⟨hmaxK, hloc, hnoe, hmax', hbr'⟩ := ChartOkPkg.nodeBlock_over R hqN hR hO W (fun v hv => (hW v).mp hv) hRL hNV w hw
    hk₀' hBB' (dat.coord w hw) ϖ' hϖ'

  have hres' : ∀ g : ↥(R.nodeIntegersOver K' w), ∃ o : ↥(NodeLocalized.coeffSubring A K'), ¬ IsUnit (g - R.nodeConst K' w o) :=
    fun g => exists_not_isUnit_sub_nodeConst_of_evalAt_mem_range_redRestrict_of_orderLawFixed R hqN hO W
      (fun v hv => (hW v).mp hv) hRL K' w hw hk₀' g

  have hfrac : ∀ z ∈ NodeLocalized.fieldOver (N * q) K', ∃ x y : ↥(modularFunctionFieldBar (N * q)),
      x ∈ R.nodeIntegersOver K' w ∧ y ∈ R.nodeIntegersOver K' w ∧ y ≠ 0 ∧
        z * ((y : ↥(modularFunctionFieldBar (N * q))) : LaurentSeries (AlgebraicClosure ℚ)) =
          ((x : ↥(modularFunctionFieldBar (N * q))) : LaurentSeries (AlgebraicClosure ℚ)) :=
    fun z hz => exists_mul_eq_of_mem_fieldOver_nodeIntegersOver R hqN K' w hwss z hz

  obtain ⟨m₁, η₁, hη₁, hc₁η⟩ := ChartOkPkg.exists_zpow_mul_unit A red hker K' ϖ' hϖ'irr hc₁ hc₁0
  obtain ⟨m₂, η₂, hη₂, hc₂η⟩ := ChartOkPkg.exists_zpow_mul_unit A red hker K' ϖ' hϖ'irr hc₂ hc₂0
  have hu0ne : (dat.u0 w : k) * (NodeLocalized.redRestrict red K' ν) ^ (dat.width w * eK w) ≠ 0 :=
    mul_ne_zero (dat.u0 w).ne_zero (pow_ne_zero _ ht0)

  have hfacQ : ((ϖ w : ↥(NodeLocalized.coeffSubring A (dat.K w))) : AlgebraicClosure ℚ) =
      ((ϖ' : ↥(NodeLocalized.coeffSubring A K')) : AlgebraicClosure ℚ) ^ r * ((ν : ↥(NodeLocalized.coeffSubring A K')) : AlgebraicClosure ℚ) := by
    have := congrArg Subtype.val hfac
    simp only [Subring.coe_mul, SubmonoidClass.coe_pow, Subring.coe_inclusion] at this
    rw [this, mul_comm]
  have hεQ : ((ν ^ eK w * Subring.inclusion (ChartOkPkg.coeffSubring_mono A hKK') (ε w) : ↥(NodeLocalized.coeffSubring A K')) : AlgebraicClosure ℚ) =
      ((ν : ↥(NodeLocalized.coeffSubring A K')) : AlgebraicClosure ℚ) ^ eK w * ((ε w : ↥(NodeLocalized.coeffSubring A (dat.K w))) : AlgebraicClosure ℚ) := by
    simp only [Subring.coe_mul, SubmonoidClass.coe_pow, Subring.coe_inclusion]
  have hεred : NodeLocalized.redRestrict red K' (ν ^ eK w * Subring.inclusion (ChartOkPkg.coeffSubring_mono A hKK') (ε w)) =
      (NodeLocalized.redRestrict red K' ν) ^ (eK w) * NodeLocalized.redRestrict red (dat.K w) (ε w) := by
    rw [map_mul, map_pow]; rfl
  exact ⟨K', hKK', hfd', hBB', ϖ', hϖ', r * eK w, Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by have := heK w hw; omega)),
    ν ^ eK w * Subring.inclusion (ChartOkPkg.coeffSubring_mono A hKK') (ε w), hε', hqϖ', _, hu', hxy', hmaxK, hloc, hnoe,
    hmax', hbr', hres', hfK, hfrac, hc₁, hc₂, m₁, m₂, η₁, η₂, hη₁, hη₂, hc₁η, hc₂η,
    Units.mk0 _ hu0ne, Units.mk0 _ ht0, Units.mk0 _ hεbar0, hu0', rfl, rfl, hεred, r, ν, hν, rfl, hfacQ, hεQ, rfl⟩

end S_ModularCurve_PlaceSpecialization_ProlongationTuple_AnnulusDatumLevel_exists_nodePackage_over_of_orderLawFixed
end P2MW
export P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_AnnulusDatumLevel_exists_nodePackage_over_of_orderLawFixed (solution)
