-- Prove2me | solution 1 for ModularCurve.PlaceSpecialization.yDepth_restrictAlong_towerInclBar_eq_yDepth_pow_ramificationIndexAlong_heckeAlphaC
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/d5b8e8db-a7ef-5cd5-86f8-abebab57cf2e

import Definitions.Def_ModularCurve_NodeDepth
import Definitions.Def_ModularCurve_GlueData
import Definitions.Def_ModularCurve_PlaceWidth
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_ModularCurve_CoeffSemilinearAut
import Definitions.Def_ValuationSubring_ReduceAt
import Definitions.Def_ModularCurve_JZeroSemistableSpecialization
import Definitions.Def_ModularCurve_HeckeModule
import Definitions.Def_ModularCurve_DegeneracyTower
import Definitions.Def_ModularCurve_CharLDegeneracyHecke
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_mem_integers_towerInclBar_and_coe_residue_eq
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_crossingExponent_eq_placeWidth_mul_of_orderLawFixed
import Theorems.Thm_ModularCurve_NodeLocalized_exists_forall_redRestrict_eq_zero_iff_and_natCast_eq_pow_mul
import Theorems.Thm_ModularCurve_NodeLocalized_isDiscreteValuationRing_coeffSubring
import Theorems.Thm_ValuationSubring_isAlgClosed_residueField_algebraicClosure_rat
import Theorems.Thm_AlgebraicCurve_Place_evalAt_mul
import Theorems.Thm_AlgebraicCurve_Place_evalAt_algebraMap_eq_evalAt_restrict
import Theorems.Thm_AlgebraicCurve_Place_restrictAlong_restrictAlong
import Theorems.Thm_AlgebraicCurve_Place_ramificationIndexAlong_comp
import Theorems.Thm_AlgebraicCurve_Place_one_le_ramificationIndexAlong
import Theorems.Thm_ModularCurve_ramificationIndexAlong_mul_placeWidth_eq_placeWidth_restrictAlong_of_coe_eq
import Theorems.Thm_ModularCurve_placeRamificationJ_dvd_jWidth_of_mem_ssPlaces
import Theorems.Thm_ModularCurve_charLDegeneracyRoof_eq_modularFunctionFieldFullC_mul
import Theorems.Thm_ModularCurve_modularFunctionFieldC_eq_modularFunctionFieldFullC
import Theorems.Thm_ModularCurve_PlaceSpecialization_frobOnPlacesGeomLevel_frobOnPlacesGeomLevel_eq_self_of_mem_ssPlaces
import Theorems.Thm_ModularCurve_isCurveOver_modularFunctionFieldBar
import Theorems.Thm_ModularCurve_PlaceSpecialization_restrictAlong_heckeAlphaC_sp_and_restrictAlong_heckeBetaC_sp_eq_sp_restrictAlong_of_isModel
import Theorems.Thm_ModularCurve_towerInclBar_isIntegral
import Theorems.Thm_ModularCurve_towerSubstBar_isIntegral
import Theorems.Thm_ModularCurve_heckeBetaCIntegral_unconditional
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_PlaceSpecialization_yDepth_restrictAlong_towerInclBar_eq_yDepth_pow_ramificationIndexAlong_heckeAlphaC
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.instIsElliptic_tateLaurent ModularCurve.instIsElliptic_tateBase ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular ModularCurve.NodeLocalized.isLocalization_nodeDenominators ModularCurve.NodeLocalized.algebraEvalRange ModularCurve.NodeLocalized.isLocalRing_modularLocalizedAtPoint instTopologicallyFGOfFiniteType AdicCompletion.instIsLocalRingMaximalIdeal AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.B3.instIsElliptic_goodModel ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap"
p2m_attr_erase "instance" "AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.instIsScalarTowerJAdjoin AlgebraicCurve.CellDissection.fintypeV AlgebraicCurve.CellDissection.fintypeC AlgebraicCurve.CellDissection.fintypeE AlgebraicCurve.CellDissection.decEqV AlgebraicCurve.CellDissection.decEqC AlgebraicCurve.CellDissection.decEqE"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄"
p2m_attr_erase "simp" "compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd"
p2m_attr_erase "simp" "ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.veluWSum_empty"
p2m_attr_erase "simp" "WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply ModularCurve.ProjectiveLine.map_mk WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff ModularCurve.coe_nodeEquiv_symm_apply ModularCurve.frobNodePair_jOfNode ModularCurve.jOfNode_mk ModularCurve.widthOf_mk ModularCurve.frobNodePairEmb_apply ModularCurve.card_nodePairsOf ModularCurve.frobNodePair_snd ModularCurve.coe_nodeEquiv_apply ModularCurve.frobNodePair_fst ModularCurve.NodeLocalized.coe_modularEvalAt AdicCompletion.evalₐ_mapₐ AdicCompletion.mapAlgEquivOfBijective_apply AdicCompletion.levelMapₐ_mk AdicCompletion.mapₐ_of AdicCompletion.mapAlgEquiv_symm_apply AdicCompletion.mapAlgEquiv_apply AdicCompletion.evalₐ_ofLevelwiseEquiv AdicCompletion.evalₐ_levelwiseHom AdicCompletion.localizationEquiv_of AdicCompletion.evalₐ_ofLevelwiseEquiv_symm Localization.AtPrime.quotientPowEquiv_mk ModularCurve.LambdaModularPolynomialData.mk.sizeOf_spec ModularCurve.LambdaModularPolynomialData.mk.injEq AdicCompletion.transportOf_of AdicCompletion.selfCompletion_smul_of AdicCompletion.tensorRingEquiv_tmul AdicCompletion.completionOfAlgHom_apply AdicCompletion.completionBaseChangeHom_of AdicCompletion.tensorRingHom_tmul"
p2m_attr_erase "simp" "AdicCompletion.stabilizerToCompletionAut_of ModularCurve.Gamma0Pair.map_toCurve WeierstrassCurve.mapPoint_eq_ratPointMap ModularCurve.Gamma0Pair.map_gen ModularCurve.Gamma0Pair.map_eq_gamma0PairMap ModularCurve.ModuliPoint.map_eq_moduliPointMapRingHom ModularCurve.ModuliPoint.map_mk WeierstrassCurve.mapPointHom_apply WeierstrassCurve.mapPoint_zero AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero ModularCurve.cuspCount_one WeierstrassCurve.Universal.halveX_zero WeierstrassCurve.Universal.specialize_X_one WeierstrassCurve.Universal.coeff_halve WeierstrassCurve.Universal.specialize_X_two WeierstrassCurve.Universal.halveCoeff_zero"
p2m_attr_erase "simp" "WeierstrassCurve.Universal.specialize_X_four WeierstrassCurve.Universal.coeff_halveX WeierstrassCurve.Universal.specialize_X_three WeierstrassCurve.Universal.specialize_X_zero HahnSeries.ramScale_apply ModularCurve.PlaceSpecialization.LevelOneProlongationPair.mk.sizeOf_spec ModularCurve.PlaceSpecialization.LevelOneProlongationPair.residue₂_apply ModularCurve.PlaceSpecialization.LevelOneProlongationPair.residue₁_apply ModularCurve.PlaceSpecialization.LevelOneProlongationPair.mk.injEq ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring"
p2m_attr_erase "simp" "ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule AlgebraicCurve.abelJacobiDiv_single AlgebraicCurve.AnalyticCoord.mk.injEq AlgebraicCurve.Cell.mk.sizeOf_spec AlgebraicCurve.RadialRegion.mk.sizeOf_spec AlgebraicCurve.RadialRegion.mk.injEq AlgebraicCurve.CellDissection.mk.sizeOf_spec AlgebraicCurve.Cell.mk.injEq AlgebraicCurve.CellDissection.mk.injEq AlgebraicCurve.AnalyticCoord.mk.sizeOf_spec"
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000
set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve
p2m_open "ModularCurve.PlaceSpecialization ModularCurve.PlaceSpecialization.ProlongationTuple~valuation_pow_crossingExponent_eq"

noncomputable section

namespace DepthTransport

local notation "Qbar" => AlgebraicClosure ℚ

theorem inv_mem_of_isUnit {F : Type*} [Field F] {S : ValuationSubring F} {y : F} (hy : y ∈ S)
    (hu : IsUnit (⟨y, hy⟩ : S)) : y⁻¹ ∈ S := by
  obtain ⟨v, hv⟩ := hu.exists_right_inv
  have hvF : y * (v : F) = 1 := by
    have h := congrArg Subtype.val hv
    simpa using h
  have hv' : (v : F) = y⁻¹ := eq_inv_of_mul_eq_one_right hvF
  exact hv' ▸ v.2

theorem inv_mem_subring_of_isUnit {F : Type*} [Field F] {S : Subring F} {y : F} (hy : y ∈ S)
    (hu : IsUnit (⟨y, hy⟩ : S)) : y⁻¹ ∈ S := by
  obtain ⟨v, hv⟩ := hu.exists_right_inv
  have hvF : y * (v : F) = 1 := by
    have h := congrArg Subtype.val hv
    simpa using h
  have hv' : (v : F) = y⁻¹ := eq_inv_of_mul_eq_one_right hvF
  exact hv' ▸ v.2

theorem eq_one_of_mul_eq_one {Γ : Type*} [LinearOrderedCommGroupWithZero Γ] {a b : Γ} (ha : a ≤ 1)
    (hb : b ≤ 1) (hab : a * b = 1) : a = 1 :=
  le_antisymm ha (calc (1 : Γ) = a * b := hab.symm
    _ ≤ a * 1 := mul_le_mul_right hb a
    _ = a := mul_one a)

theorem evalAt_pow {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)
    (hv : v.IsRational) {f : F} (hf : f ∈ v.toValuationSubring) (n : ℕ) :
    v.evalAt (f ^ n) = v.evalAt f ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, Place.evalAt_one]
  | succ n ih => rw [pow_succ, pow_succ, v.evalAt_mul hv (pow_mem hf n) hf, ih]

theorem evalAt_restrictAlong {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
    (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (w : Place K F')
    (hv : (w.restrictAlong φ hφ).IsRational) {g : F} (hg : g ∈ (w.restrictAlong φ hφ).toValuationSubring) :
    w.evalAt (φ g) = (w.restrictAlong φ hφ).evalAt g := by
  letI := algebraAlong φ
  haveI := isScalarTower_along φ
  haveI := isIntegral_along φ hφ
  exact Place.evalAt_algebraMap_eq_evalAt_restrict w hv hg

section NodeRing

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
  {k : Type*} [Field k] [CharP k q] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
  {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
  {P : PlaceSpecialization A q N data hKr k red hα hβ}

theorem isRational (V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) : V.IsRational := by
  haveI := (ModularCurve.isCurveOver_modularFunctionFieldBar (N * q)).finiteResidue V
  exact (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := AlgebraicClosure ℚ) (K := V.ResidueField)).2

theorem not_isStrictFst_of_reduceFst_mem_ssPlaces [DecidableEq k] (hqN : ¬ q ∣ N)
    (V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) (hV : P.reduceFst V ∈ ssPlaces q N k) :
    ¬ P.IsStrictFst V := fun h =>
  h.2 (ModularCurve.PlaceSpecialization.frobOnPlacesGeomLevel_frobOnPlacesGeomLevel_eq_self_of_mem_ssPlaces hqN P _ hV)

theorem valuation_evalAt_eq_one (R : ProlongationTuple P) {w : Place k (modularFunctionFieldC k N)}
    (hvalA : R.ValueIntegralityLaw w)
    {f : ↥(modularFunctionFieldBar (N * q))} (hf0 : f ≠ 0) (hf : f ∈ R.nodeIntegers w) (hfi : f⁻¹ ∈ R.nodeIntegers w)
    (V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) (hVw : P.reduceFst V = w) :
    A.valuation (V.evalAt f) = 1 := by
  have hprod : V.evalAt f * V.evalAt f⁻¹ = 1 := by
    rw [← V.evalAt_mul (isRational V) (R.mem_toValuationSubring_of_mem_nodeIntegers hf hVw)
      (R.mem_toValuationSubring_of_mem_nodeIntegers hfi hVw), mul_inv_cancel₀ hf0, Place.evalAt_one]
  refine eq_one_of_mul_eq_one ((A.valuation_le_one_iff _).mpr (hvalA f hf V hVw))
    ((A.valuation_le_one_iff _).mpr (hvalA f⁻¹ hfi V hVw)) ?_
  rw [← map_mul, hprod, map_one]

theorem valuation_evalAt_eq_of_ratio_mem (R : ProlongationTuple P) {w : Place k (modularFunctionFieldC k N)}
    (hvalA : R.ValueIntegralityLaw w)
    {f g : ↥(modularFunctionFieldBar (N * q))} (hf0 : f ≠ 0) (hg0 : g ≠ 0)
    (hfg : f * g⁻¹ ∈ R.nodeIntegers w) (hgf : g * f⁻¹ ∈ R.nodeIntegers w)
    (V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) (hVw : P.reduceFst V = w)
    (hg : g ∈ V.toValuationSubring) :
    A.valuation (V.evalAt f) = A.valuation (V.evalAt g) := by
  have hinv : (f * g⁻¹)⁻¹ = g * f⁻¹ := by rw [mul_inv, inv_inv]; exact mul_comm _ _
  have h1 := valuation_evalAt_eq_one R hvalA (mul_ne_zero hf0 (inv_ne_zero hg0)) hfg (hinv ▸ hgf) V hVw
  calc A.valuation (V.evalAt f) = A.valuation (V.evalAt ((f * g⁻¹) * g)) := by rw [inv_mul_cancel_right₀ hg0]
    _ = A.valuation (V.evalAt (f * g⁻¹)) * A.valuation (V.evalAt g) := by
        rw [V.evalAt_mul (isRational V) (R.mem_toValuationSubring_of_mem_nodeIntegers hfg hVw) hg, map_mul]
    _ = A.valuation (V.evalAt g) := by rw [h1, one_mul]

end NodeRing

section DVR
open ModularCurve.NodeLocalized

theorem isUnit_coeffSubring_of_valuation_eq_one (A : ValuationSubring (AlgebraicClosure ℚ))
    (K : IntermediateField ℚ (AlgebraicClosure ℚ))
    (d : ↥(coeffSubring A K)) (hd : A.valuation (d : AlgebraicClosure ℚ) = 1) : IsUnit d := by
  have hd0 : (d : AlgebraicClosure ℚ) ≠ 0 := by
    intro h; rw [h, map_zero] at hd; exact zero_ne_one hd
  have hinvA : (d : AlgebraicClosure ℚ)⁻¹ ∈ A :=
    (A.valuation_le_one_iff _).mp (by rw [map_inv₀, hd, inv_one])
  have hinvK : (d : AlgebraicClosure ℚ)⁻¹ ∈ K := inv_mem d.2.2
  refine ⟨⟨d, ⟨(d : AlgebraicClosure ℚ)⁻¹, hinvA, hinvK⟩, ?_, ?_⟩, rfl⟩
  · exact Subtype.ext (mul_inv_cancel₀ hd0)
  · exact Subtype.ext (inv_mul_cancel₀ hd0)

theorem valuation_eq_one_of_isUnit_coeffSubring (A : ValuationSubring (AlgebraicClosure ℚ))
    (K : IntermediateField ℚ (AlgebraicClosure ℚ))
    (d : ↥(coeffSubring A K)) (hd : IsUnit d) : A.valuation (d : AlgebraicClosure ℚ) = 1 := by
  obtain ⟨u, rfl⟩ := hd
  have h1 : A.valuation ((u : ↥(coeffSubring A K)) : AlgebraicClosure ℚ)
      * A.valuation ((↑(u⁻¹) : ↥(coeffSubring A K)) : AlgebraicClosure ℚ) = 1 := by
    rw [← map_mul, ← Subring.coe_mul, u.mul_inv, Subring.coe_one, map_one]
  have hle1 : A.valuation ((u : ↥(coeffSubring A K)) : AlgebraicClosure ℚ) ≤ 1 := A.valuation_le_one ⟨_, u.1.2.1⟩
  have hle2 : A.valuation ((↑(u⁻¹) : ↥(coeffSubring A K)) : AlgebraicClosure ℚ) ≤ 1 :=
    A.valuation_le_one ⟨_, (u⁻¹).1.2.1⟩
  exact le_antisymm hle1 (by
    calc (1 : A.ValueGroup) = _ * _ := h1.symm
      _ ≤ A.valuation ((u : ↥(coeffSubring A K)) : AlgebraicClosure ℚ) * 1 := mul_le_mul_right hle2 _
      _ = _ := mul_one _)

theorem valuation_lt_one_iff_of_forall_redRestrict {q : ℕ} [Fact q.Prime] (A : ValuationSubring (AlgebraicClosure ℚ))
    {k : Type*} [Field k] [CharP k q] (red : A →+* k)
    (hker : ∀ c : A, red c = 0 ↔ c ∈ IsLocalRing.maximalIdeal A)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) (ϖ : ↥(coeffSubring A K))
    (hϖ : ∀ d : ↥(coeffSubring A K), redRestrict red K d = 0 ↔ ∃ d', d = ϖ * d')
    (d : ↥(coeffSubring A K)) :
    A.valuation (d : AlgebraicClosure ℚ) < 1 ↔ ∃ d', d = ϖ * d' := by
  rw [← hϖ]
  show _ ↔ red (Subring.inclusion inf_le_left d) = 0
  rw [hker, ValuationSubring.valuation_lt_one_iff]
  rfl

theorem irreducible_of_forall_redRestrict {q : ℕ} [Fact q.Prime] (A : ValuationSubring (AlgebraicClosure ℚ))
    {k : Type*} [Field k] [CharP k q] (red : A →+* k)
    (hker : ∀ c : A, red c = 0 ↔ c ∈ IsLocalRing.maximalIdeal A)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K] (ϖ : ↥(coeffSubring A K))
    (hϖ : ∀ d : ↥(coeffSubring A K), redRestrict red K d = 0 ↔ ∃ d', d = ϖ * d') (hϖ0 : ϖ ≠ 0) :
    haveI := ModularCurve.NodeLocalized.isDiscreteValuationRing_coeffSubring red hker K
    Irreducible ϖ := by
  haveI := ModularCurve.NodeLocalized.isDiscreteValuationRing_coeffSubring red hker K
  apply IsDiscreteValuationRing.irreducible_of_span_eq_maximalIdeal ϖ hϖ0
  ext d
  rw [Ideal.mem_span_singleton, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  constructor
  · intro hnu
    have hlt : A.valuation (d : AlgebraicClosure ℚ) < 1 := by
      rcases lt_or_eq_of_le (A.valuation_le_one ⟨_, d.2.1⟩) with h | h
      · exact h
      · exact absurd (isUnit_coeffSubring_of_valuation_eq_one A K d h) hnu
    obtain ⟨d', hd'⟩ := (valuation_lt_one_iff_of_forall_redRestrict A red hker K ϖ hϖ d).mp hlt
    exact ⟨d', by rw [hd']⟩
  · rintro ⟨d', rfl⟩ hu
    have h1 := valuation_eq_one_of_isUnit_coeffSubring A K _ hu
    have hϖlt : A.valuation (ϖ : AlgebraicClosure ℚ) < 1 :=
      (valuation_lt_one_iff_of_forall_redRestrict A red hker K ϖ hϖ ϖ).mpr ⟨1, by rw [mul_one]⟩
    rw [Subring.coe_mul, map_mul] at h1
    have hle : A.valuation ((d' : ↥(coeffSubring A K)) : AlgebraicClosure ℚ) ≤ 1 := A.valuation_le_one ⟨_, d'.2.1⟩
    have : A.valuation (ϖ : AlgebraicClosure ℚ) * A.valuation ((d' : ↥(coeffSubring A K)) : AlgebraicClosure ℚ) < 1 :=
      calc _ ≤ A.valuation (ϖ : AlgebraicClosure ℚ) * 1 := mul_le_mul_right hle _
        _ = _ := mul_one _
        _ < 1 := hϖlt
    exact absurd h1 this.ne

theorem ne_zero_of_forall_redRestrict {q : ℕ} [Fact q.Prime] (A : ValuationSubring (AlgebraicClosure ℚ))
    {k : Type*} [Field k] [CharP k q] (red : A →+* k)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) (ϖ : ↥(coeffSubring A K))
    (hϖ : ∀ d : ↥(coeffSubring A K), redRestrict red K d = 0 ↔ ∃ d', d = ϖ * d') :
    (ϖ : AlgebraicClosure ℚ) ≠ 0 := by
  intro h0
  have hq0 : redRestrict red K ((q : ℕ) : ↥(coeffSubring A K)) = 0 := by
    rw [map_natCast]; exact CharP.cast_eq_zero k q
  obtain ⟨d', hd'⟩ := (hϖ _).mp hq0
  have h1 := congrArg (fun z : ↥(coeffSubring A K) => (z : AlgebraicClosure ℚ)) hd'
  simp only [Subring.coe_natCast, Subring.coe_mul, h0, zero_mul] at h1
  exact (Nat.cast_ne_zero.mpr (Fact.out : q.Prime).ne_zero) h1

end DVR

section Enlarge

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
  {k : Type*} [Field k] [CharP k q] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
  {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
  {P : PlaceSpecialization A q N data hKr k red hα hβ}
  (R : ProlongationTuple P)

theorem fieldOver_mono (M : ℕ) [NeZero M] {K K' : IntermediateField ℚ (AlgebraicClosure ℚ)} (h : K ≤ K') :
    NodeLocalized.fieldOver M K ≤ NodeLocalized.fieldOver M K' := by
  unfold NodeLocalized.fieldOver
  apply Subfield.closure_mono
  apply Set.union_subset_union_left
  rintro _ ⟨c, rfl⟩
  exact ⟨⟨c, h c.2⟩, rfl⟩

theorem coeffSubring_mono (A : ValuationSubring (AlgebraicClosure ℚ)) {K K' : IntermediateField ℚ (AlgebraicClosure ℚ)}
    (h : K ≤ K') : NodeLocalized.coeffSubring A K ≤ NodeLocalized.coeffSubring A K' :=
  fun _ hc => ⟨hc.1, h hc.2⟩

theorem nodeIntegersOver_mono [PerfectField k] {K K' : IntermediateField ℚ (AlgebraicClosure ℚ)} (h : K ≤ K')
    (w : Place k (modularFunctionFieldC k N)) : R.nodeIntegersOver K w ≤ R.nodeIntegersOver K' w :=
  fun _ hf => ⟨hf.1, fieldOver_mono (N * q) h hf.2⟩

theorem valuation_pow_crossingExponent_eq [IsAlgClosed k] [DecidableEq k] (hqN : ¬ q ∣ N) (hq5 : 5 ≤ q)
    (hmodel : R.IsModel)
    (W : Finset (Place k (modularFunctionFieldC k N))) (hW : ∀ w ∈ W, w ∈ ssPlaces q N k)
    (hreg : R.RegularityLaw W) (hval : R.NodeValueLaw W) (hord : R.OrderLawFixed)
    (hred : Function.Surjective red)
    (hker : ∀ c : ↥A, red c = 0 ↔ c ∈ IsLocalRing.maximalIdeal ↥A)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
    (w : Place k (modularFunctionFieldC k N)) (hw : w ∈ W)
    (ϖ : ↥(NodeLocalized.coeffSubring A K))
    (hϖ : ∀ d : ↥(NodeLocalized.coeffSubring A K), NodeLocalized.redRestrict red K d = 0 ↔ ∃ d', d = ϖ * d')
    (c : R.NodeCoordinates K w) (E : ℕ) (u : ↥(R.nodeIntegersOver K w)) (hu : IsUnit u)
    (hxy : c.x * c.y = R.nodeConst K w ϖ ^ E * u) :
    A.valuation (ϖ : AlgebraicClosure ℚ) ^ E = A.valuation ((q : ℕ) : AlgebraicClosure ℚ) ^ placeWidth N w := by
  have hϖ0 : ((ϖ : ↥(NodeLocalized.coeffSubring A K)) : AlgebraicClosure ℚ) ≠ 0 :=
    ne_zero_of_forall_redRestrict A red K ϖ hϖ

  obtain ⟨xt, hxt⟩ := hred (w.evalAt (jGeomGen k N))

  have hxint : IsIntegral ℚ (xt : AlgebraicClosure ℚ) := Algebra.IsIntegral.isIntegral _
  haveI : FiniteDimensional ℚ ↥(IntermediateField.adjoin ℚ {(xt : AlgebraicClosure ℚ)}) :=
    IntermediateField.adjoin.finiteDimensional hxint
  set K' : IntermediateField ℚ (AlgebraicClosure ℚ) := K ⊔ IntermediateField.adjoin ℚ {(xt : AlgebraicClosure ℚ)} with hK'
  haveI : FiniteDimensional ℚ ↥K' := IntermediateField.finiteDimensional_sup _ _
  have hKK' : K ≤ K' := le_sup_left
  have hxtK' : (xt : AlgebraicClosure ℚ) ∈ K' :=
    (le_sup_right : IntermediateField.adjoin ℚ {(xt : AlgebraicClosure ℚ)} ≤ K') (IntermediateField.mem_adjoin_simple_self ℚ _)

  obtain ⟨ϖ', hϖ', eK', ε', heK', hε', hqe'⟩ :=
    ModularCurve.NodeLocalized.exists_forall_redRestrict_eq_zero_iff_and_natCast_eq_pow_mul red hker K'
  have hϖ'0' : ((ϖ' : ↥(NodeLocalized.coeffSubring A K')) : AlgebraicClosure ℚ) ≠ 0 :=
    ne_zero_of_forall_redRestrict A red K' ϖ' hϖ'
  have hϖ'0 : ϖ' ≠ 0 := fun h => hϖ'0' (by rw [h]; rfl)

  set ϖ₁ : ↥(NodeLocalized.coeffSubring A K') := ⟨(ϖ : AlgebraicClosure ℚ), coeffSubring_mono A hKK' ϖ.2⟩ with hϖ₁
  have hϖ₁0 : ϖ₁ ≠ 0 := fun h => hϖ0 (congrArg (fun z : ↥(NodeLocalized.coeffSubring A K') => (z : AlgebraicClosure ℚ)) h)
  haveI := ModularCurve.NodeLocalized.isDiscreteValuationRing_coeffSubring red hker K'
  have hirr := irreducible_of_forall_redRestrict A red hker K' ϖ' hϖ' hϖ'0
  obtain ⟨n, ηu, hfac⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hϖ₁0 hirr

  set cx : ↥(R.nodeIntegersOver K' w) := ⟨c.x, nodeIntegersOver_mono R hKK' _ c.x.2⟩ with hcx
  set cy : ↥(R.nodeIntegersOver K' w) := ⟨c.y, nodeIntegersOver_mono R hKK' _ c.y.2⟩ with hcy
  let c' : R.NodeCoordinates K' w := ⟨cx, cy, c.x_fst, c.x_snd, c.y_snd, c.y_fst⟩
  set u' : ↥(R.nodeIntegersOver K' w) :=
    R.nodeConst K' _ (ηu : ↥(NodeLocalized.coeffSubring A K')) ^ E * Subring.inclusion (nodeIntegersOver_mono R hKK' _) u
    with hu'
  have hu'unit : IsUnit u' := (ηu.isUnit.map _).pow E |>.mul (hu.map _)
  have hxy' : c'.x * c'.y = R.nodeConst K' _ ϖ' ^ (n * E) * u' := by
    apply Subtype.ext
    have h0 := congrArg (fun z : ↥(R.nodeIntegersOver K w) => (z : ↥(modularFunctionFieldBar (N * q)))) hxy
    have h1 := congrArg (fun z : ↥(NodeLocalized.coeffSubring A K') =>
      algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (z : AlgebraicClosure ℚ)) hfac
    simp only [MulMemClass.coe_mul, SubmonoidClass.coe_pow, coe_nodeConst, map_mul, map_pow] at h0 h1 ⊢
    show (c.x : ↥(modularFunctionFieldBar (N * q))) * c.y = _
    rw [h0]
    show algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (ϖ₁ : AlgebraicClosure ℚ) ^ E * _ = _
    rw [h1]
    simp only [hu', MulMemClass.coe_mul, SubmonoidClass.coe_pow, coe_nodeConst, Subring.coe_inclusion]
    ring

  have hxw : NodeLocalized.redRestrict red K' ⟨(xt : AlgebraicClosure ℚ), xt.2, hxtK'⟩ = w.evalAt (jGeomGen k N) := by
    rw [← hxt]; rfl
  have hE := ModularCurve.PlaceSpecialization.ProlongationTuple.crossingExponent_eq_placeWidth_mul_of_orderLawFixed
    R hqN hq5 hmodel W hW hreg hval hord hker K' w hw ⟨(xt : AlgebraicClosure ℚ), xt.2, hxtK'⟩ hxw ϖ' hϖ' eK' ε' hε' hqe'
    c' (n * E) u' hu'unit hxy'

  have hvη := valuation_eq_one_of_isUnit_coeffSubring A K' _ ηu.isUnit
  have hvε := valuation_eq_one_of_isUnit_coeffSubring A K' ε' hε'
  have hv₁ : A.valuation (ϖ : AlgebraicClosure ℚ) = A.valuation ((ϖ' : ↥(NodeLocalized.coeffSubring A K')) : AlgebraicClosure ℚ) ^ n := by
    have := congrArg (fun z : ↥(NodeLocalized.coeffSubring A K') => A.valuation (z : AlgebraicClosure ℚ)) hfac
    simp only [Subring.coe_mul, Subring.coe_pow, map_mul, map_pow, hvη, one_mul] at this
    exact this
  have hvq : A.valuation (((q : ℕ) : AlgebraicClosure ℚ)) = A.valuation ((ϖ' : ↥(NodeLocalized.coeffSubring A K')) : AlgebraicClosure ℚ) ^ eK' := by
    have := congrArg (fun z : ↥(NodeLocalized.coeffSubring A K') => A.valuation (z : AlgebraicClosure ℚ)) hqe'
    simp only [Subring.coe_natCast, Subring.coe_mul, Subring.coe_pow, map_mul, map_pow, hvε, mul_one] at this
    exact this
  rw [hv₁, hvq, ← pow_mul, ← pow_mul, hE]
  ring_nf

end Enlarge

section Places

variable {k : Type*} [Field k] {E : Type*} [Field E] [Algebra k E]

theorem ramificationIndexAlong_inclusion_eq_one_of_eq {S T : IntermediateField k E} (hST : S = T) (h : S ≤ T)
    (hι : (IntermediateField.inclusion h).toRingHom.IsIntegral) (W : Place k T) :
    Place.ramificationIndexAlong (IntermediateField.inclusion h) W = 1 := by
  subst hST
  have h1 : 1 ≤ Place.ramificationIndexAlong (IntermediateField.inclusion h) W :=
    Place.one_le_ramificationIndexAlong _ hι W
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible W.toValuationSubring
  have hord : W.ord (π : S) = 1 := W.ord_coe_irreducible hπ
  have h2 := W.ord_restrictAlong (IntermediateField.inclusion h) hι (π : S)
  have hid : IntermediateField.inclusion h (π : S) = (π : S) := Subtype.ext rfl
  rw [hid, hord] at h2
  have hdvd : (Place.ramificationIndexAlong (IntermediateField.inclusion h) W : ℤ) ∣ 1 := ⟨_, h2⟩
  have he : (Place.ramificationIndexAlong (IntermediateField.inclusion h) W : ℤ) = 1 :=
    Int.eq_one_of_dvd_one (by exact_mod_cast (Nat.zero_le _)) hdvd
  exact_mod_cast he

end Places

namespace KappaSide

theorem restrictAlong_eq_and_ramificationIndexAlong_mul_placeWidth_eq
    {k : Type*} [Field k] [IsAlgClosed k] [DecidableEq k] {q : ℕ} [Fact q.Prime] [CharP k q]
    {N ℓ : ℕ} [NeZero N] [NeZero ℓ] [NeZero (N * ℓ)] (hqNℓ : ¬ q ∣ N * ℓ) (hq5 : 5 ≤ q)
    (hαC : (heckeAlphaC k N ℓ).toRingHom.IsIntegral)
    (hroof : modularFunctionFieldC k (N * ℓ) ≤ charLDegeneracyRoof k N ℓ)
    (hroofι : (IntermediateField.inclusion hroof).toRingHom.IsIntegral)
    (y₁ : Place k (charLDegeneracyRoof k N ℓ)) (yP : Place k (modularFunctionFieldC k (N * ℓ)))
    (wP : Place k (modularFunctionFieldC k N))
    (hy₁y : y₁.restrictAlong (IntermediateField.inclusion hroof) hroofι = yP)
    (hy₁w : y₁.restrictAlong (heckeAlphaC k N ℓ) hαC = wP)
    (hyss : yP ∈ ssPlaces q (N * ℓ) k) :
    ∃ (hroof' : charLDegeneracyRoof k N ℓ ≤ modularFunctionFieldC k (N * ℓ))
      (hι' : (IntermediateField.inclusion hroof').toRingHom.IsIntegral),
      (yP.restrictAlong (IntermediateField.inclusion hroof') hι').restrictAlong (heckeAlphaC k N ℓ) hαC = wP ∧
      y₁.ramificationIndexAlong (heckeAlphaC k N ℓ) * placeWidth (N * ℓ) yP = placeWidth N wP := by
  have hroofeq : charLDegeneracyRoof k N ℓ = modularFunctionFieldC k (N * ℓ) :=
    (ModularCurve.charLDegeneracyRoof_eq_modularFunctionFieldFullC_mul k q N ℓ hqNℓ).trans
      (ModularCurve.modularFunctionFieldC_eq_modularFunctionFieldFullC k q (N * ℓ) hqNℓ).symm
  have hCle : modularFunctionFieldC k N ≤ modularFunctionFieldC k (N * ℓ) :=
    (modularFunctionFieldC_le_charLDegeneracyRoof k N ℓ).trans hroofeq.le
  have hroof' : charLDegeneracyRoof k N ℓ ≤ modularFunctionFieldC k (N * ℓ) := hroofeq.le

  have hι' : (IntermediateField.inclusion hroof').toRingHom.IsIntegral := by
    apply RingHom.isIntegral_of_surjective
    intro z
    exact ⟨IntermediateField.inclusion hroof z, Subtype.ext
      ((IntermediateField.coe_inclusion hroof' (IntermediateField.inclusion hroof z)).trans
        (IntermediateField.coe_inclusion hroof z))⟩
  set φ0 : modularFunctionFieldC k N →ₐ[k] modularFunctionFieldC k (N * ℓ) :=
    IntermediateField.inclusion hCle with hφ0def
  have hcomp : (IntermediateField.inclusion hroof).comp φ0 = heckeAlphaC k N ℓ :=
    AlgHom.ext fun x => Subtype.ext <|
      (congrArg Subtype.val (AlgHom.comp_apply (IntermediateField.inclusion hroof) φ0 x)).trans <|
        (IntermediateField.coe_inclusion hroof (φ0 x)).trans <|
          (IntermediateField.coe_inclusion hCle x).trans (coe_heckeAlphaC k N ℓ x).symm
  have hcomp' : (IntermediateField.inclusion hroof').comp (heckeAlphaC k N ℓ) = φ0 :=
    AlgHom.ext fun x => Subtype.ext <|
      (congrArg Subtype.val (AlgHom.comp_apply (IntermediateField.inclusion hroof') (heckeAlphaC k N ℓ) x)).trans <|
        (IntermediateField.coe_inclusion hroof' (heckeAlphaC k N ℓ x)).trans <|
          (coe_heckeAlphaC k N ℓ x).trans (IntermediateField.coe_inclusion hCle x).symm
  have hχφ : ((IntermediateField.inclusion hroof).comp φ0).toRingHom.IsIntegral := by rw [hcomp]; exact hαC
  have hχφ' : ((IntermediateField.inclusion hroof').comp (heckeAlphaC k N ℓ)).toRingHom.IsIntegral :=
    RingHom.IsIntegral.trans (heckeAlphaC k N ℓ).toRingHom (IntermediateField.inclusion hroof').toRingHom hαC hι'
  have hφ0 : φ0.toRingHom.IsIntegral := by rw [← hcomp']; exact hχφ'
  have hyw : yP.restrictAlong φ0 hφ0 = wP := by
    have h1 := Place.restrictAlong_restrictAlong φ0 (IntermediateField.inclusion hroof) hφ0 hroofι hχφ y₁
    have h2 := Place.restrictAlong_congr hcomp hχφ hαC y₁
    have h0 := congrArg (Place.restrictAlong φ0 hφ0) hy₁y
    exact h0.symm.trans (h1.trans (h2.trans hy₁w))
  have he : y₁.ramificationIndexAlong (heckeAlphaC k N ℓ) = yP.ramificationIndexAlong φ0 := by
    have h1 := Place.ramificationIndexAlong_comp φ0 (IntermediateField.inclusion hroof) hφ0 hroofι hχφ y₁
    have h3 : Place.ramificationIndexAlong (IntermediateField.inclusion hroof) y₁ = 1 :=
      ramificationIndexAlong_inclusion_eq_one_of_eq hroofeq.symm hroof hroofι y₁
    have h4 := congrArg (Place.ramificationIndexAlong φ0) hy₁y
    have h5 := congrArg (fun ψ => Place.ramificationIndexAlong ψ y₁) hcomp
    exact h5.symm.trans (h1.trans ((congrArg₂ (· * ·) h3 h4).trans (one_mul _)))
  have hdiv : placeRamificationJ (N * ℓ) yP ∣ jWidth (yP.evalAt (jGeomGen k (N * ℓ))) :=
    ModularCurve.placeRamificationJ_dvd_jWidth_of_mem_ssPlaces hq5 hqNℓ hyss
  have hwidth : y₁.ramificationIndexAlong (heckeAlphaC k N ℓ) * placeWidth (N * ℓ) yP = placeWidth N wP := by
    have h1 := ModularCurve.ramificationIndexAlong_mul_placeWidth_eq_placeWidth_restrictAlong_of_coe_eq N (N * ℓ) φ0 hφ0
      (fun x => IntermediateField.coe_inclusion hCle x) yP hdiv
    rw [hyw, ← he] at h1
    exact h1
  refine ⟨hroof', hι', ?_, hwidth⟩
  have e1 := Place.restrictAlong_restrictAlong (heckeAlphaC k N ℓ) (IntermediateField.inclusion hroof') hαC hι' hχφ' yP
  have e2 := Place.restrictAlong_congr hcomp' hχφ' hφ0 yP
  exact e1.trans (e2.trans hyw)

end KappaSide

namespace BarSide

theorem reduceFst_restrictAlong_towerInclBar_eq
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N] [NeZero q]
    {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    (P : PlaceSpecialization A q N data hKr k red hα hβ)
    {ℓ : ℕ} [NeZero ℓ] [NeZero (N * ℓ)]
    {hαᵣ : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) (N * ℓ) q} {hβᵣ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) (N * ℓ) q}
    (Pᵣ : PlaceSpecialization A q (N * ℓ) data hKr k red hαᵣ hβᵣ)
    (hαℓ : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N ℓ)
    (hι : (towerInclBar (AlgebraicClosure ℚ)
      (mul_dvd_mul_right (dvd_mul_right N ℓ) q : N * q ∣ N * ℓ * q)).toRingHom.IsIntegral)
    (hαC : (heckeAlphaC k N ℓ).toRingHom.IsIntegral)
    (hroof' : charLDegeneracyRoof k N ℓ ≤ modularFunctionFieldC k (N * ℓ))
    (hι' : (IntermediateField.inclusion hroof').toRingHom.IsIntegral)
    (hspec : ∀ W₀ : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * ℓ)),
      ((Pᵣ.sp W₀).restrictAlong (IntermediateField.inclusion hroof') hι').restrictAlong (heckeAlphaC k N ℓ) hαC
        = P.sp (W₀.restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) N ℓ) hαℓ))
    (yP : Place k (modularFunctionFieldC k (N * ℓ))) (wP : Place k (modularFunctionFieldC k N))
    (hκ : (yP.restrictAlong (IntermediateField.inclusion hroof') hι').restrictAlong (heckeAlphaC k N ℓ) hαC = wP)
    (V'' : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * ℓ * q))) (hV'' : Pᵣ.reduceFst V'' = yP) :
    P.reduceFst (V''.restrictAlong (towerInclBar (AlgebraicClosure ℚ)
      (mul_dvd_mul_right (dvd_mul_right N ℓ) q : N * q ∣ N * ℓ * q)) hι) = wP := by
  have hN : N ∣ N * ℓ * q := (dvd_mul_right N ℓ).trans (dvd_mul_right (N * ℓ) q)
  have hT : (towerInclBar (AlgebraicClosure ℚ) hN).toRingHom.IsIntegral :=
    ModularCurve.towerInclBar_isIntegral (AlgebraicClosure ℚ) hN

  have h1 : (towerInclBar (AlgebraicClosure ℚ) (mul_dvd_mul_right (dvd_mul_right N ℓ) q : N * q ∣ N * ℓ * q)).comp
      (heckeAlphaBar (AlgebraicClosure ℚ) N q) = towerInclBar (AlgebraicClosure ℚ) hN :=
    towerInclBar_comp_heckeAlphaBar (AlgebraicClosure ℚ) q (mul_dvd_mul_right (dvd_mul_right N ℓ) q : N * q ∣ N * ℓ * q) hN
  have h2 : (heckeAlphaBar (AlgebraicClosure ℚ) (N * ℓ) q).comp (heckeAlphaBar (AlgebraicClosure ℚ) N ℓ)
      = towerInclBar (AlgebraicClosure ℚ) hN :=
    towerInclBar_comp_heckeAlphaBar (AlgebraicClosure ℚ) ℓ (dvd_mul_right (N * ℓ) q) hN
  have h1i : ((towerInclBar (AlgebraicClosure ℚ) (mul_dvd_mul_right (dvd_mul_right N ℓ) q : N * q ∣ N * ℓ * q)).comp
      (heckeAlphaBar (AlgebraicClosure ℚ) N q)).toRingHom.IsIntegral := by rw [h1]; exact hT
  have h2i : ((heckeAlphaBar (AlgebraicClosure ℚ) (N * ℓ) q).comp
      (heckeAlphaBar (AlgebraicClosure ℚ) N ℓ)).toRingHom.IsIntegral := by rw [h2]; exact hT
  have e1 := Place.restrictAlong_restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q)
    (towerInclBar (AlgebraicClosure ℚ) (mul_dvd_mul_right (dvd_mul_right N ℓ) q : N * q ∣ N * ℓ * q)) hα hι h1i V''
  have e2 := Place.restrictAlong_congr (h1.trans h2.symm) h1i h2i V''
  have e3 := Place.restrictAlong_restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) N ℓ)
    (heckeAlphaBar (AlgebraicClosure ℚ) (N * ℓ) q) hαℓ hαᵣ h2i V''
  have hW := e1.trans (e2.trans e3.symm)
  have hV''' : Pᵣ.sp (V''.restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) (N * ℓ) q) hαᵣ) = yP := hV''
  show P.sp ((V''.restrictAlong (towerInclBar (AlgebraicClosure ℚ)
      (mul_dvd_mul_right (dvd_mul_right N ℓ) q : N * q ∣ N * ℓ * q)) hι).restrictAlong
      (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα) = wP
  have e4 := congrArg (fun z => Place.restrictAlong (heckeAlphaC k N ℓ) hαC
    (Place.restrictAlong (IntermediateField.inclusion hroof') hι' z)) hV'''
  exact (congrArg P.sp hW).trans ((hspec _).symm.trans (e4.trans hκ))

end BarSide

end DepthTransport

open DepthTransport in
set_option maxHeartbeats 12800000 in
theorem solution
    (N q : ℕ) [NeZero N] (hq : q.Prime) (hqN : ¬ q ∣ N) (hq5 : 5 ≤ q)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q) :
    haveI : NeZero q := ⟨hq.ne_zero⟩
    haveI : Fact q.Prime := ⟨hq⟩
    haveI : CharP (ResidueField A) q := ValuationSubring.charP_residueField_of_liesOverPrime_def hq hA
    letI := instDecidableEqResidueFieldSemistable A
    letI := instAlgebraResidueFieldModularFunctionFieldCSemistable A N
    ∀ (W : Finset (Place (ResidueField A) (modularFunctionFieldC (ResidueField A) N)))
      (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q N (ResidueField A))
      (data : ModularPolynomialData q) (hKr : KroneckerCongruence q data)
      (hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q)
      (hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q)
      (P : PlaceSpecialization A q N data hKr (ResidueField A) (IsLocalRing.residue A) hα hβ)
      (R : PlaceSpecialization.ProlongationTuple P) (hmodel : R.IsModel) (hO : R.OrderLawFixed)
      (hreg : R.RegularityLaw W) (hval : R.NodeValueLaw W)
      (Ks : ↥W → IntermediateField ℚ (AlgebraicClosure ℚ)) [∀ w : ↥W, FiniteDimensional ℚ (Ks w)]
      (cs : ∀ w : ↥W, R.NodeCoordinates (Ks w) (w : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) N)))
      (ϖ : ∀ w : ↥W, ↥(NodeLocalized.coeffSubring A (Ks w)))
      (hϖ : ∀ (w : ↥W) (d : ↥(NodeLocalized.coeffSubring A (Ks w))), NodeLocalized.redRestrict (IsLocalRing.residue A) (Ks w) d = 0 ↔ ∃ d', d = ϖ w * d')
      (hvalA : ∀ w : ↥W, R.ValueIntegralityLaw (w : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) N)))
      (hxy : ∀ w : ↥W, ∃ (E : ℕ) (u : ↥(R.nodeIntegersOver (Ks w) (w : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) N)))),
        1 ≤ E ∧ IsUnit u ∧ (cs w).x * (cs w).y = R.nodeConst (Ks w) (w : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) N)) (ϖ w) ^ E * u),
        ∀ (ℓ : Nat.Primes), (ℓ : ℕ) ≠ q →
        haveI : NeZero (ℓ : ℕ) := ⟨ℓ.2.ne_zero⟩
        letI := instAlgebraResidueFieldModularFunctionFieldCSemistable A (N * ℓ)
        ∀ (Wᵣ : Finset (Place (ResidueField A) (modularFunctionFieldC (ResidueField A) (N * ℓ))))
          (hWᵣ : ∀ w, w ∈ Wᵣ ↔ w ∈ ssPlaces q (N * ℓ) (ResidueField A))
          (hαᵣ : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) (N * ℓ) q)
          (hβᵣ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) (N * ℓ) q)
          (Pᵣ : PlaceSpecialization A q (N * ℓ) data hKr (ResidueField A) (IsLocalRing.residue A) hαᵣ hβᵣ)
          (Rᵣ : PlaceSpecialization.ProlongationTuple Pᵣ) (hmodelᵣ : Rᵣ.IsModel) (hOᵣ : Rᵣ.OrderLawFixed)
          (hregᵣ : Rᵣ.RegularityLaw Wᵣ) (hvalᵣ : Rᵣ.NodeValueLaw Wᵣ)
          (Ksᵣ : ↥Wᵣ → IntermediateField ℚ (AlgebraicClosure ℚ)) [∀ w : ↥Wᵣ, FiniteDimensional ℚ (Ksᵣ w)]
          (csᵣ : ∀ w : ↥Wᵣ, Rᵣ.NodeCoordinates (Ksᵣ w) (w : Place (ResidueField A) (modularFunctionFieldC
              (ResidueField A) (N * ℓ))))
          (ϖᵣ : ∀ w : ↥Wᵣ, ↥(NodeLocalized.coeffSubring A (Ksᵣ w)))
          (hϖᵣ : ∀ (w : ↥Wᵣ) (d : ↥(NodeLocalized.coeffSubring A (Ksᵣ w))), NodeLocalized.redRestrict
              (IsLocalRing.residue A) (Ksᵣ w) d = 0 ↔ ∃ d', d = ϖᵣ w * d')
          (hvalAᵣ : ∀ w : ↥Wᵣ, Rᵣ.ValueIntegralityLaw (w : Place (ResidueField A) (modularFunctionFieldC (ResidueField
              A) (N * ℓ))))
          (hxyᵣ : ∀ w : ↥Wᵣ, ∃ (E : ℕ) (u : ↥(Rᵣ.nodeIntegersOver (Ksᵣ w) (w : Place (ResidueField A)
              (modularFunctionFieldC (ResidueField A) (N * ℓ))))),
          1 ≤ E ∧ IsUnit u ∧ (csᵣ w).x * (csᵣ w).y = Rᵣ.nodeConst (Ksᵣ w) (w : Place (ResidueField A)
              (modularFunctionFieldC (ResidueField A) (N * ℓ))) (ϖᵣ w) ^ E * u),
        ∀ (hι : (towerInclBar (AlgebraicClosure ℚ)
                  (mul_dvd_mul_right (dvd_mul_right N ℓ) q : N * q ∣ N * ℓ * q)).toRingHom.IsIntegral)
          (hαC : (heckeAlphaC (ResidueField A) N ℓ).toRingHom.IsIntegral)
          (hroof : modularFunctionFieldC (ResidueField A) (N * ℓ) ≤ charLDegeneracyRoof (ResidueField A) N ℓ)
          (hroofι : (IntermediateField.inclusion hroof).toRingHom.IsIntegral)
          (y₁ : Place (ResidueField A) (charLDegeneracyRoof (ResidueField A) N ℓ))
          (y : ↥Wᵣ) (w : ↥W),
          y₁.restrictAlong (IntermediateField.inclusion hroof) hroofι = (y : Place (ResidueField A)
              (modularFunctionFieldC (ResidueField A) (N * ℓ))) →
          y₁.restrictAlong (heckeAlphaC (ResidueField A) N ℓ) hαC = (w : Place (ResidueField A)
              (modularFunctionFieldC (ResidueField A) N)) →
          ∀ (V' : Place (AlgebraicClosure ℚ)
              (laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull (N * ℓ * q)))),
            Pᵣ.reduceFst V' = y →
            P.reduceFst (V'.restrictAlong (towerInclBar (AlgebraicClosure ℚ)
                (mul_dvd_mul_right (dvd_mul_right N ℓ) q : N * q ∣ N * ℓ * q)) hι) = w →
            (cs w).yDepth (V'.restrictAlong (towerInclBar (AlgebraicClosure ℚ)
                  (mul_dvd_mul_right (dvd_mul_right N ℓ) q : N * q ∣ N * ℓ * q)) hι)
                = (csᵣ y).yDepth V' ^ y₁.ramificationIndexAlong (heckeAlphaC (ResidueField A) N ℓ) ∧
              (P.IsStrictFst (V'.restrictAlong (towerInclBar (AlgebraicClosure ℚ)
                  (mul_dvd_mul_right (dvd_mul_right N ℓ) q : N * q ∣ N * ℓ * q)) hι) ↔ Pᵣ.IsStrictFst V') := by
  haveI : NeZero q := ⟨hq.ne_zero⟩
  haveI hqF : Fact q.Prime := ⟨hq⟩
  haveI : CharP (ResidueField A) q := ValuationSubring.charP_residueField_of_liesOverPrime_def hq hA
  letI := instDecidableEqResidueFieldSemistable A
  letI := instAlgebraResidueFieldModularFunctionFieldCSemistable A N
  intro W hW data hKr hα hβ P R hmodel hO hreg hval Ks _iK cs ϖ hϖ hvalA hxy ℓ hℓq
  haveI : NeZero (ℓ : ℕ) := ⟨ℓ.2.ne_zero⟩
  letI := instAlgebraResidueFieldModularFunctionFieldCSemistable A (N * ℓ)
  intro Wᵣ hWᵣ hαᵣ hβᵣ Pᵣ Rᵣ hmodelᵣ hOᵣ hregᵣ hvalᵣ Ksᵣ _iKᵣ csᵣ ϖᵣ hϖᵣ hvalAᵣ hxyᵣ hι hαC hroof hroofι y₁ y w hy₁y hy₁w
    V' hVy hVw

  haveI : IsAlgClosed (ResidueField A) := ValuationSubring.isAlgClosed_residueField_algebraicClosure_rat A
  have hW' : ∀ w ∈ W, w ∈ ssPlaces q N (ResidueField A) := fun w hw => (hW w).mp hw
  have hWᵣ' : ∀ w ∈ Wᵣ, w ∈ ssPlaces q (N * ℓ) (ResidueField A) := fun w hw => (hWᵣ w).mp hw
  have hqℓ : ¬ q ∣ (ℓ : ℕ) := fun h => by
    rcases (Nat.dvd_prime ℓ.2).mp h with h1 | h1
    · exact hq.one_lt.ne' h1
    · exact hℓq h1.symm
  have hqNℓ : ¬ q ∣ N * ℓ := fun h => by
    rcases hq.dvd_mul.mp h with h1 | h1
    · exact hqN h1
    · exact hqℓ h1
  have hker : ∀ c : ↥A, IsLocalRing.residue A c = 0 ↔ c ∈ IsLocalRing.maximalIdeal ↥A :=
    fun c => IsLocalRing.residue_eq_zero_iff c
  have hred : Function.Surjective (IsLocalRing.residue A) := IsLocalRing.residue_surjective

  set incl := towerInclBar (AlgebraicClosure ℚ) (mul_dvd_mul_right (dvd_mul_right N ℓ) q : N * q ∣ N * ℓ * q) with hincl
  set V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) := V'.restrictAlong incl hι with hV
  set wP : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) N) :=
    (w : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) N)) with hwP
  set yP : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) (N * ℓ)) :=
    (y : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) (N * ℓ))) with hyP

  have hnsV : ¬ P.IsStrictFst V :=
    not_isStrictFst_of_reduceFst_mem_ssPlaces hqN V (by rw [hVw]; exact hW' _ w.2)
  have hnsV' : ¬ Pᵣ.IsStrictFst V' :=
    not_isStrictFst_of_reduceFst_mem_ssPlaces hqNℓ V' (by rw [hVy]; exact hWᵣ' _ y.2)
  refine ⟨?_, ⟨fun h => absurd h hnsV, fun h => absurd h hnsV'⟩⟩

  have hxy_w := hxy w
  obtain ⟨E, u, hE, hu, hxyw⟩ := hxy_w
  have hxy_y := hxyᵣ y
  obtain ⟨Eᵣ, uᵣ, hEᵣ, huᵣ, hxyy⟩ := hxy_y

  have hvw : A.valuation ((ϖ w : ↥(NodeLocalized.coeffSubring A (Ks w))) : AlgebraicClosure ℚ) ^ E
      = A.valuation ((q : ℕ) : AlgebraicClosure ℚ) ^ placeWidth N wP :=
    valuation_pow_crossingExponent_eq R hqN hq5 hmodel W hW' hreg hval hO hred hker (Ks w) wP w.2 (ϖ w) (hϖ w)
      (cs w) E u hu hxyw
  have hvy : A.valuation ((ϖᵣ y : ↥(NodeLocalized.coeffSubring A (Ksᵣ y))) : AlgebraicClosure ℚ) ^ Eᵣ
      = A.valuation ((q : ℕ) : AlgebraicClosure ℚ) ^ placeWidth (N * ℓ) yP :=
    valuation_pow_crossingExponent_eq Rᵣ hqNℓ hq5 hmodelᵣ Wᵣ hWᵣ' hregᵣ hvalᵣ hOᵣ hred hker (Ksᵣ y) yP y.2 (ϖᵣ y) (hϖᵣ y)
      (csᵣ y) Eᵣ uᵣ huᵣ hxyy

  obtain ⟨hroof', hι', hsqκ, hwidth⟩ :=
    KappaSide.restrictAlong_eq_and_ramificationIndexAlong_mul_placeWidth_eq (k := ResidueField A) hqNℓ hq5 hαC hroof hroofι
      y₁ yP wP hy₁y hy₁w (hWᵣ' _ y.2)

  have hαℓ : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N ℓ :=
    ModularCurve.towerInclBar_isIntegral (AlgebraicClosure ℚ) (dvd_mul_right N ℓ)
  haveI : Fact (ℓ : ℕ).Prime := ⟨ℓ.2⟩
  have hβℓ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N ℓ := by
    unfold HeckeBetaBarIntegral
    rw [heckeBetaBar_eq_towerSubstBar]
    exact ModularCurve.towerSubstBar_isIntegral (AlgebraicClosure ℚ) (ℓ : ℕ) dvd_rfl
  have hβC : (heckeBetaC (ResidueField A) N ℓ).toRingHom.IsIntegral :=
    ModularCurve.heckeBetaCIntegral_unconditional (ResidueField A) N ℓ
  have hspec := fun W₀ => (ModularCurve.PlaceSpecialization.restrictAlong_heckeAlphaC_sp_and_restrictAlong_heckeBetaC_sp_eq_sp_restrictAlong_of_isModel
    N q hq hqN A hA data hKr hα hβ P R hmodel hO ℓ hℓq hαᵣ hβᵣ Pᵣ Rᵣ hmodelᵣ hOᵣ hαℓ hβℓ hαC hβC hroof' hι' W₀).1
  have hsq : ∀ V'' : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * ℓ * q)), Pᵣ.reduceFst V'' = yP →
      P.reduceFst (V''.restrictAlong incl hι) = wP := fun V'' hV'' =>
    BarSide.reduceFst_restrictAlong_towerInclBar_eq P Pᵣ hαℓ hι hαC hroof' hι' hspec yP wP hsqκ V'' hV''

  set e : ℕ := y₁.ramificationIndexAlong (heckeAlphaC (ResidueField A) N ℓ) with hedef
  set aQ : AlgebraicClosure ℚ := ((ϖ w : ↥(NodeLocalized.coeffSubring A (Ks w))) : AlgebraicClosure ℚ) ^ E with haQ
  set aQ' : AlgebraicClosure ℚ := ((ϖᵣ y : ↥(NodeLocalized.coeffSubring A (Ksᵣ y))) : AlgebraicClosure ℚ) ^ Eᵣ with haQ'
  clear_value aQ aQ'
  have hth : A.valuation aQ = A.valuation aQ' ^ e := by
    rw [haQ, haQ', map_pow, map_pow, hvw, hvy, ← pow_mul, mul_comm, hwidth]
  have haQ0 : aQ ≠ 0 := by rw [haQ]; exact pow_ne_zero _ (ne_zero_of_forall_redRestrict A _ (Ks w) (ϖ w) (hϖ w))
  have haQ'0 : aQ' ≠ 0 := by rw [haQ']; exact pow_ne_zero _ (ne_zero_of_forall_redRestrict A _ (Ksᵣ y) (ϖᵣ y) (hϖᵣ y))
  set cQ : AlgebraicClosure ℚ := aQ * (aQ' ^ e)⁻¹ with hcQ
  clear_value cQ
  have hvc : A.valuation cQ = 1 := by
    have hne : A.valuation aQ' ^ e ≠ 0 := pow_ne_zero _ ((Valuation.ne_zero_iff _).mpr haQ'0)
    rw [hcQ, map_mul, map_inv₀, hth, map_pow, mul_inv_cancel₀ hne]
  have hcA : cQ ∈ A := (A.valuation_le_one_iff _).mp hvc.le
  have hciA : cQ⁻¹ ∈ A := (A.valuation_le_one_iff _).mp (by rw [map_inv₀, hvc, inv_one])
  have hcQ0 : cQ ≠ 0 := by rw [hcQ]; exact mul_ne_zero haQ0 (inv_ne_zero (pow_ne_zero _ haQ'0))

  set x : ↥(modularFunctionFieldBar (N * q)) := ((cs w).x : ↥(modularFunctionFieldBar (N * q))) with hx
  set yv : ↥(modularFunctionFieldBar (N * q)) := ((cs w).y : ↥(modularFunctionFieldBar (N * q))) with hyv
  set uF : ↥(modularFunctionFieldBar (N * q)) := (u : ↥(modularFunctionFieldBar (N * q))) with huF
  set x' : ↥(modularFunctionFieldBar (N * ℓ * q)) := ((csᵣ y).x : ↥(modularFunctionFieldBar (N * ℓ * q))) with hx'
  set y' : ↥(modularFunctionFieldBar (N * ℓ * q)) := ((csᵣ y).y : ↥(modularFunctionFieldBar (N * ℓ * q))) with hy'
  set uF' : ↥(modularFunctionFieldBar (N * ℓ * q)) := (uᵣ : ↥(modularFunctionFieldBar (N * ℓ * q))) with huF'
  set aF : ↥(modularFunctionFieldBar (N * q)) := algebraMap (AlgebraicClosure ℚ) _ aQ with haF
  set aF' : ↥(modularFunctionFieldBar (N * ℓ * q)) := algebraMap (AlgebraicClosure ℚ) _ aQ' with haF'
  have hxyF : x * yv = aF * uF := by
    have h1 := congrArg (fun z : ↥(R.nodeIntegersOver (Ks w) wP) => (z : ↥(modularFunctionFieldBar (N * q)))) hxyw
    simp only [MulMemClass.coe_mul, SubmonoidClass.coe_pow, coe_nodeConst, ← map_pow] at h1
    rw [← haQ] at h1
    exact h1
  have hxyF' : x' * y' = aF' * uF' := by
    have h1 := congrArg (fun z : ↥(Rᵣ.nodeIntegersOver (Ksᵣ y) yP) => (z : ↥(modularFunctionFieldBar (N * ℓ * q)))) hxyy
    simp only [MulMemClass.coe_mul, SubmonoidClass.coe_pow, coe_nodeConst, ← map_pow] at h1
    rw [← haQ'] at h1
    exact h1

  have hxn : x ∈ R.nodeIntegers wP := R.nodeIntegersOver_le _ _ (cs w).x.2
  have hyn : yv ∈ R.nodeIntegers wP := R.nodeIntegersOver_le _ _ (cs w).y.2
  have hun : uF ∈ R.nodeIntegers wP := R.nodeIntegersOver_le _ _ u.2
  have huin : uF⁻¹ ∈ R.nodeIntegers wP := R.nodeIntegersOver_le _ _ (inv_mem_subring_of_isUnit u.2 hu)
  have hxn' : x' ∈ Rᵣ.nodeIntegers yP := Rᵣ.nodeIntegersOver_le _ _ (csᵣ y).x.2
  have hyn' : y' ∈ Rᵣ.nodeIntegers yP := Rᵣ.nodeIntegersOver_le _ _ (csᵣ y).y.2
  have hun' : uF' ∈ Rᵣ.nodeIntegers yP := Rᵣ.nodeIntegersOver_le _ _ uᵣ.2
  have huin' : uF'⁻¹ ∈ Rᵣ.nodeIntegers yP := Rᵣ.nodeIntegersOver_le _ _ (inv_mem_subring_of_isUnit uᵣ.2 huᵣ)

  have hUy : IsUnit (⟨yv, R.mem_integersFst_of_mem_nodeIntegers hyn⟩ : R.R₁.integers) := by
    apply R.R₁.isUnit_of_residue_ne_zero
    intro h; apply (cs w).nodeResidue₁_y_ne_zero
    rw [nodeResidue₁_apply, residue₁_apply]; exact (congrArg R.ι h).trans (map_zero _)
  have hUx : IsUnit (⟨x, R.mem_integersSnd_of_mem_nodeIntegers hxn⟩ : R.R₂.integers) := by
    apply R.R₂.isUnit_of_residue_ne_zero
    intro h; apply (cs w).nodeResidue₂_x_ne_zero
    rw [nodeResidue₂_apply, residue₂_apply]; exact (congrArg R.ι h).trans (map_zero _)
  have hUy' : IsUnit (⟨y', Rᵣ.mem_integersFst_of_mem_nodeIntegers hyn'⟩ : Rᵣ.R₁.integers) := by
    apply Rᵣ.R₁.isUnit_of_residue_ne_zero
    intro h; apply (csᵣ y).nodeResidue₁_y_ne_zero
    rw [nodeResidue₁_apply, residue₁_apply]; exact (congrArg Rᵣ.ι h).trans (map_zero _)
  have hUx' : IsUnit (⟨x', Rᵣ.mem_integersSnd_of_mem_nodeIntegers hxn'⟩ : Rᵣ.R₂.integers) := by
    apply Rᵣ.R₂.isUnit_of_residue_ne_zero
    intro h; apply (csᵣ y).nodeResidue₂_x_ne_zero
    rw [nodeResidue₂_apply, residue₂_apply]; exact (congrArg Rᵣ.ι h).trans (map_zero _)
  have hy0 : yv ≠ 0 := fun h => hUy.ne_zero (Subtype.ext h)
  have hx0 : x ≠ 0 := fun h => hUx.ne_zero (Subtype.ext h)
  have hy0' : y' ≠ 0 := fun h => hUy'.ne_zero (Subtype.ext h)
  have hx0' : x' ≠ 0 := fun h => hUx'.ne_zero (Subtype.ext h)
  have haF0 : aF ≠ 0 := by rw [haF]; exact (map_ne_zero _).mpr haQ0
  have haF'0 : aF' ≠ 0 := by rw [haF']; exact (map_ne_zero _).mpr haQ'0
  have hu0 : uF ≠ 0 := by intro h; apply mul_ne_zero hx0 hy0; rw [hxyF, h, mul_zero]
  have hu0' : uF' ≠ 0 := by intro h; apply mul_ne_zero hx0' hy0'; rw [hxyF', h, mul_zero]

  have hGy := ModularCurve.PlaceSpecialization.ProlongationTuple.exists_mem_integers_towerInclBar_and_coe_residue_eq
    R ℓ hqNℓ Rᵣ yv
  have hGx := ModularCurve.PlaceSpecialization.ProlongationTuple.exists_mem_integers_towerInclBar_and_coe_residue_eq
    R ℓ hqNℓ Rᵣ x
  have hGu := ModularCurve.PlaceSpecialization.ProlongationTuple.exists_mem_integers_towerInclBar_and_coe_residue_eq
    R ℓ hqNℓ Rᵣ uF
  have hGui := ModularCurve.PlaceSpecialization.ProlongationTuple.exists_mem_integers_towerInclBar_and_coe_residue_eq
    R ℓ hqNℓ Rᵣ uF⁻¹
  obtain ⟨hIy1, hIy1res⟩ := hGy.1 (R.mem_integersFst_of_mem_nodeIntegers hyn)
  obtain ⟨hIy2, -⟩ := hGy.2 (R.mem_integersSnd_of_mem_nodeIntegers hyn)
  obtain ⟨hIx1, -⟩ := hGx.1 (R.mem_integersFst_of_mem_nodeIntegers hxn)
  obtain ⟨hIx2, hIx2res⟩ := hGx.2 (R.mem_integersSnd_of_mem_nodeIntegers hxn)
  obtain ⟨hIu1, -⟩ := hGu.1 (R.mem_integersFst_of_mem_nodeIntegers hun)
  obtain ⟨hIu2, -⟩ := hGu.2 (R.mem_integersSnd_of_mem_nodeIntegers hun)
  obtain ⟨hIui1, -⟩ := hGui.1 (R.mem_integersFst_of_mem_nodeIntegers huin)
  obtain ⟨hIui2, -⟩ := hGui.2 (R.mem_integersSnd_of_mem_nodeIntegers huin)

  have hUIy : IsUnit (⟨incl yv, hIy1⟩ : Rᵣ.R₁.integers) := by
    apply Rᵣ.R₁.isUnit_of_residue_ne_zero
    intro h
    apply (cs w).nodeResidue₁_y_ne_zero
    have h2 : ((Rᵣ.residue₁ ⟨incl yv, hIy1⟩ : ↥(modularFunctionFieldC (ResidueField A) (N * ℓ))) :
        LaurentSeries (ResidueField A)) = 0 := by
      rw [residue₁_apply, h, map_zero, ZeroMemClass.coe_zero]
    rw [hIy1res, ZeroMemClass.coe_eq_zero] at h2
    rw [nodeResidue₁_apply]
    exact h2
  have hUIx : IsUnit (⟨incl x, hIx2⟩ : Rᵣ.R₂.integers) := by
    apply Rᵣ.R₂.isUnit_of_residue_ne_zero
    intro h
    apply (cs w).nodeResidue₂_x_ne_zero
    have h2 : ((Rᵣ.residue₂ ⟨incl x, hIx2⟩ : ↥(modularFunctionFieldC (ResidueField A) (N * ℓ))) :
        LaurentSeries (ResidueField A)) = 0 := by
      rw [residue₂_apply, h, map_zero, ZeroMemClass.coe_zero]
    rw [hIx2res, ZeroMemClass.coe_eq_zero] at h2
    rw [nodeResidue₂_apply]
    exact h2
  have hIy0 : incl yv ≠ 0 := (map_ne_zero incl).mpr hy0
  have hIx0 : incl x ≠ 0 := (map_ne_zero incl).mpr hx0

  have hmemV : ∀ {g : ↥(modularFunctionFieldBar (N * q))}, g ∈ R.nodeIntegers wP →
      ∀ V'' : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * ℓ * q)), Pᵣ.reduceFst V'' = yP →
        incl g ∈ V''.toValuationSubring := by
    intro g hg V'' hV''
    have h1 : g ∈ (V''.restrictAlong incl hι).toValuationSubring :=
      R.mem_toValuationSubring_of_mem_nodeIntegers hg (hsq V'' hV'')

    rcases eq_or_ne g 0 with hg0 | hg0
    · rw [hg0, map_zero]; exact zero_mem _
    · exact Place.mem_of_ord_nonneg V'' ((map_ne_zero incl).mpr hg0)
        ((mul_nonneg (Int.natCast_nonneg _) (Place.ord_nonneg_of_mem _ h1)).trans_eq
          (Place.ord_restrictAlong incl hι V'' g).symm)
  have hmemV' : ∀ {g : ↥(modularFunctionFieldBar (N * ℓ * q))}, g ∈ Rᵣ.nodeIntegers yP →
      ∀ V'' : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * ℓ * q)), Pᵣ.reduceFst V'' = yP →
        g ∈ V''.toValuationSubring :=
    fun hg V'' hV'' => Rᵣ.mem_toValuationSubring_of_mem_nodeIntegers hg hV''
  have haV : ∀ (c : AlgebraicClosure ℚ) (V'' : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * ℓ * q))),
      algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * ℓ * q)) c ∈ V''.toValuationSubring :=
    fun c V'' => V''.algebraMap_mem' _

  have hc1 : algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * ℓ * q)) cQ ∈ Rᵣ.R₁.integers :=
    (Rᵣ.R₁.algebraMap_mem_iff cQ).mpr hcA
  have hc2 : algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * ℓ * q)) cQ ∈ Rᵣ.R₂.integers :=
    (Rᵣ.R₂.algebraMap_mem_iff cQ).mpr hcA
  have hci1 : algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * ℓ * q)) cQ⁻¹ ∈ Rᵣ.R₁.integers :=
    (Rᵣ.R₁.algebraMap_mem_iff cQ⁻¹).mpr hciA
  have hci2 : algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * ℓ * q)) cQ⁻¹ ∈ Rᵣ.R₂.integers :=
    (Rᵣ.R₂.algebraMap_mem_iff cQ⁻¹).mpr hciA

  have hinclA : incl aF = algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * ℓ * q)) aQ := by
    rw [haF]; exact incl.commutes aQ
  have hyve : yv = aF * uF * x⁻¹ := by
    field_simp
    linear_combination hxyF
  have hy'e : y' = aF' * uF' * x'⁻¹ := by
    field_simp
    linear_combination hxyF'
  have hIyv : incl yv = algebraMap (AlgebraicClosure ℚ) _ aQ * incl uF * (incl x)⁻¹ := by
    rw [hyve, map_mul, map_mul, map_inv₀, hinclA]
  have hy'pow_inv : (y' ^ e)⁻¹ = x' ^ e * (uF' ^ e)⁻¹ * (aF' ^ e)⁻¹ := by
    rw [hy'e, mul_pow, mul_pow, inv_pow, mul_inv, mul_inv, inv_inv]
    ring
  have hy'pow : y' ^ e = aF' ^ e * uF' ^ e * (x' ^ e)⁻¹ := by
    rw [hy'e, mul_pow, mul_pow, inv_pow]
  have hcF : algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * ℓ * q)) cQ
      = algebraMap (AlgebraicClosure ℚ) _ aQ * (aF' ^ e)⁻¹ := by
    rw [hcQ, map_mul, map_inv₀, map_pow, haF']
  have hcFi : algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * ℓ * q)) cQ⁻¹
      = (algebraMap (AlgebraicClosure ℚ) _ aQ)⁻¹ * aF' ^ e := by
    rw [map_inv₀, hcF, mul_inv, inv_inv]
  set X : ↥(modularFunctionFieldBar (N * ℓ * q)) := incl yv * (y' ^ e)⁻¹ with hX
  set X' : ↥(modularFunctionFieldBar (N * ℓ * q)) := y' ^ e * (incl yv)⁻¹ with hX'

  have eX2 : X = algebraMap (AlgebraicClosure ℚ) _ cQ * (incl uF * (incl x)⁻¹) * (x' ^ e * (uF' ^ e)⁻¹) := by
    rw [hX, hIyv, hy'pow_inv, hcF]; ring
  have eX'2 : X' = algebraMap (AlgebraicClosure ℚ) _ cQ⁻¹ * (incl uF⁻¹ * incl x) * (uF' ^ e * (x' ^ e)⁻¹) := by
    rw [hX', hIyv, hy'pow, hcFi, map_inv₀, mul_inv, mul_inv, inv_inv]; ring

  have eXh : X = incl yv * (x' * uF'⁻¹ * aF'⁻¹) ^ e := by
    rw [hX, hy'pow_inv, mul_pow, mul_pow, inv_pow, inv_pow]
  have eX'h : X' = y' ^ e * (incl x * incl uF⁻¹ * (algebraMap (AlgebraicClosure ℚ) _ aQ)⁻¹) := by
    rw [hX', hIyv, map_inv₀, mul_inv, mul_inv, inv_inv]; ring

  have M1 : X ∈ Rᵣ.nodeIntegers yP := by
    refine ⟨?_, ?_, fun V'' hV'' => ?_⟩
    · rw [hX]
      exact mul_mem hIy1 (inv_mem_of_isUnit _ (hUy'.pow e))
    · rw [eX2]
      refine mul_mem (mul_mem hc2 (mul_mem hIu2 (inv_mem_of_isUnit _ hUIx))) (mul_mem (pow_mem (Rᵣ.mem_integersSnd_of_mem_nodeIntegers hxn') e) ?_)
      rw [← inv_pow]
      exact pow_mem (Rᵣ.mem_integersSnd_of_mem_nodeIntegers huin') e
    · rw [eXh]
      refine mul_mem (hmemV hyn V'' hV'') (pow_mem (mul_mem (mul_mem (hmemV' hxn' V'' hV'') (hmemV' huin' V'' hV'')) ?_) e)
      rw [haF', ← map_inv₀]; exact haV _ V''

  have M2 : X' ∈ Rᵣ.nodeIntegers yP := by
    refine ⟨?_, ?_, fun V'' hV'' => ?_⟩
    · rw [hX']
      exact mul_mem (pow_mem (Rᵣ.mem_integersFst_of_mem_nodeIntegers hyn') e) (inv_mem_of_isUnit _ hUIy)
    · rw [eX'2]
      refine mul_mem (mul_mem hci2 (mul_mem hIui2 hIx2)) (mul_mem (pow_mem (Rᵣ.mem_integersSnd_of_mem_nodeIntegers hun') e) ?_)
      rw [← inv_pow]
      exact pow_mem (inv_mem_of_isUnit _ hUx') e
    · rw [eX'h]
      refine mul_mem (pow_mem (hmemV' hyn' V'' hV'') e) (mul_mem (mul_mem (hmemV hxn V'' hV'') (hmemV huin V'' hV'')) ?_)
      rw [← map_inv₀]; exact haV _ V''

  have hye : y' ^ e ≠ 0 := pow_ne_zero _ hy0'
  have hval := valuation_evalAt_eq_of_ratio_mem Rᵣ (hvalAᵣ y) hIy0 hye M1 (by rw [← hX']; exact M2) V' hVy
    (pow_mem (Rᵣ.mem_toValuationSubring_of_mem_nodeIntegers hyn' hVy) e)

  have hev : V'.evalAt (incl yv) = V.evalAt yv :=
    evalAt_restrictAlong incl hι V' (isRational _) (R.mem_toValuationSubring_of_mem_nodeIntegers hyn hVw)
  show A.valuation (V.evalAt yv) = A.valuation (V'.evalAt y') ^ e
  rw [← hev, hval, evalAt_pow V' (isRational V') (Rᵣ.mem_toValuationSubring_of_mem_nodeIntegers hyn' hVy) e, map_pow]

end
end S_ModularCurve_PlaceSpecialization_yDepth_restrictAlong_towerInclBar_eq_yDepth_pow_ramificationIndexAlong_heckeAlphaC
end P2MW
export P2MW.S_ModularCurve_PlaceSpecialization_yDepth_restrictAlong_towerInclBar_eq_yDepth_pow_ramificationIndexAlong_heckeAlphaC (solution)
