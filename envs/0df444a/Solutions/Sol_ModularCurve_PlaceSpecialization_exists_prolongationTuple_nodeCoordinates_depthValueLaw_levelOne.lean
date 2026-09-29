-- Prove2me | solution 1 for ModularCurve.PlaceSpecialization.exists_prolongationTuple_nodeCoordinates_depthValueLaw_levelOne
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/c7211404-3af5-589a-aa61-aeef854fbf08

import Mathlib
import Definitions.Def_ModularCurve_NodeDepth
import Definitions.Def_ModularCurve_LevelOneGlueData
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_ModularCurve_JWidth
import Definitions.Def_ModularCurve_ModularUnit
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Theorems.Thm_ModularCurve_PlaceSpecialization_exists_prolongationTuple_isModel_regularityLaw_nodeValueLaw_level_one
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_inertiaFixed_nonempty_nodeCoordinates_levelOne
import Theorems.Thm_ModularCurve_NodeLocalized_exists_forall_redRestrict_eq_zero_iff_and_natCast_eq_pow_mul
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_crossingPresentation_nodeIntegersOver_levelOne
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_isLocalRing_and_isNoetherianRing_nodeIntegersOver_levelOne
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_valueIntegralityLaw_of_orderLawFixed
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_NodeCoordinates_exists_yDepth_eq_pow_of_forall_inertia_smul_eq
import Theorems.Thm_ModularCurve_isCurveOver_laurentBaseChange_modularFunctionFieldFull
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_crossingExponent_eq_placeWidth_mul_of_orderLawFixed_levelOne
import Theorems.Thm_ModularCurve_placeRamificationJ_charLGeomPlaceOfPoint_eq_one_and_placeWidth_eq_jWidth
import Theorems.Thm_ModularCurve_eq_charLGeomPlaceOfPoint_of_ord_pos
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_not_isUnit_sub_nodeConst_of_evalAt_mem_range_redRestrict_levelOne_of_five_le
import Theorems.Thm_ModularCurve_NodeLocalized_exists_finiteDimensional_forall_inertia_apply_eq_and_mem_range_redRestrict
import Theorems.Thm_ValuationSubring_ringHom_apply_eq_zero_iff_mem_maximalIdeal_of_charP
import Theorems.Thm_ModularCurve_pow_q_sq_eq_self_of_mem_ssJSet
import Theorems.Thm_AlgebraicCurve_Place_restrictAlong_surjective
import Theorems.Thm_ModularCurve_finiteAlong_heckeAlphaBar_of_prime
import Theorems.Thm_AlgebraicCurve_separableAlong_of_charZero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_PlaceSpecialization_exists_prolongationTuple_nodeCoordinates_depthValueLaw_levelOne
p2m_attr_erase "instance" "ValuationSubring.instIsAlgClosedResidueField AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt instFieldLaurentSeriesAlgClosureRat instAlgebraModularFunctionFieldBar ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instAlgebraResidueFieldSubtypeMemValuationSubringGaussBaseResOne ModularCurve.PlaceSpecialization.LevelOneProlongationPair.algGaussBase instAlgebraModularFunctionFieldFullC ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instAlgebraSubtypeMemValuationSubringGaussBaseResOne ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instAlgebraSubtypeMemValuationSubringGaussBaseResTwo instFieldModularFunctionFieldC ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isScalarTower_resOne instFieldLaurentSeries' ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isScalarTower_resTwo instModuleModularFunctionFieldBar ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isLocalHom_resBase₁ instAlgebraModularFunctionFieldC ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isLocalHom_constToGaussBase ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instFieldResOne instFieldModularFunctionFieldBar ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instAlgebraResidueFieldSubtypeMemValuationSubringGaussBaseResTwo ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instFieldResTwo instFieldModularFunctionFieldFullC ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isScalarTower_gaussBase instAlgebraLaurentSeriesAlgClosureRat ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isLocalHom_resBase₂ ModularCurve.PlaceSpecialization.LevelOneProlongationPair.algResidueConst instCommRingModularFunctionFieldBar ModularCurve.instIsElliptic_tateLaurent ModularCurve.instIsElliptic_tateBase WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.NodeLocalized.isLocalization_nodeDenominators"
p2m_attr_erase "instance" "ModularCurve.NodeLocalized.algebraEvalRange ModularCurve.NodeLocalized.isLocalRing_modularLocalizedAtPoint ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.NodeLocalized.isScalarTower_K_fieldOver_bar ModularCurve.NodeLocalized.algebraFieldOverBar ModularCurve.NodeLocalized.algebra_isIntegral_fieldOver_bar ModularCurve.NodeLocalized.isScalarTower_fieldOver_bar_laurent ModularCurve.NodeLocalized.charZero_fieldOver ModularCurve.NodeLocalized.algebraFieldOver ModularCurve.NodeLocalized.charZero_laurentSeries_algClosure instTopologicallyFGOfFiniteType AdicCompletion.instIsLocalRingMaximalIdeal ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.B3.instIsElliptic_goodModel WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral AlgebraicCurve.GaussReduction.isLocalHom_constToGauss ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar"
p2m_attr_erase "simp" "ModularCurve.PlaceSpecialization.LevelOneProlongationPair.mk.sizeOf_spec ModularCurve.PlaceSpecialization.LevelOneProlongationPair.residue₂_apply ModularCurve.PlaceSpecialization.LevelOneProlongationPair.residue₁_apply ModularCurve.PlaceSpecialization.LevelOneProlongationPair.mk.injEq ModularCurve.coe_nodeEquiv_symm_apply ModularCurve.frobNodePair_jOfNode ModularCurve.jOfNode_mk ModularCurve.widthOf_mk ModularCurve.frobNodePairEmb_apply ModularCurve.card_nodePairsOf ModularCurve.frobNodePair_snd ModularCurve.coe_nodeEquiv_apply ModularCurve.frobNodePair_fst AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring ValuationSubring.reduceAt_coe ValuationSubring.reduceAt_one ValuationSubring.reduceAt_natCast ValuationSubring.reduceAt_intCast ValuationSubring.reduceAt_zero WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero"
p2m_attr_erase "simp" "ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong ModularCurve.PlaceSpecialization.LevelOneProlongationPair.coe_gaussOrderToIntegers₂ ModularCurve.PlaceSpecialization.LevelOneProlongationPair.coe_gaussOrderToIntegers₁ ModularCurve.PlaceSpecialization.LevelOneProlongationPair.coe_toIntegers₁ ModularCurve.PlaceSpecialization.LevelOneProlongationPair.coe_constToGaussBase ModularCurve.PlaceSpecialization.LevelOneProlongationPair.coe_toIntegers₂ HahnSeries.ramScale_apply ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero"
p2m_attr_erase "simp" "TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one"
p2m_attr_erase "simp" "compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two ModularCurve.NodeLocalized.coe_modularEvalAt ModularCurve.ProjectiveLine.map_mk ModularCurve.LambdaModularPolynomialData.mk.sizeOf_spec ModularCurve.LambdaModularPolynomialData.mk.injEq AlgebraicCurve.Pic.baseChange_mk AlgebraicCurve.Place.forgetConstants_toValuationSubring AlgebraicCurve.Place.constantFieldEquiv_symm_apply AlgebraicCurve.Place.ord_forgetConstants AlgebraicCurve.Place.extendConstants_toValuationSubring AlgebraicCurve.Place.constantFieldEquiv_apply_toValuationSubring AlgebraicCurve.Place.mem_fiberConstants AlgebraicCurve.Place.restrictConstants_toValuationSubring AdicCompletion.evalₐ_mapₐ AdicCompletion.mapAlgEquivOfBijective_apply AdicCompletion.levelMapₐ_mk AdicCompletion.mapₐ_of AdicCompletion.mapAlgEquiv_symm_apply AdicCompletion.mapAlgEquiv_apply AdicCompletion.evalₐ_ofLevelwiseEquiv AdicCompletion.evalₐ_levelwiseHom"
p2m_attr_erase "simp" "AdicCompletion.localizationEquiv_of AdicCompletion.evalₐ_ofLevelwiseEquiv_symm Localization.AtPrime.quotientPowEquiv_mk AdicCompletion.transportOf_of AdicCompletion.selfCompletion_smul_of AdicCompletion.tensorRingEquiv_tmul AdicCompletion.completionOfAlgHom_apply AdicCompletion.completionBaseChangeHom_of AdicCompletion.tensorRingHom_tmul AdicCompletion.stabilizerToCompletionAut_of ModularCurve.Gamma0Pair.map_toCurve WeierstrassCurve.mapPoint_eq_ratPointMap ModularCurve.Gamma0Pair.map_gen ModularCurve.Gamma0Pair.map_eq_gamma0PairMap ModularCurve.ModuliPoint.map_eq_moduliPointMapRingHom ModularCurve.ModuliPoint.map_mk WeierstrassCurve.mapPointHom_apply WeierstrassCurve.mapPoint_zero WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec"
p2m_attr_erase "simp" "WeierstrassCurve.mem_zeroComponentSubgroup_iff WeierstrassCurve.veluX_empty WeierstrassCurve.vcInvEmbedding_apply ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.veluY_empty WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃"
p2m_attr_erase "simp" "PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.Point.netW20_zero WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero ModularCurve.cuspCount_one WeierstrassCurve.Universal.halveX_zero WeierstrassCurve.Universal.specialize_X_one WeierstrassCurve.Universal.coeff_halve WeierstrassCurve.Universal.specialize_X_two WeierstrassCurve.Universal.halveCoeff_zero WeierstrassCurve.Universal.specialize_X_four WeierstrassCurve.Universal.coeff_halveX WeierstrassCurve.Universal.specialize_X_three WeierstrassCurve.Universal.specialize_X_zero AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.ComponentChart.ofConstantReduction_integers AlgebraicCurve.ComponentChart.mk.sizeOf_spec AlgebraicCurve.ComponentChart.ofConstantReduction_placeMap AlgebraicCurve.ComponentChart.ofConstantReduction_nodes AlgebraicCurve.ComponentChart.mk.injEq AlgebraicCurve.ComponentChart.ofConstantReduction_dom AlgebraicCurve.Annulus.mk.sizeOf_spec AlgebraicCurve.Annulus.mk.injEq ModularCurve.FinitePlaceLift.traceHom_coe ModularCurve.FinitePlaceLift.mk.injEq ModularCurve.FinitePlaceLift.mk.sizeOf_spec AlgebraicCurve.GaussReduction.constToGauss_coe AlgebraicCurve.ComponentChart.ofConstantReductionNodes_dom"
p2m_attr_erase "simp" "AlgebraicCurve.ComponentChart.ofConstantReductionNodes_placeMap AlgebraicCurve.ComponentChart.ofConstantReductionNodes_nodes AlgebraicCurve.ComponentChart.ofConstantReductionNodes_residue AlgebraicCurve.ComponentChart.ofConstantReductionNodes_integers"
set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.PlaceSpecialization

namespace TData

theorem isRational (M : ℕ) [NeZero M] (V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M)) : V.IsRational := by
  haveI : IsCurveOver (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M) :=
    isCurveOver_laurentBaseChange_modularFunctionFieldFull (AlgebraicClosure ℚ) M
  haveI : Module.Finite (AlgebraicClosure ℚ) V.ResidueField := IsCurveOver.finite_residueField V
  haveI : Algebra.IsIntegral (AlgebraicClosure ℚ) V.ResidueField := Algebra.IsIntegral.of_finite _ _
  first
    | exact IsAlgClosed.algebraMap_surjective_of_isIntegral'
    | exact IsAlgClosed.algebraMap_surjective_of_isAlgebraic
    | exact IsAlgClosed.algebraMap_bijective_of_isIntegral.2

theorem coe_ne_zero_of_natCast_eq_pow_mul {A : ValuationSubring (AlgebraicClosure ℚ)} {K : IntermediateField ℚ (AlgebraicClosure ℚ)}
    {q : ℕ} [Fact q.Prime] (ϖ ε : ↥(NodeLocalized.coeffSubring A K)) (eK : ℕ) (heK : 1 ≤ eK)
    (h : ((q : ℕ) : ↥(NodeLocalized.coeffSubring A K)) = ϖ ^ eK * ε) : (ϖ : AlgebraicClosure ℚ) ≠ 0 := by
  intro h0
  have hq : ((q : ℕ) : AlgebraicClosure ℚ) ≠ 0 := by exact_mod_cast (Fact.out : q.Prime).ne_zero
  apply hq
  have h' := congrArg Subtype.val h
  have e1 : ((((q : ℕ) : ↥(NodeLocalized.coeffSubring A K)) : AlgebraicClosure ℚ)) = (q : AlgebraicClosure ℚ) := by norm_cast
  have e2 : ((ϖ ^ eK * ε : ↥(NodeLocalized.coeffSubring A K)) : AlgebraicClosure ℚ) =
      (ϖ : AlgebraicClosure ℚ) ^ eK * (ε : AlgebraicClosure ℚ) := by push_cast; rfl
  rw [e1, e2, h0, zero_pow (by omega), zero_mul] at h'
  exact h'

theorem eq_charLGeomPlaceOfPoint_evalAt {q : ℕ} {k : Type*} [Field k] [DecidableEq k]
    {w : Place k (modularFunctionFieldC k 1)} (hw : w ∈ ssPlaces q 1 k) :
    w = charLGeomPlaceOfPoint k (w.evalAt (jGeomGen k 1)) :=
  eq_charLGeomPlaceOfPoint_of_ord_pos (exists_isCentreOf_of_isRational hw.1 hw.2.1).1

theorem placeWidth_eq_jWidth_evalAt {q : ℕ} {k : Type*} [Field k] [DecidableEq k]
    {w : Place k (modularFunctionFieldC k 1)} (hw : w ∈ ssPlaces q 1 k) :
    placeWidth 1 w = jWidth (w.evalAt (jGeomGen k 1)) := by
  conv_lhs => rw [eq_charLGeomPlaceOfPoint_evalAt hw]
  exact (placeRamificationJ_charLGeomPlaceOfPoint_eq_one_and_placeWidth_eq_jWidth _).2

end TData

namespace TData

section Mono
variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] [PerfectField k] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    {P : PlaceSpecialization A q N data hKr k red hα hβ} (R : ProlongationTuple P)

theorem fieldOver_mono {K₁ K₂ : IntermediateField ℚ (AlgebraicClosure ℚ)} (h : K₁ ≤ K₂) :
    NodeLocalized.fieldOver N K₁ ≤ NodeLocalized.fieldOver N K₂ := by
  unfold NodeLocalized.fieldOver
  apply Subfield.closure_mono
  apply Set.union_subset_union_left
  rintro _ ⟨⟨a, ha⟩, rfl⟩
  exact ⟨⟨a, h ha⟩, rfl⟩

theorem nodeIntegersOver_mono {K₁ K₂ : IntermediateField ℚ (AlgebraicClosure ℚ)} (h : K₁ ≤ K₂)
    (w : Place k (modularFunctionFieldC k N)) : R.nodeIntegersOver K₁ w ≤ R.nodeIntegersOver K₂ w :=
  fun _ hf => ⟨hf.1, fieldOver_mono h hf.2⟩

def NodeCoordinates.ofLE {K₁ K₂ : IntermediateField ℚ (AlgebraicClosure ℚ)} (h : K₁ ≤ K₂)
    {w : Place k (modularFunctionFieldC k N)} (c : R.NodeCoordinates K₁ w) : R.NodeCoordinates K₂ w where
  x := ⟨c.x, nodeIntegersOver_mono R h w c.x.2⟩
  y := ⟨c.y, nodeIntegersOver_mono R h w c.y.2⟩
  x_fst := c.x_fst
  x_snd := c.x_snd
  y_snd := c.y_snd
  y_fst := c.y_fst

end Mono

theorem exists_common_field {ι : Type*} [Finite ι] (A : ValuationSubring (AlgebraicClosure ℚ))
    (Kw : ι → IntermediateField ℚ (AlgebraicClosure ℚ)) (hfd : ∀ i, FiniteDimensional ℚ ↥(Kw i))
    (hfix : ∀ i, ∀ σ ∈ A.inertiaSubgroupIn ℚ, ∀ z ∈ Kw i, σ z = z)
    (K₀ : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ ↥K₀]
    (hfix₀ : ∀ σ ∈ A.inertiaSubgroupIn ℚ, ∀ z ∈ K₀, σ z = z) :
    ∃ (K : IntermediateField ℚ (AlgebraicClosure ℚ)) (_ : FiniteDimensional ℚ ↥K),
      (∀ σ ∈ A.inertiaSubgroupIn ℚ, ∀ z ∈ K, σ z = z) ∧ (∀ i, Kw i ≤ K) ∧ K₀ ≤ K := by
  haveI := hfd
  haveI : FiniteDimensional ℚ ↥(⨆ i, Kw i) := IntermediateField.finiteDimensional_iSup_of_finite
  refine ⟨(⨆ i, Kw i) ⊔ K₀, IntermediateField.finiteDimensional_sup _ _, ?_, fun i => le_sup_of_le_left (le_iSup Kw i), le_sup_right⟩
  have hle : (⨆ i, Kw i) ⊔ K₀ ≤ IntermediateField.fixedField (A.inertiaSubgroupIn ℚ) :=
    sup_le (iSup_le fun i z hz => (IntermediateField.mem_fixedField_iff _ _).mpr fun τ hτ => hfix i τ hτ z hz)
      (fun z hz => (IntermediateField.mem_fixedField_iff _ _).mpr fun τ hτ => hfix₀ τ hτ z hz)
  intro σ hσ z hz
  exact (IntermediateField.mem_fixedField_iff _ _).mp (hle hz) σ hσ

end TData

namespace TData

theorem mem_range_redRestrict_mono {k : Type*} [Field k] {A : ValuationSubring (AlgebraicClosure ℚ)} (red : A →+* k)
    {K₁ K₂ : IntermediateField ℚ (AlgebraicClosure ℚ)} (h : K₁ ≤ K₂) {a : k}
    (ha : a ∈ Set.range (NodeLocalized.redRestrict red K₁)) : a ∈ Set.range (NodeLocalized.redRestrict red K₂) := by
  obtain ⟨x, rfl⟩ := ha
  exact ⟨⟨x.1, x.2.1, h x.2.2⟩, rfl⟩

end TData

namespace TData

theorem exists_reduceFst_eq {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    (P : PlaceSpecialization A q N data hKr k red hα hβ) (w : Place k (modularFunctionFieldC k N)) :
    ∃ V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)), P.reduceFst V = w := by
  obtain ⟨U, hU⟩ := P.d4 w
  obtain ⟨V, hV⟩ := Place.restrictAlong_surjective (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα
    (finiteAlong_heckeAlphaBar_of_prime (AlgebraicClosure ℚ) N q)
    (separableAlong_of_charZero (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα) U
  exact ⟨V, by rw [PlaceSpecialization.reduceFst]; exact (congrArg P.sp hV).trans hU⟩
end TData

set_option maxHeartbeats 4000000 in
theorem solution
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
    (hq : 5 ≤ q)
    (P : PlaceSpecialization A q 1 data hKr k red hα hβ)
    (W : Finset (Place k (modularFunctionFieldC k 1)))
    (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q 1 k)
    (e : Place k (modularFunctionFieldC k 1) → ℕ)
    (he : ∀ w ∈ W, e w = jWidth (w.evalAt (jGeomGen k 1))) :
    ∃ (R : ProlongationTuple P), R.IsModel ∧ R.RegularityLaw W ∧ R.NodeValueLaw W ∧ R.OrderLawFixed ∧
      ∃ (K : IntermediateField ℚ (AlgebraicClosure ℚ)) (_ : FiniteDimensional ℚ K)
        (ϖ : ↥(NodeLocalized.coeffSubring A K))
        (_ : ∀ d : ↥(NodeLocalized.coeffSubring A K), NodeLocalized.redRestrict red K d = 0 ↔ ∃ d', d = ϖ * d')
        (eK : ℕ) (_ : 1 ≤ eK) (ε : ↥(NodeLocalized.coeffSubring A K)) (_ : IsUnit ε)
        (_ : ((q : ℕ) : ↥(NodeLocalized.coeffSubring A K)) = ϖ ^ eK * ε)
        (cs : ∀ w ∈ W, R.NodeCoordinates K w)
        (depth : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) → ℕ),
        (∀ w (hw : w ∈ W), ∃ u : ↥(R.nodeIntegersOver K w), IsUnit u ∧
            (cs w hw).x * (cs w hw).y = R.nodeConst K w ϖ ^ (e w * eK) * u) ∧
        (∀ w (hw : w ∈ W),
            (Ideal.span {R.nodeConst K w ϖ, (cs w hw).x, (cs w hw).y}).IsMaximal ∧
            ∀ M : Ideal ↥(R.nodeIntegersOver K w), M.IsMaximal → M = Ideal.span {R.nodeConst K w ϖ, (cs w hw).x, (cs w hw).y}) ∧
        (∀ w (hw : w ∈ W),
            (Ideal.span {R.nodeConst K w ϖ, (cs w hw).x}).IsPrime ∧ (Ideal.span {R.nodeConst K w ϖ, (cs w hw).y}).IsPrime ∧
            (cs w hw).y ∉ Ideal.span {R.nodeConst K w ϖ, (cs w hw).x} ∧ (cs w hw).x ∉ Ideal.span {R.nodeConst K w ϖ, (cs w hw).y}) ∧
        (∀ w ∈ W, IsNoetherianRing ↥(R.nodeIntegersOver K w)) ∧
        (∀ w ∈ W, ∀ g : ↥(R.nodeIntegersOver K w),
            ∃ o : ↥(NodeLocalized.coeffSubring A K), ¬ IsUnit (g - R.nodeConst K w o)) ∧
        (∀ w ∈ W, R.ValueIntegralityLaw w) ∧
        (∀ w (hw : w ∈ W), (cs w hw).DepthValueLaw depth) := by
  classical

  have hq1 : ¬ q ∣ 1 := fun h => by have := Nat.le_of_dvd one_pos h; omega
  have hW' : ∀ w ∈ W, w ∈ ssPlaces q 1 k := fun w hw => (hW w).1 hw
  have hker : ∀ c : A, red c = 0 ↔ c ∈ IsLocalRing.maximalIdeal A :=
    fun c => ValuationSubring.ringHom_apply_eq_zero_iff_mem_maximalIdeal_of_charP A q red c

  obtain ⟨R, hR, hreg, hval, hO⟩ := exists_prolongationTuple_isModel_regularityLaw_nodeValueLaw_level_one P W hW

  have hKw : ∀ w ∈ W, ∃ (Kw : IntermediateField ℚ (AlgebraicClosure ℚ)) (_ : FiniteDimensional ℚ Kw),
      (∀ σ ∈ A.inertiaSubgroupIn ℚ, ∀ z ∈ Kw, σ z = z) ∧ Nonempty (R.NodeCoordinates Kw w) :=
    fun w hw => ProlongationTuple.exists_inertiaFixed_nonempty_nodeCoordinates_levelOne R hq1 hR W hW' hreg hval w hw

  choose Kw hKwfd hKwfix hKwne using hKw

  let jval : ↥W → k := fun w => (w : Place k (modularFunctionFieldC k 1)).evalAt (jGeomGen k 1)
  obtain ⟨K₀, instK₀, hK₀fix, hK₀res⟩ :=
    NodeLocalized.exists_finiteDimensional_forall_inertia_apply_eq_and_mem_range_redRestrict q A k red
      (W.attach.image jval)
      (by
        intro a ha
        obtain ⟨w, -, rfl⟩ := Finset.mem_image.mp ha
        exact pow_q_sq_eq_self_of_mem_ssJSet q (hW' w.1 w.2).2.2)
  haveI := instK₀
  obtain ⟨K, instK, hKfix, hKle, hK₀le⟩ := TData.exists_common_field A (fun w : ↥W => Kw w w.2) (fun w => hKwfd w w.2)
    (fun w => hKwfix w w.2) K₀ hK₀fix
  haveI := instK
  have cs₀ : ∀ w ∈ W, Nonempty (R.NodeCoordinates K w) := fun w hw =>
    ⟨TData.NodeCoordinates.ofLE R (hKle ⟨w, hw⟩) (hKwne w hw).some⟩
  have hKres : ∀ w ∈ W, w.evalAt (jGeomGen k 1) ∈ Set.range (NodeLocalized.redRestrict red K) := fun w hw =>
    TData.mem_range_redRestrict_mono red hK₀le (hK₀res _ (Finset.mem_image_of_mem jval (Finset.mem_attach W ⟨w, hw⟩)))

  obtain ⟨ϖ, hϖ, eK, ε, heK, hε, hqϖ⟩ := NodeLocalized.exists_forall_redRestrict_eq_zero_iff_and_natCast_eq_pow_mul red hker K
  have hϖ0 : (ϖ : AlgebraicClosure ℚ) ≠ 0 := TData.coe_ne_zero_of_natCast_eq_pow_mul ϖ ε eK heK hqϖ

  have hpres : ∀ w (hw : w ∈ W), ∃ (c : R.NodeCoordinates K w) (E : ℕ) (u : ↥(R.nodeIntegersOver K w)),
      1 ≤ E ∧ IsUnit u ∧ c.x * c.y = R.nodeConst K w ϖ ^ E * u ∧
      (Ideal.span {R.nodeConst K w ϖ, c.x, c.y}).IsMaximal ∧
      (∀ M : Ideal ↥(R.nodeIntegersOver K w), M.IsMaximal → M = Ideal.span {R.nodeConst K w ϖ, c.x, c.y}) ∧
      (Ideal.span {R.nodeConst K w ϖ, c.x}).IsPrime ∧ (Ideal.span {R.nodeConst K w ϖ, c.y}).IsPrime ∧
      c.y ∉ Ideal.span {R.nodeConst K w ϖ, c.x} ∧ c.x ∉ Ideal.span {R.nodeConst K w ϖ, c.y} := by
    intro w hw
    obtain ⟨x, hx⟩ := hKres w hw
    obtain ⟨c, -, -, eK', ε', -, -, -, E, u, hE, hu, hxy, hmax, huniq, hp1, hp2, hn1, hn2⟩ :=
      ProlongationTuple.exists_crossingPresentation_nodeIntegersOver_levelOne R hq hR W hW' hreg hval K w hw _ rfl x hx
        (cs₀ w hw).some ϖ hϖ
    exact ⟨c, E, u, hE, hu, hxy, hmax, huniq, hp1, hp2, hn1, hn2⟩
  choose c E u hE hu hxy hmax huniq hp1 hp2 hn1 hn2 using hpres

  have hEe : ∀ w (hw : w ∈ W), E w hw = e w * eK := fun w hw => by
    obtain ⟨xw, hxw⟩ := hKres w hw
    rw [ProlongationTuple.crossingExponent_eq_placeWidth_mul_of_orderLawFixed_levelOne R hq hR W hW' hreg hval hO hker K w hw
      xw hxw ϖ hϖ eK ε hε hqϖ (c w hw) (E w hw) (u w hw) (hu w hw) (hxy w hw), TData.placeWidth_eq_jWidth_evalAt (hW' w hw), he w hw]
  have hxy' : ∀ w (hw : w ∈ W), ∃ u : ↥(R.nodeIntegersOver K w), IsUnit u ∧
      (c w hw).x * (c w hw).y = R.nodeConst K w ϖ ^ (e w * eK) * u :=
    fun w hw => ⟨u w hw, hu w hw, by rw [← hEe w hw]; exact hxy w hw⟩

  have hnoeth : ∀ w ∈ W, IsNoetherianRing ↥(R.nodeIntegersOver K w) := fun w hw => by
    obtain ⟨x, hx⟩ := hKres w hw
    exact (ProlongationTuple.isLocalRing_and_isNoetherianRing_nodeIntegersOver_levelOne
      R hR W hW' hreg K w hw _ rfl x hx).2
  have hres : ∀ w ∈ W, ∀ g : ↥(R.nodeIntegersOver K w),
      ∃ o : ↥(NodeLocalized.coeffSubring A K), ¬ IsUnit (g - R.nodeConst K w o) := fun w hw g => by
    obtain ⟨V, hV⟩ := TData.exists_reduceFst_eq P w
    exact ProlongationTuple.exists_not_isUnit_sub_nodeConst_of_evalAt_mem_range_redRestrict_levelOne_of_five_le
      R hq hO W hW' hreg K w hw V hV (hKres w hw) g

  have hVI : ∀ w ∈ W, R.ValueIntegralityLaw w := fun w hw =>
    ProlongationTuple.valueIntegralityLaw_of_orderLawFixed R hq1 hO w (hW' w hw)

  have hVrat : ∀ V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)), V.IsRational :=
    TData.isRational (1 * q)
  have hTI : ∀ w (hw : w ∈ W) (V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))),
      P.reduceFst V = w →
      (∀ σ ∈ A.inertiaSubgroupIn ℚ, arithmeticGalois (modularFunctionFieldFull (1 * q)) σ • V = V) →
      ∃ d : ℕ, (c w hw).yDepth V = A.valuation (((q : ℕ) : AlgebraicClosure ℚ)) ^ d :=
    fun w hw V hV hfix =>
      ProlongationTuple.NodeCoordinates.exists_yDepth_eq_pow_of_forall_inertia_smul_eq
        (c w hw) (hVI w hw) hKfix ϖ hϖ0 (E w hw) (u w hw) (hu w hw) (hxy w hw) V hV (hVrat V) hfix
  let depth : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) → ℕ := fun V =>
    if h : P.reduceFst V ∈ W ∧
        (∀ σ ∈ A.inertiaSubgroupIn ℚ, arithmeticGalois (modularFunctionFieldFull (1 * q)) σ • V = V)
    then (hTI (P.reduceFst V) h.1 V rfl h.2).choose
    else 0
  have hdepth : ∀ w (hw : w ∈ W), (c w hw).DepthValueLaw depth := by
    intro w hw V hV hfix
    subst hV
    have hpos : P.reduceFst V ∈ W ∧
        (∀ σ ∈ A.inertiaSubgroupIn ℚ, arithmeticGalois (modularFunctionFieldFull (1 * q)) σ • V = V) := ⟨hw, hfix⟩
    show (c (P.reduceFst V) hw).yDepth V = A.valuation (((q : ℕ) : AlgebraicClosure ℚ)) ^ depth V
    simp only [depth, dif_pos hpos]
    exact (hTI (P.reduceFst V) hw V rfl hfix).choose_spec

  exact ⟨R, hR, hreg, hval, hO, K, instK, ϖ, hϖ, eK, heK, ε, hε, hqϖ, fun w hw => c w hw, depth,
    hxy', fun w hw => ⟨hmax w hw, huniq w hw⟩, fun w hw => ⟨hp1 w hw, hp2 w hw, hn1 w hw, hn2 w hw⟩,
    hnoeth, hres, hVI, hdepth⟩

end S_ModularCurve_PlaceSpecialization_exists_prolongationTuple_nodeCoordinates_depthValueLaw_levelOne
end P2MW
export P2MW.S_ModularCurve_PlaceSpecialization_exists_prolongationTuple_nodeCoordinates_depthValueLaw_levelOne (solution)
