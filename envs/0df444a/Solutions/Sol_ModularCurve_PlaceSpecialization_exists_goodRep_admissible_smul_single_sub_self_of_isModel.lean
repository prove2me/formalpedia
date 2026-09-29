-- Prove2me | solution 1 for ModularCurve.PlaceSpecialization.exists_goodRep_admissible_smul_single_sub_self_of_isModel
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/80b33b1f-2b56-521d-bebb-c9d921f13ec7

import Definitions.Def_ModularCurve_GlueData
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_ModularCurve_CoeffSemilinearAut
import Definitions.Def_ValuationSubring_ReduceAt
import Definitions.Def_WeierstrassCurve_ReductionMap
import Definitions.Def_ModularCurve_ProlongationTuple
import Definitions.Def_AlgebraicCurve_SemistableCharts
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_tubeEquation_smul_sub_self_of_annulus
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_splitDatum_of_forall_reduceFst_eq_ord_eq
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_nodeValueLaw_of_regularityLaw
import Theorems.Thm_ModularCurve_PlaceSpecialization_frobOnPlacesGeomLevel_frobOnPlacesGeomLevel_eq_self_of_mem_ssPlaces
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_mem_riemannRochSpace_ord_residue_eq_neg_of_splitDatum
import Theorems.Thm_ModularCurve_PlaceSpecialization_exists_families_isStrictFst_isStrictSnd_notMem_forall_inertia_smul_eq
import Theorems.Thm_ModularCurve_PlaceSpecialization_exists_isInftySide_reduceFst_eq_and_isZeroSide_reduceSnd_eq_of_not_isAffineGeomPlace
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_isCuspidal_of_not_isAffineGeomPlace_reduceFst
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_isInftySide_or_isZeroSide_of_isCuspidal
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_not_isAffineGeomPlace_reduceFst_of_isCuspidal
import Theorems.Thm_ModularCurve_isAffineGeomPlace_frobOnPlacesGeomLevel
import Theorems.Thm_ModularCurve_isAffineGeomPlace_or_ord_jGeomGen_lt_zero
import Theorems.Thm_ModularCurve_PlaceSpecialization_reduceFst_arithmeticGalois_smul
import Theorems.Thm_ModularCurve_PlaceSpecialization_reduceSnd_arithmeticGalois_smul
import Theorems.Thm_ModularCurve_arithFrobC_smul_eq_frobOnPlacesGeomLevel
import Theorems.Thm_ModularCurve_place_deg_eq_one_of_isAlgClosed
import Theorems.Thm_ModularCurve_hasPrincipalDivisors_modularFunctionFieldBar_unconditional
import Theorems.Thm_ModularCurve_hasPrincipalDivisors_modularFunctionFieldC_of_perfectField
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_annulus_mem_dom_iff_reduceFst_eq_of_mem_ssPlaces
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_envelope_localEquation_smul_single_sub_single
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_PlaceSpecialization_exists_goodRep_admissible_smul_single_sub_self_of_isModel
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.instIsElliptic_tateLaurent ModularCurve.instIsElliptic_tateBase WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.B3.instIsElliptic_goodModel WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK"
p2m_attr_erase "instance" "AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar ModularCurve.instIsScalarTowerJAdjoin WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.numberField_of_finiteDimensional GaloisRepAdic.instAddCommGroup GaloisRepAdic.instFree GaloisRepAdic.instFinite GaloisRepAdic.instModule ResidualGaloisRep.instModule ResidualGaloisRep.instModuleFinite ResidualGaloisRep.instAddCommGroup WeierstrassCurve.Affine.Point.instFinite ModularCurve.NodeLocalized.isLocalization_nodeDenominators ModularCurve.NodeLocalized.algebraEvalRange ModularCurve.NodeLocalized.isLocalRing_modularLocalizedAtPoint instTopologicallyFGOfFiniteType AdicCompletion.instIsLocalRingMaximalIdeal ModularCurve.NodeLocalized.isScalarTower_K_fieldOver_bar ModularCurve.NodeLocalized.algebraFieldOverBar ModularCurve.NodeLocalized.algebra_isIntegral_fieldOver_bar ModularCurve.NodeLocalized.isScalarTower_fieldOver_bar_laurent ModularCurve.NodeLocalized.charZero_fieldOver ModularCurve.NodeLocalized.algebraFieldOver ModularCurve.NodeLocalized.charZero_laurentSeries_algClosure AlgebraicCurve.CurveModel.isProper AlgebraicCurve.CurveModel.isIntegral AlgebraicCurve.CurveModel.smooth ModularCurve.IgusaScheme.isOpenImmersion_fInf ModularCurve.IgusaScheme.isOpenImmersion_ιInf ModularCurve.IgusaScheme.fact_jFull_ne_zero ModularCurve.IgusaScheme.isOpenImmersion_ιFin"
p2m_attr_erase "instance" "ModularCurve.IgusaScheme.isOpenImmersion_fFin AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin AlgebraicCurve.CurveModel.chartRing_finitePresentation AlgebraicCurve.GaussReduction.isLocalHom_constToGauss"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.PlaceSpecialization.LevelOneProlongationPair.mk.sizeOf_spec ModularCurve.PlaceSpecialization.LevelOneProlongationPair.residue₂_apply ModularCurve.PlaceSpecialization.LevelOneProlongationPair.residue₁_apply ModularCurve.PlaceSpecialization.LevelOneProlongationPair.mk.injEq ModularCurve.coe_nodeEquiv_symm_apply ModularCurve.frobNodePair_jOfNode ModularCurve.jOfNode_mk ModularCurve.widthOf_mk ModularCurve.frobNodePairEmb_apply ModularCurve.card_nodePairsOf ModularCurve.frobNodePair_snd ModularCurve.coe_nodeEquiv_apply ModularCurve.frobNodePair_fst AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen"
p2m_attr_erase "simp" "ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero"
p2m_attr_erase "simp" "TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄"
p2m_attr_erase "simp" "compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two ModularCurve.CharPModel.FibreModel.mk.injEq ModularCurve.CharPModel.FibreModel.mk.sizeOf_spec ModularCurve.Gamma0Pair.map_toCurve WeierstrassCurve.mapPoint_eq_ratPointMap ModularCurve.Gamma0Pair.map_gen ModularCurve.Gamma0Pair.map_eq_gamma0PairMap ModularCurve.ModuliPoint.map_eq_moduliPointMapRingHom ModularCurve.ModuliPoint.map_mk WeierstrassCurve.mapPointHom_apply WeierstrassCurve.mapPoint_zero WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply"
p2m_attr_erase "simp" "WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff ModularCurve.ProjectiveLine.map_mk WeierstrassCurve.veluX_empty WeierstrassCurve.vcInvEmbedding_apply ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.veluY_empty WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.netCol_one"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero ModularCurve.cuspCount_one WeierstrassCurve.Universal.halveX_zero WeierstrassCurve.Universal.specialize_X_one WeierstrassCurve.Universal.coeff_halve WeierstrassCurve.Universal.specialize_X_two WeierstrassCurve.Universal.halveCoeff_zero WeierstrassCurve.Universal.specialize_X_four WeierstrassCurve.Universal.coeff_halveX WeierstrassCurve.Universal.specialize_X_three WeierstrassCurve.Universal.specialize_X_zero HahnSeries.ramScale_apply ModularCurve.PlaceSpecialization.ProlongationTuple.NodeCoordinates.mk.sizeOf_spec ModularCurve.PlaceSpecialization.ProlongationTuple.coe_nodeConst ModularCurve.PlaceSpecialization.ProlongationTuple.NodeCoordinates.mk.injEq ModularCurve.PlaceSpecialization.ProlongationTuple.nodeResidue₂_apply ModularCurve.PlaceSpecialization.ProlongationTuple.nodeResidue₁_apply AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.differentialCoeff_zero"
p2m_attr_erase "simp" "AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ ModularCurve.symPoly_zero ModularCurve.crossingCoord_apply GaloisRepAdic.mk.injEq GaloisRepAdic.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.sizeOf_spec"
p2m_attr_erase "simp" "GaloisRepAdic.Equiv.mk.injEq ResidualGaloisRep.mk.sizeOf_spec ResidualGaloisRep.mk.injEq ResidualGaloisRep.Equiv.mk.sizeOf_spec ResidualGaloisRep.Equiv.mk.injEq AlgebraicCurve.Pic.baseChange_mk AlgebraicCurve.Place.forgetConstants_toValuationSubring AlgebraicCurve.Place.constantFieldEquiv_symm_apply AlgebraicCurve.Place.ord_forgetConstants AlgebraicCurve.Place.extendConstants_toValuationSubring AlgebraicCurve.Place.constantFieldEquiv_apply_toValuationSubring AlgebraicCurve.Place.mem_fiberConstants AlgebraicCurve.Place.restrictConstants_toValuationSubring ModularCurve.NodeLocalized.coe_modularEvalAt AdicCompletion.evalₐ_mapₐ AdicCompletion.mapAlgEquivOfBijective_apply AdicCompletion.levelMapₐ_mk AdicCompletion.mapₐ_of AdicCompletion.mapAlgEquiv_symm_apply AdicCompletion.mapAlgEquiv_apply AdicCompletion.evalₐ_ofLevelwiseEquiv AdicCompletion.evalₐ_levelwiseHom AdicCompletion.localizationEquiv_of AdicCompletion.evalₐ_ofLevelwiseEquiv_symm Localization.AtPrime.quotientPowEquiv_mk ModularCurve.LambdaModularPolynomialData.mk.sizeOf_spec ModularCurve.LambdaModularPolynomialData.mk.injEq AdicCompletion.transportOf_of AdicCompletion.selfCompletion_smul_of AdicCompletion.tensorRingEquiv_tmul AdicCompletion.completionOfAlgHom_apply AdicCompletion.completionBaseChangeHom_of AdicCompletion.tensorRingHom_tmul AdicCompletion.stabilizerToCompletionAut_of GoodReductionJacobian.RelativePic0Designation.mk.sizeOf_spec GoodReductionJacobian.AvatarSchemeBridge.mk.injEq MilneJVScheme.JacobianSchemeData.mk.injEq GoodReductionJacobian.AvatarSchemeBridge.mk.sizeOf_spec MilneJVScheme.JacobianSchemeData.mk.sizeOf_spec GoodReductionJacobian.RelativePic0Designation.mk.injEq"
p2m_attr_erase "simp" "NeronModelInfra.specGenericFibreInclusion_eq NeronModelInfra.genericFibreRestrict_coe_comp_snd NeronModelInfra.genericFibreRestrict_coe_comp_fst GoodReductionJacobian.schemeHomOverComp_coe NeronModelInfra.schemeHomOverEquivOverHom_apply GoodReductionJacobian.RelativeGroupLaw.mk.sizeOf_spec NeronModelInfra.schemeHomOverEquivOverHom_symm_apply NeronModelInfra.overHomToSchemeHomOver_coe GoodReductionJacobian.RelativeGroupLaw.mk.injEq NeronModelInfra.overHomToSchemeHomOver_schemeHomOverToOverHom NeronModelInfra.schemeHomOverToOverHom_left NeronModelInfra.schemeHomOverToOverHom_overHomToSchemeHomOver NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe AlgebraicCurve.CurveModel.mk.injEq AlgebraicCurve.CurveModel.mk.sizeOf_spec ModularCurve.IgusaScheme.ιInf_igusaTo_assoc ModularCurve.IgusaScheme.coe_jFull ModularCurve.IgusaScheme.coe_jInvChartInf ModularCurve.IgusaScheme.coe_jChartFin ModularCurve.IgusaScheme.ιFin_igusaTo ModularCurve.IgusaScheme.ιInf_igusaTo ModularCurve.IgusaScheme.ιFin_igusaTo_assoc AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces AlgebraicCurve.GaussReduction.constToGauss_coe"
p2m_attr_erase "simp" "AlgebraicCurve.ComponentChart.ofConstantReductionNodes_dom AlgebraicCurve.ComponentChart.ofConstantReductionNodes_placeMap AlgebraicCurve.ComponentChart.ofConstantReductionNodes_nodes AlgebraicCurve.ComponentChart.ofConstantReductionNodes_residue AlgebraicCurve.ComponentChart.ofConstantReductionNodes_integers"
set_option autoImplicit false
p2m_open "AlgebraicCurve IsLocalRing ModularCurve ModularCurve.PlaceSpecialization~IsInftySide~IsCuspidal~IsZeroSide~IsCuspidal'"

namespace InertialDisplacement
open ModularCurve.PlaceSpecialization.ProlongationTuple

private theorem exists_unif {K L : Type*} [Field K] [Field L] [Algebra K L] (W : Finset (Place K L)) :
    ∃ π : Place K L → L, ∀ w ∈ W, w.ord (π w) = 1 := by
  have h : ∀ w : Place K L, ∃ x : L, w.ord x = 1 := fun w => by
    obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible w.toValuationSubring
    exact ⟨(ϖ : L), w.ord_coe_irreducible hϖ⟩
  choose π hπ using h
  exact ⟨π, fun w _ => hπ w⟩

section Bookkeeping

variable {α β : Type*}

private theorem mapDomain_apply_eq_sum [DecidableEq β] (E : α →₀ ℤ) (r : α → β) (v : β) :
    Finsupp.mapDomain r E v = ∑ W ∈ E.support, if r W = v then E W else 0 := by
  classical
  rw [Finsupp.mapDomain, Finsupp.sum_apply, Finsupp.sum]
  refine Finset.sum_congr rfl fun W _ => ?_
  rw [Finsupp.single_apply]

private theorem mapDomain_nonneg (E : α →₀ ℤ) (r : α → β) (v : β)
    (h : ∀ W, r W = v → 0 ≤ E W) : 0 ≤ Finsupp.mapDomain r E v := by
  classical
  rw [mapDomain_apply_eq_sum]
  exact Finset.sum_nonneg fun W _ => by
    split_ifs with h'
    · exact h W h'
    · exact le_rfl

private theorem le_mapDomain (E : α →₀ ℤ) (r : α → β) (v : β)
    (h : ∀ W, r W = v → 0 ≤ E W) {V : α} (hV : r V = v) :
    E V ≤ Finsupp.mapDomain r E v := by
  classical
  rw [mapDomain_apply_eq_sum]
  by_cases hs : V ∈ E.support
  · rw [← Finset.add_sum_erase _ _ hs, if_pos hV]
    refine le_add_of_nonneg_right (Finset.sum_nonneg fun W _ => ?_)
    split_ifs with h'
    · exact h W h'
    · exact le_rfl
  · rw [Finsupp.notMem_support_iff.mp hs]
    exact Finset.sum_nonneg fun W _ => by
      split_ifs with h'
      · exact h W h'
      · exact le_rfl

private theorem le_mapDomain_filter (D : α →₀ ℤ) (p : α → Prop) [DecidablePred p] (r : α → β) (v : β)
    (h : ∀ W, p W → r W = v → 0 ≤ D W) {V : α} (hp : p V) (hV : r V = v) :
    D V ≤ Finsupp.mapDomain r (D.filter p) v := by
  have hDV : D V = (D.filter p) V := by rw [Finsupp.filter_apply, if_pos hp]
  rw [hDV]
  refine le_mapDomain _ r v (fun W hW => ?_) hV
  rw [Finsupp.filter_apply]
  split_ifs with hp'
  · exact h W hp' hW
  · exact le_rfl

private theorem mapDomain_eq_zero_of_forall_ne (E : α →₀ ℤ) (r : α → β) (v : β)
    (h : ∀ W, E W ≠ 0 → r W ≠ v) : Finsupp.mapDomain r E v = 0 := by
  classical
  rw [mapDomain_apply_eq_sum]
  exact Finset.sum_eq_zero fun W hW => if_neg (h W (Finsupp.mem_support_iff.mp hW))

private theorem mapDomain_filter_eq_zero_of_forall_ne (E : α →₀ ℤ) (p : α → Prop) [DecidablePred p]
    (r : α → β) (v : β) (h : ∀ W, E W ≠ 0 → r W ≠ v) : Finsupp.mapDomain r (E.filter p) v = 0 := by
  refine mapDomain_eq_zero_of_forall_ne _ r v fun W hW => h W ?_
  by_cases hp : p W
  · rwa [Finsupp.filter_apply, if_pos hp] at hW
  · exfalso
    apply hW
    rw [Finsupp.filter_apply, if_neg hp]

private theorem sum_single_apply_nonneg {m : ℕ} (Q : Fin m → α) (V : α) :
    0 ≤ (∑ i, Finsupp.single (Q i) (1 : ℤ)) V := by
  classical
  rw [Finsupp.finsetSum_apply]
  exact Finset.sum_nonneg fun i _ => by
    rw [Finsupp.single_apply]
    split_ifs <;> omega

private theorem sum_single_apply_eq_zero {m : ℕ} (Q : Fin m → α) {V : α} (h : ∀ i, Q i ≠ V) :
    (∑ i, Finsupp.single (Q i) (1 : ℤ)) V = 0 := by
  classical
  rw [Finsupp.finsetSum_apply]
  exact Finset.sum_eq_zero fun i _ => by rw [Finsupp.single_apply, if_neg (h i)]

private theorem exists_eq_of_sum_single_apply_ne_zero {m : ℕ} (Q : Fin m → α) {V : α}
    (h : (∑ i, Finsupp.single (Q i) (1 : ℤ)) V ≠ 0) : ∃ i, Q i = V := by
  by_contra hne
  exact h (sum_single_apply_eq_zero Q fun i hi => hne ⟨i, hi⟩)

private theorem sum_single_add_sum_single_apply_nonneg {m : ℕ} (Q₁ Q₂ : Fin m → α) {F : α →₀ ℤ}
    (hF : F = ∑ i, Finsupp.single (Q₁ i) (1 : ℤ) + ∑ j, Finsupp.single (Q₂ j) (1 : ℤ)) (V : α) : 0 ≤ F V := by
  subst hF
  rw [Finsupp.add_apply]
  exact add_nonneg (sum_single_apply_nonneg Q₁ V) (sum_single_apply_nonneg Q₂ V)

end Bookkeeping

section Degrees

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

private theorem degree_eq_sum_of_deg_eq_one (D : Divisor K F) (hdeg : ∀ v : Place K F, v.deg = 1) :
    Divisor.degree D = D.sum (fun _ n => n) := by
  rw [Divisor.degree, Finsupp.liftAddHom_apply]
  refine Finsupp.sum_congr fun v _ => ?_
  rw [AddMonoidHom.mulRight_apply, hdeg v, Nat.cast_one, mul_one]

private theorem degree_nonneg_of_nonneg (D : Divisor K F) (hdeg : ∀ v : Place K F, v.deg = 1)
    (hD : ∀ v, 0 ≤ D v) : 0 ≤ Divisor.degree D := by
  rw [degree_eq_sum_of_deg_eq_one D hdeg, Finsupp.sum]
  exact Finset.sum_nonneg fun v _ => hD v

private theorem degree_mapDomain_sum_single {α : Type*} (hdeg : ∀ v : Place K F, v.deg = 1) {m : ℕ}
    (r : α → Place K F) (Q : Fin m → α) :
    Divisor.degree (Finsupp.mapDomain r (∑ i, Finsupp.single (Q i) (1 : ℤ))) = m := by
  rw [Finsupp.mapDomain_finsetSum]
  simp only [Finsupp.mapDomain_single]
  rw [map_sum]
  simp [Divisor.degree_single, hdeg]

private theorem pic0Mk_eq_of_forall_sub_eq_ord (D₁ D₂ : Divisor K F)
    (h₁ : D₁ ∈ Divisor.degZero (K := K) (F := F)) (h₂ : D₂ ∈ Divisor.degZero (K := K) (F := F))
    (f : F) (hf : f ≠ 0) (h : ∀ v, (D₁ - D₂) v = v.ord f) :
    Pic0.mk ⟨D₁, h₁⟩ = Pic0.mk ⟨D₂, h₂⟩ := by
  apply QuotientAddGroup.eq.mpr
  rw [AddSubgroup.mem_addSubgroupOf, Divisor.mem_principal]
  refine ⟨f⁻¹, inv_ne_zero hf, fun v => ?_⟩
  rw [Place.ord_inv, ← h v]
  show (-D₁ + D₂) v = -(D₁ - D₂) v
  simp only [Finsupp.add_apply, Finsupp.neg_apply, Finsupp.sub_apply]
  ring

end Degrees

section Geometry

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {N : ℕ} [NeZero N] {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}

set_option hygiene false in
local notation "φ" => frobOnPlacesGeomLevel k N data hKr

private theorem trichotomy (P : PlaceSpecialization A q N data hKr k red hα hβ)
    (W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) :
    P.IsStrictFst W ∨ P.IsStrictSnd W ∨
      (φ (φ (P.reduceFst W)) = P.reduceFst W ∧ P.reduceSnd W = φ (P.reduceFst W)) := by
  rcases P.d1 W with h | h
  · change P.reduceFst W = φ (P.reduceSnd W) at h
    by_cases hfix : φ (φ (P.reduceSnd W)) = P.reduceSnd W
    · refine Or.inr (Or.inr ⟨?_, ?_⟩)
      · rw [h, hfix]
      · rw [h, hfix]
    · exact Or.inr (Or.inl ⟨h, hfix⟩)
  · change φ (P.reduceFst W) = P.reduceSnd W at h
    by_cases hfix : φ (φ (P.reduceFst W)) = P.reduceFst W
    · exact Or.inr (Or.inr ⟨hfix, h.symm⟩)
    · exact Or.inl ⟨h, hfix⟩

private theorem fixed_of_not_strict {P : PlaceSpecialization A q N data hKr k red hα hβ}
    {W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))}
    (h₁ : ¬ P.IsStrictFst W) (h₂ : ¬ P.IsStrictSnd W) :
    φ (φ (P.reduceFst W)) = P.reduceFst W ∧ P.reduceSnd W = φ (P.reduceFst W) := by
  rcases trichotomy P W with h | h | h
  · exact absurd h h₁
  · exact absurd h h₂
  · exact h

private theorem not_isStrictSnd_of_isStrictFst {P : PlaceSpecialization A q N data hKr k red hα hβ}
    {W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))} (h₁ : P.IsStrictFst W) :
    ¬ P.IsStrictSnd W := by
  intro h₂
  apply h₂.2
  have e₁ : φ (P.reduceFst W) = P.reduceSnd W := h₁.1
  have e₂ : P.reduceFst W = φ (P.reduceSnd W) := h₂.1
  rw [e₂] at e₁
  exact e₁

private theorem reduceFst_ne_of_strict {P : PlaceSpecialization A q N data hKr k red hα hβ}
    {W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))}
    (hs : P.IsStrictFst W ∨ P.IsStrictSnd W) {v : Place k ↥(modularFunctionFieldC k N)} (hv : φ (φ v) = v) :
    P.reduceFst W ≠ v := by
  rintro rfl
  rcases hs with h | h
  · exact h.2 hv
  · apply h.2
    have e : P.reduceFst W = φ (P.reduceSnd W) := h.1
    rw [e] at hv
    exact frobOnPlacesGeomLevel_injective k N data hKr hv

private theorem reduceSnd_ne_of_strict {P : PlaceSpecialization A q N data hKr k red hα hβ}
    {W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))}
    (hs : P.IsStrictFst W ∨ P.IsStrictSnd W) {v : Place k ↥(modularFunctionFieldC k N)} (hv : φ (φ v) = v) :
    P.reduceSnd W ≠ v := by
  rintro rfl
  rcases hs with h | h
  · apply h.2
    have e : P.reduceSnd W = φ (P.reduceFst W) := h.1.symm
    rw [e] at hv
    exact frobOnPlacesGeomLevel_injective k N data hKr hv
  · exact h.2 hv

private theorem frob_fixed_of_fixed {v : Place k ↥(modularFunctionFieldC k N)} (hv : φ (φ v) = v) :
    φ (φ (φ v)) = φ v := by
  rw [hv]

private theorem not_strict_smul (P : PlaceSpecialization A q N data hKr k red hα hβ)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hσ : σ ∈ A.inertiaSubgroupIn ℚ)
    {V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))}
    (hV₁ : ¬ P.IsStrictFst V) (hV₂ : ¬ P.IsStrictSnd V) :
    ¬ P.IsStrictFst (arithmeticGalois (L := AlgebraicClosure ℚ) (modularFunctionFieldFull (N * q)) σ • V) ∧
      ¬ P.IsStrictSnd (arithmeticGalois (L := AlgebraicClosure ℚ) (modularFunctionFieldFull (N * q)) σ • V) := by
  constructor
  · intro h
    apply hV₁
    obtain ⟨h₁, h₂⟩ := h
    rw [reduceFst_arithmeticGalois_smul P σ hσ V, reduceSnd_arithmeticGalois_smul P σ hσ V] at h₁
    rw [reduceFst_arithmeticGalois_smul P σ hσ V] at h₂
    exact ⟨h₁, h₂⟩
  · intro h
    apply hV₂
    obtain ⟨h₁, h₂⟩ := h
    rw [reduceFst_arithmeticGalois_smul P σ hσ V, reduceSnd_arithmeticGalois_smul P σ hσ V] at h₁
    rw [reduceSnd_arithmeticGalois_smul P σ hσ V] at h₂
    exact ⟨h₁, h₂⟩

private theorem ne_of_not_isStrictFst {P : PlaceSpecialization A q N data hKr k red hα hβ}
    {X W' : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))} (hX : ¬ P.IsStrictFst X)
    (hW' : P.IsStrictFst W') : X ≠ W' := by
  rintro rfl
  exact hX hW'

private theorem ne_of_not_isStrictSnd {P : PlaceSpecialization A q N data hKr k red hα hβ}
    {X W' : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))} (hX : ¬ P.IsStrictSnd X)
    (hW' : P.IsStrictSnd W') : X ≠ W' := by
  rintro rfl
  exact hX hW'

private theorem not_isAffineGeomPlace_reduceSnd_of_isCuspidal'
    (P : PlaceSpecialization A q N data hKr k red hα hβ)
    (V : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) (hV : IsCuspidal' P V) :
    ¬ IsAffineGeomPlace k N (P.reduceSnd V) := by
  haveI : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
  set jN : modularFunctionFieldBar N :=
    ⟨coeffEmb (AlgebraicClosure ℚ) jq,
      coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full N (jq_mem N))⟩ with hjN
  have hβj : heckeBetaBar (AlgebraicClosure ℚ) N q jN = ProlongationTuple.jQFun N q := by
    apply Subtype.ext
    rw [coe_heckeBetaBar]
    show qExpand (AlgebraicClosure ℚ) q (coeffEmb (AlgebraicClosure ℚ) jq)
      = coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ q jq)
    rw [coeffEmb, coeffMap_qExpand]
  have he : 0 < Place.ramificationIndexAlong (heckeBetaBar (AlgebraicClosure ℚ) N q) V := by
    letI := algebraAlong (heckeBetaBar (AlgebraicClosure ℚ) N q)
    haveI := isScalarTower_along (heckeBetaBar (AlgebraicClosure ℚ) N q)
    haveI := isIntegral_along (heckeBetaBar (AlgebraicClosure ℚ) N q) hβ
    exact V.ramificationIndex_pos (F := modularFunctionFieldBar N)
  have hcusp : ∀ a : A, (V.restrictAlong (heckeBetaBar (AlgebraicClosure ℚ) N q) hβ).ord
      (jN - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (a : AlgebraicClosure ℚ)) ≤ 0 := by
    intro a
    have hle := hV a
    have key := Place.ord_restrictAlong (heckeBetaBar (AlgebraicClosure ℚ) N q) hβ V
      (jN - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (a : AlgebraicClosure ℚ))
    rw [map_sub, hβj, AlgHom.commutes] at key
    rw [key] at hle
    by_contra hpos
    exact absurd hle (not_le.mpr (mul_pos (by exact_mod_cast he) (not_le.mp hpos)))
  have hpole := P.d0_j_pole (V.restrictAlong (heckeBetaBar (AlgebraicClosure ℚ) N q) hβ) hcusp
  intro haff
  have h0 := (P.reduceSnd V).ord_nonneg_of_mem haff.1
  exact absurd hpole (not_lt.mpr h0)

private theorem not_cuspidal_of_isStrictFst {P : PlaceSpecialization A q N data hKr k red hα hβ}
    {Q : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))} (hQ : P.IsStrictFst Q)
    (haff : IsAffineGeomPlace k N (P.reduceFst Q)) : ¬ IsCuspidal P Q ∧ ¬ IsCuspidal' P Q := by
  refine ⟨fun hc => ProlongationTuple.not_isAffineGeomPlace_reduceFst_of_isCuspidal P Q hc haff, fun hc => ?_⟩
  refine not_isAffineGeomPlace_reduceSnd_of_isCuspidal' P Q hc ?_
  have e : φ (P.reduceFst Q) = P.reduceSnd Q := hQ.1
  rw [← e]
  exact isAffineGeomPlace_frobOnPlacesGeomLevel k N data hKr _ haff

private theorem not_cuspidal_of_isStrictSnd {P : PlaceSpecialization A q N data hKr k red hα hβ}
    {Q : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))} (hQ : P.IsStrictSnd Q)
    (haff : IsAffineGeomPlace k N (P.reduceSnd Q)) : ¬ IsCuspidal P Q ∧ ¬ IsCuspidal' P Q := by
  refine ⟨fun hc => ?_, fun hc => not_isAffineGeomPlace_reduceSnd_of_isCuspidal' P Q hc haff⟩
  refine ProlongationTuple.not_isAffineGeomPlace_reduceFst_of_isCuspidal P Q hc ?_
  have e : P.reduceFst Q = φ (P.reduceSnd Q) := hQ.1
  rw [e]
  exact isAffineGeomPlace_frobOnPlacesGeomLevel k N data hKr _ haff

set_option synthInstance.maxHeartbeats 1600000 in

private theorem exists_finset_of_not_isAffineGeomPlace [PerfectField k] :
    ∃ B : Finset (Place k ↥(modularFunctionFieldC k N)), ∀ v, ¬ IsAffineGeomPlace k N v → v ∈ B := by
  haveI : HasPrincipalDivisors k ↥(modularFunctionFieldC k N) :=
    hasPrincipalDivisors_modularFunctionFieldC_of_perfectField k N
  by_cases hj : jGeomGen k N = 0
  · refine ⟨∅, fun v hv => ?_⟩
    rcases isAffineGeomPlace_or_ord_jGeomGen_lt_zero k N v with h | h
    · exact absurd h hv
    · rw [hj, Place.ord_zero] at h
      exact absurd h (lt_irrefl 0)
  · obtain ⟨DJ, hDJ, -⟩ := HasPrincipalDivisors.exists_divisor (K := k) _ hj
    refine ⟨DJ.support, fun v hv => ?_⟩
    rcases isAffineGeomPlace_or_ord_jGeomGen_lt_zero k N v with h | h
    · exact absurd h hv
    · rw [Finsupp.mem_support_iff, hDJ v]
      exact h.ne

end Geometry

section StrictParts

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {N : ℕ} [NeZero N] {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    (P : PlaceSpecialization A q N data hKr k red hα hβ)

set_option hygiene false in
local notation "φ" => frobOnPlacesGeomLevel k N data hKr

private theorem fstDiv_add (X Y : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) :
    P.fstDiv (X + Y) = P.fstDiv X + P.fstDiv Y := by
  ext W
  by_cases hs : P.IsStrictFst W <;> simp [PlaceSpecialization.fstDiv, hs]

private theorem sndDiv_add (X Y : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) :
    P.sndDiv (X + Y) = P.sndDiv X + P.sndDiv Y := by
  ext W
  by_cases hs : P.IsStrictSnd W <;> simp [PlaceSpecialization.sndDiv, hs]

private theorem fstDiv_eq_zero_of_forall {X : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))}
    (h : ∀ W, P.IsStrictFst W → X W = 0) : P.fstDiv X = 0 := by
  ext W
  by_cases hs : P.IsStrictFst W
  · simp [PlaceSpecialization.fstDiv, hs, h W hs]
  · simp [PlaceSpecialization.fstDiv, hs]

private theorem sndDiv_eq_zero_of_forall {X : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))}
    (h : ∀ W, P.IsStrictSnd W → X W = 0) : P.sndDiv X = 0 := by
  ext W
  by_cases hs : P.IsStrictSnd W
  · simp [PlaceSpecialization.sndDiv, hs, h W hs]
  · simp [PlaceSpecialization.sndDiv, hs]

private theorem fstDiv_eq_self_of_forall {X : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))}
    (h : ∀ W, X W ≠ 0 → P.IsStrictFst W) : P.fstDiv X = X := by
  ext W
  by_cases hs : P.IsStrictFst W
  · simp [PlaceSpecialization.fstDiv, hs]
  · have h0 : X W = 0 := by
      by_contra hne
      exact hs (h W hne)
    simp [PlaceSpecialization.fstDiv, hs, h0]

private theorem sndDiv_eq_self_of_forall {X : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))}
    (h : ∀ W, X W ≠ 0 → P.IsStrictSnd W) : P.sndDiv X = X := by
  ext W
  by_cases hs : P.IsStrictSnd W
  · simp [PlaceSpecialization.sndDiv, hs]
  · have h0 : X W = 0 := by
      by_contra hne
      exact hs (h W hne)
    simp [PlaceSpecialization.sndDiv, hs, h0]

private theorem fstDiv_apply_nonneg {X : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))}
    (hX : ∀ W, 0 ≤ X W) (W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) :
    0 ≤ P.fstDiv X W := by
  by_cases hs : P.IsStrictFst W
  · simp [PlaceSpecialization.fstDiv, hs, hX W]
  · simp [PlaceSpecialization.fstDiv, hs]

private theorem sndDiv_apply_nonneg {X : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))}
    (hX : ∀ W, 0 ≤ X W) (W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) :
    0 ≤ P.sndDiv X W := by
  by_cases hs : P.IsStrictSnd W
  · simp [PlaceSpecialization.sndDiv, hs, hX W]
  · simp [PlaceSpecialization.sndDiv, hs]

private theorem mapDomain_fstDiv_eq_zero_of_fixed (X : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)))
    {v : Place k ↥(modularFunctionFieldC k N)} (hv : φ (φ v) = v) :
    Finsupp.mapDomain P.reduceFst (P.fstDiv X) v = 0 := by
  refine mapDomain_eq_zero_of_forall_ne _ _ _ fun W hW => ?_
  by_cases hs : P.IsStrictFst W
  · exact reduceFst_ne_of_strict (Or.inl hs) hv
  · exfalso
    apply hW
    simp [PlaceSpecialization.fstDiv, hs]

private theorem mapDomain_sndDiv_eq_zero_of_fixed (X : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)))
    {v : Place k ↥(modularFunctionFieldC k N)} (hv : φ (φ v) = v) :
    Finsupp.mapDomain P.reduceSnd (P.sndDiv X) v = 0 := by
  refine mapDomain_eq_zero_of_forall_ne _ _ _ fun W hW => ?_
  by_cases hs : P.IsStrictSnd W
  · exact reduceSnd_ne_of_strict (Or.inr hs) hv
  · exfalso
    apply hW
    simp [PlaceSpecialization.sndDiv, hs]

private theorem branchFst_apply_self (X : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)))
    {w : Place k ↥(modularFunctionFieldC k N)} (hw : φ (φ w) = w) (n : ℕ) :
    (Finsupp.mapDomain P.reduceFst (P.fstDiv X) + Finsupp.single w (n : ℤ)) w = n := by
  rw [Finsupp.add_apply, mapDomain_fstDiv_eq_zero_of_fixed P X hw, Finsupp.single_eq_same, zero_add]

private theorem branchFst_apply_of_ne (X : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)))
    (w : Place k ↥(modularFunctionFieldC k N)) (n : ℕ) {v : Place k ↥(modularFunctionFieldC k N)} (hv : φ (φ v) = v)
    (hvw : v ≠ w) : (Finsupp.mapDomain P.reduceFst (P.fstDiv X) + Finsupp.single w (n : ℤ)) v = 0 := by
  classical
  rw [Finsupp.add_apply, mapDomain_fstDiv_eq_zero_of_fixed P X hv, Finsupp.single_apply, if_neg (Ne.symm hvw),
    add_zero]

private theorem branchSnd_apply_self (X : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)))
    {w' : Place k ↥(modularFunctionFieldC k N)} (hw' : φ (φ w') = w') (n : ℕ) :
    (Finsupp.mapDomain P.reduceSnd (P.sndDiv X) + Finsupp.single w' (n : ℤ)) w' = n := by
  rw [Finsupp.add_apply, mapDomain_sndDiv_eq_zero_of_fixed P X hw', Finsupp.single_eq_same, zero_add]

private theorem branchSnd_apply_of_ne (X : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)))
    (w' : Place k ↥(modularFunctionFieldC k N)) (n : ℕ) {v : Place k ↥(modularFunctionFieldC k N)} (hv : φ (φ v) = v)
    (hvw : v ≠ w') : (Finsupp.mapDomain P.reduceSnd (P.sndDiv X) + Finsupp.single w' (n : ℤ)) v = 0 := by
  classical
  rw [Finsupp.add_apply, mapDomain_sndDiv_eq_zero_of_fixed P X hv, Finsupp.single_apply, if_neg (Ne.symm hvw),
    add_zero]

end StrictParts

section Laws

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {N : ℕ} [NeZero N] {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    {P : PlaceSpecialization A q N data hKr k red hα hβ}

set_option hygiene false in
local notation "φ" => frobOnPlacesGeomLevel k N data hKr

set_option synthInstance.maxHeartbeats 1600000 in
private theorem residue₁_ne_zero (R : ProlongationTuple P) {f : ↥(modularFunctionFieldBar (N * q))}
    {h₁ : f ∈ R.R₁.integers} (hf : R.R₁.residue ⟨f, h₁⟩ ≠ 0) :
    (R.residue₁ ⟨f, h₁⟩ : ↥(modularFunctionFieldC k N)) ≠ 0 := by
  rw [ProlongationTuple.residue₁_apply]
  exact (map_ne_zero R.ι).mpr hf

set_option synthInstance.maxHeartbeats 1600000 in
private theorem residue₂_ne_zero (R : ProlongationTuple P) {f : ↥(modularFunctionFieldBar (N * q))}
    {h₂ : f ∈ R.R₂.integers} (hf : R.R₂.residue ⟨f, h₂⟩ ≠ 0) :
    (R.residue₂ ⟨f, h₂⟩ : ↥(modularFunctionFieldC k N)) ≠ 0 := by
  rw [ProlongationTuple.residue₂_apply]
  exact (map_ne_zero R.ι).mpr hf

set_option synthInstance.maxHeartbeats 1600000 in
private theorem R₁_residue_ne_zero_of_residue₁ (R : ProlongationTuple P) {f : ↥(modularFunctionFieldBar (N * q))}
    {h₁ : f ∈ R.R₁.integers} (hf : (R.residue₁ ⟨f, h₁⟩ : ↥(modularFunctionFieldC k N)) ≠ 0) :
    R.R₁.residue ⟨f, h₁⟩ ≠ 0 := by
  intro h0
  apply hf
  rw [ProlongationTuple.residue₁_apply, h0, map_zero]

set_option synthInstance.maxHeartbeats 1600000 in
private theorem R₂_residue_ne_zero_of_residue₂ (R : ProlongationTuple P) {f : ↥(modularFunctionFieldBar (N * q))}
    {h₂ : f ∈ R.R₂.integers} (hf : (R.residue₂ ⟨f, h₂⟩ : ↥(modularFunctionFieldC k N)) ≠ 0) :
    R.R₂.residue ⟨f, h₂⟩ ≠ 0 := by
  intro h0
  apply hf
  rw [ProlongationTuple.residue₂_apply, h0, map_zero]

private theorem ord_eq_of_hasValue_zpow_mul (v : Place k ↥(modularFunctionFieldC k N))
    {ϖ f : ↥(modularFunctionFieldC k N)} (hϖ : v.ord ϖ = 1) (n : ℕ) {l : k} (hl : l ≠ 0)
    (h : v.HasValue (ϖ ^ (-(n : ℤ)) * f) l) :
    f ≠ 0 ∧ v.ord f = n := by
  have hϖ0 : ϖ ≠ 0 := by
    rintro rfl
    rw [Place.ord_zero] at hϖ
    exact zero_ne_one hϖ
  have hne : ϖ ^ (-(n : ℤ)) * f ≠ 0 := h.ne_zero hl
  have hf0 : f ≠ 0 := right_ne_zero_of_mul hne
  have hϖn : ϖ ^ (-(n : ℤ)) ≠ 0 := zpow_ne_zero _ hϖ0
  have h0 : v.ord (ϖ ^ (-(n : ℤ)) * f) = 0 := h.ord_eq_zero hl
  have h1 : v.ord (ϖ ^ (-(n : ℤ)) * f) = v.ord (ϖ ^ (-(n : ℤ))) + v.ord f := v.ord_mul hϖn hf0
  have h2 : v.ord (ϖ ^ (-(n : ℤ))) = -(n : ℤ) * v.ord ϖ := v.ord_zpow ϖ _
  rw [hϖ] at h2
  exact ⟨hf0, by omega⟩

set_option synthInstance.maxHeartbeats 1600000 in

private theorem mem_integersFst_of_mul_mem (R : ProlongationTuple P) {t f : ↥(modularFunctionFieldBar (N * q))}
    (ht : t ∈ R.R₁.integers) (hres : R.R₁.residue ⟨t, ht⟩ ≠ 0) (htf : t * f ∈ R.R₁.integers) : f ∈ R.R₁.integers := by
  obtain ⟨u, hu⟩ := R.R₁.isUnit_of_residue_ne_zero hres
  have h1 : ((↑(u⁻¹) : R.R₁.integers) : ↥(modularFunctionFieldBar (N * q))) * t = 1 := by
    have h := congrArg (fun x : R.R₁.integers => (x : ↥(modularFunctionFieldBar (N * q)))) u.inv_mul
    have h' : ((↑(u⁻¹) : R.R₁.integers) : ↥(modularFunctionFieldBar (N * q)))
        * ((↑u : R.R₁.integers) : ↥(modularFunctionFieldBar (N * q))) = 1 := h
    rw [hu] at h'
    exact h'
  have hmem : ((↑(u⁻¹) : R.R₁.integers) : ↥(modularFunctionFieldBar (N * q))) * (t * f) ∈ R.R₁.integers :=
    mul_mem (↑(u⁻¹) : R.R₁.integers).2 htf
  rwa [← mul_assoc, h1, one_mul] at hmem

set_option synthInstance.maxHeartbeats 1600000 in

private theorem mem_integersSnd_of_mul_mem (R : ProlongationTuple P) {t f : ↥(modularFunctionFieldBar (N * q))}
    (ht : t ∈ R.R₂.integers) (hres : R.R₂.residue ⟨t, ht⟩ ≠ 0) (htf : t * f ∈ R.R₂.integers) : f ∈ R.R₂.integers := by
  obtain ⟨u, hu⟩ := R.R₂.isUnit_of_residue_ne_zero hres
  have h1 : ((↑(u⁻¹) : R.R₂.integers) : ↥(modularFunctionFieldBar (N * q))) * t = 1 := by
    have h := congrArg (fun x : R.R₂.integers => (x : ↥(modularFunctionFieldBar (N * q)))) u.inv_mul
    have h' : ((↑(u⁻¹) : R.R₂.integers) : ↥(modularFunctionFieldBar (N * q)))
        * ((↑u : R.R₂.integers) : ↥(modularFunctionFieldBar (N * q))) = 1 := h
    rw [hu] at h'
    exact h'
  have hmem : ((↑(u⁻¹) : R.R₂.integers) : ↥(modularFunctionFieldBar (N * q))) * (t * f) ∈ R.R₂.integers :=
    mul_mem (↑(u⁻¹) : R.R₂.integers).2 htf
  rwa [← mul_assoc, h1, one_mul] at hmem

set_option maxHeartbeats 3200000 in
set_option synthInstance.maxHeartbeats 1600000 in

private theorem envelope_residue_orders [PerfectField k] (R : ProlongationTuple P)
    (w : Place k ↥(modularFunctionFieldC k N))
    (π : Place k ↥(modularFunctionFieldC k N) → ↥(modularFunctionFieldC k N))
    (hπw : w.ord (π w) = 1)
    {t : ↥(modularFunctionFieldBar (N * q))} (ht₁ : t ∈ R.R₁.integers) (ht₂ : t ∈ R.R₂.integers) {c : k} (hc : c ≠ 0)
    (hres₁ : (R.residue₁ ⟨t, ht₁⟩ : ↥(modularFunctionFieldC k N)) = algebraMap k ↥(modularFunctionFieldC k N) c)
    (hres₂ : (R.residue₂ ⟨t, ht₂⟩ : ↥(modularFunctionFieldC k N)) = 1)
    {g : ↥(modularFunctionFieldBar (N * q))} (hg₁ : t * g ∈ R.R₁.integers) (hg₂ : t * g ∈ R.R₂.integers)
    (hgi₁ : g ∈ R.R₁.integers) (hgi₂ : g ∈ R.R₂.integers) (n₁ n₂ : ℕ) {l₁ l₂ : k} (hl₁ : l₁ ≠ 0) (hl₂ : l₂ ≠ 0)
    (htw₁ : w.HasValue (π w ^ (-(n₁ : ℤ)) * (R.residue₁ ⟨t * g, hg₁⟩ : ↥(modularFunctionFieldC k N))) l₁)
    (htw₂ : (arithFrobC q k N • w).HasValue
      ((arithFrobC q k N • π w) ^ (-(n₂ : ℤ)) * (R.residue₂ ⟨t * g, hg₂⟩ : ↥(modularFunctionFieldC k N))) l₂) :
    R.R₁.residue ⟨g, hgi₁⟩ ≠ 0 ∧ R.R₂.residue ⟨g, hgi₂⟩ ≠ 0 ∧
      w.ord (R.residue₁ ⟨g, hgi₁⟩ : ↥(modularFunctionFieldC k N)) = n₁ ∧
      (arithFrobC q k N • w).ord (R.residue₂ ⟨g, hgi₂⟩ : ↥(modularFunctionFieldC k N)) = n₂ := by
  have hprod₁ : (⟨t * g, hg₁⟩ : R.R₁.integers) = ⟨t, ht₁⟩ * ⟨g, hgi₁⟩ := Subtype.ext rfl
  have hprod₂ : (⟨t * g, hg₂⟩ : R.R₂.integers) = ⟨t, ht₂⟩ * ⟨g, hgi₂⟩ := Subtype.ext rfl
  have hmul₁ : (R.residue₁ ⟨t * g, hg₁⟩ : ↥(modularFunctionFieldC k N))
      = algebraMap k ↥(modularFunctionFieldC k N) c * R.residue₁ ⟨g, hgi₁⟩ := by
    rw [hprod₁, map_mul, hres₁]
  have hmul₂ : (R.residue₂ ⟨t * g, hg₂⟩ : ↥(modularFunctionFieldC k N)) = R.residue₂ ⟨g, hgi₂⟩ := by
    rw [hprod₂, map_mul, hres₂, one_mul]
  obtain ⟨htg₁, hord₁⟩ := ord_eq_of_hasValue_zpow_mul w hπw n₁ hl₁ htw₁
  have hπw' : (arithFrobC q k N • w).ord (arithFrobC q k N • π w) = 1 :=
    (SemilinearAut.ord_smul (arithFrobC q k N) w (π w)).trans hπw
  obtain ⟨htg₂, hord₂⟩ := ord_eq_of_hasValue_zpow_mul (arithFrobC q k N • w) hπw' n₂ hl₂ htw₂
  rw [hmul₁] at htg₁ hord₁
  rw [hmul₂] at htg₂ hord₂
  have hc' : algebraMap k ↥(modularFunctionFieldC k N) c ≠ 0 := (map_ne_zero _).mpr hc
  have hg₁' : (R.residue₁ ⟨g, hgi₁⟩ : ↥(modularFunctionFieldC k N)) ≠ 0 := right_ne_zero_of_mul htg₁
  have hsplit : w.ord (algebraMap k ↥(modularFunctionFieldC k N) c * R.residue₁ ⟨g, hgi₁⟩)
      = w.ord (algebraMap k ↥(modularFunctionFieldC k N) c) + w.ord (R.residue₁ ⟨g, hgi₁⟩) := w.ord_mul hc' hg₁'
  have hc0 : w.ord (algebraMap k ↥(modularFunctionFieldC k N) c) = 0 := (Place.hasValue_algebraMap w c).ord_eq_zero hc
  refine ⟨R₁_residue_ne_zero_of_residue₁ R hg₁', R₂_residue_ne_zero_of_residue₂ R htg₂, ?_, hord₂⟩
  omega

set_option synthInstance.maxHeartbeats 1600000 in

private theorem degree_mapDomain_fstDiv_eq_neg [IsAlgClosed k] (R : ProlongationTuple P) (hDF : R.DivisorLawFst)
    {f : ↥(modularFunctionFieldBar (N * q))} (h₁ : f ∈ R.R₁.integers) (h₂ : f ∈ R.R₂.integers)
    (hr₁ : R.R₁.residue ⟨f, h₁⟩ ≠ 0) (hr₂ : R.R₂.residue ⟨f, h₂⟩ ≠ 0)
    (Df : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) (hDf : ∀ W, Df W = W.ord f)
    {w : Place k ↥(modularFunctionFieldC k N)} (hw : φ (φ w) = w) (c : ℤ)
    (hwc : w.ord (R.residue₁ ⟨f, h₁⟩ : ↥(modularFunctionFieldC k N)) = c)
    (hother : ∀ v : Place k ↥(modularFunctionFieldC k N), φ (φ v) = v → v ≠ w →
      v.ord (R.residue₁ ⟨f, h₁⟩ : ↥(modularFunctionFieldC k N)) = 0) :
    Divisor.degree (Finsupp.mapDomain P.reduceFst (P.fstDiv Df)) = -c := by
  classical
  haveI : HasPrincipalDivisors k ↥(modularFunctionFieldC k N) :=
    hasPrincipalDivisors_modularFunctionFieldC_of_perfectField k N
  obtain ⟨Δ, hΔ, hΔdeg⟩ := HasPrincipalDivisors.exists_divisor (K := k) _ (residue₁_ne_zero R hr₁)
  have key : Finsupp.mapDomain P.reduceFst (P.fstDiv Df) = Δ - Finsupp.single w c := by
    ext v
    rw [Finsupp.sub_apply, hΔ v, Finsupp.single_apply]
    by_cases hv : φ (φ v) = v
    · rw [mapDomain_fstDiv_eq_zero_of_fixed P Df hv]
      by_cases hvw : w = v
      · subst hvw
        rw [if_pos rfl, hwc, sub_self]
      · rw [if_neg hvw, hother v hv (Ne.symm hvw), sub_zero]
    · have hvw : ¬ w = v := fun h => hv (by rw [← h]; exact hw)
      rw [if_neg hvw, sub_zero]
      exact hDF f h₁ h₂ hr₁ hr₂ Df hDf v hv
  rw [key, map_sub, hΔdeg, Divisor.degree_single, place_deg_eq_one_of_isAlgClosed k N w]
  simp

set_option synthInstance.maxHeartbeats 1600000 in

private theorem degree_mapDomain_sndDiv_eq_neg [IsAlgClosed k] (R : ProlongationTuple P) (hDS : R.DivisorLawSnd)
    {f : ↥(modularFunctionFieldBar (N * q))} (h₁ : f ∈ R.R₁.integers) (h₂ : f ∈ R.R₂.integers)
    (hr₁ : R.R₁.residue ⟨f, h₁⟩ ≠ 0) (hr₂ : R.R₂.residue ⟨f, h₂⟩ ≠ 0)
    (Df : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) (hDf : ∀ W, Df W = W.ord f)
    {w' : Place k ↥(modularFunctionFieldC k N)} (hw' : φ (φ w') = w') (c : ℤ)
    (hwc : w'.ord (R.residue₂ ⟨f, h₂⟩ : ↥(modularFunctionFieldC k N)) = c)
    (hother : ∀ v : Place k ↥(modularFunctionFieldC k N), φ (φ v) = v → v ≠ w' →
      v.ord (R.residue₂ ⟨f, h₂⟩ : ↥(modularFunctionFieldC k N)) = 0) :
    Divisor.degree (Finsupp.mapDomain P.reduceSnd (P.sndDiv Df)) = -c := by
  classical
  haveI : HasPrincipalDivisors k ↥(modularFunctionFieldC k N) :=
    hasPrincipalDivisors_modularFunctionFieldC_of_perfectField k N
  obtain ⟨Δ, hΔ, hΔdeg⟩ := HasPrincipalDivisors.exists_divisor (K := k) _ (residue₂_ne_zero R hr₂)
  have key : Finsupp.mapDomain P.reduceSnd (P.sndDiv Df) = Δ - Finsupp.single w' c := by
    ext v
    rw [Finsupp.sub_apply, hΔ v, Finsupp.single_apply]
    by_cases hv : φ (φ v) = v
    · rw [mapDomain_sndDiv_eq_zero_of_fixed P Df hv]
      by_cases hvw : w' = v
      · subst hvw
        rw [if_pos rfl, hwc, sub_self]
      · rw [if_neg hvw, hother v hv (Ne.symm hvw), sub_zero]
    · have hvw : ¬ w' = v := fun h => hv (by rw [← h]; exact hw')
      rw [if_neg hvw, sub_zero]
      exact hDS f h₁ h₂ hr₁ hr₂ Df hDf v hv
  rw [key, map_sub, hΔdeg, Divisor.degree_single, place_deg_eq_one_of_isAlgClosed k N w']
  simp

set_option synthInstance.maxHeartbeats 1600000 in

private theorem ord_residue_eq_zero_of_fixed [PerfectField k] (hqN : ¬ q ∣ N) (R : ProlongationTuple P)
    (hR : R.IsModel) (W : Finset (Place k ↥(modularFunctionFieldC k N))) (hRL : R.RegularityLaw W)
    (hO : R.OrderLawFixed) {f : ↥(modularFunctionFieldBar (N * q))} (h₁ : f ∈ R.R₁.integers) (h₂ : f ∈ R.R₂.integers)
    (hr₁ : R.R₁.residue ⟨f, h₁⟩ ≠ 0) (hr₂ : R.R₂.residue ⟨f, h₂⟩ ≠ 0)
    (Df : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) (hDf : ∀ W, Df W = W.ord f)
    {w : Place k ↥(modularFunctionFieldC k N)}
    (hfst : ∀ v : Place k ↥(modularFunctionFieldC k N), φ (φ v) = v → v ≠ w → ∀ W', Df W' ≠ 0 → P.reduceFst W' ≠ v)
    (hsnd : ∀ v : Place k ↥(modularFunctionFieldC k N), φ (φ v) = v → v ≠ φ w → ∀ W', Df W' ≠ 0 → P.reduceSnd W' ≠ v) :
    (∀ v : Place k ↥(modularFunctionFieldC k N), φ (φ v) = v → v ≠ w →
        v.ord (R.residue₁ ⟨f, h₁⟩ : ↥(modularFunctionFieldC k N)) = 0) ∧
      (∀ v : Place k ↥(modularFunctionFieldC k N), φ (φ v) = v → v ≠ φ w →
        v.ord (R.residue₂ ⟨f, h₂⟩ : ↥(modularFunctionFieldC k N)) = 0) := by
  classical
  obtain ⟨-, -, hCI, hCZ⟩ : R.DivisorLawFst ∧ R.DivisorLawSnd ∧ R.CuspLawInfty ∧ R.CuspLawZero := hR
  have hr₁' := residue₁_ne_zero R hr₁
  have hr₂' := residue₂_ne_zero R hr₂

  have haffine : ∀ v : Place k ↥(modularFunctionFieldC k N), φ (φ v) = v → v ≠ w → IsAffineGeomPlace k N v →
      v.ord (R.residue₁ ⟨f, h₁⟩ : ↥(modularFunctionFieldC k N)) = 0 ∧
        (φ v).ord (R.residue₂ ⟨f, h₂⟩ : ↥(modularFunctionFieldC k N)) = 0 := by
    intro v hv hvw haff
    have hnopole : ∀ W', P.reduceFst W' = v → 0 ≤ W'.ord f := by
      intro W' hW'
      by_contra hneg
      exact hfst v hv hvw W' (by rw [hDf]; exact (not_le.mp hneg).ne) hW'
    obtain ⟨hreg₁, hreg₂⟩ := hRL.1 f h₁ h₂ v hv haff hnopole
    have hsum := hO f h₁ h₂ hr₁ hr₂ Df hDf v hv haff
    rw [mapDomain_eq_zero_of_forall_ne _ _ _ (hfst v hv hvw)] at hsum
    have ha := hreg₁ hr₁'
    have hb := hreg₂ hr₂'
    constructor <;> omega
  constructor
  · intro v hv hvw
    by_cases haff : IsAffineGeomPlace k N v
    · exact (haffine v hv hvw haff).1
    · obtain ⟨⟨c, hc, hcv⟩, -⟩ :=
        exists_isInftySide_reduceFst_eq_and_isZeroSide_reduceSnd_eq_of_not_isAffineGeomPlace hqN P v haff
      have hlaw := hCI f h₁ h₂ hr₁ hr₂ Df hDf c hc
      rw [hcv] at hlaw
      rw [← hlaw]
      exact mapDomain_filter_eq_zero_of_forall_ne _ _ _ _ (hfst v hv hvw)
  · intro v hv hvw
    by_cases haff : IsAffineGeomPlace k N v
    · have hv' : φ (φ (φ v)) = φ v := frob_fixed_of_fixed hv
      have haff' : IsAffineGeomPlace k N (φ v) := isAffineGeomPlace_frobOnPlacesGeomLevel k N data hKr v haff
      have hvw' : φ v ≠ w := by
        intro h
        apply hvw
        rw [← h, hv]
      have h := (haffine (φ v) hv' hvw' haff').2
      rw [hv] at h
      exact h
    · obtain ⟨-, ⟨c, hc, hcv⟩⟩ :=
        exists_isInftySide_reduceFst_eq_and_isZeroSide_reduceSnd_eq_of_not_isAffineGeomPlace hqN P v haff
      have hlaw := hCZ f h₁ h₂ hr₁ hr₂ Df hDf c hc
      rw [hcv] at hlaw
      rw [← hlaw]
      exact mapDomain_filter_eq_zero_of_forall_ne _ _ _ _ (hsnd v hv hvw)

private theorem envelope_support (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
    (V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)))
    (hV₁ : ¬ P.IsStrictFst V) (hV₂ : ¬ P.IsStrictSnd V)
    (g : ↥(modularFunctionFieldBar (N * q))) (E : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)))
    (hpol : ∀ V' : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)),
      V'.ord g < 0 → P.IsStrictFst V' ∨ P.IsStrictSnd V')
    (hEshape : ∀ V' : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)),
      E V' = ((arithmeticGalois (L := AlgebraicClosure ℚ) (modularFunctionFieldFull (N * q)) σ
          • (Finsupp.single V (1 : ℤ))
        - Finsupp.single V 1 : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)))) V' + max (V'.ord g) 0)
    (hEsupp : ∀ V' ∈ E.support, P.IsStrictFst V' ∨ P.IsStrictSnd V' ∨
      (P.reduceFst V' = P.reduceFst V ∧ ¬ P.IsStrictFst V' ∧ ¬ P.IsStrictSnd V'))
    (W' : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) (hW' : W'.ord g ≠ 0) :
    (P.IsStrictFst W' ∨ P.IsStrictSnd W') ∨
      (P.reduceFst W' = P.reduceFst V ∧ ¬ P.IsStrictFst W' ∧ ¬ P.IsStrictSnd W') := by
  classical
  rcases lt_or_gt_of_ne hW' with hneg | hpos
  · exact Or.inl (hpol W' hneg)
  · by_cases hWV : W' = V
    · subst hWV
      exact Or.inr ⟨rfl, hV₁, hV₂⟩
    · have hdisp : 0 ≤ ((arithmeticGalois (L := AlgebraicClosure ℚ) (modularFunctionFieldFull (N * q)) σ
          • (Finsupp.single V (1 : ℤ))
            - Finsupp.single V 1 : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)))) W' := by
        rw [Finsupp.sub_apply, SemilinearAut.smul_single, Finsupp.single_apply, Finsupp.single_apply,
          if_neg (Ne.symm hWV)]
        split_ifs <;> omega
      have hmem : W' ∈ E.support := by
        rw [Finsupp.mem_support_iff, hEshape W', max_eq_left hpos.le]
        omega
      rcases hEsupp W' hmem with h | h | h
      · exact Or.inl (Or.inl h)
      · exact Or.inl (Or.inr h)
      · exact Or.inr h

private theorem envelope_reductions (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
    (V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)))
    (hV₁ : ¬ P.IsStrictFst V) (hV₂ : ¬ P.IsStrictSnd V)
    (g : ↥(modularFunctionFieldBar (N * q))) (E : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)))
    (hpol : ∀ V' : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)),
      V'.ord g < 0 → P.IsStrictFst V' ∨ P.IsStrictSnd V')
    (hEshape : ∀ V' : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)),
      E V' = ((arithmeticGalois (L := AlgebraicClosure ℚ) (modularFunctionFieldFull (N * q)) σ
          • (Finsupp.single V (1 : ℤ))
        - Finsupp.single V 1 : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)))) V' + max (V'.ord g) 0)
    (hEsupp : ∀ V' ∈ E.support, P.IsStrictFst V' ∨ P.IsStrictSnd V' ∨
      (P.reduceFst V' = P.reduceFst V ∧ ¬ P.IsStrictFst V' ∧ ¬ P.IsStrictSnd V'))
    (Dg : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) (hDg : ∀ W', Dg W' = W'.ord g) :
    (∀ v : Place k ↥(modularFunctionFieldC k N), φ (φ v) = v → v ≠ P.reduceFst V →
        ∀ W', Dg W' ≠ 0 → P.reduceFst W' ≠ v) ∧
      (∀ v : Place k ↥(modularFunctionFieldC k N), φ (φ v) = v → v ≠ φ (P.reduceFst V) →
        ∀ W', Dg W' ≠ 0 → P.reduceSnd W' ≠ v) := by
  constructor
  · intro v hv hvw W' hW'
    rw [hDg] at hW'
    rcases envelope_support σ V hV₁ hV₂ g E hpol hEshape hEsupp W' hW' with hs | ⟨hred, -, -⟩
    · exact reduceFst_ne_of_strict hs hv
    · rw [hred]
      exact Ne.symm hvw
  · intro v hv hvw W' hW'
    rw [hDg] at hW'
    rcases envelope_support σ V hV₁ hV₂ g E hpol hEshape hEsupp W' hW' with hs | ⟨hred, hn₁, hn₂⟩
    · exact reduceSnd_ne_of_strict hs hv
    · rw [(fixed_of_not_strict hn₁ hn₂).2, hred]
      exact Ne.symm hvw

end Laws

section Lift

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {N : ℕ} [NeZero N] {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    {P : PlaceSpecialization A q N data hKr k red hα hβ}

set_option hygiene false in
local notation "φ" => frobOnPlacesGeomLevel k N data hKr

set_option synthInstance.maxHeartbeats 1600000 in

private theorem ord_residue_eq_neg_of_exact (hqN : ¬ q ∣ N) (R : ProlongationTuple P)
    {G : ↥(modularFunctionFieldBar (N * q))} (h₁ : G ∈ R.R₁.integers) (h₂ : G ∈ R.R₂.integers)
    (D₁ D₂ : Divisor k ↥(modularFunctionFieldC k N))
    (hfix : ∀ v : Place k ↥(modularFunctionFieldC k N), φ (φ v) = v → IsAffineGeomPlace k N v →
      v.ord (R.residue₁ ⟨G, h₁⟩ : ↥(modularFunctionFieldC k N)) + D₁ v = 0 ∧
        (φ v).ord (R.residue₂ ⟨G, h₂⟩ : ↥(modularFunctionFieldC k N)) + D₂ (φ v) = 0)
    (hcI : ∀ c : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)), IsInftySide P c →
      (P.reduceFst c).ord (R.residue₁ ⟨G, h₁⟩ : ↥(modularFunctionFieldC k N)) + D₁ (P.reduceFst c) = 0)
    (hcZ : ∀ c : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)), IsZeroSide P c →
      (P.reduceSnd c).ord (R.residue₂ ⟨G, h₂⟩ : ↥(modularFunctionFieldC k N)) + D₂ (P.reduceSnd c) = 0) :
    (∀ v : Place k ↥(modularFunctionFieldC k N), φ (φ v) = v →
        v.ord (R.residue₁ ⟨G, h₁⟩ : ↥(modularFunctionFieldC k N)) = -D₁ v) ∧
      (∀ v : Place k ↥(modularFunctionFieldC k N), φ (φ v) = v →
        v.ord (R.residue₂ ⟨G, h₂⟩ : ↥(modularFunctionFieldC k N)) = -D₂ v) := by
  constructor
  · intro v hv
    by_cases haff : IsAffineGeomPlace k N v
    · have h := (hfix v hv haff).1
      linarith
    · obtain ⟨⟨c, hc, hcv⟩, -⟩ :=
        exists_isInftySide_reduceFst_eq_and_isZeroSide_reduceSnd_eq_of_not_isAffineGeomPlace hqN P v haff
      have h := hcI c hc
      rw [hcv] at h
      linarith
  · intro v hv
    by_cases haff : IsAffineGeomPlace k N v
    · have h := (hfix (φ v) (frob_fixed_of_fixed hv)
        (isAffineGeomPlace_frobOnPlacesGeomLevel k N data hKr v haff)).2
      rw [hv] at h
      linarith
    · obtain ⟨-, ⟨c, hc, hcv⟩⟩ :=
        exists_isInftySide_reduceFst_eq_and_isZeroSide_reduceSnd_eq_of_not_isAffineGeomPlace hqN P v haff
      have h := hcZ c hc
      rw [hcv] at h
      linarith

set_option synthInstance.maxHeartbeats 1600000 in

private theorem isGoodDiv_add_of_exact [PerfectField k] (hqN : ¬ q ∣ N) (R : ProlongationTuple P)
    (hR : R.IsModel) (hO : R.OrderLawFixed) (W : Finset (Place k ↥(modularFunctionFieldC k N)))
    (π : Place k ↥(modularFunctionFieldC k N) → ↥(modularFunctionFieldC k N))
    (E : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)))
    (D₁ D₂ : Divisor k ↥(modularFunctionFieldC k N)) (lam : Place k ↥(modularFunctionFieldC k N) → k)
    (hsd : R.SplitDatum W π E D₁ D₂ lam)
    {G : ↥(modularFunctionFieldBar (N * q))} (h₁ : G ∈ R.R₁.integers) (h₂ : G ∈ R.R₂.integers)
    (hG₁ : R.R₁.residue ⟨G, h₁⟩ ≠ 0) (hG₂ : R.R₂.residue ⟨G, h₂⟩ ≠ 0) (hGE : G ∈ riemannRochSpace E)
    (hfix : ∀ v : Place k ↥(modularFunctionFieldC k N), φ (φ v) = v → IsAffineGeomPlace k N v →
      v.ord (R.residue₁ ⟨G, h₁⟩ : ↥(modularFunctionFieldC k N)) + D₁ v = 0 ∧
        (φ v).ord (R.residue₂ ⟨G, h₂⟩ : ↥(modularFunctionFieldC k N)) + D₂ (φ v) = 0)
    (hcI : ∀ c : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)), IsInftySide P c →
      (P.reduceFst c).ord (R.residue₁ ⟨G, h₁⟩ : ↥(modularFunctionFieldC k N)) + D₁ (P.reduceFst c) = 0)
    (hcZ : ∀ c : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)), IsZeroSide P c →
      (P.reduceSnd c).ord (R.residue₂ ⟨G, h₂⟩ : ↥(modularFunctionFieldC k N)) + D₂ (P.reduceSnd c) = 0)
    (DG : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) (hDG : ∀ W', DG W' = W'.ord G) :
    P.IsGoodDiv (E + DG) := by
  classical
  obtain ⟨-, -, hCI, hCZ⟩ : R.DivisorLawFst ∧ R.DivisorLawSnd ∧ R.CuspLawInfty ∧ R.CuspLawZero := hR
  obtain ⟨-, -, -, -, -, hfixE, hcE₁, hcE₂, -⟩ := hsd
  have hG0 : G ≠ 0 := by
    intro hz
    apply hG₁
    have : (⟨G, h₁⟩ : R.R₁.integers) = 0 := Subtype.ext hz
    rw [this, map_zero]
  have hOG := hO G h₁ h₂ hG₁ hG₂ DG hDG
  have hCIG := hCI G h₁ h₂ hG₁ hG₂ DG hDG
  have hCZG := hCZ G h₁ h₂ hG₁ hG₂ DG hDG
  have hnn : ∀ W', 0 ≤ (E + DG) W' := by
    intro W'
    rw [Finsupp.add_apply, hDG]
    rcases (mem_riemannRochSpace_iff.mp hGE) W' with h | h
    · exact absurd h hG0
    · omega
  intro W' hW'
  have hpos : 0 < (E + DG) W' := lt_of_le_of_ne (hnn W') (Ne.symm (Finsupp.mem_support_iff.mp hW'))
  rcases trichotomy P W' with hk | hk | ⟨hv, -⟩
  · exact Or.inl hk
  · exact Or.inr hk
  · exfalso
    by_cases haff : IsAffineGeomPlace k N (P.reduceFst W')
    · have hmass : Finsupp.mapDomain P.reduceFst (E + DG) (P.reduceFst W') = 0 := by
        obtain ⟨ha, hb⟩ := hfix _ hv haff
        rw [Finsupp.mapDomain_add, Finsupp.add_apply, hOG _ hv haff, ← hfixE _ hv haff]
        omega
      have hle := le_mapDomain (E + DG) P.reduceFst (P.reduceFst W') (fun W'' _ => hnn W'') rfl
      rw [hmass] at hle
      exact absurd hle (not_le.mpr hpos)
    · have hc : IsCuspidal P W' := ProlongationTuple.isCuspidal_of_not_isAffineGeomPlace_reduceFst P W' haff
      rcases ProlongationTuple.isInftySide_or_isZeroSide_of_isCuspidal P hqN W' hc with hs | hs
      · have hmass : Finsupp.mapDomain P.reduceFst ((E + DG).filter (IsInftySide P)) (P.reduceFst W') = 0 := by
          have h := hcI W' hs
          rw [Finsupp.filter_add, Finsupp.mapDomain_add, Finsupp.add_apply, hCIG W' hs, ← hcE₁ W' hs]
          omega
        have hle := le_mapDomain_filter (E + DG) (IsInftySide P) P.reduceFst (P.reduceFst W')
          (fun W'' _ _ => hnn W'') hs rfl
        rw [hmass] at hle
        exact absurd hle (not_le.mpr hpos)
      · have hmass : Finsupp.mapDomain P.reduceSnd ((E + DG).filter (IsZeroSide P)) (P.reduceSnd W') = 0 := by
          have h := hcZ W' hs
          rw [Finsupp.filter_add, Finsupp.mapDomain_add, Finsupp.add_apply, hCZG W' hs, ← hcE₂ W' hs]
          omega
        have hle := le_mapDomain_filter (E + DG) (IsZeroSide P) P.reduceSnd (P.reduceSnd W')
          (fun W'' _ _ => hnn W'') hs rfl
        rw [hmass] at hle
        exact absurd hle (not_le.mpr hpos)

private theorem padding_apply_eq_zero {m : ℕ}
    {Q₁ Q₂ : Fin m → Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))}
    (hQ₁ : ∀ i, P.IsStrictFst (Q₁ i)) (hQ₂ : ∀ j, P.IsStrictSnd (Q₂ j))
    {F : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))}
    (hF : F = ∑ i, Finsupp.single (Q₁ i) (1 : ℤ) + ∑ j, Finsupp.single (Q₂ j) (1 : ℤ))
    {V' : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))}
    (hns : ¬ (P.IsStrictFst V' ∨ P.IsStrictSnd V')) :
    F V' = 0 := by
  subst hF
  rw [Finsupp.add_apply, sum_single_apply_eq_zero Q₁ (V := V') fun i hi => hns (Or.inl (hi ▸ hQ₁ i)),
    sum_single_apply_eq_zero Q₂ (V := V') fun j hj => hns (Or.inr (hj ▸ hQ₂ j)), add_zero]

private theorem padding_not_cuspidal {m : ℕ}
    {Q₁ Q₂ : Fin m → Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))}
    (hQ₁ : ∀ i, P.IsStrictFst (Q₁ i)) (hQ₂ : ∀ j, P.IsStrictSnd (Q₂ j))
    (haff₁ : ∀ i, IsAffineGeomPlace k N (P.reduceFst (Q₁ i))) (haff₂ : ∀ j, IsAffineGeomPlace k N (P.reduceSnd (Q₂ j)))
    {F : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))}
    (hF : F = ∑ i, Finsupp.single (Q₁ i) (1 : ℤ) + ∑ j, Finsupp.single (Q₂ j) (1 : ℤ))
    {V' : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))} (hne : F V' ≠ 0) :
    ¬ IsCuspidal P V' ∧ ¬ IsCuspidal' P V' := by
  subst hF
  rw [Finsupp.add_apply] at hne
  by_cases h1 : (∑ i, Finsupp.single (Q₁ i) (1 : ℤ)) V' = 0
  · rw [h1, zero_add] at hne
    obtain ⟨j, rfl⟩ := exists_eq_of_sum_single_apply_ne_zero Q₂ hne
    exact not_cuspidal_of_isStrictSnd (hQ₂ j) (haff₂ j)
  · obtain ⟨i, rfl⟩ := exists_eq_of_sum_single_apply_ne_zero Q₁ h1
    exact not_cuspidal_of_isStrictFst (hQ₁ i) (haff₁ i)

private theorem le_degree_fst_of_padded [IsAlgClosed k]
    (E : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)))
    (hE0 : ∀ V', 0 ≤ E V') {m : ℕ} {Q₁ Q₂ : Fin m → Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))}
    (hQ₁ : ∀ i, P.IsStrictFst (Q₁ i)) (hQ₂ : ∀ j, P.IsStrictSnd (Q₂ j))
    {F : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))}
    (hF : F = ∑ i, Finsupp.single (Q₁ i) (1 : ℤ) + ∑ j, Finsupp.single (Q₂ j) (1 : ℤ))
    (w : Place k ↥(modularFunctionFieldC k N)) (n : ℕ) :
    (m : ℤ) ≤ Divisor.degree (Finsupp.mapDomain P.reduceFst (P.fstDiv (E + F)) + Finsupp.single w (n : ℤ)) := by
  subst hF
  have hdeg1 : ∀ v : Place k ↥(modularFunctionFieldC k N), v.deg = 1 := place_deg_eq_one_of_isAlgClosed k N
  have hF₁ : P.fstDiv (∑ i, Finsupp.single (Q₁ i) (1 : ℤ)) = ∑ i, Finsupp.single (Q₁ i) (1 : ℤ) :=
    fstDiv_eq_self_of_forall P fun W' hW' => by
      obtain ⟨i, rfl⟩ := exists_eq_of_sum_single_apply_ne_zero Q₁ hW'
      exact hQ₁ i
  have hF₂ : P.fstDiv (∑ j, Finsupp.single (Q₂ j) (1 : ℤ)) = 0 :=
    fstDiv_eq_zero_of_forall P fun W' hW' =>
      sum_single_apply_eq_zero Q₂ fun j hj => not_isStrictSnd_of_isStrictFst hW' (hj ▸ hQ₂ j)
  have h0 : 0 ≤ Divisor.degree (Finsupp.mapDomain P.reduceFst (P.fstDiv E)) :=
    degree_nonneg_of_nonneg _ hdeg1 fun v => mapDomain_nonneg _ _ _ fun W' _ => fstDiv_apply_nonneg P hE0 W'
  have hn : (0 : ℤ) ≤ (n : ℤ) * (w.deg : ℤ) := by positivity
  rw [fstDiv_add, fstDiv_add, hF₁, hF₂, add_zero, Finsupp.mapDomain_add, map_add, map_add,
    degree_mapDomain_sum_single hdeg1, Divisor.degree_single]
  linarith

private theorem le_degree_snd_of_padded [IsAlgClosed k]
    (E : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)))
    (hE0 : ∀ V', 0 ≤ E V') {m : ℕ} {Q₁ Q₂ : Fin m → Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))}
    (hQ₁ : ∀ i, P.IsStrictFst (Q₁ i)) (hQ₂ : ∀ j, P.IsStrictSnd (Q₂ j))
    {F : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))}
    (hF : F = ∑ i, Finsupp.single (Q₁ i) (1 : ℤ) + ∑ j, Finsupp.single (Q₂ j) (1 : ℤ))
    (w' : Place k ↥(modularFunctionFieldC k N)) (n : ℕ) :
    (m : ℤ) ≤ Divisor.degree (Finsupp.mapDomain P.reduceSnd (P.sndDiv (E + F)) + Finsupp.single w' (n : ℤ)) := by
  subst hF
  have hdeg1 : ∀ v : Place k ↥(modularFunctionFieldC k N), v.deg = 1 := place_deg_eq_one_of_isAlgClosed k N
  have hF₁ : P.sndDiv (∑ i, Finsupp.single (Q₁ i) (1 : ℤ)) = 0 :=
    sndDiv_eq_zero_of_forall P fun W' hW' =>
      sum_single_apply_eq_zero Q₁ fun i hi => not_isStrictSnd_of_isStrictFst (hi ▸ hQ₁ i) hW'
  have hF₂ : P.sndDiv (∑ j, Finsupp.single (Q₂ j) (1 : ℤ)) = ∑ j, Finsupp.single (Q₂ j) (1 : ℤ) :=
    sndDiv_eq_self_of_forall P fun W' hW' => by
      obtain ⟨j, rfl⟩ := exists_eq_of_sum_single_apply_ne_zero Q₂ hW'
      exact hQ₂ j
  have h0 : 0 ≤ Divisor.degree (Finsupp.mapDomain P.reduceSnd (P.sndDiv E)) :=
    degree_nonneg_of_nonneg _ hdeg1 fun v => mapDomain_nonneg _ _ _ fun W' _ => sndDiv_apply_nonneg P hE0 W'
  have hn : (0 : ℤ) ≤ (n : ℤ) * (w'.deg : ℤ) := by positivity
  rw [sndDiv_add, sndDiv_add, hF₁, hF₂, zero_add, Finsupp.mapDomain_add, map_add, map_add,
    degree_mapDomain_sum_single hdeg1, Divisor.degree_single]
  linarith

end Lift

section Assembly

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {N : ℕ} [NeZero N] {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    {P : PlaceSpecialization A q N data hKr k red hα hβ}

set_option hygiene false in
local notation "φ" => frobOnPlacesGeomLevel k N data hKr

set_option maxHeartbeats 3200000 in
set_option synthInstance.maxHeartbeats 1600000 in

private theorem exists_divisor_envelope_function [IsAlgClosed k] (hqN : ¬ q ∣ N) (R : ProlongationTuple P)
    (hR : R.IsModel)
    (W : Finset (Place k ↥(modularFunctionFieldC k N))) (hRL : R.RegularityLaw W) (hO : R.OrderLawFixed)
    (π : Place k ↥(modularFunctionFieldC k N) → ↥(modularFunctionFieldC k N))
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
    (V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) (hV₁ : ¬ P.IsStrictFst V)
    (hV₂ : ¬ P.IsStrictSnd V) (hπw : (P.reduceFst V).ord (π (P.reduceFst V)) = 1) (hw2 : φ (φ (P.reduceFst V)) = P.reduceFst V)
    (t : ↥(modularFunctionFieldBar (N * q))) (ht₁ : t ∈ R.R₁.integers) (ht₂ : t ∈ R.R₂.integers) (u : (↥A)ˣ)
    (hres₁ : (R.residue₁ ⟨t, ht₁⟩ : ↥(modularFunctionFieldC k N))
      = algebraMap k ↥(modularFunctionFieldC k N) (red (u : A)))
    (hres₂ : (R.residue₂ ⟨t, ht₂⟩ : ↥(modularFunctionFieldC k N)) = 1)
    (g : ↥(modularFunctionFieldBar (N * q)))
    (E : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)))
    (hg₁ : t * g ∈ R.R₁.integers) (hg₂ : t * g ∈ R.R₂.integers) (n₁ n₂ : ℕ) (l₁ l₂ : k)
    (hgV : 0 < V.ord g)
    (hpol : ∀ V' : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)),
      V'.ord g < 0 → P.IsStrictFst V' ∨ P.IsStrictSnd V')
    (hEshape : ∀ V' : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)),
      E V' = ((arithmeticGalois (L := AlgebraicClosure ℚ) (modularFunctionFieldFull (N * q)) σ
          • (Finsupp.single V (1 : ℤ))
        - Finsupp.single V 1 : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)))) V' + max (V'.ord g) 0)
    (hEsupp : ∀ V' ∈ E.support, P.IsStrictFst V' ∨ P.IsStrictSnd V' ∨
      (P.reduceFst V' = P.reduceFst V ∧ ¬ P.IsStrictFst V' ∧ ¬ P.IsStrictSnd V'))
    (hl₁ : l₁ ≠ 0) (hl₂ : l₂ ≠ 0)
    (htw₁ : (P.reduceFst V).HasValue (π (P.reduceFst V) ^ (-(n₁ : ℤ))
      * (R.residue₁ ⟨t * g, hg₁⟩ : ↥(modularFunctionFieldC k N))) l₁)
    (htw₂ : (arithFrobC q k N • P.reduceFst V).HasValue
      ((arithFrobC q k N • π (P.reduceFst V)) ^ (-(n₂ : ℤ))
        * (R.residue₂ ⟨t * g, hg₂⟩ : ↥(modularFunctionFieldC k N))) l₂) :
    g ≠ 0 ∧ ∃ Dg : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)),
      (∀ W', Dg W' = W'.ord g) ∧ Divisor.degree Dg = 0 ∧
      Divisor.degree (Finsupp.mapDomain P.reduceFst (P.fstDiv Dg)) = -(n₁ : ℤ) ∧
      Divisor.degree (Finsupp.mapDomain P.reduceSnd (P.sndDiv Dg)) = -(n₂ : ℤ) := by
  have hg0 : g ≠ 0 := by
    rintro rfl
    rw [Place.ord_zero] at hgV
    exact lt_irrefl 0 hgV
  have hc : red (u : A) ≠ 0 := (u.isUnit.map red).ne_zero
  have htr₁ : R.R₁.residue ⟨t, ht₁⟩ ≠ 0 := by
    refine R₁_residue_ne_zero_of_residue₁ R ?_
    rw [hres₁]
    exact (map_ne_zero _).mpr hc
  have htr₂ : R.R₂.residue ⟨t, ht₂⟩ ≠ 0 := by
    refine R₂_residue_ne_zero_of_residue₂ R ?_
    rw [hres₂]
    exact one_ne_zero
  have hgi₁ : g ∈ R.R₁.integers := mem_integersFst_of_mul_mem R ht₁ htr₁ hg₁
  have hgi₂ : g ∈ R.R₂.integers := mem_integersSnd_of_mul_mem R ht₂ htr₂ hg₂
  obtain ⟨hgr₁, hgr₂, hgw₁, hgw₂⟩ := envelope_residue_orders R (P.reduceFst V) π hπw ht₁ ht₂ hc hres₁ hres₂ hg₁ hg₂
    hgi₁ hgi₂ n₁ n₂ hl₁ hl₂ htw₁ htw₂
  rw [arithFrobC_smul_eq_frobOnPlacesGeomLevel q k N data hKr] at hgw₂
  haveI : HasPrincipalDivisors (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) :=
    hasPrincipalDivisors_modularFunctionFieldBar_unconditional (N * q)
  obtain ⟨Dg, hDg, hDgdeg⟩ := HasPrincipalDivisors.exists_divisor (K := AlgebraicClosure ℚ) g hg0
  obtain ⟨hgfst, hgsnd⟩ := envelope_reductions σ V hV₁ hV₂ g E hpol hEshape hEsupp Dg hDg
  obtain ⟨hgo₁, hgo₂⟩ := ord_residue_eq_zero_of_fixed hqN R hR W hRL hO hgi₁ hgi₂ hgr₁ hgr₂ Dg hDg hgfst hgsnd
  refine ⟨hg0, Dg, hDg, hDgdeg, ?_, ?_⟩
  · exact degree_mapDomain_fstDiv_eq_neg R hR.1 hgi₁ hgi₂ hgr₁ hgr₂ Dg hDg hw2 n₁ hgw₁ hgo₁
  · exact degree_mapDomain_sndDiv_eq_neg R hR.2.1 hgi₁ hgi₂ hgr₁ hgr₂ Dg hDg (frob_fixed_of_fixed hw2) n₂ hgw₂ hgo₂

set_option maxHeartbeats 3200000 in
set_option synthInstance.maxHeartbeats 1600000 in

private theorem exists_padding_lift [IsAlgClosed k] [DecidableEq k] (hqN : ¬ q ∣ N) (R : ProlongationTuple P)
    (hR : R.IsModel) (W : Finset (Place k ↥(modularFunctionFieldC k N))) (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q N k)
    (hRL : R.RegularityLaw W) (hO : R.OrderLawFixed)
    (π : Place k ↥(modularFunctionFieldC k N) → ↥(modularFunctionFieldC k N)) (hπ : ∀ w ∈ W, w.ord (π w) = 1)
    (V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) (hVW : P.reduceFst V ∈ W)
    (hw2 : φ (φ (P.reduceFst V)) = P.reduceFst V)
    (E : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) (hE0 : ∀ V', 0 ≤ E V')
    (hEsupp : ∀ V' ∈ E.support, P.IsStrictFst V' ∨ P.IsStrictSnd V' ∨
      (P.reduceFst V' = P.reduceFst V ∧ ¬ P.IsStrictFst V' ∧ ¬ P.IsStrictSnd V'))
    (hEc : ∀ V' ∈ E.support, ¬ IsCuspidal P V' ∧ ¬ IsCuspidal' P V')
    (f : ↥(modularFunctionFieldBar (N * q))) (hf₁ : f ∈ R.R₁.integers) (hf₂ : f ∈ R.R₂.integers)
    (hford : ∀ V' : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)),
      (P.reduceFst V' = P.reduceFst V ∧ ¬ P.IsStrictFst V' ∧ ¬ P.IsStrictSnd V') → V'.ord f = E V')
    (n₁ n₂ : ℕ) (l₁ l₂ : k) (hl₁ : l₁ ≠ 0) (hl₂ : l₂ ≠ 0)
    (hn : ((n₁ : ℤ) + n₂) = Finsupp.mapDomain P.reduceFst E (P.reduceFst V))
    (htw₁ : (P.reduceFst V).HasValue (π (P.reduceFst V) ^ (-(n₁ : ℤ))
      * (R.residue₁ ⟨f, hf₁⟩ : ↥(modularFunctionFieldC k N))) l₁)
    (htw₂ : (arithFrobC q k N • P.reduceFst V).HasValue
      ((arithFrobC q k N • π (P.reduceFst V)) ^ (-(n₂ : ℤ))
        * (R.residue₂ ⟨f, hf₂⟩ : ↥(modularFunctionFieldC k N))) l₂) :
    ∃ (F : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) (G : ↥(modularFunctionFieldBar (N * q)))
      (DG : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))),
      (∀ V', ¬ (P.IsStrictFst V' ∨ P.IsStrictSnd V') → F V' = 0) ∧ G ≠ 0 ∧ (∀ W', DG W' = W'.ord G) ∧
      Divisor.degree DG = 0 ∧ P.IsGoodDiv (E + F + DG) ∧
      Divisor.degree (Finsupp.mapDomain P.reduceFst (P.fstDiv DG)) = -(-(n₁ : ℤ)) ∧
      Divisor.degree (Finsupp.mapDomain P.reduceSnd (P.sndDiv DG)) = -(-(n₂ : ℤ)) := by
  have hφC := arithFrobC_smul_eq_frobOnPlacesGeomLevel q k N data hKr (P.reduceFst V)
  have hw2' := frob_fixed_of_fixed hw2
  obtain ⟨B, hB⟩ := exists_finset_of_not_isAffineGeomPlace (N := N) (k := k)
  obtain ⟨Q₁, Q₂, hQ₁, hQ₂, -, -, hB₁, hB₂, -, -⟩ :=
    exists_families_isStrictFst_isStrictSnd_notMem_forall_inertia_smul_eq P hqN B
      (2 * genusFF (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) + 1)
      (2 * genusFF (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) + 1)
  have haff₁ : ∀ i, IsAffineGeomPlace k N (P.reduceFst (Q₁ i)) := fun i => by
    by_contra h
    exact hB₁ i (hB _ h)
  have haff₂ : ∀ j, IsAffineGeomPlace k N (P.reduceSnd (Q₂ j)) := fun j => by
    by_contra h
    exact hB₂ j (hB _ h)
  obtain ⟨F, hF⟩ : ∃ F : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)),
      F = ∑ i, Finsupp.single (Q₁ i) (1 : ℤ) + ∑ j, Finsupp.single (Q₂ j) (1 : ℤ) := ⟨_, rfl⟩
  have hFzero : ∀ V', ¬ (P.IsStrictFst V' ∨ P.IsStrictSnd V') → F V' = 0 := fun _ hns =>
    padding_apply_eq_zero hQ₁ hQ₂ hF hns
  have hE0' : ∀ V', 0 ≤ (E + F) V' := fun V' => by
    rw [Finsupp.add_apply]
    exact add_nonneg (hE0 V') (sum_single_add_sum_single_apply_nonneg Q₁ Q₂ hF V')
  have hEsupp' : ∀ V' ∈ (E + F).support, P.IsStrictFst V' ∨ P.IsStrictSnd V' ∨
      (P.reduceFst V' = P.reduceFst V ∧ ¬ P.IsStrictFst V' ∧ ¬ P.IsStrictSnd V') := by
    intro V' hV'
    by_cases hs : P.IsStrictFst V' ∨ P.IsStrictSnd V'
    · rcases hs with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
    · apply hEsupp V'
      rw [Finsupp.mem_support_iff] at hV' ⊢
      rwa [Finsupp.add_apply, hFzero V' hs, add_zero] at hV'
  have hEc' : ∀ V' ∈ (E + F).support, ¬ IsCuspidal P V' ∧ ¬ IsCuspidal' P V' := by
    intro V' hV'
    by_cases hEV : E V' = 0
    · refine padding_not_cuspidal hQ₁ hQ₂ haff₁ haff₂ hF ?_
      rw [Finsupp.mem_support_iff, Finsupp.add_apply, hEV, zero_add] at hV'
      exact hV'
    · exact hEc V' (Finsupp.mem_support_iff.mpr hEV)
  have hford' : ∀ V' : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)),
      (P.reduceFst V' = P.reduceFst V ∧ ¬ P.IsStrictFst V' ∧ ¬ P.IsStrictSnd V') → V'.ord f = (E + F) V' := by
    intro V' hV'
    rw [Finsupp.add_apply, hFzero V' fun hs => hs.elim hV'.2.1 hV'.2.2, add_zero]
    exact hford V' hV'
  have hFpush : Finsupp.mapDomain P.reduceFst F (P.reduceFst V) = 0 :=
    mapDomain_eq_zero_of_forall_ne F P.reduceFst (P.reduceFst V) fun W' hW' =>
      reduceFst_ne_of_strict (by
        by_contra hns
        exact hW' (hFzero W' hns)) hw2
  have hn' : ((n₁ : ℤ) + n₂) = Finsupp.mapDomain P.reduceFst (E + F) (P.reduceFst V) := by
    rw [Finsupp.mapDomain_add, Finsupp.add_apply, hFpush, add_zero]
    exact hn
  have hsd := ProlongationTuple.splitDatum_of_forall_reduceFst_eq_ord_eq hqN R hR W hW hRL hO π hπ (P.reduceFst V) hVW
    hw2 (E + F) hE0' hEsupp' hEc' f hf₁ hf₂ hford' n₁ n₂ l₁ l₂ hl₁ hl₂ hn' htw₁ htw₂
  rw [hφC] at hsd
  obtain ⟨G, hG₁, hG₂, hGr₁, hGr₂, hGE, hfixG, hcIG, hcZG, -⟩ :=
    ProlongationTuple.exists_mem_riemannRochSpace_ord_residue_eq_neg_of_splitDatum hqN R W hW π ∅ (E + F) _ _ _ hsd
      (by
        have h := le_degree_fst_of_padded E hE0 hQ₁ hQ₂ hF (P.reduceFst V) n₁
        push_cast at h
        exact h)
      (by
        have h := le_degree_snd_of_padded E hE0 hQ₁ hQ₂ hF (φ (P.reduceFst V)) n₂
        push_cast at h
        exact h)
  have hG0 : G ≠ 0 := by
    intro hz
    apply hGr₁
    have : (⟨G, hG₁⟩ : R.R₁.integers) = 0 := Subtype.ext hz
    rw [this, map_zero]
  haveI : HasPrincipalDivisors (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) :=
    hasPrincipalDivisors_modularFunctionFieldBar_unconditional (N * q)
  obtain ⟨DG, hDG, hDGdeg⟩ := HasPrincipalDivisors.exists_divisor (K := AlgebraicClosure ℚ) G hG0
  obtain ⟨hGo₁, hGo₂⟩ := ord_residue_eq_neg_of_exact hqN R hG₁ hG₂ _ _ hfixG hcIG hcZG
  refine ⟨F, G, DG, hFzero, hG0, hDG, hDGdeg, ?_, ?_, ?_⟩
  · exact isGoodDiv_add_of_exact hqN R hR hO W π (E + F) _ _ _ hsd hG₁ hG₂ hGr₁ hGr₂ hGE hfixG hcIG hcZG DG hDG
  · refine degree_mapDomain_fstDiv_eq_neg R hR.1 hG₁ hG₂ hGr₁ hGr₂ DG hDG hw2 (-(n₁ : ℤ)) ?_ fun v hv hvw => ?_
    · rw [hGo₁ _ hw2, branchFst_apply_self P (E + F) hw2 n₁]
    · rw [hGo₁ v hv, branchFst_apply_of_ne P (E + F) _ n₁ hv hvw, neg_zero]
  · refine degree_mapDomain_sndDiv_eq_neg R hR.2.1 hG₁ hG₂ hGr₁ hGr₂ DG hDG hw2' (-(n₂ : ℤ)) ?_ fun v hv hvw => ?_
    · rw [hGo₂ _ hw2', branchSnd_apply_self P (E + F) hw2' n₂]
    · rw [hGo₂ v hv, branchSnd_apply_of_ne P (E + F) _ n₂ hv hvw, neg_zero]

end Assembly

set_option maxHeartbeats 3200000 in
set_option synthInstance.maxHeartbeats 1600000 in
open Classical in

private theorem goodRep_of_envelope
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {N : ℕ} [NeZero N] {k : Type*} [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k]
    {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    {P : PlaceSpecialization A q N data hKr k red hα hβ}
    (hqN : ¬ q ∣ N) (R : ProlongationTuple P) (hR : R.IsModel)
    (W : Finset (Place k (modularFunctionFieldC k N))) (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q N k)
    (hRL : R.RegularityLaw W) (hO : R.OrderLawFixed)
    (π : Place k (modularFunctionFieldC k N) → modularFunctionFieldC k N) (hπ : ∀ w ∈ W, w.ord (π w) = 1)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hσ : σ ∈ A.inertiaSubgroupIn ℚ)
    (V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)))
    (hV : ¬ P.IsStrictFst V ∧ ¬ P.IsStrictSnd V ∧ P.reduceFst V ∈ W)
    (hdeg : arithmeticGalois (L := AlgebraicClosure ℚ) (modularFunctionFieldFull (N * q)) σ
          • (Finsupp.single V (1 : ℤ))
        - Finsupp.single V 1
        ∈ Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar (N * q))))
    (t : ↥(modularFunctionFieldBar (N * q))) (ht₁ : t ∈ R.R₁.integers) (ht₂ : t ∈ R.R₂.integers) (u : (↥A)ˣ)
    (hres₁ : (R.residue₁ ⟨t, ht₁⟩ : ↥(modularFunctionFieldC k N))
      = algebraMap k ↥(modularFunctionFieldC k N) (red (u : A)))
    (hres₂ : (R.residue₂ ⟨t, ht₂⟩ : ↥(modularFunctionFieldC k N)) = 1)
    (g : ↥(modularFunctionFieldBar (N * q)))
    (E : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)))
    (hg₁ : t * g ∈ R.R₁.integers) (hg₂ : t * g ∈ R.R₂.integers) (n₁ n₂ : ℕ) (l₁ l₂ : k)
    (hgV : 0 < V.ord g)
    (hpol : ∀ V' : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)),
      V'.ord g < 0 → P.IsStrictFst V' ∨ P.IsStrictSnd V')
    (hEshape : ∀ V' : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)),
      E V' = ((arithmeticGalois (L := AlgebraicClosure ℚ) (modularFunctionFieldFull (N * q)) σ
          • (Finsupp.single V (1 : ℤ))
        - Finsupp.single V 1 : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)))) V' + max (V'.ord g) 0)
    (hE0 : ∀ V', 0 ≤ E V')
    (hEsupp : ∀ V' ∈ E.support, P.IsStrictFst V' ∨ P.IsStrictSnd V' ∨
      (P.reduceFst V' = P.reduceFst V ∧ ¬ P.IsStrictFst V' ∧ ¬ P.IsStrictSnd V'))
    (hEc : ∀ V' ∈ E.support, ¬ IsCuspidal P V' ∧ ¬ IsCuspidal' P V')
    (htordE : ∀ V' : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)),
      (P.reduceFst V' = P.reduceFst V ∧ ¬ P.IsStrictFst V' ∧ ¬ P.IsStrictSnd V') → V'.ord (t * g) = E V')
    (hl₁ : l₁ ≠ 0) (hl₂ : l₂ ≠ 0)
    (hn : ((n₁ : ℤ) + n₂) = Finsupp.mapDomain P.reduceFst E (P.reduceFst V))
    (htw₁ : (P.reduceFst V).HasValue (π (P.reduceFst V) ^ (-(n₁ : ℤ))
      * (R.residue₁ ⟨t * g, hg₁⟩ : ↥(modularFunctionFieldC k N))) l₁)
    (htw₂ : (arithFrobC q k N • P.reduceFst V).HasValue
      ((arithFrobC q k N • π (P.reduceFst V)) ^ (-(n₂ : ℤ))
        * (R.residue₂ ⟨t * g, hg₂⟩ : ↥(modularFunctionFieldC k N))) l₂) :
    ∃ (D : ↥(Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar (N * q)))))
      (_ : P.IsGoodDiv (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))))
      (hadm : P.glueData (nodePairsOfPlaces (arithFrobC q k N) W)
          (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)))
        ∈ GluingData.admissible (nodePairsOfPlaces (arithFrobC q k N) W)),
      Pic0.mk D = Pic0.mk ⟨arithmeticGalois (L := AlgebraicClosure ℚ) (modularFunctionFieldFull (N * q)) σ
          • (Finsupp.single V (1 : ℤ))
        - Finsupp.single V 1, hdeg⟩ := by
  obtain ⟨hV₁, hV₂, hVW⟩ := hV
  have hw2 := frobOnPlacesGeomLevel_frobOnPlacesGeomLevel_eq_self_of_mem_ssPlaces hqN P (P.reduceFst V) ((hW _).mp hVW)
  obtain ⟨hg0, Dg, hDg, hDgdeg, hdeg₁g, hdeg₂g⟩ := InertialDisplacement.exists_divisor_envelope_function hqN R hR W hRL
    hO π σ V hV₁ hV₂ (hπ _ hVW) hw2 t ht₁ ht₂ u hres₁ hres₂ g E hg₁ hg₂ n₁ n₂ l₁ l₂ hgV hpol hEshape hEsupp hl₁ hl₂
    htw₁ htw₂
  obtain ⟨F, G, DG, hFzero, hG0, hDG, hDGdeg, hgood₀, hdeg₁G, hdeg₂G⟩ := InertialDisplacement.exists_padding_lift hqN R
    hR W hW hRL hO π hπ V hVW hw2 E hE0 hEsupp hEc (t * g) hg₁ hg₂ htordE n₁ n₂ l₁ l₂ hl₁ hl₂ hn htw₁ htw₂
  have hτ := InertialDisplacement.not_strict_smul P σ hσ hV₁ hV₂
  generalize hΔdef : (arithmeticGalois (L := AlgebraicClosure ℚ) (modularFunctionFieldFull (N * q)) σ
      • (Finsupp.single V (1 : ℤ))
    - Finsupp.single V 1 : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) = Δ at hdeg hEshape ⊢
  have hΔfst : P.fstDiv Δ = 0 :=
    InertialDisplacement.fstDiv_eq_zero_of_forall P fun W' hW' => by
      rw [← hΔdef, Finsupp.sub_apply, SemilinearAut.smul_single, Finsupp.single_apply, Finsupp.single_apply,
        if_neg (InertialDisplacement.ne_of_not_isStrictFst hτ.1 hW'),
        if_neg (InertialDisplacement.ne_of_not_isStrictFst hV₁ hW'), sub_zero]
  have hΔsnd : P.sndDiv Δ = 0 :=
    InertialDisplacement.sndDiv_eq_zero_of_forall P fun W' hW' => by
      rw [← hΔdef, Finsupp.sub_apply, SemilinearAut.smul_single, Finsupp.single_apply, Finsupp.single_apply,
        if_neg (InertialDisplacement.ne_of_not_isStrictSnd hτ.2 hW'),
        if_neg (InertialDisplacement.ne_of_not_isStrictSnd hV₂ hW'), sub_zero]
  have hΔdeg : Divisor.degree Δ = 0 := Divisor.mem_degZero.mp hdeg
  have hD0 : Δ + Dg + DG ∈ Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar (N * q))) := by
    rw [Divisor.mem_degZero, map_add, map_add, hΔdeg, hDgdeg, hDGdeg, add_zero, add_zero]
  have hgoodD : P.IsGoodDiv (Δ + Dg + DG) := by
    intro W' hW'
    by_contra hs
    apply Finsupp.mem_support_iff.mp hW'
    have hEFG : (E + F + DG) W' = 0 := by
      by_contra h
      exact hs (hgood₀ W' (Finsupp.mem_support_iff.mpr h))
    have hgnn : 0 ≤ W'.ord g := by
      by_contra h
      exact hs (hpol W' (not_le.mp h))
    have hE : E W' = Δ W' + W'.ord g := by
      rw [hEshape W', max_eq_left hgnn]
    simp only [Finsupp.add_apply] at hEFG ⊢
    rw [hFzero W' hs, hDG] at hEFG
    rw [hDg, hDG]
    omega
  have hadm : P.glueData (nodePairsOfPlaces (arithFrobC q k N) W) (Δ + Dg + DG)
      ∈ GluingData.admissible (nodePairsOfPlaces (arithFrobC q k N) W) := by
    rw [GluingData.mem_admissible]
    refine ⟨?_, ?_, fun s hs => ⟨?_, ?_⟩⟩
    · show Finsupp.mapDomain P.reduceFst (P.fstDiv (Δ + Dg + DG))
        ∈ Divisor.degZero (K := k) (F := ↥(modularFunctionFieldC k N))
      rw [Divisor.mem_degZero, InertialDisplacement.fstDiv_add, InertialDisplacement.fstDiv_add, hΔfst, zero_add,
        Finsupp.mapDomain_add, map_add, hdeg₁g, hdeg₁G]
      ring
    · show Finsupp.mapDomain P.reduceSnd (P.sndDiv (Δ + Dg + DG))
        ∈ Divisor.degZero (K := k) (F := ↥(modularFunctionFieldC k N))
      rw [Divisor.mem_degZero, InertialDisplacement.sndDiv_add, InertialDisplacement.sndDiv_add, hΔsnd, zero_add,
        Finsupp.mapDomain_add, map_add, hdeg₂g, hdeg₂G]
      ring
    · show Finsupp.mapDomain P.reduceFst (P.fstDiv (Δ + Dg + DG)) s.1 = 0
      exact InertialDisplacement.mapDomain_fstDiv_eq_zero_of_fixed P _
        (frobOnPlacesGeomLevel_frobOnPlacesGeomLevel_eq_self_of_mem_ssPlaces hqN P s.1
          ((hW _).mp (fst_mem_of_mem_nodePairsOfPlaces hs)))
    · show Finsupp.mapDomain P.reduceSnd (P.sndDiv (Δ + Dg + DG)) s.2 = 0
      rw [snd_eq_of_mem_nodePairsOfPlaces hs, arithFrobC_smul_eq_frobOnPlacesGeomLevel q k N data hKr s.1]
      exact InertialDisplacement.mapDomain_sndDiv_eq_zero_of_fixed P _ (InertialDisplacement.frob_fixed_of_fixed
        (frobOnPlacesGeomLevel_frobOnPlacesGeomLevel_eq_self_of_mem_ssPlaces hqN P s.1
          ((hW _).mp (fst_mem_of_mem_nodePairsOfPlaces hs))))
  refine ⟨⟨Δ + Dg + DG, hD0⟩, hgoodD, hadm, ?_⟩
  refine InertialDisplacement.pic0Mk_eq_of_forall_sub_eq_ord _ _ hD0 hdeg (g * G) (mul_ne_zero hg0 hG0) fun V' => ?_
  have hgG : V'.ord (g * G) = V'.ord g + V'.ord G := V'.ord_mul hg0 hG0
  simp only [Finsupp.sub_apply, Finsupp.add_apply]
  rw [hDg, hDG, hgG]
  ring

set_option synthInstance.maxHeartbeats 1600000 in
open Classical in

private theorem glue
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {N : ℕ} [NeZero N] {k : Type*} [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k]
    {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    {P : PlaceSpecialization A q N data hKr k red hα hβ}
    (hqN : ¬ q ∣ N) (R : ProlongationTuple P) (hR : R.IsModel)
    (W : Finset (Place k (modularFunctionFieldC k N))) (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q N k)
    (hRL : R.RegularityLaw W) (hO : R.OrderLawFixed)
    (π : Place k (modularFunctionFieldC k N) → modularFunctionFieldC k N) (hπ : ∀ w ∈ W, w.ord (π w) = 1)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hσ : σ ∈ A.inertiaSubgroupIn ℚ)
    (V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)))
    (hV : ¬ P.IsStrictFst V ∧ ¬ P.IsStrictSnd V ∧ P.reduceFst V ∈ W)
    (hdeg : arithmeticGalois (L := AlgebraicClosure ℚ) (modularFunctionFieldFull (N * q)) σ
          • (Finsupp.single V (1 : ℤ))
        - Finsupp.single V 1
        ∈ Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar (N * q))))
    (t : ↥(modularFunctionFieldBar (N * q))) (ht₁ : t ∈ R.R₁.integers) (ht₂ : t ∈ R.R₂.integers) (u : (↥A)ˣ)
    (hres₁ : (R.residue₁ ⟨t, ht₁⟩ : ↥(modularFunctionFieldC k N))
      = algebraMap k ↥(modularFunctionFieldC k N) (red (u : A)))
    (hres₂ : (R.residue₂ ⟨t, ht₂⟩ : ↥(modularFunctionFieldC k N)) = 1)
    (g : ↥(modularFunctionFieldBar (N * q)))
    (E : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)))
    (hg₁ : t * g ∈ R.R₁.integers) (hg₂ : t * g ∈ R.R₂.integers) (n₁ n₂ : ℕ) (l₁ l₂ : k)
    (hgV : 0 < V.ord g)
    (hpol : ∀ V' : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)),
      V'.ord g < 0 → P.IsStrictFst V' ∨ P.IsStrictSnd V')
    (hEshape : ∀ V' : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)),
      E V' = ((arithmeticGalois (L := AlgebraicClosure ℚ) (modularFunctionFieldFull (N * q)) σ
          • (Finsupp.single V (1 : ℤ))
        - Finsupp.single V 1 : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)))) V' + max (V'.ord g) 0)
    (hE0 : ∀ V', 0 ≤ E V')
    (hEsupp : ∀ V' ∈ E.support, P.IsStrictFst V' ∨ P.IsStrictSnd V' ∨
      (P.reduceFst V' = P.reduceFst V ∧ ¬ P.IsStrictFst V' ∧ ¬ P.IsStrictSnd V'))
    (hEc : ∀ V' ∈ E.support, ¬ IsCuspidal P V' ∧ ¬ IsCuspidal' P V')
    (htordE : ∀ V' : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)),
      (P.reduceFst V' = P.reduceFst V ∧ ¬ P.IsStrictFst V' ∧ ¬ P.IsStrictSnd V') → V'.ord (t * g) = E V')
    (hl₁ : l₁ ≠ 0) (hl₂ : l₂ ≠ 0)
    (hn : ((n₁ : ℤ) + n₂) = Finsupp.mapDomain P.reduceFst E (P.reduceFst V))
    (htw₁ : (P.reduceFst V).HasValue (π (P.reduceFst V) ^ (-(n₁ : ℤ))
      * (R.residue₁ ⟨t * g, hg₁⟩ : ↥(modularFunctionFieldC k N))) l₁)
    (htw₂ : (arithFrobC q k N • P.reduceFst V).HasValue
      ((arithFrobC q k N • π (P.reduceFst V)) ^ (-(n₂ : ℤ))
        * (R.residue₂ ⟨t * g, hg₂⟩ : ↥(modularFunctionFieldC k N))) l₂) :
    ∃ (D : ↥(Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar (N * q)))))
      (_ : P.IsGoodDiv (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))))
      (hadm : P.glueData (nodePairsOfPlaces (arithFrobC q k N) W)
          (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)))
        ∈ GluingData.admissible (nodePairsOfPlaces (arithFrobC q k N) W)),
      Pic0.mk D = Pic0.mk ⟨arithmeticGalois (L := AlgebraicClosure ℚ) (modularFunctionFieldFull (N * q)) σ
          • (Finsupp.single V (1 : ℤ))
        - Finsupp.single V 1, hdeg⟩ := by
  exact InertialDisplacement.goodRep_of_envelope hqN R hR W hW hRL hO π hπ σ hσ V hV hdeg t ht₁ ht₂ u hres₁ hres₂ g E
    hg₁ hg₂ n₁ n₂ l₁ l₂ hgV hpol hEshape hE0 hEsupp hEc htordE hl₁ hl₂ hn htw₁ htw₂

set_option maxHeartbeats 3200000 in

private theorem main
    (N q : ℕ) [NeZero N] (hq : q.Prime) (hqN : ¬ q ∣ N)
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
      (R : ProlongationTuple P) (hR : R.IsModel) (hRL : R.RegularityLaw W) (hO : R.OrderLawFixed),
        ∀ σ ∈ A.inertiaSubgroupIn ℚ, ∀ (V : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))),
          ¬ P.IsStrictFst V → ¬ P.IsStrictSnd V → P.reduceFst V ∈ W →
          ∀ (hdeg : arithmeticGalois (modularFunctionFieldFull (N * q)) σ • (Finsupp.single V (1 : ℤ))
              - Finsupp.single V 1
              ∈ Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar (N * q)))),
            ∃ (D : ↥(Divisor.degZero (K := AlgebraicClosure ℚ)
                (F := ↥(modularFunctionFieldBar (N * q)))))
              (_ : P.IsGoodDiv (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))))
              (hadm : P.glueData (nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W)
                  (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)))
                ∈ GluingData.admissible
                    (nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W)),
              Pic0.mk D = Pic0.mk ⟨arithmeticGalois (modularFunctionFieldFull (N * q)) σ • (Finsupp.single V (1 : ℤ))
                - Finsupp.single V 1, hdeg⟩ := by
  intro W hW data hKr hα hβ P R hR hRL hO σ hσ V hV₁ hV₂ hVW hdeg
  classical
  haveI : NeZero q := ⟨hq.ne_zero⟩
  haveI : Fact q.Prime := ⟨hq⟩
  haveI : CharP (ResidueField A) q := ValuationSubring.charP_residueField_of_liesOverPrime_def hq hA
  letI := instDecidableEqResidueFieldSemistable A
  letI := instAlgebraResidueFieldModularFunctionFieldCSemistable A N
  have hNV : R.NodeValueLaw W := ProlongationTuple.nodeValueLaw_of_regularityLaw P hqN hW R hRL
  obtain ⟨An, hdom, hmod, hσZ, hZ₁, hZ₂, hZ₂0⟩ :=
    exists_annulus_mem_dom_iff_reduceFst_eq_of_mem_ssPlaces R hqN hR W (fun v hv => (hW v).mp hv) hRL hNV hO
      (P.reduceFst V) hVW
  have hker : ∀ c : A, IsLocalRing.residue A c = 0 ↔ c ∈ IsLocalRing.maximalIdeal A :=
    fun c => IsLocalRing.residue_eq_zero_iff c
  obtain ⟨x, u, t, h₁, h₂, -, -, -, -, -, hres₁, hres₂, htord⟩ :=
    ProlongationTuple.exists_tubeEquation_smul_sub_self_of_annulus R hker σ hσ (P.reduceFst V) An hdom hmod
      (hσZ σ hσ) hZ₁ hZ₂ hZ₂0 V ((hdom V).mpr ⟨rfl, hV₁, hV₂⟩)
  obtain ⟨π, hπ⟩ := InertialDisplacement.exists_unif W
  obtain ⟨g, E, hg₁, hg₂, n₁, n₂, l₁, l₂, hgV, hpol, hEshape, hE0, hEsupp, hEc, htordE, hl₁, hl₂, hn, htw₁, htw₂⟩ :=
    exists_envelope_localEquation_smul_single_sub_single N q hq hqN A hA W hW data hKr hα hβ P R hR hRL hO π hπ
      (P.reduceFst V) hVW σ hσ V ⟨rfl, hV₁, hV₂⟩ t h₁ h₂ u hres₁ hres₂ htord
  exact InertialDisplacement.glue hqN R hR W hW hRL hO π hπ σ hσ V ⟨hV₁, hV₂, hVW⟩ hdeg t h₁ h₂ u hres₁ hres₂ g E
    hg₁ hg₂ n₁ n₂ l₁ l₂ hgV hpol hEshape hE0 hEsupp hEc htordE hl₁ hl₂ hn htw₁ htw₂

end InertialDisplacement

theorem solution
    (N q : ℕ) [NeZero N] (hq : q.Prime) (hqN : ¬ q ∣ N)
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
      (R : ProlongationTuple P) (hR : R.IsModel) (hRL : R.RegularityLaw W) (hO : R.OrderLawFixed),
        ∀ σ ∈ A.inertiaSubgroupIn ℚ, ∀ (V : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))),
          ¬ P.IsStrictFst V → ¬ P.IsStrictSnd V → P.reduceFst V ∈ W →
          ∀ (hdeg : arithmeticGalois (modularFunctionFieldFull (N * q)) σ • (Finsupp.single V (1 : ℤ))
              - Finsupp.single V 1
              ∈ Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar (N * q)))),
            ∃ (D : ↥(Divisor.degZero (K := AlgebraicClosure ℚ)
                (F := ↥(modularFunctionFieldBar (N * q)))))
              (_ : P.IsGoodDiv (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))))
              (hadm : P.glueData (nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W)
                  (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)))
                ∈ GluingData.admissible
                    (nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W)),
              Pic0.mk D = Pic0.mk ⟨arithmeticGalois (modularFunctionFieldFull (N * q)) σ • (Finsupp.single V (1 : ℤ))
                - Finsupp.single V 1, hdeg⟩ := by
  exact InertialDisplacement.main N q hq hqN A hA

end S_ModularCurve_PlaceSpecialization_exists_goodRep_admissible_smul_single_sub_self_of_isModel
end P2MW
export P2MW.S_ModularCurve_PlaceSpecialization_exists_goodRep_admissible_smul_single_sub_self_of_isModel (solution)
