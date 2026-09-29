-- Prove2me | solution 1 for ModularCurve.PlaceSpecialization.exists_goodRep_toPic0Pair_eq_zero_smul_sub_self_of_isModel
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/52299b9a-da97-51e4-a61e-90fb4720c609

import Definitions.Def_ModularCurve_GlueData
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_ModularCurve_CoeffSemilinearAut
import Definitions.Def_ValuationSubring_ReduceAt
import Definitions.Def_WeierstrassCurve_ReductionMap
import Definitions.Def_ModularCurve_ProlongationTuple
import Definitions.Def_ModularCurve_ProlongationTuple_JumpLaw
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_AlgebraicCurve_ConstantReduction
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_ModularCurve_AtkinLehner
import Definitions.Def_ModularCurve_LaurentCoeff
import Definitions.Def_ModularCurve_LaurentDescent
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_ModularCurve_QAdicPlaceMod
import Theorems.Thm_ModularCurve_isCurveOver_modularFunctionFieldC_of_perfectField
import Theorems.Thm_ModularCurve_PlaceSpecialization_exists_rep_reduce_notMem_of_moving_of_disjoint_of_isModel
import Theorems.Thm_ModularCurve_PlaceSpecialization_exists_goodRep_admissible_smul_single_sub_self_of_isModel
import Theorems.Thm_ModularCurve_PlaceSpecialization_exists_gluedMk_eq_nodeUnit_of_isGoodDiv_of_admissible_of_pic0Mk_eq_smul_single_sub_self_of_isModel
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_jumpLaw_of_isModel_of_oneSidedRegularityLaw
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_oneSidedRegularityLaw_of_isModel_of_not_dvd
import Theorems.Thm_ModularCurve_PlaceSpecialization_exists_isGoodDiv_reduce_notMem_isPrincipal_sub_of_smul_eq
import Theorems.Thm_ModularCurve_PlaceSpecialization_isGoodDiv_and_glueData_smul_sub_self_eq_zero_of_forall_isStrict
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_PlaceSpecialization_exists_goodRep_toPic0Pair_eq_zero_smul_sub_self_of_isModel
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent ModularCurve.B3.instIsElliptic_goodModel WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions"
p2m_attr_erase "instance" "AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.instIsScalarTowerJAdjoin WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.numberField_of_finiteDimensional ModularCurve.instIsElliptic_tateBase GaloisRepAdic.instAddCommGroup GaloisRepAdic.instFree GaloisRepAdic.instFinite GaloisRepAdic.instModule ResidualGaloisRep.instModule ResidualGaloisRep.instModuleFinite ResidualGaloisRep.instAddCommGroup WeierstrassCurve.Affine.Point.instFinite ModularCurve.NodeLocalized.isLocalization_nodeDenominators ModularCurve.NodeLocalized.algebraEvalRange ModularCurve.NodeLocalized.isLocalRing_modularLocalizedAtPoint instTopologicallyFGOfFiniteType AdicCompletion.instIsLocalRingMaximalIdeal ModularCurve.NodeLocalized.isScalarTower_K_fieldOver_bar ModularCurve.NodeLocalized.algebraFieldOverBar ModularCurve.NodeLocalized.algebra_isIntegral_fieldOver_bar ModularCurve.NodeLocalized.isScalarTower_fieldOver_bar_laurent ModularCurve.NodeLocalized.charZero_fieldOver ModularCurve.NodeLocalized.algebraFieldOver ModularCurve.NodeLocalized.charZero_laurentSeries_algClosure AlgebraicCurve.CurveModel.isProper AlgebraicCurve.CurveModel.isIntegral AlgebraicCurve.CurveModel.smooth ModularCurve.IgusaScheme.isOpenImmersion_fInf ModularCurve.IgusaScheme.isOpenImmersion_ιInf ModularCurve.IgusaScheme.fact_jFull_ne_zero ModularCurve.IgusaScheme.isOpenImmersion_ιFin"
p2m_attr_erase "instance" "ModularCurve.IgusaScheme.isOpenImmersion_fFin AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin AlgebraicCurve.CurveModel.chartRing_finitePresentation AlgebraicCurve.GaussReduction.isLocalHom_constToGauss CuspForm.heckeAlgebra.instCommRing CuspForm.heckeAlgebra.instIsMulCommutative CuspForm.heckeAlgebra.instIsAddTorsionFree ModularCurve.CuspSpace.instNonempty ModularCurve.CuspSpace.instSubsingletonOfOne ModularCurve.CuspSpace.instFinite ModularCurve.instAlgebraIntermediateFieldLaurent ModularCurve.instIsScalarTowerKaehlerIntermediateFieldLaurent ModularCurve.instIsScalarTowerIntermediateFieldLaurent ModularCurve.instModuleKaehlerIntermediateFieldLaurent"
p2m_attr_erase "instance" "FLT.Gamma0FundamentalSet.instContinuousConstSMulSpecialLinearGroupFinOfNatNatIntUpperHalfPlane_definitions FLT.HyperbolicMeasure.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatIntUpperHalfPlaneVolume_definitions FLT.HyperbolicMeasure.instIsOpenPosMeasureUpperHalfPlaneVolume_definitions FLT.L2ProductionInstance.isFiniteMeasure_gamma0 FLT.L2ProductionInstance.countable_SL2Z FLT.L2ProductionInstance.countable_quotient FLT.L2ProductionInstance.nontrivial_gamma0L2 HeckeEis.instModuleCoeffH1par HeckeEis.instAddCommGroupCoeffH1par HeckeEis.instFiniteIndexHeckeUpper instFieldLaurentSeriesAlgClosureRat instAlgebraModularFunctionFieldBar ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instAlgebraResidueFieldSubtypeMemValuationSubringGaussBaseResOne ModularCurve.PlaceSpecialization.LevelOneProlongationPair.algGaussBase instAlgebraModularFunctionFieldFullC ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instAlgebraSubtypeMemValuationSubringGaussBaseResOne ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instAlgebraSubtypeMemValuationSubringGaussBaseResTwo instFieldModularFunctionFieldC ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isScalarTower_resOne instFieldLaurentSeries' ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isScalarTower_resTwo instModuleModularFunctionFieldBar ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isLocalHom_resBase₁ instAlgebraModularFunctionFieldC ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isLocalHom_constToGaussBase ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instFieldResOne instFieldModularFunctionFieldBar ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instAlgebraResidueFieldSubtypeMemValuationSubringGaussBaseResTwo ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instFieldResTwo instFieldModularFunctionFieldFullC ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isScalarTower_gaussBase instAlgebraLaurentSeriesAlgClosureRat ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isLocalHom_resBase₂ ModularCurve.PlaceSpecialization.LevelOneProlongationPair.algResidueConst instCommRingModularFunctionFieldBar"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.PlaceSpecialization.LevelOneProlongationPair.mk.sizeOf_spec ModularCurve.PlaceSpecialization.LevelOneProlongationPair.residue₂_apply ModularCurve.PlaceSpecialization.LevelOneProlongationPair.residue₁_apply ModularCurve.PlaceSpecialization.LevelOneProlongationPair.mk.injEq ModularCurve.coe_nodeEquiv_symm_apply ModularCurve.frobNodePair_jOfNode ModularCurve.jOfNode_mk ModularCurve.widthOf_mk ModularCurve.frobNodePairEmb_apply ModularCurve.card_nodePairsOf ModularCurve.frobNodePair_snd ModularCurve.coe_nodeEquiv_apply ModularCurve.frobNodePair_fst"
p2m_attr_erase "simp" "ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one HahnSeries.ramScale_apply ModularCurve.Gamma0Pair.map_toCurve WeierstrassCurve.mapPoint_eq_ratPointMap ModularCurve.Gamma0Pair.map_gen ModularCurve.Gamma0Pair.map_eq_gamma0PairMap ModularCurve.ModuliPoint.map_eq_moduliPointMapRingHom ModularCurve.ModuliPoint.map_mk WeierstrassCurve.mapPointHom_apply WeierstrassCurve.mapPoint_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec"
p2m_attr_erase "simp" "EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply"
p2m_attr_erase "simp" "WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff ModularCurve.ProjectiveLine.map_mk ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ WeierstrassCurve.veluX_empty WeierstrassCurve.vcInvEmbedding_apply ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.veluY_empty WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace"
p2m_attr_erase "simp" "AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄"
p2m_attr_erase "simp" "TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero ModularCurve.cuspCount_one WeierstrassCurve.Universal.halveX_zero WeierstrassCurve.Universal.specialize_X_one WeierstrassCurve.Universal.coeff_halve WeierstrassCurve.Universal.specialize_X_two WeierstrassCurve.Universal.halveCoeff_zero WeierstrassCurve.Universal.specialize_X_four WeierstrassCurve.Universal.coeff_halveX WeierstrassCurve.Universal.specialize_X_three WeierstrassCurve.Universal.specialize_X_zero AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule"
p2m_attr_erase "simp" "AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ ModularCurve.symPoly_zero ModularCurve.frobeniusPullbackGeomLevelUnconditional_single ModularCurve.frobeniusPushforwardGeomLevelUnconditional_single ModularCurve.frobeniusGeomLevelUnconditional_apply_coe AlgebraicCurve.ComponentChart.ofConstantReduction_integers AlgebraicCurve.ComponentChart.mk.sizeOf_spec AlgebraicCurve.ComponentChart.ofConstantReduction_placeMap AlgebraicCurve.ComponentChart.ofConstantReduction_nodes AlgebraicCurve.ComponentChart.mk.injEq AlgebraicCurve.ComponentChart.ofConstantReduction_dom AlgebraicCurve.Annulus.mk.sizeOf_spec AlgebraicCurve.Annulus.mk.injEq ModularCurve.FinitePlaceLift.traceHom_coe ModularCurve.FinitePlaceLift.mk.injEq ModularCurve.FinitePlaceLift.mk.sizeOf_spec ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁"
p2m_attr_erase "simp" "ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst ModularCurve.CharPModel.FibreModel.mk.injEq ModularCurve.CharPModel.FibreModel.mk.sizeOf_spec ModularCurve.PlaceSpecialization.ProlongationTuple.NodeCoordinates.mk.sizeOf_spec ModularCurve.PlaceSpecialization.ProlongationTuple.coe_nodeConst ModularCurve.PlaceSpecialization.ProlongationTuple.NodeCoordinates.mk.injEq ModularCurve.PlaceSpecialization.ProlongationTuple.nodeResidue₂_apply ModularCurve.PlaceSpecialization.ProlongationTuple.nodeResidue₁_apply ModularCurve.crossingCoord_apply GaloisRepAdic.mk.injEq GaloisRepAdic.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.injEq ResidualGaloisRep.mk.sizeOf_spec ResidualGaloisRep.mk.injEq ResidualGaloisRep.Equiv.mk.sizeOf_spec ResidualGaloisRep.Equiv.mk.injEq AlgebraicCurve.Pic.baseChange_mk AlgebraicCurve.Place.forgetConstants_toValuationSubring AlgebraicCurve.Place.constantFieldEquiv_symm_apply AlgebraicCurve.Place.ord_forgetConstants AlgebraicCurve.Place.extendConstants_toValuationSubring AlgebraicCurve.Place.constantFieldEquiv_apply_toValuationSubring AlgebraicCurve.Place.mem_fiberConstants AlgebraicCurve.Place.restrictConstants_toValuationSubring ModularCurve.NodeLocalized.coe_modularEvalAt AdicCompletion.evalₐ_mapₐ AdicCompletion.mapAlgEquivOfBijective_apply AdicCompletion.levelMapₐ_mk AdicCompletion.mapₐ_of AdicCompletion.mapAlgEquiv_symm_apply AdicCompletion.mapAlgEquiv_apply AdicCompletion.evalₐ_ofLevelwiseEquiv AdicCompletion.evalₐ_levelwiseHom AdicCompletion.localizationEquiv_of AdicCompletion.evalₐ_ofLevelwiseEquiv_symm Localization.AtPrime.quotientPowEquiv_mk ModularCurve.LambdaModularPolynomialData.mk.sizeOf_spec"
p2m_attr_erase "simp" "ModularCurve.LambdaModularPolynomialData.mk.injEq AdicCompletion.transportOf_of AdicCompletion.selfCompletion_smul_of AdicCompletion.tensorRingEquiv_tmul AdicCompletion.completionOfAlgHom_apply AdicCompletion.completionBaseChangeHom_of AdicCompletion.tensorRingHom_tmul AdicCompletion.stabilizerToCompletionAut_of GoodReductionJacobian.RelativePic0Designation.mk.sizeOf_spec GoodReductionJacobian.AvatarSchemeBridge.mk.injEq MilneJVScheme.JacobianSchemeData.mk.injEq GoodReductionJacobian.AvatarSchemeBridge.mk.sizeOf_spec MilneJVScheme.JacobianSchemeData.mk.sizeOf_spec GoodReductionJacobian.RelativePic0Designation.mk.injEq NeronModelInfra.specGenericFibreInclusion_eq NeronModelInfra.genericFibreRestrict_coe_comp_snd NeronModelInfra.genericFibreRestrict_coe_comp_fst GoodReductionJacobian.schemeHomOverComp_coe NeronModelInfra.schemeHomOverEquivOverHom_apply GoodReductionJacobian.RelativeGroupLaw.mk.sizeOf_spec NeronModelInfra.schemeHomOverEquivOverHom_symm_apply NeronModelInfra.overHomToSchemeHomOver_coe GoodReductionJacobian.RelativeGroupLaw.mk.injEq NeronModelInfra.overHomToSchemeHomOver_schemeHomOverToOverHom NeronModelInfra.schemeHomOverToOverHom_left NeronModelInfra.schemeHomOverToOverHom_overHomToSchemeHomOver NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe AlgebraicCurve.CurveModel.mk.injEq AlgebraicCurve.CurveModel.mk.sizeOf_spec ModularCurve.IgusaScheme.ιInf_igusaTo_assoc ModularCurve.IgusaScheme.coe_jFull ModularCurve.IgusaScheme.coe_jInvChartInf ModularCurve.IgusaScheme.coe_jChartFin ModularCurve.IgusaScheme.ιFin_igusaTo"
p2m_attr_erase "simp" "ModularCurve.IgusaScheme.ιInf_igusaTo ModularCurve.IgusaScheme.ιFin_igusaTo_assoc AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces AlgebraicCurve.GaussReduction.constToGauss_coe AlgebraicCurve.ComponentChart.ofConstantReductionNodes_dom AlgebraicCurve.ComponentChart.ofConstantReductionNodes_placeMap AlgebraicCurve.ComponentChart.ofConstantReductionNodes_nodes AlgebraicCurve.ComponentChart.ofConstantReductionNodes_residue AlgebraicCurve.ComponentChart.ofConstantReductionNodes_integers ModularCurve.dualHeckeRep_apply_apply ModularCurve.coe_segmentPath ModularCurve.cuspHeckeAeval_heckeGen ModularCurve.coe_periodLatticeRestrict_apply CuspForm.heckeAlgebra.coe_U CuspForm.heckeAlgebra.coe_T ModularForm.coe_heckeTLin_apply CuspForm.coe_heckeULin_apply CuspForm.coe_heckeTLin_apply ModularForm.coe_heckeULin_apply ModularCurve.ComplexPlaceDictionary.mk.injEq ModularCurve.ComplexPlaceDictionary.mk.sizeOf_spec ModularCurve.Period.IsEquivariantPrimitive.periodHom_apply ModularCurve.Period.IsEquivariantPrimitive.period_one ModularCurve.CuspSpace.cuspDenomAux_infty ModularCurve.CuspSpace.cuspDenomAux_coe ModularCurve.CuspSpace.cuspDenom_mk_zero ModularCurve.CuspSpace.cuspDenom_mk_infty ModularCurve.mapGL_apply_coe ModularCurve.ratPoint_one_zero ModularCurve.ratPoint_zero_right"
p2m_attr_erase "simp" "ModularCurve.CuspSpace.fromCoset_mk ModularCurve.CuspSpace.cuspDenom_mk ModularCurve.ratPoint_zero_one ModularCurve.qEulerFun_coeff ModularCurve.diffQExp_D ModularCurve.qEulerOn_apply ModularCurve.qEuler_coeff FLT.TruncatedDomainPartition.unipotentDiagonalSum_zero HeckeEis.coeffCoboundaryMap_apply HeckeEis.heckeConjMat_apply_one_one HeckeEis.coe_heckeConjSL HeckeEis.mem_heckeUpperSL HeckeEis.resHom_apply HeckeEis.heckeConjMat_apply_zero_one HeckeEis.coe_transferAux HeckeEis.coe_heckeConj HeckeEis.alphaMat_apply_one_one HeckeEis.heckeConjMat_apply_one_zero HeckeEis.alphaMat_apply_zero_one HeckeEis.pullbackHom_apply HeckeEis.alphaMat_apply_one_zero HeckeEis.alphaMat_apply_zero_zero HeckeEis.heckeConjMat_apply_zero_zero ModularCurve.coe_levelPolynomialEquiv_apply ModularCurve.coe_levelBaseRingDescent_apply ModularCurve.levelConst_apply ModularCurve.PlaceSpecialization.LevelOneProlongationPair.coe_gaussOrderToIntegers₂ ModularCurve.PlaceSpecialization.LevelOneProlongationPair.coe_gaussOrderToIntegers₁ ModularCurve.PlaceSpecialization.LevelOneProlongationPair.coe_toIntegers₁ ModularCurve.PlaceSpecialization.LevelOneProlongationPair.coe_constToGaussBase ModularCurve.PlaceSpecialization.LevelOneProlongationPair.coe_toIntegers₂"
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000
set_option Elab.async false
set_option autoImplicit false

p2m_open "AlgebraicCurve IsLocalRing ModularCurve P2MW.S_ModularCurve_PlaceSpecialization_exists_goodRep_toPic0Pair_eq_zero_smul_sub_self_of_isModel.ModularCurve"

section HelpersA
variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
  {k : Type*} [Field k] [CharP k q] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
  {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
  (P : PlaceSpecialization A q N data hKr k red hα hβ)

namespace ModularCurve p2m_export "ModularCurve" "PlaceSpecialization.fstDiv PlaceSpecialization.sndDiv PrimeToTorsion instDecidableEqResidueFieldSemistable instAlgebraResidueFieldModularFunctionFieldCSemistable arithmeticGalois galois_smul_pic0_def modularFunctionFieldBar JZero ModularPolynomialData modularFunctionFieldFull jqModC modularFunctionFieldC jqModC_mem PlaceSpecialization HeckeAlphaBarIntegral HeckeBetaBarIntegral deg_eq_one_modularFunctionFieldC frobeniusGeomLevel frobeniusGeomLevel_jq frobOnPlacesGeomLevel ord_frobOnPlaces_of_pow_eq KroneckerCongruence nodePairsOfPlaces ssPlaces jModElt_notMem_qIntegersBar qInftyPlaceMod jqModC_ne_zero_def qIntegersBar arithFrobC PlaceSpecialization.ProlongationTuple isCurveOver_modularFunctionFieldC_of_perfectField PlaceSpecialization.exists_rep_reduce_notMem_of_moving_of_disjoint_of_isModel PlaceSpecialization.exists_goodRep_admissible_smul_single_sub_self_of_isModel PlaceSpecialization.exists_gluedMk_eq_nodeUnit_of_isGoodDiv_of_admissible_of_pic0Mk_eq_smul_single_sub_self_of_isModel PlaceSpecialization.ProlongationTuple.jumpLaw_of_isModel_of_oneSidedRegularityLaw PlaceSpecialization.ProlongationTuple.oneSidedRegularityLaw_of_isModel_of_not_dvd PlaceSpecialization.exists_isGoodDiv_reduce_notMem_isPrincipal_sub_of_smul_eq PlaceSpecialization.isGoodDiv_and_glueData_smul_sub_self_eq_zero_of_forall_isStrict" namespace PlaceSpecialization p2m_export "ModularCurve.PlaceSpecialization" "reduceFst reduceSnd IsStrictFst IsStrictSnd IsGoodDiv fstDiv sndDiv glueData glueData_zero isGoodDiv_zero mk d1 casesOn ProlongationTuple exists_rep_reduce_notMem_of_moving_of_disjoint_of_isModel exists_goodRep_admissible_smul_single_sub_self_of_isModel exists_gluedMk_eq_nodeUnit_of_isGoodDiv_of_admissible_of_pic0Mk_eq_smul_single_sub_self_of_isModel ProlongationTuple.jumpLaw_of_isModel_of_oneSidedRegularityLaw ProlongationTuple.oneSidedRegularityLaw_of_isModel_of_not_dvd exists_isGoodDiv_reduce_notMem_isPrincipal_sub_of_smul_eq isGoodDiv_and_glueData_smul_sub_self_eq_zero_of_forall_isStrict" end ModularCurve.PlaceSpecialization
namespace ModularCurve.PlaceSpecialization
p2m_open_scoped "ModularCurve ModularCurve.PlaceSpecialization" in

private theorem _root_.ModularCurve.PlaceSpecialization.isGoodDiv_add
    (D D' : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)))
    (hD : P.IsGoodDiv D) (hD' : P.IsGoodDiv D') : P.IsGoodDiv (D + D') := by
  classical
  intro W hW
  rcases Finset.mem_union.mp (Finsupp.support_add hW) with h | h
  · exact hD W h
  · exact hD' W h

end ModularCurve.PlaceSpecialization
p2m_export "" "ModularCurve.PlaceSpecialization.isGoodDiv_add"
namespace ModularCurve.PlaceSpecialization
p2m_open_scoped "ModularCurve ModularCurve.PlaceSpecialization" in

private theorem _root_.ModularCurve.PlaceSpecialization.glueData_add
    (S : Finset (Place k (modularFunctionFieldC k N) × Place k (modularFunctionFieldC k N)))
    (D D' : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) :
    P.glueData S (D + D') = P.glueData S D + P.glueData S D' := by
  classical
  have hf : P.fstDiv (D + D') = P.fstDiv D + P.fstDiv D' := by
    unfold PlaceSpecialization.fstDiv
    exact Finsupp.filter_add
  have hs : P.sndDiv (D + D') = P.sndDiv D + P.sndDiv D' := by
    unfold PlaceSpecialization.sndDiv
    exact Finsupp.filter_add
  show (Finsupp.mapDomain P.reduceFst (P.fstDiv (D + D')),
      Finsupp.mapDomain P.reduceSnd (P.sndDiv (D + D')), (0 : ↥S → Additive kˣ))
    = (Finsupp.mapDomain P.reduceFst (P.fstDiv D), Finsupp.mapDomain P.reduceSnd (P.sndDiv D),
        (0 : ↥S → Additive kˣ))
      + (Finsupp.mapDomain P.reduceFst (P.fstDiv D'), Finsupp.mapDomain P.reduceSnd (P.sndDiv D'),
        (0 : ↥S → Additive kˣ))
  rw [hf, hs, Finsupp.mapDomain_add, Finsupp.mapDomain_add, Prod.mk_add_mk, Prod.mk_add_mk, add_zero]

end ModularCurve.PlaceSpecialization
p2m_export "" "ModularCurve.PlaceSpecialization.glueData_add"
end HelpersA

private theorem H2Recon.nu_add_aux {k F : Type*} [Field k] [Field F] [Algebra k F]
    (S : Finset (Place k F × Place k F)) (a b c : GluingData k F S)
    (ha : a ∈ GluingData.admissible S) (hb : b ∈ GluingData.admissible S)
    (hc : c ∈ GluingData.admissible S) (h : c = a + b)
    (h1 : GluedPic0.toPic0Pair S (GluedPic0.mk S ⟨a, ha⟩) = 0)
    (h2 : GluedPic0.toPic0Pair S (GluedPic0.mk S ⟨b, hb⟩) = 0) :
    GluedPic0.toPic0Pair S (GluedPic0.mk S ⟨c, hc⟩) = 0 := by
  subst h
  have e : (⟨a + b, hc⟩ : ↥(GluingData.admissible S)) = ⟨a, ha⟩ + ⟨b, hb⟩ := rfl
  rw [e, map_add, map_add, h1, h2, add_zero]

private theorem H2Recon.A_toricGood_add
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
      (P : PlaceSpecialization A q N data hKr (ResidueField A) (IsLocalRing.residue A) hα hβ),
        ∀ y y' : JZero (N * q),
          (            ∃ (D : ↥(Divisor.degZero (K := AlgebraicClosure ℚ)
                (F := ↥(modularFunctionFieldBar (N * q)))))
              (_ : P.IsGoodDiv (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))))
              (hadm : P.glueData (nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W)
                  (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)))
                ∈ GluingData.admissible
                    (nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W)),
              Pic0.mk D = y ∧
                GluedPic0.toPic0Pair (nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W)
                  (GluedPic0.mk (nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W)
                    ⟨P.glueData (nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W)
                      (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))), hadm⟩)
                  = 0) →
          (            ∃ (D' : ↥(Divisor.degZero (K := AlgebraicClosure ℚ)
                (F := ↥(modularFunctionFieldBar (N * q)))))
              (_ : P.IsGoodDiv (D' : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))))
              (hadm' : P.glueData (nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W)
                  (D' : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)))
                ∈ GluingData.admissible
                    (nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W)),
              Pic0.mk D' = y' ∧
                GluedPic0.toPic0Pair (nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W)
                  (GluedPic0.mk (nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W)
                    ⟨P.glueData (nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W)
                      (D' : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))), hadm'⟩)
                  = 0) →
            ∃ (D : ↥(Divisor.degZero (K := AlgebraicClosure ℚ)
                (F := ↥(modularFunctionFieldBar (N * q)))))
              (_ : P.IsGoodDiv (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))))
              (hadm : P.glueData (nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W)
                  (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)))
                ∈ GluingData.admissible
                    (nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W)),
              Pic0.mk D = y + y' ∧
                GluedPic0.toPic0Pair (nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W)
                  (GluedPic0.mk (nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W)
                    ⟨P.glueData (nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W)
                      (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))), hadm⟩)
                  = 0 := by
  intro W hW data hKr hα hβ P y y' hy hy'
  haveI : NeZero q := ⟨hq.ne_zero⟩
  haveI : Fact q.Prime := ⟨hq⟩
  haveI : CharP (ResidueField A) q := ValuationSubring.charP_residueField_of_liesOverPrime_def hq hA
  letI := instDecidableEqResidueFieldSemistable A
  letI := instAlgebraResidueFieldModularFunctionFieldCSemistable A N
  have _ := hqN
  have _ := hW

  refine hy.elim fun D hD => ?_
  refine hD.elim fun hDg hD₂ => ?_
  refine hD₂.elim fun hDadm hD₃ => ?_
  refine hy'.elim fun D' hD' => ?_
  refine hD'.elim fun hD'g hD'₂ => ?_
  refine hD'₂.elim fun hD'adm hD'₃ => ?_

  have hcoe : ((D + D' : ↥(Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar (N * q))))) : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)))
      = (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) + (D' : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) :=
    AddSubgroup.coe_add _ D D'
  have hglue : P.glueData (nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W) ((D + D' : ↥(Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar (N * q))))) : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)))
      = P.glueData (nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W) (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) + P.glueData (nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W) (D' : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) := by
    rw [hcoe]
    exact P.glueData_add (nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W) _ _
  have hgood : P.IsGoodDiv ((D + D' : ↥(Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar (N * q))))) : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) := by
    rw [hcoe]
    exact P.isGoodDiv_add _ _ hDg hD'g
  have hadd : P.glueData (nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W) ((D + D' : ↥(Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar (N * q))))) : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)))
      ∈ GluingData.admissible (nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W) := by
    rw [hglue]
    exact add_mem hDadm hD'adm
  have hmk : Pic0.mk (D + D') = y + y' := by
    rw [Pic0.mk_add, hD₃.1, hD'₃.1]
  have hν : GluedPic0.toPic0Pair (nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W)
      (GluedPic0.mk (nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W)
        ⟨P.glueData (nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W) ((D + D' : ↥(Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar (N * q))))) : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))), hadd⟩) = 0 :=
    H2Recon.nu_add_aux (nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W) _ _ _ hDadm hD'adm hadd hglue hD₃.2 hD'₃.2
  exact ⟨D + D', hgood, hadd, hmk, hν⟩

private theorem H2Recon.nu_zero_aux {k F : Type*} [Field k] [Field F] [Algebra k F]
    (S : Finset (Place k F × Place k F)) (a : GluingData k F S) (ha : a ∈ GluingData.admissible S)
    (h : a = 0) : GluedPic0.toPic0Pair S (GluedPic0.mk S ⟨a, ha⟩) = 0 := by
  subst h
  have e : (⟨0, ha⟩ : ↥(GluingData.admissible S)) = 0 := rfl
  rw [e, map_zero, map_zero]

private theorem H2Recon.M1b'_exists_rep_of_move_engine_of_disjoint
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
      (R : ModularCurve.PlaceSpecialization.ProlongationTuple P) (hR : R.IsModel) (hRL : R.RegularityLaw W)
      (hO : R.OrderLawFixed),
        (∀ T : Finset (Place (ResidueField A) ↥(modularFunctionFieldC (ResidueField A) N)),
          ∃ E₀ C₀ : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)),
            (∀ V, 0 ≤ E₀ V) ∧ P.IsGoodDiv E₀ ∧
              (∀ V ∈ E₀.support, P.reduceFst V ∉ T ∧ P.reduceSnd V ∉ T) ∧
                0 < Divisor.degree E₀ ∧ (∀ V, 0 ≤ C₀ V) ∧
                  (∀ σ ∈ A.inertiaSubgroupIn ℚ,
                    arithmeticGalois (modularFunctionFieldFull (N * q)) σ • C₀ = C₀) ∧
                    0 < Divisor.degree C₀ ∧ Divisor.IsPrincipal (E₀ - C₀)) →
          ∀ (T : Finset (Place (ResidueField A) ↥(modularFunctionFieldC (ResidueField A) N))),
          (∀ w ∈ T, w ∉ W) →
          ∀ x : JZero (N * q),
            ∃ (E : ↥(Divisor.degZero (K := AlgebraicClosure ℚ)
                  (F := ↥(modularFunctionFieldBar (N * q))))),
              Pic0.mk E = x ∧
                ∀ V ∈ (E : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))).support,
                  P.reduceFst V ∉ T ∧ P.reduceSnd V ∉ T :=
  ModularCurve.PlaceSpecialization.exists_rep_reduce_notMem_of_moving_of_disjoint_of_isModel N q hq hqN A hA

section GrainAdditive
variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
  {k : Type*} [Field k] [CharP k q] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
  {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
  (P : PlaceSpecialization A q N data hKr k red hα hβ)
  (S : Finset (Place k (modularFunctionFieldC k N) × Place k (modularFunctionFieldC k N)))

namespace ModularCurve.PlaceSpecialization
p2m_open_scoped "ModularCurve ModularCurve.PlaceSpecialization" in
private theorem _root_.ModularCurve.PlaceSpecialization.isGoodDiv_addGr {D D' : Divisor (AlgebraicClosure ℚ)
    (modularFunctionFieldBar (N * q))} (hD : P.IsGoodDiv D) (hD' : P.IsGoodDiv D') :
    P.IsGoodDiv (D + D') := by
  classical
  intro W hW
  rcases Finset.mem_union.mp (Finsupp.support_add hW) with h | h
  · exact hD W h
  · exact hD' W h

end ModularCurve.PlaceSpecialization
p2m_export "" "ModularCurve.PlaceSpecialization.isGoodDiv_addGr"
namespace ModularCurve.PlaceSpecialization
p2m_open_scoped "ModularCurve ModularCurve.PlaceSpecialization" in
private theorem _root_.ModularCurve.PlaceSpecialization.isGoodDiv_negGr {D : Divisor (AlgebraicClosure ℚ)
    (modularFunctionFieldBar (N * q))} (hD : P.IsGoodDiv D) : P.IsGoodDiv (-D) := by
  intro W hW
  exact hD W (Finsupp.support_neg D ▸ hW)

end ModularCurve.PlaceSpecialization
p2m_export "" "ModularCurve.PlaceSpecialization.isGoodDiv_negGr"
namespace ModularCurve.PlaceSpecialization
p2m_open_scoped "ModularCurve ModularCurve.PlaceSpecialization" in
private theorem _root_.ModularCurve.PlaceSpecialization.glueData_addGr
    (D D' : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) :
    P.glueData S (D + D') = P.glueData S D + P.glueData S D' := by
  classical
  show (_, _, (0 : ↥S → Additive kˣ)) = (_, _, (0 : ↥S → Additive kˣ)) + (_, _, _)
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · unfold PlaceSpecialization.fstDiv
    rw [Prod.fst_add, Finsupp.filter_add, Finsupp.mapDomain_add]
  · unfold PlaceSpecialization.sndDiv
    rw [Prod.snd_add, Prod.fst_add, Finsupp.filter_add, Finsupp.mapDomain_add]
  · simp

end ModularCurve.PlaceSpecialization
p2m_export "" "ModularCurve.PlaceSpecialization.glueData_addGr"
namespace ModularCurve.PlaceSpecialization
p2m_open_scoped "ModularCurve ModularCurve.PlaceSpecialization" in
private theorem _root_.ModularCurve.PlaceSpecialization.glueData_negGr
    (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) :
    P.glueData S (-D) = -(P.glueData S D) := by
  have h := P.glueData_addGr S (-D) D
  rw [neg_add_cancel, P.glueData_zero] at h
  exact (neg_eq_of_add_eq_zero_left h.symm).symm

end ModularCurve.PlaceSpecialization
p2m_export "" "ModularCurve.PlaceSpecialization.glueData_negGr"

private def H2Recon.TG (x : JZero (N * q)) : Prop :=
  ∃ (D : ↥(Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar (N * q)))))
    (_ : P.IsGoodDiv (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))))
    (hadm : P.glueData S (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) ∈ GluingData.admissible S),
    Pic0.mk D = x ∧ ∃ χ : ↥S → Additive kˣ,
      GluedPic0.mk S ⟨P.glueData S (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))), hadm⟩ = GluedPic0.nodeUnit S χ

private theorem H2Recon.TG_zero : H2Recon.TG P S 0 := by
  have ha : P.glueData S ((0 : ↥(Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar (N * q))))) : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) ∈ GluingData.admissible S := by
    rw [ZeroMemClass.coe_zero, P.glueData_zero]; exact zero_mem _
  refine ⟨0, P.isGoodDiv_zero, ha, rfl, 0, ?_⟩
  have e : (⟨P.glueData S ((0 : ↥(Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar (N * q))))) : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))), ha⟩ : ↥(GluingData.admissible S)) = 0 :=
    Subtype.ext (show P.glueData S (0 : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) = 0 from P.glueData_zero S)
  rw [e, map_zero, map_zero]

private theorem H2Recon.TG_add {x y : JZero (N * q)} (hx : H2Recon.TG P S x) (hy : H2Recon.TG P S y) :
    H2Recon.TG P S (x + y) := by
  obtain ⟨D₁, hg₁, ha₁, hc₁, χ₁, hχ₁⟩ := hx
  obtain ⟨D₂, hg₂, ha₂, hc₂, χ₂, hχ₂⟩ := hy
  have ha : P.glueData S ((D₁ + D₂ : ↥(Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar (N * q))))) : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) ∈ GluingData.admissible S := by
    rw [AddSubgroup.coe_add, P.glueData_addGr]; exact add_mem ha₁ ha₂
  refine ⟨D₁ + D₂, P.isGoodDiv_addGr hg₁ hg₂, ha, ?_, χ₁ + χ₂, ?_⟩
  · rw [← hc₁, ← hc₂]; rfl
  · have e : (⟨P.glueData S ((D₁ + D₂ : ↥(Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar (N * q))))) : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))), ha⟩ : ↥(GluingData.admissible S))
        = ⟨P.glueData S (D₁ : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))), ha₁⟩ + ⟨P.glueData S (D₂ : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))), ha₂⟩ :=
      Subtype.ext (show P.glueData S ((D₁ : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) + (D₂ : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))))
        = P.glueData S (D₁ : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) + P.glueData S (D₂ : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) from P.glueData_addGr S _ _)
    rw [e, map_add, map_add, hχ₁, hχ₂]

private theorem H2Recon.TG_neg {x : JZero (N * q)} (hx : H2Recon.TG P S x) : H2Recon.TG P S (-x) := by
  obtain ⟨D₁, hg₁, ha₁, hc₁, χ₁, hχ₁⟩ := hx
  have ha : P.glueData S ((-D₁ : ↥(Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar (N * q))))) : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) ∈ GluingData.admissible S := by
    rw [AddSubgroup.coe_neg, P.glueData_negGr]; exact neg_mem ha₁
  refine ⟨-D₁, P.isGoodDiv_negGr hg₁, ha, ?_, -χ₁, ?_⟩
  · rw [← hc₁]; rfl
  · have e : (⟨P.glueData S ((-D₁ : ↥(Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar (N * q))))) : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))), ha⟩ : ↥(GluingData.admissible S))
        = -⟨P.glueData S (D₁ : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))), ha₁⟩ :=
      Subtype.ext (show P.glueData S (-(D₁ : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)))) = -P.glueData S (D₁ : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) from P.glueData_negGr S _)
    rw [e, map_neg, map_neg, hχ₁]

private theorem H2Recon.TG_zsmul {x : JZero (N * q)} (hx : H2Recon.TG P S x) (n : ℤ) : H2Recon.TG P S (n • x) := by
  induction n with
  | zero => rw [zero_zsmul]; exact H2Recon.TG_zero P S
  | succ i ih => rw [add_one_zsmul]; exact H2Recon.TG_add P S ih hx
  | pred i ih => rw [sub_one_zsmul]; exact H2Recon.TG_add P S ih (H2Recon.TG_neg P S hx)

omit [Fact (Nat.Prime q)] [NeZero N] P S in
private theorem H2Recon.smul_sub_self_mem_degZero
    (g : SemilinearAut (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) (E : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) :
    g • E - E ∈ Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar (N * q))) := by
  rw [Divisor.mem_degZero, map_sub, SemilinearAut.degree_smul, sub_self]

private noncomputable def H2Recon.dispHom
    (g : SemilinearAut (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) :
    Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)) →+ JZero (N * q) where
  toFun E := Pic0.mk ⟨g • E - E, H2Recon.smul_sub_self_mem_degZero g E⟩
  map_zero' := by
    have e : (⟨g • (0 : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) - 0, H2Recon.smul_sub_self_mem_degZero g 0⟩ : ↥(Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar (N * q))))) = 0 :=
      Subtype.ext (show g • (0 : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) - 0 = 0 by rw [smul_zero, sub_zero])
    show Pic0.mk _ = 0
    rw [e]; rfl
  map_add' E E' := by
    show Pic0.mk _ = Pic0.mk _ + Pic0.mk _
    rw [← Pic0.mk_add]
    exact congrArg Pic0.mk (Subtype.ext (show g • (E + E') - (E + E') = (g • E - E) + (g • E' - E') by
      rw [smul_add]; abel))

private theorem H2Recon.TG_dispHom_of_forall
    (g : SemilinearAut (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)))
    (nodal : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) → Prop)
    (hpt : ∀ V, nodal V → H2Recon.TG P S (H2Recon.dispHom g (Finsupp.single V 1)))
    (E : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) (hE : ∀ V ∈ E.support, nodal V) :
    H2Recon.TG P S (H2Recon.dispHom g E) := by
  classical
  induction E using Finsupp.induction with
  | zero => rw [map_zero]; exact H2Recon.TG_zero P S
  | single_add V n E' hV hn ih =>
    have hV0 : E' V = 0 := Classical.not_not.mp (fun h => hV (Finsupp.mem_support_iff.mpr h))
    have hVmem : V ∈ (Finsupp.single V n + E').support := by
      rw [Finsupp.mem_support_iff, Finsupp.add_apply, Finsupp.single_eq_same, hV0, add_zero]; exact hn
    have hE' : ∀ V' ∈ E'.support, nodal V' := by
      intro V' hV'
      apply hE V'
      rw [Finsupp.mem_support_iff, Finsupp.add_apply, Finsupp.single_apply,
        if_neg (fun h : V = V' => hV (by rw [h]; exact hV')), zero_add]
      exact Finsupp.mem_support_iff.mp hV'
    have hs : Finsupp.single V n = n • Finsupp.single V (1 : ℤ) := by
      rw [Finsupp.smul_single', mul_one]
    have h1 : H2Recon.TG P S (H2Recon.dispHom g (Finsupp.single V n)) := by
      rw [hs, map_zsmul]; exact H2Recon.TG_zsmul P S (hpt V (hE V hVmem)) n
    rw [map_add]; exact H2Recon.TG_add P S h1 (ih hE')

private theorem H2Recon.exists_goodRep_nodeUnit_of_forall_single
    (g : SemilinearAut (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)))
    (nodal : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) → Prop)
    (hpt : ∀ V, nodal V →
      ∀ (hdegV : g • (Finsupp.single V (1 : ℤ)) - Finsupp.single V 1
          ∈ Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar (N * q)))),
        ∃ (D : ↥(Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar (N * q)))))
          (_ : P.IsGoodDiv (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))))
          (hadm : P.glueData S (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) ∈ GluingData.admissible S),
          Pic0.mk D = Pic0.mk ⟨g • (Finsupp.single V (1 : ℤ)) - Finsupp.single V 1, hdegV⟩ ∧
            ∃ χ : ↥S → Additive kˣ,
              GluedPic0.mk S ⟨P.glueData S (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))), hadm⟩ = GluedPic0.nodeUnit S χ)
    (E : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) (hE : ∀ V ∈ E.support, nodal V)
    (hdeg : g • E - E ∈ Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar (N * q)))) :
    ∃ (D : ↥(Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar (N * q)))))
      (_ : P.IsGoodDiv (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))))
      (hadm : P.glueData S (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) ∈ GluingData.admissible S),
      Pic0.mk D = Pic0.mk ⟨g • E - E, hdeg⟩ ∧
        ∃ χ : ↥S → Additive kˣ,
          GluedPic0.mk S ⟨P.glueData S (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))), hadm⟩ = GluedPic0.nodeUnit S χ :=
  H2Recon.TG_dispHom_of_forall P S g nodal (fun V hV => hpt V hV _) E hE

end GrainAdditive

private theorem H2Recon.V12op_exists_goodRep_pic0Mk_eq_smul_single_sub_and_gluedMk_eq_nodeUnit
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
      (R : ModularCurve.PlaceSpecialization.ProlongationTuple P) (hR : R.IsModel) (hRL : R.RegularityLaw W)
      (hNV : R.NodeValueLaw W) (hO : R.OrderLawFixed),
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
                - Finsupp.single V 1, hdeg⟩ ∧
                ∃ χ : ↥(nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W) → Additive (ResidueField A)ˣ,
                  GluedPic0.mk (nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W)
                      ⟨P.glueData (nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W)
                        (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))), hadm⟩
                    = GluedPic0.nodeUnit (nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W) χ :=
  fun W hW data hKr hα hβ P R hR hRL hNV hO σ hσ V h₁ h₂ h₃ hdeg =>
    haveI : NeZero q := ⟨hq.ne_zero⟩
    haveI : Fact q.Prime := ⟨hq⟩
    haveI : CharP (ResidueField A) q := ValuationSubring.charP_residueField_of_liesOverPrime_def hq hA
    letI := instDecidableEqResidueFieldSemistable A
    letI := instAlgebraResidueFieldModularFunctionFieldCSemistable A N
    (ModularCurve.PlaceSpecialization.exists_goodRep_admissible_smul_single_sub_self_of_isModel N q hq hqN A hA
        W hW data hKr hα hβ P R hR hRL hO σ hσ V h₁ h₂ h₃ hdeg).imp fun D hD => hD.imp fun hgood hD' => hD'.imp
      fun hadm hcls =>
        ⟨hcls,
          ModularCurve.PlaceSpecialization.exists_gluedMk_eq_nodeUnit_of_isGoodDiv_of_admissible_of_pic0Mk_eq_smul_single_sub_self_of_isModel
            N q hq hqN A hA W hW data hKr hα hβ P R hR hRL hNV hO
            (ModularCurve.PlaceSpecialization.ProlongationTuple.jumpLaw_of_isModel_of_oneSidedRegularityLaw hqN P W hW R hR
              (ModularCurve.PlaceSpecialization.ProlongationTuple.oneSidedRegularityLaw_of_isModel_of_not_dvd hqN P W hW R hR))
            σ hσ V h₁ h₂ h₃ hdeg D hgood hadm hcls⟩

private theorem H2Recon.Vchi_exists_goodRep_pic0Mk_eq_smul_sub_and_gluedMk_eq_nodeUnit_of_forall_nodal
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
      (R : ModularCurve.PlaceSpecialization.ProlongationTuple P) (hR : R.IsModel) (hRL : R.RegularityLaw W)
      (hNV : R.NodeValueLaw W) (hO : R.OrderLawFixed),
        ∀ σ ∈ A.inertiaSubgroupIn ℚ, ∀ (E : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))),
          (∀ V ∈ E.support, ¬ P.IsStrictFst V ∧ ¬ P.IsStrictSnd V ∧ P.reduceFst V ∈ W) →
          ∀ (hdeg : arithmeticGalois (modularFunctionFieldFull (N * q)) σ • E - E
              ∈ Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar (N * q)))),
            ∃ (D : ↥(Divisor.degZero (K := AlgebraicClosure ℚ)
                (F := ↥(modularFunctionFieldBar (N * q)))))
              (_ : P.IsGoodDiv (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))))
              (hadm : P.glueData (nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W)
                  (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)))
                ∈ GluingData.admissible
                    (nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W)),
              Pic0.mk D = Pic0.mk ⟨arithmeticGalois (modularFunctionFieldFull (N * q)) σ • E - E, hdeg⟩ ∧
                ∃ χ : ↥(nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W) → Additive (ResidueField A)ˣ,
                  GluedPic0.mk (nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W)
                      ⟨P.glueData (nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W)
                        (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))), hadm⟩
                    = GluedPic0.nodeUnit (nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W) χ := by
  intro W hW data hKr hα hβ P R hR hRL hNV hO σ hσ E hE hdeg
  haveI : NeZero q := ⟨hq.ne_zero⟩
  haveI : Fact q.Prime := ⟨hq⟩
  haveI : CharP (ResidueField A) q := ValuationSubring.charP_residueField_of_liesOverPrime_def hq hA
  letI := instDecidableEqResidueFieldSemistable A
  letI := instAlgebraResidueFieldModularFunctionFieldCSemistable A N
  exact H2Recon.exists_goodRep_nodeUnit_of_forall_single P (nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W)
    (arithmeticGalois (modularFunctionFieldFull (N * q)) σ)
    (fun V => ¬ P.IsStrictFst V ∧ ¬ P.IsStrictSnd V ∧ P.reduceFst V ∈ W)
    (fun V hV hdegV => H2Recon.V12op_exists_goodRep_pic0Mk_eq_smul_single_sub_and_gluedMk_eq_nodeUnit N q hq hqN A hA
      W hW data hKr hα hβ P R hR hRL hNV hO σ hσ V hV.1 hV.2.1 hV.2.2 hdegV)
    E hE hdeg

private theorem H2Recon.V_exists_goodRep_toPic0Pair_eq_zero_smul_sub_of_forall_nodal
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
      (R : ModularCurve.PlaceSpecialization.ProlongationTuple P) (hR : R.IsModel) (hRL : R.RegularityLaw W)
      (hNV : R.NodeValueLaw W) (hO : R.OrderLawFixed),
        ∀ σ ∈ A.inertiaSubgroupIn ℚ, ∀ (E : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))),
          (∀ V ∈ E.support, ¬ P.IsStrictFst V ∧ ¬ P.IsStrictSnd V ∧ P.reduceFst V ∈ W) →
          ∀ (hdeg : arithmeticGalois (modularFunctionFieldFull (N * q)) σ • E - E
              ∈ Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar (N * q)))),
            ∃ (D : ↥(Divisor.degZero (K := AlgebraicClosure ℚ)
                (F := ↥(modularFunctionFieldBar (N * q)))))
              (_ : P.IsGoodDiv (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))))
              (hadm : P.glueData (nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W)
                  (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)))
                ∈ GluingData.admissible
                    (nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W)),
              Pic0.mk D = Pic0.mk ⟨arithmeticGalois (modularFunctionFieldFull (N * q)) σ • E - E, hdeg⟩ ∧
                GluedPic0.toPic0Pair (nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W)
                  (GluedPic0.mk (nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W)
                    ⟨P.glueData (nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W)
                      (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))), hadm⟩)
                  = 0 := by
  intro W hW data hKr hα hβ P R hR hRL hNV hO σ hσ E hE hdeg
  haveI : NeZero q := ⟨hq.ne_zero⟩
  haveI : Fact q.Prime := ⟨hq⟩
  haveI : CharP (ResidueField A) q := ValuationSubring.charP_residueField_of_liesOverPrime_def hq hA
  letI := instDecidableEqResidueFieldSemistable A
  letI := instAlgebraResidueFieldModularFunctionFieldCSemistable A N
  have h := H2Recon.Vchi_exists_goodRep_pic0Mk_eq_smul_sub_and_gluedMk_eq_nodeUnit_of_forall_nodal N q hq hqN A hA
    W hW data hKr hα hβ P R hR hRL hNV hO σ hσ E hE hdeg
  refine h.elim fun D h' => ?_
  refine h'.elim fun hDg h'' => ?_
  refine h''.elim fun hadm hc => ?_
  refine hc.2.elim fun χ hχ => ?_

  exact ⟨D, hDg, hadm, hc.1, (congrArg (GluedPic0.toPic0Pair (nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W)) hχ).trans
    (GluedPic0.toPic0Pair_nodeUnit (nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W) χ)⟩

private theorem ne_zero_of_ord_pos {K F : Type*} [Field K] [Field F] [Algebra K F]
    (v : Place K F) {f : F} (h : 0 < v.ord f) : f ≠ 0 := by
  rintro rfl
  rw [Place.ord_zero] at h
  exact lt_irrefl 0 h

private theorem sep_ord_pos {N : ℕ} [NeZero N] {A : ValuationSubring (AlgebraicClosure ℚ)}
    (v : Place (ResidueField A) ↥(modularFunctionFieldC (ResidueField A) N))
    {c₁ c₂ : ResidueField A}
    (h₁ : 0 < v.ord ((⟨jqModC (ResidueField A), jqModC_mem (ResidueField A) N⟩ : modularFunctionFieldC (ResidueField A) N) - algebraMap (ResidueField A) (modularFunctionFieldC (ResidueField A) N) c₁))
    (h₂ : 0 < v.ord ((⟨jqModC (ResidueField A), jqModC_mem (ResidueField A) N⟩ : modularFunctionFieldC (ResidueField A) N) - algebraMap (ResidueField A) (modularFunctionFieldC (ResidueField A) N) c₂)) : c₁ = c₂ := by
  by_contra hne
  have hsub : ((⟨jqModC (ResidueField A), jqModC_mem (ResidueField A) N⟩ : modularFunctionFieldC (ResidueField A) N) - algebraMap (ResidueField A) (modularFunctionFieldC (ResidueField A) N) c₂) - ((⟨jqModC (ResidueField A), jqModC_mem (ResidueField A) N⟩ : modularFunctionFieldC (ResidueField A) N) - algebraMap (ResidueField A) (modularFunctionFieldC (ResidueField A) N) c₁) = algebraMap (ResidueField A) (modularFunctionFieldC (ResidueField A) N) (c₁ - c₂) := by
    rw [map_sub]
    ring
  have hv₁ : v.adicValuation ((⟨jqModC (ResidueField A), jqModC_mem (ResidueField A) N⟩ : modularFunctionFieldC (ResidueField A) N) - algebraMap (ResidueField A) (modularFunctionFieldC (ResidueField A) N) c₁) < 1 := by
    rw [v.adicValuation_eq_exp_neg_ord (ne_zero_of_ord_pos v h₁), ← WithZero.exp_zero]
    exact WithZero.exp_lt_exp.mpr (by omega)
  have hv₂ : v.adicValuation ((⟨jqModC (ResidueField A), jqModC_mem (ResidueField A) N⟩ : modularFunctionFieldC (ResidueField A) N) - algebraMap (ResidueField A) (modularFunctionFieldC (ResidueField A) N) c₂) < 1 := by
    rw [v.adicValuation_eq_exp_neg_ord (ne_zero_of_ord_pos v h₂), ← WithZero.exp_zero]
    exact WithZero.exp_lt_exp.mpr (by omega)
  have hval : v.adicValuation (algebraMap (ResidueField A) (modularFunctionFieldC (ResidueField A) N) (c₁ - c₂)) < 1 := by
    rw [← hsub]
    exact lt_of_le_of_lt (Valuation.map_sub _ _ _) (max_lt hv₂ hv₁)
  have hord0 : v.ord (algebraMap (ResidueField A) (modularFunctionFieldC (ResidueField A) N) (c₁ - c₂)) = 0 :=
    ConstantReduction.ord_algebraMap v (sub_ne_zero.mpr hne)
  rw [v.adicValuation_eq_exp_neg_ord ((map_ne_zero _).mpr (sub_ne_zero.mpr hne)), hord0] at hval
  simp at hval

private theorem H2Recon.n2_frobOnPlacesGeomLevel_ord_pos_pow
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
      (P : PlaceSpecialization A q N data hKr (ResidueField A) (IsLocalRing.residue A) hα hβ),
        ∀ (v : Place (ResidueField A) ↥(modularFunctionFieldC (ResidueField A) N)) (c : ResidueField A),
          0 < v.ord
              (⟨jqModC (ResidueField A), jqModC_mem (ResidueField A) N⟩
                - algebraMap (ResidueField A) (modularFunctionFieldC (ResidueField A) N) c) →
            0 < (frobOnPlacesGeomLevel (ResidueField A) N data hKr v).ord
                (⟨jqModC (ResidueField A), jqModC_mem (ResidueField A) N⟩
                  - algebraMap (ResidueField A) (modularFunctionFieldC (ResidueField A) N)
                      (c ^ q)) := by
  intro W hW data hKr hα hβ P v c h
  haveI : NeZero q := ⟨hq.ne_zero⟩
  haveI : Fact q.Prime := ⟨hq⟩
  haveI : CharP (ResidueField A) q := ValuationSubring.charP_residueField_of_liesOverPrime_def hq hA
  letI := instDecidableEqResidueFieldSemistable A
  letI := instAlgebraResidueFieldModularFunctionFieldCSemistable A N
  haveI : CharP (modularFunctionFieldC (ResidueField A) N) q :=
    charP_of_injective_algebraMap
      (algebraMap (ResidueField A) (modularFunctionFieldC (ResidueField A) N)).injective q
  have hperf : ∀ x : ResidueField A, ∃ d : ResidueField A, d ^ q = x := fun x =>
    IsAlgClosed.exists_pow_nat_eq x hq.pos
  have hg : frobeniusGeomLevel (ResidueField A) N data hKr ((⟨jqModC (ResidueField A), jqModC_mem (ResidueField A) N⟩ : modularFunctionFieldC (ResidueField A) N) - algebraMap (ResidueField A) (modularFunctionFieldC (ResidueField A) N) (c ^ q))
      = ((⟨jqModC (ResidueField A), jqModC_mem (ResidueField A) N⟩ : modularFunctionFieldC (ResidueField A) N) - algebraMap (ResidueField A) (modularFunctionFieldC (ResidueField A) N) c) ^ q := by
    rw [map_sub, frobeniusGeomLevel_jq, (frobeniusGeomLevel (ResidueField A) N data hKr).commutes,
      sub_pow_char, map_pow]
  have heq := ord_frobOnPlaces_of_pow_eq (ResidueField A) N data hKr hperf hg v
  rw [heq]
  exact h

private theorem H2Recon.n3_isStrictFst_or_isStrictSnd_of_frobSq_ne
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
      (P : PlaceSpecialization A q N data hKr (ResidueField A) (IsLocalRing.residue A) hα hβ),
        ∀ W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)),
          frobOnPlacesGeomLevel (ResidueField A) N data hKr (frobOnPlacesGeomLevel (ResidueField A) N data hKr (P.reduceFst W)) ≠ P.reduceFst W →
            P.IsStrictFst W ∨ P.IsStrictSnd W := by
  intro W hW data hKr hα hβ P W' h
  haveI : NeZero q := ⟨hq.ne_zero⟩
  haveI : Fact q.Prime := ⟨hq⟩
  haveI : CharP (ResidueField A) q := ValuationSubring.charP_residueField_of_liesOverPrime_def hq hA
  letI := instDecidableEqResidueFieldSemistable A
  letI := instAlgebraResidueFieldModularFunctionFieldCSemistable A N
  rcases P.d1 W' with hrel | hrel
  · have hrel' : P.reduceFst W' =
        frobOnPlacesGeomLevel (ResidueField A) N data hKr (P.reduceSnd W') := hrel
    refine Or.inr ⟨hrel', fun heq => h ?_⟩
    rw [hrel', heq]
  · have hrel' : frobOnPlacesGeomLevel (ResidueField A) N data hKr (P.reduceFst W') =
        P.reduceSnd W' := hrel
    exact Or.inl ⟨hrel', h⟩

private theorem H2Recon.M1a_exists_isGoodDiv_avoid_isPrincipal_sub_stable
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
      (P : PlaceSpecialization A q N data hKr (ResidueField A) (IsLocalRing.residue A) hα hβ),
        ∀ T : Finset (Place (ResidueField A) ↥(modularFunctionFieldC (ResidueField A) N)),
          ∃ E₀ C₀ : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)),
            (∀ V, 0 ≤ E₀ V) ∧ P.IsGoodDiv E₀ ∧
              (∀ V ∈ E₀.support, P.reduceFst V ∉ T ∧ P.reduceSnd V ∉ T) ∧
                0 < Divisor.degree E₀ ∧ (∀ V, 0 ≤ C₀ V) ∧
                  (∀ σ ∈ A.inertiaSubgroupIn ℚ,
                    arithmeticGalois (modularFunctionFieldFull (N * q)) σ • C₀ = C₀) ∧
                    0 < Divisor.degree C₀ ∧ Divisor.IsPrincipal (E₀ - C₀) :=
  ModularCurve.PlaceSpecialization.exists_isGoodDiv_reduce_notMem_isPrincipal_sub_of_smul_eq N q hq hqN A hA

private theorem H2Recon.s8_pow_q_sq_eq_self_of_frobSq_fixed_of_ord_pos
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
      (P : PlaceSpecialization A q N data hKr (ResidueField A) (IsLocalRing.residue A) hα hβ),
        ∀ (v : Place (ResidueField A) ↥(modularFunctionFieldC (ResidueField A) N)) (c : ResidueField A),
          frobOnPlacesGeomLevel (ResidueField A) N data hKr
              (frobOnPlacesGeomLevel (ResidueField A) N data hKr v) = v →
            0 < v.ord ((⟨jqModC (ResidueField A), jqModC_mem (ResidueField A) N⟩ : modularFunctionFieldC (ResidueField A) N) - algebraMap (ResidueField A) (modularFunctionFieldC (ResidueField A) N) c) → c ^ (q ^ 2) = c := by
  intro W hW data hKr hα hβ P v c hfix h
  haveI : NeZero q := ⟨hq.ne_zero⟩
  haveI : Fact q.Prime := ⟨hq⟩
  haveI : CharP (ResidueField A) q := ValuationSubring.charP_residueField_of_liesOverPrime_def hq hA
  letI := instDecidableEqResidueFieldSemistable A
  letI := instAlgebraResidueFieldModularFunctionFieldCSemistable A N
  have h2 := H2Recon.n2_frobOnPlacesGeomLevel_ord_pos_pow
    N q hq hqN A hA W hW data hKr hα hβ P v c h
  have h3 := H2Recon.n2_frobOnPlacesGeomLevel_ord_pos_pow
    N q hq hqN A hA W hW data hKr hα hβ P
    (frobOnPlacesGeomLevel (ResidueField A) N data hKr v) (c ^ q) h2
  rw [hfix, ← pow_mul, ← sq] at h3
  exact sep_ord_pos v h3 h

private theorem exists_ord_pos_sub_const {N : ℕ} [NeZero N]
    {A : ValuationSubring (AlgebraicClosure ℚ)}
    [IsCurveOver (ResidueField A) (modularFunctionFieldC (ResidueField A) N)]
    (v : Place (ResidueField A) ↥(modularFunctionFieldC (ResidueField A) N))
    (hreg : 0 ≤ v.ord ((⟨jqModC (ResidueField A), jqModC_mem (ResidueField A) N⟩ : modularFunctionFieldC (ResidueField A) N)))
    (hJ0 : ((⟨jqModC (ResidueField A), jqModC_mem (ResidueField A) N⟩ : modularFunctionFieldC (ResidueField A) N)) ≠ 0)
    (hJne : ∀ c : ResidueField A, (⟨jqModC (ResidueField A), jqModC_mem (ResidueField A) N⟩ : modularFunctionFieldC (ResidueField A) N) - algebraMap (ResidueField A) (modularFunctionFieldC (ResidueField A) N) c ≠ 0) :
    ∃ c : ResidueField A, 0 < v.ord ((⟨jqModC (ResidueField A), jqModC_mem (ResidueField A) N⟩ : modularFunctionFieldC (ResidueField A) N) - algebraMap (ResidueField A) (modularFunctionFieldC (ResidueField A) N) c) := by
  classical
  have hrat : v.IsRational := by
    intro x
    have h1 : (⊥ : Subalgebra (ResidueField A) v.ResidueField) = ⊤ :=
      Subalgebra.bot_eq_top_of_finrank_eq_one
        (deg_eq_one_modularFunctionFieldC (ResidueField A) N v)
    have hx : x ∈ (⊥ : Subalgebra (ResidueField A) v.ResidueField) := by
      rw [h1]; trivial
    exact Algebra.mem_bot.mp hx
  have hmem : ((⟨jqModC (ResidueField A), jqModC_mem (ResidueField A) N⟩ : modularFunctionFieldC (ResidueField A) N)) ∈ v.toValuationSubring := v.mem_of_ord_nonneg hJ0 hreg
  refine ⟨v.evalAt ((⟨jqModC (ResidueField A), jqModC_mem (ResidueField A) N⟩ : modularFunctionFieldC (ResidueField A) N)), ?_⟩
  have hsubmem : algebraMap (ResidueField A) (modularFunctionFieldC (ResidueField A) N) (v.evalAt ((⟨jqModC (ResidueField A), jqModC_mem (ResidueField A) N⟩ : modularFunctionFieldC (ResidueField A) N))) ∈ v.toValuationSubring :=
    v.algebraMap_mem' _
  have humem : ((⟨jqModC (ResidueField A), jqModC_mem (ResidueField A) N⟩ : modularFunctionFieldC (ResidueField A) N)) - algebraMap (ResidueField A) (modularFunctionFieldC (ResidueField A) N) (v.evalAt ((⟨jqModC (ResidueField A), jqModC_mem (ResidueField A) N⟩ : modularFunctionFieldC (ResidueField A) N))) ∈ v.toValuationSubring :=
    sub_mem hmem hsubmem
  have hnonneg : 0 ≤ v.ord ((⟨jqModC (ResidueField A), jqModC_mem (ResidueField A) N⟩ : modularFunctionFieldC (ResidueField A) N) - algebraMap (ResidueField A) (modularFunctionFieldC (ResidueField A) N) (v.evalAt ((⟨jqModC (ResidueField A), jqModC_mem (ResidueField A) N⟩ : modularFunctionFieldC (ResidueField A) N)))) :=
    v.ord_nonneg_of_mem humem
  rcases lt_or_eq_of_le hnonneg with h | h
  · exact h
  · exfalso
    have hne := hJne (v.evalAt ((⟨jqModC (ResidueField A), jqModC_mem (ResidueField A) N⟩ : modularFunctionFieldC (ResidueField A) N)))
    have hinvmem : (((⟨jqModC (ResidueField A), jqModC_mem (ResidueField A) N⟩ : modularFunctionFieldC (ResidueField A) N)) - algebraMap (ResidueField A) (modularFunctionFieldC (ResidueField A) N) (v.evalAt ((⟨jqModC (ResidueField A), jqModC_mem (ResidueField A) N⟩ : modularFunctionFieldC (ResidueField A) N))))⁻¹ ∈ v.toValuationSubring := by
      refine v.mem_of_ord_nonneg (inv_ne_zero hne) ?_
      rw [← zpow_neg_one, Place.ord_zpow]
      omega
    have hunit : IsUnit ((⟨_, humem⟩ : v.toValuationSubring)) := by
      refine isUnit_iff_exists_inv.mpr ⟨⟨_, hinvmem⟩, ?_⟩
      exact Subtype.ext (mul_inv_cancel₀ hne)
    have hres0 : residue v.toValuationSubring ⟨_, humem⟩ = 0 := by
      have hsplit : ((⟨_, humem⟩ : v.toValuationSubring))
          = ⟨_, hmem⟩ - ⟨_, hsubmem⟩ := rfl
      have hconst : residue v.toValuationSubring ⟨_, hsubmem⟩
          = algebraMap (ResidueField A) v.ResidueField (v.evalAt ((⟨jqModC (ResidueField A), jqModC_mem (ResidueField A) N⟩ : modularFunctionFieldC (ResidueField A) N))) := rfl
      rw [hsplit, map_sub, hconst, ← v.algebraMap_evalAt hrat hmem, sub_self]
    have hru : IsUnit (residue v.toValuationSubring ⟨_, humem⟩) :=
      hunit.map (residue v.toValuationSubring)
    rw [hres0] at hru
    exact hru.ne_zero rfl

private theorem H2Recon.isCurveOver_modularFunctionFieldC_residueField
    (A : ValuationSubring (AlgebraicClosure ℚ)) (N : ℕ) [NeZero N] :
    IsCurveOver (ResidueField A) (modularFunctionFieldC (ResidueField A) N) :=
  isCurveOver_modularFunctionFieldC_of_perfectField (ResidueField A) N

private theorem H2Recon.M2''_exists_finset_disjoint_strict_or_mem_ssPlaces_of_reduce_notMem
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
      (P : PlaceSpecialization A q N data hKr (ResidueField A) (IsLocalRing.residue A) hα hβ),
        ∃ (Tex : Finset (Place (ResidueField A) ↥(modularFunctionFieldC (ResidueField A) N))),
          (∀ w ∈ Tex, w ∉ W) ∧
            ∀ V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)),
            P.reduceFst V ∉ Tex → P.reduceSnd V ∉ Tex →
              (P.IsStrictFst V ∨ P.IsStrictSnd V) ∨ P.reduceFst V ∈ W := by
  intro W hW data hKr hα hβ P
  classical
  haveI : NeZero q := ⟨hq.ne_zero⟩
  haveI : Fact q.Prime := ⟨hq⟩
  haveI : CharP (ResidueField A) q := ValuationSubring.charP_residueField_of_liesOverPrime_def hq hA
  letI := instDecidableEqResidueFieldSemistable A
  letI := instAlgebraResidueFieldModularFunctionFieldCSemistable A N
  haveI hICO := H2Recon.isCurveOver_modularFunctionFieldC_residueField A N
  have hc2 : 1 < q ^ 2 := by
    have := hq.two_le
    nlinarith
  have hJ0 : ((⟨jqModC (ResidueField A), jqModC_mem (ResidueField A) N⟩ : modularFunctionFieldC (ResidueField A) N)) ≠ 0 := fun h => jqModC_ne_zero_def (ResidueField A) (congrArg Subtype.val h)
  have hJne : ∀ c : ResidueField A, ((⟨jqModC (ResidueField A), jqModC_mem (ResidueField A) N⟩ : modularFunctionFieldC (ResidueField A) N)) - algebraMap (ResidueField A) (modularFunctionFieldC (ResidueField A) N) c ≠ 0 := by
    intro c h
    have heq : ((⟨jqModC (ResidueField A), jqModC_mem (ResidueField A) N⟩ : modularFunctionFieldC (ResidueField A) N)) = algebraMap (ResidueField A) (modularFunctionFieldC (ResidueField A) N) c := sub_eq_zero.mp h
    refine jModElt_notMem_qIntegersBar (ResidueField A) (jqModC_mem (ResidueField A) N) ?_
    show ((⟨jqModC (ResidueField A), jqModC_mem (ResidueField A) N⟩ : modularFunctionFieldC (ResidueField A) N)) ∈ qIntegersBar (ResidueField A) (modularFunctionFieldC (ResidueField A) N)
    rw [heq]
    exact (qInftyPlaceMod (ResidueField A) (jqModC_mem (ResidueField A) N)).algebraMap_mem' c
  obtain ⟨DJ, hDJ, -⟩ := (IsCurveOver.hasPrincipalDivisors
    (K := ResidueField A) (F := modularFunctionFieldC (ResidueField A) N)).exists_divisor _ hJ0
  have hdiv : ∀ c : ResidueField A,
      ∃ D : Divisor (ResidueField A) (modularFunctionFieldC (ResidueField A) N),
        ∀ v', D v' = v'.ord (((⟨jqModC (ResidueField A), jqModC_mem (ResidueField A) N⟩ : modularFunctionFieldC (ResidueField A) N)) - algebraMap (ResidueField A) (modularFunctionFieldC (ResidueField A) N) c) := by
    intro c
    obtain ⟨D, hD, -⟩ := (IsCurveOver.hasPrincipalDivisors
      (K := ResidueField A) (F := modularFunctionFieldC (ResidueField A) N)).exists_divisor _ (hJne c)
    exact ⟨D, hD⟩
  refine ⟨((((Polynomial.X ^ (q ^ 2) - Polynomial.X :
        Polynomial (ResidueField A)).roots).toFinset.biUnion
      (fun c => (hdiv c).choose.support)) ∪ DJ.support) \ W,
    fun w hw => (Finset.mem_sdiff.mp hw).2, ?_⟩
  intro V hfst hsnd
  by_cases hfix : frobOnPlacesGeomLevel (ResidueField A) N data hKr (frobOnPlacesGeomLevel (ResidueField A) N data hKr (P.reduceFst V)) = P.reduceFst V
  · right
    by_contra hWmem
    have hnot0 : P.reduceFst V ∉ ((((Polynomial.X ^ (q ^ 2) - Polynomial.X :
          Polynomial (ResidueField A)).roots).toFinset.biUnion
        (fun c => (hdiv c).choose.support)) ∪ DJ.support) :=
      fun h => hfst (Finset.mem_sdiff.mpr ⟨h, hWmem⟩)
    have hreg : 0 ≤ (P.reduceFst V).ord ((⟨jqModC (ResidueField A), jqModC_mem (ResidueField A) N⟩ : modularFunctionFieldC (ResidueField A) N)) := by
      by_contra hneg
      push_neg at hneg
      refine hnot0 (Finset.mem_union_right _ (Finsupp.mem_support_iff.mpr ?_))
      rw [hDJ]
      omega
    obtain ⟨c, hc⟩ := exists_ord_pos_sub_const (P.reduceFst V) hreg hJ0 hJne
    have hcfix := H2Recon.s8_pow_q_sq_eq_self_of_frobSq_fixed_of_ord_pos
      N q hq hqN A hA W hW data hKr hα hβ P (P.reduceFst V) c hfix hc
    refine hnot0 (Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨c, ?_, ?_⟩))
    · rw [Multiset.mem_toFinset,
        Polynomial.mem_roots (FiniteField.X_pow_card_sub_X_ne_zero (ResidueField A) hc2)]
      simp [hcfix]
    · exact Finsupp.mem_support_iff.mpr (by rw [(hdiv c).choose_spec]; exact hc.ne')
  · exact Or.inl (H2Recon.n3_isStrictFst_or_isStrictSnd_of_frobSq_ne N q hq hqN A hA W hW data hKr hα hβ P V hfix)

private theorem H2Recon.M1'_exists_rep_reduce_avoid_finset_of_disjoint
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
      (R : ModularCurve.PlaceSpecialization.ProlongationTuple P) (hR : R.IsModel) (hRL : R.RegularityLaw W)
      (hO : R.OrderLawFixed),
        ∀ (T : Finset (Place (ResidueField A) ↥(modularFunctionFieldC (ResidueField A) N))),
          (∀ w ∈ T, w ∉ W) →
          ∀ x : JZero (N * q),
            ∃ (E : ↥(Divisor.degZero (K := AlgebraicClosure ℚ)
                  (F := ↥(modularFunctionFieldBar (N * q))))),
              Pic0.mk E = x ∧
                ∀ V ∈ (E : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))).support,
                  P.reduceFst V ∉ T ∧ P.reduceSnd V ∉ T := by
  intro W hW data hKr hα hβ P R hR hRL hO
  exact H2Recon.M1b'_exists_rep_of_move_engine_of_disjoint N q hq hqN A hA W hW data hKr hα hβ P R hR hRL hO
    (H2Recon.M1a_exists_isGoodDiv_avoid_isPrincipal_sub_stable N q hq hqN A hA W hW data hKr hα hβ P)

private theorem H2Recon.M_exists_rep_support_strict_or_nodal
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
      (R : ModularCurve.PlaceSpecialization.ProlongationTuple P) (hR : R.IsModel) (hRL : R.RegularityLaw W)
      (hO : R.OrderLawFixed),
        ∀ x : JZero (N * q),
          ∃ (E : ↥(Divisor.degZero (K := AlgebraicClosure ℚ)
                (F := ↥(modularFunctionFieldBar (N * q))))),
            Pic0.mk E = x ∧
              ∀ V ∈ (E : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))).support,
                (P.IsStrictFst V ∨ P.IsStrictSnd V) ∨ P.reduceFst V ∈ W := by
  intro W hW data hKr hα hβ P R hR hRL hO x
  classical
  haveI : NeZero q := ⟨hq.ne_zero⟩
  haveI : Fact q.Prime := ⟨hq⟩
  haveI : CharP (ResidueField A) q := ValuationSubring.charP_residueField_of_liesOverPrime_def hq hA
  letI := instDecidableEqResidueFieldSemistable A
  letI := instAlgebraResidueFieldModularFunctionFieldCSemistable A N
  obtain ⟨Tex, hdisj, hTex⟩ :=
    H2Recon.M2''_exists_finset_disjoint_strict_or_mem_ssPlaces_of_reduce_notMem
      N q hq hqN A hA W hW data hKr hα hβ P
  obtain ⟨E, hmk, havoid⟩ :=
    H2Recon.M1'_exists_rep_reduce_avoid_finset_of_disjoint
      N q hq hqN A hA W hW data hKr hα hβ P R hR hRL hO Tex hdisj x
  exact ⟨E, hmk, fun V hV => hTex V (havoid V hV).1 (havoid V hV).2⟩

private theorem H2Recon.B_isGoodDiv_glueData_smul_sub_eq_zero_of_forall_strict
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
      (P : PlaceSpecialization A q N data hKr (ResidueField A) (IsLocalRing.residue A) hα hβ),
        ∀ σ ∈ A.inertiaSubgroupIn ℚ, ∀ (E : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))),
          (∀ V ∈ E.support, P.IsStrictFst V ∨ P.IsStrictSnd V) →
            P.IsGoodDiv (arithmeticGalois (modularFunctionFieldFull (N * q)) σ • E - E) ∧
              P.glueData (nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W) (arithmeticGalois (modularFunctionFieldFull (N * q)) σ • E - E) = 0 :=
  ModularCurve.PlaceSpecialization.isGoodDiv_and_glueData_smul_sub_self_eq_zero_of_forall_isStrict N q hq hqN A hA

open _root_.ModularCurve.PlaceSpecialization _root_.P2MW.S_ModularCurve_PlaceSpecialization_exists_goodRep_toPic0Pair_eq_zero_smul_sub_self_of_isModel.ModularCurve.PlaceSpecialization in

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
      (P : PlaceSpecialization A q N data hKr (ResidueField A) (IsLocalRing.residue A) hα hβ) (R : ProlongationTuple P) (hR : R.IsModel) (hRL : R.RegularityLaw W) (hNV : R.NodeValueLaw W) (hO : R.OrderLawFixed),
        ∀ σ ∈ A.inertiaSubgroupIn ℚ, ∀ x : JZero (N * q),
          PrimeToTorsion q x →
            ∃ (D : ↥(Divisor.degZero (K := AlgebraicClosure ℚ)
                (F := ↥(modularFunctionFieldBar (N * q)))))
              (_ : P.IsGoodDiv (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))))
              (hadm : P.glueData (nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W)
                  (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)))
                ∈ GluingData.admissible
                    (nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W)),
              Pic0.mk D = σ • x - x ∧
                GluedPic0.toPic0Pair (nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W)
                  (GluedPic0.mk (nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W)
                    ⟨P.glueData (nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W)
                      (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))), hadm⟩)
                  = 0 := by
  intro W hW data hKr hα hβ P R hRm hRL hNV hO σ hσ x _htor
  classical
  haveI : NeZero q := ⟨hq.ne_zero⟩
  haveI : Fact q.Prime := ⟨hq⟩
  haveI : CharP (ResidueField A) q := ValuationSubring.charP_residueField_of_liesOverPrime_def hq hA
  letI := instDecidableEqResidueFieldSemistable A
  letI := instAlgebraResidueFieldModularFunctionFieldCSemistable A N
  have HM := H2Recon.M_exists_rep_support_strict_or_nodal N q hq hqN A hA W hW data hKr hα hβ P R hRm hRL hO x
  obtain ⟨E₀, hmkE, hsupp⟩ := HM
  have hsplit : ((E₀ : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))).filter (fun V => P.IsStrictFst V ∨ P.IsStrictSnd V)) + ((E₀ : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))).filter (fun V => ¬ (P.IsStrictFst V ∨ P.IsStrictSnd V))) = (E₀ : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) := by
    ext V
    rw [Finsupp.add_apply, Finsupp.filter_apply, Finsupp.filter_apply]
    by_cases h : P.IsStrictFst V ∨ P.IsStrictSnd V
    · rw [if_pos h, if_neg (not_not_intro h), add_zero]
    · rw [if_neg h, if_pos h, zero_add]
  have hEs : ∀ V ∈ ((E₀ : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))).filter (fun V => P.IsStrictFst V ∨ P.IsStrictSnd V)).support, P.IsStrictFst V ∨ P.IsStrictSnd V := by
    intro V hV
    simp only [Finsupp.support_filter, Finset.mem_filter] at hV
    exact hV.2
  have hEn : ∀ V ∈ ((E₀ : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))).filter (fun V => ¬ (P.IsStrictFst V ∨ P.IsStrictSnd V))).support,
      ¬ P.IsStrictFst V ∧ ¬ P.IsStrictSnd V ∧ P.reduceFst V ∈ W := by
    intro V hV
    simp only [Finsupp.support_filter, Finset.mem_filter] at hV
    exact ⟨fun h => hV.2 (Or.inl h), fun h => hV.2 (Or.inr h),
      (hsupp V hV.1).resolve_left hV.2⟩
  have hB := H2Recon.B_isGoodDiv_glueData_smul_sub_eq_zero_of_forall_strict
    N q hq hqN A hA W hW data hKr hα hβ P σ hσ ((E₀ : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))).filter (fun V => P.IsStrictFst V ∨ P.IsStrictSnd V)) hEs
  have hdegEs : arithmeticGalois (modularFunctionFieldFull (N * q)) σ • ((E₀ : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))).filter (fun V => P.IsStrictFst V ∨ P.IsStrictSnd V)) - ((E₀ : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))).filter (fun V => P.IsStrictFst V ∨ P.IsStrictSnd V))
      ∈ Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar (N * q))) := by
    rw [Divisor.mem_degZero, map_sub, SemilinearAut.degree_smul, sub_self]
  have hdegEn : arithmeticGalois (modularFunctionFieldFull (N * q)) σ • ((E₀ : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))).filter (fun V => ¬ (P.IsStrictFst V ∨ P.IsStrictSnd V))) - ((E₀ : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))).filter (fun V => ¬ (P.IsStrictFst V ∨ P.IsStrictSnd V)))
      ∈ Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar (N * q))) := by
    rw [Divisor.mem_degZero, map_sub, SemilinearAut.degree_smul, sub_self]
  have hR := H2Recon.V_exists_goodRep_toPic0Pair_eq_zero_smul_sub_of_forall_nodal
    N q hq hqN A hA W hW data hKr hα hβ P R hRm hRL hNV hO σ hσ ((E₀ : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))).filter (fun V => ¬ (P.IsStrictFst V ∨ P.IsStrictSnd V))) hEn hdegEn
  have hadm₁ : P.glueData (nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W) (arithmeticGalois (modularFunctionFieldFull (N * q)) σ • ((E₀ : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))).filter (fun V => P.IsStrictFst V ∨ P.IsStrictSnd V)) - ((E₀ : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))).filter (fun V => P.IsStrictFst V ∨ P.IsStrictSnd V))) ∈ GluingData.admissible (nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W) := by
    rw [hB.2]
    exact zero_mem _
  have hν₁ : GluedPic0.toPic0Pair (nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W)
      (GluedPic0.mk (nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W) ⟨_, hadm₁⟩) = 0 :=
    H2Recon.nu_zero_aux (nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W) _ hadm₁ hB.2
  have hA := H2Recon.A_toricGood_add N q hq hqN A hA W hW data hKr hα hβ P
    (Pic0.mk ⟨arithmeticGalois (modularFunctionFieldFull (N * q)) σ • ((E₀ : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))).filter (fun V => P.IsStrictFst V ∨ P.IsStrictSnd V)) - ((E₀ : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))).filter (fun V => P.IsStrictFst V ∨ P.IsStrictSnd V)), hdegEs⟩)
    (Pic0.mk ⟨arithmeticGalois (modularFunctionFieldFull (N * q)) σ • ((E₀ : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))).filter (fun V => ¬ (P.IsStrictFst V ∨ P.IsStrictSnd V))) - ((E₀ : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))).filter (fun V => ¬ (P.IsStrictFst V ∨ P.IsStrictSnd V))), hdegEn⟩)
    ⟨⟨arithmeticGalois (modularFunctionFieldFull (N * q)) σ • ((E₀ : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))).filter (fun V => P.IsStrictFst V ∨ P.IsStrictSnd V)) - ((E₀ : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))).filter (fun V => P.IsStrictFst V ∨ P.IsStrictSnd V)), hdegEs⟩, hB.1, hadm₁, rfl, hν₁⟩ hR
  have hmk_sub : ∀ (a b : ↥(Divisor.degZero (K := AlgebraicClosure ℚ)
      (F := ↥(modularFunctionFieldBar (N * q))))), Pic0.mk (a - b) = Pic0.mk a - Pic0.mk b := by
    intro a b
    rw [eq_sub_iff_add_eq, ← Pic0.mk_add, sub_add_cancel]
  have hdivsum : (arithmeticGalois (modularFunctionFieldFull (N * q)) σ • ((E₀ : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))).filter (fun V => P.IsStrictFst V ∨ P.IsStrictSnd V)) - ((E₀ : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))).filter (fun V => P.IsStrictFst V ∨ P.IsStrictSnd V))) + (arithmeticGalois (modularFunctionFieldFull (N * q)) σ • ((E₀ : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))).filter (fun V => ¬ (P.IsStrictFst V ∨ P.IsStrictSnd V))) - ((E₀ : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))).filter (fun V => ¬ (P.IsStrictFst V ∨ P.IsStrictSnd V))))
      = arithmeticGalois (modularFunctionFieldFull (N * q)) σ • (E₀ : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) - (E₀ : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) := by
    conv_rhs => rw [← hsplit]
    rw [smul_add]
    abel
  have hclass : Pic0.mk ⟨arithmeticGalois (modularFunctionFieldFull (N * q)) σ • ((E₀ : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))).filter (fun V => P.IsStrictFst V ∨ P.IsStrictSnd V)) - ((E₀ : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))).filter (fun V => P.IsStrictFst V ∨ P.IsStrictSnd V)), hdegEs⟩ + Pic0.mk ⟨arithmeticGalois (modularFunctionFieldFull (N * q)) σ • ((E₀ : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))).filter (fun V => ¬ (P.IsStrictFst V ∨ P.IsStrictSnd V))) - ((E₀ : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))).filter (fun V => ¬ (P.IsStrictFst V ∨ P.IsStrictSnd V))), hdegEn⟩
      = σ • x - x := by
    calc Pic0.mk ⟨arithmeticGalois (modularFunctionFieldFull (N * q)) σ • ((E₀ : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))).filter (fun V => P.IsStrictFst V ∨ P.IsStrictSnd V)) - ((E₀ : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))).filter (fun V => P.IsStrictFst V ∨ P.IsStrictSnd V)), hdegEs⟩ + Pic0.mk ⟨arithmeticGalois (modularFunctionFieldFull (N * q)) σ • ((E₀ : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))).filter (fun V => ¬ (P.IsStrictFst V ∨ P.IsStrictSnd V))) - ((E₀ : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))).filter (fun V => ¬ (P.IsStrictFst V ∨ P.IsStrictSnd V))), hdegEn⟩
        = Pic0.mk (⟨arithmeticGalois (modularFunctionFieldFull (N * q)) σ • ((E₀ : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))).filter (fun V => P.IsStrictFst V ∨ P.IsStrictSnd V)) - ((E₀ : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))).filter (fun V => P.IsStrictFst V ∨ P.IsStrictSnd V)), hdegEs⟩ + ⟨arithmeticGalois (modularFunctionFieldFull (N * q)) σ • ((E₀ : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))).filter (fun V => ¬ (P.IsStrictFst V ∨ P.IsStrictSnd V))) - ((E₀ : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))).filter (fun V => ¬ (P.IsStrictFst V ∨ P.IsStrictSnd V))), hdegEn⟩) :=
          (Pic0.mk_add _ _).symm
      _ = Pic0.mk (SemilinearAut.degZeroSMulHom (arithmeticGalois (modularFunctionFieldFull (N * q)) σ) E₀ - E₀) := by
          congr 1
          refine Subtype.ext ?_
          push_cast [AddSubgroup.coe_add, AddSubgroup.coe_sub, SemilinearAut.coe_degZeroSMulHom]
          exact hdivsum
      _ = Pic0.mk (SemilinearAut.degZeroSMulHom (arithmeticGalois (modularFunctionFieldFull (N * q)) σ) E₀) - Pic0.mk E₀ := hmk_sub _ _
      _ = σ • x - x := by
          rw [← SemilinearAut.pic0_smul_mk, ← ModularCurve.galois_smul_pic0_def, hmkE]
  exact ⟨hA.choose, hA.choose_spec.choose, hA.choose_spec.choose_spec.choose,
    (hA.choose_spec.choose_spec.choose_spec.1).trans hclass, hA.choose_spec.choose_spec.choose_spec.2⟩

#print axioms solution

end S_ModularCurve_PlaceSpecialization_exists_goodRep_toPic0Pair_eq_zero_smul_sub_self_of_isModel
end P2MW
export P2MW.S_ModularCurve_PlaceSpecialization_exists_goodRep_toPic0Pair_eq_zero_smul_sub_self_of_isModel (solution)
