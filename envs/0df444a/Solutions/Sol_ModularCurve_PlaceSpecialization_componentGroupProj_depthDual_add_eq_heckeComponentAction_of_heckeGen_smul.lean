-- Prove2me | solution 1 for ModularCurve.PlaceSpecialization.componentGroupProj_depthDual_add_eq_heckeComponentAction_of_heckeGen_smul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/993344e6-87d6-516c-a002-9999aca66ce2

import Definitions.Def_ModularCurve_NodeDepth
import Definitions.Def_ModularCurve_PlaceWidthChar
import Definitions.Def_ModularCurve_ComponentGroupHecke
import Definitions.Def_ModularCurve_CharLDegeneracyHecke
import Definitions.Def_ModularCurve_HeckeModule
import Definitions.Def_ValuationSubring_ReduceAt
import Definitions.Def_ModularCurve_GlueData
import Definitions.Def_ModularCurve_PlaceWidth
import Theorems.Thm_ModularCurve_heckeOperatorsCommuteBar
import Theorems.Thm_ModularCurve_heckeInputsAlong_of_prime
import Theorems.Thm_ModularCurve_hasPrincipalDivisors_modularFunctionFieldBar_unconditional
import Theorems.Thm_ModularCurve_heckeAlphaBarIntegral_of_prime
import Theorems.Thm_ModularCurve_heckeBetaBarIntegral_of_prime
import Theorems.Thm_ModularCurve_PlaceSpecialization_depthDual_eq_zero_of_isGoodDiv
import Theorems.Thm_ModularCurve_PlaceSpecialization_depthDual_add_mem_range_gramMap_of_isPrincipal
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_nodeValueLaw_of_regularityLaw
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_valueIntegralityLaw_of_orderLawFixed
import Theorems.Thm_ModularCurve_PlaceSpecialization_frobOnPlacesGeomLevel_frobOnPlacesGeomLevel_eq_self_of_mem_ssPlaces
import Theorems.Thm_ModularCurve_PlaceSpecialization_isStrictFst_or_isStrictSnd_iff
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_crossingExponent_eq_placeWidthChar_mul_of_orderLawFixed
import Theorems.Thm_ModularCurve_one_le_placeWidthChar_of_mem_ssPlaces
import Theorems.Thm_ModularCurve_arithFrobC_smul_eq_frobOnPlacesGeomLevel
import Theorems.Thm_ValuationSubring_isAlgClosed_residueField
import Theorems.Thm_ModularCurve_PlaceSpecialization_componentGroupProj_depthDual_add_eq_heckeComponentAction_of_heckeGen_smul_of_lt_five
import Theorems.Thm_ModularCurve_PlaceSpecialization_componentGroupProj_depthDual_add_eq_heckeComponentAction_of_heckeGen_smul_of_five_le_of_not_isGoodDiv
import Theorems.Thm_ModularCurve_finrankAlong_heckeBetaBar
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_NodeCoordinates_depth_lt_of_depthValueLaw_of_nodeEquation
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_NodeCoordinates_depth_pos_of_depthValueLaw_of_nodeEquation
import Theorems.Thm_ModularCurve_PlaceSpecialization_exists_rep_eq_off_strict_reduce_notMem_heckeDivBar_strictPart_good_kindResp_of_isModel
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_PlaceSpecialization_componentGroupProj_depthDual_add_eq_heckeComponentAction_of_heckeGen_smul
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent ModularCurve.B3.instIsElliptic_goodModel WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral instTopologicallyFGOfFiniteType AdicCompletion.instIsLocalRingMaximalIdeal ModularCurve.instIsElliptic_tateBase WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.NodeLocalized.isLocalization_nodeDenominators ModularCurve.NodeLocalized.algebraEvalRange ModularCurve.NodeLocalized.isLocalRing_modularLocalizedAtPoint ModularCurve.NodeLocalized.isScalarTower_K_fieldOver_bar ModularCurve.NodeLocalized.algebraFieldOverBar ModularCurve.NodeLocalized.algebra_isIntegral_fieldOver_bar ModularCurve.NodeLocalized.isScalarTower_fieldOver_bar_laurent ModularCurve.NodeLocalized.charZero_fieldOver ModularCurve.NodeLocalized.algebraFieldOver ModularCurve.NodeLocalized.charZero_laurentSeries_algClosure ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar"
p2m_attr_erase "instance" "AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.instIsScalarTowerJAdjoin GaloisRepAdic.instAddCommGroup GaloisRepAdic.instFree GaloisRepAdic.instFinite GaloisRepAdic.instModule ResidualGaloisRep.instModule ResidualGaloisRep.instModuleFinite ResidualGaloisRep.instAddCommGroup WeierstrassCurve.Affine.Point.instFinite AlgebraicCurve.CurveModel.isProper AlgebraicCurve.CurveModel.isIntegral AlgebraicCurve.CurveModel.smooth ModularCurve.IgusaScheme.isOpenImmersion_fInf ModularCurve.IgusaScheme.isOpenImmersion_ιInf ModularCurve.IgusaScheme.fact_jFull_ne_zero ModularCurve.IgusaScheme.isOpenImmersion_ιFin ModularCurve.IgusaScheme.isOpenImmersion_fFin"
p2m_attr_erase "instance" "AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin AlgebraicCurve.CurveModel.chartRing_finitePresentation ModularCurve.numberField_of_finiteDimensional AlgebraicCurve.GaussReduction.isLocalHom_constToGauss instFieldLaurentSeriesAlgClosureRat instAlgebraModularFunctionFieldBar ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instAlgebraResidueFieldSubtypeMemValuationSubringGaussBaseResOne ModularCurve.PlaceSpecialization.LevelOneProlongationPair.algGaussBase instAlgebraModularFunctionFieldFullC ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instAlgebraSubtypeMemValuationSubringGaussBaseResOne ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instAlgebraSubtypeMemValuationSubringGaussBaseResTwo instFieldModularFunctionFieldC ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isScalarTower_resOne instFieldLaurentSeries'"
p2m_attr_erase "instance" "ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isScalarTower_resTwo instModuleModularFunctionFieldBar ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isLocalHom_resBase₁ instAlgebraModularFunctionFieldC ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isLocalHom_constToGaussBase ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instFieldResOne instFieldModularFunctionFieldBar ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instAlgebraResidueFieldSubtypeMemValuationSubringGaussBaseResTwo ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instFieldResTwo instFieldModularFunctionFieldFullC ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isScalarTower_gaussBase instAlgebraLaurentSeriesAlgClosureRat ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isLocalHom_resBase₂ ModularCurve.PlaceSpecialization.LevelOneProlongationPair.algResidueConst instCommRingModularFunctionFieldBar CuspForm.heckeAlgebra.instCommRing CuspForm.heckeAlgebra.instIsMulCommutative CuspForm.heckeAlgebra.instIsAddTorsionFree ModularCurve.CuspSpace.instNonempty ModularCurve.CuspSpace.instSubsingletonOfOne ModularCurve.CuspSpace.instFinite ModularCurve.instAlgebraIntermediateFieldLaurent ModularCurve.instIsScalarTowerKaehlerIntermediateFieldLaurent ModularCurve.instIsScalarTowerIntermediateFieldLaurent ModularCurve.instModuleKaehlerIntermediateFieldLaurent FLT.Gamma0FundamentalSet.instContinuousConstSMulSpecialLinearGroupFinOfNatNatIntUpperHalfPlane_definitions FLT.HyperbolicMeasure.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatIntUpperHalfPlaneVolume_definitions FLT.HyperbolicMeasure.instIsOpenPosMeasureUpperHalfPlaneVolume_definitions FLT.L2ProductionInstance.isFiniteMeasure_gamma0 FLT.L2ProductionInstance.countable_SL2Z FLT.L2ProductionInstance.countable_quotient FLT.L2ProductionInstance.nontrivial_gamma0L2 HeckeEis.instModuleCoeffH1par HeckeEis.instAddCommGroupCoeffH1par HeckeEis.instFiniteIndexHeckeUpper ModularCurve.LevelOnePhi.instAddCommGroup AlgebraicCurve.CellDissection.fintypeV AlgebraicCurve.CellDissection.fintypeC AlgebraicCurve.CellDissection.fintypeE AlgebraicCurve.CellDissection.decEqV"
p2m_attr_erase "instance" "AlgebraicCurve.CellDissection.decEqC AlgebraicCurve.CellDissection.decEqE WeierstrassCurve.Affine.instIsDiscreteValuationRingSubtypeFunctionFieldMemValuationSubringValuationSubringWithZeroMultiplicativeIntValuationInfty WeierstrassCurve.Affine.valuationInfty_isNontrivial WeierstrassCurve.veluQuotient2_isShortNF WeierstrassCurve.instIsShortNFMk"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.Gamma0Pair.map_toCurve WeierstrassCurve.mapPoint_eq_ratPointMap ModularCurve.Gamma0Pair.map_gen ModularCurve.Gamma0Pair.map_eq_gamma0PairMap ModularCurve.ModuliPoint.map_eq_moduliPointMapRingHom ModularCurve.ModuliPoint.map_mk WeierstrassCurve.mapPointHom_apply"
p2m_attr_erase "simp" "WeierstrassCurve.mapPoint_zero AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.Affine.Point.coordsOrZero_some"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff ModularCurve.ProjectiveLine.map_mk ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ WeierstrassCurve.veluX_empty WeierstrassCurve.vcInvEmbedding_apply ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU"
p2m_attr_erase "simp" "ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.veluY_empty WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ"
p2m_attr_erase "simp" "TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero ModularCurve.cuspCount_one WeierstrassCurve.Universal.halveX_zero WeierstrassCurve.Universal.specialize_X_one WeierstrassCurve.Universal.coeff_halve WeierstrassCurve.Universal.specialize_X_two WeierstrassCurve.Universal.halveCoeff_zero WeierstrassCurve.Universal.specialize_X_four WeierstrassCurve.Universal.coeff_halveX WeierstrassCurve.Universal.specialize_X_three WeierstrassCurve.Universal.specialize_X_zero HahnSeries.ramScale_apply"
p2m_attr_erase "simp" "ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ ModularCurve.coe_nodeEquiv_symm_apply ModularCurve.frobNodePair_jOfNode ModularCurve.jOfNode_mk ModularCurve.widthOf_mk ModularCurve.frobNodePairEmb_apply ModularCurve.card_nodePairsOf ModularCurve.frobNodePair_snd ModularCurve.coe_nodeEquiv_apply ModularCurve.frobNodePair_fst ModularCurve.NodeLocalized.coe_modularEvalAt AdicCompletion.evalₐ_mapₐ AdicCompletion.mapAlgEquivOfBijective_apply AdicCompletion.levelMapₐ_mk AdicCompletion.mapₐ_of AdicCompletion.mapAlgEquiv_symm_apply AdicCompletion.mapAlgEquiv_apply AdicCompletion.evalₐ_ofLevelwiseEquiv AdicCompletion.evalₐ_levelwiseHom AdicCompletion.localizationEquiv_of AdicCompletion.evalₐ_ofLevelwiseEquiv_symm Localization.AtPrime.quotientPowEquiv_mk ModularCurve.LambdaModularPolynomialData.mk.sizeOf_spec ModularCurve.LambdaModularPolynomialData.mk.injEq AdicCompletion.transportOf_of AdicCompletion.selfCompletion_smul_of"
p2m_attr_erase "simp" "AdicCompletion.tensorRingEquiv_tmul AdicCompletion.completionOfAlgHom_apply AdicCompletion.completionBaseChangeHom_of AdicCompletion.tensorRingHom_tmul AdicCompletion.stabilizerToCompletionAut_of AlgebraicCurve.Pic.baseChange_mk AlgebraicCurve.Place.forgetConstants_toValuationSubring AlgebraicCurve.Place.constantFieldEquiv_symm_apply AlgebraicCurve.Place.ord_forgetConstants AlgebraicCurve.Place.extendConstants_toValuationSubring AlgebraicCurve.Place.constantFieldEquiv_apply_toValuationSubring AlgebraicCurve.Place.mem_fiberConstants AlgebraicCurve.Place.restrictConstants_toValuationSubring AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule"
p2m_attr_erase "simp" "AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL GoodReductionJacobian.RelativePic0Designation.mk.sizeOf_spec GoodReductionJacobian.AvatarSchemeBridge.mk.injEq MilneJVScheme.JacobianSchemeData.mk.injEq GoodReductionJacobian.AvatarSchemeBridge.mk.sizeOf_spec MilneJVScheme.JacobianSchemeData.mk.sizeOf_spec GoodReductionJacobian.RelativePic0Designation.mk.injEq NeronModelInfra.specGenericFibreInclusion_eq NeronModelInfra.genericFibreRestrict_coe_comp_snd NeronModelInfra.genericFibreRestrict_coe_comp_fst GoodReductionJacobian.schemeHomOverComp_coe NeronModelInfra.schemeHomOverEquivOverHom_apply GoodReductionJacobian.RelativeGroupLaw.mk.sizeOf_spec NeronModelInfra.schemeHomOverEquivOverHom_symm_apply NeronModelInfra.overHomToSchemeHomOver_coe GoodReductionJacobian.RelativeGroupLaw.mk.injEq NeronModelInfra.overHomToSchemeHomOver_schemeHomOverToOverHom NeronModelInfra.schemeHomOverToOverHom_left NeronModelInfra.schemeHomOverToOverHom_overHomToSchemeHomOver NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe GaloisRepAdic.mk.injEq GaloisRepAdic.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.injEq"
p2m_attr_erase "simp" "ResidualGaloisRep.mk.sizeOf_spec ResidualGaloisRep.mk.injEq ResidualGaloisRep.Equiv.mk.sizeOf_spec ResidualGaloisRep.Equiv.mk.injEq AlgebraicCurve.CurveModel.mk.injEq AlgebraicCurve.CurveModel.mk.sizeOf_spec ModularCurve.CharPModel.FibreModel.mk.injEq ModularCurve.CharPModel.FibreModel.mk.sizeOf_spec ModularCurve.IgusaScheme.ιInf_igusaTo_assoc ModularCurve.IgusaScheme.coe_jFull ModularCurve.IgusaScheme.coe_jInvChartInf ModularCurve.IgusaScheme.coe_jChartFin ModularCurve.IgusaScheme.ιFin_igusaTo ModularCurve.IgusaScheme.ιInf_igusaTo ModularCurve.IgusaScheme.ιFin_igusaTo_assoc AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces ModularCurve.PlaceSpecialization.LevelOneProlongationPair.mk.sizeOf_spec ModularCurve.PlaceSpecialization.LevelOneProlongationPair.residue₂_apply ModularCurve.PlaceSpecialization.LevelOneProlongationPair.residue₁_apply ModularCurve.PlaceSpecialization.LevelOneProlongationPair.mk.injEq ModularCurve.symPoly_zero ModularCurve.frobeniusPullbackGeomLevelUnconditional_single ModularCurve.frobeniusPushforwardGeomLevelUnconditional_single ModularCurve.frobeniusGeomLevelUnconditional_apply_coe AlgebraicCurve.GaussReduction.constToGauss_coe AlgebraicCurve.ComponentChart.ofConstantReductionNodes_dom AlgebraicCurve.ComponentChart.ofConstantReductionNodes_placeMap AlgebraicCurve.ComponentChart.ofConstantReductionNodes_nodes AlgebraicCurve.ComponentChart.ofConstantReductionNodes_residue AlgebraicCurve.ComponentChart.ofConstantReductionNodes_integers"
p2m_attr_erase "simp" "ModularCurve.FinitePlaceLift.traceHom_coe ModularCurve.FinitePlaceLift.mk.injEq ModularCurve.FinitePlaceLift.mk.sizeOf_spec AlgebraicCurve.ComponentChart.ofConstantReduction_integers AlgebraicCurve.ComponentChart.mk.sizeOf_spec AlgebraicCurve.ComponentChart.ofConstantReduction_placeMap AlgebraicCurve.ComponentChart.ofConstantReduction_nodes AlgebraicCurve.ComponentChart.mk.injEq AlgebraicCurve.ComponentChart.ofConstantReduction_dom AlgebraicCurve.Annulus.mk.sizeOf_spec AlgebraicCurve.Annulus.mk.injEq ModularCurve.PlaceSpecialization.LevelOneProlongationPair.coe_gaussOrderToIntegers₂ ModularCurve.PlaceSpecialization.LevelOneProlongationPair.coe_gaussOrderToIntegers₁ ModularCurve.PlaceSpecialization.LevelOneProlongationPair.coe_toIntegers₁ ModularCurve.PlaceSpecialization.LevelOneProlongationPair.coe_constToGaussBase ModularCurve.PlaceSpecialization.LevelOneProlongationPair.coe_toIntegers₂ ModularCurve.coe_levelPolynomialEquiv_apply ModularCurve.coe_levelBaseRingDescent_apply ModularCurve.levelConst_apply ModularCurve.coe_laurentDescent_apply ModularCurve.dualHeckeRep_apply_apply ModularCurve.coe_segmentPath ModularCurve.cuspHeckeAeval_heckeGen ModularCurve.coe_periodLatticeRestrict_apply CuspForm.heckeAlgebra.coe_U CuspForm.heckeAlgebra.coe_T ModularForm.coe_heckeTLin_apply CuspForm.coe_heckeULin_apply CuspForm.coe_heckeTLin_apply ModularForm.coe_heckeULin_apply ModularCurve.ComplexPlaceDictionary.mk.injEq ModularCurve.ComplexPlaceDictionary.mk.sizeOf_spec ModularCurve.Period.IsEquivariantPrimitive.periodHom_apply ModularCurve.Period.IsEquivariantPrimitive.period_one ModularCurve.CuspSpace.cuspDenomAux_infty ModularCurve.CuspSpace.cuspDenomAux_coe ModularCurve.CuspSpace.cuspDenom_mk_zero ModularCurve.CuspSpace.cuspDenom_mk_infty ModularCurve.mapGL_apply_coe ModularCurve.ratPoint_one_zero"
p2m_attr_erase "simp" "ModularCurve.ratPoint_zero_right ModularCurve.CuspSpace.fromCoset_mk ModularCurve.CuspSpace.cuspDenom_mk ModularCurve.ratPoint_zero_one ModularCurve.qEulerFun_coeff ModularCurve.diffQExp_D ModularCurve.qEulerOn_apply ModularCurve.qEuler_coeff FLT.TruncatedDomainPartition.unipotentDiagonalSum_zero HeckeEis.coeffCoboundaryMap_apply HeckeEis.heckeConjMat_apply_one_one HeckeEis.coe_heckeConjSL HeckeEis.mem_heckeUpperSL HeckeEis.resHom_apply HeckeEis.heckeConjMat_apply_zero_one HeckeEis.coe_transferAux HeckeEis.coe_heckeConj HeckeEis.alphaMat_apply_one_one HeckeEis.heckeConjMat_apply_one_zero HeckeEis.alphaMat_apply_zero_one HeckeEis.pullbackHom_apply HeckeEis.alphaMat_apply_one_zero HeckeEis.alphaMat_apply_zero_zero HeckeEis.heckeConjMat_apply_zero_zero AlgebraicCurve.abelJacobiDiv_single AlgebraicCurve.AnalyticCoord.mk.injEq AlgebraicCurve.Cell.mk.sizeOf_spec AlgebraicCurve.RadialRegion.mk.sizeOf_spec AlgebraicCurve.RadialRegion.mk.injEq AlgebraicCurve.CellDissection.mk.sizeOf_spec AlgebraicCurve.Cell.mk.injEq AlgebraicCurve.CellDissection.mk.injEq AlgebraicCurve.AnalyticCoord.mk.sizeOf_spec AddMonoid.End.dualEndDataOfSurjective_trace AddMonoid.End.dualEndDataOfSurjective_norm"
set_option autoImplicit false
p2m_open "AlgebraicCurve IsLocalRing ModularCurve~period"

namespace Comp554

def diffVec {ι : Type*} [Fintype ι] [DecidableEq ι] (s₀ i : ι) : characterLattice ι :=
  ⟨Pi.single i 1 - Pi.single s₀ 1, by
    rw [mem_characterLattice]
    simp [Finset.sum_sub_distrib]⟩

@[scoped simp] theorem diffVec_coe {ι : Type*} [Fintype ι] [DecidableEq ι] (s₀ i : ι) :
    ((diffVec s₀ i : characterLattice ι) : ι → ℤ) = Pi.single i 1 - Pi.single s₀ 1 := rfl

theorem gramMap_diffVec_apply {ι : Type*} [Fintype ι] [DecidableEq ι] (e : ι → ℕ) (s₀ i : ι)
    (D : characterLattice ι) :
    gramMap e (diffVec s₀ i) D = (e i : ℤ) * D.1 i - (e s₀ : ℤ) * D.1 s₀ := by
  rw [gramMap_apply]
  simp only [diffVec_coe, Pi.sub_apply, sub_mul, mul_sub, Finset.sum_sub_distrib]
  simp [Pi.single_apply]

theorem dualMap_vertex_sub_eq_sum {ι : Type*} [Fintype ι] [DecidableEq ι]
    (e : ι → ℕ) (B : Matrix ι ι ℤ) {n : ℤ} (hrow : HeckeRowSums B n) (hsym : HeckeWeightSymm e B)
    (s₀ : ι) :
    (heckeCharacterAction B hrow).dualMap ((e s₀ : ℤ) • crossingCoord s₀) -
        n • ((e s₀ : ℤ) • crossingCoord s₀) =
      ∑ i : ι, B s₀ i • gramMap e (diffVec s₀ i) := by
  apply LinearMap.ext
  intro D
  simp only [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.dualMap_apply, crossingCoord_apply,
    heckeCharacterAction_coe, heckeDivisorAction_apply, LinearMap.coe_sum, Finset.sum_apply,
    gramMap_diffVec_apply, smul_eq_mul]
  rw [← hrow s₀, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun i _ => by linear_combination ((D : ι → ℤ) i) * hsym i s₀

theorem componentGroupProj_eq_zero_of_mem {ι : Type*} [Fintype ι] (e : ι → ℕ)
    {x : Module.Dual ℤ (characterLattice ι)} (hx : x ∈ LinearMap.range (gramMap e)) :
    componentGroupProj e x = 0 := by
  show Submodule.Quotient.mk x = (0 : componentGroup e)
  exact (Submodule.Quotient.mk_eq_zero _).mpr hx

theorem componentGroupProj_eq_of_sub_mem {ι : Type*} [Fintype ι] (e : ι → ℕ)
    {x y : Module.Dual ℤ (characterLattice ι)} (h : x - y ∈ LinearMap.range (gramMap e)) :
    componentGroupProj e x = componentGroupProj e y := by
  rw [← sub_eq_zero, ← map_sub]
  exact componentGroupProj_eq_zero_of_mem e h

theorem componentGroupProj_dualMap_vertex {ι : Type*} [Fintype ι]
    (e : ι → ℕ) (B : Matrix ι ι ℤ) {n : ℤ} (hrow : HeckeRowSums B n) (hsym : HeckeWeightSymm e B)
    (s₀ : ι) :
    componentGroupProj e ((heckeCharacterAction B hrow).dualMap ((e s₀ : ℤ) • crossingCoord s₀)) =
      n • componentGroupProj e ((e s₀ : ℤ) • crossingCoord s₀) := by
  classical
  rw [← LinearMap.map_smul_of_tower]
  apply componentGroupProj_eq_of_sub_mem
  rw [dualMap_vertex_sub_eq_sum e B hrow hsym s₀]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (LinearMap.mem_range_self _ _)

theorem heckeComponentAction_proj_zsmul_vertex {ι : Type*} [Fintype ι]
    (e : ι → ℕ) (B : Matrix ι ι ℤ) {n : ℤ} (hrow : HeckeRowSums B n) (hsym : HeckeWeightSymm e B)
    (s₀ : ι) (m : ℤ) :
    heckeComponentAction e B hrow hsym (componentGroupProj e (m • ((e s₀ : ℤ) • crossingCoord s₀))) =
      (n * m) • componentGroupProj e ((e s₀ : ℤ) • crossingCoord s₀) := by
  rw [componentGroupProj_heckeComponentAction, LinearMap.map_smul_of_tower, LinearMap.map_smul_of_tower,
    componentGroupProj_dualMap_vertex e B hrow hsym s₀, smul_smul, mul_comm]

theorem smul_comb {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] (a b b₁ k : R) (c : M) :
    (a - k * b) • c = (a - k * b₁) • c - k • ((b - b₁) • c) := by
  module

theorem componentGroupProj_smul_eq_of_sub_smul_mem {ι : Type*} [Fintype ι] (e : ι → ℕ)
    {a b : ℤ} {v : Module.Dual ℤ (characterLattice ι)} (h : (a - b) • v ∈ LinearMap.range (gramMap e)) :
    componentGroupProj e (a • v) = b • componentGroupProj e v := by
  rw [← LinearMap.map_smul_of_tower]
  rw [sub_smul] at h
  exact componentGroupProj_eq_of_sub_mem e h

end Comp554
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_componentGroupProj_depthDual_add_eq_heckeComponentAction_of_heckeGen_smul.Comp554"

namespace Comp554

section DivisorBookkeeping

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
  {k : Type*} [Field k] [CharP k q] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
  {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
  (P : PlaceSpecialization A q N data hKr k red hα hβ)

theorem sndDiv_sub (D E : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) :
    P.sndDiv (D - E) = P.sndDiv D - P.sndDiv E := by
  classical
  unfold PlaceSpecialization.sndDiv
  exact map_sub (Finsupp.filterAddHom _) D E

theorem isGoodDiv_sub {D E : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))}
    (hD : P.IsGoodDiv D) (hE : P.IsGoodDiv E) : P.IsGoodDiv (D - E) := by
  classical
  intro V hV
  rw [sub_eq_add_neg] at hV
  rcases Finset.mem_union.mp (Finsupp.support_add hV) with h | h
  · exact hD V h
  · exact hE V (by rwa [Finsupp.support_neg] at h)

theorem reduceFst_notMem_of_strict {W : Finset (Place k (modularFunctionFieldC k N))}
    (hWfix : ∀ w ∈ W, frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr w) = w)
    {V : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))}
    (hV : P.IsStrictFst V ∨ P.IsStrictSnd V) : P.reduceFst V ∉ W := fun hmem =>
  ((PlaceSpecialization.isStrictFst_or_isStrictSnd_iff P V).mp hV) (hWfix _ hmem)

theorem not_isStrictSnd_of_isStrictFst {V : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))}
    (h : P.IsStrictFst V) : ¬ P.IsStrictSnd V := fun h' =>
  h.2 (by rw [h.1, ← h'.1])

theorem fstDiv_add_sndDiv_of_isGoodDiv {D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))}
    (hD : P.IsGoodDiv D) : P.fstDiv D + P.sndDiv D = D := by
  classical
  unfold PlaceSpecialization.fstDiv PlaceSpecialization.sndDiv
  ext V
  rw [Finsupp.add_apply, Finsupp.filter_apply, Finsupp.filter_apply]
  by_cases hV : V ∈ D.support
  · rcases hD V hV with h | h
    · rw [if_pos h, if_neg (not_isStrictSnd_of_isStrictFst P h), add_zero]
    · rw [if_neg (fun h' => not_isStrictSnd_of_isStrictFst P h' h), if_pos h, zero_add]
  · rw [Finsupp.notMem_support_iff.mp hV]
    simp

end DivisorBookkeeping
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_componentGroupProj_depthDual_add_eq_heckeComponentAction_of_heckeGen_smul.Comp554"

section Grain

theorem one_le_of_eq_pow_mul_unit {R k : Type*} [CommRing R] [Field k] (f : R →+* k)
    {x ϖ ε : R} {n : ℕ} (hε : IsUnit ε) (h : x = ϖ ^ n * ε) (hx : f x = 0) : 1 ≤ n := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    rw [pow_zero, one_mul] at h
    subst h
    exact absurd (hε.map f) (by rw [hx]; exact not_isUnit_zero)
  · exact hn

theorem mk_eq_mk_of_isPrincipal_sub {K F : Type*} [Field K] [Field F] [Algebra K F]
    {D D₁ : ↥(Divisor.degZero (K := K) (F := F))}
    (h : Divisor.IsPrincipal ((D : Divisor K F) - (D₁ : Divisor K F))) : Pic0.mk D = Pic0.mk D₁ := by
  unfold Pic0.mk
  refine QuotientAddGroup.eq.mpr ?_
  rw [AddSubgroup.mem_addSubgroupOf]
  have hc : ((-D + D₁ : ↥(Divisor.degZero (K := K) (F := F))) : Divisor K F) =
      -((D : Divisor K F) - (D₁ : Divisor K F)) := by
    push_cast
    abel
  rw [hc]
  exact neg_mem (show ((D : Divisor K F) - (D₁ : Divisor K F)) ∈ Divisor.principal from h)

theorem isPrincipal_sub_of_mk_eq_mk {K F : Type*} [Field K] [Field F] [Algebra K F]
    {D D₁ : ↥(Divisor.degZero (K := K) (F := F))} (h : Pic0.mk D = Pic0.mk D₁) :
    Divisor.IsPrincipal ((D₁ : Divisor K F) - (D : Divisor K F)) := by
  unfold Pic0.mk at h
  have h' := QuotientAddGroup.eq.mp h
  rw [AddSubgroup.mem_addSubgroupOf] at h'
  have hc : ((-D + D₁ : ↥(Divisor.degZero (K := K) (F := F))) : Divisor K F) =
      (D₁ : Divisor K F) - (D : Divisor K F) := by
    push_cast
    abel
  rw [hc] at h'
  exact h'

theorem heckeGen_smul_mk (M : ℕ) [NeZero M] (ℓ : Nat.Primes)
    (D : ↥(Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar M)))) :
    haveI : NeZero (ℓ : ℕ) := ⟨ℓ.2.ne_zero⟩
    haveI : HasPrincipalDivisors (AlgebraicClosure ℚ) (modularFunctionFieldBar (M * (ℓ : ℕ))) :=
      hasPrincipalDivisors_modularFunctionFieldBar_unconditional (M * (ℓ : ℕ))
    ∀ (hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) M ℓ)
      (hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) M ℓ),
      ∃ E : ↥(Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar M))),
        (E : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar M)) =
            heckeDivBar hα hβ (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar M)) ∧
          (letI := heckeModuleBar M; heckeGen ℓ • (Pic0.mk D : JZero M)) = Pic0.mk E := by
  haveI : NeZero (ℓ : ℕ) := ⟨ℓ.2.ne_zero⟩
  haveI : Fact (ℓ : ℕ).Prime := ⟨ℓ.2⟩
  haveI : HasPrincipalDivisors (AlgebraicClosure ℚ) (modularFunctionFieldBar (M * (ℓ : ℕ))) :=
    hasPrincipalDivisors_modularFunctionFieldBar_unconditional (M * (ℓ : ℕ))
  intro hα hβ
  have hin := heckeInputsAlong_of_prime (AlgebraicClosure ℚ) M (ℓ : ℕ)
  obtain ⟨hα', hβ', hP', hfin', hFI', hN'⟩ := hin
  refine ⟨Pic0.degZeroCorrespondence (heckeBetaBar (AlgebraicClosure ℚ) M (ℓ : ℕ))
    (heckeAlphaBar (AlgebraicClosure ℚ) M (ℓ : ℕ)) hβ' hα' hFI' D, rfl, ?_⟩
  refine (heckeModuleBar_heckeGen_smul (heckeOperatorsCommuteBar M) ℓ (Pic0.mk D)).trans ?_
  haveI := hP'
  rw [heckeOperatorBar_apply, heckeOperatorAlong_eq hα' hβ' hFI' hfin' hN']
  rfl

theorem degree_heckeDivBar (M : ℕ) [NeZero M] (ℓ : Nat.Primes) (hℓ : ¬ (ℓ : ℕ) ∣ M) :
    haveI : NeZero (ℓ : ℕ) := ⟨ℓ.2.ne_zero⟩
    ∀ (hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) M ℓ)
      (hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) M ℓ)
      [HasPrincipalDivisors (AlgebraicClosure ℚ) (modularFunctionFieldBar (M * (ℓ : ℕ)))]
      (X : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar M)),
      Divisor.degree (heckeDivBar hα hβ X) = ((((ℓ : ℕ) : ℤ)) + 1) * Divisor.degree X := by

  haveI : NeZero (ℓ : ℕ) := ⟨ℓ.2.ne_zero⟩
  haveI : Fact (ℓ : ℕ).Prime := ⟨ℓ.2⟩
  intro hα hβ _ X
  obtain ⟨hα', hβ', hP', hfin', hFI', hN'⟩ := heckeInputsAlong_of_prime (AlgebraicClosure ℚ) M (ℓ : ℕ)
  have h := Divisor.degree_correspondence (heckeBetaBar (AlgebraicClosure ℚ) M (ℓ : ℕ))
    (heckeAlphaBar (AlgebraicClosure ℚ) M (ℓ : ℕ)) hβ hα hFI' X
  rw [finrankAlong_heckeBetaBar, if_neg hℓ] at h
  rw [heckeDivBar, h]
  push_cast
  ring

end Grain
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_componentGroupProj_depthDual_add_eq_heckeComponentAction_of_heckeGen_smul.Comp554"

end Comp554
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_componentGroupProj_depthDual_add_eq_heckeComponentAction_of_heckeGen_smul.Comp554"

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in
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
      (R : PlaceSpecialization.ProlongationTuple P) (hmodel : R.IsModel) (hO : R.OrderLawFixed)
      (hreg : R.RegularityLaw W)
      (e : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) N) → ℕ)
      (he : ∀ w ∈ W, e w = placeWidthChar q N w)
      (depth : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) → ℕ)
      (hdepth :
        (∀ w ∈ W, ∃ (K : IntermediateField ℚ (AlgebraicClosure ℚ)) (_ : FiniteDimensional ℚ K)
          (xw : ↥(NodeLocalized.coeffSubring A K))
          (_ : NodeLocalized.redRestrict (IsLocalRing.residue A) K xw = w.evalAt (jGeomGen (ResidueField A) N))
          (ϖ : ↥(NodeLocalized.coeffSubring A K))
          (_ : ∀ d : ↥(NodeLocalized.coeffSubring A K),
            NodeLocalized.redRestrict (IsLocalRing.residue A) K d = 0 ↔ ∃ d', d = ϖ * d')
          (eK : ℕ) (ε : ↥(NodeLocalized.coeffSubring A K)) (_ : IsUnit ε)
          (_ : ((q : ℕ) : ↥(NodeLocalized.coeffSubring A K)) = ϖ ^ eK * ε)
          (c : R.NodeCoordinates K w) (E : ℕ) (u : ↥(R.nodeIntegersOver K w)) (_ : IsUnit u)
          (_ : ∀ g g' : ↥(R.nodeIntegersOver K w),
            0 < w.ord (R.nodeResidue₁ w ⟨g, g.2.1⟩) → w.ord (R.nodeResidue₁ w ⟨g', g'.2.1⟩) = 1 →
            ∃ b : ↥(R.nodeIntegersOver K w),
              R.nodeResidue₁ w ⟨g, g.2.1⟩ = R.nodeResidue₁ w ⟨g', g'.2.1⟩ * R.nodeResidue₁ w ⟨b, b.2.1⟩)
          (_ : ∀ g g' : ↥(R.nodeIntegersOver K w),
            0 < (arithFrobC q (ResidueField A) N • w).ord (R.nodeResidue₂ w ⟨g, g.2.1⟩) →
            (arithFrobC q (ResidueField A) N • w).ord (R.nodeResidue₂ w ⟨g', g'.2.1⟩) = 1 →
            ∃ b : ↥(R.nodeIntegersOver K w),
              R.nodeResidue₂ w ⟨g, g.2.1⟩ = R.nodeResidue₂ w ⟨g', g'.2.1⟩ * R.nodeResidue₂ w ⟨b, b.2.1⟩),
          c.x * c.y = R.nodeConst K w ϖ ^ E * u ∧ c.DepthValueLaw depth))
      (ℓ : Nat.Primes) (hℓ : ¬ (ℓ : ℕ) ∣ N * q)
      (B : Matrix ↥(nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W)
        ↥(nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W) ℤ)
      (hB : haveI : NeZero (ℓ : ℕ) := ⟨ℓ.2.ne_zero⟩;
        ∀ [HasPrincipalDivisors (ResidueField A) (charLDegeneracyRoof (ResidueField A) N ℓ)]
          (hαc : HeckeAlphaCIntegral (ResidueField A) N ℓ) (hβc : HeckeBetaCIntegral (ResidueField A) N ℓ)
          (s t : ↥(nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W)),
          B t s = Divisor.correspondence (heckeAlphaC (ResidueField A) N ℓ) (heckeBetaC (ResidueField A) N ℓ) hαc hβc
            (Finsupp.single t.1.1 1) s.1.1)
      (hrow : HeckeRowSums B (((ℓ : ℕ) : ℤ) + 1))
      (hsym : HeckeWeightSymm (widthOfPlaces (arithFrobC q (ResidueField A) N) W e) B)
      (D D' : ↥(Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar (N * q)))))
      (hD : ∀ V ∈ (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))).support,
        (∀ σ ∈ A.inertiaSubgroupIn ℚ,
            arithmeticGalois (modularFunctionFieldFull (N * q)) σ • V = V) ∧
          (P.IsStrictFst V ∨ P.IsStrictSnd V ∨ P.reduceFst V ∈ W))
      (hD' : ∀ V ∈ (D' : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))).support,
        (∀ σ ∈ A.inertiaSubgroupIn ℚ,
            arithmeticGalois (modularFunctionFieldFull (N * q)) σ • V = V) ∧
          (P.IsStrictFst V ∨ P.IsStrictSnd V ∨ P.reduceFst V ∈ W))
      (hT :
        (letI := heckeModuleBar (N * q); heckeGen ℓ • (Pic0.mk D : JZero (N * q))) = Pic0.mk D')
      (s₀ : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) N) ×
        Place (ResidueField A) (modularFunctionFieldC (ResidueField A) N))
      (hs₀ : s₀ ∈ nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W),
      componentGroupProj (widthOfPlaces (arithFrobC q (ResidueField A) N) W e)
          (P.depthDual (arithFrobC q (ResidueField A) N) W depth
              (D' : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) +
            Divisor.degree (P.sndDiv (D' : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)))) •
              ((e s₀.1 : ℤ) • crossingCoord
                (⟨s₀, hs₀⟩ : ↥(nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W)))) =
        heckeComponentAction (widthOfPlaces (arithFrobC q (ResidueField A) N) W e) B hrow hsym
          (componentGroupProj (widthOfPlaces (arithFrobC q (ResidueField A) N) W e)
            (P.depthDual (arithFrobC q (ResidueField A) N) W depth
                (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) +
              Divisor.degree (P.sndDiv (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)))) •
                ((e s₀.1 : ℤ) • crossingCoord
                  (⟨s₀, hs₀⟩ : ↥(nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W))))) := by
  intro W hW data hKr hα hβ P R hmodel hO hreg e he depth hdepth ℓ hℓ B hB hrow hsym D D' hD hD' hT s₀ hs₀
  haveI : NeZero q := ⟨hq.ne_zero⟩
  haveI : Fact q.Prime := ⟨hq⟩
  haveI : CharP (ResidueField A) q := ValuationSubring.charP_residueField_of_liesOverPrime_def hq hA
  letI := instDecidableEqResidueFieldSemistable A
  letI := instAlgebraResidueFieldModularFunctionFieldCSemistable A N
  haveI : IsAlgClosed (ResidueField A) := ValuationSubring.isAlgClosed_residueField A
  haveI : NeZero (ℓ : ℕ) := ⟨ℓ.2.ne_zero⟩
  haveI : Fact (ℓ : ℕ).Prime := ⟨ℓ.2⟩
  have hℓq : (ℓ : ℕ) ≠ q := by
    intro h
    apply hℓ
    rw [h]
    exact dvd_mul_left q N
  have hℓNq : ¬ (ℓ : ℕ) ∣ N * q := hℓ
  have hWss : ∀ w ∈ W, w ∈ ssPlaces q N (ResidueField A) := fun w hw => (hW w).1 hw
  have hWfix : ∀ w ∈ W, frobOnPlacesGeomLevel (ResidueField A) N data hKr
      (frobOnPlacesGeomLevel (ResidueField A) N data hKr w) = w := fun w hw =>
    PlaceSpecialization.frobOnPlacesGeomLevel_frobOnPlacesGeomLevel_eq_self_of_mem_ssPlaces hqN P w (hWss w hw)
  have hker : ∀ c : ↥A, IsLocalRing.residue ↥A c = 0 ↔ c ∈ IsLocalRing.maximalIdeal ↥A :=
    fun c => IsLocalRing.residue_eq_zero_iff c
  have hval : R.NodeValueLaw W :=
    PlaceSpecialization.ProlongationTuple.nodeValueLaw_of_regularityLaw P hqN hW R hreg

  have hnofix : (∀ w ∈ W, e w = 1) → ∀ V : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)),
      (∀ σ ∈ A.inertiaSubgroupIn ℚ, arithmeticGalois (modularFunctionFieldFull (N * q)) σ • V = V) →
        P.reduceFst V ∈ W → False := fun hw1 V hfix hVW => by
    obtain ⟨K, hKfin, xw, hxw, ϖ, hϖ, eK, ε, hε, hqϖ, c, E, u, hu, -, -, hxy, hDVL⟩ := hdepth _ hVW
    haveI := hKfin
    have hvalA := PlaceSpecialization.ProlongationTuple.valueIntegralityLaw_of_orderLawFixed R hqN hO _ (hWss _ hVW)
    have hE := PlaceSpecialization.ProlongationTuple.crossingExponent_eq_placeWidthChar_mul_of_orderLawFixed R hqN
      hmodel W hWss hreg hval hO hker K _ hVW xw hxw ϖ hϖ eK ε hε hqϖ c E u hu hxy
    rw [hE] at hxy
    have hlt := PlaceSpecialization.ProlongationTuple.NodeCoordinates.depth_lt_of_depthValueLaw_of_nodeEquation hA R
      hqN hmodel hO W hWss hreg hval K _ hVW hvalA ϖ eK ε hε hqϖ c _ u hu hxy depth hDVL V rfl hfix
    have hpos := PlaceSpecialization.ProlongationTuple.NodeCoordinates.depth_pos_of_depthValueLaw_of_nodeEquation hA R
      hqN hmodel hO W hWss hreg hval K _ hVW hvalA ϖ eK ε hε hqϖ c _ u hu hxy depth hDVL V rfl hfix
    rw [← he _ hVW, hw1 _ hVW] at hlt
    omega

  by_cases hq5 : 5 ≤ q
  swap
  ·
    have hRES := ModularCurve.PlaceSpecialization.componentGroupProj_depthDual_add_eq_heckeComponentAction_of_heckeGen_smul_of_lt_five N q hq hqN A hA
    exact hRES W hW data hKr hα hβ P R hmodel hO hreg e he depth hdepth ℓ hℓ B hB hrow hsym D D' hD hD' hT s₀ hs₀ (not_le.mp hq5)
  by_cases hgood :
      P.IsGoodDiv (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) ∧
        P.IsGoodDiv (D' : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)))
  swap
  · by_cases hw1 : ∀ w ∈ W, e w = 1
    ·
      exact absurd ⟨fun V hV => (hD V hV).2.elim Or.inl fun h => h.elim Or.inr fun hVW =>
          (hnofix hw1 V (hD V hV).1 hVW).elim,
        fun V hV => (hD' V hV).2.elim Or.inl fun h => h.elim Or.inr fun hVW =>
          (hnofix hw1 V (hD' V hV).1 hVW).elim⟩ hgood
    ·
      have hANN := ModularCurve.PlaceSpecialization.componentGroupProj_depthDual_add_eq_heckeComponentAction_of_heckeGen_smul_of_five_le_of_not_isGoodDiv N q hq hqN A hA
      exact hANN W hW data hKr hα hβ P R hmodel hO hreg e he depth hdepth ℓ hℓ B hB hrow hsym D D' hD hD' hT s₀ hs₀ hq5 hgood hw1
  obtain ⟨hgD, hgD'⟩ := hgood

  have h0 := PlaceSpecialization.depthDual_eq_zero_of_isGoodDiv P (arithFrobC q (ResidueField A) N) W hWfix depth
    (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) hgD
  have h0' := PlaceSpecialization.depthDual_eq_zero_of_isGoodDiv P (arithFrobC q (ResidueField A) N) W hWfix depth
    (D' : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) hgD'

  have halg := Comp554.heckeComponentAction_proj_zsmul_vertex
    (widthOfPlaces (arithFrobC q (ResidueField A) N) W e) B hrow hsym ⟨s₀, hs₀⟩
    (Divisor.degree (P.sndDiv (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)))))
  simp only [widthOfPlaces_apply] at halg

  simp only [h0, h0', zero_add]
  refine Eq.trans ?_ halg.symm

  suffices hG2 :
      (Divisor.degree (P.sndDiv (D' : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)))) -
          ((((ℓ : ℕ) : ℤ)) + 1) * Divisor.degree (P.sndDiv (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))))) •
        ((e s₀.1 : ℤ) • crossingCoord
          (⟨s₀, hs₀⟩ : ↥(nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W))) ∈
      LinearMap.range (gramMap (widthOfPlaces (arithFrobC q (ResidueField A) N) W e)) by
    exact Comp554.componentGroupProj_smul_eq_of_sub_smul_mem _ hG2

  haveI hPD : HasPrincipalDivisors (AlgebraicClosure ℚ) (modularFunctionFieldBar ((N * q) * (ℓ : ℕ))) :=
    hasPrincipalDivisors_modularFunctionFieldBar_unconditional ((N * q) * (ℓ : ℕ))
  have hαℓ : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) (N * q) ℓ :=
    heckeAlphaBarIntegral_of_prime (AlgebraicClosure ℚ) (N * q) ℓ
  have hβℓ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) (N * q) ℓ :=
    heckeBetaBarIntegral_of_prime (AlgebraicClosure ℚ) (N * q) ℓ

  have hKIND :
      ∃ D₁ : ↥(Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar (N * q)))),
        P.IsGoodDiv (D₁ : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) ∧
        Divisor.IsPrincipal ((D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) -
          (D₁ : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)))) ∧
        P.IsGoodDiv (heckeDivBar hαℓ hβℓ
          (D₁ : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)))) ∧
        P.sndDiv (heckeDivBar hαℓ hβℓ
            (D₁ : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)))) =
          heckeDivBar hαℓ hβℓ
            (P.sndDiv (D₁ : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)))) := by

    have h13 :=
      PlaceSpecialization.exists_rep_eq_off_strict_reduce_notMem_heckeDivBar_strictPart_good_kindResp_of_isModel N q hq
        hqN A hA W hW data hKr hα hβ P R hmodel hreg hval hO ℓ hℓq hαℓ hβℓ ∅ D
    obtain ⟨D₁, hmk₁, hoff, -, hgT₁, -, hsndT₁⟩ := h13
    have hgD₁ : P.IsGoodDiv (D₁ : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) := fun V hV => by
      by_contra h
      refine (Finsupp.mem_support_iff.mp hV) ?_
      rw [hoff V h]
      exact Finsupp.notMem_support_iff.mp fun hV' => h (hgD V hV')
    rw [Comp554.fstDiv_add_sndDiv_of_isGoodDiv P hgD₁] at hgT₁ hsndT₁
    exact ⟨D₁, hgD₁, Comp554.isPrincipal_sub_of_mk_eq_mk hmk₁, hgT₁, hsndT₁⟩
  obtain ⟨D₁, hgD₁, hpr₁, hgT₁, hsndT₁⟩ := hKIND

  have hS1 := Comp554.heckeGen_smul_mk (N * q) ℓ D₁ hαℓ hβℓ
  obtain ⟨E₁, hE₁, hTE₁⟩ := hS1
  have hmk : Pic0.mk D = Pic0.mk D₁ := Comp554.mk_eq_mk_of_isPrincipal_sub hpr₁
  have hpr' : Divisor.IsPrincipal
      ((D' : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) -
        heckeDivBar hαℓ hβℓ (D₁ : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)))) := by
    rw [← hE₁]
    exact Comp554.isPrincipal_sub_of_mk_eq_mk (by rw [← hTE₁, ← hmk]; exact hT)

  have hdeg : Divisor.degree (P.sndDiv (heckeDivBar hαℓ hβℓ
      (D₁ : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))))) =
      ((((ℓ : ℕ) : ℤ)) + 1) *
        Divisor.degree (P.sndDiv (D₁ : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)))) := by
    rw [hsndT₁]
    exact Comp554.degree_heckeDivBar (N * q) ℓ hℓNq hαℓ hβℓ _

  have PRINC : ∀ Z : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)),
      Divisor.IsPrincipal Z → P.IsGoodDiv Z →
        Divisor.degree (P.sndDiv Z) •
            ((e s₀.1 : ℤ) • crossingCoord
              (⟨s₀, hs₀⟩ : ↥(nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W))) ∈
          LinearMap.range (gramMap (widthOfPlaces (arithFrobC q (ResidueField A) N) W e)) := by
    intro Z hZ hgZ

    choose Kf hKfin xwf hxwf ϖf hϖf eKf εf hεf hqϖf cf Ef uf huf hsat₁ hsat₂ hrest using
      fun w : ↥W => hdepth w.1 w.2
    haveI : ∀ w : ↥W, FiniteDimensional ℚ (Kf w) := hKfin
    have hvalA : ∀ w : ↥W,
        R.ValueIntegralityLaw (w : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) N)) :=
      fun w => PlaceSpecialization.ProlongationTuple.valueIntegralityLaw_of_orderLawFixed R hqN hO _ (hWss _ w.2)

    have hE1 : ∀ w : ↥W, 1 ≤ Ef w := fun w => by
      rw [PlaceSpecialization.ProlongationTuple.crossingExponent_eq_placeWidthChar_mul_of_orderLawFixed R hqN hmodel
        W hWss hreg hval hO hker (Kf w) _ w.2 (xwf w) (hxwf w) (ϖf w) (hϖf w) (eKf w) (εf w) (hεf w) (hqϖf w)
        (cf w) (Ef w) (uf w) (huf w) (hrest w).1]
      exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero
        (Nat.one_le_iff_ne_zero.mp (one_le_placeWidthChar_of_mem_ssPlaces hqN (hWss _ w.2)))
        (Nat.one_le_iff_ne_zero.mp (Comp554.one_le_of_eq_pow_mul_unit
          (NodeLocalized.redRestrict (IsLocalRing.residue ↥A) (Kf w))
          (hεf w) (hqϖf w) (by rw [map_natCast]; exact CharP.cast_eq_zero _ _))))
    have hsuppZ : ∀ V ∈ Z.support, P.IsStrictFst V ∨ P.IsStrictSnd V ∨ P.reduceFst V ∈ W :=
      fun V hV => (hgZ V hV).elim Or.inl (fun h => Or.inr (Or.inl h))

    have h3c := PlaceSpecialization.depthDual_add_mem_range_gramMap_of_isPrincipal N q hq hqN hq5 A hA
      W hW data hKr hα hβ P R hmodel hO hreg hval Kf cf ϖf hϖf hvalA
      (fun w => ⟨Ef w, uf w, hE1 w, huf w, (hrest w).1⟩) 1 one_pos Z hZ hsuppZ depth
      (fun w V hV hred => absurd (show P.reduceFst V ∈ W by rw [hred]; exact w.2)
        (Comp554.reduceFst_notMem_of_strict P hWfix (hgZ V hV)))
      s₀ hs₀

    have hwe : (fun s : ↥(nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W) =>
        1 * widthOfPlaces (arithFrobC q (ResidueField A) N) W (placeWidth N) s) =
        widthOfPlaces (arithFrobC q (ResidueField A) N) W e := by
      funext s
      rw [one_mul, widthOfPlaces_apply, widthOfPlaces_apply, he _ (fst_mem_of_mem_nodePairsOfPlaces s.2),
        placeWidthChar_of_five_le hq5]
    have hes₀ : (((1 * placeWidth N s₀.1 : ℕ)) : ℤ) = (e s₀.1 : ℤ) := by
      rw [one_mul, he _ (fst_mem_of_mem_nodePairsOfPlaces hs₀), placeWidthChar_of_five_le hq5]
    have hrg : LinearMap.range (gramMap fun s : ↥(nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W) =>
        1 * widthOfPlaces (arithFrobC q (ResidueField A) N) W (placeWidth N) s) =
        LinearMap.range (gramMap (widthOfPlaces (arithFrobC q (ResidueField A) N) W e)) :=

      congrArg (fun w => LinearMap.range (gramMap w)) hwe
    have hdZ := PlaceSpecialization.depthDual_eq_zero_of_isGoodDiv P (arithFrobC q (ResidueField A) N) W hWfix depth Z hgZ

    simp only [hdZ, zero_add, hes₀, hrg] at h3c
    exact h3c
  have h1 := PRINC _ hpr' (Comp554.isGoodDiv_sub P hgD' hgT₁)
  have h2 := PRINC _ hpr₁ (Comp554.isGoodDiv_sub P hgD hgD₁)

  simp only [Comp554.sndDiv_sub, map_sub, hdeg] at h1
  simp only [Comp554.sndDiv_sub, map_sub] at h2
  have h3 := Submodule.sub_mem _ h1 (Submodule.smul_mem _ ((((ℓ : ℕ) : ℤ)) + 1) h2)
  exact (congrArg (fun x => x ∈ LinearMap.range (gramMap (widthOfPlaces (arithFrobC q (ResidueField A) N) W e)))
    (Comp554.smul_comb _ _ _ _ _)).mpr h3

end S_ModularCurve_PlaceSpecialization_componentGroupProj_depthDual_add_eq_heckeComponentAction_of_heckeGen_smul
end P2MW
export P2MW.S_ModularCurve_PlaceSpecialization_componentGroupProj_depthDual_add_eq_heckeComponentAction_of_heckeGen_smul (solution)
