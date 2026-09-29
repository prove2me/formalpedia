-- Prove2me | solution 1 for ModularCurve.PlaceSpecialization.componentGroupProj_depthDual_add_eq_heckeComponentAction_of_heckeGen_smul_of_lt_five_of_not_isGoodDiv
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/47f3e9d7-8fca-5ec0-8930-277636c0dcd8

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
import Theorems.Thm_ModularCurve_PlaceSpecialization_depthDual_add_mem_range_gramMap_of_isPrincipal_widthChar
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_nodeValueLaw_of_regularityLaw
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_valueIntegralityLaw_of_orderLawFixed
import Theorems.Thm_ModularCurve_PlaceSpecialization_frobOnPlacesGeomLevel_frobOnPlacesGeomLevel_eq_self_of_mem_ssPlaces
import Theorems.Thm_ModularCurve_PlaceSpecialization_isStrictFst_or_isStrictSnd_iff
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_crossingExponent_eq_placeWidthChar_mul_of_orderLawFixed
import Theorems.Thm_ModularCurve_one_le_placeWidthChar_of_mem_ssPlaces
import Theorems.Thm_ModularCurve_arithFrobC_smul_eq_frobOnPlacesGeomLevel
import Theorems.Thm_ValuationSubring_isAlgClosed_residueField
import Theorems.Thm_ModularCurve_finrankAlong_heckeBetaBar
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_NodeCoordinates_depth_lt_of_depthValueLaw_of_nodeEquation
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_NodeCoordinates_depth_pos_of_depthValueLaw_of_nodeEquation
import Theorems.Thm_ModularCurve_PlaceSpecialization_exists_rep_eq_off_strict_reduce_notMem_heckeDivBar_strictPart_good_kindResp_of_isModel
import Theorems.Thm_ModularCurve_PlaceSpecialization_exists_reduceFst_eq_and_yDepth_restrictAlong_heckeAlphaBar_pow_placeWidthChar_eq_of_ne_of_not_dvd
import Theorems.Thm_ModularCurve_PlaceSpecialization_reduceFst_mem_ssPlaces_of_mem_support_heckeDivBar_single_of_ne
import Theorems.Thm_ModularCurve_PlaceSpecialization_mapDomain_reduceFst_heckeDivBar_single_apply_eq_correspondence_of_ne
import Theorems.Thm_ModularCurve_placeWidthChar_mul_correspondence_heckeBetaC_heckeAlphaC_single_apply_eq_of_prime
import Theorems.Thm_ModularCurve_PlaceSpecialization_mapDomain_reduceFst_heckeDivBar_eq_heckeDivFibre_mapDomain_reduceFst_of_ne_of_isModel_of_orderLawFixed
import Theorems.Thm_ModularCurve_hasPrincipalDivisors_charLDegeneracyRoof
import Theorems.Thm_ModularCurve_heckeInputsFibre_of_natCast_ne_zero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_PlaceSpecialization_componentGroupProj_depthDual_add_eq_heckeComponentAction_of_heckeGen_smul_of_lt_five_of_not_isGoodDiv
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent ModularCurve.B3.instIsElliptic_goodModel WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral instTopologicallyFGOfFiniteType AdicCompletion.instIsLocalRingMaximalIdeal ModularCurve.instIsElliptic_tateBase WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.NodeLocalized.isLocalization_nodeDenominators ModularCurve.NodeLocalized.algebraEvalRange ModularCurve.NodeLocalized.isLocalRing_modularLocalizedAtPoint ModularCurve.NodeLocalized.isScalarTower_K_fieldOver_bar ModularCurve.NodeLocalized.algebraFieldOverBar ModularCurve.NodeLocalized.algebra_isIntegral_fieldOver_bar ModularCurve.NodeLocalized.isScalarTower_fieldOver_bar_laurent ModularCurve.NodeLocalized.charZero_fieldOver ModularCurve.NodeLocalized.algebraFieldOver ModularCurve.NodeLocalized.charZero_laurentSeries_algClosure ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar"
p2m_attr_erase "instance" "AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.instIsScalarTowerJAdjoin GaloisRepAdic.instAddCommGroup GaloisRepAdic.instFree GaloisRepAdic.instFinite GaloisRepAdic.instModule ResidualGaloisRep.instModule ResidualGaloisRep.instModuleFinite ResidualGaloisRep.instAddCommGroup WeierstrassCurve.Affine.Point.instFinite AlgebraicCurve.CurveModel.isProper AlgebraicCurve.CurveModel.isIntegral AlgebraicCurve.CurveModel.smooth ModularCurve.IgusaScheme.isOpenImmersion_fInf ModularCurve.IgusaScheme.isOpenImmersion_ιInf ModularCurve.IgusaScheme.fact_jFull_ne_zero ModularCurve.IgusaScheme.isOpenImmersion_ιFin ModularCurve.IgusaScheme.isOpenImmersion_fFin"
p2m_attr_erase "instance" "AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin AlgebraicCurve.CurveModel.chartRing_finitePresentation ModularCurve.numberField_of_finiteDimensional CuspForm.heckeAlgebra.instCommRing CuspForm.heckeAlgebra.instIsMulCommutative CuspForm.heckeAlgebra.instIsAddTorsionFree ModularCurve.CuspSpace.instNonempty ModularCurve.CuspSpace.instSubsingletonOfOne ModularCurve.CuspSpace.instFinite ModularCurve.instAlgebraIntermediateFieldLaurent ModularCurve.instIsScalarTowerKaehlerIntermediateFieldLaurent ModularCurve.instIsScalarTowerIntermediateFieldLaurent ModularCurve.instModuleKaehlerIntermediateFieldLaurent FLT.Gamma0FundamentalSet.instContinuousConstSMulSpecialLinearGroupFinOfNatNatIntUpperHalfPlane_definitions"
p2m_attr_erase "instance" "FLT.HyperbolicMeasure.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatIntUpperHalfPlaneVolume_definitions FLT.HyperbolicMeasure.instIsOpenPosMeasureUpperHalfPlaneVolume_definitions FLT.L2ProductionInstance.isFiniteMeasure_gamma0 FLT.L2ProductionInstance.countable_SL2Z FLT.L2ProductionInstance.countable_quotient FLT.L2ProductionInstance.nontrivial_gamma0L2 HeckeEis.instModuleCoeffH1par HeckeEis.instAddCommGroupCoeffH1par HeckeEis.instFiniteIndexHeckeUpper instFieldLaurentSeriesAlgClosureRat instAlgebraModularFunctionFieldBar ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instAlgebraResidueFieldSubtypeMemValuationSubringGaussBaseResOne ModularCurve.PlaceSpecialization.LevelOneProlongationPair.algGaussBase instAlgebraModularFunctionFieldFullC ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instAlgebraSubtypeMemValuationSubringGaussBaseResOne ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instAlgebraSubtypeMemValuationSubringGaussBaseResTwo instFieldModularFunctionFieldC ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isScalarTower_resOne instFieldLaurentSeries' ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isScalarTower_resTwo instModuleModularFunctionFieldBar ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isLocalHom_resBase₁ instAlgebraModularFunctionFieldC ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isLocalHom_constToGaussBase ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instFieldResOne instFieldModularFunctionFieldBar ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instAlgebraResidueFieldSubtypeMemValuationSubringGaussBaseResTwo ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instFieldResTwo instFieldModularFunctionFieldFullC ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isScalarTower_gaussBase instAlgebraLaurentSeriesAlgClosureRat ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isLocalHom_resBase₂ ModularCurve.PlaceSpecialization.LevelOneProlongationPair.algResidueConst instCommRingModularFunctionFieldBar ModularCurve.LevelOnePhi.instAddCommGroup AlgebraicCurve.GaussReduction.isLocalHom_constToGauss AlgebraicCurve.CellDissection.fintypeV AlgebraicCurve.CellDissection.fintypeC AlgebraicCurve.CellDissection.fintypeE AlgebraicCurve.CellDissection.decEqV"
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
p2m_attr_erase "simp" "ResidualGaloisRep.mk.sizeOf_spec ResidualGaloisRep.mk.injEq ResidualGaloisRep.Equiv.mk.sizeOf_spec ResidualGaloisRep.Equiv.mk.injEq AlgebraicCurve.CurveModel.mk.injEq AlgebraicCurve.CurveModel.mk.sizeOf_spec ModularCurve.CharPModel.FibreModel.mk.injEq ModularCurve.CharPModel.FibreModel.mk.sizeOf_spec ModularCurve.IgusaScheme.ιInf_igusaTo_assoc ModularCurve.IgusaScheme.coe_jFull ModularCurve.IgusaScheme.coe_jInvChartInf ModularCurve.IgusaScheme.coe_jChartFin ModularCurve.IgusaScheme.ιFin_igusaTo ModularCurve.IgusaScheme.ιInf_igusaTo ModularCurve.IgusaScheme.ιFin_igusaTo_assoc AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces ModularCurve.PlaceSpecialization.LevelOneProlongationPair.mk.sizeOf_spec ModularCurve.PlaceSpecialization.LevelOneProlongationPair.residue₂_apply ModularCurve.PlaceSpecialization.LevelOneProlongationPair.residue₁_apply ModularCurve.PlaceSpecialization.LevelOneProlongationPair.mk.injEq ModularCurve.symPoly_zero ModularCurve.frobeniusPullbackGeomLevelUnconditional_single ModularCurve.frobeniusPushforwardGeomLevelUnconditional_single ModularCurve.frobeniusGeomLevelUnconditional_apply_coe ModularCurve.coe_levelPolynomialEquiv_apply ModularCurve.coe_levelBaseRingDescent_apply ModularCurve.levelConst_apply ModularCurve.coe_laurentDescent_apply ModularCurve.dualHeckeRep_apply_apply ModularCurve.coe_segmentPath"
p2m_attr_erase "simp" "ModularCurve.cuspHeckeAeval_heckeGen ModularCurve.coe_periodLatticeRestrict_apply CuspForm.heckeAlgebra.coe_U CuspForm.heckeAlgebra.coe_T ModularForm.coe_heckeTLin_apply CuspForm.coe_heckeULin_apply CuspForm.coe_heckeTLin_apply ModularForm.coe_heckeULin_apply ModularCurve.ComplexPlaceDictionary.mk.injEq ModularCurve.ComplexPlaceDictionary.mk.sizeOf_spec ModularCurve.Period.IsEquivariantPrimitive.periodHom_apply ModularCurve.Period.IsEquivariantPrimitive.period_one ModularCurve.CuspSpace.cuspDenomAux_infty ModularCurve.CuspSpace.cuspDenomAux_coe ModularCurve.CuspSpace.cuspDenom_mk_zero ModularCurve.CuspSpace.cuspDenom_mk_infty ModularCurve.mapGL_apply_coe ModularCurve.ratPoint_one_zero ModularCurve.ratPoint_zero_right ModularCurve.CuspSpace.fromCoset_mk ModularCurve.CuspSpace.cuspDenom_mk ModularCurve.ratPoint_zero_one ModularCurve.qEulerFun_coeff ModularCurve.diffQExp_D ModularCurve.qEulerOn_apply ModularCurve.qEuler_coeff FLT.TruncatedDomainPartition.unipotentDiagonalSum_zero HeckeEis.coeffCoboundaryMap_apply HeckeEis.heckeConjMat_apply_one_one HeckeEis.coe_heckeConjSL HeckeEis.mem_heckeUpperSL HeckeEis.resHom_apply HeckeEis.heckeConjMat_apply_zero_one HeckeEis.coe_transferAux HeckeEis.coe_heckeConj HeckeEis.alphaMat_apply_one_one HeckeEis.heckeConjMat_apply_one_zero HeckeEis.alphaMat_apply_zero_one HeckeEis.pullbackHom_apply HeckeEis.alphaMat_apply_one_zero"
p2m_attr_erase "simp" "HeckeEis.alphaMat_apply_zero_zero HeckeEis.heckeConjMat_apply_zero_zero ModularCurve.PlaceSpecialization.LevelOneProlongationPair.coe_gaussOrderToIntegers₂ ModularCurve.PlaceSpecialization.LevelOneProlongationPair.coe_gaussOrderToIntegers₁ ModularCurve.PlaceSpecialization.LevelOneProlongationPair.coe_toIntegers₁ ModularCurve.PlaceSpecialization.LevelOneProlongationPair.coe_constToGaussBase ModularCurve.PlaceSpecialization.LevelOneProlongationPair.coe_toIntegers₂ AlgebraicCurve.GaussReduction.constToGauss_coe AlgebraicCurve.ComponentChart.ofConstantReductionNodes_dom AlgebraicCurve.ComponentChart.ofConstantReductionNodes_placeMap AlgebraicCurve.ComponentChart.ofConstantReductionNodes_nodes AlgebraicCurve.ComponentChart.ofConstantReductionNodes_residue AlgebraicCurve.ComponentChart.ofConstantReductionNodes_integers ModularCurve.FinitePlaceLift.traceHom_coe ModularCurve.FinitePlaceLift.mk.injEq ModularCurve.FinitePlaceLift.mk.sizeOf_spec AlgebraicCurve.ComponentChart.ofConstantReduction_integers AlgebraicCurve.ComponentChart.mk.sizeOf_spec AlgebraicCurve.ComponentChart.ofConstantReduction_placeMap AlgebraicCurve.ComponentChart.ofConstantReduction_nodes AlgebraicCurve.ComponentChart.mk.injEq AlgebraicCurve.ComponentChart.ofConstantReduction_dom AlgebraicCurve.Annulus.mk.sizeOf_spec AlgebraicCurve.Annulus.mk.injEq AlgebraicCurve.abelJacobiDiv_single AlgebraicCurve.AnalyticCoord.mk.injEq AlgebraicCurve.Cell.mk.sizeOf_spec AlgebraicCurve.RadialRegion.mk.sizeOf_spec AlgebraicCurve.RadialRegion.mk.injEq AlgebraicCurve.CellDissection.mk.sizeOf_spec AlgebraicCurve.Cell.mk.injEq AlgebraicCurve.CellDissection.mk.injEq AlgebraicCurve.AnalyticCoord.mk.sizeOf_spec AddMonoid.End.dualEndDataOfSurjective_trace AddMonoid.End.dualEndDataOfSurjective_norm"
set_option autoImplicit false
set_option maxHeartbeats 3200000
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

theorem gramMap_const_mul_apply {ι : Type*} [Fintype ι] (w : ι → ℕ) (e' : ℕ)
    (γ : characterLattice ι) :
    gramMap (fun s => e' * w s) γ = (e' : ℤ) • gramMap w γ := by
  refine LinearMap.ext fun D => ?_
  simp only [gramMap_apply, LinearMap.smul_apply, smul_eq_mul, Nat.cast_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun x _ => by ring

theorem mem_range_gramMap_of_smul_mem_range_gramMap_mul {ι : Type*} [Fintype ι]
    (w : ι → ℕ) (e' : ℕ) (he' : 0 < e') (x : Module.Dual ℤ (characterLattice ι))
    (h : (e' : ℤ) • x ∈ LinearMap.range (gramMap fun s => e' * w s)) :
    x ∈ LinearMap.range (gramMap w) := by
  obtain ⟨γ, hγ⟩ := h
  refine ⟨γ, ?_⟩
  rw [gramMap_const_mul_apply] at hγ
  have he0 : (e' : ℤ) ≠ 0 := by exact_mod_cast he'.ne'

  refine LinearMap.ext fun D => ?_
  have hD := congrArg (fun f : Module.Dual ℤ (characterLattice ι) => f D) hγ
  simp only [LinearMap.smul_apply, smul_eq_mul] at hD
  exact Int.eq_of_mul_eq_mul_left he0 hD

theorem dualMap_crossingCoord {ι : Type*} [Fintype ι] (B : Matrix ι ι ℤ) {n : ℤ} (hrow : HeckeRowSums B n) (t : ι) :
    (heckeCharacterAction B hrow).dualMap (crossingCoord t) = ∑ i : ι, B i t • crossingCoord i := by
  apply LinearMap.ext
  intro γ
  simp only [LinearMap.dualMap_apply, crossingCoord_apply, heckeCharacterAction_coe, heckeDivisorAction_apply,
    LinearMap.coe_sum, Finset.sum_apply, LinearMap.smul_apply, smul_eq_mul]

theorem mapDomain_apply_eq_sum {α β M : Type*} [AddCommMonoid M] [DecidableEq β] (f : α → β) (X : α →₀ M) (b : β) :
    Finsupp.mapDomain f X b = ∑ a ∈ X.support, if f a = b then X a else 0 := by
  classical
  unfold Finsupp.mapDomain
  rw [Finsupp.sum_apply]
  unfold Finsupp.sum
  refine Finset.sum_congr rfl fun a _ => ?_
  simp only [Finsupp.single_apply]

theorem annulus_algebra {ι : Type*} [Fintype ι] (w : ι → ℕ) (B : Matrix ι ι ℤ) {n : ℤ}
    (hrow : HeckeRowSums B n) (hsym : HeckeWeightSymm w B) (s₀ : ι) (e' : ℕ) (he' : 0 < e')
    (dD dD' : Module.Dual ℤ (characterLattice ι)) (a a' a₁ : ℤ)
    (h1 : (e' : ℤ) • (dD' - (heckeCharacterAction B hrow).dualMap dD) +
        (a' - n * a₁) • (((e' : ℤ) * (w s₀ : ℤ)) • crossingCoord s₀) ∈
          LinearMap.range (gramMap fun s => e' * w s))
    (h2 : (a - a₁) • (((e' : ℤ) * (w s₀ : ℤ)) • crossingCoord s₀) ∈ LinearMap.range (gramMap fun s => e' * w s)) :
    componentGroupProj w (dD' + a' • ((w s₀ : ℤ) • crossingCoord s₀)) =
      heckeComponentAction w B hrow hsym (componentGroupProj w (dD + a • ((w s₀ : ℤ) • crossingCoord s₀))) := by
  set c₀ : Module.Dual ℤ (characterLattice ι) := (w s₀ : ℤ) • crossingCoord s₀ with hc₀
  have hrot : ((e' : ℤ) * (w s₀ : ℤ)) • crossingCoord s₀ = (e' : ℤ) • c₀ := by
    rw [hc₀, smul_smul]
  rw [hrot] at h1 h2

  have h4 := Submodule.sub_mem _ h1 (Submodule.smul_mem _ n h2)
  have hX : (e' : ℤ) • ((dD' + a' • c₀) - ((heckeCharacterAction B hrow).dualMap dD + (n * a) • c₀)) ∈
      LinearMap.range (gramMap fun s => e' * w s) := by
    convert h4 using 1
    module
  have hX' := mem_range_gramMap_of_smul_mem_range_gramMap_mul w e' he' _ hX
  rw [componentGroupProj_eq_of_sub_mem _ hX']
  simp only [map_add, componentGroupProj_heckeComponentAction, LinearMap.map_smul_of_tower]
  rw [hc₀, componentGroupProj_dualMap_vertex w B hrow hsym s₀, smul_smul, mul_comm]

theorem smul_mul_smul_rot {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] (a b e : R) (x : M) :
    a • ((e * b) • x) = e • ((a * b) • x) := by
  module

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
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_componentGroupProj_depthDual_add_eq_heckeComponentAction_of_heckeGen_smul_of_lt_five_of_not_isGoodDiv.Comp554"

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

theorem sndDiv_add (D E : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) :
    P.sndDiv (D + E) = P.sndDiv D + P.sndDiv E := by
  classical
  unfold PlaceSpecialization.sndDiv
  exact map_add (Finsupp.filterAddHom _) D E

theorem sndDiv_eq_zero_of_forall_not {D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))}
    (h : ∀ V ∈ D.support, ¬ P.IsStrictSnd V) : P.sndDiv D = 0 := by
  classical
  unfold PlaceSpecialization.sndDiv
  rw [Finsupp.filter_eq_zero_iff]
  intro V hV
  by_contra hDV
  exact h V (Finsupp.mem_support_iff.mpr hDV) hV

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

open Classical in

theorem sub_fstDiv_add_sndDiv_apply (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)))
    (V : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) :
    (D - (P.fstDiv D + P.sndDiv D)) V = if P.IsStrictFst V ∨ P.IsStrictSnd V then 0 else D V := by
  classical
  unfold PlaceSpecialization.fstDiv PlaceSpecialization.sndDiv
  rw [Finsupp.sub_apply, Finsupp.add_apply, Finsupp.filter_apply, Finsupp.filter_apply]
  by_cases h1 : P.IsStrictFst V
  · rw [if_pos h1, if_neg (not_isStrictSnd_of_isStrictFst P h1), if_pos (Or.inl h1)]
    ring
  · by_cases h2 : P.IsStrictSnd V
    · rw [if_neg h1, if_pos h2, if_pos (Or.inr h2)]
      ring
    · rw [if_neg h1, if_neg h2, if_neg (fun h : P.IsStrictFst V ∨ P.IsStrictSnd V => h.elim h1 h2)]
      ring

open Classical in

theorem not_isStrict_of_mem_support_sub_fstDiv_add_sndDiv
    {D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))}
    {V : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))}
    (hV : V ∈ (D - (P.fstDiv D + P.sndDiv D)).support) :
    ¬ (P.IsStrictFst V ∨ P.IsStrictSnd V) ∧ (D - (P.fstDiv D + P.sndDiv D)) V = D V ∧ V ∈ D.support := by
  have h := sub_fstDiv_add_sndDiv_apply P D V
  have hne := Finsupp.mem_support_iff.mp hV
  by_cases hs : P.IsStrictFst V ∨ P.IsStrictSnd V
  · rw [if_pos hs] at h
    exact absurd h hne
  · rw [if_neg hs] at h
    exact ⟨hs, h, Finsupp.mem_support_iff.mpr (h ▸ hne)⟩

theorem exists_mem_support_single_of_mem_support_map {K F K' F' : Type*} [Field K] [Field F] [Algebra K F]
    [Field K'] [Field F'] [Algebra K' F']
    (f : Divisor K F →+ Divisor K' F') (X : Divisor K F) {V : Place K' F'} (hV : V ∈ (f X).support) :
    ∃ V₀ ∈ X.support, V ∈ (f (Finsupp.single V₀ 1)).support := by
  classical
  have hX : f X = ∑ V₀ ∈ X.support, X V₀ • f (Finsupp.single V₀ 1) := by
    conv_lhs => rw [← Finsupp.sum_single X]
    rw [Finsupp.sum, map_sum]
    refine Finset.sum_congr rfl fun V₀ _ => ?_
    rw [← map_zsmul, Finsupp.smul_single, smul_eq_mul, mul_one]
  rw [hX] at hV
  obtain ⟨V₀, hV₀, hV'⟩ := Finset.mem_biUnion.mp (Finsupp.support_finsetSum hV)
  exact ⟨V₀, hV₀, Finsupp.support_smul hV'⟩

theorem mem_support_or_of_mem_support_sub {α M : Type*} [AddGroup M] {X Y : α →₀ M} {a : α}
    (h : a ∈ (X - Y).support) : a ∈ X.support ∨ a ∈ Y.support := by
  classical
  rcases Finset.mem_union.mp (Finsupp.support_sub h) with h' | h'
  · exact Or.inl h'
  · exact Or.inr h'

theorem mem_support_or_of_mem_support_add {α M : Type*} [AddZeroClass M] {X Y : α →₀ M} {a : α}
    (h : a ∈ (X + Y).support) : a ∈ X.support ∨ a ∈ Y.support := by
  classical
  rcases Finset.mem_union.mp (Finsupp.support_add h) with h' | h'
  · exact Or.inl h'
  · exact Or.inr h'

theorem exists_of_mem_support_correspondence_single {K F F' : Type*} [Field K] [Field F] [Field F']
    [Algebra K F] [Algebra K F'] [HasPrincipalDivisors K F']
    (φ ψ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (hψ : ψ.toRingHom.IsIntegral)
    (v v' : Place K F) (n : ℤ)
    (h : v' ∈ (Divisor.correspondence φ ψ hφ hψ (Finsupp.single v n)).support) :
    ∃ R ∈ Place.fiberAlong φ hφ v, R.restrictAlong ψ hψ = v' := by
  classical
  rw [Divisor.correspondence_apply, Divisor.pullbackAlong_single, map_sum] at h
  obtain ⟨R, hR, hR'⟩ := Finset.mem_biUnion.mp (Finsupp.support_finsetSum h)
  rw [Divisor.pushforwardAlong_single] at hR'
  exact ⟨R, hR, (Finset.mem_singleton.mp (Finsupp.support_single_subset hR')).symm⟩

set_option maxHeartbeats 3200000 in

theorem eq_smulNodePair_of_mem {g : SemilinearAut k (modularFunctionFieldC k N)} {W : Finset (Place k (modularFunctionFieldC k N))}
    {s : Place k (modularFunctionFieldC k N) × Place k (modularFunctionFieldC k N)} (hs : s ∈ nodePairsOfPlaces g W) :
    s = smulNodePair g s.1 :=
  Prod.ext rfl (snd_eq_of_mem_nodePairsOfPlaces hs)

set_option maxHeartbeats 3200000 in

theorem depthDual_single (g : SemilinearAut k (modularFunctionFieldC k N)) (W : Finset (Place k (modularFunctionFieldC k N)))
    (depth : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)) → ℕ)
    (V₀ : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) (n : ℤ) (h : P.reduceFst V₀ ∈ W) :
    P.depthDual g W depth (Finsupp.single V₀ n) =
      (n * depth V₀) • crossingCoord (⟨smulNodePair g (P.reduceFst V₀), smulNodePair_mem_nodePairsOfPlaces g h⟩ :
        ↥(nodePairsOfPlaces g W)) := by
  classical
  unfold PlaceSpecialization.depthDual PlaceSpecialization.depthDiv
  rw [Finsupp.sum_single_index (by simp)]
  rw [Finset.sum_eq_single (⟨smulNodePair g (P.reduceFst V₀), smulNodePair_mem_nodePairsOfPlaces g h⟩ :
        ↥(nodePairsOfPlaces g W))]
  · simp only [smulNodePair_fst, Finsupp.single_eq_same]
  · intro s _ hs
    rw [Finsupp.single_apply, if_neg, zero_smul]
    intro heq
    apply hs
    apply Subtype.ext
    rw [eq_smulNodePair_of_mem s.2, ← heq]
  · intro h'
    exact absurd (Finset.mem_univ _) h'

set_option maxHeartbeats 6400000 in

theorem depthDual_perNode (g : SemilinearAut k (modularFunctionFieldC k N)) (W : Finset (Place k (modularFunctionFieldC k N)))
    (depth depthZ : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)) → ℕ)
    (B : Matrix ↥(nodePairsOfPlaces g W) ↥(nodePairsOfPlaces g W) ℤ) {n : ℤ} (hrow : HeckeRowSums B n)
    (pw : Place k (modularFunctionFieldC k N) → ℕ)
    (V₀ : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) (hV₀ : P.reduceFst V₀ ∈ W)
    (TV : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)))
    (C : Divisor k (modularFunctionFieldC k N)) (m₀ e' : ℤ)
    (hdZT : ∀ V ∈ TV.support, (depthZ V : ℤ) = depth V₀ * pw (P.reduceFst V) * m₀)
    (hCNT : ∀ w, Finsupp.mapDomain P.reduceFst TV w = C w)
    (hMCB : ∀ s : ↥(nodePairsOfPlaces g W),
      (pw (s : Place k (modularFunctionFieldC k N) × Place k (modularFunctionFieldC k N)).1 : ℤ) * C (s : Place k (modularFunctionFieldC k N) × Place k (modularFunctionFieldC k N)).1 =
        (pw (P.reduceFst V₀) : ℤ) * B s ⟨smulNodePair g (P.reduceFst V₀), smulNodePair_mem_nodePairsOfPlaces g hV₀⟩)
    (he' : e' = (pw (P.reduceFst V₀) : ℤ) * m₀) :
    P.depthDual g W depthZ TV =
      e' • (heckeCharacterAction B hrow).dualMap (P.depthDual g W depth (Finsupp.single V₀ 1)) := by
  classical
  rw [depthDual_single P g W depth V₀ 1 hV₀, one_mul, map_smul, dualMap_crossingCoord B hrow, Finset.smul_sum,
    Finset.smul_sum]
  unfold PlaceSpecialization.depthDual
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [smul_smul, smul_smul]
  congr 1
  have hcoefV : ∀ V ∈ TV.support,
      Finsupp.single (P.reduceFst V) (TV V * (depthZ V : ℤ)) (s : Place k (modularFunctionFieldC k N) × Place k (modularFunctionFieldC k N)).1 =
        ((depth V₀ : ℤ) * pw (s : Place k (modularFunctionFieldC k N) × Place k (modularFunctionFieldC k N)).1 * m₀) * Finsupp.single (P.reduceFst V) (TV V) (s : Place k (modularFunctionFieldC k N) × Place k (modularFunctionFieldC k N)).1 := by
    intro V hV
    by_cases h : P.reduceFst V = (s : Place k (modularFunctionFieldC k N) × Place k (modularFunctionFieldC k N)).1
    · rw [← h, Finsupp.single_eq_same, Finsupp.single_eq_same, hdZT V hV]
      ring
    · rw [Finsupp.single_apply, Finsupp.single_apply, if_neg h, if_neg h, mul_zero]
  have hLHS : P.depthDiv depthZ TV (s : Place k (modularFunctionFieldC k N) × Place k (modularFunctionFieldC k N)).1 =
      ((depth V₀ : ℤ) * pw (s : Place k (modularFunctionFieldC k N) × Place k (modularFunctionFieldC k N)).1 * m₀) * Finsupp.mapDomain P.reduceFst TV (s : Place k (modularFunctionFieldC k N) × Place k (modularFunctionFieldC k N)).1 := by
    unfold PlaceSpecialization.depthDiv Finsupp.mapDomain
    rw [Finsupp.sum_apply, Finsupp.sum_apply]
    unfold Finsupp.sum
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl hcoefV
  rw [hLHS, hCNT]
  linear_combination ((depth V₀ : ℤ) * m₀) * hMCB s -
    ((depth V₀ : ℤ) * B s ⟨smulNodePair g (P.reduceFst V₀), smulNodePair_mem_nodePairsOfPlaces g hV₀⟩) * he'

theorem addMonoidHom_apply_eq_smul_of_eq_on_support_single {α R N : Type*} [CommRing R] [AddCommGroup N] [Module R N]
    (φ ψ : (α →₀ ℤ) →+ N) (c : R) (X : α →₀ ℤ)
    (h : ∀ a ∈ X.support, φ (Finsupp.single a 1) = c • ψ (Finsupp.single a 1)) :
    φ X = c • ψ X := by
  classical
  conv_lhs => rw [← Finsupp.sum_single X]
  conv_rhs => rw [← Finsupp.sum_single X]
  rw [Finsupp.sum, map_sum, map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun a ha => ?_
  have hs : Finsupp.single a (X a) = X a • Finsupp.single a (1 : ℤ) := by
    rw [Finsupp.smul_single, smul_eq_mul, mul_one]
  rw [hs, map_zsmul, map_zsmul, h a ha, smul_comm]

theorem mass_combine {M N R : Type*} [AddCommGroup M] [AddCommGroup N] [CommRing R] [Module R N]
    (δ : M →+ N) (c : R) (Dp TD1 Tstr Tnode : M) (dDp LdD : N)
    (hT : TD1 = Tstr + Tnode) (ha : δ Dp = c • dDp) (hb : δ Tstr = 0) (hc : δ Tnode = c • LdD) :
    δ (Dp - TD1) = c • (dDp - LdD) := by
  rw [map_sub, hT, map_add, ha, hb, hc, zero_add, smul_sub]

end DivisorBookkeeping
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_componentGroupProj_depthDual_add_eq_heckeComponentAction_of_heckeGen_smul_of_lt_five_of_not_isGoodDiv.Comp554"

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
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_componentGroupProj_depthDual_add_eq_heckeComponentAction_of_heckeGen_smul_of_lt_five_of_not_isGoodDiv.Comp554"

end Comp554
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_componentGroupProj_depthDual_add_eq_heckeComponentAction_of_heckeGen_smul_of_lt_five_of_not_isGoodDiv.Comp554"

namespace Comp554

section DepthDual

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
  {k : Type*} [Field k] [CharP k q] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
  {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
  (P : PlaceSpecialization A q N data hKr k red hα hβ)

theorem depthDiv_add (depth : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)) → ℕ)
    (D E : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) :
    P.depthDiv depth (D + E) = P.depthDiv depth D + P.depthDiv depth E := by
  unfold PlaceSpecialization.depthDiv
  exact Finsupp.sum_add_index' (fun V => by simp) (fun V m n => by rw [add_mul, Finsupp.single_add])

theorem depthDual_add (g : SemilinearAut k (modularFunctionFieldC k N)) (W : Finset (Place k (modularFunctionFieldC k N)))
    (depth : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)) → ℕ)
    (D E : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) :
    P.depthDual g W depth (D + E) = P.depthDual g W depth D + P.depthDual g W depth E := by
  unfold PlaceSpecialization.depthDual
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [depthDiv_add, Finsupp.add_apply, add_smul]

noncomputable def depthDualHom (g : SemilinearAut k (modularFunctionFieldC k N))
    (W : Finset (Place k (modularFunctionFieldC k N)))
    (depth : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)) → ℕ) :
    Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)) →+
      Module.Dual ℤ (characterLattice ↥(nodePairsOfPlaces g W)) :=
  AddMonoidHom.mk' (P.depthDual g W depth) (depthDual_add P g W depth)

@[scoped simp] theorem depthDualHom_apply (g : SemilinearAut k (modularFunctionFieldC k N))
    (W : Finset (Place k (modularFunctionFieldC k N)))
    (depth : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)) → ℕ)
    (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) :
    depthDualHom P g W depth D = P.depthDual g W depth D := rfl

theorem depthDual_sub (g : SemilinearAut k (modularFunctionFieldC k N)) (W : Finset (Place k (modularFunctionFieldC k N)))
    (depth : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)) → ℕ)
    (D E : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) :
    P.depthDual g W depth (D - E) = P.depthDual g W depth D - P.depthDual g W depth E :=
  map_sub (depthDualHom P g W depth) D E

theorem depthDual_zsmul (g : SemilinearAut k (modularFunctionFieldC k N)) (W : Finset (Place k (modularFunctionFieldC k N)))
    (depth : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)) → ℕ)
    (n : ℤ) (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) :
    P.depthDual g W depth (n • D) = n • P.depthDual g W depth D :=
  map_zsmul (depthDualHom P g W depth) n D

theorem depthDual_finset_sum {ι : Type*} (s : Finset ι)
    (g : SemilinearAut k (modularFunctionFieldC k N)) (W : Finset (Place k (modularFunctionFieldC k N)))
    (depth : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)) → ℕ)
    (D : ι → Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) :
    P.depthDual g W depth (∑ i ∈ s, D i) = ∑ i ∈ s, P.depthDual g W depth (D i) :=
  map_sum (depthDualHom P g W depth) D s

theorem depthDiv_apply [DecidableEq (Place k (modularFunctionFieldC k N))]
    (depth : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)) → ℕ)
    (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) (w : Place k (modularFunctionFieldC k N)) :
    P.depthDiv depth D w = ∑ V ∈ D.support, if P.reduceFst V = w then D V * (depth V : ℤ) else 0 := by
  unfold PlaceSpecialization.depthDiv
  rw [Finsupp.sum_apply]
  unfold Finsupp.sum
  refine Finset.sum_congr rfl fun V _ => ?_
  simp only [Finsupp.single_apply]

theorem depthDual_eq_smul_of_forall_mem_support
    (g : SemilinearAut k (modularFunctionFieldC k N)) (W : Finset (Place k (modularFunctionFieldC k N)))
    (depth depth' : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)) → ℕ) (c : ℤ)
    (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)))
    (h : ∀ V ∈ D.support, P.reduceFst V ∈ W → (depth' V : ℤ) = c * depth V) :
    P.depthDual g W depth' D = c • P.depthDual g W depth D := by
  classical
  unfold PlaceSpecialization.depthDual
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [smul_smul]
  congr 1
  rw [depthDiv_apply, depthDiv_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun V hV => ?_
  by_cases hVs : P.reduceFst V = (s : Place k (modularFunctionFieldC k N) × Place k (modularFunctionFieldC k N)).1
  · rw [if_pos hVs, if_pos hVs, h V hV (hVs ▸ fst_mem_of_mem_nodePairsOfPlaces s.2)]
    ring
  · rw [if_neg hVs, if_neg hVs, mul_zero]

theorem depthDual_eq_zero_of_forall_reduceFst_notMem
    (g : SemilinearAut k (modularFunctionFieldC k N)) (W : Finset (Place k (modularFunctionFieldC k N)))
    (depth : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)) → ℕ)
    (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)))
    (h : ∀ V ∈ D.support, P.reduceFst V ∉ W) :
    P.depthDual g W depth D = 0 := by
  have h0 := depthDual_eq_smul_of_forall_mem_support P g W depth depth 0 D
    (fun V hV hW => absurd hW (h V hV))
  rwa [zero_smul] at h0

end DepthDual
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_componentGroupProj_depthDual_add_eq_heckeComponentAction_of_heckeGen_smul_of_lt_five_of_not_isGoodDiv.Comp554"

section Exponents

theorem valuation_natCast_pow_injective {A : ValuationSubring (AlgebraicClosure ℚ)} {q : ℕ} (hq : q.Prime)
    (hA : A.LiesOverPrime q) :
    Function.Injective fun n : ℕ => A.valuation (((q : ℕ) : AlgebraicClosure ℚ)) ^ n := by
  have h0 : A.valuation (((q : ℕ) : AlgebraicClosure ℚ)) ≠ 0 :=
    (Valuation.ne_zero_iff _).mpr (by exact_mod_cast hq.ne_zero)
  have h1 : A.valuation (((q : ℕ) : AlgebraicClosure ℚ)) < 1 := by
    have hmem : (((q : ℕ) : A)) ∈ IsLocalRing.maximalIdeal ↥A := ValuationSubring.natCast_mem_maximalIdeal_of_liesOverPrime hA
    have := (A.valuation_lt_one_iff _).mp hmem
    simpa using this
  exact (pow_right_strictAnti₀ (zero_lt_iff.mpr h0) h1).injective

end Exponents
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_componentGroupProj_depthDual_add_eq_heckeComponentAction_of_heckeGen_smul_of_lt_five_of_not_isGoodDiv.Comp554"

end Comp554
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_componentGroupProj_depthDual_add_eq_heckeComponentAction_of_heckeGen_smul_of_lt_five_of_not_isGoodDiv.Comp554"

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 32000000 in
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
      (hs₀ : s₀ ∈ nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W)
      (hq5 : q < 5)
      (hcase : ¬ (P.IsGoodDiv (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) ∧ P.IsGoodDiv (D' : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)))))
      (hwid : ¬ ∀ w ∈ W, e w = 1),
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
  intro W hW data hKr hα hβ P R hmodel hO hreg e he depth hdepth ℓ hℓ B hB hrow hsym D D' hD hD' hT s₀ hs₀ hq5 hcase hwid
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
  have hxyW : ∀ w : ↥W, ∃ (E : ℕ) (u : ↥(R.nodeIntegersOver (Kf w)
      (w : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) N)))),
      1 ≤ E ∧ IsUnit u ∧ (cf w).x * (cf w).y = R.nodeConst (Kf w) _ (ϖf w) ^ E * u :=
    fun w => ⟨Ef w, uf w, hE1 w, huf w, (hrest w).1⟩

  have hepw : ∀ w ∈ W, e w = placeWidthChar q N w := he

  haveI hPD : HasPrincipalDivisors (AlgebraicClosure ℚ) (modularFunctionFieldBar ((N * q) * (ℓ : ℕ))) :=
    hasPrincipalDivisors_modularFunctionFieldBar_unconditional ((N * q) * (ℓ : ℕ))
  have hαℓ : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) (N * q) ℓ :=
    heckeAlphaBarIntegral_of_prime (AlgebraicClosure ℚ) (N * q) ℓ
  have hβℓ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) (N * q) ℓ :=
    heckeBetaBarIntegral_of_prime (AlgebraicClosure ℚ) (N * q) ℓ

  have hNκ : ((N : ℕ) : ResidueField A) ≠ 0 := fun h => hqN ((CharP.cast_eq_zero_iff (ResidueField A) q N).mp h)
  have hℓκ : (((ℓ : ℕ) : ℕ) : ResidueField A) ≠ 0 := fun h =>
    hℓq ((Nat.prime_dvd_prime_iff_eq hq ℓ.2).mp ((CharP.cast_eq_zero_iff (ResidueField A) q _).mp h)).symm
  haveI hPDκ : HasPrincipalDivisors (ResidueField A) (charLDegeneracyRoof (ResidueField A) N ℓ) :=
    hasPrincipalDivisors_charLDegeneracyRoof (ResidueField A) N ℓ hNκ hℓκ
  have hIF := heckeInputsFibre_of_natCast_ne_zero (ResidueField A) N ℓ hℓκ
  obtain ⟨-, hβc, hαc, -⟩ := hIF

  have hHF := ModularCurve.PlaceSpecialization.mapDomain_reduceFst_heckeDivBar_eq_heckeDivFibre_mapDomain_reduceFst_of_ne_of_isModel_of_orderLawFixed N q hq A hA data hKr hα hβ P ℓ hℓq hαℓ hβℓ hqN R hmodel hO hβc hαc

  have h13 :=
    PlaceSpecialization.exists_rep_eq_off_strict_reduce_notMem_heckeDivBar_strictPart_good_kindResp_of_isModel N q hq
      hqN A hA W hW data hKr hα hβ P R hmodel hreg hval hO ℓ hℓq hαℓ hβℓ ∅ D
  obtain ⟨D₁, hmk₁, hoff, -, hgT₁, -, hsndT₁⟩ := h13

  have hS1 := Comp554.heckeGen_smul_mk (N * q) ℓ D₁ hαℓ hβℓ
  obtain ⟨E₁, hE₁, hTE₁⟩ := hS1
  have hmk : Pic0.mk D = Pic0.mk D₁ := hmk₁.symm
  have hpr' : Divisor.IsPrincipal
      ((D' : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) - heckeDivBar hαℓ hβℓ (D₁ : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)))) := by
    rw [← hE₁]
    exact Comp554.isPrincipal_sub_of_mk_eq_mk (by rw [← hTE₁, ← hmk]; exact hT)

  have hSCALE : ∃ e' : ℕ, 0 < e' ∧ ∀ w ∈ W, e w ∣ e' :=
    ⟨∏ w ∈ W, e w, Finset.prod_pos fun w hw => by rw [he w hw]; exact one_le_placeWidthChar_of_mem_ssPlaces hqN (hWss w hw),
      fun w hw => Finset.dvd_prod_of_mem e hw⟩
  obtain ⟨e', he'0, he'dvd⟩ := hSCALE

  have hvq := Comp554.valuation_natCast_pow_injective hq hA
  have hdZex : ∃ depthZ : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)) → ℕ,
      ∀ (V : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) (w : ↥W) (n : ℕ),
        P.reduceFst V = ↑w →
          (cf w).yDepth V ^ e' = A.valuation (((q : ℕ) : AlgebraicClosure ℚ)) ^ n → depthZ V = n := by
    refine ⟨fun V => Classical.epsilon fun n : ℕ => ∀ w : ↥W, P.reduceFst V = ↑w →
        (cf w).yDepth V ^ e' = A.valuation (((q : ℕ) : AlgebraicClosure ℚ)) ^ n, fun V w n hVw hn => ?_⟩
    have hex : ∃ m : ℕ, ∀ w' : ↥W, P.reduceFst V = ↑w' →
        (cf w').yDepth V ^ e' = A.valuation (((q : ℕ) : AlgebraicClosure ℚ)) ^ m :=
      ⟨n, fun w' hw' => by
        obtain rfl : w = w' := Subtype.ext (hVw.symm.trans hw')
        exact hn⟩
    have hspec := Classical.epsilon_spec hex w hVw
    exact hvq (hspec.symm.trans hn)
  obtain ⟨depthZ, hdepthZ⟩ := hdZex

  have hDn : ∃ Dn : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)),
      Dn = (D₁ : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) - (P.fstDiv (D₁ : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) + P.sndDiv (D₁ : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)))) := ⟨_, rfl⟩
  obtain ⟨Dnode, hDnode⟩ := hDn
  have hDnode_supp : ∀ V ∈ Dnode.support,
      ¬ (P.IsStrictFst V ∨ P.IsStrictSnd V) ∧ Dnode V = (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) V ∧
      (∀ σ ∈ A.inertiaSubgroupIn ℚ, arithmeticGalois (modularFunctionFieldFull (N * q)) σ • V = V) ∧
      P.reduceFst V ∈ W := by
    intro V hV
    rw [hDnode] at hV
    obtain ⟨hns, hvalV, hsuppV⟩ := Comp554.not_isStrict_of_mem_support_sub_fstDiv_add_sndDiv P hV
    have hDV : (D₁ : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) V = (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) V := hoff V hns
    have hVD : V ∈ (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))).support := by
      rw [Finsupp.mem_support_iff, ← hDV]
      exact Finsupp.mem_support_iff.mp hsuppV
    refine ⟨hns, by rw [hDnode, hvalV, hDV], (hD V hVD).1, ?_⟩
    rcases (hD V hVD).2 with h | h | h
    · exact absurd (Or.inl h) hns
    · exact absurd (Or.inr h) hns
    · exact h
  have hD₁dec : (D₁ : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) = (P.fstDiv (D₁ : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) + P.sndDiv (D₁ : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)))) + Dnode := by
    rw [hDnode]
    abel
  have hTdec : heckeDivBar hαℓ hβℓ (D₁ : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) =
      heckeDivBar hαℓ hβℓ (P.fstDiv (D₁ : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) + P.sndDiv (D₁ : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)))) + heckeDivBar hαℓ hβℓ Dnode := by
    conv_lhs => rw [hD₁dec]
    rw [map_add]

  have hSUPPW : ∀ V ∈ (heckeDivBar hαℓ hβℓ Dnode).support, P.reduceFst V ∈ W := by
    intro V hV
    obtain ⟨V₀, hV₀, hV'⟩ := Comp554.exists_mem_support_single_of_mem_support_map (heckeDivBar hαℓ hβℓ) Dnode hV
    have hV₀W := (hDnode_supp V₀ hV₀).2.2.2

    have hSS := ModularCurve.PlaceSpecialization.reduceFst_mem_ssPlaces_of_mem_support_heckeDivBar_single_of_ne N q hq A hA data hKr hα hβ P ℓ hℓq hαℓ hβℓ V₀ V ((hW _).1 hV₀W) hV'
    exact (hW _).2 hSS

  have hsuppZ : ∀ V ∈ ((D' : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) - heckeDivBar hαℓ hβℓ (D₁ : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)))).support,
      P.IsStrictFst V ∨ P.IsStrictSnd V ∨ P.reduceFst V ∈ W := by
    intro V hV
    rcases Comp554.mem_support_or_of_mem_support_sub hV with h | h
    · exact (hD' V h).2
    · rw [hTdec] at h
      rcases Comp554.mem_support_or_of_mem_support_add h with h' | h'
      · exact (hgT₁ V h').elim Or.inl (fun h2 => Or.inr (Or.inl h2))
      · exact Or.inr (Or.inr (hSUPPW V h'))

  have hTRANSPORT : ∀ (V₀ V : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) (w₀ w : ↥W),
      P.reduceFst V₀ = ↑w₀ → V ∈ (heckeDivBar hαℓ hβℓ (Finsupp.single V₀ 1)).support → P.reduceFst V = ↑w →
        (cf w).yDepth V ^ placeWidthChar q N (w₀ : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) N)) =
          (cf w₀).yDepth V₀ ^ placeWidthChar q N (w : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) N)) := by
    intro V₀ V w₀ w hV₀ hV hVw

    have hV2 : V ∈ (Divisor.correspondence (heckeBetaBar (AlgebraicClosure ℚ) (N * q) ℓ)
        (heckeAlphaBar (AlgebraicClosure ℚ) (N * q) ℓ) hβℓ hαℓ (Finsupp.single V₀ 1)).support := hV
    have hY := Comp554.exists_of_mem_support_correspondence_single
      (heckeBetaBar (AlgebraicClosure ℚ) (N * q) ℓ) (heckeAlphaBar (AlgebraicClosure ℚ) (N * q) ℓ) hβℓ hαℓ V₀ V 1 hV2
    obtain ⟨Y, hYβ, hYα⟩ := hY
    have hYβ' : Y.restrictAlong (heckeBetaBar (AlgebraicClosure ℚ) (N * q) ℓ) hβℓ = V₀ := Place.mem_fiberAlong.mp hYβ

    have h3f := PlaceSpecialization.exists_reduceFst_eq_and_yDepth_restrictAlong_heckeAlphaBar_pow_placeWidthChar_eq_of_ne_of_not_dvd N q hq
      hqN A hA W hW data hKr hα hβ P R hmodel hO hreg hval Kf cf ϖf hϖf hvalA hxyW ℓ hℓq
      (fun h => hℓ (dvd_mul_of_dvd_left h q)) hαℓ hβℓ Y w₀
      (by rw [hYβ']; exact hV₀)
    obtain ⟨w'', hw'', hpow⟩ := h3f
    rw [hYα] at hw'' hpow
    rw [hYβ'] at hpow
    obtain rfl : w'' = w := Subtype.ext (hw''.symm.trans hVw)
    exact hpow

  have hreadZ : ∀ (w : ↥W), ∀ V ∈ ((D' : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) - heckeDivBar hαℓ hβℓ (D₁ : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)))).support,
      P.reduceFst V = ↑w → (cf w).yDepth V ^ e' = A.valuation (((q : ℕ) : AlgebraicClosure ℚ)) ^ depthZ V := by
    intro w V hV hVw

    suffices hex : ∃ n : ℕ, (cf w).yDepth V ^ e' = A.valuation (((q : ℕ) : AlgebraicClosure ℚ)) ^ n by
      obtain ⟨n, hn⟩ := hex
      rw [hdepthZ V w n hVw hn]
      exact hn
    rcases Comp554.mem_support_or_of_mem_support_sub hV with h | h
    ·
      refine ⟨e' * depth V, ?_⟩
      rw [(hrest w).2 V hVw (hD' V h).1, ← pow_mul, mul_comm]
    · rw [hTdec] at h
      rcases Comp554.mem_support_or_of_mem_support_add h with h' | h'
      ·
        exact absurd (hVw ▸ w.2 : P.reduceFst V ∈ W) (Comp554.reduceFst_notMem_of_strict P hWfix (hgT₁ V h'))
      ·
        obtain ⟨V₀, hV₀, hVV₀⟩ :=
          Comp554.exists_mem_support_single_of_mem_support_map (heckeDivBar hαℓ hβℓ) Dnode h'
        obtain ⟨-, -, hfix₀, hV₀W⟩ := hDnode_supp V₀ hV₀
        obtain ⟨m, hm⟩ := he'dvd _ hV₀W
        have ht := hTRANSPORT V₀ V ⟨_, hV₀W⟩ w rfl hVV₀ hVw
        have hd₀ := (hrest ⟨_, hV₀W⟩).2 V₀ rfl hfix₀
        refine ⟨depth V₀ * placeWidthChar q N (w : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) N)) * m, ?_⟩
        rw [hepw _ hV₀W] at hm
        rw [hm, pow_mul, ht, hd₀, ← pow_mul, ← pow_mul, mul_assoc]

  have h3c := PlaceSpecialization.depthDual_add_mem_range_gramMap_of_isPrincipal_widthChar N q hq hqN A hA
    W hW data hKr hα hβ P R hmodel hO hreg hval Kf cf ϖf hϖf hvalA hxyW e' he'0 _ hpr' hsuppZ depthZ hreadZ s₀ hs₀

  have hgood₂ : P.IsGoodDiv ((D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) - (D₁ : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)))) := fun V hV => by
    by_contra hns
    refine (Finsupp.mem_support_iff.mp hV) ?_
    rw [Finsupp.sub_apply, hoff V hns, sub_self]
  have hpr₂ : Divisor.IsPrincipal ((D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) - (D₁ : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)))) :=
    Comp554.isPrincipal_sub_of_mk_eq_mk hmk₁
  have hsupp₂ : ∀ V ∈ ((D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) - (D₁ : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)))).support, P.IsStrictFst V ∨ P.IsStrictSnd V ∨ P.reduceFst V ∈ W :=
    fun V hV => (hgood₂ V hV).elim Or.inl (fun h => Or.inr (Or.inl h))
  have h3c₂ := PlaceSpecialization.depthDual_add_mem_range_gramMap_of_isPrincipal_widthChar N q hq hqN A hA
    W hW data hKr hα hβ P R hmodel hO hreg hval Kf cf ϖf hϖf hvalA hxyW e' he'0 _ hpr₂ hsupp₂ depthZ
    (fun w V hV hred => absurd (show P.reduceFst V ∈ W by rw [hred]; exact w.2)
      (Comp554.reduceFst_notMem_of_strict P hWfix (hgood₂ V hV))) s₀ hs₀
  have hdZ₂ := Comp554.depthDual_eq_zero_of_forall_reduceFst_notMem P (arithFrobC q (ResidueField A) N) W depthZ
    ((D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) - (D₁ : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)))) (fun V hV => Comp554.reduceFst_notMem_of_strict P hWfix (hgood₂ V hV))

  have hMASS : P.depthDual (arithFrobC q (ResidueField A) N) W depthZ ((D' : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) - heckeDivBar hαℓ hβℓ (D₁ : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)))) =
      (e' : ℤ) • (P.depthDual (arithFrobC q (ResidueField A) N) W depth (D' : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) -
        (heckeCharacterAction B hrow).dualMap (P.depthDual (arithFrobC q (ResidueField A) N) W depth (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))))) := by

    have ha : P.depthDual (arithFrobC q (ResidueField A) N) W depthZ (D' : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) = (e' : ℤ) • P.depthDual (arithFrobC q (ResidueField A) N) W depth (D' : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) :=
      Comp554.depthDual_eq_smul_of_forall_mem_support P (arithFrobC q (ResidueField A) N) W depth depthZ e' (D' : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) fun V hV hVW => by
        have hn := hdepthZ V ⟨_, hVW⟩ (e' * depth V) rfl
          (by rw [(hrest ⟨_, hVW⟩).2 V rfl (hD' V hV).1, ← pow_mul, mul_comm])
        rw [hn]
        push_cast
        rfl

    have hb : P.depthDual (arithFrobC q (ResidueField A) N) W depthZ
        (heckeDivBar hαℓ hβℓ (P.fstDiv (D₁ : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) + P.sndDiv (D₁ : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))))) = 0 :=
      Comp554.depthDual_eq_zero_of_forall_reduceFst_notMem P (arithFrobC q (ResidueField A) N) W depthZ _ fun V hV =>
        Comp554.reduceFst_notMem_of_strict P hWfix (hgT₁ V hV)

    have hc₀ : P.depthDual (arithFrobC q (ResidueField A) N) W depth (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) = P.depthDual (arithFrobC q (ResidueField A) N) W depth Dnode := by
      have hz := Comp554.depthDual_eq_zero_of_forall_reduceFst_notMem P (arithFrobC q (ResidueField A) N) W depth ((D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) - Dnode)
        fun V hV => by

          have hstr : P.IsStrictFst V ∨ P.IsStrictSnd V := by
            by_contra hns
            refine Finsupp.mem_support_iff.mp hV ?_
            rw [Finsupp.sub_apply, hDnode, Comp554.sub_fstDiv_add_sndDiv_apply, if_neg hns, hoff V hns, sub_self]
          exact Comp554.reduceFst_notMem_of_strict P hWfix hstr
      rw [Comp554.depthDual_sub] at hz
      exact sub_eq_zero.mp hz

    have hPERNODE : ∀ V₀ ∈ Dnode.support,
        P.depthDual (arithFrobC q (ResidueField A) N) W depthZ (heckeDivBar hαℓ hβℓ (Finsupp.single V₀ 1)) =
          (e' : ℤ) • (heckeCharacterAction B hrow).dualMap (P.depthDual (arithFrobC q (ResidueField A) N) W depth (Finsupp.single V₀ 1)) := by
      intro V₀ hV₀
      have hx₀ := hDnode_supp V₀ hV₀
      obtain ⟨-, -, hfix₀, hV₀W⟩ := hx₀
      have hdv := he'dvd _ hV₀W
      obtain ⟨m₀, hm₀⟩ := hdv
      have hd₀ := (hrest ⟨_, hV₀W⟩).2 V₀ rfl hfix₀

      have hdZT : ∀ V ∈ (heckeDivBar hαℓ hβℓ (Finsupp.single V₀ 1)).support, ∀ w' : ↥W,
          P.reduceFst V = ↑w' → (depthZ V : ℤ) = depth V₀ * placeWidthChar q N (w' : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) N)) * m₀ := by
        intro V hV w' hVw'
        have ht := hTRANSPORT V₀ V ⟨_, hV₀W⟩ w' rfl hV hVw'
        have hn := hdepthZ V w' (depth V₀ * placeWidthChar q N (w' : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) N)) * m₀) hVw' (by
          rw [hepw _ hV₀W] at hm₀
          rw [hm₀, pow_mul, ht, hd₀, ← pow_mul, ← pow_mul, mul_assoc])
        rw [hn]
        push_cast
        ring

      have hCNT := (ModularCurve.PlaceSpecialization.mapDomain_reduceFst_heckeDivBar_single_apply_eq_correspondence_of_ne N q hq A hA data hKr hα hβ P ℓ hℓq hαℓ hβℓ hβc hαc V₀ hHF).1

      have hMC : ∀ w' : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) N),
          (placeWidthChar q N w' : ℤ) *
              Divisor.correspondence (heckeBetaC (ResidueField A) N ℓ) (heckeAlphaC (ResidueField A) N ℓ) hβc hαc
                (Finsupp.single (P.reduceFst V₀) 1) w' =
            (placeWidthChar q N (P.reduceFst V₀) : ℤ) *
              Divisor.correspondence (heckeAlphaC (ResidueField A) N ℓ) (heckeBetaC (ResidueField A) N ℓ) hαc hβc
                (Finsupp.single w' 1) (P.reduceFst V₀) := fun w' =>
        ModularCurve.placeWidthChar_mul_correspondence_heckeBetaC_heckeAlphaC_single_apply_eq_of_prime N ℓ q ℓ.2 hℓq hqN (fun h => hℓ (dvd_mul_of_dvd_left h q)) hαc hβc (P.reduceFst V₀) w'

      have hTVW : ∀ V ∈ (heckeDivBar hαℓ hβℓ (Finsupp.single V₀ 1)).support, P.reduceFst V ∈ W := fun V hV =>
        (hW _).2 (ModularCurve.PlaceSpecialization.reduceFst_mem_ssPlaces_of_mem_support_heckeDivBar_single_of_ne N q hq A hA data hKr hα hβ P ℓ hℓq hαℓ hβℓ V₀ V ((hW _).1 hV₀W) hV)

      have hdZT' : ∀ V ∈ (heckeDivBar hαℓ hβℓ (Finsupp.single V₀ 1)).support,
          (depthZ V : ℤ) = depth V₀ * placeWidthChar q N (P.reduceFst V) * m₀ := fun V hV =>
        hdZT V hV ⟨_, hTVW V hV⟩ rfl

      have ht₀ : ((⟨smulNodePair (arithFrobC q (ResidueField A) N) (P.reduceFst V₀),
          smulNodePair_mem_nodePairsOfPlaces (arithFrobC q (ResidueField A) N) hV₀W⟩ :
            ↥(nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W)) :
          Place (ResidueField A) (modularFunctionFieldC (ResidueField A) N) × Place (ResidueField A) (modularFunctionFieldC (ResidueField A) N)).1 =
          P.reduceFst V₀ :=
        smulNodePair_fst _ _
      have hMCB : ∀ s : ↥(nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W),
          (placeWidthChar q N (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) N) × Place (ResidueField A) (modularFunctionFieldC (ResidueField A) N)).1 : ℤ) *
              Divisor.correspondence (heckeBetaC (ResidueField A) N ℓ) (heckeAlphaC (ResidueField A) N ℓ) hβc hαc
                (Finsupp.single (P.reduceFst V₀) 1) (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) N) × Place (ResidueField A) (modularFunctionFieldC (ResidueField A) N)).1 =
            (placeWidthChar q N (P.reduceFst V₀) : ℤ) *
              B s ⟨smulNodePair (arithFrobC q (ResidueField A) N) (P.reduceFst V₀),
                smulNodePair_mem_nodePairsOfPlaces (arithFrobC q (ResidueField A) N) hV₀W⟩ := by
        intro s
        have hMC' := hMC (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) N) × Place (ResidueField A) (modularFunctionFieldC (ResidueField A) N)).1
        rw [hMC', hB hαc hβc _ s, ht₀]
      have hew₀ : (e' : ℤ) = placeWidthChar q N (P.reduceFst V₀ : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) N)) * m₀ := by
        rw [← hepw _ hV₀W]
        exact_mod_cast hm₀
      exact Comp554.depthDual_perNode P (arithFrobC q (ResidueField A) N) W depth depthZ B hrow (placeWidthChar q N) V₀ hV₀W
        _ _ (m₀ : ℤ) (e' : ℤ) hdZT' hCNT hMCB hew₀

    have hc := Comp554.addMonoidHom_apply_eq_smul_of_eq_on_support_single
      ((Comp554.depthDualHom P (arithFrobC q (ResidueField A) N) W depthZ).comp (heckeDivBar hαℓ hβℓ))
      (((heckeCharacterAction B hrow).dualMap).toAddMonoidHom.comp (Comp554.depthDualHom P (arithFrobC q (ResidueField A) N) W depth))
      (e' : ℤ) Dnode hPERNODE
    have hc' : P.depthDual (arithFrobC q (ResidueField A) N) W depthZ (heckeDivBar hαℓ hβℓ Dnode) =
        (e' : ℤ) • (heckeCharacterAction B hrow).dualMap (P.depthDual (arithFrobC q (ResidueField A) N) W depth (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)))) :=
      hc.trans (congrArg (fun x => (e' : ℤ) • (heckeCharacterAction B hrow).dualMap x) hc₀.symm)
    exact Comp554.mass_combine (Comp554.depthDualHom P (arithFrobC q (ResidueField A) N) W depthZ) (e' : ℤ) _ _ _ _ _ _ hTdec ha hb hc'

  have hsndNode : P.sndDiv (heckeDivBar hαℓ hβℓ Dnode) = 0 :=
    Comp554.sndDiv_eq_zero_of_forall_not P fun V hV hs =>
      Comp554.reduceFst_notMem_of_strict P hWfix (Or.inr hs) (hSUPPW V hV)
  have hdegZ : Divisor.degree (P.sndDiv ((D' : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) - heckeDivBar hαℓ hβℓ (D₁ : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))))) =
      Divisor.degree (P.sndDiv (D' : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)))) -
        ((((ℓ : ℕ) : ℤ)) + 1) * Divisor.degree (P.sndDiv (D₁ : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)))) := by
    rw [Comp554.sndDiv_sub, map_sub, hTdec, Comp554.sndDiv_add, map_add, hsndT₁, hsndNode, map_zero, add_zero,
      Comp554.degree_heckeDivBar (N * q) ℓ hℓNq hαℓ hβℓ]

  have hwe : (fun s : ↥(nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W) => e' * widthOfPlaces (arithFrobC q (ResidueField A) N) W (placeWidthChar q N) s) =
      fun s => e' * widthOfPlaces (arithFrobC q (ResidueField A) N) W e s := by
    funext s
    rw [widthOfPlaces_apply, widthOfPlaces_apply, hepw _ (fst_mem_of_mem_nodePairsOfPlaces s.2)]
  have hrg := congrArg (fun w => LinearMap.range (gramMap w)) hwe
  have hes₀ : (((e' * placeWidthChar q N s₀.1 : ℕ)) : ℤ) = (e' : ℤ) * (e s₀.1 : ℤ) := by
    rw [hepw _ (fst_mem_of_mem_nodePairsOfPlaces hs₀)]
    push_cast
    rfl
  simp only [hrg, hes₀, hMASS, hdegZ] at h3c
  simp only [hrg, hes₀, hdZ₂, zero_add, Comp554.sndDiv_sub, map_sub] at h3c₂

  exact Comp554.annulus_algebra (widthOfPlaces (arithFrobC q (ResidueField A) N) W e) B hrow hsym ⟨s₀, hs₀⟩ e' he'0 _ _ _ _ _ h3c h3c₂

end S_ModularCurve_PlaceSpecialization_componentGroupProj_depthDual_add_eq_heckeComponentAction_of_heckeGen_smul_of_lt_five_of_not_isGoodDiv
end P2MW
export P2MW.S_ModularCurve_PlaceSpecialization_componentGroupProj_depthDual_add_eq_heckeComponentAction_of_heckeGen_smul_of_lt_five_of_not_isGoodDiv (solution)
