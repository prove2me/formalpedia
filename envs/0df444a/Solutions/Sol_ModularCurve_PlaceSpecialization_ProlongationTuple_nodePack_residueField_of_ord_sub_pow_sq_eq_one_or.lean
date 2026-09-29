-- Prove2me | solution 1 for ModularCurve.PlaceSpecialization.ProlongationTuple.nodePack_residueField_of_ord_sub_pow_sq_eq_one_or
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/82b59412-1f20-5cc0-b8e9-6d3a28d53fb4

import Definitions.Def_ModularCurve_NodeLocalizedPlaces
import Definitions.Def_ModularCurve_SpecializationMap
import Theorems.Thm_ModularCurve_PlaceSpecialization_exists_ord_sub_pow_sq_eq_one_of_mem_ssPlaces
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_nonempty_nodeCoordinates_bot_of_ord_sub_pow_sq_eq_one
import Theorems.Thm_ModularCurve_exists_isAtkinLehnerAutFull_of_prime_of_not_dvd
import Theorems.Thm_ModularCurve_functionFieldGeneration
import Theorems.Thm_ModularCurve_NodeLocalized_exists_forall_redRestrict_eq_zero_iff_and_natCast_eq_pow_mul
import Theorems.Thm_ModularCurve_PlaceSpecialization_frobOnPlacesGeomLevel_frobOnPlacesGeomLevel_eq_self_of_mem_ssPlaces
import Theorems.Thm_ModularCurve_hasPrincipalDivisors_modularFunctionFieldBar_unconditional
import Theorems.Thm_ModularCurve_arithFrobC_smul_eq_frobOnPlacesGeomLevel
import Definitions.Def_FieldTheory_RatAlgClosureGalois
import Definitions.Def_AlgebraicCurve_PlaceEvaluationAlgebra
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_valueIntegralityLaw_of_orderLawFixed
import Theorems.Thm_ModularCurve_arithmeticGalois_smul_eq_self_and_evalAt_smul_of_coe_mem_fieldOver
import Theorems.Thm_MWFL_exists_finiteDimensional_fixingSubgroup_smul_eq_place
import Theorems.Thm_ModularCurve_isRational_place_modularFunctionFieldBar
import Theorems.Thm_ModularCurve_PlaceSpecialization_reduceFst_surjective
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_hasValue_nodeResidue_red_of_hasValue_of_sp_eq_spPlace
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_isLocalRing_and_isNoetherianRing_nodeIntegersOver_of_sp_eq_spPlace
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_nodeResidue_saturated_of_sp_eq_spPlace_residueField
import Definitions.Def_ValuationSubring_ReduceAt
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_nodePack_residueField_of_ord_sub_pow_sq_eq_one_or
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent"
p2m_attr_erase "instance" "ModularCurve.B3.instIsElliptic_goodModel ModularCurve.instIsScalarTowerJAdjoin WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular GaloisRepAdic.instAddCommGroup GaloisRepAdic.instFree GaloisRepAdic.instFinite GaloisRepAdic.instModule ResidualGaloisRep.instModule ResidualGaloisRep.instModuleFinite ResidualGaloisRep.instAddCommGroup WeierstrassCurve.Affine.Point.instFinite AlgebraicCurve.CurveModel.isProper AlgebraicCurve.CurveModel.isIntegral AlgebraicCurve.CurveModel.smooth ModularCurve.IgusaScheme.isOpenImmersion_fInf ModularCurve.IgusaScheme.isOpenImmersion_ιInf ModularCurve.IgusaScheme.fact_jFull_ne_zero ModularCurve.IgusaScheme.isOpenImmersion_ιFin ModularCurve.IgusaScheme.isOpenImmersion_fFin AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing"
p2m_attr_erase "instance" "AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin AlgebraicCurve.CurveModel.chartRing_finitePresentation ModularCurve.NodeLocalized.isScalarTower_K_fieldOver_bar ModularCurve.NodeLocalized.algebraFieldOverBar ModularCurve.NodeLocalized.algebra_isIntegral_fieldOver_bar ModularCurve.NodeLocalized.isScalarTower_fieldOver_bar_laurent ModularCurve.NodeLocalized.charZero_fieldOver ModularCurve.NodeLocalized.algebraFieldOver ModularCurve.NodeLocalized.charZero_laurentSeries_algClosure ModularCurve.instIsElliptic_tateBase ModularCurve.NodeLocalized.isLocalization_nodeDenominators ModularCurve.NodeLocalized.algebraEvalRange ModularCurve.NodeLocalized.isLocalRing_modularLocalizedAtPoint instTopologicallyFGOfFiniteType AdicCompletion.instIsLocalRingMaximalIdeal ModularCurve.numberField_of_finiteDimensional CuspForm.heckeAlgebra.instCommRing CuspForm.heckeAlgebra.instIsMulCommutative CuspForm.heckeAlgebra.instIsAddTorsionFree ModularCurve.CuspSpace.instNonempty ModularCurve.CuspSpace.instSubsingletonOfOne ModularCurve.CuspSpace.instFinite ModularCurve.instAlgebraIntermediateFieldLaurent ModularCurve.instIsScalarTowerKaehlerIntermediateFieldLaurent ModularCurve.instIsScalarTowerIntermediateFieldLaurent ModularCurve.instModuleKaehlerIntermediateFieldLaurent FLT.Gamma0FundamentalSet.instContinuousConstSMulSpecialLinearGroupFinOfNatNatIntUpperHalfPlane_definitions FLT.HyperbolicMeasure.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatIntUpperHalfPlaneVolume_definitions FLT.HyperbolicMeasure.instIsOpenPosMeasureUpperHalfPlaneVolume_definitions FLT.L2ProductionInstance.isFiniteMeasure_gamma0 FLT.L2ProductionInstance.countable_SL2Z FLT.L2ProductionInstance.countable_quotient FLT.L2ProductionInstance.nontrivial_gamma0L2"
p2m_attr_erase "instance" "HeckeEis.instModuleCoeffH1par HeckeEis.instAddCommGroupCoeffH1par HeckeEis.instFiniteIndexHeckeUpper instFieldLaurentSeriesAlgClosureRat instAlgebraModularFunctionFieldBar ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instAlgebraResidueFieldSubtypeMemValuationSubringGaussBaseResOne ModularCurve.PlaceSpecialization.LevelOneProlongationPair.algGaussBase instAlgebraModularFunctionFieldFullC ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instAlgebraSubtypeMemValuationSubringGaussBaseResOne ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instAlgebraSubtypeMemValuationSubringGaussBaseResTwo instFieldModularFunctionFieldC ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isScalarTower_resOne instFieldLaurentSeries' ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isScalarTower_resTwo instModuleModularFunctionFieldBar ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isLocalHom_resBase₁ instAlgebraModularFunctionFieldC ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isLocalHom_constToGaussBase ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instFieldResOne instFieldModularFunctionFieldBar ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instAlgebraResidueFieldSubtypeMemValuationSubringGaussBaseResTwo ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instFieldResTwo instFieldModularFunctionFieldFullC ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isScalarTower_gaussBase instAlgebraLaurentSeriesAlgClosureRat ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isLocalHom_resBase₂ ModularCurve.PlaceSpecialization.LevelOneProlongationPair.algResidueConst instCommRingModularFunctionFieldBar"
p2m_attr_erase "simp" "AlgebraicCurve.Pic.baseChange_mk AlgebraicCurve.Place.forgetConstants_toValuationSubring AlgebraicCurve.Place.constantFieldEquiv_symm_apply AlgebraicCurve.Place.ord_forgetConstants AlgebraicCurve.Place.extendConstants_toValuationSubring AlgebraicCurve.Place.constantFieldEquiv_apply_toValuationSubring AlgebraicCurve.Place.mem_fiberConstants AlgebraicCurve.Place.restrictConstants_toValuationSubring ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg"
p2m_attr_erase "simp" "WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong ModularCurve.cuspCount_one ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five"
p2m_attr_erase "simp" "ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule HahnSeries.ramScale_apply WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual"
p2m_attr_erase "simp" "AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm ModularCurve.ProjectiveLine.map_mk ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂"
p2m_attr_erase "simp" "WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero"
p2m_attr_erase "simp" "TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff ModularCurve.Gamma0Pair.map_toCurve WeierstrassCurve.mapPoint_eq_ratPointMap ModularCurve.Gamma0Pair.map_gen ModularCurve.Gamma0Pair.map_eq_gamma0PairMap ModularCurve.ModuliPoint.map_eq_moduliPointMapRingHom ModularCurve.ModuliPoint.map_mk WeierstrassCurve.mapPointHom_apply WeierstrassCurve.mapPoint_zero WeierstrassCurve.Universal.halveX_zero WeierstrassCurve.Universal.specialize_X_one WeierstrassCurve.Universal.coeff_halve WeierstrassCurve.Universal.specialize_X_two WeierstrassCurve.Universal.halveCoeff_zero WeierstrassCurve.Universal.specialize_X_four WeierstrassCurve.Universal.coeff_halveX WeierstrassCurve.Universal.specialize_X_three WeierstrassCurve.Universal.specialize_X_zero GoodReductionJacobian.RelativePic0Designation.mk.sizeOf_spec GoodReductionJacobian.AvatarSchemeBridge.mk.injEq"
p2m_attr_erase "simp" "MilneJVScheme.JacobianSchemeData.mk.injEq GoodReductionJacobian.AvatarSchemeBridge.mk.sizeOf_spec MilneJVScheme.JacobianSchemeData.mk.sizeOf_spec GoodReductionJacobian.RelativePic0Designation.mk.injEq NeronModelInfra.specGenericFibreInclusion_eq NeronModelInfra.genericFibreRestrict_coe_comp_snd NeronModelInfra.genericFibreRestrict_coe_comp_fst GoodReductionJacobian.schemeHomOverComp_coe NeronModelInfra.schemeHomOverEquivOverHom_apply GoodReductionJacobian.RelativeGroupLaw.mk.sizeOf_spec NeronModelInfra.schemeHomOverEquivOverHom_symm_apply NeronModelInfra.overHomToSchemeHomOver_coe GoodReductionJacobian.RelativeGroupLaw.mk.injEq NeronModelInfra.overHomToSchemeHomOver_schemeHomOverToOverHom NeronModelInfra.schemeHomOverToOverHom_left NeronModelInfra.schemeHomOverToOverHom_overHomToSchemeHomOver NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe GaloisRepAdic.mk.injEq GaloisRepAdic.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.injEq ResidualGaloisRep.mk.sizeOf_spec ResidualGaloisRep.mk.injEq ResidualGaloisRep.Equiv.mk.sizeOf_spec ResidualGaloisRep.Equiv.mk.injEq AlgebraicCurve.CurveModel.mk.injEq AlgebraicCurve.CurveModel.mk.sizeOf_spec ModularCurve.IgusaScheme.ιInf_igusaTo_assoc ModularCurve.IgusaScheme.coe_jFull ModularCurve.IgusaScheme.coe_jInvChartInf ModularCurve.IgusaScheme.coe_jChartFin ModularCurve.IgusaScheme.ιFin_igusaTo ModularCurve.IgusaScheme.ιInf_igusaTo ModularCurve.IgusaScheme.ιFin_igusaTo_assoc"
p2m_attr_erase "simp" "AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces ModularCurve.coe_nodeEquiv_symm_apply ModularCurve.frobNodePair_jOfNode ModularCurve.jOfNode_mk ModularCurve.widthOf_mk ModularCurve.frobNodePairEmb_apply ModularCurve.card_nodePairsOf ModularCurve.frobNodePair_snd ModularCurve.coe_nodeEquiv_apply ModularCurve.frobNodePair_fst ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst ModularCurve.NodeLocalized.coe_modularEvalAt AdicCompletion.evalₐ_mapₐ AdicCompletion.mapAlgEquivOfBijective_apply AdicCompletion.levelMapₐ_mk AdicCompletion.mapₐ_of AdicCompletion.mapAlgEquiv_symm_apply AdicCompletion.mapAlgEquiv_apply AdicCompletion.evalₐ_ofLevelwiseEquiv AdicCompletion.evalₐ_levelwiseHom AdicCompletion.localizationEquiv_of AdicCompletion.evalₐ_ofLevelwiseEquiv_symm"
p2m_attr_erase "simp" "Localization.AtPrime.quotientPowEquiv_mk ModularCurve.LambdaModularPolynomialData.mk.sizeOf_spec ModularCurve.LambdaModularPolynomialData.mk.injEq AdicCompletion.transportOf_of AdicCompletion.selfCompletion_smul_of AdicCompletion.tensorRingEquiv_tmul AdicCompletion.completionOfAlgHom_apply AdicCompletion.completionBaseChangeHom_of AdicCompletion.tensorRingHom_tmul AdicCompletion.stabilizerToCompletionAut_of ModularCurve.symPoly_zero ModularCurve.coe_levelPolynomialEquiv_apply ModularCurve.coe_levelBaseRingDescent_apply ModularCurve.levelConst_apply ModularCurve.coe_laurentDescent_apply ModularCurve.dualHeckeRep_apply_apply ModularCurve.coe_segmentPath ModularCurve.cuspHeckeAeval_heckeGen ModularCurve.coe_periodLatticeRestrict_apply CuspForm.heckeAlgebra.coe_U CuspForm.heckeAlgebra.coe_T ModularForm.coe_heckeTLin_apply CuspForm.coe_heckeULin_apply CuspForm.coe_heckeTLin_apply ModularForm.coe_heckeULin_apply ModularCurve.ComplexPlaceDictionary.mk.injEq ModularCurve.ComplexPlaceDictionary.mk.sizeOf_spec ModularCurve.Period.IsEquivariantPrimitive.periodHom_apply ModularCurve.Period.IsEquivariantPrimitive.period_one ModularCurve.CuspSpace.cuspDenomAux_infty ModularCurve.CuspSpace.cuspDenomAux_coe ModularCurve.CuspSpace.cuspDenom_mk_zero ModularCurve.CuspSpace.cuspDenom_mk_infty ModularCurve.mapGL_apply_coe ModularCurve.ratPoint_one_zero ModularCurve.ratPoint_zero_right ModularCurve.CuspSpace.fromCoset_mk ModularCurve.CuspSpace.cuspDenom_mk ModularCurve.ratPoint_zero_one ModularCurve.qEulerFun_coeff"
p2m_attr_erase "simp" "ModularCurve.diffQExp_D ModularCurve.qEulerOn_apply ModularCurve.qEuler_coeff FLT.TruncatedDomainPartition.unipotentDiagonalSum_zero HeckeEis.coeffCoboundaryMap_apply HeckeEis.heckeConjMat_apply_one_one HeckeEis.coe_heckeConjSL HeckeEis.mem_heckeUpperSL HeckeEis.resHom_apply HeckeEis.heckeConjMat_apply_zero_one HeckeEis.coe_transferAux HeckeEis.coe_heckeConj HeckeEis.alphaMat_apply_one_one HeckeEis.heckeConjMat_apply_one_zero HeckeEis.alphaMat_apply_zero_one HeckeEis.pullbackHom_apply HeckeEis.alphaMat_apply_one_zero HeckeEis.alphaMat_apply_zero_zero HeckeEis.heckeConjMat_apply_zero_zero ModularCurve.frobeniusPullbackGeomLevelUnconditional_single ModularCurve.frobeniusPushforwardGeomLevelUnconditional_single ModularCurve.frobeniusGeomLevelUnconditional_apply_coe ModularCurve.PlaceSpecialization.LevelOneProlongationPair.mk.sizeOf_spec ModularCurve.PlaceSpecialization.LevelOneProlongationPair.residue₂_apply ModularCurve.PlaceSpecialization.LevelOneProlongationPair.residue₁_apply ModularCurve.PlaceSpecialization.LevelOneProlongationPair.mk.injEq ModularCurve.PlaceSpecialization.LevelOneProlongationPair.coe_gaussOrderToIntegers₂ ModularCurve.PlaceSpecialization.LevelOneProlongationPair.coe_gaussOrderToIntegers₁ ModularCurve.PlaceSpecialization.LevelOneProlongationPair.coe_toIntegers₁ ModularCurve.PlaceSpecialization.LevelOneProlongationPair.coe_constToGaussBase ModularCurve.PlaceSpecialization.LevelOneProlongationPair.coe_toIntegers₂"
set_option synthInstance.maxHeartbeats 1600000

p2m_open "AlgebraicCurve IsLocalRing ModularCurve P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_nodePack_residueField_of_ord_sub_pow_sq_eq_one_or.ModularCurve"
open ModularCurve.PlaceSpecialization ModularCurve.PlaceSpecialization.ProlongationTuple

namespace ModularCurve
p2m_export "ModularCurve" "PlaceSpecialization.ProlongationTuple modularFunctionFieldBar ModularPolynomialData jqModC jqNModC modularFunctionFieldC jqModC_mem jqNModC_mem PlaceSpecialization HeckeAlphaBarIntegral HeckeBetaBarIntegral frobOnPlacesGeomLevel KroneckerCongruence ssPlaces IsAffineGeomPlace arithFrobC IsAtkinLehnerAutFull atkinLehnerInvolutionFull isAtkinLehnerAutFull_atkinLehnerInvolutionFull NodeLocalized.coeffSubring NodeLocalized.redRestrict NodeLocalized.fieldOver CharPModel.FibreModel PlaceSpecialization.exists_ord_sub_pow_sq_eq_one_of_mem_ssPlaces exists_isAtkinLehnerAutFull_of_prime_of_not_dvd functionFieldGeneration NodeLocalized.exists_forall_redRestrict_eq_zero_iff_and_natCast_eq_pow_mul PlaceSpecialization.frobOnPlacesGeomLevel_frobOnPlacesGeomLevel_eq_self_of_mem_ssPlaces hasPrincipalDivisors_modularFunctionFieldBar_unconditional arithFrobC_smul_eq_frobOnPlacesGeomLevel PlaceSpecialization.ProlongationTuple.valueIntegralityLaw_of_orderLawFixed arithmeticGalois_smul_eq_self_and_evalAt_smul_of_coe_mem_fieldOver isRational_place_modularFunctionFieldBar PlaceSpecialization.reduceFst_surjective"
p2m_open "ModularCurve"

private theorem nodeLocalized_fieldOver_mono (M : ℕ) [NeZero M]
    {K K' : IntermediateField ℚ (AlgebraicClosure ℚ)} (hKK' : K ≤ K') :
    NodeLocalized.fieldOver M K ≤ NodeLocalized.fieldOver M K' := by
  unfold NodeLocalized.fieldOver
  refine Subfield.closure_mono (Set.union_subset_union_left _ ?_)
  rintro _ ⟨c, rfl⟩
  exact ⟨⟨(c : AlgebraicClosure ℚ), hKK' c.2⟩, rfl⟩

section

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
  {k : Type*} [Field k] [CharP k q] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
  {P : PlaceSpecialization A q N data hKr k red hα hβ} (R : ProlongationTuple P)
  {w : Place k (modularFunctionFieldC k N)}

private theorem mem_nodeIntegersOver_of_le {K K' : IntermediateField ℚ (AlgebraicClosure ℚ)} (hKK' : K ≤ K')
    {f : ↥(modularFunctionFieldBar (N * q))} (hf : f ∈ R.nodeIntegersOver K w) : f ∈ R.nodeIntegersOver K' w :=
  ⟨hf.1, nodeLocalized_fieldOver_mono (N * q) hKK' hf.2⟩

private def nodeCoordinatesOfLe [IsAlgClosed k] {K K' : IntermediateField ℚ (AlgebraicClosure ℚ)} (hKK' : K ≤ K')
    (c : R.NodeCoordinates K w) : R.NodeCoordinates K' w where
  x := ⟨c.x, mem_nodeIntegersOver_of_le R hKK' c.x.2⟩
  y := ⟨c.y, mem_nodeIntegersOver_of_le R hKK' c.y.2⟩
  x_fst := c.x_fst
  x_snd := c.x_snd
  y_snd := c.y_snd
  y_fst := c.y_fst

private theorem nonempty_nodeCoordinates_of_mem_ssPlaces [IsAlgClosed k] [DecidableEq k] (hqN : ¬ q ∣ N)
    (hw : w ∈ ssPlaces q N k)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) : Nonempty (R.NodeCoordinates K w) := by
  obtain ⟨g₀, y, g, gbar, h₀, hg, hy, hgbar, hordw, hordφ, hpole⟩ :=
    PlaceSpecialization.exists_ord_sub_pow_sq_eq_one_of_mem_ssPlaces P hqN w hw
  have hAL : IsAtkinLehnerAutFull N q (atkinLehnerInvolutionFull N q) :=
    isAtkinLehnerAutFull_atkinLehnerInvolutionFull N q
      (exists_isAtkinLehnerAutFull_of_prime_of_not_dvd N q Fact.out hqN)
  obtain ⟨c⟩ := nonempty_nodeCoordinates_bot_of_ord_sub_pow_sq_eq_one R hAL (functionFieldGeneration (N * q)) w hw
    g₀ y g gbar h₀ hg hy hgbar hordw hordφ hpole
  exact ⟨nodeCoordinatesOfLe R bot_le c⟩

private theorem red_eq_zero_iff_mem_maximalIdeal (hred : Function.Surjective red) (c : A) :
    red c = 0 ↔ c ∈ IsLocalRing.maximalIdeal A := by
  rw [← RingHom.mem_ker, IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective red hred)]

include q in

private theorem exists_uniformizer_coeffSubring (hred : Function.Surjective red)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K] :
    ∃ ϖ : ↥(NodeLocalized.coeffSubring A K),
      ∀ d : ↥(NodeLocalized.coeffSubring A K), NodeLocalized.redRestrict red K d = 0 ↔ ∃ d', d = ϖ * d' := by
  obtain ⟨ϖ, hϖ, -⟩ := NodeLocalized.exists_forall_redRestrict_eq_zero_iff_and_natCast_eq_pow_mul red
    (red_eq_zero_iff_mem_maximalIdeal hred) K
  exact ⟨ϖ, hϖ⟩

end

end ModularCurve

namespace ModularCurve
p2m_export "ModularCurve" "PlaceSpecialization.ProlongationTuple modularFunctionFieldBar ModularPolynomialData jqModC jqNModC modularFunctionFieldC jqModC_mem jqNModC_mem PlaceSpecialization HeckeAlphaBarIntegral HeckeBetaBarIntegral frobOnPlacesGeomLevel KroneckerCongruence ssPlaces IsAffineGeomPlace arithFrobC IsAtkinLehnerAutFull atkinLehnerInvolutionFull isAtkinLehnerAutFull_atkinLehnerInvolutionFull NodeLocalized.coeffSubring NodeLocalized.redRestrict NodeLocalized.fieldOver CharPModel.FibreModel PlaceSpecialization.exists_ord_sub_pow_sq_eq_one_of_mem_ssPlaces exists_isAtkinLehnerAutFull_of_prime_of_not_dvd functionFieldGeneration NodeLocalized.exists_forall_redRestrict_eq_zero_iff_and_natCast_eq_pow_mul PlaceSpecialization.frobOnPlacesGeomLevel_frobOnPlacesGeomLevel_eq_self_of_mem_ssPlaces hasPrincipalDivisors_modularFunctionFieldBar_unconditional arithFrobC_smul_eq_frobOnPlacesGeomLevel PlaceSpecialization.ProlongationTuple.valueIntegralityLaw_of_orderLawFixed arithmeticGalois_smul_eq_self_and_evalAt_smul_of_coe_mem_fieldOver isRational_place_modularFunctionFieldBar PlaceSpecialization.reduceFst_surjective"
p2m_open "ModularCurve"

section

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
  {k : Type*} [Field k] [CharP k q] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
  {P : PlaceSpecialization A q N data hKr k red hα hβ} (R : ProlongationTuple P)
  (K : IntermediateField ℚ (AlgebraicClosure ℚ)) (w : Place k (modularFunctionFieldC k N))

private noncomputable def resOver₁ : ↥(R.nodeIntegersOver K w) →+* ↥(modularFunctionFieldC k N) :=
  (R.nodeResidue₁ w).comp (Subring.inclusion (R.nodeIntegersOver_le K w))

private noncomputable def resOver₂ : ↥(R.nodeIntegersOver K w) →+* ↥(modularFunctionFieldC k N) :=
  (R.nodeResidue₂ w).comp (Subring.inclusion (R.nodeIntegersOver_le K w))

private theorem resOver₁_apply (g : ↥(R.nodeIntegersOver K w)) : resOver₁ R K w g = R.nodeResidue₁ w ⟨g, g.2.1⟩ := rfl

private theorem resOver₂_apply (g : ↥(R.nodeIntegersOver K w)) : resOver₂ R K w g = R.nodeResidue₂ w ⟨g, g.2.1⟩ := rfl

variable {R K w}

private theorem nodeResidue₁_ne_zero_of_isUnit {g : ↥(R.nodeIntegersOver K w)} (hg : IsUnit g) :
    R.nodeResidue₁ w ⟨g, g.2.1⟩ ≠ 0 :=
  (hg.map (resOver₁ R K w)).ne_zero

private theorem nodeResidue₂_ne_zero_of_isUnit {g : ↥(R.nodeIntegersOver K w)} (hg : IsUnit g) :
    R.nodeResidue₂ w ⟨g, g.2.1⟩ ≠ 0 :=
  (hg.map (resOver₂ R K w)).ne_zero

private theorem nodeResidue₁_nodeConst_eq_zero {d : ↥(NodeLocalized.coeffSubring A K)}
    (hd : IsLocalRing.residue A ⟨(d : AlgebraicClosure ℚ), d.2.1⟩ = 0) :
    R.nodeResidue₁ w ⟨R.nodeConst K w d, (R.nodeConst K w d).2.1⟩ = 0 := by
  rw [nodeResidue₁_apply, residue₁_apply]
  have h := @RegularProlongation.residue_algebraMap _ (_) _ _ (_) (_) _ (_) (_) R.R₁ ⟨(d : AlgebraicClosure ℚ), d.2.1⟩
  rw [hd, map_zero] at h
  exact (congrArg R.ι h).trans (map_zero R.ι)

private theorem residue_eq_zero_of_redRestrict_eq_zero (hred : Function.Surjective red)
    {d : ↥(NodeLocalized.coeffSubring A K)} (hd : NodeLocalized.redRestrict red K d = 0) :
    IsLocalRing.residue A ⟨(d : AlgebraicClosure ℚ), d.2.1⟩ = 0 := by
  rw [IsLocalRing.residue_eq_zero_iff, ← IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective red hred),
    RingHom.mem_ker]
  exact hd

private theorem redRestrict_eq_zero_of_forall_iff {ϖ : ↥(NodeLocalized.coeffSubring A K)}
    (hϖ : ∀ d : ↥(NodeLocalized.coeffSubring A K), NodeLocalized.redRestrict red K d = 0 ↔ ∃ d', d = ϖ * d') :
    NodeLocalized.redRestrict red K ϖ = 0 :=
  (hϖ ϖ).mpr ⟨1, (mul_one ϖ).symm⟩

private theorem span_le_maximalIdeal [PerfectField k] [IsLocalRing ↥(R.nodeIntegersOver K w)]
    (hred : Function.Surjective red) (c : R.NodeCoordinates K w) {ϖ : ↥(NodeLocalized.coeffSubring A K)}
    (hϖ : NodeLocalized.redRestrict red K ϖ = 0) :
    Ideal.span {R.nodeConst K w ϖ, c.x, c.y} ≤ IsLocalRing.maximalIdeal ↥(R.nodeIntegersOver K w) := by
  rw [Ideal.span_le]
  rintro g (rfl | rfl | rfl)
  · exact (IsLocalRing.mem_maximalIdeal _).mpr fun h =>
      nodeResidue₁_ne_zero_of_isUnit h (nodeResidue₁_nodeConst_eq_zero (residue_eq_zero_of_redRestrict_eq_zero hred hϖ))
  · exact (IsLocalRing.mem_maximalIdeal _).mpr fun h => nodeResidue₁_ne_zero_of_isUnit h c.x_fst
  · exact (IsLocalRing.mem_maximalIdeal _).mpr fun h => nodeResidue₂_ne_zero_of_isUnit h c.y_snd

private theorem maximalIdeal_eq_span_of_branch_lifts [PerfectField k] [IsLocalRing ↥(R.nodeIntegersOver K w)]
    (hred : Function.Surjective red) (c : R.NodeCoordinates K w) {ϖ : ↥(NodeLocalized.coeffSubring A K)}
    (hϖ : NodeLocalized.redRestrict red K ϖ = 0)
    (L₁ : ∀ g ∈ IsLocalRing.maximalIdeal ↥(R.nodeIntegersOver K w), ∃ h : ↥(R.nodeIntegersOver K w),
      R.nodeResidue₁ w ⟨g - c.y * h, (g - c.y * h).2.1⟩ = 0)
    (L₂ : ∀ g ∈ IsLocalRing.maximalIdeal ↥(R.nodeIntegersOver K w), ∃ h : ↥(R.nodeIntegersOver K w),
      R.nodeResidue₂ w ⟨g - c.x * h, (g - c.x * h).2.1⟩ = 0)
    (L₃ : ∀ g : ↥(R.nodeIntegersOver K w), R.nodeResidue₁ w ⟨g, g.2.1⟩ = 0 → R.nodeResidue₂ w ⟨g, g.2.1⟩ = 0 →
      ∃ b : ↥(R.nodeIntegersOver K w), g = R.nodeConst K w ϖ * b) :
    IsLocalRing.maximalIdeal ↥(R.nodeIntegersOver K w) = Ideal.span {R.nodeConst K w ϖ, c.x, c.y} := by
  refine le_antisymm (fun g hg => ?_) (span_le_maximalIdeal hred c hϖ)

  obtain ⟨h₁, hh₁⟩ := L₁ g hg
  have hy_mem : c.y * h₁ ∈ IsLocalRing.maximalIdeal ↥(R.nodeIntegersOver K w) :=
    Ideal.mul_mem_right _ _ ((IsLocalRing.mem_maximalIdeal _).mpr fun h => nodeResidue₂_ne_zero_of_isUnit h c.y_snd)

  obtain ⟨h₂, hh₂⟩ := L₂ (g - c.y * h₁) (Ideal.sub_mem _ hg hy_mem)

  have hx : resOver₁ R K w c.x = 0 := c.x_fst
  have hy : resOver₂ R K w c.y = 0 := c.y_snd
  have h1 : resOver₁ R K w (g - c.y * h₁ - c.x * h₂) = 0 := by
    have e : resOver₁ R K w (g - c.y * h₁) = 0 := hh₁
    rw [map_sub, e, map_mul, hx, zero_mul, sub_zero]
  have h2 : resOver₂ R K w (g - c.y * h₁ - c.x * h₂) = 0 := hh₂
  obtain ⟨b, hb⟩ := L₃ (g - c.y * h₁ - c.x * h₂) h1 h2

  have hg' : g = R.nodeConst K w ϖ * b + c.x * h₂ + c.y * h₁ := by
    rw [← hb]; ring
  rw [hg']
  refine Ideal.add_mem _ (Ideal.add_mem _ ?_ ?_) ?_
  · exact Ideal.mul_mem_right _ _ (Ideal.subset_span (by simp))
  · exact Ideal.mul_mem_right _ _ (Ideal.subset_span (by simp))
  · exact Ideal.mul_mem_right _ _ (Ideal.subset_span (by simp))

end

end ModularCurve

namespace ModularCurve
p2m_export "ModularCurve" "PlaceSpecialization.ProlongationTuple modularFunctionFieldBar ModularPolynomialData jqModC jqNModC modularFunctionFieldC jqModC_mem jqNModC_mem PlaceSpecialization HeckeAlphaBarIntegral HeckeBetaBarIntegral frobOnPlacesGeomLevel KroneckerCongruence ssPlaces IsAffineGeomPlace arithFrobC IsAtkinLehnerAutFull atkinLehnerInvolutionFull isAtkinLehnerAutFull_atkinLehnerInvolutionFull NodeLocalized.coeffSubring NodeLocalized.redRestrict NodeLocalized.fieldOver CharPModel.FibreModel PlaceSpecialization.exists_ord_sub_pow_sq_eq_one_of_mem_ssPlaces exists_isAtkinLehnerAutFull_of_prime_of_not_dvd functionFieldGeneration NodeLocalized.exists_forall_redRestrict_eq_zero_iff_and_natCast_eq_pow_mul PlaceSpecialization.frobOnPlacesGeomLevel_frobOnPlacesGeomLevel_eq_self_of_mem_ssPlaces hasPrincipalDivisors_modularFunctionFieldBar_unconditional arithFrobC_smul_eq_frobOnPlacesGeomLevel PlaceSpecialization.ProlongationTuple.valueIntegralityLaw_of_orderLawFixed arithmeticGalois_smul_eq_self_and_evalAt_smul_of_coe_mem_fieldOver isRational_place_modularFunctionFieldBar PlaceSpecialization.reduceFst_surjective"
p2m_open "ModularCurve"

section

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
  {k : Type*} [Field k] [CharP k q] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
  {P : PlaceSpecialization A q N data hKr k red hα hβ} (R : ProlongationTuple P)
  {w : Place k (modularFunctionFieldC k N)}

private theorem nw_ord_neg_of_notMem {K' F' : Type*} [Field K'] [Field F'] [Algebra K' F'] (v : Place K' F')
    {f : F'} (hf : f ∉ v.toValuationSubring) : v.ord f < 0 := by
  have hf0 : f ≠ 0 := fun h => hf (h ▸ zero_mem _)
  exact not_le.mp fun h => hf ((v.mem_iff_ord_nonneg hf0).mpr h)

private theorem nw_ord_eq_zero_of_notMem_maximalIdeal {K' F' : Type*} [Field K'] [Field F'] [Algebra K' F']
    (v : Place K' F') {f : F'} (hf : f ∈ v.toValuationSubring)
    (hm : (⟨f, hf⟩ : v.toValuationSubring) ∉ IsLocalRing.maximalIdeal v.toValuationSubring) :
    v.ord f = 0 ∧ f ≠ 0 := by
  have hu : IsUnit (⟨f, hf⟩ : v.toValuationSubring) := by
    by_contra h
    exact hm ((IsLocalRing.mem_maximalIdeal _).mpr h)
  refine ⟨?_, fun h0 => hu.ne_zero (Subtype.ext h0)⟩
  have := v.ord_coe_unit hu.unit
  rwa [IsUnit.unit_spec] at this

private theorem nw_add_one_notMem_maximalIdeal {K' F' : Type*} [Field K'] [Field F'] [Algebra K' F']
    (v : Place K' F') {f : F'} (hf : f ∈ v.toValuationSubring)
    (hm : (⟨f, hf⟩ : v.toValuationSubring) ∈ IsLocalRing.maximalIdeal v.toValuationSubring) :
    (⟨f + 1, add_mem hf (one_mem _)⟩ : v.toValuationSubring) ∉ IsLocalRing.maximalIdeal v.toValuationSubring := by
  intro h
  have h1 : (1 : v.toValuationSubring) ∈ IsLocalRing.maximalIdeal v.toValuationSubring := by
    have := Ideal.sub_mem _ h hm
    rwa [show (⟨f + 1, add_mem hf (one_mem _)⟩ : v.toValuationSubring) - ⟨f, hf⟩ = 1 from
      Subtype.ext (add_sub_cancel_left f 1)] at this
  exact (IsLocalRing.mem_maximalIdeal _).mp h1 isUnit_one

private theorem nw_add_one_notMem {K' F' : Type*} [Field K'] [Field F'] [Algebra K' F'] (v : Place K' F')
    {f : F'} (hf : f ∉ v.toValuationSubring) : f + 1 ∉ v.toValuationSubring := fun h => by
  have h' := sub_mem h (one_mem v.toValuationSubring)
  rw [add_sub_cancel_right] at h'
  exact hf h'

private theorem nw_ord_nodeResidue₁_add_ord_nodeResidue₂_nonneg [DecidableEq k] (hqN : ¬ q ∣ N)
    (hO : R.OrderLawFixed) (hw : w ∈ ssPlaces q N k) (g : ↥(R.nodeIntegers w))
    (h₁ : R.nodeResidue₁ w g ≠ 0) (h₂ : R.nodeResidue₂ w g ≠ 0) :
    0 ≤ w.ord (R.nodeResidue₁ w g) + (frobOnPlacesGeomLevel k N data hKr w).ord (R.nodeResidue₂ w g) := by
  classical
  have hg0 : g ≠ 0 := fun h => h₁ (by rw [h, map_zero])
  have hf0 : (g : ↥(modularFunctionFieldBar (N * q))) ≠ 0 := fun h => hg0 (ZeroMemClass.coe_eq_zero.mp h)
  obtain ⟨D, hD, -⟩ := @HasPrincipalDivisors.exists_divisor _ _ (_) (_) (_)
    (ModularCurve.hasPrincipalDivisors_modularFunctionFieldBar_unconditional (N * q))
    (g : ↥(modularFunctionFieldBar (N * q))) hf0
  have hfix := ModularCurve.PlaceSpecialization.frobOnPlacesGeomLevel_frobOnPlacesGeomLevel_eq_self_of_mem_ssPlaces
    hqN P w hw
  have haff : IsAffineGeomPlace k N w := hw.2.1
  have key := hO (g : ↥(modularFunctionFieldBar (N * q))) g.2.1 g.2.2.1
    (fun h0 => h₁ (by rw [nodeResidue₁_apply, residue₁_apply, h0, map_zero]))
    (fun h0 => h₂ (by rw [nodeResidue₂_apply, residue₂_apply, h0, map_zero])) D hD w hfix haff
  rw [nodeResidue₁_apply, nodeResidue₂_apply, ← key]

  show 0 ≤ (D.sum fun V n => Finsupp.single (P.reduceFst V) n) w
  rw [Finsupp.sum_apply]
  unfold Finsupp.sum
  refine Finset.sum_nonneg fun V _ => ?_
  show 0 ≤ Finsupp.single (P.reduceFst V) (D V) w
  rw [Finsupp.single_apply]
  split_ifs with hV
  · rw [hD V]
    exact R.ord_nonneg_of_mem_nodeIntegers g.2 hV
  · exact le_rfl

private theorem nw_nodeResidue₁_regular [DecidableEq k] (hqN : ¬ q ∣ N) (hO : R.OrderLawFixed)
    (hw : w ∈ ssPlaces q N k) (g : ↥(R.nodeIntegers w)) :
    R.nodeResidue₁ w g = 0 ∨ 0 ≤ w.ord (R.nodeResidue₁ w g) := by
  classical
  rcases eq_or_ne (R.nodeResidue₁ w g) 0 with hz | hz
  · exact Or.inl hz
  refine Or.inr (not_lt.mp fun hneg => ?_)
  have hnot : R.nodeResidue₁ w g ∉ w.toValuationSubring := fun h => not_lt.mpr (w.ord_nonneg_of_mem h) hneg

  by_cases hcase : ∃ h : R.nodeResidue₂ w g ∈ (frobOnPlacesGeomLevel k N data hKr w).toValuationSubring,
      (⟨R.nodeResidue₂ w g, h⟩ : ↥(frobOnPlacesGeomLevel k N data hKr w).toValuationSubring)
        ∈ IsLocalRing.maximalIdeal ↥(frobOnPlacesGeomLevel k N data hKr w).toValuationSubring
  · obtain ⟨hmem, hmax⟩ := hcase
    have hnot' : R.nodeResidue₁ w (g + 1) ∉ w.toValuationSubring := by
      rw [map_add, map_one]; exact nw_add_one_notMem w hnot
    have hmem' : R.nodeResidue₂ w (g + 1) ∈ (frobOnPlacesGeomLevel k N data hKr w).toValuationSubring := by
      rw [map_add, map_one]; exact add_mem hmem (one_mem _)
    have hunit : (⟨R.nodeResidue₂ w (g + 1), hmem'⟩ : ↥(frobOnPlacesGeomLevel k N data hKr w).toValuationSubring)
        ∉ IsLocalRing.maximalIdeal ↥(frobOnPlacesGeomLevel k N data hKr w).toValuationSubring := by
      have e : (⟨R.nodeResidue₂ w (g + 1), hmem'⟩ : ↥(frobOnPlacesGeomLevel k N data hKr w).toValuationSubring)
          = ⟨R.nodeResidue₂ w g + 1, add_mem hmem (one_mem _)⟩ := Subtype.ext (by
        show R.nodeResidue₂ w (g + 1) = R.nodeResidue₂ w g + 1
        rw [map_add, map_one])
      rw [e]
      exact nw_add_one_notMem_maximalIdeal _ hmem hmax
    have hord₂ := nw_ord_eq_zero_of_notMem_maximalIdeal _ hmem' hunit
    have hne₁ : R.nodeResidue₁ w (g + 1) ≠ 0 := fun h => hnot' (by rw [h]; exact zero_mem _)
    have hsum := nw_ord_nodeResidue₁_add_ord_nodeResidue₂_nonneg R hqN hO hw (g + 1) hne₁ hord₂.2
    have hlt : w.ord (R.nodeResidue₁ w (g + 1)) < 0 := nw_ord_neg_of_notMem w hnot'
    have h0 : (frobOnPlacesGeomLevel k N data hKr w).ord (R.nodeResidue₂ w (g + 1)) = 0 := hord₂.1
    omega
  ·
    by_cases hmem : R.nodeResidue₂ w g ∈ (frobOnPlacesGeomLevel k N data hKr w).toValuationSubring
    · have hord₂ := nw_ord_eq_zero_of_notMem_maximalIdeal _ hmem fun hm => hcase ⟨hmem, hm⟩
      have hsum := nw_ord_nodeResidue₁_add_ord_nodeResidue₂_nonneg R hqN hO hw g hz hord₂.2
      have h0 := hord₂.1
      omega
    · have hlt₂ := nw_ord_neg_of_notMem _ hmem
      have hne₂ : R.nodeResidue₂ w g ≠ 0 := fun h => hmem (by rw [h]; exact zero_mem _)
      have hsum := nw_ord_nodeResidue₁_add_ord_nodeResidue₂_nonneg R hqN hO hw g hz hne₂
      omega

private theorem nw_nodeResidue₂_regular [DecidableEq k] (hqN : ¬ q ∣ N) (hO : R.OrderLawFixed)
    (hw : w ∈ ssPlaces q N k) (g : ↥(R.nodeIntegers w)) :
    R.nodeResidue₂ w g = 0 ∨ 0 ≤ (frobOnPlacesGeomLevel k N data hKr w).ord (R.nodeResidue₂ w g) := by
  classical
  rcases eq_or_ne (R.nodeResidue₂ w g) 0 with hz | hz
  · exact Or.inl hz
  refine Or.inr (not_lt.mp fun hneg => ?_)
  have hnot : R.nodeResidue₂ w g ∉ (frobOnPlacesGeomLevel k N data hKr w).toValuationSubring := fun h =>
    not_lt.mpr ((frobOnPlacesGeomLevel k N data hKr w).ord_nonneg_of_mem h) hneg
  by_cases hcase : ∃ h : R.nodeResidue₁ w g ∈ w.toValuationSubring,
      (⟨R.nodeResidue₁ w g, h⟩ : ↥w.toValuationSubring) ∈ IsLocalRing.maximalIdeal ↥w.toValuationSubring
  · obtain ⟨hmem, hmax⟩ := hcase
    have hnot' : R.nodeResidue₂ w (g + 1) ∉ (frobOnPlacesGeomLevel k N data hKr w).toValuationSubring := by
      rw [map_add, map_one]; exact nw_add_one_notMem _ hnot
    have hmem' : R.nodeResidue₁ w (g + 1) ∈ w.toValuationSubring := by
      rw [map_add, map_one]; exact add_mem hmem (one_mem _)
    have hunit : (⟨R.nodeResidue₁ w (g + 1), hmem'⟩ : ↥w.toValuationSubring)
        ∉ IsLocalRing.maximalIdeal ↥w.toValuationSubring := by
      have e : (⟨R.nodeResidue₁ w (g + 1), hmem'⟩ : ↥w.toValuationSubring)
          = ⟨R.nodeResidue₁ w g + 1, add_mem hmem (one_mem _)⟩ := Subtype.ext (by
        show R.nodeResidue₁ w (g + 1) = R.nodeResidue₁ w g + 1
        rw [map_add, map_one])
      rw [e]
      exact nw_add_one_notMem_maximalIdeal _ hmem hmax
    have hord₁ := nw_ord_eq_zero_of_notMem_maximalIdeal _ hmem' hunit
    have hne₂ : R.nodeResidue₂ w (g + 1) ≠ 0 := fun h => hnot' (by rw [h]; exact zero_mem _)
    have hsum := nw_ord_nodeResidue₁_add_ord_nodeResidue₂_nonneg R hqN hO hw (g + 1) hord₁.2 hne₂
    have hlt : (frobOnPlacesGeomLevel k N data hKr w).ord (R.nodeResidue₂ w (g + 1)) < 0 :=
      nw_ord_neg_of_notMem _ hnot'
    have h0 : w.ord (R.nodeResidue₁ w (g + 1)) = 0 := hord₁.1
    omega
  · by_cases hmem : R.nodeResidue₁ w g ∈ w.toValuationSubring
    · have hord₁ := nw_ord_eq_zero_of_notMem_maximalIdeal _ hmem fun hm => hcase ⟨hmem, hm⟩
      have hsum := nw_ord_nodeResidue₁_add_ord_nodeResidue₂_nonneg R hqN hO hw g hord₁.2 hz
      have h0 := hord₁.1
      omega
    · have hlt₁ := nw_ord_neg_of_notMem _ hmem
      have hne₁ : R.nodeResidue₁ w g ≠ 0 := fun h => hmem (by rw [h]; exact zero_mem _)
      have hsum := nw_ord_nodeResidue₁_add_ord_nodeResidue₂_nonneg R hqN hO hw g hne₁ hz
      omega

private theorem nw_hreg [IsAlgClosed k] [DecidableEq k] (hqN : ¬ q ∣ N) (hO : R.OrderLawFixed)
    (hw : w ∈ ssPlaces q N k) (K : IntermediateField ℚ (AlgebraicClosure ℚ)) :
    ∀ g : ↥(R.nodeIntegersOver K w),
      (R.nodeResidue₁ w ⟨g, g.2.1⟩ = 0 ∨ 0 ≤ w.ord (R.nodeResidue₁ w ⟨g, g.2.1⟩)) ∧
      (R.nodeResidue₂ w ⟨g, g.2.1⟩ = 0 ∨ 0 ≤ (arithFrobC q k N • w).ord (R.nodeResidue₂ w ⟨g, g.2.1⟩)) := by
  intro g
  refine ⟨nw_nodeResidue₁_regular R hqN hO hw ⟨g, g.2.1⟩, ?_⟩
  rw [ModularCurve.arithFrobC_smul_eq_frobOnPlacesGeomLevel q k N data hKr w]
  exact nw_nodeResidue₂_regular R hqN hO hw ⟨g, g.2.1⟩

end

end ModularCurve

namespace ModularCurve
p2m_export "ModularCurve" "PlaceSpecialization.ProlongationTuple modularFunctionFieldBar ModularPolynomialData jqModC jqNModC modularFunctionFieldC jqModC_mem jqNModC_mem PlaceSpecialization HeckeAlphaBarIntegral HeckeBetaBarIntegral frobOnPlacesGeomLevel KroneckerCongruence ssPlaces IsAffineGeomPlace arithFrobC IsAtkinLehnerAutFull atkinLehnerInvolutionFull isAtkinLehnerAutFull_atkinLehnerInvolutionFull NodeLocalized.coeffSubring NodeLocalized.redRestrict NodeLocalized.fieldOver CharPModel.FibreModel PlaceSpecialization.exists_ord_sub_pow_sq_eq_one_of_mem_ssPlaces exists_isAtkinLehnerAutFull_of_prime_of_not_dvd functionFieldGeneration NodeLocalized.exists_forall_redRestrict_eq_zero_iff_and_natCast_eq_pow_mul PlaceSpecialization.frobOnPlacesGeomLevel_frobOnPlacesGeomLevel_eq_self_of_mem_ssPlaces hasPrincipalDivisors_modularFunctionFieldBar_unconditional arithFrobC_smul_eq_frobOnPlacesGeomLevel PlaceSpecialization.ProlongationTuple.valueIntegralityLaw_of_orderLawFixed arithmeticGalois_smul_eq_self_and_evalAt_smul_of_coe_mem_fieldOver isRational_place_modularFunctionFieldBar PlaceSpecialization.reduceFst_surjective"
p2m_open "ModularCurve"

section

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
  {k : Type*} [Field k] [CharP k q] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
  {P : PlaceSpecialization A q N data hKr k red hα hβ} (R : ProlongationTuple P)
  {w : Place k (modularFunctionFieldC k N)}

private theorem nw_evalAt_sub_of_mem {K' F' : Type*} [Field K'] [Field F'] [Algebra K' F'] (v : Place K' F')
    (hv : v.IsRational) {f g : F'} (hf : f ∈ v.toValuationSubring) (hg : g ∈ v.toValuationSubring) :
    v.evalAt (f - g) = v.evalAt f - v.evalAt g := by
  apply v.algebraMap_residueField_injective
  rw [map_sub, v.algebraMap_evalAt hv (sub_mem hf hg), v.algebraMap_evalAt hv hf, v.algebraMap_evalAt hv hg,
    ← map_sub]
  rfl

private theorem nw_evalAt_mul_of_mem {K' F' : Type*} [Field K'] [Field F'] [Algebra K' F'] (v : Place K' F')
    (hv : v.IsRational) {f g : F'} (hf : f ∈ v.toValuationSubring) (hg : g ∈ v.toValuationSubring) :
    v.evalAt (f * g) = v.evalAt f * v.evalAt g := by
  apply v.algebraMap_residueField_injective
  rw [map_mul, v.algebraMap_evalAt hv (mul_mem hf hg), v.algebraMap_evalAt hv hf, v.algebraMap_evalAt hv hg,
    ← map_mul]
  rfl

private theorem nw_not_isUnit_of_evalAt_eq_zero {K : IntermediateField ℚ (AlgebraicClosure ℚ)}
    {V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))} (hV : P.reduceFst V = w)
    {u : ↥(R.nodeIntegersOver K w)} (hu : V.evalAt (u : ↥(modularFunctionFieldBar (N * q))) = 0) : ¬ IsUnit u := by
  intro h
  obtain ⟨u', hu'⟩ := h.exists_right_inv
  have hrat := ModularCurve.isRational_place_modularFunctionFieldBar (N * q) V
  have hm : (u : ↥(modularFunctionFieldBar (N * q))) ∈ V.toValuationSubring :=
    R.mem_toValuationSubring_of_mem_nodeIntegers u.2.1 hV
  have hm' : (u' : ↥(modularFunctionFieldBar (N * q))) ∈ V.toValuationSubring :=
    R.mem_toValuationSubring_of_mem_nodeIntegers u'.2.1 hV
  have hmul := nw_evalAt_mul_of_mem V hrat hm hm'
  rw [← MulMemClass.coe_mul, hu', OneMemClass.coe_one, V.evalAt_one, hu, zero_mul] at hmul
  exact one_ne_zero hmul

private theorem nw_hres_of_reduceFst_eq [IsAlgClosed k] [DecidableEq k] (hqN : ¬ q ∣ N) (hO : R.OrderLawFixed)
    (hw : w ∈ ssPlaces q N k) {V₀ : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))}
    (hV₀ : P.reduceFst V₀ = w) (K : IntermediateField ℚ (AlgebraicClosure ℚ)) (hK : FiniteDimensional ℚ K) :
    ∃ (K' : IntermediateField ℚ (AlgebraicClosure ℚ)) (_ : FiniteDimensional ℚ K'), K ≤ K' ∧
      ∀ g : ↥(R.nodeIntegersOver K' w),
        ∃ o : ↥(NodeLocalized.coeffSubring A K'), ¬ IsUnit (g - R.nodeConst K' w o) := by
  obtain ⟨K₀, hK₀, hfixV⟩ := MWFL.exists_finiteDimensional_fixingSubgroup_smul_eq_place (N * q) V₀
  haveI := hK
  haveI := hK₀
  refine ⟨K ⊔ K₀, IntermediateField.finiteDimensional_sup K K₀, le_sup_left, fun g => ?_⟩
  have hrat := ModularCurve.isRational_place_modularFunctionFieldBar (N * q) V₀

  have hcA : V₀.evalAt (g : ↥(modularFunctionFieldBar (N * q))) ∈ A :=
    ModularCurve.PlaceSpecialization.ProlongationTuple.valueIntegralityLaw_of_orderLawFixed R hqN hO w hw
      (g : ↥(modularFunctionFieldBar (N * q))) g.2.1 V₀ hV₀
  have hcK : V₀.evalAt (g : ↥(modularFunctionFieldBar (N * q))) ∈ K ⊔ K₀ := by
    suffices hfix : V₀.evalAt (g : ↥(modularFunctionFieldBar (N * q)))
        ∈ IntermediateField.fixedField (K ⊔ K₀).fixingSubgroup by
      rwa [InfiniteGalois.fixedField_fixingSubgroup (K ⊔ K₀)] at hfix
    rw [IntermediateField.mem_fixedField_iff]
    intro σ hσ
    rw [IntermediateField.mem_fixingSubgroup_iff] at hσ
    have hσ₀ : σ ∈ K₀.fixingSubgroup := by
      rw [IntermediateField.mem_fixingSubgroup_iff]
      exact fun z hz => hσ z ((le_sup_right : K₀ ≤ K ⊔ K₀) hz)
    have h := (ModularCurve.arithmeticGalois_smul_eq_self_and_evalAt_smul_of_coe_mem_fieldOver (N * q) (K ⊔ K₀) σ hσ
      (g : ↥(modularFunctionFieldBar (N * q))) g.2.2).2 V₀ hrat
    rw [hfixV σ hσ₀] at h
    exact h.symm
  refine ⟨⟨V₀.evalAt (g : ↥(modularFunctionFieldBar (N * q))), Subring.mem_inf.mpr ⟨hcA, hcK⟩⟩,
    nw_not_isUnit_of_evalAt_eq_zero R hV₀ ?_⟩

  have hm : (g : ↥(modularFunctionFieldBar (N * q))) ∈ V₀.toValuationSubring :=
    R.mem_toValuationSubring_of_mem_nodeIntegers g.2.1 hV₀
  rw [AddSubgroupClass.coe_sub, coe_nodeConst, nw_evalAt_sub_of_mem V₀ hrat hm (V₀.algebraMap_mem' _),
    V₀.evalAt_algebraMap_eq, sub_self]

private theorem nw_hres [IsAlgClosed k] [DecidableEq k] (hqN : ¬ q ∣ N) (hO : R.OrderLawFixed)
    (hw : w ∈ ssPlaces q N k) (K : IntermediateField ℚ (AlgebraicClosure ℚ)) (hK : FiniteDimensional ℚ K) :
    ∃ (K' : IntermediateField ℚ (AlgebraicClosure ℚ)) (_ : FiniteDimensional ℚ K'), K ≤ K' ∧
      ∀ g : ↥(R.nodeIntegersOver K' w),
        ∃ o : ↥(NodeLocalized.coeffSubring A K'), ¬ IsUnit (g - R.nodeConst K' w o) := by
  obtain ⟨V₀, hV₀⟩ := ModularCurve.PlaceSpecialization.reduceFst_surjective P w
  exact nw_hres_of_reduceFst_eq R hqN hO hw hV₀ K hK

end

end ModularCurve

namespace ModularCurve
p2m_export "ModularCurve" "PlaceSpecialization.ProlongationTuple modularFunctionFieldBar ModularPolynomialData jqModC jqNModC modularFunctionFieldC jqModC_mem jqNModC_mem PlaceSpecialization HeckeAlphaBarIntegral HeckeBetaBarIntegral frobOnPlacesGeomLevel KroneckerCongruence ssPlaces IsAffineGeomPlace arithFrobC IsAtkinLehnerAutFull atkinLehnerInvolutionFull isAtkinLehnerAutFull_atkinLehnerInvolutionFull NodeLocalized.coeffSubring NodeLocalized.redRestrict NodeLocalized.fieldOver CharPModel.FibreModel PlaceSpecialization.exists_ord_sub_pow_sq_eq_one_of_mem_ssPlaces exists_isAtkinLehnerAutFull_of_prime_of_not_dvd functionFieldGeneration NodeLocalized.exists_forall_redRestrict_eq_zero_iff_and_natCast_eq_pow_mul PlaceSpecialization.frobOnPlacesGeomLevel_frobOnPlacesGeomLevel_eq_self_of_mem_ssPlaces hasPrincipalDivisors_modularFunctionFieldBar_unconditional arithFrobC_smul_eq_frobOnPlacesGeomLevel PlaceSpecialization.ProlongationTuple.valueIntegralityLaw_of_orderLawFixed arithmeticGalois_smul_eq_self_and_evalAt_smul_of_coe_mem_fieldOver isRational_place_modularFunctionFieldBar PlaceSpecialization.reduceFst_surjective"
p2m_open "ModularCurve"

section

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
  {k : Type*} [Field k] [CharP k q] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
  {P : PlaceSpecialization A q N data hKr k red hα hβ}

private theorem inv_mem_of_notMem_maximalIdeal {F : Type*} [Field F] (O : ValuationSubring F) {x : F} (h : x ∈ O)
    (hx : (⟨x, h⟩ : O) ∉ IsLocalRing.maximalIdeal O) : x⁻¹ ∈ O := by
  have hunit : IsUnit (⟨x, h⟩ : O) := IsLocalRing.notMem_maximalIdeal.mp hx
  have hv : O.valuation x = 1 := (O.valuation_eq_one_iff _).mp hunit
  exact ValuationSubring.mem_of_valuation_le_one _ _ (by rw [map_inv₀, hv, inv_one])

private theorem eq_zero_of_mapDomain_eq_zero {α β : Type*} (g : α → β) (D : α →₀ ℤ) (b : β)
    (hnn : ∀ a, g a = b → 0 ≤ D a) (h0 : Finsupp.mapDomain g D b = 0) (a : α) (ha : g a = b) : D a = 0 := by
  classical
  have hexpand : Finsupp.mapDomain g D b = ∑ c ∈ D.support, (if g c = b then D c else 0) := by
    rw [Finsupp.mapDomain, Finsupp.sum_apply, Finsupp.sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Finsupp.single_apply]
  have hterm : ∀ c ∈ D.support, 0 ≤ (if g c = b then D c else 0) := by
    intro c _
    split_ifs with hc
    · exact hnn c hc
    · exact le_rfl
  by_cases haD : a ∈ D.support
  · have hle : (if g a = b then D a else 0) ≤ ∑ c ∈ D.support, (if g c = b then D c else 0) :=
      Finset.single_le_sum hterm haD
    rw [← hexpand, h0, if_pos ha] at hle
    exact le_antisymm hle (hnn a ha)
  · exact Finsupp.notMem_support_iff.mp haD

set_option synthInstance.maxHeartbeats 1600000 in

private theorem residue₁_ne_zero_of_nodeResidue₁_ne_zero (R : ProlongationTuple P) (w : Place k (modularFunctionFieldC k N))
    {g : ↥(modularFunctionFieldBar (N * q))} (hg : g ∈ R.nodeIntegers w) (h : R.nodeResidue₁ w ⟨g, hg⟩ ≠ 0)
    (h₁ : g ∈ R.R₁.integers) : R.R₁.residue ⟨g, h₁⟩ ≠ 0 := by
  intro h0
  apply h
  rw [nodeResidue₁_apply]
  simp only [ProlongationTuple.residue₁, RingHom.comp_apply]
  rw [h0, map_zero]

set_option synthInstance.maxHeartbeats 1600000 in

private theorem residue₂_ne_zero_of_nodeResidue₂_ne_zero (R : ProlongationTuple P) (w : Place k (modularFunctionFieldC k N))
    {g : ↥(modularFunctionFieldBar (N * q))} (hg : g ∈ R.nodeIntegers w) (h : R.nodeResidue₂ w ⟨g, hg⟩ ≠ 0)
    (h₂ : g ∈ R.R₂.integers) : R.R₂.residue ⟨g, h₂⟩ ≠ 0 := by
  intro h0
  apply h
  rw [nodeResidue₂_apply]
  simp only [ProlongationTuple.residue₂, RingHom.comp_apply]
  rw [h0, map_zero]

set_option synthInstance.maxHeartbeats 1600000 in
private theorem branchTwo_unit_of_bridge [IsAlgClosed k] (R : ProlongationTuple P) (w : Place k (modularFunctionFieldC k N))
    (hbridge :
      (∀ V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)), P.reduceFst V = w →
        ∀ (g : ↥(R.nodeIntegers w)) (c : AlgebraicClosure ℚ),
        V.HasValue (g : ↥(modularFunctionFieldBar (N * q))) c →
        ∃ hcA : c ∈ A,
        w.HasValue (R.nodeResidue₁ w g : ↥(modularFunctionFieldC k N)) (red ⟨c, hcA⟩)) ∧
      (∀ V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)), P.reduceFst V = w →
        ∀ (g : ↥(R.nodeIntegers w)) (c : AlgebraicClosure ℚ),
        V.HasValue (g : ↥(modularFunctionFieldBar (N * q))) c →
        ∃ hcA : c ∈ A,
        (arithFrobC q k N • w).HasValue (R.nodeResidue₂ w g : ↥(modularFunctionFieldC k N)) (red ⟨c, hcA⟩)))
    (hrat : ∀ V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)), V.IsRational)
    (V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) (hV : P.reduceFst V = w)
    (g : ↥(R.nodeIntegers w)) (hmem : (R.nodeResidue₁ w g : ↥(modularFunctionFieldC k N)) ∈ w.toValuationSubring)
    (hunit : (⟨R.nodeResidue₁ w g, hmem⟩ : ↥w.toValuationSubring) ∉ IsLocalRing.maximalIdeal ↥w.toValuationSubring) :
    R.nodeResidue₂ w g ≠ 0 ∧
      (frobOnPlacesGeomLevel k N data hKr w).ord (R.nodeResidue₂ w g : ↥(modularFunctionFieldC k N)) = 0 := by
  obtain ⟨c, hc, -⟩ := V.exists_hasValue_of_surjective (hrat V) (g.2.2.2 V hV)
  obtain ⟨hcA, hval₁⟩ := hbridge.1 V hV g c hc
  have hred : red ⟨c, hcA⟩ ≠ 0 := by
    intro h0
    apply hunit
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    exact hval₁.residue_eq.trans (by rw [h0, map_zero]; rfl)
  obtain ⟨hcA', hval₂⟩ := hbridge.2 V hV g c hc
  rw [← arithFrobC_smul_eq_frobOnPlacesGeomLevel q k N data hKr w]
  exact ⟨hval₂.ne_zero hred, hval₂.ord_eq_zero hred⟩

set_option synthInstance.maxHeartbeats 1600000 in
private theorem inv_mem_nodeIntegersOver_of_units (R : ProlongationTuple P) (hO : R.OrderLawFixed)
    (w : Place k (modularFunctionFieldC k N)) (hwa : IsAffineGeomPlace k N w)
    (hfix : frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr w) = w)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) (g : ↥(R.nodeIntegersOver K w))
    (hne₁ : R.nodeResidue₁ w ⟨g, g.2.1⟩ ≠ 0) (hord₁ : w.ord (R.nodeResidue₁ w ⟨g, g.2.1⟩) = 0)
    (hne₂ : R.nodeResidue₂ w ⟨g, g.2.1⟩ ≠ 0)
    (hord₂ : (frobOnPlacesGeomLevel k N data hKr w).ord (R.nodeResidue₂ w ⟨g, g.2.1⟩) = 0) :
    ((g : ↥(modularFunctionFieldBar (N * q)))⁻¹) ∈ R.nodeIntegersOver K w := by
  obtain ⟨f, hB⟩ := g
  have h₁ : f ∈ R.R₁.integers := hB.1.1
  have h₂ : f ∈ R.R₂.integers := hB.1.2.1
  have hr₁ : R.R₁.residue ⟨f, h₁⟩ ≠ 0 := residue₁_ne_zero_of_nodeResidue₁_ne_zero R w hB.1 hne₁ h₁
  have hr₂ : R.R₂.residue ⟨f, h₂⟩ ≠ 0 := residue₂_ne_zero_of_nodeResidue₂_ne_zero R w hB.1 hne₂ h₂
  have hf0 : f ≠ 0 := by
    intro hf0
    apply hr₁
    rw [show (⟨f, h₁⟩ : R.R₁.integers) = 0 from Subtype.ext hf0, map_zero]
  have hm₁ : (⟨f, h₁⟩ : R.R₁.integers) ∉ IsLocalRing.maximalIdeal R.R₁.integers := by
    rw [← R.R₁.ker_residue]; exact hr₁
  have hm₂ : (⟨f, h₂⟩ : R.R₂.integers) ∉ IsLocalRing.maximalIdeal R.R₂.integers := by
    rw [← R.R₂.ker_residue]; exact hr₂
  refine ⟨⟨inv_mem_of_notMem_maximalIdeal _ h₁ hm₁, inv_mem_of_notMem_maximalIdeal _ h₂ hm₂, fun V hVw => ?_⟩, ?_⟩
  · obtain ⟨D, hD, -⟩ := (hasPrincipalDivisors_modularFunctionFieldBar_unconditional (N * q)).exists_divisor f hf0
    have hsum := hO f h₁ h₂ hr₁ hr₂ D hD w hfix hwa
    rw [nodeResidue₁_apply] at hord₁
    rw [nodeResidue₂_apply] at hord₂
    have hres₁ : w.ord (R.residue₁ ⟨f, h₁⟩) = 0 := hord₁
    have hres₂ : (frobOnPlacesGeomLevel k N data hKr w).ord (R.residue₂ ⟨f, h₂⟩) = 0 := hord₂
    rw [hres₁, hres₂, add_zero] at hsum
    have hDV : D V = 0 :=
      eq_zero_of_mapDomain_eq_zero P.reduceFst D w
        (fun W hW => by rw [hD W]; exact R.ord_nonneg_of_mem_nodeIntegers hB.1 hW) hsum V hVw
    rw [hD V] at hDV
    exact Place.mem_of_ord_nonneg V (inv_ne_zero hf0) (by rw [Place.ord_inv, hDV]; exact le_rfl)
  · have hcoe : ((f⁻¹ : ↥(modularFunctionFieldBar (N * q))) : LaurentSeries (AlgebraicClosure ℚ))
        = ((f : LaurentSeries (AlgebraicClosure ℚ)))⁻¹ := by simp
    show ((f⁻¹ : ↥(modularFunctionFieldBar (N * q))) : LaurentSeries (AlgebraicClosure ℚ)) ∈ NodeLocalized.fieldOver (N * q) K
    rw [hcoe]
    exact inv_mem hB.2

set_option synthInstance.maxHeartbeats 1600000 in
private theorem isUnit_of_notMem_maximalIdeal_branchOne [IsAlgClosed k] (R : ProlongationTuple P) (hO : R.OrderLawFixed)
    (w : Place k (modularFunctionFieldC k N)) (hwa : IsAffineGeomPlace k N w)
    (hfix : frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr w) = w)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ))
    (hreg₁ : ∀ g : ↥(R.nodeIntegers w), (R.nodeResidue₁ w g : ↥(modularFunctionFieldC k N)) ∈ w.toValuationSubring)
    (hbridge :
      (∀ V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)), P.reduceFst V = w →
        ∀ (g : ↥(R.nodeIntegers w)) (c : AlgebraicClosure ℚ),
        V.HasValue (g : ↥(modularFunctionFieldBar (N * q))) c →
        ∃ hcA : c ∈ A,
        w.HasValue (R.nodeResidue₁ w g : ↥(modularFunctionFieldC k N)) (red ⟨c, hcA⟩)) ∧
      (∀ V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)), P.reduceFst V = w →
        ∀ (g : ↥(R.nodeIntegers w)) (c : AlgebraicClosure ℚ),
        V.HasValue (g : ↥(modularFunctionFieldBar (N * q))) c →
        ∃ hcA : c ∈ A,
        (arithFrobC q k N • w).HasValue (R.nodeResidue₂ w g : ↥(modularFunctionFieldC k N)) (red ⟨c, hcA⟩)))
    (hrat : ∀ V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)), V.IsRational)
    (g : ↥(R.nodeIntegersOver K w))
    (hunit : (⟨R.nodeResidue₁ w ⟨g, g.2.1⟩, hreg₁ _⟩ : ↥w.toValuationSubring) ∉
      IsLocalRing.maximalIdeal ↥w.toValuationSubring) :
    IsUnit g := by
  obtain ⟨V, hV⟩ := P.reduceFst_surjective w
  obtain ⟨u, hu⟩ := IsLocalRing.notMem_maximalIdeal.mp hunit
  have hne₁ : R.nodeResidue₁ w ⟨g, g.2.1⟩ ≠ 0 := by
    intro h0
    apply u.ne_zero
    apply Subtype.ext
    rw [hu]
    exact h0
  have hord₁ : w.ord (R.nodeResidue₁ w ⟨g, g.2.1⟩ : ↥(modularFunctionFieldC k N)) = 0 := by
    have h := w.ord_coe_unit u
    rw [hu] at h
    exact h
  obtain ⟨hne₂, hord₂⟩ := branchTwo_unit_of_bridge R w hbridge hrat V hV ⟨g, g.2.1⟩ (hreg₁ _) hunit
  have hinv := inv_mem_nodeIntegersOver_of_units R hO w hwa hfix K g hne₁ hord₁ hne₂ hord₂
  have hf0 : (g : ↥(modularFunctionFieldBar (N * q))) ≠ 0 := by
    intro h0
    apply hne₁
    have hz : (⟨g, g.2.1⟩ : ↥(R.nodeIntegers w)) = 0 := Subtype.ext h0
    rw [hz, map_zero]
  refine isUnit_iff_exists_inv.mpr ⟨⟨_, hinv⟩, ?_⟩
  apply Subtype.ext
  rw [Subring.coe_mul, Subring.coe_one]
  exact mul_inv_cancel₀ hf0

set_option synthInstance.maxHeartbeats 1600000 in
private theorem nodeResidue₁_one_sub (R : ProlongationTuple P) (w : Place k (modularFunctionFieldC k N))
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) (g : ↥(R.nodeIntegersOver K w)) :
    R.nodeResidue₁ w ⟨(1 - g : ↥(R.nodeIntegersOver K w)), (1 - g).2.1⟩ = 1 - R.nodeResidue₁ w ⟨g, g.2.1⟩ := by
  have e : (⟨(1 - g : ↥(R.nodeIntegersOver K w)), (1 - g).2.1⟩ : ↥(R.nodeIntegers w)) = 1 - ⟨g, g.2.1⟩ :=
    Subtype.ext rfl
  rw [e, map_sub, map_one]

set_option synthInstance.maxHeartbeats 1600000 in
private theorem isLocalRing_nodeIntegersOver_of_bridge [IsAlgClosed k] (R : ProlongationTuple P) (hO : R.OrderLawFixed)
    (w : Place k (modularFunctionFieldC k N)) (hwa : IsAffineGeomPlace k N w)
    (hfix : frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr w) = w)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ))
    (hreg₁ : ∀ g : ↥(R.nodeIntegers w), (R.nodeResidue₁ w g : ↥(modularFunctionFieldC k N)) ∈ w.toValuationSubring)
    (hbridge :
      (∀ V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)), P.reduceFst V = w →
        ∀ (g : ↥(R.nodeIntegers w)) (c : AlgebraicClosure ℚ),
        V.HasValue (g : ↥(modularFunctionFieldBar (N * q))) c →
        ∃ hcA : c ∈ A,
        w.HasValue (R.nodeResidue₁ w g : ↥(modularFunctionFieldC k N)) (red ⟨c, hcA⟩)) ∧
      (∀ V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)), P.reduceFst V = w →
        ∀ (g : ↥(R.nodeIntegers w)) (c : AlgebraicClosure ℚ),
        V.HasValue (g : ↥(modularFunctionFieldBar (N * q))) c →
        ∃ hcA : c ∈ A,
        (arithFrobC q k N • w).HasValue (R.nodeResidue₂ w g : ↥(modularFunctionFieldC k N)) (red ⟨c, hcA⟩)))
    (hrat : ∀ V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)), V.IsRational) :
    IsLocalRing ↥(R.nodeIntegersOver K w) := by
  refine IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun g => ?_
  by_cases h : (⟨R.nodeResidue₁ w ⟨g, g.2.1⟩, hreg₁ _⟩ : ↥w.toValuationSubring) ∈
      IsLocalRing.maximalIdeal ↥w.toValuationSubring
  · right
    refine isUnit_of_notMem_maximalIdeal_branchOne R hO w hwa hfix K hreg₁ hbridge hrat (1 - g) ?_
    intro h1
    have e : (⟨R.nodeResidue₁ w ⟨(1 - g : ↥(R.nodeIntegersOver K w)), (1 - g).2.1⟩, hreg₁ _⟩ : ↥w.toValuationSubring)
        = 1 - ⟨R.nodeResidue₁ w ⟨g, g.2.1⟩, hreg₁ _⟩ :=
      Subtype.ext (nodeResidue₁_one_sub R w K g)
    rw [e] at h1
    have h1' := (IsLocalRing.maximalIdeal ↥w.toValuationSubring).add_mem h1 h
    rw [sub_add_cancel] at h1'
    exact (IsLocalRing.maximalIdeal.isMaximal ↥w.toValuationSubring).ne_top ((Ideal.eq_top_iff_one _).mpr h1')
  · left
    exact isUnit_of_notMem_maximalIdeal_branchOne R hO w hwa hfix K hreg₁ hbridge hrat g h

set_option synthInstance.maxHeartbeats 1600000 in
private theorem isUnit_of_nodeResidue₁_unit [IsAlgClosed k] (R : ProlongationTuple P) (hO : R.OrderLawFixed)
    (w : Place k (modularFunctionFieldC k N)) (hwa : IsAffineGeomPlace k N w)
    (hfix : frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr w) = w)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ))
    (hreg₁ : ∀ g : ↥(R.nodeIntegers w), (R.nodeResidue₁ w g : ↥(modularFunctionFieldC k N)) ∈ w.toValuationSubring)
    (hbridge :
      (∀ V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)), P.reduceFst V = w →
        ∀ (g : ↥(R.nodeIntegers w)) (c : AlgebraicClosure ℚ),
        V.HasValue (g : ↥(modularFunctionFieldBar (N * q))) c →
        ∃ hcA : c ∈ A,
        w.HasValue (R.nodeResidue₁ w g : ↥(modularFunctionFieldC k N)) (red ⟨c, hcA⟩)) ∧
      (∀ V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)), P.reduceFst V = w →
        ∀ (g : ↥(R.nodeIntegers w)) (c : AlgebraicClosure ℚ),
        V.HasValue (g : ↥(modularFunctionFieldBar (N * q))) c →
        ∃ hcA : c ∈ A,
        (arithFrobC q k N • w).HasValue (R.nodeResidue₂ w g : ↥(modularFunctionFieldC k N)) (red ⟨c, hcA⟩)))
    (hrat : ∀ V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)), V.IsRational)
    (g : ↥(R.nodeIntegersOver K w))
    (hne : R.nodeResidue₁ w ⟨g, g.2.1⟩ ≠ 0) (hord : w.ord (R.nodeResidue₁ w ⟨g, g.2.1⟩) = 0) : IsUnit g := by
  refine isUnit_of_notMem_maximalIdeal_branchOne R hO w hwa hfix K hreg₁ hbridge hrat g ?_
  intro hmem
  have hinv : (R.nodeResidue₁ w ⟨g, g.2.1⟩ : ↥(modularFunctionFieldC k N))⁻¹ ∈ w.toValuationSubring :=
    Place.mem_of_ord_nonneg w (inv_ne_zero hne) (by rw [Place.ord_inv, hord]; exact le_rfl)
  have hunit : IsUnit (⟨R.nodeResidue₁ w ⟨g, g.2.1⟩, hreg₁ _⟩ : ↥w.toValuationSubring) :=
    isUnit_iff_exists_inv.mpr ⟨⟨_, hinv⟩, Subtype.ext (by exact mul_inv_cancel₀ hne)⟩
  exact IsLocalRing.notMem_maximalIdeal.mpr hunit hmem

set_option synthInstance.maxHeartbeats 1600000 in
private theorem isUnit_of_nodeResidue₂_unit [IsAlgClosed k] (R : ProlongationTuple P) (hO : R.OrderLawFixed)
    (w : Place k (modularFunctionFieldC k N)) (hwa : IsAffineGeomPlace k N w)
    (hfix : frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr w) = w)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ))
    (hreg₁ : ∀ g : ↥(R.nodeIntegers w), (R.nodeResidue₁ w g : ↥(modularFunctionFieldC k N)) ∈ w.toValuationSubring)
    (hbridge :
      (∀ V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)), P.reduceFst V = w →
        ∀ (g : ↥(R.nodeIntegers w)) (c : AlgebraicClosure ℚ),
        V.HasValue (g : ↥(modularFunctionFieldBar (N * q))) c →
        ∃ hcA : c ∈ A,
        w.HasValue (R.nodeResidue₁ w g : ↥(modularFunctionFieldC k N)) (red ⟨c, hcA⟩)) ∧
      (∀ V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)), P.reduceFst V = w →
        ∀ (g : ↥(R.nodeIntegers w)) (c : AlgebraicClosure ℚ),
        V.HasValue (g : ↥(modularFunctionFieldBar (N * q))) c →
        ∃ hcA : c ∈ A,
        (arithFrobC q k N • w).HasValue (R.nodeResidue₂ w g : ↥(modularFunctionFieldC k N)) (red ⟨c, hcA⟩)))
    (hrat : ∀ V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)), V.IsRational)
    (g : ↥(R.nodeIntegersOver K w))
    (hne : R.nodeResidue₂ w ⟨g, g.2.1⟩ ≠ 0)
    (hord : (arithFrobC q k N • w).ord (R.nodeResidue₂ w ⟨g, g.2.1⟩) = 0) : IsUnit g := by
  refine isUnit_of_notMem_maximalIdeal_branchOne R hO w hwa hfix K hreg₁ hbridge hrat g ?_
  intro hmem
  obtain ⟨V, hV⟩ := P.reduceFst_surjective w
  obtain ⟨c, hc, -⟩ := V.exists_hasValue_of_surjective (hrat V) (g.2.1.2.2 V hV)
  obtain ⟨hcA, hval₁⟩ := hbridge.1 V hV ⟨g, g.2.1⟩ c hc
  obtain ⟨hcA', hval₂⟩ := hbridge.2 V hV ⟨g, g.2.1⟩ c hc

  have h1 : algebraMap k w.ResidueField (red ⟨c, hcA⟩) = 0 := by
    rw [← hval₁.residue_eq]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hmem
  have hred0 : red ⟨c, hcA⟩ = 0 := (algebraMap k w.ResidueField).injective (by rw [h1, map_zero])

  have hinv : (R.nodeResidue₂ w ⟨g, g.2.1⟩ : ↥(modularFunctionFieldC k N))⁻¹ ∈
      (arithFrobC q k N • w).toValuationSubring :=
    Place.mem_of_ord_nonneg _ (inv_ne_zero hne) (by rw [Place.ord_inv, hord]; exact le_rfl)
  have hu₂ : IsUnit (⟨R.nodeResidue₂ w ⟨g, g.2.1⟩, hval₂.mem⟩ : ↥(arithFrobC q k N • w).toValuationSubring) :=
    isUnit_iff_exists_inv.mpr ⟨⟨_, hinv⟩, Subtype.ext (by exact mul_inv_cancel₀ hne)⟩
  apply IsLocalRing.notMem_maximalIdeal.mpr hu₂
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  exact hval₂.residue_eq.trans (by rw [show red ⟨c, hcA'⟩ = 0 from hred0]; exact map_zero _)

end

end ModularCurve

namespace ModularCurve
p2m_export "ModularCurve" "PlaceSpecialization.ProlongationTuple modularFunctionFieldBar ModularPolynomialData jqModC jqNModC modularFunctionFieldC jqModC_mem jqNModC_mem PlaceSpecialization HeckeAlphaBarIntegral HeckeBetaBarIntegral frobOnPlacesGeomLevel KroneckerCongruence ssPlaces IsAffineGeomPlace arithFrobC IsAtkinLehnerAutFull atkinLehnerInvolutionFull isAtkinLehnerAutFull_atkinLehnerInvolutionFull NodeLocalized.coeffSubring NodeLocalized.redRestrict NodeLocalized.fieldOver CharPModel.FibreModel PlaceSpecialization.exists_ord_sub_pow_sq_eq_one_of_mem_ssPlaces exists_isAtkinLehnerAutFull_of_prime_of_not_dvd functionFieldGeneration NodeLocalized.exists_forall_redRestrict_eq_zero_iff_and_natCast_eq_pow_mul PlaceSpecialization.frobOnPlacesGeomLevel_frobOnPlacesGeomLevel_eq_self_of_mem_ssPlaces hasPrincipalDivisors_modularFunctionFieldBar_unconditional arithFrobC_smul_eq_frobOnPlacesGeomLevel PlaceSpecialization.ProlongationTuple.valueIntegralityLaw_of_orderLawFixed arithmeticGalois_smul_eq_self_and_evalAt_smul_of_coe_mem_fieldOver isRational_place_modularFunctionFieldBar PlaceSpecialization.reduceFst_surjective"
p2m_open "ModularCurve"

section

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
  {k : Type*} [Field k] [CharP k q] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
  {P : PlaceSpecialization A q N data hKr k red hα hβ} (R : ProlongationTuple P)
  {w : Place k (modularFunctionFieldC k N)} {K : IntermediateField ℚ (AlgebraicClosure ℚ)}

private theorem nodeResidue₁_sub_mul' (g y h : ↥(R.nodeIntegersOver K w)) :
    R.nodeResidue₁ w ⟨g - y * h, (g - y * h).2.1⟩ =
      R.nodeResidue₁ w ⟨g, g.2.1⟩ - R.nodeResidue₁ w ⟨y, y.2.1⟩ * R.nodeResidue₁ w ⟨h, h.2.1⟩ := by
  rw [← map_mul, ← map_sub]
  congr 1

private theorem nodeResidue₂_sub_mul' (g x h : ↥(R.nodeIntegersOver K w)) :
    R.nodeResidue₂ w ⟨g - x * h, (g - x * h).2.1⟩ =
      R.nodeResidue₂ w ⟨g, g.2.1⟩ - R.nodeResidue₂ w ⟨x, x.2.1⟩ * R.nodeResidue₂ w ⟨h, h.2.1⟩ := by
  rw [← map_mul, ← map_sub]
  congr 1

private theorem branch_lifts_of_saturated [IsAlgClosed k] [IsLocalRing ↥(R.nodeIntegersOver K w)]
    (hreg : ∀ g : ↥(R.nodeIntegersOver K w),
      (R.nodeResidue₁ w ⟨g, g.2.1⟩ = 0 ∨ 0 ≤ w.ord (R.nodeResidue₁ w ⟨g, g.2.1⟩)) ∧
      (R.nodeResidue₂ w ⟨g, g.2.1⟩ = 0 ∨ 0 ≤ (arithFrobC q k N • w).ord (R.nodeResidue₂ w ⟨g, g.2.1⟩)))
    (hunit₁ : ∀ g : ↥(R.nodeIntegersOver K w), R.nodeResidue₁ w ⟨g, g.2.1⟩ ≠ 0 →
      w.ord (R.nodeResidue₁ w ⟨g, g.2.1⟩) = 0 → IsUnit g)
    (hunit₂ : ∀ g : ↥(R.nodeIntegersOver K w), R.nodeResidue₂ w ⟨g, g.2.1⟩ ≠ 0 →
      (arithFrobC q k N • w).ord (R.nodeResidue₂ w ⟨g, g.2.1⟩) = 0 → IsUnit g)
    (hsat₁ : ∀ g g' : ↥(R.nodeIntegersOver K w),
      0 < w.ord (R.nodeResidue₁ w ⟨g, g.2.1⟩) → w.ord (R.nodeResidue₁ w ⟨g', g'.2.1⟩) = 1 →
      ∃ b : ↥(R.nodeIntegersOver K w),
      R.nodeResidue₁ w ⟨g, g.2.1⟩ = R.nodeResidue₁ w ⟨g', g'.2.1⟩ * R.nodeResidue₁ w ⟨b, b.2.1⟩)
    (hsat₂ : ∀ g g' : ↥(R.nodeIntegersOver K w),
      0 < (arithFrobC q k N • w).ord (R.nodeResidue₂ w ⟨g, g.2.1⟩) →
      (arithFrobC q k N • w).ord (R.nodeResidue₂ w ⟨g', g'.2.1⟩) = 1 →
      ∃ b : ↥(R.nodeIntegersOver K w),
      R.nodeResidue₂ w ⟨g, g.2.1⟩ = R.nodeResidue₂ w ⟨g', g'.2.1⟩ * R.nodeResidue₂ w ⟨b, b.2.1⟩)
    (c : R.NodeCoordinates K w) :
    (∀ g ∈ maximalIdeal ↥(R.nodeIntegersOver K w), ∃ h : ↥(R.nodeIntegersOver K w),
      R.nodeResidue₁ w ⟨g - c.y * h, (g - c.y * h).2.1⟩ = 0) ∧
    (∀ g ∈ maximalIdeal ↥(R.nodeIntegersOver K w), ∃ h : ↥(R.nodeIntegersOver K w),
      R.nodeResidue₂ w ⟨g - c.x * h, (g - c.x * h).2.1⟩ = 0) := by
  refine ⟨fun g hg => ?_, fun g hg => ?_⟩
  · have hng : ¬ IsUnit g := mem_nonunits_iff.mp ((mem_maximalIdeal g).mp hg)
    by_cases h0 : R.nodeResidue₁ w ⟨g, g.2.1⟩ = 0
    · exact ⟨c.x, by rw [nodeResidue₁_sub_mul', h0, c.x_fst, mul_zero, sub_zero]⟩
    · have hord : 0 < w.ord (R.nodeResidue₁ w ⟨g, g.2.1⟩) := by
        rcases (hreg g).1 with h | h
        · exact absurd h h0
        · exact lt_of_le_of_ne h (fun heq => hng (hunit₁ g h0 heq.symm))
      obtain ⟨b, hb⟩ := hsat₁ g c.y hord c.y_fst
      exact ⟨b, by rw [nodeResidue₁_sub_mul', hb, sub_self]⟩
  · have hng : ¬ IsUnit g := mem_nonunits_iff.mp ((mem_maximalIdeal g).mp hg)
    by_cases h0 : R.nodeResidue₂ w ⟨g, g.2.1⟩ = 0
    · exact ⟨c.y, by rw [nodeResidue₂_sub_mul', h0, c.y_snd, mul_zero, sub_zero]⟩
    · have hord : 0 < (arithFrobC q k N • w).ord (R.nodeResidue₂ w ⟨g, g.2.1⟩) := by
        rcases (hreg g).2 with h | h
        · exact absurd h h0
        · exact lt_of_le_of_ne h (fun heq => hng (hunit₂ g h0 heq.symm))
      obtain ⟨b, hb⟩ := hsat₂ g c.x hord c.x_snd
      exact ⟨b, by rw [nodeResidue₂_sub_mul', hb, sub_self]⟩

end

end ModularCurve

private theorem solution_aux
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    [IsAlgClosed k] [DecidableEq k] (hqN : ¬ q ∣ N) (fm : CharPModel.FibreModel N A q k red) (hred : Function.Surjective red)
    (dataAll : ∀ (d : ℕ) [NeZero d], d ∣ N → ModularPolynomialData d)
    (hsep : (((dataAll N (dvd_refl N)).Φ.map
        (Polynomial.mapRingHom (Int.castRingHom k))).map
      (algebraMap (Polynomial k) (RatFunc k))).Separable)
    (P : PlaceSpecialization A q N data hKr k red hα hβ) (hP : P.sp = fm.spPlace hred dataAll hsep)
    (R : ProlongationTuple P) (hO : R.OrderLawFixed)
    (w : Place k (modularFunctionFieldC k N)) (hw : w ∈ ssPlaces q N k)
    (hπ : w.ord ((⟨jqModC k, jqModC_mem k N⟩ : ↥(modularFunctionFieldC k N))
        - (⟨jqModC k, jqModC_mem k N⟩ : ↥(modularFunctionFieldC k N)) ^ (q ^ 2)) = 1 ∨
      w.ord ((⟨jqNModC k N, jqNModC_mem k N⟩ : ↥(modularFunctionFieldC k N))
        - (⟨jqNModC k N, jqNModC_mem k N⟩ : ↥(modularFunctionFieldC k N)) ^ (q ^ 2)) = 1)
    (hSATM : ∀ (K : IntermediateField ℚ (AlgebraicClosure ℚ)) (_ : FiniteDimensional ℚ K),
      (∀ g : ↥(R.nodeIntegersOver K w), ∃ o : ↥(NodeLocalized.coeffSubring A K), ¬ IsUnit (g - R.nodeConst K w o)) →
      (∀ g g' : ↥(R.nodeIntegersOver K w),
        0 < w.ord (R.nodeResidue₁ w ⟨g, g.2.1⟩) → w.ord (R.nodeResidue₁ w ⟨g', g'.2.1⟩) = 1 →
        ∃ b : ↥(R.nodeIntegersOver K w),
          R.nodeResidue₁ w ⟨g, g.2.1⟩ = R.nodeResidue₁ w ⟨g', g'.2.1⟩ * R.nodeResidue₁ w ⟨b, b.2.1⟩) ∧
      (∀ g g' : ↥(R.nodeIntegersOver K w),
        0 < (arithFrobC q k N • w).ord (R.nodeResidue₂ w ⟨g, g.2.1⟩) →
        (arithFrobC q k N • w).ord (R.nodeResidue₂ w ⟨g', g'.2.1⟩) = 1 →
        ∃ b : ↥(R.nodeIntegersOver K w),
          R.nodeResidue₂ w ⟨g, g.2.1⟩ = R.nodeResidue₂ w ⟨g', g'.2.1⟩ * R.nodeResidue₂ w ⟨b, b.2.1⟩) ∧
      (∀ ϖ : ↥(NodeLocalized.coeffSubring A K),
        (∀ d : ↥(NodeLocalized.coeffSubring A K), NodeLocalized.redRestrict red K d = 0 ↔ ∃ d', d = ϖ * d') →
        ∀ g : ↥(R.nodeIntegersOver K w), R.nodeResidue₁ w ⟨g, g.2.1⟩ = 0 → R.nodeResidue₂ w ⟨g, g.2.1⟩ = 0 →
          ∃ b : ↥(R.nodeIntegersOver K w), g = R.nodeConst K w ϖ * b)) :
    ∀ K : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ K →
      ∃ (K' : IntermediateField ℚ (AlgebraicClosure ℚ)) (_ : FiniteDimensional ℚ K'), K ≤ K' ∧
        ∃ (c : R.NodeCoordinates K' w) (ϖ : ↥(NodeLocalized.coeffSubring A K'))
          (_ : IsLocalRing ↥(R.nodeIntegersOver K' w)) (_ : IsNoetherianRing ↥(R.nodeIntegersOver K' w)),
          (∀ d : ↥(NodeLocalized.coeffSubring A K'), NodeLocalized.redRestrict red K' d = 0 ↔ ∃ d', d = ϖ * d') ∧
          IsLocalRing.maximalIdeal ↥(R.nodeIntegersOver K' w) = Ideal.span {R.nodeConst K' w ϖ, c.x, c.y} ∧
          (∀ g : ↥(R.nodeIntegersOver K' w), ∃ o : ↥(NodeLocalized.coeffSubring A K'), ¬ IsUnit (g - R.nodeConst K' w o)) ∧
          ∀ g : ↥(R.nodeIntegersOver K' w),
            (R.nodeResidue₁ w ⟨g, g.2.1⟩ = 0 ∨ 0 ≤ w.ord (R.nodeResidue₁ w ⟨g, g.2.1⟩)) ∧
            (R.nodeResidue₂ w ⟨g, g.2.1⟩ = 0 ∨ 0 ≤ (arithFrobC q k N • w).ord (R.nodeResidue₂ w ⟨g, g.2.1⟩)) := by
  have _ := hπ
  intro K hK

  obtain ⟨K₀, hK₀, hKK₀, htail⟩ :=
    isLocalRing_and_isNoetherianRing_nodeIntegersOver_of_sp_eq_spPlace hqN fm hred dataAll hsep P hP R w hw K hK
  obtain ⟨K', hK', hK₀K', hres⟩ := ModularCurve.nw_hres R hqN hO hw K₀ hK₀
  haveI := hK'
  have hKK' : K ≤ K' := le_trans hKK₀ hK₀K'
  have hbridge := hasValue_nodeResidue_red_of_hasValue_of_sp_eq_spPlace hqN fm hred dataAll hsep P hP R hO w hw
  have hfix := ModularCurve.PlaceSpecialization.frobOnPlacesGeomLevel_frobOnPlacesGeomLevel_eq_self_of_mem_ssPlaces
    hqN P w hw
  have hreg₁ : ∀ g : ↥(R.nodeIntegers w),
      (R.nodeResidue₁ w g : ↥(modularFunctionFieldC k N)) ∈ w.toValuationSubring := fun g =>
    (ModularCurve.nw_nodeResidue₁_regular R hqN hO hw g).elim (fun h0 => by rw [h0]; exact zero_mem _)
      (fun h => by
        by_cases hz : R.nodeResidue₁ w g = 0
        · rw [hz]; exact zero_mem _
        · exact w.mem_of_ord_nonneg hz h)
  have hrat : ∀ V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)), V.IsRational :=
    fun V => ModularCurve.isRational_place_modularFunctionFieldBar (N * q) V
  haveI hloc : IsLocalRing ↥(R.nodeIntegersOver K' w) :=
    ModularCurve.isLocalRing_nodeIntegersOver_of_bridge R hO w hw.2.1 hfix K' hreg₁ hbridge hrat
  have hreg := ModularCurve.nw_hreg R hqN hO hw K'
  have hnoeth : IsNoetherianRing ↥(R.nodeIntegersOver K' w) := (htail K' hK' hK₀K').2
  obtain ⟨hsat₁, hsat₂, hL₃⟩ := hSATM K' hK' hres
  obtain ⟨c⟩ := ModularCurve.nonempty_nodeCoordinates_of_mem_ssPlaces R hqN hw K'
  obtain ⟨ϖ, hϖ⟩ := ModularCurve.exists_uniformizer_coeffSubring (q := q) hred K'
  obtain ⟨L₁, L₂⟩ := ModularCurve.branch_lifts_of_saturated R hreg
    (fun g => ModularCurve.isUnit_of_nodeResidue₁_unit R hO w hw.2.1 hfix K' hreg₁ hbridge hrat g)
    (fun g => ModularCurve.isUnit_of_nodeResidue₂_unit R hO w hw.2.1 hfix K' hreg₁ hbridge hrat g) hsat₁ hsat₂ c
  have L₃ := hL₃ ϖ hϖ
  have hmax := ModularCurve.maximalIdeal_eq_span_of_branch_lifts hred c
    (ModularCurve.redRestrict_eq_zero_of_forall_iff hϖ) L₁ L₂ L₃
  exact ⟨K', hK', hKK', c, ϖ, hloc, hnoeth, hϖ, hmax, hres, hreg⟩

theorem solution
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    [CharP (IsLocalRing.ResidueField ↥A) q]
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    [DecidableEq (IsLocalRing.ResidueField ↥A)] (hqN : ¬ q ∣ N)
    (fm : CharPModel.FibreModel N A q (IsLocalRing.ResidueField ↥A) (IsLocalRing.residue ↥A))
    (dataAll : ∀ (d : ℕ) [NeZero d], d ∣ N → ModularPolynomialData d)
    (hsep : (((dataAll N (dvd_refl N)).Φ.map
        (Polynomial.mapRingHom (Int.castRingHom (IsLocalRing.ResidueField ↥A)))).map
      (algebraMap (Polynomial (IsLocalRing.ResidueField ↥A)) (RatFunc (IsLocalRing.ResidueField ↥A)))).Separable)
    (P : PlaceSpecialization A q N data hKr (IsLocalRing.ResidueField ↥A) (IsLocalRing.residue ↥A) hα hβ)
    (hP : P.sp = fm.spPlace IsLocalRing.residue_surjective dataAll hsep)
    (R : ProlongationTuple P) (hO : R.OrderLawFixed)
    (w : Place (IsLocalRing.ResidueField ↥A) (modularFunctionFieldC (IsLocalRing.ResidueField ↥A) N))
    (hw : w ∈ ssPlaces q N (IsLocalRing.ResidueField ↥A))
    (hπ : w.ord ((⟨jqModC (IsLocalRing.ResidueField ↥A), jqModC_mem (IsLocalRing.ResidueField ↥A) N⟩ :
            ↥(modularFunctionFieldC (IsLocalRing.ResidueField ↥A) N))
        - (⟨jqModC (IsLocalRing.ResidueField ↥A), jqModC_mem (IsLocalRing.ResidueField ↥A) N⟩ :
            ↥(modularFunctionFieldC (IsLocalRing.ResidueField ↥A) N)) ^ (q ^ 2)) = 1 ∨
      w.ord ((⟨jqNModC (IsLocalRing.ResidueField ↥A) N, jqNModC_mem (IsLocalRing.ResidueField ↥A) N⟩ :
            ↥(modularFunctionFieldC (IsLocalRing.ResidueField ↥A) N))
        - (⟨jqNModC (IsLocalRing.ResidueField ↥A) N, jqNModC_mem (IsLocalRing.ResidueField ↥A) N⟩ :
            ↥(modularFunctionFieldC (IsLocalRing.ResidueField ↥A) N)) ^ (q ^ 2)) = 1) :
    ∀ K : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ K →
      ∃ (K' : IntermediateField ℚ (AlgebraicClosure ℚ)) (_ : FiniteDimensional ℚ K'), K ≤ K' ∧
        ∃ (c : R.NodeCoordinates K' w) (ϖ : ↥(NodeLocalized.coeffSubring A K'))
          (_ : IsLocalRing ↥(R.nodeIntegersOver K' w)) (_ : IsNoetherianRing ↥(R.nodeIntegersOver K' w)),
          (∀ d : ↥(NodeLocalized.coeffSubring A K'),
            NodeLocalized.redRestrict (IsLocalRing.residue ↥A) K' d = 0 ↔ ∃ d', d = ϖ * d') ∧
          IsLocalRing.maximalIdeal ↥(R.nodeIntegersOver K' w) = Ideal.span {R.nodeConst K' w ϖ, c.x, c.y} ∧
          (∀ g : ↥(R.nodeIntegersOver K' w), ∃ o : ↥(NodeLocalized.coeffSubring A K'), ¬ IsUnit (g - R.nodeConst K' w o)) ∧
          ∀ g : ↥(R.nodeIntegersOver K' w),
            (R.nodeResidue₁ w ⟨g, g.2.1⟩ = 0 ∨ 0 ≤ w.ord (R.nodeResidue₁ w ⟨g, g.2.1⟩)) ∧
            (R.nodeResidue₂ w ⟨g, g.2.1⟩ = 0 ∨
              0 ≤ (arithFrobC q (IsLocalRing.ResidueField ↥A) N • w).ord (R.nodeResidue₂ w ⟨g, g.2.1⟩)) := by
  intro K hK
  exact solution_aux hqN fm IsLocalRing.residue_surjective dataAll hsep P hP R hO w hw hπ
    (fun K' hK' hres => by
      haveI := hK'
      exact nodeResidue_saturated_of_sp_eq_spPlace_residueField hqN fm dataAll hsep P hP R hO w hw K' hres)
    K hK

end S_ModularCurve_PlaceSpecialization_ProlongationTuple_nodePack_residueField_of_ord_sub_pow_sq_eq_one_or
end P2MW
export P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_nodePack_residueField_of_ord_sub_pow_sq_eq_one_or (solution)
