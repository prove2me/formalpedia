-- Prove2me | solution 1 for ModularCurve.PlaceSpecialization.gluedSpecialization_twoLevel_degeneracyGlue_of_isModel_placeWidthChar_restrictAlong
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/a172d608-91f1-5d6d-84ac-a607a496b539

import Definitions.Def_ModularCurve_JZeroSemistableSpecialization
import Definitions.Def_ModularCurve_HeckeModule
import Definitions.Def_ValuationSubring_ReduceAt
import Definitions.Def_WeierstrassCurve_ReductionMap
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_ModularCurve_CoeffSemilinearAut
import Definitions.Def_ModularCurve_PlaceSpecialization
import Definitions.Def_ModularCurve_GlueData
import Definitions.Def_ModularCurve_ToricDescentData
import Definitions.Def_ModularCurve_PlaceWidthChar
import Definitions.Def_ModularCurve_ProlongationTuple
import Definitions.Def_AlgebraicCurve_GluedPic0Pushforward
import Definitions.Def_AlgebraicCurve_Correspondence
import Theorems.Thm_ModularCurve_degeneracyPushforwardInputs_of_prime
import Theorems.Thm_ModularCurve_PlaceSpecialization_isGoodDiv_pushforwardAlong_and_glueData_eq_of_isModel
import Theorems.Thm_AlgebraicCurve_fundamentalIdentityAlong
import Theorems.Thm_ModularCurve_place_deg_eq_one_of_isAlgClosed
import Theorems.Thm_ModularCurve_hasPrincipalDivisors_modularFunctionFieldC_of_perfectField
import Theorems.Thm_AlgebraicCurve_SemilinearAut_restrict_smul
import Theorems.Thm_AlgebraicCurve_SemilinearAut_ramificationIndex_smul
import Theorems.Thm_ModularCurve_degeneracyPair_finiteSeparableDeg_ssPlaces_preserved_reflected
import Theorems.Thm_ModularCurve_finite_setOf_frobOnPlacesGeomLevel_frobOnPlacesGeomLevel_eq_self
import Theorems.Thm_ModularCurve_exists_degeneracyPair_residueField
import Theorems.Thm_AlgebraicCurve_GluingData_isGluedPrincipal_pushforwardMap_of_separableAlong
import Theorems.Thm_ModularCurve_PlaceSpecialization_exists_isGoodDiv_mem_admissible_mk_eq_reduce_notMem_nodePairsOfPlaces
import Theorems.Thm_ModularCurve_ramificationIndexAlong_mul_placeWidthChar_eq_placeWidthChar_restrictAlong_degeneracyPair
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_PlaceSpecialization_gluedSpecialization_twoLevel_degeneracyGlue_of_isModel_placeWidthChar_restrictAlong
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.SpecializationWitnessData.addCommGroup ModularCurve.CommutingHeckeFamily.commRing_adjoin AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions"
p2m_attr_erase "instance" "WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent ModularCurve.B3.instIsElliptic_goodModel ModularCurve.instIsScalarTowerJAdjoin WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular AlgebraicCurve.CellDissection.fintypeV AlgebraicCurve.CellDissection.fintypeC AlgebraicCurve.CellDissection.fintypeE AlgebraicCurve.CellDissection.decEqV AlgebraicCurve.CellDissection.decEqC AlgebraicCurve.CellDissection.decEqE ModularCurve.numberField_of_finiteDimensional GaloisRepAdic.instAddCommGroup GaloisRepAdic.instFree GaloisRepAdic.instFinite GaloisRepAdic.instModule ResidualGaloisRep.instModule ResidualGaloisRep.instModuleFinite ResidualGaloisRep.instAddCommGroup WeierstrassCurve.Affine.Point.instFinite ModularCurve.IgusaScheme.isOpenImmersion_fInf ModularCurve.IgusaScheme.isOpenImmersion_ιInf ModularCurve.IgusaScheme.fact_jFull_ne_zero ModularCurve.IgusaScheme.isOpenImmersion_ιFin ModularCurve.IgusaScheme.isOpenImmersion_fFin AlgebraicCurve.CurveModel.isProper AlgebraicCurve.CurveModel.isIntegral AlgebraicCurve.CurveModel.smooth CuspForm.heckeAlgebra.instCommRing CuspForm.heckeAlgebra.instIsMulCommutative CuspForm.heckeAlgebra.instIsAddTorsionFree ModularCurve.CuspSpace.instNonempty"
p2m_attr_erase "instance" "ModularCurve.CuspSpace.instSubsingletonOfOne ModularCurve.CuspSpace.instFinite ModularCurve.instAlgebraIntermediateFieldLaurent ModularCurve.instIsScalarTowerKaehlerIntermediateFieldLaurent ModularCurve.instIsScalarTowerIntermediateFieldLaurent ModularCurve.instModuleKaehlerIntermediateFieldLaurent FLT.Gamma0FundamentalSet.instContinuousConstSMulSpecialLinearGroupFinOfNatNatIntUpperHalfPlane_definitions FLT.HyperbolicMeasure.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatIntUpperHalfPlaneVolume_definitions FLT.HyperbolicMeasure.instIsOpenPosMeasureUpperHalfPlaneVolume_definitions FLT.L2ProductionInstance.isFiniteMeasure_gamma0 FLT.L2ProductionInstance.countable_SL2Z FLT.L2ProductionInstance.countable_quotient FLT.L2ProductionInstance.nontrivial_gamma0L2 HeckeEis.instModuleCoeffH1par HeckeEis.instAddCommGroupCoeffH1par HeckeEis.instFiniteIndexHeckeUpper AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing"
p2m_attr_erase "instance" "AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin AlgebraicCurve.CurveModel.chartRing_finitePresentation instFieldLaurentSeriesAlgClosureRat instAlgebraModularFunctionFieldBar ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instAlgebraResidueFieldSubtypeMemValuationSubringGaussBaseResOne ModularCurve.PlaceSpecialization.LevelOneProlongationPair.algGaussBase instAlgebraModularFunctionFieldFullC ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instAlgebraSubtypeMemValuationSubringGaussBaseResOne ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instAlgebraSubtypeMemValuationSubringGaussBaseResTwo instFieldModularFunctionFieldC ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isScalarTower_resOne instFieldLaurentSeries' ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isScalarTower_resTwo instModuleModularFunctionFieldBar ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isLocalHom_resBase₁ instAlgebraModularFunctionFieldC ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isLocalHom_constToGaussBase ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instFieldResOne instFieldModularFunctionFieldBar ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instAlgebraResidueFieldSubtypeMemValuationSubringGaussBaseResTwo ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instFieldResTwo instFieldModularFunctionFieldFullC ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isScalarTower_gaussBase instAlgebraLaurentSeriesAlgClosureRat ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isLocalHom_resBase₂ ModularCurve.PlaceSpecialization.LevelOneProlongationPair.algResidueConst instCommRingModularFunctionFieldBar ModularCurve.instIsElliptic_tateBase ModularCurve.NodeLocalized.isLocalization_nodeDenominators ModularCurve.NodeLocalized.algebraEvalRange ModularCurve.NodeLocalized.isLocalRing_modularLocalizedAtPoint ModularCurve.NodeLocalized.isScalarTower_K_fieldOver_bar ModularCurve.NodeLocalized.algebraFieldOverBar ModularCurve.NodeLocalized.algebra_isIntegral_fieldOver_bar ModularCurve.NodeLocalized.isScalarTower_fieldOver_bar_laurent ModularCurve.NodeLocalized.charZero_fieldOver ModularCurve.NodeLocalized.algebraFieldOver ModularCurve.NodeLocalized.charZero_laurentSeries_algClosure"
p2m_attr_erase "instance" "instTopologicallyFGOfFiniteType AdicCompletion.instIsLocalRingMaximalIdeal WeierstrassCurve.Affine.instIsDiscreteValuationRingSubtypeFunctionFieldMemValuationSubringValuationSubringWithZeroMultiplicativeIntValuationInfty WeierstrassCurve.Affine.valuationInfty_isNontrivial WeierstrassCurve.veluQuotient2_isShortNF WeierstrassCurve.instIsShortNFMk"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaC AlgebraicCurve.Divisor.coe_degZeroEnd ModularCurve.coe_heckeAlphaC ModularCurve.CommutingHeckeFamily.mk.injEq ModularCurve.SpecializationWitnessData.mk.sizeOf_spec ModularCurve.SpecializationWitnessData.mk.injEq ModularCurve.CommutingHeckeFamily.mk.sizeOf_spec ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree"
p2m_attr_erase "simp" "ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.PlaceSpecialization.LevelOneProlongationPair.mk.sizeOf_spec ModularCurve.PlaceSpecialization.LevelOneProlongationPair.residue₂_apply ModularCurve.PlaceSpecialization.LevelOneProlongationPair.residue₁_apply ModularCurve.PlaceSpecialization.LevelOneProlongationPair.mk.injEq ModularCurve.coe_nodeEquiv_symm_apply ModularCurve.frobNodePair_jOfNode ModularCurve.jOfNode_mk ModularCurve.widthOf_mk ModularCurve.frobNodePairEmb_apply ModularCurve.card_nodePairsOf ModularCurve.frobNodePair_snd ModularCurve.coe_nodeEquiv_apply ModularCurve.frobNodePair_fst AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.Place.differentialCoeff_zero"
p2m_attr_erase "simp" "AlgebraicCurve.Place.differentialCoeff_dCoord ModularCurve.cuspCount_one AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule HahnSeries.ramScale_apply compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄"
p2m_attr_erase "simp" "compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm ModularCurve.ProjectiveLine.map_mk ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU"
p2m_attr_erase "simp" "ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ"
p2m_attr_erase "simp" "TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff AlgebraicCurve.abelJacobiDiv_single AlgebraicCurve.AnalyticCoord.mk.injEq AlgebraicCurve.Cell.mk.sizeOf_spec AlgebraicCurve.RadialRegion.mk.sizeOf_spec AlgebraicCurve.RadialRegion.mk.injEq AlgebraicCurve.CellDissection.mk.sizeOf_spec AlgebraicCurve.Cell.mk.injEq AlgebraicCurve.CellDissection.mk.injEq"
p2m_attr_erase "simp" "AlgebraicCurve.AnalyticCoord.mk.sizeOf_spec AddMonoid.End.dualEndDataOfSurjective_trace AddMonoid.End.dualEndDataOfSurjective_norm ModularCurve.frobeniusPullbackGeomLevelUnconditional_single ModularCurve.frobeniusPushforwardGeomLevelUnconditional_single ModularCurve.frobeniusGeomLevelUnconditional_apply_coe ModularCurve.Gamma0Pair.map_toCurve WeierstrassCurve.mapPoint_eq_ratPointMap ModularCurve.Gamma0Pair.map_gen ModularCurve.Gamma0Pair.map_eq_gamma0PairMap ModularCurve.ModuliPoint.map_eq_moduliPointMapRingHom ModularCurve.ModuliPoint.map_mk WeierstrassCurve.mapPointHom_apply WeierstrassCurve.mapPoint_zero WeierstrassCurve.Universal.halveX_zero WeierstrassCurve.Universal.specialize_X_one WeierstrassCurve.Universal.coeff_halve WeierstrassCurve.Universal.specialize_X_two WeierstrassCurve.Universal.halveCoeff_zero WeierstrassCurve.Universal.specialize_X_four WeierstrassCurve.Universal.coeff_halveX WeierstrassCurve.Universal.specialize_X_three WeierstrassCurve.Universal.specialize_X_zero ModularCurve.symPoly_zero GaloisRepAdic.mk.injEq GaloisRepAdic.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.injEq ResidualGaloisRep.mk.sizeOf_spec ResidualGaloisRep.mk.injEq ResidualGaloisRep.Equiv.mk.sizeOf_spec ResidualGaloisRep.Equiv.mk.injEq ModularCurve.CharPModel.FibreModel.mk.injEq ModularCurve.CharPModel.FibreModel.mk.sizeOf_spec ModularCurve.IgusaScheme.ιInf_igusaTo_assoc ModularCurve.IgusaScheme.coe_jFull ModularCurve.IgusaScheme.coe_jInvChartInf ModularCurve.IgusaScheme.coe_jChartFin ModularCurve.IgusaScheme.ιFin_igusaTo ModularCurve.IgusaScheme.ιInf_igusaTo"
p2m_attr_erase "simp" "ModularCurve.IgusaScheme.ιFin_igusaTo_assoc GoodReductionJacobian.RelativePic0Designation.mk.sizeOf_spec GoodReductionJacobian.AvatarSchemeBridge.mk.injEq MilneJVScheme.JacobianSchemeData.mk.injEq GoodReductionJacobian.AvatarSchemeBridge.mk.sizeOf_spec MilneJVScheme.JacobianSchemeData.mk.sizeOf_spec GoodReductionJacobian.RelativePic0Designation.mk.injEq NeronModelInfra.specGenericFibreInclusion_eq NeronModelInfra.genericFibreRestrict_coe_comp_snd NeronModelInfra.genericFibreRestrict_coe_comp_fst GoodReductionJacobian.schemeHomOverComp_coe NeronModelInfra.schemeHomOverEquivOverHom_apply GoodReductionJacobian.RelativeGroupLaw.mk.sizeOf_spec NeronModelInfra.schemeHomOverEquivOverHom_symm_apply NeronModelInfra.overHomToSchemeHomOver_coe GoodReductionJacobian.RelativeGroupLaw.mk.injEq NeronModelInfra.overHomToSchemeHomOver_schemeHomOverToOverHom NeronModelInfra.schemeHomOverToOverHom_left NeronModelInfra.schemeHomOverToOverHom_overHomToSchemeHomOver NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe AlgebraicCurve.CurveModel.mk.injEq AlgebraicCurve.CurveModel.mk.sizeOf_spec ModularCurve.dualHeckeRep_apply_apply ModularCurve.coe_segmentPath ModularCurve.cuspHeckeAeval_heckeGen ModularCurve.coe_periodLatticeRestrict_apply CuspForm.heckeAlgebra.coe_U CuspForm.heckeAlgebra.coe_T ModularForm.coe_heckeTLin_apply CuspForm.coe_heckeULin_apply CuspForm.coe_heckeTLin_apply ModularForm.coe_heckeULin_apply ModularCurve.ComplexPlaceDictionary.mk.injEq ModularCurve.ComplexPlaceDictionary.mk.sizeOf_spec"
p2m_attr_erase "simp" "ModularCurve.Period.IsEquivariantPrimitive.periodHom_apply ModularCurve.Period.IsEquivariantPrimitive.period_one ModularCurve.CuspSpace.cuspDenomAux_infty ModularCurve.CuspSpace.cuspDenomAux_coe ModularCurve.CuspSpace.cuspDenom_mk_zero ModularCurve.CuspSpace.cuspDenom_mk_infty ModularCurve.mapGL_apply_coe ModularCurve.ratPoint_one_zero ModularCurve.ratPoint_zero_right ModularCurve.CuspSpace.fromCoset_mk ModularCurve.CuspSpace.cuspDenom_mk ModularCurve.ratPoint_zero_one ModularCurve.qEulerFun_coeff ModularCurve.diffQExp_D ModularCurve.qEulerOn_apply ModularCurve.qEuler_coeff FLT.TruncatedDomainPartition.unipotentDiagonalSum_zero HeckeEis.coeffCoboundaryMap_apply HeckeEis.heckeConjMat_apply_one_one HeckeEis.coe_heckeConjSL HeckeEis.mem_heckeUpperSL HeckeEis.resHom_apply HeckeEis.heckeConjMat_apply_zero_one HeckeEis.coe_transferAux HeckeEis.coe_heckeConj HeckeEis.alphaMat_apply_one_one HeckeEis.heckeConjMat_apply_one_zero HeckeEis.alphaMat_apply_zero_one HeckeEis.pullbackHom_apply HeckeEis.alphaMat_apply_one_zero HeckeEis.alphaMat_apply_zero_zero HeckeEis.heckeConjMat_apply_zero_zero AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal"
p2m_attr_erase "simp" "AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces ModularCurve.coe_levelPolynomialEquiv_apply ModularCurve.coe_levelBaseRingDescent_apply ModularCurve.levelConst_apply ModularCurve.coe_laurentDescent_apply ModularCurve.PlaceSpecialization.LevelOneProlongationPair.coe_gaussOrderToIntegers₂ ModularCurve.PlaceSpecialization.LevelOneProlongationPair.coe_gaussOrderToIntegers₁ ModularCurve.PlaceSpecialization.LevelOneProlongationPair.coe_toIntegers₁ ModularCurve.PlaceSpecialization.LevelOneProlongationPair.coe_constToGaussBase ModularCurve.PlaceSpecialization.LevelOneProlongationPair.coe_toIntegers₂ ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst ModularCurve.NodeLocalized.coe_modularEvalAt ModularCurve.LambdaModularPolynomialData.mk.sizeOf_spec ModularCurve.LambdaModularPolynomialData.mk.injEq AlgebraicCurve.Pic.baseChange_mk AlgebraicCurve.Place.forgetConstants_toValuationSubring AlgebraicCurve.Place.constantFieldEquiv_symm_apply AlgebraicCurve.Place.ord_forgetConstants AlgebraicCurve.Place.extendConstants_toValuationSubring AlgebraicCurve.Place.constantFieldEquiv_apply_toValuationSubring AlgebraicCurve.Place.mem_fiberConstants AlgebraicCurve.Place.restrictConstants_toValuationSubring ModularCurve.PlaceSpecialization.ProlongationTuple.NodeCoordinates.mk.sizeOf_spec ModularCurve.PlaceSpecialization.ProlongationTuple.coe_nodeConst ModularCurve.PlaceSpecialization.ProlongationTuple.NodeCoordinates.mk.injEq ModularCurve.PlaceSpecialization.ProlongationTuple.nodeResidue₂_apply ModularCurve.PlaceSpecialization.ProlongationTuple.nodeResidue₁_apply AdicCompletion.evalₐ_mapₐ AdicCompletion.mapAlgEquivOfBijective_apply AdicCompletion.levelMapₐ_mk"
p2m_attr_erase "simp" "AdicCompletion.mapₐ_of AdicCompletion.mapAlgEquiv_symm_apply AdicCompletion.mapAlgEquiv_apply AdicCompletion.evalₐ_ofLevelwiseEquiv AdicCompletion.evalₐ_levelwiseHom AdicCompletion.localizationEquiv_of AdicCompletion.evalₐ_ofLevelwiseEquiv_symm Localization.AtPrime.quotientPowEquiv_mk AdicCompletion.transportOf_of AdicCompletion.selfCompletion_smul_of AdicCompletion.tensorRingEquiv_tmul AdicCompletion.completionOfAlgHom_apply AdicCompletion.completionBaseChangeHom_of AdicCompletion.tensorRingHom_tmul AdicCompletion.stabilizerToCompletionAut_of"

set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000
set_option Elab.async false

namespace NodePairTransport

open AlgebraicCurve ModularCurve

variable {K F₁ F₂ : Type*} [Field K] [Field F₁] [Field F₂] [Algebra K F₁] [Algebra K F₂]
variable (σ₁ : SemilinearAut K F₁) (σ₂ : SemilinearAut K F₂)
  {T₁ : Set (Place K F₁)} {T₂ : Set (Place K F₂)}
  {W₁ : Finset (Place K F₁)} {W₂ : Finset (Place K F₂)}
  (hW₁ : ∀ w, w ∈ W₁ ↔ w ∈ T₁) (hW₂ : ∀ w, w ∈ W₂ ↔ w ∈ T₂)

private def pairMap (ab : ↥T₁ → ↥T₂) (n₁ : ↥(nodePairsOfPlaces σ₁ W₁)) : ↥(nodePairsOfPlaces σ₂ W₂) :=
  ⟨smulNodePair σ₂ ↑(ab ⟨(↑n₁ : Place K F₁ × Place K F₁).1,
      (hW₁ _).mp (fst_mem_of_mem_nodePairsOfPlaces n₁.2)⟩),
    smulNodePair_mem_nodePairsOfPlaces _ ((hW₂ _).mpr (ab _).2)⟩

private def pairMult (m : ↥T₁ → ℕ) (n₁ : ↥(nodePairsOfPlaces σ₁ W₁)) : ℕ :=
  m ⟨(↑n₁ : Place K F₁ × Place K F₁).1, (hW₁ _).mp (fst_mem_of_mem_nodePairsOfPlaces n₁.2)⟩

private theorem smulNodePair_fst_coe {F : Type*} [Field F] [Algebra K F] (σ : SemilinearAut K F)
    {W : Finset (Place K F)} (n : ↥(nodePairsOfPlaces σ W)) :
    smulNodePair σ (↑n : Place K F × Place K F).1 = ↑n := by
  obtain ⟨w, _, h⟩ := (mem_nodePairsOfPlaces_iff σ W _).mp n.2
  rw [← h, smulNodePair_fst]

private theorem nodeFibreSum_pairMap [Fintype ↥T₁] [DecidableEq ↥(nodePairsOfPlaces σ₂ W₂)]
    [DecidableEq ↥T₂] (ab : ↥T₁ → ↥T₂) (m : ↥T₁ → ℕ)
    (g : ↥(nodePairsOfPlaces σ₁ W₁) → Additive Kˣ) (n₂ : ↥(nodePairsOfPlaces σ₂ W₂)) :
    GluingData.nodeFibreSum (nodePairsOfPlaces σ₁ W₁) (nodePairsOfPlaces σ₂ W₂)
        (pairMap σ₁ σ₂ hW₁ hW₂ ab) (pairMult σ₁ hW₁ m) g n₂
      = ∑ p₁ with ab p₁ =
            (⟨(↑n₂ : Place K F₂ × Place K F₂).1,
              (hW₂ _).mp (fst_mem_of_mem_nodePairsOfPlaces n₂.2)⟩ : ↥T₂),
          m p₁ • g ⟨smulNodePair σ₁ ↑p₁,
            smulNodePair_mem_nodePairsOfPlaces _ ((hW₁ ↑p₁).mpr p₁.2)⟩ := by
  rw [GluingData.nodeFibreSum_apply]
  refine Finset.sum_nbij'
    (fun n₁ => ⟨(↑n₁ : Place K F₁ × Place K F₁).1,
      (hW₁ _).mp (fst_mem_of_mem_nodePairsOfPlaces n₁.2)⟩)
    (fun p₁ => ⟨smulNodePair σ₁ ↑p₁, smulNodePair_mem_nodePairsOfPlaces _ ((hW₁ ↑p₁).mpr p₁.2)⟩)
    ?_ ?_ ?_ ?_ ?_
  ·
    intro n₁ hn₁
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hn₁ ⊢
    exact Subtype.ext
      (congrArg (fun n : ↥(nodePairsOfPlaces σ₂ W₂) => (↑n : Place K F₂ × Place K F₂).1) hn₁)
  ·
    intro p₁ hp₁
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp₁ ⊢
    apply Subtype.ext
    have h₁ : (⟨(smulNodePair σ₁ (↑p₁ : Place K F₁)).1,
        (hW₁ _).mp (fst_mem_of_mem_nodePairsOfPlaces
          (smulNodePair_mem_nodePairsOfPlaces _ ((hW₁ ↑p₁).mpr p₁.2)))⟩ : ↥T₁) = p₁ :=
      Subtype.ext rfl
    show smulNodePair σ₂ _ = _
    rw [h₁, hp₁]
    exact smulNodePair_fst_coe σ₂ n₂
  · intro n₁ _
    exact Subtype.ext (smulNodePair_fst_coe σ₁ n₁)
  · intro p₁ _
    exact Subtype.ext rfl
  · intro n₁ _
    exact congrArg₂ (fun (a : ℕ) (b : Additive Kˣ) => a • b) rfl
      (congrArg g (Subtype.ext (smulNodePair_fst_coe σ₁ n₁))).symm

variable {σ₁ σ₂}

private theorem pushforwardMap_nodeUnit_pairMap [Fintype ↥T₁] [DecidableEq ↥(nodePairsOfPlaces σ₂ W₂)]
    [DecidableEq ↥T₂]
    (ab : ↥T₁ → ↥T₂) (m : ↥T₁ → ℕ)
    (φ : F₂ →ₐ[K] F₁) (hφ : φ.toRingHom.IsIntegral)
    (hadm : ∀ x ∈ GluingData.admissible (nodePairsOfPlaces σ₁ W₁),
      GluingData.pushforwardMap (nodePairsOfPlaces σ₁ W₁) (nodePairsOfPlaces σ₂ W₂)
        (pairMap σ₁ σ₂ hW₁ hW₂ ab) (pairMult σ₁ hW₁ m) φ hφ x
          ∈ GluingData.admissible (nodePairsOfPlaces σ₂ W₂))
    (hprin : ∀ x : GluingData K F₁ (nodePairsOfPlaces σ₁ W₁),
      GluingData.IsGluedPrincipal (nodePairsOfPlaces σ₁ W₁) x →
        GluingData.IsGluedPrincipal (nodePairsOfPlaces σ₂ W₂)
          (GluingData.pushforwardMap (nodePairsOfPlaces σ₁ W₁) (nodePairsOfPlaces σ₂ W₂)
            (pairMap σ₁ σ₂ hW₁ hW₂ ab) (pairMult σ₁ hW₁ m) φ hφ x))
    (g : ↥(nodePairsOfPlaces σ₁ W₁) → Additive Kˣ) :
    GluedPic0.pushforwardMap (nodePairsOfPlaces σ₁ W₁) (nodePairsOfPlaces σ₂ W₂)
        (pairMap σ₁ σ₂ hW₁ hW₂ ab) (pairMult σ₁ hW₁ m) φ hφ hadm hprin
        (GluedPic0.nodeUnit (nodePairsOfPlaces σ₁ W₁) g)
      = GluedPic0.nodeUnit (nodePairsOfPlaces σ₂ W₂)
          (fun n₂ => ∑ p₁ with ab p₁ =
              (⟨(↑n₂ : Place K F₂ × Place K F₂).1,
                (hW₂ _).mp (fst_mem_of_mem_nodePairsOfPlaces n₂.2)⟩ : ↥T₂),
            m p₁ • g ⟨smulNodePair σ₁ ↑p₁,
              smulNodePair_mem_nodePairsOfPlaces _ ((hW₁ ↑p₁).mpr p₁.2)⟩) := by
  rw [GluedPic0.pushforwardMap_nodeUnit]
  exact congrArg _ (funext fun n₂ => nodeFibreSum_pairMap σ₁ σ₂ hW₁ hW₂ ab m g n₂)

end NodePairTransport

open AlgebraicCurve IsLocalRing ModularCurve

private theorem collfin_fixed (M s q' : ℕ) [NeZero M] [NeZero s] (hq' : q'.Prime)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q') :
    haveI : NeZero q' := ⟨hq'.ne_zero⟩
    haveI : Fact q'.Prime := ⟨hq'⟩
    haveI : CharP (ResidueField A) q' := ValuationSubring.charP_residueField_of_liesOverPrime_def hq' hA
    letI := instDecidableEqResidueFieldSemistable A
    letI := instAlgebraResidueFieldModularFunctionFieldCSemistable A (M * s)
    letI := instAlgebraResidueFieldModularFunctionFieldCSemistable A M
    ∀ (data : ModularPolynomialData q') (hKr : KroneckerCongruence q' data)
      (ψ : ↥(modularFunctionFieldC (ResidueField A) M) →ₐ[ResidueField A]
        ↥(modularFunctionFieldC (ResidueField A) (M * s)))
      (_hψ : ψ.toRingHom.IsIntegral),
      Set.Finite {v : Place (ResidueField A) ↥(modularFunctionFieldC (ResidueField A) M) |
        frobOnPlacesGeomLevel (ResidueField A) M data hKr (frobOnPlacesGeomLevel (ResidueField A) M data hKr v) = v} :=
            by
  haveI : NeZero q' := ⟨hq'.ne_zero⟩
  haveI : Fact q'.Prime := ⟨hq'⟩
  haveI : CharP (ResidueField A) q' := ValuationSubring.charP_residueField_of_liesOverPrime_def hq' hA
  letI := instDecidableEqResidueFieldSemistable A
  letI := instAlgebraResidueFieldModularFunctionFieldCSemistable A (M * s)
  letI := instAlgebraResidueFieldModularFunctionFieldCSemistable A M
  intro data hKr ψ hψ
  exact finite_setOf_frobOnPlacesGeomLevel_frobOnPlacesGeomLevel_eq_self (ResidueField A) M data hKr

private theorem collfin_fibre (M s q' : ℕ) [NeZero M] [NeZero s] (hq' : q'.Prime)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q') :
    haveI : NeZero q' := ⟨hq'.ne_zero⟩
    haveI : Fact q'.Prime := ⟨hq'⟩
    haveI : CharP (ResidueField A) q' := ValuationSubring.charP_residueField_of_liesOverPrime_def hq' hA
    letI := instDecidableEqResidueFieldSemistable A
    letI := instAlgebraResidueFieldModularFunctionFieldCSemistable A (M * s)
    letI := instAlgebraResidueFieldModularFunctionFieldCSemistable A M
    ∀ (data : ModularPolynomialData q') (_hKr : KroneckerCongruence q' data)
      (ψ : ↥(modularFunctionFieldC (ResidueField A) M) →ₐ[ResidueField A]
        ↥(modularFunctionFieldC (ResidueField A) (M * s)))
      (hψ : ψ.toRingHom.IsIntegral),
      ∀ v : Place (ResidueField A) ↥(modularFunctionFieldC (ResidueField A) M),
        Set.Finite {w : Place (ResidueField A) ↥(modularFunctionFieldC (ResidueField A) (M * s)) | w.restrictAlong ψ hψ
            = v} := by
  haveI : NeZero q' := ⟨hq'.ne_zero⟩
  haveI : Fact q'.Prime := ⟨hq'⟩
  haveI : CharP (ResidueField A) q' := ValuationSubring.charP_residueField_of_liesOverPrime_def hq' hA
  letI := instDecidableEqResidueFieldSemistable A
  letI := instAlgebraResidueFieldModularFunctionFieldCSemistable A (M * s)
  letI := instAlgebraResidueFieldModularFunctionFieldCSemistable A M
  intro data hKr ψ hψ v
  haveI : HasPrincipalDivisors (ResidueField A) ↥(modularFunctionFieldC (ResidueField A) (M * s)) :=
    hasPrincipalDivisors_modularFunctionFieldC_of_perfectField (ResidueField A) (M * s)
  refine (Place.fiberAlong ψ hψ v).finite_toSet.subset ?_
  intro w hw
  exact Place.mem_fiberAlong.2 hw

private theorem loc_COLLFIN (M s q' : ℕ) [NeZero M] [NeZero s] (hq' : q'.Prime)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q') :
    haveI : NeZero q' := ⟨hq'.ne_zero⟩
    haveI : Fact q'.Prime := ⟨hq'⟩
    haveI : CharP (ResidueField A) q' := ValuationSubring.charP_residueField_of_liesOverPrime_def hq' hA
    letI := instDecidableEqResidueFieldSemistable A
    letI := instAlgebraResidueFieldModularFunctionFieldCSemistable A (M * s)
    letI := instAlgebraResidueFieldModularFunctionFieldCSemistable A M
    ∀ (data : ModularPolynomialData q') (hKr : KroneckerCongruence q' data)
      (ψ : ↥(modularFunctionFieldC (ResidueField A) M) →ₐ[ResidueField A]
        ↥(modularFunctionFieldC (ResidueField A) (M * s)))
      (hψ : ψ.toRingHom.IsIntegral),
      Set.Finite {w : Place (ResidueField A) ↥(modularFunctionFieldC (ResidueField A) (M * s)) |
        frobOnPlacesGeomLevel (ResidueField A) M data hKr
            (frobOnPlacesGeomLevel (ResidueField A) M data hKr (w.restrictAlong ψ hψ)) =
          w.restrictAlong ψ hψ} := by
  haveI : NeZero q' := ⟨hq'.ne_zero⟩
  haveI : Fact q'.Prime := ⟨hq'⟩
  haveI : CharP (ResidueField A) q' := ValuationSubring.charP_residueField_of_liesOverPrime_def hq' hA
  letI := instDecidableEqResidueFieldSemistable A
  letI := instAlgebraResidueFieldModularFunctionFieldCSemistable A (M * s)
  letI := instAlgebraResidueFieldModularFunctionFieldCSemistable A M
  intro data hKr ψ hψ
  have hfix := collfin_fixed M s q' hq' A hA data hKr ψ hψ
  have hfib := collfin_fibre M s q' hq' A hA data hKr ψ hψ
  have h : ((fun w : Place (ResidueField A) ↥(modularFunctionFieldC (ResidueField A) (M * s)) =>
      w.restrictAlong ψ hψ) ⁻¹'
      {v : Place (ResidueField A) ↥(modularFunctionFieldC (ResidueField A) M) |
        frobOnPlacesGeomLevel (ResidueField A) M data hKr (frobOnPlacesGeomLevel (ResidueField A) M data hKr v) =
            v}).Finite :=
    hfix.preimage' fun b _ => (hfib b).subset fun w hw =>
      Set.mem_singleton_iff.1 (Set.mem_preimage.1 hw)
  exact h

private theorem loc_LEGS (M s q' : ℕ) [NeZero M] [NeZero s] (hq' : q'.Prime)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q') (hq'Ms : ¬ q' ∣ M * s) :
    haveI : NeZero q' := ⟨hq'.ne_zero⟩
    haveI : Fact q'.Prime := ⟨hq'⟩
    haveI : CharP (ResidueField A) q' := ValuationSubring.charP_residueField_of_liesOverPrime_def hq' hA
    letI := instAlgebraResidueFieldModularFunctionFieldCSemistable A (M * s)
    letI := instAlgebraResidueFieldModularFunctionFieldCSemistable A M
    ∃ (φ : Fin 2 → (↥(modularFunctionFieldC (ResidueField A) M) →ₐ[ResidueField A]
        ↥(modularFunctionFieldC (ResidueField A) (M * s))))
      (_ : ∀ i, (φ i).toRingHom.IsIntegral),
      (∀ x, ((φ 0 x : ↥(modularFunctionFieldC (ResidueField A) (M * s))) :
          LaurentSeries (ResidueField A)) = x) ∧
      (∀ x, ((φ 1 x : ↥(modularFunctionFieldC (ResidueField A) (M * s))) :
          LaurentSeries (ResidueField A)) = qExpand (ResidueField A) s x) := by
  exact ModularCurve.exists_degeneracyPair_residueField M s q' hq' A hA hq'Ms

private theorem loc_BETA_SEP
    {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
    [HasPrincipalDivisors K F']
    (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral)
    (hfin : FiniteAlong K φ) (hsep : SeparableAlong K φ)
    (S' : Finset (Place K F' × Place K F')) (S : Finset (Place K F × Place K F)) [DecidableEq ↥S]
    (ν : ↥S' → ↥S)
    (hν : ∀ n' : ↥S',
      ((ν n' : ↥S) : Place K F × Place K F).1 = Place.restrictAlong φ hφ (n' : Place K F' × Place K F').1 ∧
        ((ν n' : ↥S) : Place K F × Place K F).2 = Place.restrictAlong φ hφ (n' : Place K F' × Place K F').2)
    (hfst : ∀ (n : ↥S) (w : Place K F'), Place.restrictAlong φ hφ w = (n : Place K F × Place K F).1 →
      ∃! n' : ↥S', ν n' = n ∧ (n' : Place K F' × Place K F').1 = w)
    (hsnd : ∀ (n : ↥S) (w : Place K F'), Place.restrictAlong φ hφ w = (n : Place K F × Place K F).2 →
      ∃! n' : ↥S', ν n' = n ∧ (n' : Place K F' × Place K F').2 = w)
    (m : ↥S' → ℕ)
    (hm₁ : ∀ n' : ↥S', m n' = Place.ramificationIndexAlong φ (n' : Place K F' × Place K F').1 *
      Place.inertiaDegAlong φ hφ (n' : Place K F' × Place K F').1)
    (hm₂ : ∀ n' : ↥S', m n' = Place.ramificationIndexAlong φ (n' : Place K F' × Place K F').2 *
      Place.inertiaDegAlong φ hφ (n' : Place K F' × Place K F').2)
    {x : GluingData K F' S'} (hx : GluingData.IsGluedPrincipal S' x) :
    GluingData.IsGluedPrincipal S (GluingData.pushforwardMap S' S ν m φ hφ x) := by
  exact AlgebraicCurve.GluingData.isGluedPrincipal_pushforwardMap_of_separableAlong φ hφ hfin hsep S' S ν hν
    hfst hsnd m hm₁ hm₂ hx

private theorem frob_intertwines_degeneracy (M s q' : ℕ) [NeZero M] [NeZero s] [Fact q'.Prime]
    {k : Type*} [Field k] [CharP k q'] [PerfectField k] :
    haveI : NeZero (M * s) := ⟨Nat.mul_ne_zero (NeZero.ne M) (NeZero.ne s)⟩
    ∀ (φ : Fin 2 → (↥(modularFunctionFieldC k M) →ₐ[k] ↥(modularFunctionFieldC k (M * s))))
      (hφα : ∀ x, ((φ 0 x : ↥(modularFunctionFieldC k (M * s))) : LaurentSeries k) = x)
      (hφβ : ∀ x, ((φ 1 x : ↥(modularFunctionFieldC k (M * s))) : LaurentSeries k) = qExpand k s x)
      (i : Fin 2),
      SemilinearAut.IntertwinesAlong (φ i).toRingHom (arithFrobC q' k M) (arithFrobC q' k (M * s)) := by
  haveI : NeZero (M * s) := ⟨Nat.mul_ne_zero (NeZero.ne M) (NeZero.ne s)⟩
  intro φ hφα hφβ
  refine Fin.forall_fin_two.mpr ⟨fun x => ?_, fun x => ?_⟩
  · apply Subtype.ext
    show ((arithFrobC q' k (M * s) • φ 0 x : ↥(modularFunctionFieldC k (M * s))) : LaurentSeries k) =
      ((φ 0 (arithFrobC q' k M • x) : ↥(modularFunctionFieldC k (M * s))) : LaurentSeries k)
    rw [hφα (arithFrobC q' k M • x)]
    simp only [arithFrobC, coe_coeffSemilinearAut_smul, hφα]
  · apply Subtype.ext
    show ((arithFrobC q' k (M * s) • φ 1 x : ↥(modularFunctionFieldC k (M * s))) : LaurentSeries k) =
      ((φ 1 (arithFrobC q' k M • x) : ↥(modularFunctionFieldC k (M * s))) : LaurentSeries k)
    rw [hφβ (arithFrobC q' k M • x)]
    simp only [arithFrobC, coe_coeffSemilinearAut_smul, hφβ, coeffSemilinearAut.coeffMap_qExpand]

private theorem loc_ARITHCOMM (M s q' : ℕ) [NeZero M] [NeZero s] [Fact q'.Prime]
    {k : Type*} [Field k] [CharP k q'] [PerfectField k] :
    haveI : NeZero (M * s) := ⟨Nat.mul_ne_zero (NeZero.ne M) (NeZero.ne s)⟩
    ∀ (φ : Fin 2 → (↥(modularFunctionFieldC k M) →ₐ[k] ↥(modularFunctionFieldC k (M * s))))
      (hφ : ∀ i, (φ i).toRingHom.IsIntegral)
      (hφα : ∀ x, ((φ 0 x : ↥(modularFunctionFieldC k (M * s))) : LaurentSeries k) = x)
      (hφβ : ∀ x, ((φ 1 x : ↥(modularFunctionFieldC k (M * s))) : LaurentSeries k) = qExpand k s x)
      (i : Fin 2) (p : Place k ↥(modularFunctionFieldC k (M * s))),
      Place.restrictAlong (φ i) (hφ i) (arithFrobC q' k (M * s) • p) =
        arithFrobC q' k M • Place.restrictAlong (φ i) (hφ i) p := by
  haveI : NeZero (M * s) := ⟨Nat.mul_ne_zero (NeZero.ne M) (NeZero.ne s)⟩
  intro φ hφ hφα hφβ i p
  letI := algebraAlong (φ i)
  haveI := isScalarTower_along (φ i)
  haveI := isIntegral_along (φ i) (hφ i)
  exact SemilinearAut.restrict_smul (frob_intertwines_degeneracy M s q' φ hφα hφβ i) p

private theorem loc_RAMFROB (M s q' : ℕ) [NeZero M] [NeZero s] [Fact q'.Prime]
    {k : Type*} [Field k] [CharP k q'] [PerfectField k] :
    haveI : NeZero (M * s) := ⟨Nat.mul_ne_zero (NeZero.ne M) (NeZero.ne s)⟩
    ∀ (φ : Fin 2 → (↥(modularFunctionFieldC k M) →ₐ[k] ↥(modularFunctionFieldC k (M * s))))
      (hφ : ∀ i, (φ i).toRingHom.IsIntegral)
      (hφα : ∀ x, ((φ 0 x : ↥(modularFunctionFieldC k (M * s))) : LaurentSeries k) = x)
      (hφβ : ∀ x, ((φ 1 x : ↥(modularFunctionFieldC k (M * s))) : LaurentSeries k) = qExpand k s x)
      (i : Fin 2) (p : Place k ↥(modularFunctionFieldC k (M * s))),
      Place.ramificationIndexAlong (φ i) (arithFrobC q' k (M * s) • p) =
        Place.ramificationIndexAlong (φ i) p := by
  haveI : NeZero (M * s) := ⟨Nat.mul_ne_zero (NeZero.ne M) (NeZero.ne s)⟩
  intro φ hφ hφα hφβ i p
  letI := algebraAlong (φ i)
  exact SemilinearAut.ramificationIndex_smul (frob_intertwines_degeneracy M s q' φ hφα hφβ i) p

private theorem loc_INERTIA1 {k F F' : Type*} [Field k] [Field F] [Field F']
    [Algebra k F] [Algebra k F'] (φ : F →ₐ[k] F') (hφ : φ.toRingHom.IsIntegral)
    (w : Place k F') (hw : w.deg = 1) : Place.inertiaDegAlong φ hφ w = 1 := by
  letI := algebraAlong φ
  haveI := isScalarTower_along φ
  haveI := isIntegral_along φ hφ
  have h := Place.deg_restrict_mul_inertiaDeg (F := F) w
  rw [hw] at h
  exact Nat.eq_one_of_mul_eq_one_left h

private theorem pushforwardAlongHom_levelCast
    {n₁ n₂ : ℕ} (h : n₁ = n₂) {F : Type*} [Field F] [Algebra (AlgebraicClosure ℚ) F]
    (ψ : F →ₐ[AlgebraicClosure ℚ] ↥(modularFunctionFieldBar n₂)) (hψ : ψ.toRingHom.IsIntegral)
    (hfin : FiniteAlong (AlgebraicClosure ℚ) ψ) (hN : NormFormulaAlong (AlgebraicClosure ℚ) ψ hfin)
    (hle : modularFunctionFieldBar n₂ ≤ modularFunctionFieldBar n₁)
    (hδ : ((IntermediateField.inclusion hle).comp ψ).toRingHom.IsIntegral)
    (D : ↥(Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar n₁))))
    (y : JZero n₁) (z : JZero n₂) (hz : h ▸ y = z) (hy : Pic0.mk D = y) :
    Pic0.pushforwardAlongHom ψ hψ hfin hN z =
      Pic0.mk ⟨Divisor.pushforwardAlong ((IntermediateField.inclusion hle).comp ψ) hδ
          (D : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar n₁)),
        Divisor.pushforwardAlong_mem_degZero _ _ D.2⟩ := by
  subst h hy
  subst hz
  have hc : (IntermediateField.inclusion hle).comp ψ = ψ := AlgHom.ext fun x => Subtype.ext rfl
  revert hδ
  rw [hc]
  intro hδ
  exact Pic0.pushforwardAlongHom_mk ψ hψ hfin hN D

private noncomputable def degeneracyLegsBar (M s q' : ℕ) [NeZero M] [NeZero s] [NeZero q']
    (hle : modularFunctionFieldBar (M * q' * s) ≤ modularFunctionFieldBar (M * s * q')) :
    Fin 2 → (↥(modularFunctionFieldBar (M * q')) →ₐ[AlgebraicClosure ℚ]
      ↥(modularFunctionFieldBar (M * s * q'))) :=
  ![(IntermediateField.inclusion hle).comp (heckeAlphaBar (AlgebraicClosure ℚ) (M * q') s),
    (IntermediateField.inclusion hle).comp (heckeBetaBar (AlgebraicClosure ℚ) (M * q') s)]

private theorem degeneracyLegsBar_zero (M s q' : ℕ) [NeZero M] [NeZero s] [NeZero q']
    (hle : modularFunctionFieldBar (M * q' * s) ≤ modularFunctionFieldBar (M * s * q')) :
    degeneracyLegsBar M s q' hle 0 =
      (IntermediateField.inclusion hle).comp (heckeAlphaBar (AlgebraicClosure ℚ) (M * q') s) :=
  rfl

private theorem degeneracyLegsBar_one (M s q' : ℕ) [NeZero M] [NeZero s] [NeZero q']
    (hle : modularFunctionFieldBar (M * q' * s) ≤ modularFunctionFieldBar (M * s * q')) :
    degeneracyLegsBar M s q' hle 1 =
      (IntermediateField.inclusion hle).comp (heckeBetaBar (AlgebraicClosure ℚ) (M * q') s) :=
  rfl

private theorem degeneracyLegsBar_coe_zero (M s q' : ℕ) [NeZero M] [NeZero s] [NeZero q']
    (hle : modularFunctionFieldBar (M * q' * s) ≤ modularFunctionFieldBar (M * s * q'))
    (y : ↥(modularFunctionFieldBar (M * q'))) :
    ((degeneracyLegsBar M s q' hle 0 y : ↥(modularFunctionFieldBar (M * s * q'))) :
      LaurentSeries (AlgebraicClosure ℚ)) = y := by
  have h : degeneracyLegsBar M s q' hle 0 y =
      IntermediateField.inclusion hle (heckeAlphaBar (AlgebraicClosure ℚ) (M * q') s y) := rfl
  exact (congrArg Subtype.val h).trans
    ((IntermediateField.coe_inclusion hle _).trans (coe_heckeAlphaBar (N := M * q') (ℓ := s) y))

private theorem degeneracyLegsBar_coe_one (M s q' : ℕ) [NeZero M] [NeZero s] [NeZero q']
    (hle : modularFunctionFieldBar (M * q' * s) ≤ modularFunctionFieldBar (M * s * q'))
    (y : ↥(modularFunctionFieldBar (M * q'))) :
    ((degeneracyLegsBar M s q' hle 1 y : ↥(modularFunctionFieldBar (M * s * q'))) :
      LaurentSeries (AlgebraicClosure ℚ)) = qExpand (AlgebraicClosure ℚ) s y := by
  have h : degeneracyLegsBar M s q' hle 1 y =
      IntermediateField.inclusion hle (heckeBetaBar (AlgebraicClosure ℚ) (M * q') s y) := rfl
  exact (congrArg Subtype.val h).trans
    ((IntermediateField.coe_inclusion hle _).trans (coe_heckeBetaBar (N := M * q') (ℓ := s) y))

private theorem classTransport (M s q' : ℕ) [NeZero M] [NeZero s] [NeZero q'] [Fact s.Prime]
    (hle : modularFunctionFieldBar (M * q' * s) ≤ modularFunctionFieldBar (M * s * q'))
    (hαI : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) (M * q') s)
    (hβI : HeckeBetaBarIntegral (AlgebraicClosure ℚ) (M * q') s)
    (hfinα : FiniteAlong (AlgebraicClosure ℚ) (heckeAlphaBar (AlgebraicClosure ℚ) (M * q') s))
    (hNα : NormFormulaAlong (AlgebraicClosure ℚ) (heckeAlphaBar (AlgebraicClosure ℚ) (M * q') s) hfinα)
    (hfinβ : FiniteAlong (AlgebraicClosure ℚ) (heckeBetaBar (AlgebraicClosure ℚ) (M * q') s))
    (hNβ : NormFormulaAlong (AlgebraicClosure ℚ) (heckeBetaBar (AlgebraicClosure ℚ) (M * q') s) hfinβ)
    (hδ : ∀ j, (degeneracyLegsBar M s q' hle j).toRingHom.IsIntegral) (i : Fin 2)
    (D : ↥(Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar (M * s * q')))))
    (x : JZero (M * s * q')) (z : JZero (M * q' * s)) (hz : Nat.mul_right_comm M s q' ▸ x = z)
    (hDx : Pic0.mk D = x) :
    Pic0.mk ⟨Divisor.pushforwardAlong (degeneracyLegsBar M s q' hle i) (hδ i)
          (D : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (M * s * q'))),
        Divisor.pushforwardAlong_mem_degZero _ _ D.2⟩ =
      degeneracyPushforwardPair (M * q') s i z := by
  rw [degeneracyPushforwardPair_eq hαI hβI hfinα hNα hfinβ hNβ]
  fin_cases i
  · exact (pushforwardAlongHom_levelCast (Nat.mul_right_comm M s q')
      (heckeAlphaBar (AlgebraicClosure ℚ) (M * q') s) hαI hfinα hNα hle (hδ 0) D x z hz hDx).symm
  · exact (pushforwardAlongHom_levelCast (Nat.mul_right_comm M s q')
      (heckeBetaBar (AlgebraicClosure ℚ) (M * q') s) hβI hfinβ hNβ hle (hδ 1) D x z hz hDx).symm

private theorem goodRep_package
    (M s q' : ℕ) [NeZero M] [NeZero s] (hs : s.Prime) (hq' : q'.Prime)
    (hsq' : s ≠ q') (hq'M : ¬ q' ∣ M) (hsM : ¬ s ∣ M)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q') :
    haveI : NeZero q' := ⟨hq'.ne_zero⟩
    haveI : Fact q'.Prime := ⟨hq'⟩
    haveI : CharP (ResidueField A) q' := ValuationSubring.charP_residueField_of_liesOverPrime_def hq' hA
    letI := heckeModuleBar ((M * s) * q')
    letI := heckeModuleBar (M * s)
    letI := heckeModuleBar (M * q')
    letI := heckeModuleBar M
    letI := instDecidableEqResidueFieldSemistable A
    letI := instAlgebraResidueFieldModularFunctionFieldCSemistable A (M * s)
    letI := instAlgebraResidueFieldModularFunctionFieldCSemistable A M
    ∀ [Fintype ↥(ssPlaces q' (M * s) (ResidueField A))]
      [Fintype ↥(ssPlaces q' M (ResidueField A))]
      [DecidableEq ↥(ssPlaces q' (M * s) (ResidueField A))]
      [DecidableEq ↥(ssPlaces q' M (ResidueField A))],
    ∀ (W₁ : Finset (Place (ResidueField A) (modularFunctionFieldC (ResidueField A) (M * s))))
      (hW₁ : ∀ w, w ∈ W₁ ↔ w ∈ ssPlaces q' (M * s) (ResidueField A))
      (hstab₁ : SemilinearAut.IsNodeStable
        (nodePairsOfPlaces (arithFrobC q' (ResidueField A) (M * s)) W₁) (arithFrobC q' (ResidueField A) (M * s)))
      (data₁ : ModularPolynomialData q') (hKr₁ : KroneckerCongruence q' data₁)
      (hα₁ : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) (M * s) q')
      (hβ₁ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) (M * s) q')
      (P₁ : PlaceSpecialization A q' (M * s) data₁ hKr₁ (ResidueField A) (IsLocalRing.residue A) hα₁ hβ₁)
      (R₁ : PlaceSpecialization.ProlongationTuple P₁) (hmodel₁ : R₁.IsModel) (hO₁ : R₁.OrderLawFixed)
      (e₁ : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) (M * s)) → ℕ)
      (he₁ : ∀ p ∈ W₁, 0 < e₁ p)
      (hpin₁ : ∀ w ∈ W₁, e₁ w = placeWidthChar q' (M * s) w)
      (comp₁ : ↥(inertiaInvariants A ((M * s) * q')) →+
        componentGroup (widthOfPlaces (arithFrobC q' (ResidueField A) (M * s)) W₁ e₁))
      (sp₁ : ↥(inertiaInvariants A ((M * s) * q')) →+
        GluedPic0 (ResidueField A) (modularFunctionFieldC (ResidueField A) (M * s))
          (nodePairsOfPlaces (arithFrobC q' (ResidueField A) (M * s)) W₁))
      (hsurj₁ : Function.Surjective comp₁)
      (hker₁ : ∀ x : ↥(inertiaInvariants A ((M * s) * q')),
        comp₁ x = 0 ↔ P₁.IsGoodClass (nodePairsOfPlaces (arithFrobC q' (ResidueField A) (M * s)) W₁) (x : JZero ((M *
            s) * q')))
      (hsp₁ : P₁.IsGluedSpecialization (nodePairsOfPlaces (arithFrobC q' (ResidueField A) (M * s)) W₁) sp₁),
    ∀ (W₂ : Finset (Place (ResidueField A) (modularFunctionFieldC (ResidueField A) (M))))
      (hW₂ : ∀ w, w ∈ W₂ ↔ w ∈ ssPlaces q' (M) (ResidueField A))
      (hstab₂ : SemilinearAut.IsNodeStable
        (nodePairsOfPlaces (arithFrobC q' (ResidueField A) (M)) W₂) (arithFrobC q' (ResidueField A) (M)))
      (data₂ : ModularPolynomialData q') (hKr₂ : KroneckerCongruence q' data₂)
      (hα₂ : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) (M) q')
      (hβ₂ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) (M) q')
      (P₂ : PlaceSpecialization A q' (M) data₂ hKr₂ (ResidueField A) (IsLocalRing.residue A) hα₂ hβ₂)
      (R₂ : PlaceSpecialization.ProlongationTuple P₂) (hmodel₂ : R₂.IsModel) (hO₂ : R₂.OrderLawFixed)
      (e₂ : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) (M)) → ℕ)
      (he₂ : ∀ p ∈ W₂, 0 < e₂ p)
      (hpin₂ : ∀ w ∈ W₂, e₂ w = placeWidthChar q' M w)
      (comp₂ : ↥(inertiaInvariants A ((M) * q')) →+
        componentGroup (widthOfPlaces (arithFrobC q' (ResidueField A) (M)) W₂ e₂))
      (sp₂ : ↥(inertiaInvariants A ((M) * q')) →+
        GluedPic0 (ResidueField A) (modularFunctionFieldC (ResidueField A) (M))
          (nodePairsOfPlaces (arithFrobC q' (ResidueField A) (M)) W₂))
      (hsurj₂ : Function.Surjective comp₂)
      (hker₂ : ∀ x : ↥(inertiaInvariants A ((M) * q')),
        comp₂ x = 0 ↔ P₂.IsGoodClass (nodePairsOfPlaces (arithFrobC q' (ResidueField A) (M)) W₂) (x : JZero ((M) *
            q')))
      (hsp₂ : P₂.IsGluedSpecialization (nodePairsOfPlaces (arithFrobC q' (ResidueField A) (M)) W₂) sp₂),
    ∀ (ab : Fin 2 → (↥(ssPlaces q' (M * s) (ResidueField A)) → ↥(ssPlaces q' M (ResidueField A))))
      (m : Fin 2 → ↥(ssPlaces q' (M * s) (ResidueField A)) → ℕ)
      (φ : Fin 2 → ((modularFunctionFieldC (ResidueField A) M) →ₐ[ResidueField A] (modularFunctionFieldC (ResidueField
          A) (M * s))))
      (hφ : ∀ i, (φ i).toRingHom.IsIntegral)
      (hφα : ∀ x, ((φ 0 x : ↥(modularFunctionFieldC (ResidueField A) (M * s))) : LaurentSeries (ResidueField A)) = x)
      (hφβ : ∀ x, ((φ 1 x : ↥(modularFunctionFieldC (ResidueField A) (M * s))) : LaurentSeries (ResidueField A)) =
        qExpand (ResidueField A) s x)
      [DecidableEq ↥(nodePairsOfPlaces (arithFrobC q' (ResidueField A) M) W₂)]
      (hadm : ∀ (i : Fin 2), ∀ x ∈ GluingData.admissible (nodePairsOfPlaces (arithFrobC q' (ResidueField A) (M * s))
          W₁),
        GluingData.pushforwardMap (nodePairsOfPlaces (arithFrobC q' (ResidueField A) (M * s)) W₁) (nodePairsOfPlaces
            (arithFrobC q' (ResidueField A) M) W₂)
          (NodePairTransport.pairMap _ _ hW₁ hW₂ (ab i)) (NodePairTransport.pairMult _ hW₁ (m i)) (φ i) (hφ i) x
            ∈ GluingData.admissible (nodePairsOfPlaces (arithFrobC q' (ResidueField A) M) W₂)),
    ∀ (i : Fin 2) (x : ↥(inertiaInvariants A ((M * s) * q'))) (z : JZero ((M * q') * s))
      (_ : Nat.mul_right_comm M s q' ▸ (x : JZero ((M * s) * q')) = z),
      P₁.IsGoodClass (nodePairsOfPlaces (arithFrobC q' (ResidueField A) (M * s)) W₁) (x : JZero ((M * s) * q')) →
        ∀ (hle : modularFunctionFieldBar (M * q' * s) ≤ modularFunctionFieldBar (M * s * q')),
          ∃ (D : ↥(Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar ((M * s) * q')))))
            (hδ : ∀ j, (degeneracyLegsBar M s q' hle j).toRingHom.IsIntegral),
            P₁.IsGoodDiv (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar ((M * s) * q'))) ∧
              P₁.glueData (nodePairsOfPlaces (arithFrobC q' (ResidueField A) (M * s)) W₁) D
                  ∈ GluingData.admissible (nodePairsOfPlaces (arithFrobC q' (ResidueField A) (M * s)) W₁) ∧
                Pic0.mk D = (x : JZero ((M * s) * q')) ∧
                  P₂.IsGoodDiv (Divisor.pushforwardAlong (degeneracyLegsBar M s q' hle i) (hδ i)
                    (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar ((M * s) * q')))) ∧
                    P₂.glueData (nodePairsOfPlaces (arithFrobC q' (ResidueField A) M) W₂)
                        (Divisor.pushforwardAlong (degeneracyLegsBar M s q' hle i) (hδ i)
                          (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar ((M * s) * q')))) =
                      GluingData.pushforwardMap (nodePairsOfPlaces (arithFrobC q' (ResidueField A) (M * s)) W₁)
                        (nodePairsOfPlaces (arithFrobC q' (ResidueField A) M) W₂)
                        (NodePairTransport.pairMap _ _ hW₁ hW₂ (ab i)) (NodePairTransport.pairMult _ hW₁ (m i)) (φ i)
                            (hφ i)
                        (P₁.glueData (nodePairsOfPlaces (arithFrobC q' (ResidueField A) (M * s)) W₁) D) := by
  intro _ _ _ _ W₁ hW₁ hstab₁ data₁ hKr₁ hα₁ hβ₁ P₁ R₁ hmodel₁ hO₁ e₁ he₁ hpin₁ comp₁ sp₁ hsurj₁ hker₁ hsp₁
    W₂ hW₂ hstab₂ data₂ hKr₂ hα₂ hβ₂ P₂ R₂ hmodel₂ hO₂ e₂ he₂ hpin₂ comp₂ sp₂ hsurj₂ hker₂ hsp₂
    ab m φ hφ hφα hφβ _ hadm i x z hz hgood hle
  haveI : NeZero q' := ⟨hq'.ne_zero⟩
  haveI : Fact q'.Prime := ⟨hq'⟩
  haveI : Fact s.Prime := ⟨hs⟩
  haveI : CharP (ResidueField A) q' := ValuationSubring.charP_residueField_of_liesOverPrime_def hq' hA
  letI := instDecidableEqResidueFieldSemistable A
  letI := instAlgebraResidueFieldModularFunctionFieldCSemistable A (M * s)
  letI := instAlgebraResidueFieldModularFunctionFieldCSemistable A M
  haveI : NeZero (M * s) := ⟨Nat.mul_ne_zero (NeZero.ne M) (NeZero.ne s)⟩
  have hq'Ms : ¬ q' ∣ M * s := fun h =>
    ((Nat.Prime.dvd_mul hq').mp h).elim hq'M fun h' => hsq' ((Nat.prime_dvd_prime_iff_eq hq' hs).mp h').symm

  have hcoll := loc_COLLFIN M s q' hq' A hA data₂ hKr₂ (φ i) (hφ i)

  obtain ⟨D, hgoodD, hadmD, hDx, havoid⟩ :=
      ModularCurve.PlaceSpecialization.exists_isGoodDiv_mem_admissible_mk_eq_reduce_notMem_nodePairsOfPlaces (M * s) q'
          hq' hq'Ms A hA data₁ hKr₁ hα₁ hβ₁ P₁ R₁ hmodel₁ hO₁
    W₁ hW₁ hcoll.toFinset (x : JZero ((M * s) * q')) hgood

  have hge : modularFunctionFieldBar (M * s * q') ≤ modularFunctionFieldBar (M * q' * s) :=
    le_of_eq (congrArg modularFunctionFieldBar (Nat.mul_right_comm M s q'))
  have hsurjι : Function.Surjective (IntermediateField.inclusion hle).toRingHom := fun y =>
    ⟨⟨(y : LaurentSeries (AlgebraicClosure ℚ)), hge y.2⟩, Subtype.ext rfl⟩
  obtain ⟨hαI, hβI, hfinα, hfinβ, hNα, hNβ⟩ := degeneracyPushforwardInputs_of_prime (M * q') s
  have hδ : ∀ j, (degeneracyLegsBar M s q' hle j).toRingHom.IsIntegral := by
    intro j
    fin_cases j
    · exact RingHom.IsIntegral.trans _ _ hαI (RingHom.isIntegral_of_surjective _ hsurjι)
    · exact RingHom.IsIntegral.trans _ _ hβI (RingHom.isIntegral_of_surjective _ hsurjι)
  have hδα := degeneracyLegsBar_coe_zero M s q' hle
  have hδβ := degeneracyLegsBar_coe_one M s q' hle

  obtain ⟨hgood₂, hglue⟩ := PlaceSpecialization.isGoodDiv_pushforwardAlong_and_glueData_eq_of_isModel
    M s q' hs hq' hsq' hq'M A hA data₁ hKr₁ hα₁ hβ₁ P₁ R₁ hmodel₁ hO₁
    data₂ hKr₂ hα₂ hβ₂ P₂ R₂ hmodel₂ hO₂
    (nodePairsOfPlaces (arithFrobC q' (ResidueField A) (M * s)) W₁) (nodePairsOfPlaces (arithFrobC q' (ResidueField A)
        M) W₂)
    (NodePairTransport.pairMap _ _ hW₁ hW₂ (ab i)) (NodePairTransport.pairMult _ hW₁ (m i))
    (degeneracyLegsBar M s q' hle) hδ hδα hδβ φ hφ hφα hφβ i D (fun W hW => by
      have h := havoid W hW
      simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq] at h
      exact h)
  exact ⟨D, hδ, hgoodD, hadmD, hDx, hgood₂, hglue⟩

private theorem goodTransport
    (M s q' : ℕ) [NeZero M] [NeZero s] (hs : s.Prime) (hq' : q'.Prime)
    (hsq' : s ≠ q') (hq'M : ¬ q' ∣ M) (hsM : ¬ s ∣ M)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q') :
    haveI : NeZero q' := ⟨hq'.ne_zero⟩
    haveI : Fact q'.Prime := ⟨hq'⟩
    haveI : CharP (ResidueField A) q' := ValuationSubring.charP_residueField_of_liesOverPrime_def hq' hA
    letI := heckeModuleBar ((M * s) * q')
    letI := heckeModuleBar (M * s)
    letI := heckeModuleBar (M * q')
    letI := heckeModuleBar M
    letI := instDecidableEqResidueFieldSemistable A
    letI := instAlgebraResidueFieldModularFunctionFieldCSemistable A (M * s)
    letI := instAlgebraResidueFieldModularFunctionFieldCSemistable A M
    ∀ [Fintype ↥(ssPlaces q' (M * s) (ResidueField A))]
      [Fintype ↥(ssPlaces q' M (ResidueField A))]
      [DecidableEq ↥(ssPlaces q' (M * s) (ResidueField A))]
      [DecidableEq ↥(ssPlaces q' M (ResidueField A))],
    ∀ (W₁ : Finset (Place (ResidueField A) (modularFunctionFieldC (ResidueField A) (M * s))))
      (hW₁ : ∀ w, w ∈ W₁ ↔ w ∈ ssPlaces q' (M * s) (ResidueField A))
      (hstab₁ : SemilinearAut.IsNodeStable
        (nodePairsOfPlaces (arithFrobC q' (ResidueField A) (M * s)) W₁) (arithFrobC q' (ResidueField A) (M * s)))
      (data₁ : ModularPolynomialData q') (hKr₁ : KroneckerCongruence q' data₁)
      (hα₁ : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) (M * s) q')
      (hβ₁ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) (M * s) q')
      (P₁ : PlaceSpecialization A q' (M * s) data₁ hKr₁ (ResidueField A) (IsLocalRing.residue A) hα₁ hβ₁)
      (R₁ : PlaceSpecialization.ProlongationTuple P₁) (hmodel₁ : R₁.IsModel) (hO₁ : R₁.OrderLawFixed)
      (e₁ : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) (M * s)) → ℕ)
      (he₁ : ∀ p ∈ W₁, 0 < e₁ p)
      (hpin₁ : ∀ w ∈ W₁, e₁ w = placeWidthChar q' (M * s) w)
      (comp₁ : ↥(inertiaInvariants A ((M * s) * q')) →+
        componentGroup (widthOfPlaces (arithFrobC q' (ResidueField A) (M * s)) W₁ e₁))
      (sp₁ : ↥(inertiaInvariants A ((M * s) * q')) →+
        GluedPic0 (ResidueField A) (modularFunctionFieldC (ResidueField A) (M * s))
          (nodePairsOfPlaces (arithFrobC q' (ResidueField A) (M * s)) W₁))
      (hsurj₁ : Function.Surjective comp₁)
      (hker₁ : ∀ x : ↥(inertiaInvariants A ((M * s) * q')),
        comp₁ x = 0 ↔ P₁.IsGoodClass (nodePairsOfPlaces (arithFrobC q' (ResidueField A) (M * s)) W₁) (x : JZero ((M *
            s) * q')))
      (hsp₁ : P₁.IsGluedSpecialization (nodePairsOfPlaces (arithFrobC q' (ResidueField A) (M * s)) W₁) sp₁),
    ∀ (W₂ : Finset (Place (ResidueField A) (modularFunctionFieldC (ResidueField A) (M))))
      (hW₂ : ∀ w, w ∈ W₂ ↔ w ∈ ssPlaces q' (M) (ResidueField A))
      (hstab₂ : SemilinearAut.IsNodeStable
        (nodePairsOfPlaces (arithFrobC q' (ResidueField A) (M)) W₂) (arithFrobC q' (ResidueField A) (M)))
      (data₂ : ModularPolynomialData q') (hKr₂ : KroneckerCongruence q' data₂)
      (hα₂ : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) (M) q')
      (hβ₂ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) (M) q')
      (P₂ : PlaceSpecialization A q' (M) data₂ hKr₂ (ResidueField A) (IsLocalRing.residue A) hα₂ hβ₂)
      (R₂ : PlaceSpecialization.ProlongationTuple P₂) (hmodel₂ : R₂.IsModel) (hO₂ : R₂.OrderLawFixed)
      (e₂ : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) (M)) → ℕ)
      (he₂ : ∀ p ∈ W₂, 0 < e₂ p)
      (hpin₂ : ∀ w ∈ W₂, e₂ w = placeWidthChar q' M w)
      (comp₂ : ↥(inertiaInvariants A ((M) * q')) →+
        componentGroup (widthOfPlaces (arithFrobC q' (ResidueField A) (M)) W₂ e₂))
      (sp₂ : ↥(inertiaInvariants A ((M) * q')) →+
        GluedPic0 (ResidueField A) (modularFunctionFieldC (ResidueField A) (M))
          (nodePairsOfPlaces (arithFrobC q' (ResidueField A) (M)) W₂))
      (hsurj₂ : Function.Surjective comp₂)
      (hker₂ : ∀ x : ↥(inertiaInvariants A ((M) * q')),
        comp₂ x = 0 ↔ P₂.IsGoodClass (nodePairsOfPlaces (arithFrobC q' (ResidueField A) (M)) W₂) (x : JZero ((M) *
            q')))
      (hsp₂ : P₂.IsGluedSpecialization (nodePairsOfPlaces (arithFrobC q' (ResidueField A) (M)) W₂) sp₂),
    ∀ (ab : Fin 2 → (↥(ssPlaces q' (M * s) (ResidueField A)) → ↥(ssPlaces q' M (ResidueField A))))
      (m : Fin 2 → ↥(ssPlaces q' (M * s) (ResidueField A)) → ℕ)
      (φ : Fin 2 → ((modularFunctionFieldC (ResidueField A) M) →ₐ[ResidueField A] (modularFunctionFieldC (ResidueField
          A) (M * s))))
      (hφ : ∀ i, (φ i).toRingHom.IsIntegral)
      (hφα : ∀ x, ((φ 0 x : ↥(modularFunctionFieldC (ResidueField A) (M * s))) : LaurentSeries (ResidueField A)) = x)
      (hφβ : ∀ x, ((φ 1 x : ↥(modularFunctionFieldC (ResidueField A) (M * s))) : LaurentSeries (ResidueField A)) =
        qExpand (ResidueField A) s x)
      [DecidableEq ↥(nodePairsOfPlaces (arithFrobC q' (ResidueField A) M) W₂)]
      (hadm : ∀ (i : Fin 2), ∀ x ∈ GluingData.admissible (nodePairsOfPlaces (arithFrobC q' (ResidueField A) (M * s))
          W₁),
        GluingData.pushforwardMap (nodePairsOfPlaces (arithFrobC q' (ResidueField A) (M * s)) W₁) (nodePairsOfPlaces
            (arithFrobC q' (ResidueField A) M) W₂)
          (NodePairTransport.pairMap _ _ hW₁ hW₂ (ab i)) (NodePairTransport.pairMult _ hW₁ (m i)) (φ i) (hφ i) x
            ∈ GluingData.admissible (nodePairsOfPlaces (arithFrobC q' (ResidueField A) M) W₂)),
    ∀ (i : Fin 2) (x : ↥(inertiaInvariants A ((M * s) * q'))) (z : JZero ((M * q') * s))
      (_ : Nat.mul_right_comm M s q' ▸ (x : JZero ((M * s) * q')) = z),
      P₁.IsGoodClass (nodePairsOfPlaces (arithFrobC q' (ResidueField A) (M * s)) W₁) (x : JZero ((M * s) * q')) →
        P₂.IsGoodClass (nodePairsOfPlaces (arithFrobC q' (ResidueField A) M) W₂) (degeneracyPushforwardPair (M * q') s
            i z) := by
  intro _ _ _ _ W₁ hW₁ hstab₁ data₁ hKr₁ hα₁ hβ₁ P₁ R₁ hmodel₁ hO₁ e₁ he₁ hpin₁ comp₁ sp₁ hsurj₁ hker₁ hsp₁
    W₂ hW₂ hstab₂ data₂ hKr₂ hα₂ hβ₂ P₂ R₂ hmodel₂ hO₂ e₂ he₂ hpin₂ comp₂ sp₂ hsurj₂ hker₂ hsp₂
    ab m φ hφ hφα hφβ _ hadm i x z hz hgood
  haveI : NeZero q' := ⟨hq'.ne_zero⟩
  haveI : Fact q'.Prime := ⟨hq'⟩
  haveI : Fact s.Prime := ⟨hs⟩
  haveI : CharP (ResidueField A) q' := ValuationSubring.charP_residueField_of_liesOverPrime_def hq' hA
  letI := instDecidableEqResidueFieldSemistable A
  letI := instAlgebraResidueFieldModularFunctionFieldCSemistable A (M * s)
  letI := instAlgebraResidueFieldModularFunctionFieldCSemistable A M
  haveI : NeZero (M * s) := ⟨Nat.mul_ne_zero (NeZero.ne M) (NeZero.ne s)⟩
  have hq'Ms : ¬ q' ∣ M * s := fun h =>
    ((Nat.Prime.dvd_mul hq').mp h).elim hq'M fun h' => hsq' ((Nat.prime_dvd_prime_iff_eq hq' hs).mp h').symm

  have hcoll := loc_COLLFIN M s q' hq' A hA data₂ hKr₂ (φ i) (hφ i)

  obtain ⟨D, hgoodD, hadmD, hDx, havoid⟩ :=
      ModularCurve.PlaceSpecialization.exists_isGoodDiv_mem_admissible_mk_eq_reduce_notMem_nodePairsOfPlaces (M * s) q'
          hq' hq'Ms A hA data₁ hKr₁ hα₁ hβ₁ P₁ R₁ hmodel₁ hO₁
    W₁ hW₁ hcoll.toFinset (x : JZero ((M * s) * q')) hgood

  have hle : modularFunctionFieldBar (M * q' * s) ≤ modularFunctionFieldBar (M * s * q') :=
    le_of_eq (congrArg modularFunctionFieldBar (Nat.mul_right_comm M q' s))
  have hge : modularFunctionFieldBar (M * s * q') ≤ modularFunctionFieldBar (M * q' * s) :=
    le_of_eq (congrArg modularFunctionFieldBar (Nat.mul_right_comm M s q'))
  have hsurjι : Function.Surjective (IntermediateField.inclusion hle).toRingHom := fun y =>
    ⟨⟨(y : LaurentSeries (AlgebraicClosure ℚ)), hge y.2⟩, Subtype.ext rfl⟩
  obtain ⟨hαI, hβI, hfinα, hfinβ, hNα, hNβ⟩ := degeneracyPushforwardInputs_of_prime (M * q') s
  have hδ : ∀ j, (degeneracyLegsBar M s q' hle j).toRingHom.IsIntegral := by
    intro j
    fin_cases j
    · exact RingHom.IsIntegral.trans _ _ hαI (RingHom.isIntegral_of_surjective _ hsurjι)
    · exact RingHom.IsIntegral.trans _ _ hβI (RingHom.isIntegral_of_surjective _ hsurjι)
  have hδα := degeneracyLegsBar_coe_zero M s q' hle
  have hδβ := degeneracyLegsBar_coe_one M s q' hle

  obtain ⟨hgood₂, hglue⟩ := PlaceSpecialization.isGoodDiv_pushforwardAlong_and_glueData_eq_of_isModel
    M s q' hs hq' hsq' hq'M A hA data₁ hKr₁ hα₁ hβ₁ P₁ R₁ hmodel₁ hO₁
    data₂ hKr₂ hα₂ hβ₂ P₂ R₂ hmodel₂ hO₂
    (nodePairsOfPlaces (arithFrobC q' (ResidueField A) (M * s)) W₁) (nodePairsOfPlaces (arithFrobC q' (ResidueField A)
        M) W₂)
    (NodePairTransport.pairMap _ _ hW₁ hW₂ (ab i)) (NodePairTransport.pairMult _ hW₁ (m i))
    (degeneracyLegsBar M s q' hle) hδ hδα hδβ φ hφ hφα hφβ i D (fun W hW => by
      have h := havoid W hW
      simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq] at h
      exact h)

  refine ⟨⟨Divisor.pushforwardAlong (degeneracyLegsBar M s q' hle i) (hδ i)
      (D : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (M * s * q'))),
    Divisor.pushforwardAlong_mem_degZero _ _ D.2⟩, hgood₂, ?_,
    classTransport M s q' hle hαI hβI hfinα hNα hfinβ hNβ hδ i D _ z hz hDx⟩
  show P₂.glueData (nodePairsOfPlaces (arithFrobC q' (ResidueField A) M) W₂)
      (Divisor.pushforwardAlong (degeneracyLegsBar M s q' hle i) (hδ i)
        (D : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (M * s * q')))) ∈ _
  rw [hglue]
  exact hadm i _ hadmD

set_option maxHeartbeats 6400000 in

private theorem specCompat
    (M s q' : ℕ) [NeZero M] [NeZero s] (hs : s.Prime) (hq' : q'.Prime)
    (hsq' : s ≠ q') (hq'M : ¬ q' ∣ M) (hsM : ¬ s ∣ M)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q') :
    haveI : NeZero q' := ⟨hq'.ne_zero⟩
    haveI : Fact q'.Prime := ⟨hq'⟩
    haveI : CharP (ResidueField A) q' := ValuationSubring.charP_residueField_of_liesOverPrime_def hq' hA
    letI := heckeModuleBar ((M * s) * q')
    letI := heckeModuleBar (M * s)
    letI := heckeModuleBar (M * q')
    letI := heckeModuleBar M
    letI := instDecidableEqResidueFieldSemistable A
    letI := instAlgebraResidueFieldModularFunctionFieldCSemistable A (M * s)
    letI := instAlgebraResidueFieldModularFunctionFieldCSemistable A M
    ∀ [Fintype ↥(ssPlaces q' (M * s) (ResidueField A))]
      [Fintype ↥(ssPlaces q' M (ResidueField A))]
      [DecidableEq ↥(ssPlaces q' (M * s) (ResidueField A))]
      [DecidableEq ↥(ssPlaces q' M (ResidueField A))],
    ∀ (W₁ : Finset (Place (ResidueField A) (modularFunctionFieldC (ResidueField A) (M * s))))
      (hW₁ : ∀ w, w ∈ W₁ ↔ w ∈ ssPlaces q' (M * s) (ResidueField A))
      (hstab₁ : SemilinearAut.IsNodeStable
        (nodePairsOfPlaces (arithFrobC q' (ResidueField A) (M * s)) W₁) (arithFrobC q' (ResidueField A) (M * s)))
      (data₁ : ModularPolynomialData q') (hKr₁ : KroneckerCongruence q' data₁)
      (hα₁ : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) (M * s) q')
      (hβ₁ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) (M * s) q')
      (P₁ : PlaceSpecialization A q' (M * s) data₁ hKr₁ (ResidueField A) (IsLocalRing.residue A) hα₁ hβ₁)
      (R₁ : PlaceSpecialization.ProlongationTuple P₁) (hmodel₁ : R₁.IsModel) (hO₁ : R₁.OrderLawFixed)
      (e₁ : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) (M * s)) → ℕ)
      (he₁ : ∀ p ∈ W₁, 0 < e₁ p)
      (hpin₁ : ∀ w ∈ W₁, e₁ w = placeWidthChar q' (M * s) w)
      (comp₁ : ↥(inertiaInvariants A ((M * s) * q')) →+
        componentGroup (widthOfPlaces (arithFrobC q' (ResidueField A) (M * s)) W₁ e₁))
      (sp₁ : ↥(inertiaInvariants A ((M * s) * q')) →+
        GluedPic0 (ResidueField A) (modularFunctionFieldC (ResidueField A) (M * s))
          (nodePairsOfPlaces (arithFrobC q' (ResidueField A) (M * s)) W₁))
      (hsurj₁ : Function.Surjective comp₁)
      (hker₁ : ∀ x : ↥(inertiaInvariants A ((M * s) * q')),
        comp₁ x = 0 ↔ P₁.IsGoodClass (nodePairsOfPlaces (arithFrobC q' (ResidueField A) (M * s)) W₁) (x : JZero ((M *
            s) * q')))
      (hsp₁ : P₁.IsGluedSpecialization (nodePairsOfPlaces (arithFrobC q' (ResidueField A) (M * s)) W₁) sp₁),
    ∀ (W₂ : Finset (Place (ResidueField A) (modularFunctionFieldC (ResidueField A) (M))))
      (hW₂ : ∀ w, w ∈ W₂ ↔ w ∈ ssPlaces q' (M) (ResidueField A))
      (hstab₂ : SemilinearAut.IsNodeStable
        (nodePairsOfPlaces (arithFrobC q' (ResidueField A) (M)) W₂) (arithFrobC q' (ResidueField A) (M)))
      (data₂ : ModularPolynomialData q') (hKr₂ : KroneckerCongruence q' data₂)
      (hα₂ : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) (M) q')
      (hβ₂ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) (M) q')
      (P₂ : PlaceSpecialization A q' (M) data₂ hKr₂ (ResidueField A) (IsLocalRing.residue A) hα₂ hβ₂)
      (R₂ : PlaceSpecialization.ProlongationTuple P₂) (hmodel₂ : R₂.IsModel) (hO₂ : R₂.OrderLawFixed)
      (e₂ : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) (M)) → ℕ)
      (he₂ : ∀ p ∈ W₂, 0 < e₂ p)
      (hpin₂ : ∀ w ∈ W₂, e₂ w = placeWidthChar q' M w)
      (comp₂ : ↥(inertiaInvariants A ((M) * q')) →+
        componentGroup (widthOfPlaces (arithFrobC q' (ResidueField A) (M)) W₂ e₂))
      (sp₂ : ↥(inertiaInvariants A ((M) * q')) →+
        GluedPic0 (ResidueField A) (modularFunctionFieldC (ResidueField A) (M))
          (nodePairsOfPlaces (arithFrobC q' (ResidueField A) (M)) W₂))
      (hsurj₂ : Function.Surjective comp₂)
      (hker₂ : ∀ x : ↥(inertiaInvariants A ((M) * q')),
        comp₂ x = 0 ↔ P₂.IsGoodClass (nodePairsOfPlaces (arithFrobC q' (ResidueField A) (M)) W₂) (x : JZero ((M) *
            q')))
      (hsp₂ : P₂.IsGluedSpecialization (nodePairsOfPlaces (arithFrobC q' (ResidueField A) (M)) W₂) sp₂),
    ∀ (ab : Fin 2 → (↥(ssPlaces q' (M * s) (ResidueField A)) → ↥(ssPlaces q' M (ResidueField A))))
      (m : Fin 2 → ↥(ssPlaces q' (M * s) (ResidueField A)) → ℕ)
      (φ : Fin 2 → ((modularFunctionFieldC (ResidueField A) M) →ₐ[ResidueField A] (modularFunctionFieldC (ResidueField
          A) (M * s))))
      (hφ : ∀ i, (φ i).toRingHom.IsIntegral)
      (hφα : ∀ x, ((φ 0 x : ↥(modularFunctionFieldC (ResidueField A) (M * s))) : LaurentSeries (ResidueField A)) = x)
      (hφβ : ∀ x, ((φ 1 x : ↥(modularFunctionFieldC (ResidueField A) (M * s))) : LaurentSeries (ResidueField A)) =
        qExpand (ResidueField A) s x)
      [DecidableEq ↥(nodePairsOfPlaces (arithFrobC q' (ResidueField A) M) W₂)]
      (hadm : ∀ (i : Fin 2), ∀ x ∈ GluingData.admissible (nodePairsOfPlaces (arithFrobC q' (ResidueField A) (M * s))
          W₁),
        GluingData.pushforwardMap (nodePairsOfPlaces (arithFrobC q' (ResidueField A) (M * s)) W₁) (nodePairsOfPlaces
            (arithFrobC q' (ResidueField A) M) W₂)
          (NodePairTransport.pairMap _ _ hW₁ hW₂ (ab i)) (NodePairTransport.pairMult _ hW₁ (m i)) (φ i) (hφ i) x
            ∈ GluingData.admissible (nodePairsOfPlaces (arithFrobC q' (ResidueField A) M) W₂))
      (hprin : ∀ (i : Fin 2), ∀ x : GluingData (ResidueField A) (modularFunctionFieldC (ResidueField A) (M * s))
          (nodePairsOfPlaces (arithFrobC q' (ResidueField A) (M * s)) W₁),
        GluingData.IsGluedPrincipal (nodePairsOfPlaces (arithFrobC q' (ResidueField A) (M * s)) W₁) x →
          GluingData.IsGluedPrincipal (nodePairsOfPlaces (arithFrobC q' (ResidueField A) M) W₂)
            (GluingData.pushforwardMap (nodePairsOfPlaces (arithFrobC q' (ResidueField A) (M * s)) W₁)
                (nodePairsOfPlaces (arithFrobC q' (ResidueField A) M) W₂)
              (NodePairTransport.pairMap _ _ hW₁ hW₂ (ab i)) (NodePairTransport.pairMult _ hW₁ (m i)) (φ i) (hφ i) x))
      (i : Fin 2) (x : ↥(inertiaInvariants A ((M * s) * q'))) (z : JZero ((M * q') * s))
      (_ : Nat.mul_right_comm M s q' ▸ (x : JZero ((M * s) * q')) = z)
      (hx : degeneracyPushforwardPair (M * q') s i z ∈ inertiaInvariants A (M * q')),
      P₁.IsGoodClass (nodePairsOfPlaces (arithFrobC q' (ResidueField A) (M * s)) W₁) (x : JZero ((M * s) * q')) →
        sp₂ ⟨degeneracyPushforwardPair (M * q') s i z, hx⟩ =
          GluedPic0.pushforwardMap (nodePairsOfPlaces (arithFrobC q' (ResidueField A) (M * s)) W₁) (nodePairsOfPlaces
              (arithFrobC q' (ResidueField A) M) W₂)
            (NodePairTransport.pairMap _ _ hW₁ hW₂ (ab i)) (NodePairTransport.pairMult _ hW₁ (m i))
            (φ i) (hφ i) (hadm i) (hprin i) (sp₁ x) := by
  intro _ _ _ _ W₁ hW₁ hstab₁ data₁ hKr₁ hα₁ hβ₁ P₁ R₁ hmodel₁ hO₁ e₁ he₁ hpin₁ comp₁ sp₁ hsurj₁ hker₁ hsp₁
    W₂ hW₂ hstab₂ data₂ hKr₂ hα₂ hβ₂ P₂ R₂ hmodel₂ hO₂ e₂ he₂ hpin₂ comp₂ sp₂ hsurj₂ hker₂ hsp₂
    ab m φ hφ hφα hφβ _ hadm hprin i x z hz hx hgood
  haveI : NeZero q' := ⟨hq'.ne_zero⟩
  haveI : Fact q'.Prime := ⟨hq'⟩
  haveI : Fact s.Prime := ⟨hs⟩
  haveI : CharP (ResidueField A) q' := ValuationSubring.charP_residueField_of_liesOverPrime_def hq' hA
  letI := instDecidableEqResidueFieldSemistable A
  letI := instAlgebraResidueFieldModularFunctionFieldCSemistable A (M * s)
  letI := instAlgebraResidueFieldModularFunctionFieldCSemistable A M
  haveI : NeZero (M * s) := ⟨Nat.mul_ne_zero (NeZero.ne M) (NeZero.ne s)⟩
  have hle : modularFunctionFieldBar (M * q' * s) ≤ modularFunctionFieldBar (M * s * q') :=
    le_of_eq (congrArg modularFunctionFieldBar (Nat.mul_right_comm M q' s))
  obtain ⟨hαI, hβI, hfinα, hfinβ, hNα, hNβ⟩ := degeneracyPushforwardInputs_of_prime (M * q') s
  have hpkg := goodRep_package M s q' hs hq' hsq' hq'M hsM A hA
    W₁ hW₁ hstab₁ data₁ hKr₁ hα₁ hβ₁ P₁ R₁ hmodel₁ hO₁ e₁ he₁ hpin₁ comp₁ sp₁ hsurj₁ hker₁ hsp₁ W₂
    hW₂ hstab₂ data₂ hKr₂ hα₂ hβ₂ P₂ R₂ hmodel₂ hO₂ e₂ he₂ hpin₂ comp₂ sp₂ hsurj₂ hker₂ hsp₂ ab m φ
    hφ hφα hφβ hadm i x z hz hgood hle
  obtain ⟨D, hδ, hgoodD, hadmD, hDx, hgood₂, hglue⟩ := hpkg

  have hmk₂ := (classTransport M s q' hle hαI hβI hfinα hNα hfinβ hNβ hδ i D _ z hz hDx).symm

  have hH₁ : Pic0.mk D ∈ inertiaInvariants A ((M * s) * q') :=
    (congrArg (fun y => y ∈ inertiaInvariants A ((M * s) * q')) hDx).mpr x.2
  have hsp1x : sp₁ x = GluedPic0.mk (nodePairsOfPlaces (arithFrobC q' (ResidueField A) (M * s)) W₁)
      ⟨P₁.glueData (nodePairsOfPlaces (arithFrobC q' (ResidueField A) (M * s)) W₁) (D : Divisor (AlgebraicClosure ℚ)
          ↥(modularFunctionFieldBar (M * s * q'))), hadmD⟩ := by
    have h := hsp₁ D hH₁
      ⟨P₁.glueData (nodePairsOfPlaces (arithFrobC q' (ResidueField A) (M * s)) W₁) (D : Divisor (AlgebraicClosure ℚ)
          ↥(modularFunctionFieldBar (M * s * q'))), hadmD⟩ hgoodD rfl
    have hxe : (⟨Pic0.mk D, hH₁⟩ : ↥(inertiaInvariants A ((M * s) * q'))) = x := Subtype.ext hDx
    exact (congrArg sp₁ hxe).symm.trans h

  have hadm₂mem : P₂.glueData (nodePairsOfPlaces (arithFrobC q' (ResidueField A) M) W₂)
      (Divisor.pushforwardAlong (degeneracyLegsBar M s q' hle i) (hδ i)
        (D : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (M * s * q'))))
        ∈ GluingData.admissible (nodePairsOfPlaces (arithFrobC q' (ResidueField A) M) W₂) := by
    exact (congrArg (fun g => g ∈ GluingData.admissible (nodePairsOfPlaces (arithFrobC q' (ResidueField A) M) W₂))
        hglue).mpr
      (hadm i _ hadmD)

  have hH₂ := hmk₂ ▸ hx
  have hsp2D := hsp₂ ⟨Divisor.pushforwardAlong (degeneracyLegsBar M s q' hle i) (hδ i)
        (D : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (M * s * q'))),
      Divisor.pushforwardAlong_mem_degZero _ _ D.2⟩ hH₂
    ⟨P₂.glueData (nodePairsOfPlaces (arithFrobC q' (ResidueField A) M) W₂)
      (Divisor.pushforwardAlong (degeneracyLegsBar M s q' hle i) (hδ i)
        (D : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (M * s * q')))), hadm₂mem⟩
    hgood₂ rfl

  have h3 := congrArg (GluedPic0.mk (nodePairsOfPlaces (arithFrobC q' (ResidueField A) M) W₂))
    (Subtype.ext
      (a1 := ⟨P₂.glueData (nodePairsOfPlaces (arithFrobC q' (ResidueField A) M) W₂)
        (Divisor.pushforwardAlong (degeneracyLegsBar M s q' hle i) (hδ i)
          (D : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (M * s * q')))), hadm₂mem⟩)
      (hglue.trans (GluedPic0.coe_admissiblePushforwardMap _ _
      (NodePairTransport.pairMap _ _ hW₁ hW₂ (ab i)) (NodePairTransport.pairMult _ hW₁ (m i)) (φ i) (hφ i) (hadm i)
      ⟨P₁.glueData (nodePairsOfPlaces (arithFrobC q' (ResidueField A) (M * s)) W₁) (D : Divisor (AlgebraicClosure ℚ)
          ↥(modularFunctionFieldBar (M * s * q'))), hadmD⟩).symm))
  have h4 := (GluedPic0.pushforwardMap_mk _ _
      (NodePairTransport.pairMap _ _ hW₁ hW₂ (ab i)) (NodePairTransport.pairMult _ hW₁ (m i)) (φ i) (hφ i)
      (hadm i) (hprin i)
      ⟨P₁.glueData (nodePairsOfPlaces (arithFrobC q' (ResidueField A) (M * s)) W₁) (D : Divisor (AlgebraicClosure ℚ)
          ↥(modularFunctionFieldBar (M * s * q'))), hadmD⟩).symm
  have hxe₂ : (⟨degeneracyPushforwardPair (M * q') s i z, hx⟩ : ↥(inertiaInvariants A (M * q'))) = ⟨_, hH₂⟩ :=
    Subtype.ext hmk₂
  have h5 := congrArg (GluedPic0.pushforwardMap (nodePairsOfPlaces (arithFrobC q' (ResidueField A) (M * s)) W₁)
      (nodePairsOfPlaces (arithFrobC q' (ResidueField A) M) W₂)
    (NodePairTransport.pairMap _ _ hW₁ hW₂ (ab i)) (NodePairTransport.pairMult _ hW₁ (m i))
    (φ i) (hφ i) (hadm i) (hprin i)) hsp1x
  exact (congrArg sp₂ hxe₂).trans (hsp2D.trans (h3.trans (h4.trans h5.symm)))

private theorem admTransport
    (M s q' : ℕ) [NeZero M] [NeZero s] (hs : s.Prime) (hq' : q'.Prime)
    (hsq' : s ≠ q') (hq'M : ¬ q' ∣ M) (hsM : ¬ s ∣ M)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q') :
    haveI : NeZero q' := ⟨hq'.ne_zero⟩
    haveI : Fact q'.Prime := ⟨hq'⟩
    haveI : CharP (ResidueField A) q' := ValuationSubring.charP_residueField_of_liesOverPrime_def hq' hA
    letI := instDecidableEqResidueFieldSemistable A
    letI := instAlgebraResidueFieldModularFunctionFieldCSemistable A (M * s)
    letI := instAlgebraResidueFieldModularFunctionFieldCSemistable A M
    haveI : NeZero (M * s) := ⟨Nat.mul_ne_zero (NeZero.ne M) (NeZero.ne s)⟩
    ∀ [Fintype ↥(ssPlaces q' (M * s) (ResidueField A))] [Fintype ↥(ssPlaces q' M (ResidueField A))]
      [DecidableEq ↥(ssPlaces q' (M * s) (ResidueField A))] [DecidableEq ↥(ssPlaces q' M (ResidueField A))],
    ∀ (W₁ : Finset (Place (ResidueField A) (modularFunctionFieldC (ResidueField A) (M * s))))
      (hW₁ : ∀ w, w ∈ W₁ ↔ w ∈ ssPlaces q' (M * s) (ResidueField A))
      (hstab₁ : SemilinearAut.IsNodeStable
        (nodePairsOfPlaces (arithFrobC q' (ResidueField A) (M * s)) W₁) (arithFrobC q' (ResidueField A) (M * s)))
      (W₂ : Finset (Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M)))
      (hW₂ : ∀ w, w ∈ W₂ ↔ w ∈ ssPlaces q' M (ResidueField A))
      (hstab₂ : SemilinearAut.IsNodeStable
        (nodePairsOfPlaces (arithFrobC q' (ResidueField A) M) W₂) (arithFrobC q' (ResidueField A) M))
      (φ : Fin 2 → ((modularFunctionFieldC (ResidueField A) M) →ₐ[ResidueField A]
        (modularFunctionFieldC (ResidueField A) (M * s))))
      (hφ : ∀ i, (φ i).toRingHom.IsIntegral)
      (hφα : ∀ x, ((φ 0 x : ↥(modularFunctionFieldC (ResidueField A) (M * s))) :
        LaurentSeries (ResidueField A)) = x)
      (hφβ : ∀ x, ((φ 1 x : ↥(modularFunctionFieldC (ResidueField A) (M * s))) :
        LaurentSeries (ResidueField A)) = qExpand (ResidueField A) s x)
      [DecidableEq ↥(nodePairsOfPlaces (arithFrobC q' (ResidueField A) M) W₂)]
      (ab : Fin 2 → (↥(ssPlaces q' (M * s) (ResidueField A)) → ↥(ssPlaces q' M (ResidueField A))))
      (m : Fin 2 → ↥(ssPlaces q' (M * s) (ResidueField A)) → ℕ)
      (hab : ∀ i p, (ab i p : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M)) =
        Place.restrictAlong (φ i) (hφ i) ↑p)
      (hm : ∀ i p, m i p = Place.ramificationIndexAlong (φ i)
        (p : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) (M * s)))),
    ∀ (i : Fin 2), ∀ x ∈ GluingData.admissible (nodePairsOfPlaces (arithFrobC q' (ResidueField A) (M * s)) W₁),
      GluingData.pushforwardMap (nodePairsOfPlaces (arithFrobC q' (ResidueField A) (M * s)) W₁) (nodePairsOfPlaces
          (arithFrobC q' (ResidueField A) M) W₂)
        (NodePairTransport.pairMap _ _ hW₁ hW₂ (ab i)) (NodePairTransport.pairMult _ hW₁ (m i)) (φ i) (hφ i) x
          ∈ GluingData.admissible (nodePairsOfPlaces (arithFrobC q' (ResidueField A) M) W₂) := by
  intro _ _ _ _ W₁ hW₁ hstab₁ W₂ hW₂ hstab₂ φ hφ hφα hφβ _ ab m hab hm
  haveI : NeZero q' := ⟨hq'.ne_zero⟩
  haveI : Fact q'.Prime := ⟨hq'⟩
  haveI : CharP (ResidueField A) q' := ValuationSubring.charP_residueField_of_liesOverPrime_def hq' hA
  letI := instDecidableEqResidueFieldSemistable A
  letI := instAlgebraResidueFieldModularFunctionFieldCSemistable A (M * s)
  letI := instAlgebraResidueFieldModularFunctionFieldCSemistable A M
  haveI : NeZero (M * s) := ⟨Nat.mul_ne_zero (NeZero.ne M) (NeZero.ne s)⟩
  have hpack :=
    degeneracyPair_finiteSeparableDeg_ssPlaces_preserved_reflected M s q' hs hsq' hq'M hsM
      (k := ResidueField A) φ hφ hφα hφβ
  obtain ⟨hfinP, hsepP, hdegP, hpresP, hreflP⟩ := hpack
  intro i x hx
  refine GluingData.pushforwardMap_mem_admissible _ _ _ _ (φ i) (hφ i) ?_ ?_ hx
  ·
    intro n hn w hw
    obtain ⟨v, hv, hvn⟩ := (mem_nodePairsOfPlaces_iff _ W₂ _).mp hn
    have hn1 : n.1 ∈ W₂ := by rw [← hvn, smulNodePair_fst]; exact hv
    have hwss := hreflP i n.1 ((hW₂ _).mp hn1) w hw
    exact ⟨smulNodePair (arithFrobC q' (ResidueField A) (M * s)) w,
      smulNodePair_mem_nodePairsOfPlaces _ ((hW₁ w).mpr hwss), rfl⟩
  ·
    intro n hn w hw
    obtain ⟨v, hv, hvn⟩ := (mem_nodePairsOfPlaces_iff _ W₂ _).mp hn
    have hn2 : n.2 ∈ W₂ := by
      have h := fst_mem_of_mem_nodePairsOfPlaces (hstab₂ _ hn)
      rw [← hvn, smulNodePair_fst] at h
      rw [← hvn, smulNodePair_snd]
      exact h
    have hwss := hreflP i n.2 ((hW₂ _).mp hn2) w hw
    have hW₁stab : ∀ u ∈ W₁, arithFrobC q' (ResidueField A) (M * s) • u ∈ W₁ := fun u hu =>
      fst_mem_of_mem_nodePairsOfPlaces (hstab₁ _ (smulNodePair_mem_nodePairsOfPlaces _ hu))
    have hsurj := Finset.surjOn_of_injOn_of_card_le (s := W₁) (t := W₁)
      (fun u => arithFrobC q' (ResidueField A) (M * s) • u) (fun ⦃u⦄ hu => hW₁stab u hu)
      (MulAction.injective (arithFrobC q' (ResidueField A) (M * s))).injOn le_rfl
    obtain ⟨u, hu, huw⟩ := hsurj ((hW₁ w).mpr hwss)
    exact ⟨smulNodePair (arithFrobC q' (ResidueField A) (M * s)) u,
      smulNodePair_mem_nodePairsOfPlaces _ hu, huw⟩

private theorem prinTransport
    (M s q' : ℕ) [NeZero M] [NeZero s] (hs : s.Prime) (hq' : q'.Prime)
    (hsq' : s ≠ q') (hq'M : ¬ q' ∣ M) (hsM : ¬ s ∣ M)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q') :
    haveI : NeZero q' := ⟨hq'.ne_zero⟩
    haveI : Fact q'.Prime := ⟨hq'⟩
    haveI : CharP (ResidueField A) q' := ValuationSubring.charP_residueField_of_liesOverPrime_def hq' hA
    letI := instDecidableEqResidueFieldSemistable A
    letI := instAlgebraResidueFieldModularFunctionFieldCSemistable A (M * s)
    letI := instAlgebraResidueFieldModularFunctionFieldCSemistable A M
    haveI : NeZero (M * s) := ⟨Nat.mul_ne_zero (NeZero.ne M) (NeZero.ne s)⟩
    ∀ [Fintype ↥(ssPlaces q' (M * s) (ResidueField A))] [Fintype ↥(ssPlaces q' M (ResidueField A))]
      [DecidableEq ↥(ssPlaces q' (M * s) (ResidueField A))] [DecidableEq ↥(ssPlaces q' M (ResidueField A))],
    ∀ (W₁ : Finset (Place (ResidueField A) (modularFunctionFieldC (ResidueField A) (M * s))))
      (hW₁ : ∀ w, w ∈ W₁ ↔ w ∈ ssPlaces q' (M * s) (ResidueField A))
      (hstab₁ : SemilinearAut.IsNodeStable
        (nodePairsOfPlaces (arithFrobC q' (ResidueField A) (M * s)) W₁) (arithFrobC q' (ResidueField A) (M * s)))
      (W₂ : Finset (Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M)))
      (hW₂ : ∀ w, w ∈ W₂ ↔ w ∈ ssPlaces q' M (ResidueField A))
      (hstab₂ : SemilinearAut.IsNodeStable
        (nodePairsOfPlaces (arithFrobC q' (ResidueField A) M) W₂) (arithFrobC q' (ResidueField A) M))
      (φ : Fin 2 → ((modularFunctionFieldC (ResidueField A) M) →ₐ[ResidueField A]
        (modularFunctionFieldC (ResidueField A) (M * s))))
      (hφ : ∀ i, (φ i).toRingHom.IsIntegral)
      (hφα : ∀ x, ((φ 0 x : ↥(modularFunctionFieldC (ResidueField A) (M * s))) :
        LaurentSeries (ResidueField A)) = x)
      (hφβ : ∀ x, ((φ 1 x : ↥(modularFunctionFieldC (ResidueField A) (M * s))) :
        LaurentSeries (ResidueField A)) = qExpand (ResidueField A) s x)
      [DecidableEq ↥(nodePairsOfPlaces (arithFrobC q' (ResidueField A) M) W₂)]
      (ab : Fin 2 → (↥(ssPlaces q' (M * s) (ResidueField A)) → ↥(ssPlaces q' M (ResidueField A))))
      (m : Fin 2 → ↥(ssPlaces q' (M * s) (ResidueField A)) → ℕ)
      (hab : ∀ i p, (ab i p : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M)) =
        Place.restrictAlong (φ i) (hφ i) ↑p)
      (hm : ∀ i p, m i p = Place.ramificationIndexAlong (φ i)
        (p : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) (M * s)))),
    ∀ (i : Fin 2), ∀ x : GluingData (ResidueField A) (modularFunctionFieldC (ResidueField A) (M * s))
        (nodePairsOfPlaces (arithFrobC q' (ResidueField A) (M * s)) W₁),
      GluingData.IsGluedPrincipal (nodePairsOfPlaces (arithFrobC q' (ResidueField A) (M * s)) W₁) x →
        GluingData.IsGluedPrincipal (nodePairsOfPlaces (arithFrobC q' (ResidueField A) M) W₂)
          (GluingData.pushforwardMap (nodePairsOfPlaces (arithFrobC q' (ResidueField A) (M * s)) W₁) (nodePairsOfPlaces
              (arithFrobC q' (ResidueField A) M) W₂)
            (NodePairTransport.pairMap _ _ hW₁ hW₂ (ab i)) (NodePairTransport.pairMult _ hW₁ (m i)) (φ i) (hφ i) x) :=
                by
  intro _ _ _ _ W₁ hW₁ hstab₁ W₂ hW₂ hstab₂ φ hφ hφα hφβ _ ab m hab hm
  haveI : NeZero q' := ⟨hq'.ne_zero⟩
  haveI : Fact q'.Prime := ⟨hq'⟩
  haveI : CharP (ResidueField A) q' := ValuationSubring.charP_residueField_of_liesOverPrime_def hq' hA
  letI := instDecidableEqResidueFieldSemistable A
  letI := instAlgebraResidueFieldModularFunctionFieldCSemistable A (M * s)
  letI := instAlgebraResidueFieldModularFunctionFieldCSemistable A M
  haveI : NeZero (M * s) := ⟨Nat.mul_ne_zero (NeZero.ne M) (NeZero.ne s)⟩
  have hpack :=
    degeneracyPair_finiteSeparableDeg_ssPlaces_preserved_reflected M s q' hs hsq' hq'M hsM
      (k := ResidueField A) φ hφ hφα hφβ
  obtain ⟨hfinP, hsepP, hdegP, hpresP, hreflP⟩ := hpack
  intro i x hx
  haveI : HasPrincipalDivisors (ResidueField A) (modularFunctionFieldC (ResidueField A) (M * s)) :=
    hasPrincipalDivisors_modularFunctionFieldC_of_perfectField (ResidueField A) (M * s)
  have hcomm := loc_ARITHCOMM M s q' (k := ResidueField A) φ hφ hφα hφβ i
  have hram := loc_RAMFROB M s q' (k := ResidueField A) φ hφ hφα hφβ i
  have hW₁stab : ∀ u ∈ W₁, arithFrobC q' (ResidueField A) (M * s) • u ∈ W₁ := fun u hu =>
    fst_mem_of_mem_nodePairsOfPlaces (hstab₁ _ (smulNodePair_mem_nodePairsOfPlaces _ hu))
  have hsurj := Finset.surjOn_of_injOn_of_card_le (s := W₁) (t := W₁)
    (fun u => arithFrobC q' (ResidueField A) (M * s) • u) (fun ⦃u⦄ hu => hW₁stab u hu)
    (MulAction.injective (arithFrobC q' (ResidueField A) (M * s))).injOn le_rfl
  refine loc_BETA_SEP (φ i) (hφ i) (hfinP i) (hsepP i) _ _
    (NodePairTransport.pairMap _ _ hW₁ hW₂ (ab i)) ?_ ?_ ?_ (NodePairTransport.pairMult _ hW₁ (m i)) ?_ ?_ hx
  ·
    intro n'
    obtain ⟨w, -, hn'⟩ := (mem_nodePairsOfPlaces_iff _ W₁ _).mp n'.2
    have h2 : arithFrobC q' (ResidueField A) (M * s) • n'.1.1 = n'.1.2 := by
      simp only [← hn', smulNodePair_fst, smulNodePair_snd]
    refine ⟨hab i _, ?_⟩
    show arithFrobC q' (ResidueField A) M •
        ((ab i _ : ↥(ssPlaces q' M (ResidueField A))) :
          Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M)) = _
    rw [hab, ← h2, hcomm]
  ·
    intro n w hw
    obtain ⟨v, hv, hvn⟩ := (mem_nodePairsOfPlaces_iff _ W₂ _).mp n.2
    have hn1 : n.1.1 ∈ W₂ := by
      rw [← hvn, smulNodePair_fst]; exact hv
    have hwss := hreflP i _ ((hW₂ _).mp hn1) w hw
    refine ⟨⟨smulNodePair (arithFrobC q' (ResidueField A) (M * s)) w,
      smulNodePair_mem_nodePairsOfPlaces _ ((hW₁ w).mpr hwss)⟩, ⟨?_, rfl⟩, ?_⟩
    · apply Subtype.ext
      show smulNodePair (arithFrobC q' (ResidueField A) M)
          ((ab i _ : ↥(ssPlaces q' M (ResidueField A))) :
            Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M)) = _
      rw [hab]
      show smulNodePair (arithFrobC q' (ResidueField A) M) (Place.restrictAlong (φ i) (hφ i) w) = _
      rw [hw, ← hvn, smulNodePair_fst]
    · rintro n'' ⟨-, hn''⟩
      apply Subtype.ext
      obtain ⟨u, -, hun⟩ := (mem_nodePairsOfPlaces_iff _ W₁ _).mp n''.2
      rw [← hun] at hn'' ⊢
      rw [smulNodePair_fst] at hn''
      rw [hn'']
  ·
    intro n w hw
    obtain ⟨v, hv, hvn⟩ := (mem_nodePairsOfPlaces_iff _ W₂ _).mp n.2
    have hn2 : n.1.2 ∈ W₂ := by
      have h := fst_mem_of_mem_nodePairsOfPlaces (hstab₂ _ n.2)
      rw [← hvn, smulNodePair_fst] at h
      rw [← hvn, smulNodePair_snd]
      exact h
    have hwss := hreflP i _ ((hW₂ _).mp hn2) w hw
    obtain ⟨u, hu, huw⟩ := hsurj ((hW₁ w).mpr hwss)
    have huw : arithFrobC q' (ResidueField A) (M * s) • u = w := huw
    have hru : Place.restrictAlong (φ i) (hφ i) u = v := by
      apply MulAction.injective (arithFrobC q' (ResidueField A) M)
      show arithFrobC q' (ResidueField A) M • Place.restrictAlong (φ i) (hφ i) u =
        arithFrobC q' (ResidueField A) M • v
      rw [← hcomm, huw, hw, ← hvn, smulNodePair_snd]
    refine ⟨⟨smulNodePair (arithFrobC q' (ResidueField A) (M * s)) u,
      smulNodePair_mem_nodePairsOfPlaces _ hu⟩, ⟨?_, huw⟩, ?_⟩
    · apply Subtype.ext
      show smulNodePair (arithFrobC q' (ResidueField A) M)
          ((ab i _ : ↥(ssPlaces q' M (ResidueField A))) :
            Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M)) = _
      rw [hab]
      show smulNodePair (arithFrobC q' (ResidueField A) M) (Place.restrictAlong (φ i) (hφ i) u) = _
      rw [hru, ← hvn]
    · rintro n'' ⟨-, hn''⟩
      apply Subtype.ext
      obtain ⟨u'', -, hun⟩ := (mem_nodePairsOfPlaces_iff _ W₁ _).mp n''.2
      rw [← hun] at hn'' ⊢
      rw [smulNodePair_snd] at hn''
      have hu'' : u'' = u :=
        MulAction.injective (arithFrobC q' (ResidueField A) (M * s)) (hn''.trans huw.symm)
      rw [hu'']
  ·
    intro n'
    show m i _ = _
    rw [hm, loc_INERTIA1 (φ i) (hφ i) _ (place_deg_eq_one_of_isAlgClosed (ResidueField A) (M * s) _), mul_one]
  · intro n'
    obtain ⟨u, -, hun⟩ := (mem_nodePairsOfPlaces_iff _ W₁ _).mp n'.2
    have h2 : n'.1.2 = arithFrobC q' (ResidueField A) (M * s) • n'.1.1 := by
      simp only [← hun, smulNodePair_fst, smulNodePair_snd]
    show m i _ = _
    rw [hm, h2, hram, loc_INERTIA1 (φ i) (hφ i) _ (place_deg_eq_one_of_isAlgClosed (ResidueField A) (M * s) _),
        mul_one]

private theorem fibreSum_eq
    (M s q' : ℕ) [NeZero M] [NeZero s] (hs : s.Prime) (hq' : q'.Prime)
    (hsq' : s ≠ q') (hq'M : ¬ q' ∣ M) (hsM : ¬ s ∣ M)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q') :
    haveI : NeZero q' := ⟨hq'.ne_zero⟩
    haveI : Fact q'.Prime := ⟨hq'⟩
    haveI : CharP (ResidueField A) q' := ValuationSubring.charP_residueField_of_liesOverPrime_def hq' hA
    letI := instDecidableEqResidueFieldSemistable A
    letI := instAlgebraResidueFieldModularFunctionFieldCSemistable A (M * s)
    letI := instAlgebraResidueFieldModularFunctionFieldCSemistable A M
    haveI : NeZero (M * s) := ⟨Nat.mul_ne_zero (NeZero.ne M) (NeZero.ne s)⟩
    ∀ [Fintype ↥(ssPlaces q' (M * s) (ResidueField A))] [Fintype ↥(ssPlaces q' M (ResidueField A))]
      [DecidableEq ↥(ssPlaces q' (M * s) (ResidueField A))] [DecidableEq ↥(ssPlaces q' M (ResidueField A))],
    ∀ (W₁ : Finset (Place (ResidueField A) (modularFunctionFieldC (ResidueField A) (M * s))))
      (hW₁ : ∀ w, w ∈ W₁ ↔ w ∈ ssPlaces q' (M * s) (ResidueField A))
      (hstab₁ : SemilinearAut.IsNodeStable
        (nodePairsOfPlaces (arithFrobC q' (ResidueField A) (M * s)) W₁) (arithFrobC q' (ResidueField A) (M * s)))
      (W₂ : Finset (Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M)))
      (hW₂ : ∀ w, w ∈ W₂ ↔ w ∈ ssPlaces q' M (ResidueField A))
      (hstab₂ : SemilinearAut.IsNodeStable
        (nodePairsOfPlaces (arithFrobC q' (ResidueField A) M) W₂) (arithFrobC q' (ResidueField A) M))
      (φ : Fin 2 → ((modularFunctionFieldC (ResidueField A) M) →ₐ[ResidueField A]
        (modularFunctionFieldC (ResidueField A) (M * s))))
      (hφ : ∀ i, (φ i).toRingHom.IsIntegral)
      (hφα : ∀ x, ((φ 0 x : ↥(modularFunctionFieldC (ResidueField A) (M * s))) :
        LaurentSeries (ResidueField A)) = x)
      (hφβ : ∀ x, ((φ 1 x : ↥(modularFunctionFieldC (ResidueField A) (M * s))) :
        LaurentSeries (ResidueField A)) = qExpand (ResidueField A) s x)
      [DecidableEq ↥(nodePairsOfPlaces (arithFrobC q' (ResidueField A) M) W₂)]
      (ab : Fin 2 → (↥(ssPlaces q' (M * s) (ResidueField A)) → ↥(ssPlaces q' M (ResidueField A))))
      (m : Fin 2 → ↥(ssPlaces q' (M * s) (ResidueField A)) → ℕ)
      (hab : ∀ i p, (ab i p : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M)) =
        Place.restrictAlong (φ i) (hφ i) ↑p)
      (hm : ∀ i p, m i p = Place.ramificationIndexAlong (φ i)
        (p : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) (M * s)))),
    ∀ (i : Fin 2) (v : ↥(ssPlaces q' M (ResidueField A))), (∑ p with ab i p = v, m i p) = s + 1 := by
  intro _ _ _ _ W₁ hW₁ hstab₁ W₂ hW₂ hstab₂ φ hφ hφα hφβ _ ab m hab hm
  haveI : NeZero q' := ⟨hq'.ne_zero⟩
  haveI : Fact q'.Prime := ⟨hq'⟩
  haveI : CharP (ResidueField A) q' := ValuationSubring.charP_residueField_of_liesOverPrime_def hq' hA
  letI := instDecidableEqResidueFieldSemistable A
  letI := instAlgebraResidueFieldModularFunctionFieldCSemistable A (M * s)
  letI := instAlgebraResidueFieldModularFunctionFieldCSemistable A M
  haveI : NeZero (M * s) := ⟨Nat.mul_ne_zero (NeZero.ne M) (NeZero.ne s)⟩
  have hpack :=
    degeneracyPair_finiteSeparableDeg_ssPlaces_preserved_reflected M s q' hs hsq' hq'M hsM
      (k := ResidueField A) φ hφ hφα hφβ
  obtain ⟨hfinP, hsepP, hdegP, hpresP, hreflP⟩ := hpack
  intro i v
  haveI : HasPrincipalDivisors (ResidueField A) (modularFunctionFieldC (ResidueField A) (M * s)) :=
    hasPrincipalDivisors_modularFunctionFieldC_of_perfectField (ResidueField A) (M * s)

  have key : (∑ p with ab i p = v, m i p) =
      ∑ w ∈ Place.fiberAlong (φ i) (hφ i) (v : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M)),
        Place.ramificationIndexAlong (φ i) w := by
    refine Finset.sum_bij (fun p _ => (p : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) (M * s))))
      ?_ ?_ ?_ ?_
    · intro p hp
      beta_reduce
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
      rw [Place.mem_fiberAlong, ← hab, hp]
    · intro p₁ _ p₂ _ h
      exact Subtype.ext h
    · intro w hw
      rw [Place.mem_fiberAlong] at hw
      refine ⟨⟨w, hreflP i _ v.2 w hw⟩, ?_, rfl⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact Subtype.ext ((hab i _).trans hw)
    · intro p _
      exact hm i p
  rw [key]

  have hFI := fundamentalIdentityAlong (φ i) (hφ i) (hfinP i) (hsepP i)
  have hsum : ∑ w ∈ Place.fiberAlong (φ i) (hφ i) (v : Place (ResidueField A) (modularFunctionFieldC (ResidueField A)
      M)),
      ((Place.ramificationIndexAlong (φ i) w : ℤ) * (w.deg : ℤ)) =
        (finrankAlong (ResidueField A) (φ i) : ℤ) *
          ((v : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M)).deg : ℤ) := by
    letI := algebraAlong (φ i)
    haveI := isScalarTower_along (φ i)
    haveI := isIntegral_along (φ i) (hφ i)
    haveI : FundamentalIdentity (ResidueField A) (modularFunctionFieldC (ResidueField A) M)
        (modularFunctionFieldC (ResidueField A) (M * s)) := hFI
    exact FundamentalIdentity.sum_ramificationIndex_mul_deg _
  simp only [place_deg_eq_one_of_isAlgClosed, Nat.cast_one, mul_one, hdegP i] at hsum
  exact_mod_cast hsum

theorem solution
    (M s q' : ℕ) [NeZero M] [NeZero s] (hs : s.Prime) (hq' : q'.Prime)
    (hsq' : s ≠ q') (hq'M : ¬ q' ∣ M) (hsM : ¬ s ∣ M)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q') :
    haveI : NeZero q' := ⟨hq'.ne_zero⟩
    haveI : Fact q'.Prime := ⟨hq'⟩
    haveI : CharP (ResidueField A) q' := ValuationSubring.charP_residueField_of_liesOverPrime_def hq' hA
    letI := heckeModuleBar ((M * s) * q')
    letI := heckeModuleBar (M * s)
    letI := heckeModuleBar (M * q')
    letI := heckeModuleBar M
    letI := instDecidableEqResidueFieldSemistable A
    letI := instAlgebraResidueFieldModularFunctionFieldCSemistable A (M * s)
    letI := instAlgebraResidueFieldModularFunctionFieldCSemistable A M
    ∀ [Fintype ↥(ssPlaces q' (M * s) (ResidueField A))]
      [Fintype ↥(ssPlaces q' M (ResidueField A))]
      [DecidableEq ↥(ssPlaces q' (M * s) (ResidueField A))]
      [DecidableEq ↥(ssPlaces q' M (ResidueField A))],
    ∀ (W₁ : Finset (Place (ResidueField A) (modularFunctionFieldC (ResidueField A) (M * s))))
      (hW₁ : ∀ w, w ∈ W₁ ↔ w ∈ ssPlaces q' (M * s) (ResidueField A))
      (hstab₁ : SemilinearAut.IsNodeStable
        (nodePairsOfPlaces (arithFrobC q' (ResidueField A) (M * s)) W₁) (arithFrobC q' (ResidueField A) (M * s)))
      (data₁ : ModularPolynomialData q') (hKr₁ : KroneckerCongruence q' data₁)
      (hα₁ : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) (M * s) q')
      (hβ₁ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) (M * s) q')
      (P₁ : PlaceSpecialization A q' (M * s) data₁ hKr₁ (ResidueField A) (IsLocalRing.residue A) hα₁ hβ₁)
      (R₁ : PlaceSpecialization.ProlongationTuple P₁) (hmodel₁ : R₁.IsModel) (hO₁ : R₁.OrderLawFixed)
      (e₁ : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) (M * s)) → ℕ)
      (he₁ : ∀ p ∈ W₁, 0 < e₁ p)
      (hpin₁ : ∀ w ∈ W₁, e₁ w = placeWidthChar q' (M * s) w)
      (comp₁ : ↥(inertiaInvariants A ((M * s) * q')) →+
        componentGroup (widthOfPlaces (arithFrobC q' (ResidueField A) (M * s)) W₁ e₁))
      (sp₁ : ↥(inertiaInvariants A ((M * s) * q')) →+
        GluedPic0 (ResidueField A) (modularFunctionFieldC (ResidueField A) (M * s))
          (nodePairsOfPlaces (arithFrobC q' (ResidueField A) (M * s)) W₁))
      (hsurj₁ : Function.Surjective comp₁)
      (hker₁ : ∀ x : ↥(inertiaInvariants A ((M * s) * q')),
        comp₁ x = 0 ↔ P₁.IsGoodClass (nodePairsOfPlaces (arithFrobC q' (ResidueField A) (M * s)) W₁) (x : JZero ((M * s) * q')))
      (hsp₁ : P₁.IsGluedSpecialization (nodePairsOfPlaces (arithFrobC q' (ResidueField A) (M * s)) W₁) sp₁),
    ∀ (W₂ : Finset (Place (ResidueField A) (modularFunctionFieldC (ResidueField A) (M))))
      (hW₂ : ∀ w, w ∈ W₂ ↔ w ∈ ssPlaces q' (M) (ResidueField A))
      (hstab₂ : SemilinearAut.IsNodeStable
        (nodePairsOfPlaces (arithFrobC q' (ResidueField A) (M)) W₂) (arithFrobC q' (ResidueField A) (M)))
      (data₂ : ModularPolynomialData q') (hKr₂ : KroneckerCongruence q' data₂)
      (hα₂ : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) (M) q')
      (hβ₂ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) (M) q')
      (P₂ : PlaceSpecialization A q' (M) data₂ hKr₂ (ResidueField A) (IsLocalRing.residue A) hα₂ hβ₂)
      (R₂ : PlaceSpecialization.ProlongationTuple P₂) (hmodel₂ : R₂.IsModel) (hO₂ : R₂.OrderLawFixed)
      (e₂ : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) (M)) → ℕ)
      (he₂ : ∀ p ∈ W₂, 0 < e₂ p)
      (hpin₂ : ∀ w ∈ W₂, e₂ w = placeWidthChar q' M w)
      (comp₂ : ↥(inertiaInvariants A ((M) * q')) →+
        componentGroup (widthOfPlaces (arithFrobC q' (ResidueField A) (M)) W₂ e₂))
      (sp₂ : ↥(inertiaInvariants A ((M) * q')) →+
        GluedPic0 (ResidueField A) (modularFunctionFieldC (ResidueField A) (M))
          (nodePairsOfPlaces (arithFrobC q' (ResidueField A) (M)) W₂))
      (hsurj₂ : Function.Surjective comp₂)
      (hker₂ : ∀ x : ↥(inertiaInvariants A ((M) * q')),
        comp₂ x = 0 ↔ P₂.IsGoodClass (nodePairsOfPlaces (arithFrobC q' (ResidueField A) (M)) W₂) (x : JZero ((M) * q')))
      (hsp₂ : P₂.IsGluedSpecialization (nodePairsOfPlaces (arithFrobC q' (ResidueField A) (M)) W₂) sp₂),
      ∃ (ab : Fin 2 → (↥(ssPlaces q' (M * s) (ResidueField A)) →
            ↥(ssPlaces q' M (ResidueField A))))
        (w : ↥(ssPlaces q' (M * s) (ResidueField A)) → ℕ+)
        (wV : ↥(ssPlaces q' M (ResidueField A)) → ℕ+)
        (m : Fin 2 → ↥(ssPlaces q' (M * s) (ResidueField A)) → ℕ)
        (Φ : Fin 2 → (GluedPic0 (ResidueField A)
              (modularFunctionFieldC (ResidueField A) (M * s)) (nodePairsOfPlaces (arithFrobC q' (ResidueField A) (M * s)) W₁) →+
            GluedPic0 (ResidueField A)
              (modularFunctionFieldC (ResidueField A) M) (nodePairsOfPlaces (arithFrobC q' (ResidueField A) M) W₂))),
        (∀ p : ↥(ssPlaces q' (M * s) (ResidueField A)), (w p : ℕ) = e₁ ↑p) ∧
        (∀ v : ↥(ssPlaces q' M (ResidueField A)), (wV v : ℕ) = e₂ ↑v) ∧
        (∀ (i : Fin 2) (x : ↥(inertiaInvariants A ((M * s) * q')))
            (z : JZero ((M * q') * s))
            (_ : Nat.mul_right_comm M s q' ▸ (x : JZero ((M * s) * q')) = z)
            (hx : degeneracyPushforwardPair (M * q') s i z ∈ inertiaInvariants A (M * q')),
            comp₁ x = 0 →
              comp₂ ⟨degeneracyPushforwardPair (M * q') s i z, hx⟩ = 0) ∧
        (∀ (i : Fin 2) (x : ↥(inertiaInvariants A ((M * s) * q')))
            (z : JZero ((M * q') * s))
            (_ : Nat.mul_right_comm M s q' ▸ (x : JZero ((M * s) * q')) = z)
            (hx : degeneracyPushforwardPair (M * q') s i z ∈ inertiaInvariants A (M * q')),
            comp₁ x = 0 →
              comp₂ ⟨degeneracyPushforwardPair (M * q') s i z, hx⟩ = 0 →
                sp₂ ⟨degeneracyPushforwardPair (M * q') s i z, hx⟩ = Φ i (sp₁ x)) ∧
        (∀ (i : Fin 2) (p : ↥(ssPlaces q' (M * s) (ResidueField A))),
            m i p * (w p : ℕ) = (wV (ab i p) : ℕ)) ∧
        (∀ (i : Fin 2) (v : ↥(ssPlaces q' M (ResidueField A))),
            (∑ p with ab i p = v, m i p) = s + 1) ∧
        (∀ (i : Fin 2) (g : ↥(nodePairsOfPlaces (arithFrobC q' (ResidueField A) (M * s)) W₁) → Additive (ResidueField A)ˣ),
            Φ i (GluedPic0.nodeUnit (nodePairsOfPlaces (arithFrobC q' (ResidueField A) (M * s)) W₁) g) =
              GluedPic0.nodeUnit (nodePairsOfPlaces (arithFrobC q' (ResidueField A) M) W₂)
                (fun n₂ => ∑ p₁ with ab i p₁ =
                    (⟨(↑n₂ : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M) ×
                        Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M)).1,
                      (hW₂ _).mp (fst_mem_of_mem_nodePairsOfPlaces n₂.2)⟩ :
                      ↥(ssPlaces q' M (ResidueField A))),
                  m i p₁ • g ⟨smulNodePair (arithFrobC q' (ResidueField A) (M * s)) ↑p₁,
                    smulNodePair_mem_nodePairsOfPlaces _ ((hW₁ ↑p₁).mpr p₁.2)⟩)) ∧
        (∀ (φ : Fin 2 → (↥(modularFunctionFieldC (IsLocalRing.ResidueField A) M) →ₐ[IsLocalRing.ResidueField A]
                ↥(modularFunctionFieldC (IsLocalRing.ResidueField A) (M * s))))
            (hφ : ∀ i, (φ i).toRingHom.IsIntegral),
            (∀ x, ((φ 0 x : ↥(modularFunctionFieldC (IsLocalRing.ResidueField A) (M * s))) :
                LaurentSeries (IsLocalRing.ResidueField A)) = x) →
            (∀ x, ((φ 1 x : ↥(modularFunctionFieldC (IsLocalRing.ResidueField A) (M * s))) :
                LaurentSeries (IsLocalRing.ResidueField A)) = qExpand (IsLocalRing.ResidueField A) s x) →
            ∀ (i : Fin 2) (p : ↥(ssPlaces q' (M * s) (IsLocalRing.ResidueField A))),
              AlgebraicCurve.Place.restrictAlong (φ i) (hφ i) (↑p) = ↑(ab i p)) := by

  haveI : NeZero q' := ⟨hq'.ne_zero⟩
  haveI : Fact q'.Prime := ⟨hq'⟩
  haveI : CharP (ResidueField A) q' :=
    ValuationSubring.charP_residueField_of_liesOverPrime_def hq' hA
  letI := heckeModuleBar ((M * s) * q')
  letI := heckeModuleBar (M * s)
  letI := heckeModuleBar (M * q')
  letI := heckeModuleBar M
  letI := instDecidableEqResidueFieldSemistable A
  letI := instAlgebraResidueFieldModularFunctionFieldCSemistable A (M * s)
  letI := instAlgebraResidueFieldModularFunctionFieldCSemistable A M

  intro _ _ _ _ W₁ hW₁ hstab₁ data₁ hKr₁ hα₁ hβ₁ P₁ R₁ hmodel₁ hO₁ e₁ he₁ hpin₁ comp₁ sp₁ hsurj₁ hker₁ hsp₁
    W₂ hW₂ hstab₂ data₂ hKr₂ hα₂ hβ₂ P₂ R₂ hmodel₂ hO₂ e₂ he₂ hpin₂ comp₂ sp₂ hsurj₂ hker₂ hsp₂
  haveI : NeZero (M * s) := ⟨Nat.mul_ne_zero (NeZero.ne M) (NeZero.ne s)⟩

  haveI : DecidableEq ↥(nodePairsOfPlaces (arithFrobC q' (ResidueField A) M) W₂) := Classical.decEq _

  haveI : Fact q'.Prime := ⟨hq'⟩
  haveI : CharP (ResidueField A) q' := ValuationSubring.charP_residueField_of_liesOverPrime_def hq' hA
  have hq'Ms : ¬ q' ∣ M * s := fun h =>
    ((Nat.Prime.dvd_mul hq').mp h).elim hq'M fun h' => hsq' ((Nat.prime_dvd_prime_iff_eq hq' hs).mp h').symm
  have hlegs := loc_LEGS M s q' hq' A hA hq'Ms
  obtain ⟨φ, hφ, hφα, hφβ⟩ := hlegs

  have hpack :=
    degeneracyPair_finiteSeparableDeg_ssPlaces_preserved_reflected M s q' hs hsq' hq'M hsM
      (k := ResidueField A) φ hφ hφα hφβ
  obtain ⟨hfinP, hsepP, hdegP, hpresP, hreflP⟩ := hpack

  let ab : Fin 2 → (↥(ssPlaces q' (M * s) (ResidueField A)) → ↥(ssPlaces q' M (ResidueField A))) :=
    fun i p => ⟨Place.restrictAlong (φ i) (hφ i) ↑p, hpresP i ↑p p.2⟩
  let m : Fin 2 → ↥(ssPlaces q' (M * s) (ResidueField A)) → ℕ :=
    fun i p => Place.ramificationIndexAlong (φ i) ↑p
  have hab : ∀ i p, (ab i p : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M)) =
      Place.restrictAlong (φ i) (hφ i) ↑p := fun _ _ => rfl
  have hm : ∀ i p, m i p = Place.ramificationIndexAlong (φ i)
      (p : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) (M * s))) := fun _ _ => rfl
  have hadm := admTransport M s q' hs hq' hsq' hq'M hsM A hA W₁ hW₁ hstab₁ W₂ hW₂ hstab₂
    φ hφ hφα hφβ ab m hab hm
  have hprin := prinTransport M s q' hs hq' hsq' hq'M hsM A hA W₁ hW₁ hstab₁ W₂ hW₂ hstab₂
    φ hφ hφα hφβ ab m hab hm

  have hΦ := fun (i : Fin 2) (g : ↥(nodePairsOfPlaces (arithFrobC q' (ResidueField A) (M * s)) W₁) → Additive
      (ResidueField A)ˣ) =>
    NodePairTransport.pushforwardMap_nodeUnit_pairMap hW₁ hW₂ (ab i) (m i) (φ i) (hφ i) (hadm i) (hprin i) g

  have hC3 := goodTransport M s q' hs hq' hsq' hq'M hsM A hA W₁ hW₁ hstab₁ data₁ hKr₁ hα₁ hβ₁ P₁ R₁ hmodel₁ hO₁
      e₁ he₁ hpin₁ comp₁ sp₁
    hsurj₁ hker₁ hsp₁ W₂ hW₂ hstab₂ data₂ hKr₂ hα₂ hβ₂ P₂ R₂ hmodel₂ hO₂ e₂ he₂ hpin₂ comp₂ sp₂ hsurj₂ hker₂ hsp₂
    ab m φ hφ hφα hφβ hadm
  have hC4 := specCompat M s q' hs hq' hsq' hq'M hsM A hA W₁ hW₁ hstab₁ data₁ hKr₁ hα₁ hβ₁ P₁ R₁ hmodel₁ hO₁ e₁
      he₁ hpin₁ comp₁ sp₁
    hsurj₁ hker₁ hsp₁ W₂ hW₂ hstab₂ data₂ hKr₂ hα₂ hβ₂ P₂ R₂ hmodel₂ hO₂ e₂ he₂ hpin₂ comp₂ sp₂ hsurj₂ hker₂ hsp₂ ab m
        φ hφ hφα hφβ hadm hprin

  have hC5 : ∀ (i : Fin 2) (p : ↥(ssPlaces q' (M * s) (ResidueField A))),
      m i p * placeWidthChar q' (M * s)
          (p : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) (M * s)))
        = placeWidthChar q' M (ab i p : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M)) :=
    fun i p =>
      ramificationIndexAlong_mul_placeWidthChar_eq_placeWidthChar_restrictAlong_degeneracyPair M s q'
        hs hsq' hq'M ab m φ hφ hφα hφβ hab hm i p

  have hC6 := fibreSum_eq M s q' hs hq' hsq' hq'M hsM A hA W₁ hW₁ hstab₁ W₂ hW₂ hstab₂
    φ hφ hφα hφβ ab m hab hm

  refine ⟨ab, fun p => ⟨e₁ ↑p, he₁ ↑p ((hW₁ ↑p).mpr p.2)⟩,
    fun v => ⟨e₂ ↑v, he₂ ↑v ((hW₂ ↑v).mpr v.2)⟩, m,
    fun i => GluedPic0.pushforwardMap (nodePairsOfPlaces (arithFrobC q' (ResidueField A) (M * s)) W₁)
        (nodePairsOfPlaces (arithFrobC q' (ResidueField A) M) W₂)
      (NodePairTransport.pairMap _ _ hW₁ hW₂ (ab i)) (NodePairTransport.pairMult _ hW₁ (m i))
      (φ i) (hφ i) (hadm i) (hprin i),
    ?_, ?_, ?_, ?_, ?_, ?_, hΦ, ?_⟩
  · exact fun _ => rfl
  · exact fun _ => rfl
  ·
    intro i x z hz hx h0
    exact (hker₂ _).mpr (hC3 i x z hz ((hker₁ x).mp h0))
  ·
    intro i x z hz hx h0 _
    exact hC4 i x z hz hx ((hker₁ x).mp h0)
  ·
    intro i p
    have h5 := hC5 i p
    rw [← hpin₁ _ ((hW₁ _).mpr p.2), ← hpin₂ _ ((hW₂ _).mpr (ab i p).2)] at h5
    exact h5
  ·
    exact hC6
  ·
    intro φ' hφ' hφα' hφβ' i p
    have hφeq : φ' = φ :=
      funext (Fin.forall_fin_two.mpr
        ⟨AlgHom.ext fun x => Subtype.ext ((hφα' x).trans (hφα x).symm),
         AlgHom.ext fun x => Subtype.ext ((hφβ' x).trans (hφβ x).symm)⟩)
    subst hφeq
    rfl

#print axioms solution

end S_ModularCurve_PlaceSpecialization_gluedSpecialization_twoLevel_degeneracyGlue_of_isModel_placeWidthChar_restrictAlong
end P2MW
export P2MW.S_ModularCurve_PlaceSpecialization_gluedSpecialization_twoLevel_degeneracyGlue_of_isModel_placeWidthChar_restrictAlong (solution)
