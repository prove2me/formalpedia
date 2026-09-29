-- Prove2me | solution 1 for ModularCurve.PlaceSpecialization.exists_reduceFst_eq_and_yDepth_restrictAlong_heckeAlphaBar_pow_placeWidthChar_eq_of_ne_of_not_dvd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/1efc3fc9-deb1-5c12-b358-4700001c6f9e

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
import Definitions.Def_ModularCurve_PlaceWidthChar
import Theorems.Thm_ModularCurve_PlaceSpecialization_restrictAlong_heckeAlphaC_sp_and_restrictAlong_heckeBetaC_sp_eq_sp_restrictAlong_of_isModel
import Theorems.Thm_ModularCurve_PlaceSpecialization_yDepth_restrictAlong_towerInclBar_eq_yDepth_pow_ramificationIndexAlong_heckeAlphaC_of_prime
import Theorems.Thm_ModularCurve_PlaceSpecialization_yDepth_restrictAlong_towerSubstBar_eq_yDepth_pow_ramificationIndexAlong_heckeBetaC_of_prime
import Theorems.Thm_ModularCurve_placeWidthChar_restrictAlong_mul_ramificationIndexAlong_heckeAlphaC_heckeBetaC_cross_of_prime
import Theorems.Thm_ModularCurve_degeneracyPair_finiteSeparableDeg_ssPlaces_preserved_reflected
import Theorems.Thm_ModularCurve_exists_placeSpecialization_prolongationTuple_isModel_regularityLaw_nodeValueLaw_orderLawFixed
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_inertiaFixed_range_redRestrict_forall_nodeCoordinates_presentation_of_orderLawFixed
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_valueIntegralityLaw_of_orderLawFixed
import Theorems.Thm_ModularCurve_one_le_placeWidthChar_of_mem_ssPlaces
import Theorems.Thm_ModularCurve_ssPlaces_finite
import Theorems.Thm_ModularCurve_heckeAlphaBarIntegral_of_prime
import Theorems.Thm_ModularCurve_heckeBetaBarIntegral_of_prime
import Theorems.Thm_ModularCurve_towerInclBar_isIntegral
import Theorems.Thm_ModularCurve_towerSubstBar_isIntegral
import Theorems.Thm_ModularCurve_heckeAlphaCIntegral_unconditional
import Theorems.Thm_ModularCurve_heckeBetaCIntegral_unconditional
import Theorems.Thm_ModularCurve_charLDegeneracyRoof_eq_modularFunctionFieldC_mul
import Theorems.Thm_ValuationSubring_isAlgClosed_residueField
import Theorems.Thm_AlgebraicCurve_Place_restrictAlong_restrictAlong
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_PlaceSpecialization_exists_reduceFst_eq_and_yDepth_restrictAlong_heckeAlphaBar_pow_placeWidthChar_eq_of_ne_of_not_dvd
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite"
p2m_attr_erase "instance" "WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent ModularCurve.B3.instIsElliptic_goodModel ModularCurve.instIsScalarTowerJAdjoin WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular AlgebraicCurve.CellDissection.fintypeV AlgebraicCurve.CellDissection.fintypeC AlgebraicCurve.CellDissection.fintypeE AlgebraicCurve.CellDissection.decEqV AlgebraicCurve.CellDissection.decEqC AlgebraicCurve.CellDissection.decEqE ModularCurve.instIsElliptic_tateBase ModularCurve.NodeLocalized.isLocalization_nodeDenominators ModularCurve.NodeLocalized.algebraEvalRange ModularCurve.NodeLocalized.isLocalRing_modularLocalizedAtPoint instTopologicallyFGOfFiniteType AdicCompletion.instIsLocalRingMaximalIdeal WeierstrassCurve.Affine.instIsDiscreteValuationRingSubtypeFunctionFieldMemValuationSubringValuationSubringWithZeroMultiplicativeIntValuationInfty WeierstrassCurve.Affine.valuationInfty_isNontrivial WeierstrassCurve.veluQuotient2_isShortNF WeierstrassCurve.instIsShortNFMk ModularCurve.IgusaScheme.isOpenImmersion_fInf ModularCurve.IgusaScheme.isOpenImmersion_ιInf ModularCurve.IgusaScheme.fact_jFull_ne_zero ModularCurve.IgusaScheme.isOpenImmersion_ιFin ModularCurve.IgusaScheme.isOpenImmersion_fFin GaloisRepAdic.instAddCommGroup GaloisRepAdic.instFree GaloisRepAdic.instFinite GaloisRepAdic.instModule ResidualGaloisRep.instModule ResidualGaloisRep.instModuleFinite ResidualGaloisRep.instAddCommGroup WeierstrassCurve.Affine.Point.instFinite"
p2m_attr_erase "instance" "AlgebraicCurve.CurveModel.isProper AlgebraicCurve.CurveModel.isIntegral AlgebraicCurve.CurveModel.smooth AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin AlgebraicCurve.CurveModel.chartRing_finitePresentation ModularCurve.numberField_of_finiteDimensional CuspForm.heckeAlgebra.instCommRing CuspForm.heckeAlgebra.instIsMulCommutative CuspForm.heckeAlgebra.instIsAddTorsionFree ModularCurve.CuspSpace.instNonempty ModularCurve.CuspSpace.instSubsingletonOfOne ModularCurve.CuspSpace.instFinite ModularCurve.instAlgebraIntermediateFieldLaurent ModularCurve.instIsScalarTowerKaehlerIntermediateFieldLaurent"
p2m_attr_erase "instance" "ModularCurve.instIsScalarTowerIntermediateFieldLaurent ModularCurve.instModuleKaehlerIntermediateFieldLaurent FLT.Gamma0FundamentalSet.instContinuousConstSMulSpecialLinearGroupFinOfNatNatIntUpperHalfPlane_definitions FLT.HyperbolicMeasure.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatIntUpperHalfPlaneVolume_definitions FLT.HyperbolicMeasure.instIsOpenPosMeasureUpperHalfPlaneVolume_definitions FLT.L2ProductionInstance.isFiniteMeasure_gamma0 FLT.L2ProductionInstance.countable_SL2Z FLT.L2ProductionInstance.countable_quotient FLT.L2ProductionInstance.nontrivial_gamma0L2 HeckeEis.instModuleCoeffH1par HeckeEis.instAddCommGroupCoeffH1par HeckeEis.instFiniteIndexHeckeUpper instFieldLaurentSeriesAlgClosureRat instAlgebraModularFunctionFieldBar ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instAlgebraResidueFieldSubtypeMemValuationSubringGaussBaseResOne ModularCurve.PlaceSpecialization.LevelOneProlongationPair.algGaussBase instAlgebraModularFunctionFieldFullC ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instAlgebraSubtypeMemValuationSubringGaussBaseResOne ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instAlgebraSubtypeMemValuationSubringGaussBaseResTwo instFieldModularFunctionFieldC ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isScalarTower_resOne instFieldLaurentSeries' ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isScalarTower_resTwo instModuleModularFunctionFieldBar ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isLocalHom_resBase₁ instAlgebraModularFunctionFieldC ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isLocalHom_constToGaussBase ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instFieldResOne instFieldModularFunctionFieldBar ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instAlgebraResidueFieldSubtypeMemValuationSubringGaussBaseResTwo ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instFieldResTwo instFieldModularFunctionFieldFullC ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isScalarTower_gaussBase instAlgebraLaurentSeriesAlgClosureRat ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isLocalHom_resBase₂ ModularCurve.PlaceSpecialization.LevelOneProlongationPair.algResidueConst instCommRingModularFunctionFieldBar ModularCurve.NodeLocalized.isScalarTower_K_fieldOver_bar ModularCurve.NodeLocalized.algebraFieldOverBar ModularCurve.NodeLocalized.algebra_isIntegral_fieldOver_bar"
p2m_attr_erase "instance" "ModularCurve.NodeLocalized.isScalarTower_fieldOver_bar_laurent ModularCurve.NodeLocalized.charZero_fieldOver ModularCurve.NodeLocalized.algebraFieldOver ModularCurve.NodeLocalized.charZero_laurentSeries_algClosure"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.PlaceSpecialization.LevelOneProlongationPair.mk.sizeOf_spec ModularCurve.PlaceSpecialization.LevelOneProlongationPair.residue₂_apply ModularCurve.PlaceSpecialization.LevelOneProlongationPair.residue₁_apply ModularCurve.PlaceSpecialization.LevelOneProlongationPair.mk.injEq ModularCurve.coe_nodeEquiv_symm_apply ModularCurve.frobNodePair_jOfNode ModularCurve.jOfNode_mk"
p2m_attr_erase "simp" "ModularCurve.widthOf_mk ModularCurve.frobNodePairEmb_apply ModularCurve.card_nodePairsOf ModularCurve.frobNodePair_snd ModularCurve.coe_nodeEquiv_apply ModularCurve.frobNodePair_fst AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord ModularCurve.cuspCount_one AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe"
p2m_attr_erase "simp" "AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule HahnSeries.ramScale_apply compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one"
p2m_attr_erase "simp" "WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero"
p2m_attr_erase "simp" "PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm ModularCurve.ProjectiveLine.map_mk ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃"
p2m_attr_erase "simp" "ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero"
p2m_attr_erase "simp" "TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff"
p2m_attr_erase "simp" "AlgebraicCurve.abelJacobiDiv_single AlgebraicCurve.AnalyticCoord.mk.injEq AlgebraicCurve.Cell.mk.sizeOf_spec AlgebraicCurve.RadialRegion.mk.sizeOf_spec AlgebraicCurve.RadialRegion.mk.injEq AlgebraicCurve.CellDissection.mk.sizeOf_spec AlgebraicCurve.Cell.mk.injEq AlgebraicCurve.CellDissection.mk.injEq AlgebraicCurve.AnalyticCoord.mk.sizeOf_spec ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst ModularCurve.NodeLocalized.coe_modularEvalAt AdicCompletion.evalₐ_mapₐ AdicCompletion.mapAlgEquivOfBijective_apply AdicCompletion.levelMapₐ_mk AdicCompletion.mapₐ_of AdicCompletion.mapAlgEquiv_symm_apply AdicCompletion.mapAlgEquiv_apply AdicCompletion.evalₐ_ofLevelwiseEquiv AdicCompletion.evalₐ_levelwiseHom AdicCompletion.localizationEquiv_of AdicCompletion.evalₐ_ofLevelwiseEquiv_symm Localization.AtPrime.quotientPowEquiv_mk ModularCurve.LambdaModularPolynomialData.mk.sizeOf_spec ModularCurve.LambdaModularPolynomialData.mk.injEq AdicCompletion.transportOf_of AdicCompletion.selfCompletion_smul_of AdicCompletion.tensorRingEquiv_tmul AdicCompletion.completionOfAlgHom_apply AdicCompletion.completionBaseChangeHom_of AdicCompletion.tensorRingHom_tmul AdicCompletion.stabilizerToCompletionAut_of ModularCurve.Gamma0Pair.map_toCurve"
p2m_attr_erase "simp" "WeierstrassCurve.mapPoint_eq_ratPointMap ModularCurve.Gamma0Pair.map_gen ModularCurve.Gamma0Pair.map_eq_gamma0PairMap ModularCurve.ModuliPoint.map_eq_moduliPointMapRingHom ModularCurve.ModuliPoint.map_mk WeierstrassCurve.mapPointHom_apply WeierstrassCurve.mapPoint_zero WeierstrassCurve.Universal.halveX_zero WeierstrassCurve.Universal.specialize_X_one WeierstrassCurve.Universal.coeff_halve WeierstrassCurve.Universal.specialize_X_two WeierstrassCurve.Universal.halveCoeff_zero WeierstrassCurve.Universal.specialize_X_four WeierstrassCurve.Universal.coeff_halveX WeierstrassCurve.Universal.specialize_X_three WeierstrassCurve.Universal.specialize_X_zero AddMonoid.End.dualEndDataOfSurjective_trace AddMonoid.End.dualEndDataOfSurjective_norm ModularCurve.CharPModel.FibreModel.mk.injEq ModularCurve.CharPModel.FibreModel.mk.sizeOf_spec ModularCurve.IgusaScheme.ιInf_igusaTo_assoc ModularCurve.IgusaScheme.coe_jFull ModularCurve.IgusaScheme.coe_jInvChartInf ModularCurve.IgusaScheme.coe_jChartFin ModularCurve.IgusaScheme.ιFin_igusaTo ModularCurve.IgusaScheme.ιInf_igusaTo ModularCurve.IgusaScheme.ιFin_igusaTo_assoc GaloisRepAdic.mk.injEq GaloisRepAdic.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.injEq ResidualGaloisRep.mk.sizeOf_spec ResidualGaloisRep.mk.injEq ResidualGaloisRep.Equiv.mk.sizeOf_spec ResidualGaloisRep.Equiv.mk.injEq GoodReductionJacobian.RelativePic0Designation.mk.sizeOf_spec GoodReductionJacobian.AvatarSchemeBridge.mk.injEq MilneJVScheme.JacobianSchemeData.mk.injEq GoodReductionJacobian.AvatarSchemeBridge.mk.sizeOf_spec MilneJVScheme.JacobianSchemeData.mk.sizeOf_spec"
p2m_attr_erase "simp" "GoodReductionJacobian.RelativePic0Designation.mk.injEq NeronModelInfra.specGenericFibreInclusion_eq NeronModelInfra.genericFibreRestrict_coe_comp_snd NeronModelInfra.genericFibreRestrict_coe_comp_fst GoodReductionJacobian.schemeHomOverComp_coe NeronModelInfra.schemeHomOverEquivOverHom_apply GoodReductionJacobian.RelativeGroupLaw.mk.sizeOf_spec NeronModelInfra.schemeHomOverEquivOverHom_symm_apply NeronModelInfra.overHomToSchemeHomOver_coe GoodReductionJacobian.RelativeGroupLaw.mk.injEq NeronModelInfra.overHomToSchemeHomOver_schemeHomOverToOverHom NeronModelInfra.schemeHomOverToOverHom_left NeronModelInfra.schemeHomOverToOverHom_overHomToSchemeHomOver NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe AlgebraicCurve.CurveModel.mk.injEq AlgebraicCurve.CurveModel.mk.sizeOf_spec AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces ModularCurve.symPoly_zero ModularCurve.coe_levelPolynomialEquiv_apply ModularCurve.coe_levelBaseRingDescent_apply ModularCurve.levelConst_apply ModularCurve.coe_laurentDescent_apply ModularCurve.dualHeckeRep_apply_apply ModularCurve.coe_segmentPath"
p2m_attr_erase "simp" "ModularCurve.cuspHeckeAeval_heckeGen ModularCurve.coe_periodLatticeRestrict_apply CuspForm.heckeAlgebra.coe_U CuspForm.heckeAlgebra.coe_T ModularForm.coe_heckeTLin_apply CuspForm.coe_heckeULin_apply CuspForm.coe_heckeTLin_apply ModularForm.coe_heckeULin_apply ModularCurve.ComplexPlaceDictionary.mk.injEq ModularCurve.ComplexPlaceDictionary.mk.sizeOf_spec ModularCurve.Period.IsEquivariantPrimitive.periodHom_apply ModularCurve.Period.IsEquivariantPrimitive.period_one ModularCurve.CuspSpace.cuspDenomAux_infty ModularCurve.CuspSpace.cuspDenomAux_coe ModularCurve.CuspSpace.cuspDenom_mk_zero ModularCurve.CuspSpace.cuspDenom_mk_infty ModularCurve.mapGL_apply_coe ModularCurve.ratPoint_one_zero ModularCurve.ratPoint_zero_right ModularCurve.CuspSpace.fromCoset_mk ModularCurve.CuspSpace.cuspDenom_mk ModularCurve.ratPoint_zero_one ModularCurve.qEulerFun_coeff ModularCurve.diffQExp_D ModularCurve.qEulerOn_apply ModularCurve.qEuler_coeff FLT.TruncatedDomainPartition.unipotentDiagonalSum_zero HeckeEis.coeffCoboundaryMap_apply HeckeEis.heckeConjMat_apply_one_one HeckeEis.coe_heckeConjSL HeckeEis.mem_heckeUpperSL HeckeEis.resHom_apply HeckeEis.heckeConjMat_apply_zero_one HeckeEis.coe_transferAux HeckeEis.coe_heckeConj HeckeEis.alphaMat_apply_one_one HeckeEis.heckeConjMat_apply_one_zero HeckeEis.alphaMat_apply_zero_one HeckeEis.pullbackHom_apply HeckeEis.alphaMat_apply_one_zero"
p2m_attr_erase "simp" "HeckeEis.alphaMat_apply_zero_zero HeckeEis.heckeConjMat_apply_zero_zero ModularCurve.frobeniusPullbackGeomLevelUnconditional_single ModularCurve.frobeniusPushforwardGeomLevelUnconditional_single ModularCurve.frobeniusGeomLevelUnconditional_apply_coe ModularCurve.PlaceSpecialization.LevelOneProlongationPair.coe_gaussOrderToIntegers₂ ModularCurve.PlaceSpecialization.LevelOneProlongationPair.coe_gaussOrderToIntegers₁ ModularCurve.PlaceSpecialization.LevelOneProlongationPair.coe_toIntegers₁ ModularCurve.PlaceSpecialization.LevelOneProlongationPair.coe_constToGaussBase ModularCurve.PlaceSpecialization.LevelOneProlongationPair.coe_toIntegers₂ AlgebraicCurve.Pic.baseChange_mk AlgebraicCurve.Place.forgetConstants_toValuationSubring AlgebraicCurve.Place.constantFieldEquiv_symm_apply AlgebraicCurve.Place.ord_forgetConstants AlgebraicCurve.Place.extendConstants_toValuationSubring AlgebraicCurve.Place.constantFieldEquiv_apply_toValuationSubring AlgebraicCurve.Place.mem_fiberConstants AlgebraicCurve.Place.restrictConstants_toValuationSubring"
set_option autoImplicit false
set_option Elab.async false

open AlgebraicCurve IsLocalRing ModularCurve

noncomputable section

namespace Reduce3f

theorem mem_restrictAlong_iff {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
    (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (w : Place K F') (f : F) :
    f ∈ (w.restrictAlong φ hφ).toValuationSubring ↔ φ f ∈ w.toValuationSubring :=
  Iff.rfl

theorem restrictAlong_eq_self_of_forall_eq {K F : Type*} [Field K] [Field F] [Algebra K F]
    (φ : F →ₐ[K] F) (hφ : φ.toRingHom.IsIntegral) (hid : ∀ x, φ x = x) (w : Place K F) :
    w.restrictAlong φ hφ = w :=
  Place.ext (SetLike.ext fun x => by rw [mem_restrictAlong_iff, hid])

theorem isIntegral_inclusion_of_le {K E : Type*} [Field K] [Field E] [Algebra K E]
    {S T : IntermediateField K E} (hST : S ≤ T) (hTS : T ≤ S) :
    (IntermediateField.inclusion hST).toRingHom.IsIntegral :=
  RingHom.isIntegral_of_surjective _ fun y => ⟨⟨(y : E), hTS y.2⟩, Subtype.ext rfl⟩

theorem restrictAlong_inclusion_restrictAlong_inclusion {K E : Type*} [Field K] [Field E] [Algebra K E]
    {S T : IntermediateField K E} (hST : S ≤ T) (hTS : T ≤ S)
    (h : (IntermediateField.inclusion hST).toRingHom.IsIntegral)
    (h' : (IntermediateField.inclusion hTS).toRingHom.IsIntegral) (w : Place K T) :
    (w.restrictAlong (IntermediateField.inclusion hST) h).restrictAlong (IntermediateField.inclusion hTS) h' = w :=
  Place.ext (SetLike.ext fun x => by
    rw [mem_restrictAlong_iff, mem_restrictAlong_iff]
    exact Iff.of_eq (congrArg (· ∈ w.toValuationSubring) (Subtype.ext rfl)))

end Reduce3f

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
      (hreg : R.RegularityLaw W) (hval : R.NodeValueLaw W)
      (Ks : ↥W → IntermediateField ℚ (AlgebraicClosure ℚ)) [∀ w : ↥W, FiniteDimensional ℚ (Ks w)]
      (cs : ∀ w : ↥W, R.NodeCoordinates (Ks w) (w : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) N)))
      (ϖ : ∀ w : ↥W, ↥(NodeLocalized.coeffSubring A (Ks w)))
      (hϖ : ∀ (w : ↥W) (d : ↥(NodeLocalized.coeffSubring A (Ks w))), NodeLocalized.redRestrict (IsLocalRing.residue A) (Ks w) d = 0 ↔ ∃ d', d = ϖ w * d')
      (hvalA : ∀ w : ↥W, R.ValueIntegralityLaw (w : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) N)))
      (hxy : ∀ w : ↥W, ∃ (E : ℕ) (u : ↥(R.nodeIntegersOver (Ks w) (w : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) N)))),
        1 ≤ E ∧ IsUnit u ∧ (cs w).x * (cs w).y = R.nodeConst (Ks w) (w : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) N)) (ϖ w) ^ E * u),
        ∀ (ℓ : Nat.Primes), (ℓ : ℕ) ≠ q → ¬ (ℓ : ℕ) ∣ N →
        haveI : NeZero (ℓ : ℕ) := ⟨ℓ.2.ne_zero⟩
        ∀ (hα' : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) (N * q) ℓ)
          (hβ' : HeckeBetaBarIntegral (AlgebraicClosure ℚ) (N * q) ℓ)
          (V' : Place (AlgebraicClosure ℚ)
            (laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull (N * q * ℓ))))
          (w : ↥W),
          P.reduceFst (V'.restrictAlong (heckeBetaBar (AlgebraicClosure ℚ) (N * q) ℓ) hβ') = w →
          ∃ w'' : ↥W,
            P.reduceFst (V'.restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) (N * q) ℓ) hα') = w'' ∧
            (cs w'').yDepth (V'.restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) (N * q) ℓ) hα')
                ^ placeWidthChar q N (w : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) N))
              = (cs w).yDepth (V'.restrictAlong (heckeBetaBar (AlgebraicClosure ℚ) (N * q) ℓ) hβ')
                ^ placeWidthChar q N (w'' : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) N)) := by
  haveI : NeZero q := ⟨hq.ne_zero⟩
  haveI hqF : Fact q.Prime := ⟨hq⟩
  haveI : CharP (ResidueField A) q := ValuationSubring.charP_residueField_of_liesOverPrime_def hq hA
  letI := instDecidableEqResidueFieldSemistable A
  letI := instAlgebraResidueFieldModularFunctionFieldCSemistable A N
  intro W hW data hKr hα hβ P R hmodel hO hreg hval Ks _instKs cs ϖ hϖ hvalA hxy ℓ hℓq hℓN
  haveI hℓ0 : NeZero (ℓ : ℕ) := ⟨ℓ.2.ne_zero⟩
  haveI hℓP : Fact (ℓ : ℕ).Prime := ⟨ℓ.2⟩
  intro hα' hβ' V' w hw

  have hqNℓ : ¬ q ∣ N * ℓ := by
    intro h
    rcases (Nat.Prime.dvd_mul hq).1 h with h | h
    · exact hqN h
    · exact hℓq ((Nat.prime_dvd_prime_iff_eq hq ℓ.2).1 h).symm
  have hqℓ : q ≠ (ℓ : ℕ) := fun h => hℓq h.symm
  haveI hAC : IsAlgClosed (ResidueField A) := ValuationSubring.isAlgClosed_residueField A
  letI := instAlgebraResidueFieldModularFunctionFieldCSemistable A (N * ℓ)
  have hredsurj : Function.Surjective (IsLocalRing.residue A) := IsLocalRing.residue_surjective
  have hker : ∀ c : A, IsLocalRing.residue A c = 0 ↔ c ∈ IsLocalRing.maximalIdeal A :=
    fun c => IsLocalRing.residue_eq_zero_iff c

  have h₀ : N * ℓ * q ∣ N * q * ℓ := dvd_of_eq (Nat.mul_right_comm N ℓ q)
  have hι₀ := ModularCurve.towerInclBar_isIntegral (AlgebraicClosure ℚ) h₀
  have hι : (towerInclBar (AlgebraicClosure ℚ)
      (mul_dvd_mul_right (dvd_mul_right N ℓ) q : N * q ∣ N * ℓ * q)).toRingHom.IsIntegral :=
    ModularCurve.towerInclBar_isIntegral _ _
  have hι' : (towerSubstBar (AlgebraicClosure ℚ) (N * q) ℓ
      (dvd_of_eq (Nat.mul_right_comm N q ℓ) : N * q * ℓ ∣ N * ℓ * q)).toRingHom.IsIntegral :=
    ModularCurve.towerSubstBar_isIntegral _ _ _
  set V'ᵣ : Place (AlgebraicClosure ℚ) (laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull (N * ℓ * q))) :=
    V'.restrictAlong (towerInclBar (AlgebraicClosure ℚ) h₀) hι₀ with hV'ᵣ
  have eα : V'ᵣ.restrictAlong (towerInclBar (AlgebraicClosure ℚ)
        (mul_dvd_mul_right (dvd_mul_right N ℓ) q : N * q ∣ N * ℓ * q)) hι
      = V'.restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) (N * q) ℓ) hα' := by
      have hc : (towerInclBar (AlgebraicClosure ℚ) h₀).comp (towerInclBar (AlgebraicClosure ℚ)
          (mul_dvd_mul_right (dvd_mul_right N ℓ) q : N * q ∣ N * ℓ * q))
          = heckeAlphaBar (AlgebraicClosure ℚ) (N * q) ℓ :=
        AlgHom.ext fun x => Subtype.ext (by
          simp only [AlgHom.comp_apply, coe_towerInclBar, coe_heckeAlphaBar])
      rw [hV'ᵣ, Place.restrictAlong_restrictAlong _ _ hι hι₀ (by rw [hc]; exact hα')]
      exact Place.restrictAlong_congr hc _ _ _
  have eβ : V'ᵣ.restrictAlong (towerSubstBar (AlgebraicClosure ℚ) (N * q) ℓ
        (dvd_of_eq (Nat.mul_right_comm N q ℓ) : N * q * ℓ ∣ N * ℓ * q)) hι'
      = V'.restrictAlong (heckeBetaBar (AlgebraicClosure ℚ) (N * q) ℓ) hβ' := by
      have hc : (towerInclBar (AlgebraicClosure ℚ) h₀).comp (towerSubstBar (AlgebraicClosure ℚ) (N * q) ℓ
          (dvd_of_eq (Nat.mul_right_comm N q ℓ) : N * q * ℓ ∣ N * ℓ * q))
          = heckeBetaBar (AlgebraicClosure ℚ) (N * q) ℓ :=
        AlgHom.ext fun x => Subtype.ext (by
          simp only [AlgHom.comp_apply, coe_towerInclBar, coe_towerSubstBar, coe_heckeBetaBar])
      rw [hV'ᵣ, Place.restrictAlong_restrictAlong _ _ hι' hι₀ (by rw [hc]; exact hβ')]
      exact Place.restrictAlong_congr hc _ _ _

  obtain ⟨Wᵣ, hWᵣ⟩ : ∃ Wᵣ : Finset (Place (ResidueField A) (modularFunctionFieldC (ResidueField A) (N * ℓ))),
      ∀ w, w ∈ Wᵣ ↔ w ∈ ssPlaces q (N * ℓ) (ResidueField A) :=
    ⟨(ModularCurve.ssPlaces_finite q (N * ℓ) (ResidueField A)).toFinset, fun w => Set.Finite.mem_toFinset _⟩
  have hαᵣ : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) (N * ℓ) q :=
    ModularCurve.heckeAlphaBarIntegral_of_prime _ _ _
  have hβᵣ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) (N * ℓ) q :=
    ModularCurve.heckeBetaBarIntegral_of_prime _ _ _
  obtain ⟨Pᵣ, Rᵣ, hmodelᵣ, hregᵣ, hvalᵣ, hOᵣ⟩ :=
    ModularCurve.exists_placeSpecialization_prolongationTuple_isModel_regularityLaw_nodeValueLaw_orderLawFixed
      (N * ℓ) q hq hqNℓ A hA Wᵣ hWᵣ data hKr hαᵣ hβᵣ
  obtain ⟨K₀, hK₀fd, -, hϖ₀, -, csᵣ', hxy₀, -, -, -, -⟩ :=
    Rᵣ.exists_inertiaFixed_range_redRestrict_forall_nodeCoordinates_presentation_of_orderLawFixed
      hqNℓ hker hmodelᵣ hOᵣ Wᵣ (fun w hw => (hWᵣ w).1 hw) hregᵣ hvalᵣ
  let Ksᵣ : ↥Wᵣ → IntermediateField ℚ (AlgebraicClosure ℚ) := fun _ => K₀
  haveI hKsᵣ : ∀ y : ↥Wᵣ, FiniteDimensional ℚ (Ksᵣ y) := fun _ => hK₀fd
  let csᵣ : ∀ y : ↥Wᵣ, Rᵣ.NodeCoordinates (Ksᵣ y)
      (y : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) (N * ℓ))) := fun y => csᵣ' y y.2
  let ϖᵣ : ∀ y : ↥Wᵣ, ↥(NodeLocalized.coeffSubring A (Ksᵣ y)) :=
    fun _ => ((q : ℕ) : ↥(NodeLocalized.coeffSubring A K₀))
  have hϖᵣ : ∀ (y : ↥Wᵣ) (d : ↥(NodeLocalized.coeffSubring A (Ksᵣ y))),
      NodeLocalized.redRestrict (IsLocalRing.residue A) (Ksᵣ y) d = 0 ↔ ∃ d', d = ϖᵣ y * d' :=
    fun _ d => hϖ₀ d
  have hvalAᵣ : ∀ y : ↥Wᵣ, Rᵣ.ValueIntegralityLaw
      (y : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) (N * ℓ))) :=
    fun y => Rᵣ.valueIntegralityLaw_of_orderLawFixed hqNℓ hOᵣ _ ((hWᵣ _).1 y.2)
  have hxyᵣ : ∀ y : ↥Wᵣ, ∃ (E : ℕ) (u : ↥(Rᵣ.nodeIntegersOver (Ksᵣ y)
      (y : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) (N * ℓ))))),
      1 ≤ E ∧ IsUnit u ∧ (csᵣ y).x * (csᵣ y).y = Rᵣ.nodeConst (Ksᵣ y)
        (y : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) (N * ℓ))) (ϖᵣ y) ^ E * u := by
    intro y
    obtain ⟨u, hu, h⟩ := hxy₀ y y.2
    exact ⟨_, u, ModularCurve.one_le_placeWidthChar_of_mem_ssPlaces hqNℓ ((hWᵣ _).1 y.2), hu, h⟩

  have hroofeq := ModularCurve.charLDegeneracyRoof_eq_modularFunctionFieldC_mul (ResidueField A) q N ℓ hqN hqℓ
  have hroof : modularFunctionFieldC (ResidueField A) (N * ℓ) ≤ charLDegeneracyRoof (ResidueField A) N ℓ :=
    le_of_eq hroofeq.symm
  have hroof' : charLDegeneracyRoof (ResidueField A) N ℓ ≤ modularFunctionFieldC (ResidueField A) (N * ℓ) :=
    le_of_eq hroofeq
  have hroofι : (IntermediateField.inclusion hroof).toRingHom.IsIntegral := by
      exact Reduce3f.isIntegral_inclusion_of_le hroof hroof'
  have hroofι' : (IntermediateField.inclusion hroof').toRingHom.IsIntegral := by
      exact Reduce3f.isIntegral_inclusion_of_le hroof' hroof
  have hαC : (heckeAlphaC (ResidueField A) N ℓ).toRingHom.IsIntegral :=
    ModularCurve.heckeAlphaCIntegral_unconditional (ResidueField A) N ℓ
  have hβC : (heckeBetaC (ResidueField A) N ℓ).toRingHom.IsIntegral :=
    ModularCurve.heckeBetaCIntegral_unconditional (ResidueField A) N ℓ
  have hαℓ : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N ℓ := ModularCurve.heckeAlphaBarIntegral_of_prime _ _ _
  have hβℓ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N ℓ := ModularCurve.heckeBetaBarIntegral_of_prime _ _ _
  set W₀ : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * ℓ)) :=
    V'ᵣ.restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) (N * ℓ) q) hαᵣ with hW₀
  have hred : Pᵣ.reduceFst V'ᵣ = Pᵣ.sp W₀ := rfl
  set y₀ : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) (N * ℓ)) := Pᵣ.sp W₀ with hy₀
  set y₁ : Place (ResidueField A) (charLDegeneracyRoof (ResidueField A) N ℓ) :=
    y₀.restrictAlong (IntermediateField.inclusion hroof') hroofι' with hy₁def
  have hy₁ : y₁.restrictAlong (IntermediateField.inclusion hroof) hroofι = y₀ :=
    Reduce3f.restrictAlong_inclusion_restrictAlong_inclusion hroof' hroof hroofι' hroofι y₀
  obtain ⟨sqα, sqβ⟩ :
      y₁.restrictAlong (heckeAlphaC (ResidueField A) N ℓ) hαC
          = P.sp (W₀.restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) N ℓ) hαℓ) ∧
        y₁.restrictAlong (heckeBetaC (ResidueField A) N ℓ) hβC
          = P.sp (W₀.restrictAlong (heckeBetaBar (AlgebraicClosure ℚ) N ℓ) hβℓ) :=
    ModularCurve.PlaceSpecialization.restrictAlong_heckeAlphaC_sp_and_restrictAlong_heckeBetaC_sp_eq_sp_restrictAlong_of_isModel N q hq hqN A hA data hKr hα hβ P R hmodel hO ℓ hℓq
      hαᵣ hβᵣ Pᵣ Rᵣ hmodelᵣ hOᵣ hαℓ hβℓ hαC hβC hroof' hroofι' W₀
  have redα : P.reduceFst (V'ᵣ.restrictAlong (towerInclBar (AlgebraicClosure ℚ)
        (mul_dvd_mul_right (dvd_mul_right N ℓ) q : N * q ∣ N * ℓ * q)) hι)
      = P.sp (W₀.restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) N ℓ) hαℓ) := by
      have h3 : N ∣ N * ℓ * q := dvd_mul_of_dvd_left (dvd_mul_right N ℓ) q
      have hT := ModularCurve.towerInclBar_isIntegral (AlgebraicClosure ℚ) h3
      have hc1 : (towerInclBar (AlgebraicClosure ℚ) (mul_dvd_mul_right (dvd_mul_right N ℓ) q : N * q ∣ N * ℓ * q)).comp
            (heckeAlphaBar (AlgebraicClosure ℚ) N q) = towerInclBar (AlgebraicClosure ℚ) h3 :=
        AlgHom.ext fun x => Subtype.ext (by
          simp only [AlgHom.comp_apply, coe_towerInclBar, coe_heckeAlphaBar])
      have hc2 : (heckeAlphaBar (AlgebraicClosure ℚ) (N * ℓ) q).comp (heckeAlphaBar (AlgebraicClosure ℚ) N ℓ)
            = towerInclBar (AlgebraicClosure ℚ) h3 :=
        AlgHom.ext fun x => Subtype.ext (by
          simp only [AlgHom.comp_apply, coe_towerInclBar, coe_heckeAlphaBar])
      unfold PlaceSpecialization.reduceFst
      rw [Place.restrictAlong_restrictAlong _ _ hα hι (by rw [hc1]; exact hT), hW₀,
        Place.restrictAlong_restrictAlong _ _ hαℓ hαᵣ (by rw [hc2]; exact hT),
        Place.restrictAlong_congr hc1 _ hT, Place.restrictAlong_congr hc2 _ hT]
  have redβ : P.reduceFst (V'ᵣ.restrictAlong (towerSubstBar (AlgebraicClosure ℚ) (N * q) ℓ
        (dvd_of_eq (Nat.mul_right_comm N q ℓ) : N * q * ℓ ∣ N * ℓ * q)) hι')
      = P.sp (W₀.restrictAlong (heckeBetaBar (AlgebraicClosure ℚ) N ℓ) hβℓ) := by
      have h3 : N * ℓ ∣ N * ℓ * q := dvd_mul_right (N * ℓ) q
      have hT := ModularCurve.towerSubstBar_isIntegral (AlgebraicClosure ℚ) (ℓ : ℕ) h3
      have hc1 : (towerSubstBar (AlgebraicClosure ℚ) (N * q) ℓ
            (dvd_of_eq (Nat.mul_right_comm N q ℓ) : N * q * ℓ ∣ N * ℓ * q)).comp
            (heckeAlphaBar (AlgebraicClosure ℚ) N q) = towerSubstBar (AlgebraicClosure ℚ) N ℓ h3 :=
        AlgHom.ext fun x => Subtype.ext (by
          simp only [AlgHom.comp_apply, coe_towerSubstBar, coe_heckeAlphaBar])
      have hc2 : (heckeAlphaBar (AlgebraicClosure ℚ) (N * ℓ) q).comp (heckeBetaBar (AlgebraicClosure ℚ) N ℓ)
            = towerSubstBar (AlgebraicClosure ℚ) N ℓ h3 :=
        AlgHom.ext fun x => Subtype.ext (by
          simp only [AlgHom.comp_apply, coe_towerSubstBar, coe_heckeAlphaBar, coe_heckeBetaBar])
      unfold PlaceSpecialization.reduceFst
      rw [Place.restrictAlong_restrictAlong _ _ hα hι' (by rw [hc1]; exact hT), hW₀,
        Place.restrictAlong_restrictAlong _ _ hβℓ hαᵣ (by rw [hc2]; exact hT),
        Place.restrictAlong_congr hc1 _ hT, Place.restrictAlong_congr hc2 _ hT]
  have hw' : y₁.restrictAlong (heckeBetaC (ResidueField A) N ℓ) hβC
      = (w : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) N)) := by
    rw [sqβ, ← redβ, eβ]; exact hw

  have hwss : (w : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) N)) ∈ ssPlaces q N (ResidueField A) :=
    (hW _).1 w.2
  let φ : Fin 2 → (modularFunctionFieldC (ResidueField A) N →ₐ[(ResidueField A)] modularFunctionFieldC (ResidueField A) (N * ℓ)) :=
    ![(IntermediateField.inclusion hroof').comp (heckeAlphaC (ResidueField A) N ℓ),
      (IntermediateField.inclusion hroof').comp (heckeBetaC (ResidueField A) N ℓ)]
  have hφ0 : φ 0 = (IntermediateField.inclusion hroof').comp (heckeAlphaC (ResidueField A) N ℓ) :=
    Matrix.cons_val_zero _ _
  have hφ1 : φ 1 = (IntermediateField.inclusion hroof').comp (heckeBetaC (ResidueField A) N ℓ) :=
    (Matrix.cons_val_one _ _).trans (Matrix.head_cons _ _)
  have hIα : ((IntermediateField.inclusion hroof').comp (heckeAlphaC (ResidueField A) N ℓ)).toRingHom.IsIntegral :=
    RingHom.IsIntegral.trans _ _ hαC hroofι'
  have hIβ : ((IntermediateField.inclusion hroof').comp (heckeBetaC (ResidueField A) N ℓ)).toRingHom.IsIntegral :=
    RingHom.IsIntegral.trans _ _ hβC hroofι'
  have hφ : ∀ i, (φ i).toRingHom.IsIntegral := by
    intro i
    fin_cases i
    · exact (congrArg (fun ψ : (modularFunctionFieldC (ResidueField A) N →ₐ[(ResidueField A)]
          modularFunctionFieldC (ResidueField A) (N * ℓ)) => ψ.toRingHom.IsIntegral) hφ0).mpr hIα
    · exact (congrArg (fun ψ : (modularFunctionFieldC (ResidueField A) N →ₐ[(ResidueField A)]
          modularFunctionFieldC (ResidueField A) (N * ℓ)) => ψ.toRingHom.IsIntegral) hφ1).mpr hIβ
  have hφα : ∀ x, ((φ 0 x : modularFunctionFieldC (ResidueField A) (N * ℓ)) : LaurentSeries (ResidueField A)) = x := by
    intro x
    rw [hφ0]
    exact (IntermediateField.coe_inclusion hroof' _).trans (coe_heckeAlphaC (ResidueField A) N ℓ x)
  have hφβ : ∀ x, ((φ 1 x : modularFunctionFieldC (ResidueField A) (N * ℓ)) : LaurentSeries (ResidueField A))
      = qExpand (ResidueField A) ℓ x := by
    intro x
    rw [hφ1]
    exact (IntermediateField.coe_inclusion hroof' _).trans (coe_heckeBetaC (ResidueField A) N ℓ x)
  have hSS := ModularCurve.degeneracyPair_finiteSeparableDeg_ssPlaces_preserved_reflected
    N ℓ q ℓ.2 hℓq hqN hℓN (k := ResidueField A) φ hφ hφα hφβ
  have hXα : Place.restrictAlong (φ 0) (hφ 0) y₀ = y₁.restrictAlong (heckeAlphaC (ResidueField A) N ℓ) hαC :=
    (Place.restrictAlong_congr hφ0 (hφ 0) hIα y₀).trans
      (Place.restrictAlong_restrictAlong (heckeAlphaC (ResidueField A) N ℓ)
        (IntermediateField.inclusion hroof') hαC hroofι' hIα y₀).symm
  have hXβ : Place.restrictAlong (φ 1) (hφ 1) y₀ = y₁.restrictAlong (heckeBetaC (ResidueField A) N ℓ) hβC :=
    (Place.restrictAlong_congr hφ1 (hφ 1) hIβ y₀).trans
      (Place.restrictAlong_restrictAlong (heckeBetaC (ResidueField A) N ℓ)
        (IntermediateField.inclusion hroof') hβC hroofι' hIβ y₀).symm
  have hy₀ss : y₀ ∈ ssPlaces q (N * ℓ) (ResidueField A) :=
    hSS.2.2.2.2 1 _ hwss y₀ (hXβ.trans hw')
  have hw''ss : y₁.restrictAlong (heckeAlphaC (ResidueField A) N ℓ) hαC ∈ ssPlaces q N (ResidueField A) :=
    hXα ▸ hSS.2.2.2.1 0 y₀ hy₀ss
  let y : ↥Wᵣ := ⟨y₀, (hWᵣ _).2 hy₀ss⟩
  let w'' : ↥W := ⟨_, (hW _).2 hw''ss⟩
  have hw''₁ : y₁.restrictAlong (heckeAlphaC (ResidueField A) N ℓ) hαC
      = (w'' : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) N)) := rfl
  refine ⟨w'', ?_, ?_⟩
  · rw [← eα]; exact redα.trans (sqα.symm.trans hw''₁)
  ·
    have hA9 := (ModularCurve.PlaceSpecialization.yDepth_restrictAlong_towerInclBar_eq_yDepth_pow_ramificationIndexAlong_heckeAlphaC_of_prime N q hq hqN A hA
      W hW data hKr hα hβ P R hmodel hO hreg hval Ks cs ϖ hϖ hvalA hxy ℓ hℓq
      Wᵣ hWᵣ hαᵣ hβᵣ Pᵣ Rᵣ hmodelᵣ hOᵣ hregᵣ hvalᵣ Ksᵣ csᵣ ϖᵣ hϖᵣ hvalAᵣ hxyᵣ
      hι hαC hroof hroofι y₁ y w'' hy₁ hw''₁ V'ᵣ rfl (redα.trans (sqα.symm.trans hw''₁))).1
    have hB6 := (ModularCurve.PlaceSpecialization.yDepth_restrictAlong_towerSubstBar_eq_yDepth_pow_ramificationIndexAlong_heckeBetaC_of_prime N q hq hqN A hA
      W hW data hKr hα hβ P R hmodel hO hreg hval Ks cs ϖ hϖ hvalA hxy ℓ hℓq
      Wᵣ hWᵣ hαᵣ hβᵣ Pᵣ Rᵣ hmodelᵣ hOᵣ hregᵣ hvalᵣ Ksᵣ csᵣ ϖᵣ hϖᵣ hvalAᵣ hxyᵣ
      hι' hβC hroof hroofι y₁ y w hy₁ hw' V'ᵣ rfl (redβ.trans (sqβ.symm.trans hw'))).1

    have hcross := ModularCurve.placeWidthChar_restrictAlong_mul_ramificationIndexAlong_heckeAlphaC_heckeBetaC_cross_of_prime
      N ℓ q ℓ.2 hℓq hqN hℓN (k := ResidueField A) hαC hβC y₁
    rw [hw', hw''₁] at hcross
    have hexp : y₁.ramificationIndexAlong (heckeAlphaC (ResidueField A) N ℓ)
          * placeWidthChar q N (w : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) N))
        = y₁.ramificationIndexAlong (heckeBetaC (ResidueField A) N ℓ)
          * placeWidthChar q N (w'' : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) N)) := by
      have := hcross
      push_cast at this
      exact_mod_cast (by linarith : _)

    rw [← eα, ← eβ, hA9, hB6, ← pow_mul, ← pow_mul, hexp]

end
end S_ModularCurve_PlaceSpecialization_exists_reduceFst_eq_and_yDepth_restrictAlong_heckeAlphaBar_pow_placeWidthChar_eq_of_ne_of_not_dvd
end P2MW
export P2MW.S_ModularCurve_PlaceSpecialization_exists_reduceFst_eq_and_yDepth_restrictAlong_heckeAlphaBar_pow_placeWidthChar_eq_of_ne_of_not_dvd (solution)
