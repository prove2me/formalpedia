-- Prove2me | solution 1 for ModularCurve.mazurRealizationFamily_of_modRepIsIrreducible_of_isUnramifiedAt
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/e6c807a4-8edf-51e4-a26e-328d9e90ae17

import Definitions.Def_GaloisRep_Residual
import Definitions.Def_FLTPrelim_ModularRep
import Definitions.Def_ModularCurve_HeckeModule
import Definitions.Def_ModularCurve_MazurPrincipleCore
import Theorems.Thm_WeierstrassCurve_exists_ideal_heckeAlgebra_of_isNormalizedEigenform
import Theorems.Thm_ModularCurve_exists_isEigenformIdeal_heckeTorsion_jZero_ne_bot_of_isMaximal_heckeAlgebra_two
import Theorems.Thm_ModularCurve_not_isEventuallyEisenstein_of_modRepIsIrreducible
import Theorems.Thm_WeierstrassCurve_modRep_blrDecomposition_heckeTorsion_of_frobeniusQuadratic
import Theorems.Thm_ModularCurve_frobeniusQuadratic_JZero
import Theorems.Thm_ModularCurve_heckeOperatorsCommuteBar
import Theorems.Thm_ModularCurve_smulCommClass_JZero_of_heckeOperatorsCommuteBar
import Theorems.Thm_ModularCurve_mTorsionGaloisRep_jZero_galoisFactorsThroughFiniteLevel
import Theorems.Thm_ModularCurve_heckeTorsion_jZero_finite_of_natCast_mem
import Theorems.Thm_WeierstrassCurve_det_galoisRepModuleEnd_frobenius_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_mazurRealizationFamily_of_modRepIsIrreducible_of_isUnramifiedAt
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion"
p2m_attr_erase "instance" "ModularCurve.CuspSpace.instNonempty ModularCurve.CuspSpace.instSubsingletonOfOne ModularCurve.CuspSpace.instFinite ModularCurve.instAlgebraIntermediateFieldLaurent ModularCurve.instIsScalarTowerKaehlerIntermediateFieldLaurent ModularCurve.instIsScalarTowerIntermediateFieldLaurent ModularCurve.instModuleKaehlerIntermediateFieldLaurent ModularCurve.Gamma0Pair.isElliptic ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.B3.instIsElliptic_goodModel ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar ModularCurve.instIsScalarTowerJAdjoin FLT.Gamma0FundamentalSet.instContinuousConstSMulSpecialLinearGroupFinOfNatNatIntUpperHalfPlane_definitions FLT.HyperbolicMeasure.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatIntUpperHalfPlaneVolume_definitions FLT.HyperbolicMeasure.instIsOpenPosMeasureUpperHalfPlaneVolume_definitions FLT.L2ProductionInstance.isFiniteMeasure_gamma0 FLT.L2ProductionInstance.countable_SL2Z FLT.L2ProductionInstance.countable_quotient FLT.L2ProductionInstance.nontrivial_gamma0L2 HeckeEis.instModuleCoeffH1par HeckeEis.instAddCommGroupCoeffH1par HeckeEis.instFiniteIndexHeckeUpper ModularCurve.Period.parabolicHoms_int_moduleFinite ModularCurve.Period.instGroupFG_SL2Z ModularCurve.Period.instIsNoetherian_addHom_int ModularCurve.Period.instGroupFG_Gamma0 FrobeniusDensity.isMaximal_ratPrimeIdeal FrobeniusDensity.liesOver_ratBelow"
p2m_attr_erase "instance" "WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular"
p2m_attr_erase "simp" "PowerSeries.coeff_heckeV PowerSeries.coeff_heckeU ModularCurve.dualHeckeRep_apply_apply ModularCurve.coe_segmentPath ModularCurve.cuspHeckeAeval_heckeGen ModularCurve.coe_periodLatticeRestrict_apply ModularCurve.jqNModC_one ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero"
p2m_attr_erase "simp" "AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularCurve.ComplexPlaceDictionary.mk.injEq ModularCurve.ComplexPlaceDictionary.mk.sizeOf_spec ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero"
p2m_attr_erase "simp" "ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.coe_cuspidalDivisor₀ ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.Period.IsEquivariantPrimitive.periodHom_apply ModularCurve.Period.IsEquivariantPrimitive.period_one ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄"
p2m_attr_erase "simp" "ModularCurve.ProjectiveLine.map_mk AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule ModularCurve.cuspCount_one ModularCurve.CuspSpace.cuspDenomAux_infty ModularCurve.CuspSpace.cuspDenomAux_coe ModularCurve.CuspSpace.cuspDenom_mk_zero ModularCurve.CuspSpace.cuspDenom_mk_infty ModularCurve.mapGL_apply_coe ModularCurve.ratPoint_one_zero ModularCurve.ratPoint_zero_right ModularCurve.CuspSpace.fromCoset_mk ModularCurve.CuspSpace.cuspDenom_mk ModularCurve.ratPoint_zero_one ModularCurve.qEulerFun_coeff ModularCurve.diffQExp_D ModularCurve.qEulerOn_apply ModularCurve.qEuler_coeff ModularCurve.gamma0PairMap_gen ModularCurve.moduliPointMapRingHom_mk ModularCurve.Gamma0Pair.mk.injEq ModularCurve.ModuliPoint.j_mk ModularCurve.Gamma0Pair.mk.sizeOf_spec ModularCurve.gamma0PairMap_toCurve WeierstrassCurve.Affine.vcY_vcYInv"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero WeierstrassCurve.ratPointHom_apply WeierstrassCurve.ratPointMap_zero ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ WeierstrassCurve.veluX_empty WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.genusOnePic0Equiv_apply WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂"
p2m_attr_erase "simp" "Param.B.sizeOf_spec compl₂EDS_two AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.reducePoint_zero"
p2m_attr_erase "simp" "HahnSeries.ramScale_apply WeierstrassCurve.veluPointMap2_zero FLT.TruncatedDomainPartition.unipotentDiagonalSum_zero HeckeEis.coeffCoboundaryMap_apply HeckeEis.heckeConjMat_apply_one_one HeckeEis.coe_heckeConjSL HeckeEis.mem_heckeUpperSL HeckeEis.resHom_apply HeckeEis.heckeConjMat_apply_zero_one HeckeEis.coe_transferAux HeckeEis.coe_heckeConj HeckeEis.alphaMat_apply_one_one HeckeEis.heckeConjMat_apply_one_zero HeckeEis.alphaMat_apply_zero_one HeckeEis.pullbackHom_apply HeckeEis.alphaMat_apply_one_zero HeckeEis.alphaMat_apply_zero_zero HeckeEis.heckeConjMat_apply_zero_zero AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap ModularCurve.Period.jConjMat_apply_zero_one ModularCurve.Period.jConjSL_coe ModularCurve.Period.jConjMat_apply_one_zero ModularCurve.Period.jConjMat_apply_one_one ModularCurve.Period.jConjGamma0_coe ModularCurve.Period.charInvolution_apply ModularCurve.Period.jConjMat_apply_zero_zero FrobeniusEndo.linePencil_apply WeierstrassCurve.Universal.halveX_zero WeierstrassCurve.Universal.specialize_X_one WeierstrassCurve.Universal.coeff_halve WeierstrassCurve.Universal.specialize_X_two WeierstrassCurve.Universal.halveCoeff_zero WeierstrassCurve.Universal.specialize_X_four"
p2m_attr_erase "simp" "WeierstrassCurve.Universal.coeff_halveX WeierstrassCurve.Universal.specialize_X_three WeierstrassCurve.Universal.specialize_X_zero TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec WeierstrassCurve.Affine.mem_fibSet ResidualGaloisRep.Equiv.mk.sizeOf_spec ResidualGaloisRep.Equiv.mk.injEq ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong ModularCurve.qExpandAlgHomC_apply ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero"
p2m_attr_erase "simp" "TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff"

set_option autoImplicit false

open ModularCurve
open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point

private theorem c_intCast_eq (a : ℤ) : (MvPolynomial.C a : HeckeAlg) = (a : HeckeAlg) := by
  simp

private theorem c1_ideal (p : ℕ) [Fact p.Prime] (W : WeierstrassCurve ℤ) (M : ℕ) [NeZero M]
    (hres : W.IsResiduallyModularOfLevel p M) :
    letI := heckeModuleBar M
    ∃ 𝔪 : Ideal HeckeAlg, 𝔪.IsMaximal ∧ ((p : ℕ) : HeckeAlg) ∈ 𝔪 ∧
      (∀ (ℓ : ℕ) (hℓ : ℓ.Prime), W.IsGoodPrimeFor ℓ → ¬ ℓ ∣ M → ℓ ≠ p →
        heckeGen ⟨ℓ, hℓ⟩ - MvPolynomial.C (W.apOfModel ℓ : ℤ) ∈ 𝔪) ∧
      heckeTorsion (JZero M) 𝔪 ≠ ⊥ := by
  obtain ⟨f, 𝔪₀, hf, h𝔪₀, hp𝔪₀, hcong⟩ := hres
  let S₀ : Set ℕ := {ℓ | ℓ ∣ M} ∪ {p}
  obtain ⟨𝔪₂, hmax₂, hp₂, hT₂⟩ :=
    WeierstrassCurve.exists_ideal_heckeAlgebra_of_isNormalizedEigenform p W S₀ f 𝔪₀ hf h𝔪₀ hp𝔪₀
      (fun ℓ hℓ hgood hS => hcong ℓ hℓ hgood (fun h => hS (Or.inl h)) (fun h => hS (Or.inr h)))
  obtain ⟨𝔪, hmax, -, hp𝔪, hbin, hne⟩ :=
    ModularCurve.exists_isEigenformIdeal_heckeTorsion_jZero_ne_bot_of_isMaximal_heckeAlgebra_two
      M p S₀ W.IsGoodPrimeFor (fun ℓ => W.apOfModel ℓ) 𝔪₂ hmax₂ hp₂ hT₂
  refine ⟨𝔪, hmax, hp𝔪, ?_, hne⟩
  intro ℓ hℓ hgood hM hp
  have hS : ℓ ∉ S₀ := fun h => h.elim hM (fun h' => hp h')
  rw [c_intCast_eq]
  exact hbin ℓ hℓ hS hM hgood

private theorem c2_notEis (p : ℕ) [Fact p.Prime] (W : WeierstrassCurve ℤ) (hΔ : W.Δ ≠ 0)
    (hirr : W.ModRepIsIrreducible p) (M : ℕ) [NeZero M] (𝔪 : Ideal HeckeAlg) (hmax : 𝔪.IsMaximal)
    (hp𝔪 : ((p : ℕ) : HeckeAlg) ∈ 𝔪)
    (hbin : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime), W.IsGoodPrimeFor ℓ → ¬ ℓ ∣ M → ℓ ≠ p →
      heckeGen ⟨ℓ, hℓ⟩ - MvPolynomial.C (W.apOfModel ℓ : ℤ) ∈ 𝔪) :
    ¬ IsEventuallyEisenstein 𝔪 := by
  have hfin : ({ℓ : ℕ | ℓ ∣ M} ∪ {p} : Set ℕ).Finite := by
    refine Set.Finite.union ?_ (Set.finite_singleton p)
    exact (Nat.divisors M).finite_toSet.subset
      (fun ℓ hℓ => Nat.mem_divisors.2 ⟨hℓ, NeZero.ne M⟩)
  refine ModularCurve.not_isEventuallyEisenstein_of_modRepIsIrreducible p W hΔ hirr _ hfin 0
    (by simp) 𝔪 hmax.ne_top hp𝔪 ?_
  intro ℓ hℓ hS hgood
  have hM : ¬ ℓ ∣ M := fun h => hS (Or.inl h)
  have hp : ℓ ≠ p := fun h => hS (Or.inr h)
  have h := hbin ℓ hℓ hgood hM hp
  rw [c_intCast_eq] at h
  simpa using h

private abbrev matAction {G : Type*} [Monoid G] {R : Type*} [CommRing R]
    (ρ : G →* Matrix (Fin 2) (Fin 2) R) : DistribMulAction G (Fin 2 → R) where
  smul σ v := (ρ σ).mulVec v
  one_smul v := by
    show (ρ 1).mulVec v = v
    rw [map_one, Matrix.one_mulVec]
  mul_smul σ τ v := by
    show (ρ (σ * τ)).mulVec v = (ρ σ).mulVec ((ρ τ).mulVec v)
    rw [map_mul, Matrix.mulVec_mulVec]
  smul_zero σ := by
    show (ρ σ).mulVec 0 = 0
    exact Matrix.mulVec_zero _
  smul_add σ v w := by
    show (ρ σ).mulVec (v + w) = (ρ σ).mulVec v + (ρ σ).mulVec w
    exact Matrix.mulVec_add _ _ _

private theorem matAction_smulComm {G : Type*} [Monoid G] {R : Type*} [CommRing R]
    (ρ : G →* Matrix (Fin 2) (Fin 2) R) :
    letI := matAction ρ
    SMulCommClass G R (Fin 2 → R) :=
  letI := matAction ρ
  ⟨fun σ c v => Matrix.mulVec_smul (ρ σ) c v⟩

private theorem matAction_det {G : Type*} [Monoid G] {R : Type*} [CommRing R]
    (ρ : G →* Matrix (Fin 2) (Fin 2) R) (σ : G) :
    letI := matAction ρ
    haveI := matAction_smulComm ρ
    LinearMap.det (DistribSMul.toLinearMap R (Fin 2 → R) σ) = (ρ σ).det := by
  letI := matAction ρ
  haveI := matAction_smulComm ρ
  have h : DistribSMul.toLinearMap R (Fin 2 → R) σ = Matrix.toLin' (ρ σ) :=
    LinearMap.ext fun v => by
      rw [Matrix.toLin'_apply]
      rfl
  rw [h, LinearMap.det_toLin']

private theorem block_package (p : ℕ) [Fact p.Prime] (q : ℕ)
    {J : Type} [AddCommGroup J] [Module HeckeAlg J]
    [DistribMulAction (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) J]
    [SMulCommClass (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) HeckeAlg J]
    (𝔪 : Ideal HeckeAlg) [Nontrivial (HeckeAlg ⧸ 𝔪)] [CharP (HeckeAlg ⧸ 𝔪) p]
    (ρm : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* Matrix (Fin 2) (Fin 2) (ZMod p))
    {n : ℕ} (hn : 0 < n) (e : heckeTorsion J 𝔪 ≃ₗ[HeckeAlg ⧸ 𝔪] (Fin n → (Fin 2 → HeckeAlg ⧸ 𝔪)))
    (he : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (w : heckeTorsion J 𝔪) (i : Fin n),
      e (mTorsionGaloisRep J 𝔪 σ w) i =
        ((ρm σ).map (ZMod.castHom (dvd_refl p) (HeckeAlg ⧸ 𝔪))).mulVec (e w i))
    (hunr : ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime q →
      ∀ σ ∈ A.inertiaSubgroupIn ℚ, ρm σ = 1)
    (hdet : ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime q →
      ∀ frob : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, A.IsFrobeniusAt frob q →
        (ρm frob).det = (q : ZMod p)) :
    ∃ (V : Type) (_ : AddCommGroup V) (_ : Module (HeckeAlg ⧸ 𝔪) V)
      (_ : DistribMulAction (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) V)
      (_ : SMulCommClass (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (HeckeAlg ⧸ 𝔪) V)
      (ι : V →+ J),
      Module.finrank (HeckeAlg ⧸ 𝔪) V = 2 ∧ Function.Injective ι ∧
      (∀ (g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (v : V), ι (g • v) = g • ι v) ∧
      (∀ v : V, ι v ∈ heckeTorsion J 𝔪) ∧
      (∀ (t : HeckeAlg) (v : V), ι (Ideal.Quotient.mk 𝔪 t • v) = t • ι v) ∧
      ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime q →
        (∀ σ ∈ A.inertiaSubgroupIn ℚ, ∀ v : V, σ • v = v) ∧
        ∀ frob : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, A.IsFrobeniusAt frob q →
          LinearMap.det (DistribSMul.toLinearMap (HeckeAlg ⧸ 𝔪) V frob) = ((q : ℕ) : HeckeAlg ⧸ 𝔪) := by

  let ρM : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* Matrix (Fin 2) (Fin 2) (HeckeAlg ⧸ 𝔪) :=
    (RingHom.mapMatrix (ZMod.castHom (dvd_refl p) (HeckeAlg ⧸ 𝔪))).toMonoidHom.comp ρm
  have hρM : ∀ σ, ρM σ = (ρm σ).map (ZMod.castHom (dvd_refl p) (HeckeAlg ⧸ 𝔪)) := fun σ => rfl
  letI instDMA : DistribMulAction (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (Fin 2 → HeckeAlg ⧸ 𝔪) :=
    matAction ρM
  haveI instSCC : SMulCommClass (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (HeckeAlg ⧸ 𝔪)
      (Fin 2 → HeckeAlg ⧸ 𝔪) :=
    matAction_smulComm ρM

  let i₀ : Fin n := ⟨0, hn⟩
  let ιₗ : (Fin 2 → HeckeAlg ⧸ 𝔪) →ₗ[HeckeAlg ⧸ 𝔪] heckeTorsion J 𝔪 :=
    e.symm.toLinearMap ∘ₗ LinearMap.single (HeckeAlg ⧸ 𝔪) (fun _ : Fin n => Fin 2 → HeckeAlg ⧸ 𝔪) i₀
  let ι : (Fin 2 → HeckeAlg ⧸ 𝔪) →+ J := ((heckeTorsion J 𝔪).subtype.toAddMonoidHom).comp ιₗ.toAddMonoidHom
  have hιₗ : ∀ v, ιₗ v = e.symm (Pi.single i₀ v) := fun v => rfl
  have hι : ∀ v, ι v = ((ιₗ v : heckeTorsion J 𝔪) : J) := fun v => rfl
  refine ⟨Fin 2 → HeckeAlg ⧸ 𝔪, inferInstance, inferInstance, instDMA, instSCC, ι, ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    exact Module.finrank_fin_fun (HeckeAlg ⧸ 𝔪)
  ·
    intro v w hvw
    rw [hι, hι, hιₗ, hιₗ] at hvw
    exact Pi.single_injective i₀ (e.symm.injective (Subtype.ext hvw))
  ·
    intro g v
    rw [hι, hι, hιₗ, hιₗ]
    have key : e.symm (Pi.single i₀ (g • v)) = mTorsionGaloisRep J 𝔪 g (e.symm (Pi.single i₀ v)) := by
      apply e.injective
      rw [LinearEquiv.apply_symm_apply]
      funext i
      rw [he g _ i, LinearEquiv.apply_symm_apply, ← hρM]
      by_cases hi : i = i₀
      · subst hi
        rw [Pi.single_eq_same, Pi.single_eq_same]
        rfl
      · rw [Pi.single_eq_of_ne hi, Pi.single_eq_of_ne hi, Matrix.mulVec_zero]
    rw [key, coe_mTorsionGaloisRep_apply]
  ·
    intro v
    rw [hι]
    exact (ιₗ v).2
  ·
    intro t v
    rw [hι, hι, LinearMap.map_smul, Submodule.torsionBySet.mk_smul, Submodule.coe_smul]
  ·
    intro A hA
    refine ⟨?_, ?_⟩
    · intro σ hσ v
      have h2 : ρM σ = 1 := by
        show (RingHom.mapMatrix (ZMod.castHom (dvd_refl p) (HeckeAlg ⧸ 𝔪))).toMonoidHom (ρm σ) = 1
        rw [hunr A hA σ hσ, map_one]
      show (ρM σ).mulVec v = v
      rw [h2, Matrix.one_mulVec]
    · intro frob hfrob
      rw [matAction_det ρM frob]
      show ((RingHom.mapMatrix (ZMod.castHom (dvd_refl p) (HeckeAlg ⧸ 𝔪))) (ρm frob)).det =
        ((q : ℕ) : HeckeAlg ⧸ 𝔪)
      rw [← RingHom.map_det, hdet A hA frob hfrob, map_natCast]

theorem solution
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (W : WeierstrassCurve ℤ) (hΔ : W.Δ ≠ 0)
    (hcard₁ : Nat.card (Submodule.torsionBy ℤ
      ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point p) = p ^ 2)
    (hker : GaloisFactorsThroughFiniteLevel
      (WeierstrassCurve.Affine.Point.galoisRepModuleEnd (K := AlgebraicClosure ℚ) ℚ
        (W.map (Int.castRingHom ℚ)) p))
    (hirr : W.ModRepIsIrreducible p) (q : ℕ) [NeZero q] (hq : q.Prime) (hqp : q ≠ p)
    (hunr : ((W.map (Int.castRingHom ℚ)).residualGaloisRepOf p hcard₁ hker).IsUnramifiedAt q) :
    ∀ (N : ℕ) [NeZero N], ¬ q ∣ N → W.IsResiduallyModularOfLevel p (N * q) →
      ∃ 𝔪 : Ideal HeckeAlg, 𝔪.IsMaximal ∧ ((p : ℕ) : HeckeAlg) ∈ 𝔪 ∧ ¬ IsEventuallyEisenstein 𝔪 ∧
        (∀ (ℓ : ℕ) (hℓ : ℓ.Prime), W.IsGoodPrimeFor ℓ → ¬ ℓ ∣ N * q → ℓ ≠ p →
          heckeGen ⟨ℓ, hℓ⟩ - MvPolynomial.C (W.apOfModel ℓ : ℤ) ∈ 𝔪) ∧
        ∃ (V : Type) (_ : AddCommGroup V) (_ : Module (HeckeAlg ⧸ 𝔪) V)
          (_ : DistribMulAction (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) V)
          (_ : SMulCommClass (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (HeckeAlg ⧸ 𝔪) V)
          (ι : V →+ JZero (N * q)),
          Module.finrank (HeckeAlg ⧸ 𝔪) V = 2 ∧ Function.Injective ι ∧
          (∀ (g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (v : V), ι (g • v) = g • ι v) ∧
          (letI := heckeModuleBar (N * q); ∀ v : V, ι v ∈ heckeTorsion (JZero (N * q)) 𝔪) ∧
          (letI := heckeModuleBar (N * q);
            ∀ (t : HeckeAlg) (v : V), ι (Ideal.Quotient.mk 𝔪 t • v) = t • ι v) ∧
          ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime q →
            (∀ σ ∈ A.inertiaSubgroupIn ℚ, ∀ v : V, σ • v = v) ∧
            ∀ frob : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, A.IsFrobeniusAt frob q →
              LinearMap.det (DistribSMul.toLinearMap (HeckeAlg ⧸ 𝔪) V frob) = ((q : ℕ) : HeckeAlg ⧸ 𝔪) := by
  intro N instN hqN hres
  letI := heckeModuleBar (N * q)
  obtain ⟨𝔪, hmax, hpm, hbin, hne⟩ := c1_ideal p W (N * q) hres
  have heis : ¬ IsEventuallyEisenstein 𝔪 := c2_notEis p W hΔ hirr (N * q) 𝔪 hmax hpm hbin

  haveI hnt : Nontrivial (HeckeAlg ⧸ 𝔪) := Ideal.Quotient.nontrivial_iff.mpr hmax.ne_top
  haveI : 𝔪.IsPrime := hmax.isPrime
  haveI : IsDomain (HeckeAlg ⧸ 𝔪) := Ideal.Quotient.isDomain 𝔪
  haveI : CharP (HeckeAlg ⧸ 𝔪) p :=
    (CharP.charP_iff_prime_eq_zero (Fact.out : p.Prime)).mpr (by
      rw [← map_natCast (Ideal.Quotient.mk 𝔪), Ideal.Quotient.eq_zero_iff_mem]
      exact hpm)

  haveI hell : (W.map (Int.castRingHom ℚ)).IsElliptic :=
    ⟨by
      rw [WeierstrassCurve.map_Δ, isUnit_iff_ne_zero]
      simpa using hΔ⟩
  have hW : W.IsIntegralModelOf (W.map (Int.castRingHom ℚ)) := ⟨1, one_smul _ _⟩

  haveI hsmc : SMulCommClass (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) HeckeAlg (JZero (N * q)) :=
    smulCommClass_JZero_of_heckeOperatorsCommuteBar (N * q) (heckeOperatorsCommuteBar (N * q))
  have hES := frobeniusQuadratic_JZero (N * q) p (heckeOperatorsCommuteBar (N * q)) hsmc
  have hfin := heckeTorsion_jZero_finite_of_natCast_mem (N * q) 𝔪 p (Fact.out : p.Prime).pos hpm
  have hcont := mTorsionGaloisRep_jZero_galoisFactorsThroughFiniteLevel (N * q) 𝔪 hsmc hfin

  haveI : Finite (Submodule.torsionBy ℤ ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point p) :=
    Nat.finite_of_card_ne_zero (by
      rw [hcard₁]
      exact pow_ne_zero 2 (Fact.out : p.Prime).pos.ne')
  let b : Module.Basis (Fin 2) (ZMod p)
      (Submodule.torsionBy ℤ ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point p) :=
    Module.finBasisOfFinrankEq (ZMod p) _
      ((W.map (Int.castRingHom ℚ)).residualGaloisRepOf p hcard₁ hker).finrank_eq

  let ρm : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* Matrix (Fin 2) (Fin 2) (ZMod p) :=
    ((LinearMap.toMatrixAlgEquiv b).toMulEquiv.toMonoidHom).comp
      (galoisRepModuleEnd (S := ℚ) (K := AlgebraicClosure ℚ) (W.map (Int.castRingHom ℚ)) p)
  have hρm : ∀ σ, ρm σ = LinearMap.toMatrix b b
      (galoisRepModuleEnd (S := ℚ) (K := AlgebraicClosure ℚ) (W.map (Int.castRingHom ℚ)) p σ) :=
    fun σ => rfl

  obtain ⟨n, e, he⟩ :=
    WeierstrassCurve.modRep_blrDecomposition_heckeTorsion_of_frobeniusQuadratic
      (W.map (Int.castRingHom ℚ)) W hW p hp2 (J := JZero (N * q))
      (Nat.pos_of_ne_zero (NeZero.ne (N * q))) 𝔪 hmax hirr hker hbin hES hcont hfin b

  have hn : 0 < n := by
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · exfalso
      apply hne
      subst h0
      rw [Submodule.eq_bot_iff]
      intro x hx
      have h1 : e ⟨x, hx⟩ = e 0 := Subsingleton.elim _ _
      have h2 := e.injective h1
      simpa using congrArg Subtype.val h2
    · exact h0

  have hunr' : ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime q →
      ∀ σ ∈ A.inertiaSubgroupIn ℚ, ρm σ = 1 := by
    intro A hA σ hσ
    have h1 : galoisRepModuleEnd (S := ℚ) (K := AlgebraicClosure ℚ) (W.map (Int.castRingHom ℚ)) p σ = 1 :=
      hunr A hA σ hσ
    show ((LinearMap.toMatrixAlgEquiv b).toMulEquiv.toMonoidHom)
        (galoisRepModuleEnd (S := ℚ) (K := AlgebraicClosure ℚ) (W.map (Int.castRingHom ℚ)) p σ) = 1
    rw [h1, map_one]
  have hdet' : ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime q →
      ∀ frob : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, A.IsFrobeniusAt frob q →
        (ρm frob).det = (q : ZMod p) := by
    intro A hA frob hfrob
    rw [hρm, LinearMap.det_toMatrix]
    exact WeierstrassCurve.det_galoisRepModuleEnd_frobenius_eq (W.map (Int.castRingHom ℚ))
      (Fact.out : p.Prime) hq hqp A hA frob hfrob
  obtain ⟨V, i₁, i₂, i₃, i₄, ι, h₁, h₂, h₃, h₄, h₅, h₆⟩ :=
    block_package p q (J := JZero (N * q)) 𝔪 ρm hn e he hunr' hdet'
  exact ⟨𝔪, hmax, hpm, heis, hbin, V, i₁, i₂, i₃, i₄, ι, h₁, h₂, h₃, h₄, h₅, h₆⟩

end S_ModularCurve_mazurRealizationFamily_of_modRepIsIrreducible_of_isUnramifiedAt
end P2MW
export P2MW.S_ModularCurve_mazurRealizationFamily_of_modRepIsIrreducible_of_isUnramifiedAt (solution)
