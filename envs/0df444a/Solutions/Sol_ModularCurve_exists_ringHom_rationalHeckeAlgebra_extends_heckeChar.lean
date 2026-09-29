-- Prove2me | solution 1 for ModularCurve.exists_ringHom_rationalHeckeAlgebra_extends_heckeChar
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/e3c28aa5-703a-57d7-a0ce-840734c6c3ca

import Mathlib
import Definitions.Def_CuspForm_HeckeAlgebra
import Definitions.Def_ModularCurve_JZeroTateModule
import Definitions.Def_ModularCurve_HeckeModule
import Definitions.Def_ModularCurve_HeckeInputsAll
import Theorems.Thm_ModularCurve_linearIndependent_rationalHeckeRep_of_linearIndependent
import Theorems.Thm_ModularCurve_exists_injective_ringHom_adjoin_heckeOperatorBar_cuspForm
import Theorems.Thm_ModularCurve_moduleFinite_padicInt_tateModule_jZero
import Theorems.Thm_RingHom_exists_comp_algebraMap_eq_of_isIntegral_of_isAlgClosed
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_ringHom_rationalHeckeAlgebra_extends_heckeChar
p2m_attr_erase "instance" "ModularCurve.CuspSpace.instNonempty ModularCurve.CuspSpace.instSubsingletonOfOne ModularCurve.CuspSpace.instFinite ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instAlgebraIntermediateFieldLaurent ModularCurve.instIsScalarTowerKaehlerIntermediateFieldLaurent ModularCurve.instIsScalarTowerIntermediateFieldLaurent ModularCurve.instModuleKaehlerIntermediateFieldLaurent AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois ModularCurve.Gamma0Pair.isElliptic ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.B3.instIsElliptic_goodModel AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar"
p2m_attr_erase "instance" "AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.instIsScalarTowerJAdjoin FLT.Gamma0FundamentalSet.instContinuousConstSMulSpecialLinearGroupFinOfNatNatIntUpperHalfPlane_definitions FLT.HyperbolicMeasure.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatIntUpperHalfPlaneVolume_definitions FLT.HyperbolicMeasure.instIsOpenPosMeasureUpperHalfPlaneVolume_definitions FLT.L2ProductionInstance.isFiniteMeasure_gamma0 FLT.L2ProductionInstance.countable_SL2Z FLT.L2ProductionInstance.countable_quotient FLT.L2ProductionInstance.nontrivial_gamma0L2 HeckeEis.instModuleCoeffH1par HeckeEis.instAddCommGroupCoeffH1par HeckeEis.instFiniteIndexHeckeUpper ModularCurve.Period.parabolicHoms_int_moduleFinite ModularCurve.Period.instGroupFG_SL2Z ModularCurve.Period.instIsNoetherian_addHom_int ModularCurve.Period.instGroupFG_Gamma0 AlgebraicCurve.CellDissection.fintypeV AlgebraicCurve.CellDissection.fintypeC"
p2m_attr_erase "instance" "AlgebraicCurve.CellDissection.fintypeE AlgebraicCurve.CellDissection.decEqV AlgebraicCurve.CellDissection.decEqC AlgebraicCurve.CellDissection.decEqE"
p2m_attr_erase "simp" "ModularCurve.dualHeckeRep_apply_apply ModularCurve.coe_segmentPath ModularCurve.cuspHeckeAeval_heckeGen ModularCurve.coe_periodLatticeRestrict_apply ModularCurve.Period.IsEquivariantPrimitive.periodHom_apply ModularCurve.Period.IsEquivariantPrimitive.period_one ModularCurve.cuspCount_one ModularCurve.CuspSpace.cuspDenomAux_infty ModularCurve.CuspSpace.cuspDenomAux_coe ModularCurve.CuspSpace.cuspDenom_mk_zero ModularCurve.CuspSpace.cuspDenom_mk_infty ModularCurve.mapGL_apply_coe ModularCurve.ratPoint_one_zero ModularCurve.ratPoint_zero_right ModularCurve.CuspSpace.fromCoset_mk ModularCurve.CuspSpace.cuspDenom_mk ModularCurve.ratPoint_zero_one ModularCurve.ProjectiveLine.map_mk ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.qEulerFun_coeff ModularCurve.diffQExp_D ModularCurve.qEulerOn_apply ModularCurve.qEuler_coeff AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord ModularCurve.coe_cuspidalDivisor₀ ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring"
p2m_attr_erase "simp" "ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.gamma0PairMap_gen ModularCurve.moduliPointMapRingHom_mk ModularCurve.Gamma0Pair.mk.injEq ModularCurve.ModuliPoint.j_mk ModularCurve.Gamma0Pair.mk.sizeOf_spec ModularCurve.gamma0PairMap_toCurve WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero WeierstrassCurve.ratPointHom_apply WeierstrassCurve.ratPointMap_zero ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.jqNModC_one WeierstrassCurve.veluX_empty WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty"
p2m_attr_erase "simp" "WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal"
p2m_attr_erase "simp" "AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one compl₂EDSAux_neg_two"
p2m_attr_erase "simp" "compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm"
p2m_attr_erase "simp" "AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply HahnSeries.ramScale_apply AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven"
p2m_attr_erase "simp" "ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar WeierstrassCurve.veluPointMap2_zero AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq ModularCurve.ComplexPlaceDictionary.mk.injEq"
p2m_attr_erase "simp" "ModularCurve.ComplexPlaceDictionary.mk.sizeOf_spec FLT.TruncatedDomainPartition.unipotentDiagonalSum_zero HeckeEis.coeffCoboundaryMap_apply HeckeEis.heckeConjMat_apply_one_one HeckeEis.coe_heckeConjSL HeckeEis.mem_heckeUpperSL HeckeEis.resHom_apply HeckeEis.heckeConjMat_apply_zero_one HeckeEis.coe_transferAux HeckeEis.coe_heckeConj HeckeEis.alphaMat_apply_one_one HeckeEis.heckeConjMat_apply_one_zero HeckeEis.alphaMat_apply_zero_one HeckeEis.pullbackHom_apply HeckeEis.alphaMat_apply_one_zero HeckeEis.alphaMat_apply_zero_zero HeckeEis.heckeConjMat_apply_zero_zero AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap ModularCurve.Period.jConjMat_apply_zero_one ModularCurve.Period.jConjSL_coe ModularCurve.Period.jConjMat_apply_one_zero ModularCurve.Period.jConjMat_apply_one_one ModularCurve.Period.jConjGamma0_coe ModularCurve.Period.charInvolution_apply ModularCurve.Period.jConjMat_apply_zero_zero PowerSeries.coeff_heckeV PowerSeries.coeff_heckeU AlgebraicCurve.abelJacobiDiv_single AlgebraicCurve.AnalyticCoord.mk.injEq AlgebraicCurve.Cell.mk.sizeOf_spec AlgebraicCurve.RadialRegion.mk.sizeOf_spec AlgebraicCurve.RadialRegion.mk.injEq AlgebraicCurve.CellDissection.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicCurve.Cell.mk.injEq AlgebraicCurve.CellDissection.mk.injEq AlgebraicCurve.AnalyticCoord.mk.sizeOf_spec"

open scoped TensorProduct

noncomputable section

namespace W6BTR

open Submodule in

theorem transfer_relation
    {P T E Ω F : Type} [Field F] [CharZero F]
    [AddCommGroup P] [AddCommGroup T] [AddCommGroup E] [Module F E]
    [AddCommGroup Ω] [Module F Ω]
    (α : P →+ T) (β : P →+ Ω) (hαβ : ∀ g, α g = 0 → β g = 0)
    (γ : T →+ E)
    (hγ : ∀ {ι : Type} (u : ι → T), LinearIndependent ℤ u → LinearIndependent F (fun i => γ (u i)))
    {κ : Type} [Fintype κ] (x : κ → P) (c : κ → F)
    (hf : ∑ k, c k • γ (α (x k)) = 0) :
    ∑ k, c k • β (x k) = 0 := by
  classical
  obtain ⟨s, hs, hmax⟩ := exists_maximal_linearIndepOn ℤ (fun k => α (x k))
  have hrel : ∀ k, ∃ r : ℤ, r ≠ 0 ∧ ∃ a : s → ℤ, ∑ j : s, a j • α (x j) = r • α (x k) := by
    intro k
    by_cases hk : k ∈ s
    · refine ⟨1, one_ne_zero, Pi.single ⟨k, hk⟩ 1, ?_⟩
      rw [one_smul, Finset.sum_eq_single ⟨k, hk⟩ (fun j _ hj => by rw [Pi.single_eq_of_ne hj, zero_smul])
        (fun h => absurd (Finset.mem_univ _) h), Pi.single_eq_same, one_smul]
    · obtain ⟨r, hr, hmem⟩ := hmax k hk
      rw [Set.image_eq_range] at hmem
      obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).1 hmem
      exact ⟨r, hr, a, ha⟩
  choose r hr a ha using hrel
  have hli : LinearIndependent F (fun j : s => γ (α (x j))) := hγ _ hs
  have hr' : ∀ k, (r k : F) ≠ 0 := fun k => Int.cast_ne_zero.2 (hr k)
  have hvan : ∀ k, α (∑ j : s, a k j • x j - r k • x k) = 0 := fun k => by
    rw [map_sub, map_sum, map_zsmul]
    simp_rw [map_zsmul]
    rw [ha, sub_self]
  have hγrel : ∀ k, γ (α (x k)) = (r k : F)⁻¹ • ∑ j : s, (a k j : F) • γ (α (x j)) := fun k => by
    rw [eq_inv_smul_iff₀ (hr' k), Int.cast_smul_eq_zsmul, ← map_zsmul, ← ha k, map_sum]
    simp_rw [map_zsmul, Int.cast_smul_eq_zsmul]
  have hβrel : ∀ k, β (x k) = (r k : F)⁻¹ • ∑ j : s, (a k j : F) • β (x j) := fun k => by
    have h := hαβ _ (hvan k)
    rw [map_sub, sub_eq_zero, map_sum, map_zsmul] at h
    rw [eq_inv_smul_iff₀ (hr' k), Int.cast_smul_eq_zsmul, ← h]
    simp_rw [map_zsmul, Int.cast_smul_eq_zsmul]
  set d : s → F := fun j => ∑ k, c k * ((r k : F)⁻¹ * (a k j : F)) with hd
  have key : ∀ {X : Type} [AddCommGroup X] [Module F X] (φ : κ → X) (ψ : s → X),
      (∀ k, φ k = (r k : F)⁻¹ • ∑ j : s, (a k j : F) • ψ j) →
        ∑ k, c k • φ k = ∑ j, d j • ψ j := by
    intro X _ _ φ ψ h
    calc ∑ k, c k • φ k = ∑ k, ∑ j, (c k * ((r k : F)⁻¹ * (a k j : F))) • ψ j := by
            refine Finset.sum_congr rfl fun k _ => ?_
            rw [h k, Finset.smul_sum, Finset.smul_sum]
            refine Finset.sum_congr rfl fun j _ => ?_
            rw [smul_smul, smul_smul, mul_assoc]
      _ = ∑ j, ∑ k, (c k * ((r k : F)⁻¹ * (a k j : F))) • ψ j := Finset.sum_comm
      _ = ∑ j, d j • ψ j := by
            refine Finset.sum_congr rfl fun j _ => ?_
            rw [hd, Finset.sum_smul]
  have hd0 : ∀ j, d j = 0 := by
    have h0 : ∑ j, d j • γ (α (x j)) = 0 := by
      rw [← key (fun k => γ (α (x k))) (fun j => γ (α (x j))) hγrel]
      exact hf
    exact Fintype.linearIndependent_iff.1 hli d h0
  rw [key (fun k => β (x k)) (fun j => β (x j)) hβrel]
  simp [hd0]

theorem aeval_eq_sum_coeff_smul {I F C : Type} [Field F] [CommRing C] [Algebra F C]
    (e : MvPolynomial I F →ₐ[F] C) (f : MvPolynomial I F) :
    e f = ∑ m ∈ f.support,
      MvPolynomial.coeff m f • e (MvPolynomial.map (Int.castRingHom F) (MvPolynomial.monomial m 1)) := by
  conv_lhs => rw [f.as_sum, map_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [MvPolynomial.map_monomial, map_one, ← map_smul, MvPolynomial.smul_monomial, smul_eq_mul,
    mul_one]

open ModularCurve

section Engine

variable (p : ℕ) [Fact p.Prime] (J : Type) [AddCommGroup J] [Module HeckeAlg J]

local notation "A" => rationalHeckeAlgebra p J
local notation "EndV" => Module.End ℚ_[p] (RationalTateModule p J)
local notation "Ann" => Module.annihilator HeckeAlg J

scoped instance isMulCommutative_A : IsMulCommutative A :=
  Algebra.isMulCommutative_adjoin ℚ_[p] (by
    rintro _ ⟨s, rfl⟩ _ ⟨t, rfl⟩
    rw [← map_mul, ← map_mul, mul_comm])

open scoped IsMulCommutative in
scoped instance instCommRingA : CommRing A := inferInstance

theorem rationalHeckeRep_eq_zero_of_mem {t : HeckeAlg} (ht : t ∈ Ann) :
    rationalHeckeRep p J t = 0 := by
  have h0 : tateHeckeRep p J t = 0 := by
    refine LinearMap.ext fun x => Subtype.ext (funext fun n => ?_)
    rw [coe_tateHeckeRep_apply_apply, LinearMap.zero_apply, TateModule.coe_zero, Pi.zero_apply]
    exact Module.mem_annihilator.1 ht _
  rw [rationalHeckeRep_apply, h0, LinearMap.baseChange_zero]

def gam : (HeckeAlg ⧸ Ann) →+* EndV :=
  Ideal.Quotient.lift Ann (rationalHeckeRep p J) (fun _ ht => rationalHeckeRep_eq_zero_of_mem p J ht)

theorem gam_mk (t : HeckeAlg) : gam p J (Ideal.Quotient.mk Ann t) = rationalHeckeRep p J t :=
  Ideal.Quotient.lift_mk _ _ _

variable [Module.Finite ℤ_[p] (TateModule p J)]

scoped instance instFiniteV : Module.Finite ℚ_[p] (RationalTateModule p J) := inferInstance

scoped instance instFiniteEndV : Module.Finite ℚ_[p] EndV := inferInstance

scoped instance instFiniteA : Module.Finite ℚ_[p] A :=
  Module.Finite.of_injective (Subalgebra.val A).toLinearMap Subtype.val_injective

theorem engine {I : Type} (v : I → Nat.Primes) (TS : Type) [CommRing TS] (g : I → TS)
    (hrel : ∀ f : MvPolynomial I ℤ,
      MvPolynomial.eval₂Hom (Int.castRingHom HeckeAlg) (fun i => heckeGen (v i)) f ∈ Ann →
        MvPolynomial.eval₂Hom (Int.castRingHom TS) g f = 0)
    (hfaith : ∀ {ι : Type} (t : ι → HeckeAlg),
      LinearIndependent ℤ (fun i => Ideal.Quotient.mk Ann (t i)) →
        LinearIndependent ℚ_[p] (fun i => rationalHeckeRep p J (t i)))
    (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra ℚ_[p] Ω] (χ : TS →+* Ω) :
    ∃ Λ : A →+* Ω, (∀ c : ℚ_[p], Λ (algebraMap ℚ_[p] A c) = algebraMap ℚ_[p] Ω c) ∧
      ∀ i : I, Λ ⟨rationalHeckeRep p J (heckeGen (v i)),
        rationalHeckeRep_mem_rationalHeckeAlgebra p J _⟩ = χ (g i) := by
  classical

  let rJ : MvPolynomial I ℤ →+* HeckeAlg :=
    MvPolynomial.eval₂Hom (Int.castRingHom HeckeAlg) (fun i => heckeGen (v i))
  let rS : MvPolynomial I ℤ →+* TS := MvPolynomial.eval₂Hom (Int.castRingHom TS) g
  let TV : I → A := fun i =>
    ⟨rationalHeckeRep p J (heckeGen (v i)), rationalHeckeRep_mem_rationalHeckeAlgebra p J _⟩
  let eV : MvPolynomial I ℚ_[p] →ₐ[ℚ_[p]] A := MvPolynomial.aeval TV
  let eχ : MvPolynomial I ℚ_[p] →ₐ[ℚ_[p]] Ω := MvPolynomial.aeval (fun i => χ (g i))
  have hrJ_X : ∀ i, rJ (MvPolynomial.X i) = heckeGen (v i) := fun i => MvPolynomial.eval₂_X _ _ _
  have hrS_X : ∀ i, rS (MvPolynomial.X i) = g i := fun i => MvPolynomial.eval₂_X _ _ _
  have heV_X : ∀ i, eV (MvPolynomial.X i) = TV i := fun i => MvPolynomial.aeval_X _ _
  have heχ_X : ∀ i, eχ (MvPolynomial.X i) = χ (g i) := fun i => MvPolynomial.aeval_X _ _

  have hE1 : ∀ f : MvPolynomial I ℤ,
      ((eV (MvPolynomial.map (Int.castRingHom ℚ_[p]) f) : A) : EndV)
        = rationalHeckeRep p J (rJ f) := by
    have key : ((Subalgebra.val A).toRingHom.comp
        (eV.toRingHom.comp (MvPolynomial.map (Int.castRingHom ℚ_[p]))))
          = (rationalHeckeRep p J).comp rJ := by
      refine MvPolynomial.ringHom_ext (fun r => ?_) (fun i => ?_)
      · rw [eq_intCast, map_intCast, map_intCast]
      · show ((eV (MvPolynomial.map (Int.castRingHom ℚ_[p]) (MvPolynomial.X i)) : A) : EndV)
          = rationalHeckeRep p J (rJ (MvPolynomial.X i))
        rw [MvPolynomial.map_X, heV_X, hrJ_X]
    intro f
    exact RingHom.congr_fun key f

  have hE2 : ∀ f : MvPolynomial I ℤ,
      eχ (MvPolynomial.map (Int.castRingHom ℚ_[p]) f) = χ (rS f) := by
    have key : (eχ.toRingHom.comp (MvPolynomial.map (Int.castRingHom ℚ_[p])))
        = χ.comp rS := by
      refine MvPolynomial.ringHom_ext (fun r => ?_) (fun i => ?_)
      · rw [eq_intCast, map_intCast, map_intCast]
      · show eχ (MvPolynomial.map (Int.castRingHom ℚ_[p]) (MvPolynomial.X i))
          = χ (rS (MvPolynomial.X i))
        rw [MvPolynomial.map_X, heχ_X, hrS_X]
    intro f
    exact RingHom.congr_fun key f

  have hker : ∀ f : MvPolynomial I ℚ_[p], eV f = 0 → eχ f = 0 := by
    intro f hf
    have hT := transfer_relation (F := ℚ_[p])
      (((Ideal.Quotient.mk Ann).comp rJ).toAddMonoidHom) ((χ.comp rS).toAddMonoidHom)
      (fun q hq => by
        have hq' : rJ q ∈ Ann := Ideal.Quotient.eq_zero_iff_mem.1 hq
        show χ (rS q) = 0
        rw [hrel q hq', map_zero])
      (gam p J).toAddMonoidHom
      (fun {ι} u hu => by
        choose t ht using fun i => Ideal.Quotient.mk_surjective (u i)
        have hu' : LinearIndependent ℤ (fun i => Ideal.Quotient.mk Ann (t i)) := by
          have : (fun i => Ideal.Quotient.mk Ann (t i)) = u := funext ht
          rw [this]; exact hu
        have h := hfaith t hu'
        have e : (fun i => (gam p J).toAddMonoidHom (u i)) = fun i => rationalHeckeRep p J (t i) := by
          funext i
          show gam p J (u i) = rationalHeckeRep p J (t i)
          rw [← ht i, gam_mk]
        rw [e]; exact h)
      (fun m : ↥f.support => (MvPolynomial.monomial (m : I →₀ ℕ) (1 : ℤ) : MvPolynomial I ℤ))
      (fun m => MvPolynomial.coeff (m : I →₀ ℕ) f)
      (by
        have h1 : ∀ m : ↥f.support,
            (gam p J).toAddMonoidHom ((((Ideal.Quotient.mk Ann).comp rJ).toAddMonoidHom)
              (MvPolynomial.monomial (m : I →₀ ℕ) (1 : ℤ)))
              = ((eV (MvPolynomial.map (Int.castRingHom ℚ_[p])
                  (MvPolynomial.monomial (m : I →₀ ℕ) 1)) : A) : EndV) := fun m => by
          show gam p J (Ideal.Quotient.mk Ann (rJ _)) = _
          rw [gam_mk, hE1]
        simp_rw [h1]
        rw [Finset.sum_coe_sort f.support (fun m => MvPolynomial.coeff m f •
          ((eV (MvPolynomial.map (Int.castRingHom ℚ_[p]) (MvPolynomial.monomial m 1)) : A) : EndV))]
        have h2 : ((eV f : A) : EndV) = 0 := by rw [hf]; rfl
        rw [aeval_eq_sum_coeff_smul eV f, AddSubmonoidClass.coe_finsetSum] at h2
        simpa only [Subalgebra.coe_smul] using h2)

    rw [aeval_eq_sum_coeff_smul eχ f, ← Finset.sum_coe_sort]
    refine Eq.trans (Finset.sum_congr rfl fun m _ => ?_) hT
    rw [hE2]
    rfl

  letI : Algebra (MvPolynomial I ℚ_[p]) A := eV.toRingHom.toAlgebra
  haveI : IsScalarTower ℚ_[p] (MvPolynomial I ℚ_[p]) A :=
    IsScalarTower.of_algebraMap_eq (fun c => (eV.commutes c).symm)
  haveI : Algebra.IsIntegral ℚ_[p] A := Algebra.IsIntegral.of_finite ℚ_[p] A
  haveI : Algebra.IsIntegral (MvPolynomial I ℚ_[p]) A := Algebra.IsIntegral.tower_top (R := ℚ_[p])
  have hker' : RingHom.ker (algebraMap (MvPolynomial I ℚ_[p]) (rationalHeckeAlgebra p J))
      ≤ RingHom.ker eχ.toRingHom := fun f hf => by
    rw [RingHom.mem_ker] at hf ⊢
    exact hker f hf
  obtain ⟨Λ, hΛ⟩ := RingHom.exists_comp_algebraMap_eq_of_isIntegral_of_isAlgClosed eχ.toRingHom hker'
  have hΛ' : ∀ f, Λ (eV f) = eχ f := fun f => RingHom.congr_fun hΛ f
  refine ⟨Λ, fun c => ?_, fun i => ?_⟩
  · rw [← eV.commutes c, hΛ', eχ.commutes]
  · rw [← heχ_X i, ← hΛ', heV_X]

end Engine

theorem mvPolynomial_int_ringHom_ext {σ R : Type} [Semiring R]
    {f g : MvPolynomial σ ℤ →+* R} (hX : ∀ i, f (MvPolynomial.X i) = g (MvPolynomial.X i)) :
    f = g :=
  MvPolynomial.ringHom_ext
    (fun r => RingHom.congr_fun (RingHom.ext_int (f.comp MvPolynomial.C) (g.comp MvPolynomial.C)) r)
    hX

theorem hrel_jZero (N : ℕ) [NeZero N] (hin : HeckeInputsAll N) (hcomm : HeckeOperatorsCommuteBar N)
    (S : Set ℕ) (f : MvPolynomial {ℓ : Nat.Primes // ¬ (ℓ : ℕ) ∣ N ∧ (ℓ : ℕ) ∉ S} ℤ)
    (hf : letI := heckeModuleBar N
      MvPolynomial.eval₂Hom (Int.castRingHom HeckeAlg) (fun i => heckeGen i.1) f
        ∈ Module.annihilator HeckeAlg (JZero N)) :
    MvPolynomial.eval₂Hom (Int.castRingHom ↥(CuspForm.heckeAlgebra N 2 S))
      (fun i => CuspForm.heckeAlgebra.T (k := 2) i.1.prop i.2.1 i.2.2) f = 0 := by
  letI := heckeModuleBar N
  obtain ⟨Φ, -, hΦ⟩ := exists_injective_ringHom_adjoin_heckeOperatorBar_cuspForm N hin hcomm

  obtain ⟨rJ, hrJ⟩ : ∃ rJ : MvPolynomial {ℓ : Nat.Primes // ¬ (ℓ : ℕ) ∣ N ∧ (ℓ : ℕ) ∉ S} ℤ
      →+* HeckeAlg, rJ = MvPolynomial.eval₂Hom (Int.castRingHom HeckeAlg) (fun i => heckeGen i.1) :=
    ⟨_, rfl⟩
  obtain ⟨rS, hrS⟩ : ∃ rS : MvPolynomial {ℓ : Nat.Primes // ¬ (ℓ : ℕ) ∣ N ∧ (ℓ : ℕ) ∉ S} ℤ
      →+* ↥(CuspForm.heckeAlgebra N 2 S), rS = MvPolynomial.eval₂Hom
        (Int.castRingHom ↥(CuspForm.heckeAlgebra N 2 S))
        (fun i => CuspForm.heckeAlgebra.T (k := 2) i.1.prop i.2.1 i.2.2) := ⟨_, rfl⟩
  rw [← hrJ] at hf
  rw [← hrS]
  have hrJ_X : ∀ i, rJ (MvPolynomial.X i) = heckeGen i.1 := fun i => by
    rw [hrJ]; exact MvPolynomial.eval₂_X _ _ _
  have hrS_X : ∀ i, rS (MvPolynomial.X i) = CuspForm.heckeAlgebra.T (k := 2) i.1.prop i.2.1 i.2.2 :=
    fun i => by rw [hrS]; exact MvPolynomial.eval₂_X _ _ _

  obtain ⟨ψ, hψ⟩ : ∃ ψ : MvPolynomial {ℓ : Nat.Primes // ¬ (ℓ : ℕ) ∣ N ∧ (ℓ : ℕ) ∉ S} ℤ →+*
      Module.End ℂ (CuspForm (CongruenceSubgroup.Gamma0 N) 2),
      ∀ q, ψ q = Φ (heckeEvalBarAux hcomm (rJ q)) :=
    ⟨Φ.comp ((heckeEvalBarAux hcomm).toRingHom.comp rJ), fun _ => rfl⟩
  obtain ⟨θ, hθ⟩ : ∃ θ : MvPolynomial {ℓ : Nat.Primes // ¬ (ℓ : ℕ) ∣ N ∧ (ℓ : ℕ) ∉ S} ℤ →+*
      Module.End ℂ (CuspForm (CongruenceSubgroup.Gamma0 N) 2),
      ∀ q, θ q = ((rS q : ↥(CuspForm.heckeAlgebra N 2 S)) :
        Module.End ℂ (CuspForm (CongruenceSubgroup.Gamma0 N) 2)) :=
    ⟨(CuspForm.heckeAlgebra N 2 S).val.toRingHom.comp rS, fun _ => rfl⟩
  have hψX : ∀ i, ψ (MvPolynomial.X i) = CuspForm.heckeTLin 2 i.1.prop i.2.1 := fun i => by
    rw [hψ]
    rw [hrJ_X i]
    have e := heckeEvalBarAux_heckeGen hcomm i.1
    exact (congrArg Φ e).trans (hΦ i.1 i.2.1)
  have hθX : ∀ i, θ (MvPolynomial.X i) = CuspForm.heckeTLin 2 i.1.prop i.2.1 := fun i => by
    rw [hθ, hrS_X i]
    rfl
  have key : ψ = θ := mvPolynomial_int_ringHom_ext fun i => (hψX i).trans (hθX i).symm
  have h1 : heckeEvalBar hcomm (rJ f) = 0 := by
    refine LinearMap.ext fun x => ?_
    rw [← heckeModuleBar_smul_def hcomm, LinearMap.zero_apply]
    exact Module.mem_annihilator.1 hf x
  have h2 : heckeEvalBarAux hcomm (rJ f) = 0 :=
    Subtype.ext ((heckeEvalBar_apply hcomm (rJ f)).symm.trans
      (h1.trans (ZeroMemClass.coe_zero _).symm))
  have h3 : Φ (heckeEvalBarAux hcomm (rJ f)) = ((rS f : ↥(CuspForm.heckeAlgebra N 2 S)) :
      Module.End ℂ (CuspForm (CongruenceSubgroup.Gamma0 N) 2)) :=
    (hψ f).symm.trans ((RingHom.congr_fun key f).trans (hθ f))
  have h4 : ((rS f : ↥(CuspForm.heckeAlgebra N 2 S)) :
      Module.End ℂ (CuspForm (CongruenceSubgroup.Gamma0 N) 2)) = 0 :=
    h3.symm.trans ((congrArg Φ h2).trans (map_zero Φ))
  exact Subtype.ext (h4.trans (ZeroMemClass.coe_zero _).symm)

end W6BTR

theorem solution
    (N p : ℕ) [NeZero N] [Fact p.Prime]
    (hin : ModularCurve.HeckeInputsAll N) (hcomm : ModularCurve.HeckeOperatorsCommuteBar N)
    (S : Set ℕ) (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra ℚ_[p] Ω]
    (χ : ↥(CuspForm.heckeAlgebra N 2 S) →+* Ω) :
    letI := ModularCurve.heckeModuleBar N
    ∃ Λ : ↥(ModularCurve.rationalHeckeAlgebra p (ModularCurve.JZero N)) →+* Ω,
      (∀ c : ℚ_[p],
        Λ (algebraMap ℚ_[p] ↥(ModularCurve.rationalHeckeAlgebra p (ModularCurve.JZero N)) c)
          = algebraMap ℚ_[p] Ω c) ∧
      ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (hℓS : ℓ ∉ S),
        Λ ⟨ModularCurve.rationalHeckeRep p (ModularCurve.JZero N) (ModularCurve.heckeGen ⟨ℓ, hℓ⟩),
            ModularCurve.rationalHeckeRep_mem_rationalHeckeAlgebra p (ModularCurve.JZero N) _⟩
          = χ (CuspForm.heckeAlgebra.T hℓ hℓN hℓS) := by
  letI := ModularCurve.heckeModuleBar N
  haveI : Module.Finite ℤ_[p] (TateModule p (ModularCurve.JZero N)) :=
    ModularCurve.moduleFinite_padicInt_tateModule_jZero N p

  have E1 := W6BTR.engine p (ModularCurve.JZero N)
    (I := {ℓ : Nat.Primes // ¬ (ℓ : ℕ) ∣ N ∧ (ℓ : ℕ) ∉ S}) (fun i => i.1)
    ↥(CuspForm.heckeAlgebra N 2 S) (fun i => CuspForm.heckeAlgebra.T (k := 2) i.1.prop i.2.1 i.2.2)
  have E2 := E1 (fun f hf => W6BTR.hrel_jZero N hin hcomm S f hf)
  have E3 := E2 (fun t ht =>
    ModularCurve.linearIndependent_rationalHeckeRep_of_linearIndependent N p hin hcomm t ht)
  have E4 := E3 Ω
  have E5 := E4 χ
  cases E5 with
  | intro Λ h =>
    have hc := h.1
    have hΛ := h.2
    refine ⟨Λ, ?_, ?_⟩
    · exact hc
    · intro ℓ hℓ hℓN hℓS
      have h1 := hΛ ⟨⟨ℓ, hℓ⟩, hℓN, hℓS⟩
      exact h1

end
end S_ModularCurve_exists_ringHom_rationalHeckeAlgebra_extends_heckeChar
end P2MW
export P2MW.S_ModularCurve_exists_ringHom_rationalHeckeAlgebra_extends_heckeChar (solution)
