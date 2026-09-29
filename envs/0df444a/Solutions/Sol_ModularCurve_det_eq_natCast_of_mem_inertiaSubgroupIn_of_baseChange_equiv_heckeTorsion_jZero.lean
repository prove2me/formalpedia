-- Prove2me | solution 1 for ModularCurve.det_eq_natCast_of_mem_inertiaSubgroupIn_of_baseChange_equiv_heckeTorsion_jZero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/c5ab8ca7-1abd-5745-9719-f772656c6b6c

import Mathlib
import Definitions.Def_ModularCurve_HeckeModule
import Definitions.Def_HeckeGalois_EichlerShimura
import Definitions.Def_GaloisRep_Residual
import Definitions.Def_FLTPrelim_Ramification
import Theorems.Thm_GaloisRep_det_eq_pow_of_forall_rootsOfUnity_of_det_frobenius_eq_pow
import Theorems.Thm_ModularCurve_frobeniusQuadratic_JZero
import Theorems.Thm_ModularCurve_heckeOperatorsCommuteBar
import Theorems.Thm_ModularCurve_mTorsionGaloisRep_jZero_galoisFactorsThroughFiniteLevel
import Theorems.Thm_ModularCurve_JZero_cardinalityAJ_genusFF
import Theorems.Thm_ModularCurve_JZero_finite_torsion_pow_of_cardinalityAJ
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_det_eq_natCast_of_mem_inertiaSubgroupIn_of_baseChange_equiv_heckeTorsion_jZero
p2m_attr_erase "instance" "AlgebraicClosure.Rat.isGalois FrobeniusDensity.isMaximal_ratPrimeIdeal FrobeniusDensity.liesOver_ratBelow AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation ModularCurve.instIsDomainTensorProduct CuspForm.heckeAlgebra.instCommRing CuspForm.heckeAlgebra.instIsMulCommutative CuspForm.heckeAlgebra.instIsAddTorsionFree ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue"
p2m_attr_erase "instance" "AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.CuspSpace.instNonempty ModularCurve.CuspSpace.instSubsingletonOfOne ModularCurve.CuspSpace.instFinite ModularCurve.instAlgebraIntermediateFieldLaurent ModularCurve.instIsScalarTowerKaehlerIntermediateFieldLaurent ModularCurve.instIsScalarTowerIntermediateFieldLaurent ModularCurve.instModuleKaehlerIntermediateFieldLaurent ModularCurve.Gamma0Pair.isElliptic ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.B3.instIsElliptic_goodModel ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar ModularCurve.instIsScalarTowerJAdjoin FLT.Gamma0FundamentalSet.instContinuousConstSMulSpecialLinearGroupFinOfNatNatIntUpperHalfPlane_definitions FLT.HyperbolicMeasure.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatIntUpperHalfPlaneVolume_definitions FLT.HyperbolicMeasure.instIsOpenPosMeasureUpperHalfPlaneVolume_definitions FLT.L2ProductionInstance.isFiniteMeasure_gamma0 FLT.L2ProductionInstance.countable_SL2Z FLT.L2ProductionInstance.countable_quotient FLT.L2ProductionInstance.nontrivial_gamma0L2 HeckeEis.instModuleCoeffH1par HeckeEis.instAddCommGroupCoeffH1par HeckeEis.instFiniteIndexHeckeUpper WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4"
p2m_attr_erase "instance" "ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular AlgebraicCurve.CellDissection.fintypeV AlgebraicCurve.CellDissection.fintypeC AlgebraicCurve.CellDissection.fintypeE AlgebraicCurve.CellDissection.decEqV AlgebraicCurve.CellDissection.decEqC AlgebraicCurve.CellDissection.decEqE"
p2m_attr_erase "simp" "TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong ModularCurve.qExpandAlgHomC_apply ModularCurve.jqNModC_one ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk"
p2m_attr_erase "simp" "ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_cuspidalDivisor₀ ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring"
p2m_attr_erase "simp" "ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.dualHeckeRep_apply_apply ModularCurve.coe_segmentPath ModularCurve.cuspHeckeAeval_heckeGen ModularCurve.coe_periodLatticeRestrict_apply CuspForm.heckeAlgebra.coe_U CuspForm.heckeAlgebra.coe_T ModularForm.coe_heckeTLin_apply CuspForm.coe_heckeULin_apply CuspForm.coe_heckeTLin_apply ModularForm.coe_heckeULin_apply ModularCurve.ComplexPlaceDictionary.mk.injEq ModularCurve.ComplexPlaceDictionary.mk.sizeOf_spec ModularCurve.Period.IsEquivariantPrimitive.periodHom_apply ModularCurve.Period.IsEquivariantPrimitive.period_one PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁"
p2m_attr_erase "simp" "PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ ModularCurve.ProjectiveLine.map_mk AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one"
p2m_attr_erase "simp" "AlgebraicCurve.Place.mem_poleSubmodule ModularCurve.cuspCount_one ModularCurve.CuspSpace.cuspDenomAux_infty ModularCurve.CuspSpace.cuspDenomAux_coe ModularCurve.CuspSpace.cuspDenom_mk_zero ModularCurve.CuspSpace.cuspDenom_mk_infty ModularCurve.mapGL_apply_coe ModularCurve.ratPoint_one_zero ModularCurve.ratPoint_zero_right ModularCurve.CuspSpace.fromCoset_mk ModularCurve.CuspSpace.cuspDenom_mk ModularCurve.ratPoint_zero_one ModularCurve.qEulerFun_coeff ModularCurve.diffQExp_D ModularCurve.qEulerOn_apply ModularCurve.qEuler_coeff ModularCurve.gamma0PairMap_gen ModularCurve.moduliPointMapRingHom_mk ModularCurve.Gamma0Pair.mk.injEq ModularCurve.ModuliPoint.j_mk ModularCurve.Gamma0Pair.mk.sizeOf_spec ModularCurve.gamma0PairMap_toCurve WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero WeierstrassCurve.ratPointHom_apply WeierstrassCurve.ratPointMap_zero ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ WeierstrassCurve.veluX_empty WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁"
p2m_attr_erase "simp" "WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one"
p2m_attr_erase "simp" "WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm WeierstrassCurve.veluQuotientOfSums_a₂"
p2m_attr_erase "simp" "WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply HahnSeries.ramScale_apply WeierstrassCurve.veluPointMap2_zero FLT.TruncatedDomainPartition.unipotentDiagonalSum_zero HeckeEis.coeffCoboundaryMap_apply HeckeEis.heckeConjMat_apply_one_one HeckeEis.coe_heckeConjSL HeckeEis.mem_heckeUpperSL HeckeEis.resHom_apply HeckeEis.heckeConjMat_apply_zero_one HeckeEis.coe_transferAux HeckeEis.coe_heckeConj HeckeEis.alphaMat_apply_one_one HeckeEis.heckeConjMat_apply_one_zero HeckeEis.alphaMat_apply_zero_one HeckeEis.pullbackHom_apply HeckeEis.alphaMat_apply_one_zero"
p2m_attr_erase "simp" "HeckeEis.alphaMat_apply_zero_zero HeckeEis.heckeConjMat_apply_zero_zero AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero"
p2m_attr_erase "simp" "TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff AlgebraicCurve.abelJacobiDiv_single AlgebraicCurve.AnalyticCoord.mk.injEq AlgebraicCurve.Cell.mk.sizeOf_spec AlgebraicCurve.RadialRegion.mk.sizeOf_spec AlgebraicCurve.RadialRegion.mk.injEq AlgebraicCurve.CellDissection.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicCurve.Cell.mk.injEq AlgebraicCurve.CellDissection.mk.injEq AlgebraicCurve.AnalyticCoord.mk.sizeOf_spec"

set_option autoImplicit false

open ModularCurve Polynomial

namespace SolD

theorem trace_eq_of_baseChange_equiv {R k V W : Type*} [CommRing R] [Field k] [Algebra R k]
    [AddCommGroup V] [Module R V] [Module.Free R V] [Module.Finite R V]
    [AddCommGroup W] [Module k W]
    (σ : Module.End R V) (ρ : Module.End k W) (e : TensorProduct R k V ≃ₗ[k] W)
    (he : ∀ (c : k) (v : V), e (c ⊗ₜ[R] σ v) = ρ (e (c ⊗ₜ[R] v))) :
    algebraMap R k (LinearMap.trace R V σ) = LinearMap.trace k W ρ := by
  have h1 : ρ = e.conj (σ.baseChange k) := by
    apply LinearMap.ext
    intro w
    obtain ⟨u, rfl⟩ := e.surjective w
    rw [LinearEquiv.conj_apply, LinearMap.comp_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.coe_coe, e.symm_apply_apply]
    induction u using TensorProduct.induction_on with
    | zero => simp only [LinearEquiv.map_zero, LinearMap.map_zero]
    | tmul c v => rw [LinearMap.baseChange_tmul]; exact (he c v).symm
    | add x y hx hy => simp only [LinearEquiv.map_add, LinearMap.map_add, hx, hy]
  rw [h1, LinearMap.trace_conj', LinearMap.trace_baseChange]

theorem finite_heckeTorsion (M : ℕ) [NeZero M] (p : ℕ) [Fact p.Prime] (𝔪 : Ideal HeckeAlg)
    (hp𝔪 : ((p : ℕ) : HeckeAlg) ∈ 𝔪) :
    letI := heckeModuleBar M
    Finite ↥(heckeTorsion (JZero M) 𝔪) := by
  letI := heckeModuleBar M
  have hfin := JZero.finite_torsion_pow_of_cardinalityAJ M p (JZero.cardinalityAJ_genusFF M p) 1
  rw [pow_one] at hfin
  let f : ↥(heckeTorsion (JZero M) 𝔪) →
      ↥(AlgebraicCurve.Pic0.torsion (AlgebraicClosure ℚ) (modularFunctionFieldBar M) p) :=
    fun x => ⟨(x : JZero M), by
      rw [AlgebraicCurve.Pic0.mem_torsion]
      have hx := (mem_heckeTorsion_iff (JZero M) 𝔪 x).mp x.2 _ hp𝔪
      have hC : ((p : ℕ) : HeckeAlg) = MvPolynomial.C (p : ℤ) := by simp
      rw [hC, heckeModuleBar_C_smul] at hx
      exact hx⟩
  exact Finite.of_injective f fun x y h => Subtype.ext (congrArg Subtype.val h :)

theorem cayleyHamilton_two {F W : Type*} [CommRing F] [Nontrivial F] [AddCommGroup W] [Module F W]
    [Module.Free F W] [Module.Finite F W] (h2 : Module.finrank F W = 2) (f : Module.End F W)
    (t : F) (ht : LinearMap.trace F W f = t) :
    f * f - t • f + LinearMap.det f • (1 : Module.End F W) = 0 := by
  classical
  let b := Module.finBasisOfFinrankEq F W h2
  have hcp : f.charpoly = X ^ 2 - C t * X + C (LinearMap.det f) := by
    rw [← f.charpoly_toMatrix b, Matrix.charpoly_fin_two, ← LinearMap.trace_eq_matrix_trace F b f,
      LinearMap.det_toMatrix b f, ht]
  have h := f.aeval_self_charpoly
  rw [hcp] at h
  simp only [map_add, map_sub, map_mul, map_pow, aeval_X, aeval_C] at h
  rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, smul_one_mul, sq] at h
  exact h

theorem det_eq_of_quadratic {F W : Type*} [CommRing F] [IsDomain F] [AddCommGroup W] [Module F W]
    [Module.Free F W] [Module.Finite F W] (h2 : Module.finrank F W = 2) (f : Module.End F W)
    (t c : F) (ht : LinearMap.trace F W f = t) (hq : ∀ v : W, f (f v) - t • f v + c • v = 0) :
    LinearMap.det f = c := by
  classical
  have hCH := cayleyHamilton_two h2 f t ht
  have hq' : f * f - t • f + c • (1 : Module.End F W) = 0 := by
    apply LinearMap.ext; intro v
    rw [LinearMap.zero_apply, LinearMap.add_apply, LinearMap.sub_apply, LinearMap.smul_apply,
      LinearMap.smul_apply, Module.End.mul_apply, Module.End.one_apply]
    exact hq v
  have hdiff : (c - LinearMap.det f) • (1 : Module.End F W) = 0 := by
    have := sub_eq_zero.mpr (hq'.trans hCH.symm)
    rw [sub_smul, ← this]
    abel
  let b := Module.finBasisOfFinrankEq F W h2
  have hv : (b 0 : W) ≠ 0 := b.ne_zero 0
  have hv0 : (c - LinearMap.det f) • (b 0) = 0 := by
    have := LinearMap.congr_fun hdiff (b 0)
    rwa [LinearMap.smul_apply, Module.End.one_apply, LinearMap.zero_apply] at this
  rcases smul_eq_zero.mp hv0 with h | h
  · exact (sub_eq_zero.mp h).symm
  · exact absurd h hv

end SolD

set_option maxHeartbeats 16000000 in
set_option synthInstance.maxHeartbeats 1600000 in
theorem solution
    (M : ℕ) [NeZero M] (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (hpM : ¬ p ∣ M)
    (𝔪 : Ideal HeckeAlg) [𝔪.IsMaximal] (hp𝔪 : ((p : ℕ) : HeckeAlg) ∈ 𝔪)
    {k : Type} [Field k] (ι : HeckeAlg ⧸ 𝔪 →+* k)
    (ρbar : ResidualGaloisRep k) (hirr : ρbar.IsAbsolutelyIrreducible) (S₀ : Finset ℕ)
    (hatt : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime), ℓ ∉ S₀ → ¬ ℓ ∣ M → ℓ ≠ p →
      ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime ℓ →
        ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, A.IsFrobeniusAt σ ℓ →
          LinearMap.trace k ρbar.V (ρbar.ρ σ) = ι (Ideal.Quotient.mk 𝔪 (heckeGen ⟨ℓ, hℓ⟩)))
    (hsmc : letI := heckeModuleBar M
      SMulCommClass (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) HeckeAlg (JZero M))
    (V : letI := heckeModuleBar M; Submodule (HeckeAlg ⧸ 𝔪) ↥(heckeTorsion (JZero M) 𝔪))
    (σV : letI := heckeModuleBar M; haveI := hsmc
      (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* Module.End (HeckeAlg ⧸ 𝔪) ↥V)
    (hσV : letI := heckeModuleBar M; haveI := hsmc
      ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (v : ↥V),
        ((σV σ v : ↥V) : ↥(heckeTorsion (JZero M) 𝔪)) =
          mTorsionGaloisRep (JZero M) 𝔪 σ (v : ↥(heckeTorsion (JZero M) 𝔪)))
    (hV2 : letI := heckeModuleBar M; Module.finrank (HeckeAlg ⧸ 𝔪) ↥V = 2)
    (e : letI := heckeModuleBar M; letI := ι.toAlgebra; TensorProduct (HeckeAlg ⧸ 𝔪) k ↥V ≃ₗ[k] ρbar.V)
    (he : letI := heckeModuleBar M; letI := ι.toAlgebra
      ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (c : k) (v : ↥V),
        e (c ⊗ₜ[HeckeAlg ⧸ 𝔪] σV σ v) = ρbar.ρ σ (e (c ⊗ₜ[HeckeAlg ⧸ 𝔪] v)))
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hσ : σ ∈ A.inertiaSubgroupIn ℚ)
    (a : ℕ) (ha : ∀ μ : AlgebraicClosure ℚ, μ ^ p = 1 → σ μ = μ ^ a) :
    letI := heckeModuleBar M; haveI := hsmc
    LinearMap.det ((σV σ : Module.End (HeckeAlg ⧸ 𝔪) ↥V) : ↥V →ₗ[HeckeAlg ⧸ 𝔪] ↥V) = (a : HeckeAlg ⧸ 𝔪) := by
  letI := heckeModuleBar M
  haveI := hsmc
  classical
  have hp0 : ((p : ℕ) : HeckeAlg ⧸ 𝔪) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk 𝔪) p, Ideal.Quotient.eq_zero_iff_mem]; exact hp𝔪
  haveI : CharP (HeckeAlg ⧸ 𝔪) p := (CharP.charP_iff_prime_eq_zero Fact.out).mpr hp0
  haveI : IsDomain (HeckeAlg ⧸ 𝔪) := Ideal.Quotient.isDomain 𝔪

  haveI hVfree : Module.Free (HeckeAlg ⧸ 𝔪) ↥V := by
    letI := Ideal.Quotient.field 𝔪
    exact Module.Free.of_divisionRing (HeckeAlg ⧸ 𝔪) ↥V
  haveI hVfin : Module.Finite (HeckeAlg ⧸ 𝔪) ↥V := Module.finite_of_finrank_eq_succ hV2
  have hιinj : Function.Injective ι := by
    letI := Ideal.Quotient.field 𝔪
    exact ι.injective
  have hcomm : HeckeOperatorsCommuteBar M := heckeOperatorsCommuteBar M
  let bV := Module.finBasisOfFinrankEq (HeckeAlg ⧸ 𝔪) ↥V hV2

  have hES : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime), ¬ ℓ ∣ M → ℓ ≠ p →
      ∀ B : ValuationSubring (AlgebraicClosure ℚ), B.LiesOverPrime ℓ →
        ∀ τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, B.IsFrobeniusAt τ ℓ →
          ∀ v : ↥V, σV τ (σV τ v) - (Ideal.Quotient.mk 𝔪 (heckeGen ⟨ℓ, hℓ⟩)) • σV τ v
            + (ℓ : HeckeAlg ⧸ 𝔪) • v = 0 := by
    intro ℓ hℓ hℓM hℓp B hB τ hτ v
    have hℓMp : ¬ ℓ ∣ M * p := by
      intro h
      rcases (Nat.Prime.dvd_mul hℓ).mp h with h | h
      · exact hℓM h
      · exact hℓp ((Nat.prime_dvd_prime_iff_eq hℓ Fact.out).mp h)
    have hx : ∃ n : ℕ, p ^ n • (((v : ↥(heckeTorsion (JZero M) 𝔪)) : JZero M)) = 0 := by
      refine ⟨1, ?_⟩
      have h := (mem_heckeTorsion_iff (JZero M) 𝔪 ((v : ↥(heckeTorsion (JZero M) 𝔪)) : JZero M)).mp
        (v : ↥(heckeTorsion (JZero M) 𝔪)).2 (p : HeckeAlg) hp𝔪
      rwa [Nat.cast_smul_eq_nsmul, ← pow_one p] at h
    have h := frobeniusQuadratic_JZero M p hcomm hsmc ℓ hℓ hℓMp B hB τ hτ _ hx

    apply Subtype.ext; apply Subtype.ext
    have e1 : (((σV τ (σV τ v) : ↥V) : ↥(heckeTorsion (JZero M) 𝔪)) : JZero M) =
        τ • τ • (((v : ↥(heckeTorsion (JZero M) 𝔪)) : JZero M)) := by
      rw [hσV, coe_mTorsionGaloisRep_apply, hσV, coe_mTorsionGaloisRep_apply]
    have e2 : ((((Ideal.Quotient.mk 𝔪 (heckeGen ⟨ℓ, hℓ⟩)) • σV τ v : ↥V) : ↥(heckeTorsion (JZero M) 𝔪)) : JZero M) =
        heckeGen ⟨ℓ, hℓ⟩ • (τ • (((v : ↥(heckeTorsion (JZero M) 𝔪)) : JZero M))) := by
      rw [Submodule.coe_smul, Submodule.torsionBySet.mk_smul, Submodule.coe_smul, hσV, coe_mTorsionGaloisRep_apply]
    have e3 : ((((ℓ : HeckeAlg ⧸ 𝔪) • v : ↥V) : ↥(heckeTorsion (JZero M) 𝔪)) : JZero M) =
        ℓ • (((v : ↥(heckeTorsion (JZero M) 𝔪)) : JZero M)) := by
      rw [Submodule.coe_smul, ← map_natCast (Ideal.Quotient.mk 𝔪) ℓ, Submodule.torsionBySet.mk_smul,
        Submodule.coe_smul, Nat.cast_smul_eq_nsmul]
    simp only [Submodule.coe_add, Submodule.coe_sub, Submodule.coe_zero]
    rw [e1, e2, e3]
    exact h

  have htr : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime), ℓ ∉ S₀ → ¬ ℓ ∣ M → ℓ ≠ p →
      ∀ B : ValuationSubring (AlgebraicClosure ℚ), B.LiesOverPrime ℓ →
        ∀ τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, B.IsFrobeniusAt τ ℓ →
          LinearMap.trace (HeckeAlg ⧸ 𝔪) ↥V (σV τ) = Ideal.Quotient.mk 𝔪 (heckeGen ⟨ℓ, hℓ⟩) := by
    intro ℓ hℓ hℓS hℓM hℓp B hB τ hτ
    apply hιinj
    rw [← hatt ℓ hℓ hℓS hℓM hℓp B hB τ hτ]
    have h := @SolD.trace_eq_of_baseChange_equiv (HeckeAlg ⧸ 𝔪) k ↥V ρbar.V _ _ ι.toAlgebra _ _ hVfree hVfin _ _
      (σV τ) (ρbar.ρ τ) e (he τ)
    rw [RingHom.algebraMap_toAlgebra] at h
    exact h

  have hdetFrob : ∀ (ℓ : ℕ), ℓ.Prime → ¬ ℓ ∣ M → ℓ ∉ (↑S₀ : Set ℕ) → ℓ ≠ p →
      ∀ B : ValuationSubring (AlgebraicClosure ℚ), B.LiesOverPrime ℓ →
        ∀ τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, B.IsFrobeniusAt τ ℓ →
          LinearMap.det ((σV τ : Module.End (HeckeAlg ⧸ 𝔪) ↥V) : ↥V →ₗ[HeckeAlg ⧸ 𝔪] ↥V) =
            (ℓ : HeckeAlg ⧸ 𝔪) := by
    intro ℓ hℓ hℓM hℓS hℓp B hB τ hτ
    exact SolD.det_eq_of_quadratic hV2 (σV τ) _ _ (htr ℓ hℓ hℓS hℓM hℓp B hB τ hτ) (hES ℓ hℓ hℓM hℓp B hB τ hτ)

  letI instF : Field (HeckeAlg ⧸ 𝔪) := Ideal.Quotient.field 𝔪
  let toM : Module.End (HeckeAlg ⧸ 𝔪) ↥V →* Matrix (Fin 2) (Fin 2) (HeckeAlg ⧸ 𝔪) :=
    (LinearMap.toMatrixAlgEquiv bV : Module.End (HeckeAlg ⧸ 𝔪) ↥V ≃ₐ[HeckeAlg ⧸ 𝔪] _).toMonoidHom
  let ρM : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* GL (Fin 2) (HeckeAlg ⧸ 𝔪) :=
    (toM.comp σV).toHomUnits
  have hρM : ∀ g, (ρM g).val = LinearMap.toMatrix bV bV (σV g) := fun g => rfl
  have hdetM : ∀ g, Matrix.det (ρM g).val =
      LinearMap.det ((σV g : Module.End (HeckeAlg ⧸ 𝔪) ↥V) : ↥V →ₗ[HeckeAlg ⧸ 𝔪] ↥V) := by
    intro g; rw [hρM, LinearMap.det_toMatrix]
  have hfinJ : Finite ↥(heckeTorsion (JZero M) 𝔪) := SolD.finite_heckeTorsion M p 𝔪 hp𝔪
  have hlevel : GaloisFactorsThroughFiniteLevel ρM := by
    obtain ⟨L, hL, hLfix⟩ := mTorsionGaloisRep_jZero_galoisFactorsThroughFiniteLevel M 𝔪 hsmc hfinJ
    refine ⟨L, hL, fun g hg => ?_⟩
    have h1 := hLfix g hg
    have hσ1 : σV g = 1 := by
      apply LinearMap.ext; intro v; apply Subtype.ext
      rw [hσV, h1]; rfl
    apply Units.ext
    show toM (σV g) = 1
    rw [hσ1, map_one]
  have hcheb := GaloisRep.det_eq_pow_of_forall_rootsOfUnity_of_det_frobenius_eq_pow p M (↑S₀ : Set ℕ)
    S₀.finite_toSet 1 ρM hlevel
    (fun ℓ hℓ hℓM hℓS hℓp B hB τ hτ => by rw [pow_one, hdetM]; exact hdetFrob ℓ hℓ hℓM hℓS hℓp B hB τ hτ)
    A hA σ hσ a ha
  rw [pow_one, hdetM] at hcheb
  exact hcheb

end S_ModularCurve_det_eq_natCast_of_mem_inertiaSubgroupIn_of_baseChange_equiv_heckeTorsion_jZero
end P2MW
export P2MW.S_ModularCurve_det_eq_natCast_of_mem_inertiaSubgroupIn_of_baseChange_equiv_heckeTorsion_jZero (solution)
