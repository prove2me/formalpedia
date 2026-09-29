-- Prove2me | solution 1 for ModularCurve.residualRealization_of_occurs
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/3c593def-1078-5e5f-b20f-17c26ccc098a

import Mathlib
import Definitions.Def_ModularCurve_JZeroTateModule
import Definitions.Def_ModularCurve_ResidualRealization
import Definitions.Def_ModularCurve_HeckeModule
import Theorems.Thm_ModularCurve_rationalRankTwoCyclotomic_family
import Theorems.Thm_ModularCurve_JZero_torsion_fixed_by_open
import Theorems.Thm_ModularCurve_JZero_exists_abelJacobiCard
import Theorems.Thm_ModularCurve_heckeOperatorsCommuteBar
import Theorems.Thm_ModularCurve_smulCommClass_JZero_of_heckeOperatorsCommuteBar
import Theorems.Thm_RingHom_exists_comp_algebraMap_eq_of_isIntegral_of_isAlgClosed
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_residualRealization_of_occurs
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois CuspForm.heckeAlgebra.instCommRing CuspForm.heckeAlgebra.instIsMulCommutative CuspForm.heckeAlgebra.instIsAddTorsionFree ModularCurve.CuspSpace.instNonempty ModularCurve.CuspSpace.instSubsingletonOfOne ModularCurve.CuspSpace.instFinite ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.instAlgebraIntermediateFieldLaurent ModularCurve.instIsScalarTowerKaehlerIntermediateFieldLaurent ModularCurve.instIsScalarTowerIntermediateFieldLaurent ModularCurve.instModuleKaehlerIntermediateFieldLaurent ModularCurve.Gamma0Pair.isElliptic ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.B3.instIsElliptic_goodModel"
p2m_attr_erase "instance" "AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.instIsScalarTowerJAdjoin HeckeEis.instFiniteIndexHeckeUpper ModularCurve.Period.parabolicHoms_int_moduleFinite ModularCurve.Period.instGroupFG_SL2Z ModularCurve.Period.instIsNoetherian_addHom_int ModularCurve.Period.instGroupFG_Gamma0 FLT.Gamma0FundamentalSet.instContinuousConstSMulSpecialLinearGroupFinOfNatNatIntUpperHalfPlane_definitions FLT.HyperbolicMeasure.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatIntUpperHalfPlaneVolume_definitions FLT.HyperbolicMeasure.instIsOpenPosMeasureUpperHalfPlaneVolume_definitions FLT.L2ProductionInstance.isFiniteMeasure_gamma0 FLT.L2ProductionInstance.countable_SL2Z FLT.L2ProductionInstance.countable_quotient FLT.L2ProductionInstance.nontrivial_gamma0L2 HeckeEis.instModuleCoeffH1par"
p2m_attr_erase "instance" "HeckeEis.instAddCommGroupCoeffH1par AlgebraicCurve.CellDissection.fintypeV AlgebraicCurve.CellDissection.fintypeC AlgebraicCurve.CellDissection.fintypeE AlgebraicCurve.CellDissection.decEqV AlgebraicCurve.CellDissection.decEqC AlgebraicCurve.CellDissection.decEqE"
p2m_attr_erase "simp" "ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff"
p2m_attr_erase "simp" "ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_cuspidalDivisor₀ ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five"
p2m_attr_erase "simp" "ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.dualHeckeRep_apply_apply ModularCurve.coe_segmentPath ModularCurve.cuspHeckeAeval_heckeGen ModularCurve.coe_periodLatticeRestrict_apply CuspForm.heckeAlgebra.coe_U CuspForm.heckeAlgebra.coe_T ModularForm.coe_heckeTLin_apply CuspForm.coe_heckeULin_apply CuspForm.coe_heckeTLin_apply ModularForm.coe_heckeULin_apply ModularCurve.Period.IsEquivariantPrimitive.periodHom_apply ModularCurve.Period.IsEquivariantPrimitive.period_one ModularCurve.cuspCount_one ModularCurve.CuspSpace.cuspDenomAux_infty ModularCurve.CuspSpace.cuspDenomAux_coe ModularCurve.CuspSpace.cuspDenom_mk_zero ModularCurve.CuspSpace.cuspDenom_mk_infty ModularCurve.mapGL_apply_coe ModularCurve.ratPoint_one_zero ModularCurve.ratPoint_zero_right ModularCurve.CuspSpace.fromCoset_mk ModularCurve.CuspSpace.cuspDenom_mk ModularCurve.ratPoint_zero_one ModularCurve.ProjectiveLine.map_mk ModularCurve.qEulerFun_coeff ModularCurve.diffQExp_D ModularCurve.qEulerOn_apply ModularCurve.qEuler_coeff AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord ModularCurve.gamma0PairMap_gen ModularCurve.moduliPointMapRingHom_mk ModularCurve.Gamma0Pair.mk.injEq ModularCurve.ModuliPoint.j_mk ModularCurve.Gamma0Pair.mk.sizeOf_spec ModularCurve.gamma0PairMap_toCurve"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero WeierstrassCurve.ratPointHom_apply WeierstrassCurve.ratPointMap_zero ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ WeierstrassCurve.veluX_empty WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg"
p2m_attr_erase "simp" "WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero"
p2m_attr_erase "simp" "ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply HahnSeries.ramScale_apply AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none WeierstrassCurve.veluPointMap2_zero AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule"
p2m_attr_erase "simp" "AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule ModularCurve.Period.jConjMat_apply_zero_one ModularCurve.Period.jConjSL_coe ModularCurve.Period.jConjMat_apply_one_zero ModularCurve.Period.jConjMat_apply_one_one ModularCurve.Period.jConjGamma0_coe ModularCurve.Period.charInvolution_apply ModularCurve.Period.jConjMat_apply_zero_zero HeckeEis.heckeConjMat_apply_one_one HeckeEis.coe_heckeConjSL HeckeEis.mem_heckeUpperSL HeckeEis.resHom_apply HeckeEis.heckeConjMat_apply_zero_one HeckeEis.coe_transferAux HeckeEis.coe_heckeConj HeckeEis.alphaMat_apply_one_one HeckeEis.heckeConjMat_apply_one_zero HeckeEis.alphaMat_apply_zero_one HeckeEis.pullbackHom_apply HeckeEis.alphaMat_apply_one_zero HeckeEis.alphaMat_apply_zero_zero HeckeEis.heckeConjMat_apply_zero_zero PowerSeries.coeff_heckeV PowerSeries.coeff_heckeU AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq ModularCurve.ComplexPlaceDictionary.mk.injEq ModularCurve.ComplexPlaceDictionary.mk.sizeOf_spec FLT.TruncatedDomainPartition.unipotentDiagonalSum_zero"
p2m_attr_erase "simp" "HeckeEis.coeffCoboundaryMap_apply AlgebraicCurve.DivisorialWeilPairingData.toChar_apply AlgebraicCurve.WeilDatum.coe_classRight AlgebraicCurve.WeilDatum.coe_degZeroRight AlgebraicCurve.DivisorialWeilPairingData.mk.sizeOf_spec AlgebraicCurve.WeilDatum.coe_classLeft AlgebraicCurve.WeilDatum.coe_degZeroLeft AlgebraicCurve.DivisorialWeilPairingData.mk.injEq AlgebraicCurve.DivisorialWeilPairingData.toHom_apply_apply AlgebraicCurve.WeilDatum.mk.sizeOf_spec AlgebraicCurve.WeilDatum.mk.injEq AlgebraicCurve.WeilPairingData.evalAddChar_zero AlgebraicCurve.PrincipalPolarization.mk.injEq AlgebraicCurve.WeilPairingData.evalAddChar_apply AlgebraicCurve.H1Gm.degree_ofPic0 AlgebraicCurve.WeilPairingData.mk.sizeOf_spec AlgebraicCurve.HomPic0Gm.map_one AlgebraicCurve.PrincipalPolarization.mk.sizeOf_spec AlgebraicCurve.WeilPairingData.autodualityEquiv_apply AlgebraicCurve.WeilPairingData.eval_zero_right AlgebraicCurve.H1Gm.ofPic0_mk AlgebraicCurve.WeilPairingData.eval_neg_left AlgebraicCurve.HomPic0Gm.map_apply AlgebraicCurve.H1Gm.degree_mk AlgebraicCurve.HomPic0Gm.map_id AlgebraicCurve.WeilPairingData.mk.injEq AlgebraicCurve.WeilPairingData.congr_eval AlgebraicCurve.WeilPairingData.eval_neg_right AlgebraicCurve.WeilPairingData.eval_zero_left AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap ModularCurve.tateMap_apply AlgebraicCurve.abelJacobiDiv_single AlgebraicCurve.AnalyticCoord.mk.injEq"
p2m_attr_erase "simp" "AlgebraicCurve.Cell.mk.sizeOf_spec AlgebraicCurve.RadialRegion.mk.sizeOf_spec AlgebraicCurve.RadialRegion.mk.injEq AlgebraicCurve.CellDissection.mk.sizeOf_spec AlgebraicCurve.Cell.mk.injEq AlgebraicCurve.CellDissection.mk.injEq AlgebraicCurve.AnalyticCoord.mk.sizeOf_spec"
set_option Elab.async false

set_option autoImplicit false

noncomputable section

open scoped TensorProduct

namespace ModularCurve
p2m_export "ModularCurve" "tateHeckeRep coe_tateHeckeRep_apply_apply RationalTateModule rationalGaloisRep rationalGaloisRep_apply rationalHeckeRep rationalHeckeRep_apply rationalHeckeRep_tmul rationalHeckeAlgebra rationalHeckeRep_mem_rationalHeckeAlgebra RationalRankTwoCyclotomicOf RationalRankTwoCyclotomic modularFunctionFieldBar JZero HeckeAlg heckeTorsion IsResidualRealization CyclotomicDeterminant heckeModuleBar rationalRankTwoCyclotomic_family JZero.torsion_fixed_by_open JZero.exists_abelJacobiCard heckeOperatorsCommuteBar smulCommClass_JZero_of_heckeOperatorsCommuteBar"
p2m_open "ModularCurve~baseChangeHom~baseChangeHom_injective"

namespace X4IntegralSide

variable (p : ℕ) [Fact p.Prime] (J : Type) [AddCommGroup J] [Module HeckeAlg J]

omit [Module HeckeAlg J] in

theorem eq_zero_of_natCast_smul_eq_zero (x : TateModule p J) (h : (p : ℤ_[p]) • x = 0) : x = 0 := by
  refine Subtype.ext (funext fun n => ?_)
  have h1 : ((((p : ℕ) : ℤ_[p]) • x : TateModule p J) : ℕ → J) (n + 1) = 0 := by
    rw [h, TateModule.coe_zero, Pi.zero_apply]
  rw [TateModule.natCast_padicInt_smul_apply, TateModule.compat] at h1
  rw [h1, TateModule.coe_zero, Pi.zero_apply]

omit [Module HeckeAlg J] in
theorem eq_zero_of_pow_smul_eq_zero (n : ℕ) (x : TateModule p J) (h : (p : ℤ_[p]) ^ n • x = 0) :
    x = 0 := by
  induction n generalizing x with
  | zero => rwa [pow_zero, one_smul] at h
  | succ n ih =>
    rw [pow_succ, mul_smul] at h
    exact eq_zero_of_natCast_smul_eq_zero p J x (ih ((p : ℤ_[p]) • x) h)

omit [Module HeckeAlg J] in

scoped instance noZeroSMulDivisors_tateModule : NoZeroSMulDivisors ℤ_[p] (TateModule p J) :=
  ⟨fun {c x} h => or_iff_not_imp_left.2 fun hc => by
    rw [PadicInt.unitCoeff_spec hc, mul_smul] at h
    exact eq_zero_of_pow_smul_eq_zero p J _ x ((Units.isUnit _).smul_eq_zero.1 h)⟩

omit [Module HeckeAlg J] in

theorem mk_one_injective :
    Function.Injective (TensorProduct.mk ℤ_[p] ℚ_[p] (TateModule p J) 1) := by
  refine (injective_iff_map_eq_zero _).2 fun x hx => ?_
  obtain ⟨s, hs⟩ := (IsLocalizedModule.eq_zero_iff (nonZeroDivisors ℤ_[p])
    (f := TensorProduct.mk ℤ_[p] ℚ_[p] (TateModule p J) 1)).1 hx
  rw [Submonoid.smul_def] at hs
  exact (smul_eq_zero.1 hs).resolve_left (nonZeroDivisors.coe_ne_zero s)

omit [Module HeckeAlg J] in

theorem baseChangeHom_injective :
    Function.Injective (Module.End.baseChangeHom ℤ_[p] ℚ_[p] (TateModule p J)) := by
  refine (injective_iff_map_eq_zero _).2 fun f hf => LinearMap.ext fun x => mk_one_injective p J ?_
  have h1 := LinearMap.congr_fun hf ((1 : ℚ_[p]) ⊗ₜ[ℤ_[p]] x)
  rw [LinearMap.zero_apply] at h1
  rw [LinearMap.zero_apply, TensorProduct.mk_apply, TensorProduct.mk_apply, TensorProduct.tmul_zero]
  exact h1

def integralHeckeAlgebra : Subalgebra ℤ_[p] (Module.End ℤ_[p] (TateModule p J)) :=
  Algebra.adjoin ℤ_[p] (Set.range (tateHeckeRep p J))

theorem tateHeckeRep_mem_integralHeckeAlgebra (t : HeckeAlg) :
    tateHeckeRep p J t ∈ integralHeckeAlgebra p J :=
  Algebra.subset_adjoin (Set.mem_range_self t)

def heckeToIntegralHeckeAlgebra : HeckeAlg →+* integralHeckeAlgebra p J :=
  (tateHeckeRep p J).codRestrict (integralHeckeAlgebra p J)
    (tateHeckeRep_mem_integralHeckeAlgebra p J)

@[scoped simp]
theorem coe_heckeToIntegralHeckeAlgebra (t : HeckeAlg) :
    (heckeToIntegralHeckeAlgebra p J t : Module.End ℤ_[p] (TateModule p J)) = tateHeckeRep p J t :=
  rfl

scoped instance isMulCommutative_integralHeckeAlgebra : IsMulCommutative (integralHeckeAlgebra p J) :=
  Algebra.isMulCommutative_adjoin ℤ_[p] (by
    rintro _ ⟨s, rfl⟩ _ ⟨t, rfl⟩
    rw [← map_mul, ← map_mul, mul_comm])

example : Module (integralHeckeAlgebra p J) (TateModule p J) := inferInstance
set_option synthInstance.maxHeartbeats 320000 in
example : IsScalarTower ℤ_[p] (integralHeckeAlgebra p J) (TateModule p J) := inferInstance

theorem integralHeckeAlgebra_smul_def (a : integralHeckeAlgebra p J) (x : TateModule p J) :
    a • x = (a : Module.End ℤ_[p] (TateModule p J)) x :=
  rfl

theorem baseChangeHom_mem_rationalHeckeAlgebra (a : integralHeckeAlgebra p J) :
    Module.End.baseChangeHom ℤ_[p] ℚ_[p] (TateModule p J) a ∈ rationalHeckeAlgebra p J := by
  obtain ⟨a, ha⟩ := a
  refine Algebra.adjoin_induction (fun x hx => ?_) (fun r => ?_) (fun x y _ _ hx hy => ?_)
    (fun x y _ _ hx hy => ?_) ha
  · obtain ⟨t, rfl⟩ := hx
    exact rationalHeckeRep_mem_rationalHeckeAlgebra p J t
  · rw [AlgHom.commutes, Algebra.algebraMap_eq_smul_one,
      ← algebraMap_smul ℚ_[p] r (1 : Module.End ℚ_[p] (RationalTateModule p J)),
      ← Algebra.algebraMap_eq_smul_one]
    exact Subalgebra.algebraMap_mem _ _
  · rw [map_add]; exact Subalgebra.add_mem _ hx hy
  · rw [map_mul]; exact Subalgebra.mul_mem _ hx hy

def integralToRationalHeckeAlgebra : integralHeckeAlgebra p J →+* rationalHeckeAlgebra p J :=
  ((Module.End.baseChangeHom ℤ_[p] ℚ_[p] (TateModule p J)).toRingHom.comp
      (integralHeckeAlgebra p J).val.toRingHom).codRestrict (rationalHeckeAlgebra p J)
    (fun a => baseChangeHom_mem_rationalHeckeAlgebra p J a)

theorem integralToRationalHeckeAlgebra_heckeTo (t : HeckeAlg) :
    (integralToRationalHeckeAlgebra p J (heckeToIntegralHeckeAlgebra p J t) :
        Module.End ℚ_[p] (RationalTateModule p J)) = rationalHeckeRep p J t :=
  rfl

theorem coe_integralToRationalHeckeAlgebra (a : integralHeckeAlgebra p J) :
    (integralToRationalHeckeAlgebra p J a : Module.End ℚ_[p] (RationalTateModule p J))
      = Module.End.baseChangeHom ℤ_[p] ℚ_[p] (TateModule p J) a :=
  rfl

theorem integralToRationalHeckeAlgebra_injective :
    Function.Injective (integralToRationalHeckeAlgebra p J) := fun a b h =>
  Subtype.ext (baseChangeHom_injective p J
    (show Module.End.baseChangeHom ℤ_[p] ℚ_[p] (TateModule p J) a
        = Module.End.baseChangeHom ℤ_[p] ℚ_[p] (TateModule p J) b from congrArg Subtype.val h))

scoped instance finite_integralHeckeAlgebra [Module.Finite ℤ_[p] (TateModule p J)]
    [Module.Free ℤ_[p] (TateModule p J)] : Module.Finite ℤ_[p] (integralHeckeAlgebra p J) :=
  Module.Finite.of_injective (integralHeckeAlgebra p J).val.toLinearMap Subtype.val_injective

theorem ker_eq_torsionOf (k : Type) [Field k] (φ : HeckeAlg →+* k)
    (hmax : (RingHom.ker φ).IsMaximal) {x₀ : J}
    (hx₀ : x₀ ∈ Submodule.torsionBySet HeckeAlg J ((RingHom.ker φ : Ideal HeckeAlg) : Set HeckeAlg))
    (hx₀ne : x₀ ≠ 0) : RingHom.ker φ = Ideal.torsionOf HeckeAlg J x₀ := by
  rw [Submodule.mem_torsionBySet_iff] at hx₀
  refine hmax.eq_of_le (fun h1 => hx₀ne ?_) (fun a ha => ?_)
  · have h := (Ideal.mem_torsionOf_iff x₀ (1 : HeckeAlg)).1 (h1 ▸ Submodule.mem_top)
    rwa [one_smul] at h
  · exact (Ideal.mem_torsionOf_iff x₀ a).2 (hx₀ ⟨a, ha⟩)

omit [Fact p.Prime] in

theorem mem_torsionBy_of_mem_torsionBySet (k : Type) [Field k] (φ : HeckeAlg →+* k)
    (hp : (p : k) = 0) {x₀ : J}
    (hx₀ : x₀ ∈ Submodule.torsionBySet HeckeAlg J ((RingHom.ker φ : Ideal HeckeAlg) : Set HeckeAlg)) :
    x₀ ∈ Submodule.torsionBy ℤ J ((p ^ 1 : ℕ) : ℤ) := by
  rw [Submodule.mem_torsionBySet_iff] at hx₀
  refine (Submodule.mem_torsionBy_iff _ _).2 ?_
  have hpk : ((p : ℕ) : HeckeAlg) ∈ RingHom.ker φ := by
    rw [RingHom.mem_ker, map_natCast, hp]
  have h := hx₀ ⟨_, hpk⟩
  rw [Nat.cast_smul_eq_nsmul] at h
  rw [pow_one, Nat.cast_smul_eq_nsmul]
  exact h

theorem ker_heckeToIntegralHeckeAlgebra_le
    (hsurj : ∀ m ∈ Submodule.torsionBy ℤ J ((p ^ 1 : ℕ) : ℤ),
      ∃ x : TateModule p J, TateModule.proj p J 1 x = m)
    (k : Type) [Field k] (φ : HeckeAlg →+* k) (hp : (p : k) = 0)
    (hmax : (RingHom.ker φ).IsMaximal)
    (hocc : Submodule.torsionBySet HeckeAlg J ((RingHom.ker φ : Ideal HeckeAlg) : Set HeckeAlg) ≠ ⊥) :
    RingHom.ker (heckeToIntegralHeckeAlgebra p J) ≤ RingHom.ker φ := by
  intro t ht
  obtain ⟨x₀, hx₀, hx₀ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hocc
  have hann := ker_eq_torsionOf J k φ hmax hx₀ hx₀ne
  obtain ⟨x, hx⟩ := hsurj x₀ (mem_torsionBy_of_mem_torsionBySet p J k φ hp hx₀)

  have htx₀ : t • x₀ = 0 := by
    have ht0 : tateHeckeRep p J t = 0 := by
      have := congrArg Subtype.val (RingHom.mem_ker.1 ht)
      exact this
    have key : TateModule.proj p J 1 (tateHeckeRep p J t x) = t • TateModule.proj p J 1 x := rfl
    rw [← hx, ← key, ht0, LinearMap.zero_apply, map_zero]
  rw [hann]
  exact (Ideal.mem_torsionOf_iff x₀ t).2 htx₀

theorem algebraMap_padicInt_eq_natCast_appr (k : Type) [Field k] [Algebra ℤ_[p] k]
    (hp : (p : k) = 0) (c : ℤ_[p]) : algebraMap ℤ_[p] k c = ((c.appr 1 : ℕ) : k) := by
  obtain ⟨d, hd⟩ := Ideal.mem_span_singleton'.1 (PadicInt.appr_spec 1 c)
  have hc : c = ((c.appr 1 : ℕ) : ℤ_[p]) + d * (p : ℤ_[p]) ^ 1 := by rw [hd, add_sub_cancel]
  conv_lhs => rw [hc]
  rw [map_add, map_natCast, map_mul, map_pow, map_natCast, hp, pow_one, mul_zero, add_zero]

def IntegralHeckeRing : Type :=
  integralHeckeAlgebra p J

scoped instance commRing_integralHeckeRing : CommRing (IntegralHeckeRing p J) where
  toRing := inferInstanceAs (Ring (integralHeckeAlgebra p J))
  mul_comm a b := (isMulCommutative_integralHeckeAlgebra p J).is_comm.comm a b

scoped instance algebra_integralHeckeRing : Algebra ℤ_[p] (IntegralHeckeRing p J) :=
  inferInstanceAs (Algebra ℤ_[p] (integralHeckeAlgebra p J))

scoped instance module_integralHeckeRing : Module (IntegralHeckeRing p J) (TateModule p J) :=
  inferInstanceAs (Module (integralHeckeAlgebra p J) (TateModule p J))

set_option synthInstance.maxHeartbeats 320000 in
scoped instance isScalarTower_integralHeckeRing :
    IsScalarTower ℤ_[p] (IntegralHeckeRing p J) (TateModule p J) :=
  inferInstanceAs (IsScalarTower ℤ_[p] (integralHeckeAlgebra p J) (TateModule p J))

def IntegralHeckeRing.ofSubalgebra : integralHeckeAlgebra p J ≃+* IntegralHeckeRing p J :=
  RingEquiv.refl _

def IntegralHeckeRing.algEquiv : integralHeckeAlgebra p J ≃ₐ[ℤ_[p]] IntegralHeckeRing p J :=
  AlgEquiv.refl

theorem IntegralHeckeRing.smul_def (a : IntegralHeckeRing p J) (x : TateModule p J) :
    a • x = ((IntegralHeckeRing.ofSubalgebra p J).symm a : Module.End ℤ_[p] (TateModule p J)) x :=
  rfl

theorem IntegralHeckeRing.coe_algebraMap (c : ℤ_[p]) :
    ((IntegralHeckeRing.ofSubalgebra p J).symm (algebraMap ℤ_[p] (IntegralHeckeRing p J) c) :
      Module.End ℤ_[p] (TateModule p J)) = algebraMap ℤ_[p] _ c :=
  rfl

scoped instance isMulCommutative_rationalHeckeAlgebra : IsMulCommutative (rationalHeckeAlgebra p J) :=
  Algebra.isMulCommutative_adjoin ℚ_[p] (by
    rintro _ ⟨s, rfl⟩ _ ⟨t, rfl⟩
    rw [← map_mul, ← map_mul, mul_comm])

def RationalHeckeRing : Type :=
  rationalHeckeAlgebra p J

scoped instance commRing_rationalHeckeRing : CommRing (RationalHeckeRing p J) where
  toRing := inferInstanceAs (Ring (rationalHeckeAlgebra p J))
  mul_comm a b := (isMulCommutative_rationalHeckeAlgebra p J).is_comm.comm a b

scoped instance algebra_rationalHeckeRing : Algebra ℚ_[p] (RationalHeckeRing p J) :=
  inferInstanceAs (Algebra ℚ_[p] (rationalHeckeAlgebra p J))

scoped instance module_rationalHeckeRing : Module (RationalHeckeRing p J) (RationalTateModule p J) :=
  inferInstanceAs (Module (rationalHeckeAlgebra p J) (RationalTateModule p J))

scoped instance isScalarTower_rationalHeckeRing :
    IsScalarTower ℚ_[p] (RationalHeckeRing p J) (RationalTateModule p J) :=
  inferInstanceAs (IsScalarTower ℚ_[p] (rationalHeckeAlgebra p J) (RationalTateModule p J))

def RationalHeckeRing.ofSubalgebra : rationalHeckeAlgebra p J ≃+* RationalHeckeRing p J :=
  RingEquiv.refl _

theorem RationalHeckeRing.smul_def (a : RationalHeckeRing p J) (v : RationalTateModule p J) :
    a • v = ((RationalHeckeRing.ofSubalgebra p J).symm a :
      Module.End ℚ_[p] (RationalTateModule p J)) v :=
  rfl

open scoped IsMulCommutative in

theorem RationalHeckeRing.det_ofSubalgebra
    (f : Module.End (rationalHeckeAlgebra p J) (RationalTateModule p J)) :
    RationalHeckeRing.ofSubalgebra p J (LinearMap.det f)
      = LinearMap.det (show Module.End (RationalHeckeRing p J) (RationalTateModule p J) from f) :=
  rfl

def integralToRationalHeckeRing : IntegralHeckeRing p J →+* RationalHeckeRing p J :=
  ((RationalHeckeRing.ofSubalgebra p J).toRingHom.comp (integralToRationalHeckeAlgebra p J)).comp
    (IntegralHeckeRing.ofSubalgebra p J).symm.toRingHom

scoped instance algebra_integral_rationalHeckeRing : Algebra (IntegralHeckeRing p J) (RationalHeckeRing p J) :=
  (integralToRationalHeckeRing p J).toAlgebra

theorem algebraMap_integral_rational_def (a : IntegralHeckeRing p J) :
    ((RationalHeckeRing.ofSubalgebra p J).symm (algebraMap (IntegralHeckeRing p J)
        (RationalHeckeRing p J) a) : Module.End ℚ_[p] (RationalTateModule p J))
      = Module.End.baseChangeHom ℤ_[p] ℚ_[p] (TateModule p J)
          ((IntegralHeckeRing.ofSubalgebra p J).symm a : Module.End ℤ_[p] (TateModule p J)) :=
  rfl

theorem algebraMap_integral_rational_injective :
    Function.Injective (algebraMap (IntegralHeckeRing p J) (RationalHeckeRing p J)) :=
  integralToRationalHeckeAlgebra_injective p J

scoped instance module_integralHeckeRing_rational :
    Module (IntegralHeckeRing p J) (RationalTateModule p J) :=
  Module.compHom (RationalTateModule p J) (algebraMap (IntegralHeckeRing p J) (RationalHeckeRing p J))

scoped instance isScalarTower_integral_rational_rational :
    IsScalarTower (IntegralHeckeRing p J) (RationalHeckeRing p J) (RationalTateModule p J) :=
  IsScalarTower.of_algebraMap_smul fun _ _ => rfl

theorem IntegralHeckeRing.smul_rational_def (a : IntegralHeckeRing p J) (v : RationalTateModule p J) :
    a • v = Module.End.baseChangeHom ℤ_[p] ℚ_[p] (TateModule p J)
      ((IntegralHeckeRing.ofSubalgebra p J).symm a : Module.End ℤ_[p] (TateModule p J)) v :=
  rfl

theorem algebraMap_natCast_p :
    algebraMap (IntegralHeckeRing p J) (RationalHeckeRing p J)
        (algebraMap ℤ_[p] (IntegralHeckeRing p J) p)
      = algebraMap ℚ_[p] (RationalHeckeRing p J) p := by
  refine (RationalHeckeRing.ofSubalgebra p J).symm.injective (Subtype.ext ?_)
  rw [algebraMap_integral_rational_def, IntegralHeckeRing.coe_algebraMap, AlgHom.commutes,
    map_natCast]
  exact (map_natCast (algebraMap ℚ_[p] (Module.End ℚ_[p] (RationalTateModule p J))) p).symm

theorem algebraMap_algebraMap_padicInt (c : ℤ_[p]) :
    algebraMap (IntegralHeckeRing p J) (RationalHeckeRing p J)
        (algebraMap ℤ_[p] (IntegralHeckeRing p J) c)
      = algebraMap ℚ_[p] (RationalHeckeRing p J) c := by
  refine (RationalHeckeRing.ofSubalgebra p J).symm.injective (Subtype.ext ?_)
  rw [algebraMap_integral_rational_def, IntegralHeckeRing.coe_algebraMap, AlgHom.commutes,
    Algebra.algebraMap_eq_smul_one,
    ← algebraMap_smul ℚ_[p] c (1 : Module.End ℚ_[p] (RationalTateModule p J)),
    ← Algebra.algebraMap_eq_smul_one]
  rfl

theorem exists_algHom_integralHeckeRing
    (hsurj : ∀ m ∈ Submodule.torsionBy ℤ J ((p ^ 1 : ℕ) : ℤ),
      ∃ x : TateModule p J, TateModule.proj p J 1 x = m)
    (k : Type) [Field k] [Algebra ℤ_[p] k] (φ : HeckeAlg →+* k) (hp : (p : k) = 0)
    (hmax : (RingHom.ker φ).IsMaximal)
    (hocc : Submodule.torsionBySet HeckeAlg J ((RingHom.ker φ : Ideal HeckeAlg) : Set HeckeAlg) ≠ ⊥) :
    ∃ φ₀ : IntegralHeckeRing p J →ₐ[ℤ_[p]] k,
      ∀ t : HeckeAlg, φ₀ (IntegralHeckeRing.ofSubalgebra p J (heckeToIntegralHeckeAlgebra p J t))
        = φ t := by
  classical
  set W := Submodule.torsionBySet HeckeAlg J ((RingHom.ker φ : Ideal HeckeAlg) : Set HeckeAlg)
    with hW
  obtain ⟨x₀, hx₀, hx₀ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hocc
  have hann := ker_eq_torsionOf J k φ hmax hx₀ hx₀ne
  obtain ⟨ξ, hξ⟩ := hsurj x₀ (mem_torsionBy_of_mem_torsionBySet p J k φ hp hx₀)

  let gen : HeckeAlg → IntegralHeckeRing p J := fun t =>
    IntegralHeckeRing.ofSubalgebra p J (heckeToIntegralHeckeAlgebra p J t)
  let Ψ : MvPolynomial HeckeAlg ℤ_[p] →ₐ[ℤ_[p]] IntegralHeckeRing p J :=
    MvPolynomial.aeval (R := ℤ_[p]) gen
  let Θ : MvPolynomial HeckeAlg ℤ_[p] →ₐ[ℤ_[p]] k := MvPolynomial.aeval (R := ℤ_[p]) (φ : HeckeAlg → k)

  have hΨsurj : Function.Surjective Ψ := by
    rintro ⟨v, hv⟩
    refine Algebra.adjoin_induction (fun x hx => ?_) (fun r => ?_) (fun x y _ _ hx hy => ?_)
      (fun x y _ _ hx hy => ?_) hv
    · obtain ⟨t, rfl⟩ := hx
      exact ⟨MvPolynomial.X t, MvPolynomial.aeval_X gen t⟩
    · exact ⟨MvPolynomial.C r, MvPolynomial.algHom_C Ψ r⟩
    · obtain ⟨f, hf⟩ := hx
      obtain ⟨g, hg⟩ := hy
      exact ⟨f + g, by rw [map_add, hf, hg]; rfl⟩
    · obtain ⟨f, hf⟩ := hx
      obtain ⟨g, hg⟩ := hy
      exact ⟨f * g, by rw [map_mul, hf, hg]; rfl⟩

  have key : ∀ f : MvPolynomial HeckeAlg ℤ_[p], ∃ t : HeckeAlg, φ t = Θ f ∧
      ∀ x : TateModule p J, TateModule.proj p J 1 x ∈ W →
        TateModule.proj p J 1 (Ψ f • x) = t • TateModule.proj p J 1 x := by
    intro f
    induction f using MvPolynomial.induction_on with
    | C c =>
      refine ⟨((c.appr 1 : ℕ) : HeckeAlg), ?_, fun x _ => ?_⟩
      · rw [map_natCast, MvPolynomial.algHom_C, algebraMap_padicInt_eq_natCast_appr p k hp]
      · rw [MvPolynomial.algHom_C, algebraMap_smul, TateModule.proj_apply, TateModule.proj_apply,
          TateModule.smul_apply, natCast_zsmul, Nat.cast_smul_eq_nsmul]
    | add f g hf hg =>
      obtain ⟨s, hs, hs'⟩ := hf
      obtain ⟨t, ht, ht'⟩ := hg
      refine ⟨s + t, by rw [map_add, map_add, hs, ht], fun x hx => ?_⟩
      rw [map_add, add_smul, map_add, hs' x hx, ht' x hx, add_smul]
    | mul_X f s hf =>
      obtain ⟨t, ht, ht'⟩ := hf
      refine ⟨t * s, by rw [map_mul, map_mul, ht, MvPolynomial.aeval_X], fun x hx => ?_⟩
      have hsx : TateModule.proj p J 1 (gen s • x) = s • TateModule.proj p J 1 x := rfl
      have hsxW : TateModule.proj p J 1 (gen s • x) ∈ W := by
        rw [hsx]; exact W.smul_mem s hx
      rw [map_mul, MvPolynomial.aeval_X, mul_smul, ht' _ hsxW, hsx, mul_smul]

  have hker : ∀ f : MvPolynomial HeckeAlg ℤ_[p], f ∈ RingHom.ker Ψ → Θ f = 0 := by
    intro f hf
    obtain ⟨t, ht, ht'⟩ := key f
    have hξW : TateModule.proj p J 1 ξ ∈ W := by rw [hξ]; exact hx₀
    have h0 := ht' ξ hξW
    rw [RingHom.mem_ker.1 hf, zero_smul, map_zero, hξ] at h0
    rw [← ht, ← RingHom.mem_ker, hann]
    exact (Ideal.mem_torsionOf_iff x₀ t).2 h0.symm

  refine ⟨(Ideal.Quotient.liftₐ (RingHom.ker Ψ) Θ hker).comp
      (Ideal.quotientKerAlgEquivOfSurjective hΨsurj).symm.toAlgHom, fun t => ?_⟩
  have ht : gen t = Ψ (MvPolynomial.X t) := (MvPolynomial.aeval_X gen t).symm
  show Ideal.Quotient.liftₐ (RingHom.ker Ψ) Θ hker
      ((Ideal.quotientKerAlgEquivOfSurjective hΨsurj).symm (gen t)) = φ t
  rw [ht, Ideal.quotientKerAlgEquivOfSurjective_symm_apply]
  exact MvPolynomial.aeval_X (φ : HeckeAlg → k) t

theorem exists_algHom_integralHeckeAlgebra
    (hsurj : ∀ m ∈ Submodule.torsionBy ℤ J ((p ^ 1 : ℕ) : ℤ),
      ∃ x : TateModule p J, TateModule.proj p J 1 x = m)
    (k : Type) [Field k] [Algebra ℤ_[p] k] (φ : HeckeAlg →+* k) (hp : (p : k) = 0)
    (hmax : (RingHom.ker φ).IsMaximal)
    (hocc : Submodule.torsionBySet HeckeAlg J ((RingHom.ker φ : Ideal HeckeAlg) : Set HeckeAlg) ≠ ⊥) :
    ∃ φ₀ : integralHeckeAlgebra p J →ₐ[ℤ_[p]] k,
      ∀ t : HeckeAlg, φ₀ (heckeToIntegralHeckeAlgebra p J t) = φ t := by
  obtain ⟨φ₀, h⟩ := exists_algHom_integralHeckeRing p J hsurj k φ hp hmax hocc
  exact ⟨φ₀.comp (IntegralHeckeRing.algEquiv p J).toAlgHom, h⟩

omit [Module HeckeAlg J] in

theorem End.eq_zero_of_mul_algebraMap_pow {n : ℕ} {f : Module.End ℤ_[p] (TateModule p J)}
    (h : f * algebraMap ℤ_[p] (Module.End ℤ_[p] (TateModule p J)) ((p : ℤ_[p]) ^ n) = 0) :
    f = 0 := by
  refine LinearMap.ext fun x => ?_
  have hx := LinearMap.congr_fun h x
  rw [Module.End.mul_apply, Module.algebraMap_end_apply, map_smul, LinearMap.zero_apply] at hx
  rw [LinearMap.zero_apply]
  exact eq_zero_of_pow_smul_eq_zero p J n (f x) hx

theorem eq_zero_of_mul_pow_eq_zero {n : ℕ} {a : IntegralHeckeRing p J}
    (h : a * algebraMap ℤ_[p] (IntegralHeckeRing p J) p ^ n = 0) : a = 0 := by
  refine (IntegralHeckeRing.ofSubalgebra p J).symm.injective (Subtype.ext ?_)
  refine End.eq_zero_of_mul_algebraMap_pow p J (n := n) ?_
  rw [map_pow]
  exact congrArg (fun b : IntegralHeckeRing p J =>
    ((IntegralHeckeRing.ofSubalgebra p J).symm b : Module.End ℤ_[p] (TateModule p J))) h

theorem exists_prime_le_ker_not_mem (k : Type) [Field k] [Algebra ℤ_[p] k]
    (φ₀ : IntegralHeckeRing p J →ₐ[ℤ_[p]] k) :
    ∃ 𝔓 : Ideal (IntegralHeckeRing p J), 𝔓.IsPrime ∧ 𝔓 ≤ RingHom.ker φ₀ ∧
      (algebraMap ℤ_[p] (IntegralHeckeRing p J) p) ∉ 𝔓 := by
  haveI h𝔪 : (RingHom.ker φ₀).IsPrime := RingHom.ker_isPrime φ₀
  let S : Submonoid (IntegralHeckeRing p J) :=
    (RingHom.ker φ₀).primeCompl ⊔ Submonoid.powers (algebraMap ℤ_[p] (IntegralHeckeRing p J) p)
  have hdisj : Disjoint (((⊥ : Ideal (IntegralHeckeRing p J)) : Set (IntegralHeckeRing p J))) S := by
    refine Set.disjoint_left.2 fun a ha hS => ?_
    rw [SetLike.mem_coe, Ideal.mem_bot] at ha
    obtain ⟨y, hy, z, hz, hyz⟩ := Submonoid.mem_sup.1 hS
    obtain ⟨n, rfl⟩ := (Submonoid.mem_powers_iff _ _).1 hz
    rw [ha] at hyz
    exact hy (by rw [eq_zero_of_mul_pow_eq_zero p J hyz]; exact Ideal.zero_mem _)
  obtain ⟨𝔓, h𝔓, -, h𝔓S⟩ := Ideal.exists_le_prime_disjoint (⊥ : Ideal (IntegralHeckeRing p J)) S hdisj
  refine ⟨𝔓, h𝔓, fun a ha => ?_, fun hP => ?_⟩
  · by_contra hna
    exact Set.disjoint_left.1 h𝔓S ha (Submonoid.mem_sup_left hna)
  · exact Set.disjoint_left.1 h𝔓S hP (Submonoid.mem_sup_right (Submonoid.mem_powers _))

theorem exists_pow_mul_eq_algebraMap (q : ℚ_[p]) :
    ∃ n : ℕ, ∃ c : ℤ_[p], (p : ℚ_[p]) ^ n * q = algebraMap ℤ_[p] ℚ_[p] c := by
  obtain ⟨⟨c, s⟩, h⟩ := IsLocalization.surj (nonZeroDivisors ℤ_[p]) q

  have hs : (s : ℤ_[p]) ≠ 0 := nonZeroDivisors.coe_ne_zero s
  set u : ℤ_[p]ˣ := PadicInt.unitCoeff hs with hu
  refine ⟨(s : ℤ_[p]).valuation, c * ↑u⁻¹, ?_⟩
  have hs' : (s : ℤ_[p]) = (u : ℤ_[p]) * (p : ℤ_[p]) ^ (s : ℤ_[p]).valuation :=
    PadicInt.unitCoeff_spec hs
  have hU : algebraMap ℤ_[p] ℚ_[p] (u : ℤ_[p]) * algebraMap ℤ_[p] ℚ_[p] ↑u⁻¹ = 1 := by
    rw [← map_mul, Units.mul_inv, map_one]
  simp only at h
  rw [hs', map_mul, map_pow, map_natCast] at h
  calc (p : ℚ_[p]) ^ (s : ℤ_[p]).valuation * q
      = (p : ℚ_[p]) ^ (s : ℤ_[p]).valuation * q
          * (algebraMap ℤ_[p] ℚ_[p] (u : ℤ_[p]) * algebraMap ℤ_[p] ℚ_[p] ↑u⁻¹) := by
        rw [hU, mul_one]
    _ = q * (algebraMap ℤ_[p] ℚ_[p] (u : ℤ_[p]) * (p : ℚ_[p]) ^ (s : ℤ_[p]).valuation)
          * algebraMap ℤ_[p] ℚ_[p] ↑u⁻¹ := by ring
    _ = algebraMap ℤ_[p] ℚ_[p] (c * ↑u⁻¹) := by rw [h, map_mul]

section Localization

abbrev powersP : Submonoid (IntegralHeckeRing p J) :=
  Submonoid.powers (algebraMap ℤ_[p] (IntegralHeckeRing p J) p)

theorem exists_pow_smul_eq_algebraMap (z : RationalHeckeRing p J) :
    ∃ n : ℕ, ∃ a : IntegralHeckeRing p J,
      (p : ℚ_[p]) ^ n • z = algebraMap (IntegralHeckeRing p J) (RationalHeckeRing p J) a := by

  suffices h : ∀ v ∈ rationalHeckeAlgebra p J, ∃ n : ℕ, ∃ a : integralHeckeAlgebra p J,
      (p : ℚ_[p]) ^ n • v = Module.End.baseChangeHom ℤ_[p] ℚ_[p] (TateModule p J) a by
    obtain ⟨n, a, h⟩ := h ((RationalHeckeRing.ofSubalgebra p J).symm z).1
      ((RationalHeckeRing.ofSubalgebra p J).symm z).2
    exact ⟨n, IntegralHeckeRing.ofSubalgebra p J a,
      (RationalHeckeRing.ofSubalgebra p J).symm.injective (Subtype.ext h)⟩
  intro v hv
  refine Algebra.adjoin_induction (fun x hx => ?_) (fun q => ?_) (fun x y _ _ hx hy => ?_)
    (fun x y _ _ hx hy => ?_) hv
  · obtain ⟨t, rfl⟩ := hx
    exact ⟨0, heckeToIntegralHeckeAlgebra p J t, by rw [pow_zero, one_smul]; rfl⟩
  · obtain ⟨n, c, hc⟩ := exists_pow_mul_eq_algebraMap p q
    refine ⟨n, algebraMap ℤ_[p] _ c, ?_⟩
    rw [Algebra.smul_def, ← map_mul, hc, Subalgebra.coe_algebraMap, AlgHom.commutes,
      Algebra.algebraMap_eq_smul_one (A := Module.End ℚ_[p] (RationalTateModule p J)),
      Algebra.algebraMap_eq_smul_one (A := Module.End ℚ_[p] (RationalTateModule p J)),
      algebraMap_smul]
  · obtain ⟨m, a, ha⟩ := hx
    obtain ⟨n, b, hb⟩ := hy
    refine ⟨m + n, (p : ℤ_[p]) ^ n • a + (p : ℤ_[p]) ^ m • b, ?_⟩
    rw [smul_add, pow_add, mul_smul, mul_smul, smul_comm ((p : ℚ_[p]) ^ m) ((p : ℚ_[p]) ^ n) x,
      ha, hb, Subalgebra.coe_add, Subalgebra.coe_smul, Subalgebra.coe_smul, map_add, map_smul,
      map_smul, ← algebraMap_smul ℚ_[p] ((p : ℤ_[p]) ^ n), ← algebraMap_smul ℚ_[p] ((p : ℤ_[p]) ^ m),
      map_pow, map_pow, map_natCast]
  · obtain ⟨m, a, ha⟩ := hx
    obtain ⟨n, b, hb⟩ := hy
    refine ⟨m + n, a * b, ?_⟩
    rw [pow_add, ← smul_mul_smul_comm, ha, hb, Subalgebra.coe_mul, map_mul]

theorem natCast_p_ne_zero : (p : ℚ_[p]) ≠ 0 :=
  Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero

scoped instance isLocalization_rationalHeckeRing :
    IsLocalization (powersP p J) (RationalHeckeRing p J) := by
  refine (isLocalization_iff _ _).2 ⟨?_, ?_, ?_⟩
  · rintro ⟨s, hs⟩
    obtain ⟨n, rfl⟩ := (Submonoid.mem_powers_iff _ _).1 hs
    show IsUnit (algebraMap _ _ (algebraMap ℤ_[p] (IntegralHeckeRing p J) p ^ n))
    rw [map_pow, algebraMap_natCast_p]
    exact ((isUnit_iff_ne_zero.2 (natCast_p_ne_zero p)).map _).pow n
  · intro z
    obtain ⟨n, a, h⟩ := exists_pow_smul_eq_algebraMap p J z
    refine ⟨(a, ⟨_, n, rfl⟩), ?_⟩
    show z * algebraMap _ _ (algebraMap ℤ_[p] (IntegralHeckeRing p J) p ^ n) = _
    rw [map_pow, algebraMap_natCast_p, ← map_pow, mul_comm, ← Algebra.smul_def, h]
  · intro a b h
    exact ⟨1, by rw [algebraMap_integral_rational_injective p J h]⟩

def ι : TateModule p J →ₗ[IntegralHeckeRing p J] RationalTateModule p J where
  toFun x := (1 : ℚ_[p]) ⊗ₜ x
  map_add' x y := TensorProduct.tmul_add 1 x y
  map_smul' _ _ := rfl

theorem ι_apply (x : TateModule p J) : ι p J x = (1 : ℚ_[p]) ⊗ₜ x := rfl

theorem ι_injective : Function.Injective (ι p J) := fun _ _ h => mk_one_injective p J h

scoped instance isLocalizedModule_ι : IsLocalizedModule (powersP p J) (ι p J) where
  map_units s := by
    obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff _ _).1 s.2
    rw [← hn, map_pow]
    refine IsUnit.pow n ?_
    have hfun : ⇑(algebraMap (IntegralHeckeRing p J)
        (Module.End (IntegralHeckeRing p J) (RationalTateModule p J))
          (algebraMap ℤ_[p] (IntegralHeckeRing p J) p)) = fun v => (p : ℚ_[p]) • v := by
      funext v
      rw [Module.algebraMap_end_apply, ← IsScalarTower.algebraMap_smul (RationalHeckeRing p J),
        algebraMap_natCast_p, algebraMap_smul]
    rw [Module.End.isUnit_iff, hfun]
    exact ⟨smul_right_injective _ (natCast_p_ne_zero p),
      fun w => ⟨(p : ℚ_[p])⁻¹ • w, smul_inv_smul₀ (natCast_p_ne_zero p) w⟩⟩
  surj y := by
    induction y using TensorProduct.induction_on with
    | zero =>
      refine ⟨(0, 1), ?_⟩
      show ((1 : powersP p J) : IntegralHeckeRing p J) • (0 : RationalTateModule p J) = ι p J 0
      rw [smul_zero, map_zero]
    | tmul q x =>
      obtain ⟨n, c, hc⟩ := exists_pow_mul_eq_algebraMap p q
      refine ⟨(c • x, ⟨_, n, rfl⟩), ?_⟩
      show (algebraMap ℤ_[p] (IntegralHeckeRing p J) p ^ n) • (q ⊗ₜ[ℤ_[p]] x)
        = (1 : ℚ_[p]) ⊗ₜ[ℤ_[p]] (c • x)
      rw [← IsScalarTower.algebraMap_smul (RationalHeckeRing p J), map_pow, algebraMap_natCast_p,
        ← map_pow, algebraMap_smul, TensorProduct.smul_tmul', smul_eq_mul, hc,
        Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
    | add y₁ y₂ h₁ h₂ =>
      obtain ⟨⟨x₁, s₁⟩, h₁⟩ := h₁
      obtain ⟨⟨x₂, s₂⟩, h₂⟩ := h₂
      refine ⟨((s₂ : IntegralHeckeRing p J) • x₁ + (s₁ : IntegralHeckeRing p J) • x₂, s₁ * s₂), ?_⟩
      simp only at h₁ h₂
      rw [Submonoid.smul_def] at h₁ h₂ ⊢
      rw [Submonoid.coe_mul, smul_add, mul_smul, mul_smul,
        smul_comm (s₁ : IntegralHeckeRing p J) (s₂ : IntegralHeckeRing p J) y₁, h₁, h₂, map_add,
        map_smul, map_smul]
  exists_of_eq h := ⟨1, by rw [ι_injective p J h]⟩

theorem isBaseChange_ι : IsBaseChange (RationalHeckeRing p J) (ι p J) :=
  (isLocalizedModule_iff_isBaseChange (powersP p J) (RationalHeckeRing p J) (ι p J)).1 inferInstance

end Localization

section FibreDimension

variable {K L : Type} [Field K] [Field L] [Algebra K L] [DistribMulAction (L ≃ₐ[K] L) J]

theorem finrank_baseChange_eq_two (N : ℕ)
    (h : RationalRankTwoCyclotomicOf (K := K) (L := L) N p J)
    (F : Type) [Field F] [Algebra (IntegralHeckeRing p J) F]
    (hpF : algebraMap (IntegralHeckeRing p J) F (algebraMap ℤ_[p] (IntegralHeckeRing p J) p) ≠ 0) :
    Module.finrank F (F ⊗[IntegralHeckeRing p J] TateModule p J) = 2 := by
  obtain ⟨b, -⟩ := h
  let b' : Module.Basis (Fin 2) (RationalHeckeRing p J) (RationalTateModule p J) := b

  have hunit : ∀ s : powersP p J, IsUnit (algebraMap (IntegralHeckeRing p J) F s) := by
    rintro ⟨s, hs⟩
    obtain ⟨n, rfl⟩ := (Submonoid.mem_powers_iff _ _).1 hs
    show IsUnit (algebraMap _ F (algebraMap ℤ_[p] (IntegralHeckeRing p J) p ^ n))
    rw [map_pow]
    exact (isUnit_iff_ne_zero.2 hpF).pow n
  let χ : RationalHeckeRing p J →+* F := IsLocalization.lift hunit
  letI : Algebra (RationalHeckeRing p J) F := χ.toAlgebra
  haveI : IsScalarTower (IntegralHeckeRing p J) (RationalHeckeRing p J) F :=
    IsScalarTower.of_algebraMap_eq fun a => (IsLocalization.lift_eq hunit a).symm
  haveI : Nontrivial (RationalHeckeRing p J) := χ.domain_nontrivial
  haveI : Module.Free (RationalHeckeRing p J) (RationalTateModule p J) := Module.Free.of_basis b'

  have bc : IsBaseChange F (((TensorProduct.mk (RationalHeckeRing p J) F (RationalTateModule p J) 1
      ).restrictScalars (IntegralHeckeRing p J)).comp (ι p J)) :=
    (isBaseChange_ι p J).comp
      (TensorProduct.isBaseChange (RationalHeckeRing p J) (RationalTateModule p J) F)
  rw [bc.equiv.finrank_eq, Module.finrank_baseChange, Module.finrank_eq_card_basis b',
    Fintype.card_fin]

end FibreDimension

section RationalToField

variable (F : Type) [Field F] [Algebra (IntegralHeckeRing p J) F]

theorem isUnit_algebraMap_powersP
    (hpF : algebraMap (IntegralHeckeRing p J) F (algebraMap ℤ_[p] (IntegralHeckeRing p J) p) ≠ 0)
    (s : powersP p J) : IsUnit (algebraMap (IntegralHeckeRing p J) F s) := by
  obtain ⟨s, hs⟩ := s
  obtain ⟨n, rfl⟩ := (Submonoid.mem_powers_iff _ _).1 hs
  show IsUnit (algebraMap _ F (algebraMap ℤ_[p] (IntegralHeckeRing p J) p ^ n))
  rw [map_pow]
  exact (isUnit_iff_ne_zero.2 hpF).pow n

def rationalToField
    (hpF : algebraMap (IntegralHeckeRing p J) F (algebraMap ℤ_[p] (IntegralHeckeRing p J) p) ≠ 0) :
    RationalHeckeRing p J →+* F :=
  IsLocalization.lift (isUnit_algebraMap_powersP p J F hpF)

theorem rationalToField_algebraMap
    (hpF : algebraMap (IntegralHeckeRing p J) F (algebraMap ℤ_[p] (IntegralHeckeRing p J) p) ≠ 0)
    (a : IntegralHeckeRing p J) :
    rationalToField p J F hpF (algebraMap (IntegralHeckeRing p J) (RationalHeckeRing p J) a)
      = algebraMap (IntegralHeckeRing p J) F a :=
  IsLocalization.lift_eq _ a

theorem det_baseChange_eq_rationalToField_det {K L : Type} [Field K] [Field L] [Algebra K L]
    [DistribMulAction (L ≃ₐ[K] L) J] (N : ℕ)
    (h : RationalRankTwoCyclotomicOf (K := K) (L := L) N p J)
    (hpF : algebraMap (IntegralHeckeRing p J) F (algebraMap ℤ_[p] (IntegralHeckeRing p J) p) ≠ 0)
    (σT : Module.End (IntegralHeckeRing p J) (TateModule p J))
    (σV : Module.End (RationalHeckeRing p J) (RationalTateModule p J))
    (hσ : ∀ x, σV (ι p J x) = ι p J (σT x)) :
    LinearMap.det (σT.baseChange F) = rationalToField p J F hpF (LinearMap.det σV) := by
  obtain ⟨b, -⟩ := h
  let b' : Module.Basis (Fin 2) (RationalHeckeRing p J) (RationalTateModule p J) := b
  letI : Algebra (RationalHeckeRing p J) F := (rationalToField p J F hpF).toAlgebra
  haveI : IsScalarTower (IntegralHeckeRing p J) (RationalHeckeRing p J) F :=
    IsScalarTower.of_algebraMap_eq fun a => (rationalToField_algebraMap p J F hpF a).symm
  haveI : Module.Free (RationalHeckeRing p J) (RationalTateModule p J) := Module.Free.of_basis b'
  haveI : Module.Finite (RationalHeckeRing p J) (RationalTateModule p J) := Module.Finite.of_basis b'
  have bc : IsBaseChange F (((TensorProduct.mk (RationalHeckeRing p J) F (RationalTateModule p J) 1
      ).restrictScalars (IntegralHeckeRing p J)).comp (ι p J)) :=
    (isBaseChange_ι p J).comp
      (TensorProduct.isBaseChange (RationalHeckeRing p J) (RationalTateModule p J) F)

  have hcomm : ∀ z, bc.equiv (σT.baseChange F z) = σV.baseChange F (bc.equiv z) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero, map_zero]
    | tmul a x =>
      rw [LinearMap.baseChange_tmul, IsBaseChange.equiv_tmul, IsBaseChange.equiv_tmul, map_smul]
      show a • ((1 : F) ⊗ₜ[RationalHeckeRing p J] ι p J (σT x))
        = a • σV.baseChange F ((1 : F) ⊗ₜ[RationalHeckeRing p J] ι p J x)
      rw [LinearMap.baseChange_tmul, hσ]
    | add z₁ z₂ h₁ h₂ => rw [map_add, map_add, h₁, h₂, map_add, map_add]
  have hconj : σT.baseChange F
      = (bc.equiv.symm : _ →ₗ[F] _) ∘ₗ σV.baseChange F ∘ₗ (bc.equiv.symm.symm : _ →ₗ[F] _) := by
    refine LinearMap.ext fun z => ?_
    rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.coe_coe,
      LinearEquiv.symm_symm, ← hcomm, LinearEquiv.symm_apply_apply]
  rw [hconj, LinearMap.det_conj, LinearMap.det_baseChange]
  rfl

end RationalToField

variable (G : Type) [Monoid G] [DistribMulAction G J]

theorem rep_mul_tateHeckeRep [SMulCommClass G HeckeAlg J] (g : G) (t : HeckeAlg) :
    TateModule.rep p J G g * tateHeckeRep p J t = tateHeckeRep p J t * TateModule.rep p J G g := by
  refine LinearMap.ext fun x => Subtype.ext (funext fun n => ?_)
  show g • (t • (x : ℕ → J) n) = t • (g • (x : ℕ → J) n)
  exact smul_comm g t ((x : ℕ → J) n)

theorem commute_rep_of_mem [SMulCommClass G HeckeAlg J] (g : G)
    {a : Module.End ℤ_[p] (TateModule p J)} (ha : a ∈ integralHeckeAlgebra p J) :
    Commute (TateModule.rep p J G g) a :=
  Algebra.commute_of_mem_adjoin_of_forall_mem_commute ha (by
    rintro _ ⟨t, rfl⟩
    exact rep_mul_tateHeckeRep p J G g t)

def integralGaloisRepLinear [SMulCommClass G HeckeAlg J] :
    G →* (TateModule p J →ₗ[integralHeckeAlgebra p J] TateModule p J) where
  toFun g :=
    { toFun := TateModule.rep p J G g
      map_add' := map_add _
      map_smul' := fun a x => by
        show TateModule.rep p J G g ((a : Module.End ℤ_[p] (TateModule p J)) x)
          = (a : Module.End ℤ_[p] (TateModule p J)) (TateModule.rep p J G g x)
        exact LinearMap.congr_fun (commute_rep_of_mem p J G g a.2).eq x }
  map_one' := LinearMap.ext fun x => by
    show TateModule.rep p J G 1 x = x
    rw [map_one]
    rfl
  map_mul' g h := LinearMap.ext fun x => by
    show TateModule.rep p J G (g * h) x = TateModule.rep p J G g (TateModule.rep p J G h x)
    rw [map_mul]
    rfl

theorem integralGaloisRepLinear_apply [SMulCommClass G HeckeAlg J] (g : G) (x : TateModule p J) :
    integralGaloisRepLinear p J G g x = TateModule.rep p J G g x :=
  rfl

def integralGaloisRep' [SMulCommClass G HeckeAlg J] :
    G →* (TateModule p J →ₗ[IntegralHeckeRing p J] TateModule p J) where
  toFun g :=
    { toFun := TateModule.rep p J G g
      map_add' := map_add _
      map_smul' := fun a x => (integralGaloisRepLinear p J G g).map_smul
        ((IntegralHeckeRing.ofSubalgebra p J).symm a) x }
  map_one' := LinearMap.ext fun x => by
    show TateModule.rep p J G 1 x = x
    rw [map_one]
    rfl
  map_mul' g h := LinearMap.ext fun x => by
    show TateModule.rep p J G (g * h) x = TateModule.rep p J G g (TateModule.rep p J G h x)
    rw [map_mul]
    rfl

theorem integralGaloisRep'_apply [SMulCommClass G HeckeAlg J] (g : G) (x : TateModule p J) :
    integralGaloisRep' p J G g x = TateModule.rep p J G g x :=
  rfl

section PadicAlgebra

omit [Module HeckeAlg J] in

theorem injective_of_map_natCast_ne_zero {R : Type} [CommRing R] [NoZeroDivisors R]
    (g : ℤ_[p] →+* R) (hg : g p ≠ 0) : Function.Injective g := by
  refine (injective_iff_map_eq_zero _).2 fun c hc => by_contra fun hc0 => hg ?_
  rw [PadicInt.unitCoeff_spec hc0, map_mul, map_pow] at hc
  exact eq_zero_of_pow_eq_zero (((Units.isUnit _).map g).mul_right_eq_zero.1 hc)

omit [Module HeckeAlg J] in

theorem isUnit_algebraMap_of_ne_zero (F : Type) [Field F] [Algebra ℤ_[p] F]
    (h : algebraMap ℤ_[p] F p ≠ 0) (s : nonZeroDivisors ℤ_[p]) : IsUnit (algebraMap ℤ_[p] F s) :=
  isUnit_iff_ne_zero.2 (map_ne_zero_of_mem_nonZeroDivisors _
    (injective_of_map_natCast_ne_zero p _ h) s.2)

omit [Module HeckeAlg J] in

abbrev padicAlgebraOfNeZero (F : Type) [Field F] [Algebra ℤ_[p] F] (h : algebraMap ℤ_[p] F p ≠ 0) :
    Algebra ℚ_[p] F :=
  (IsLocalization.lift (isUnit_algebraMap_of_ne_zero p F h) : ℚ_[p] →+* F).toAlgebra

omit [Module HeckeAlg J] in
theorem padicAlgebraOfNeZero_isScalarTower (F : Type) [Field F] [Algebra ℤ_[p] F]
    (h : algebraMap ℤ_[p] F p ≠ 0) :
    letI := padicAlgebraOfNeZero p F h
    IsScalarTower ℤ_[p] ℚ_[p] F :=
  letI := padicAlgebraOfNeZero p F h
  IsScalarTower.of_algebraMap_eq fun c =>
    (IsLocalization.lift_eq (isUnit_algebraMap_of_ne_zero p F h) c).symm

end PadicAlgebra

section ResidueField

variable (𝔓 : Ideal (IntegralHeckeRing p J)) [𝔓.IsPrime]

scoped instance finite_integralHeckeRing [Module.Finite ℤ_[p] (TateModule p J)]
    [Module.Free ℤ_[p] (TateModule p J)] : Module.Finite ℤ_[p] (IntegralHeckeRing p J) :=
  inferInstanceAs (Module.Finite ℤ_[p] (integralHeckeAlgebra p J))

scoped instance finite_integralHeckeRing_quotient [Module.Finite ℤ_[p] (TateModule p J)]
    [Module.Free ℤ_[p] (TateModule p J)] : Module.Finite ℤ_[p] (IntegralHeckeRing p J ⧸ 𝔓) :=
  Module.Finite.of_surjective (Ideal.Quotient.mkₐ ℤ_[p] 𝔓).toLinearMap
    (Ideal.Quotient.mkₐ_surjective ℤ_[p] 𝔓)

theorem injective_algebraMap_quotient
    (hp𝔓 : algebraMap ℤ_[p] (IntegralHeckeRing p J) p ∉ 𝔓) :
    Function.Injective (algebraMap ℤ_[p] (IntegralHeckeRing p J ⧸ 𝔓)) := by
  refine injective_of_map_natCast_ne_zero p _ fun h => hp𝔓 ?_
  rwa [IsScalarTower.algebraMap_apply ℤ_[p] (IntegralHeckeRing p J) (IntegralHeckeRing p J ⧸ 𝔓),
    Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem] at h

theorem finite_padic_of_isFractionRing_quotient
    (hp𝔓 : algebraMap ℤ_[p] (IntegralHeckeRing p J) p ∉ 𝔓)
    [Module.Finite ℤ_[p] (TateModule p J)] [Module.Free ℤ_[p] (TateModule p J)]
    (F : Type) [Field F] [Algebra ℤ_[p] F] [Algebra ℚ_[p] F] [IsScalarTower ℤ_[p] ℚ_[p] F]
    [Algebra (IntegralHeckeRing p J ⧸ 𝔓) F] [IsScalarTower ℤ_[p] (IntegralHeckeRing p J ⧸ 𝔓) F]
    [IsFractionRing (IntegralHeckeRing p J ⧸ 𝔓) F] : Module.Finite ℚ_[p] F := by
  have hinj := injective_algebraMap_quotient p J 𝔓 hp𝔓
  haveI : IsLocalization
      (Algebra.algebraMapSubmonoid (IntegralHeckeRing p J ⧸ 𝔓) (nonZeroDivisors ℤ_[p])) F := by
    refine (IsLocalization.iff_of_le_of_exists_dvd _
      (nonZeroDivisors (IntegralHeckeRing p J ⧸ 𝔓)) ?_ ?_).2 inferInstance
    · rintro x ⟨c, hc, rfl⟩
      exact mem_nonZeroDivisors_of_ne_zero (map_ne_zero_of_mem_nonZeroDivisors _ hinj hc)
    · intro n hn
      obtain ⟨r, hr, hdvd⟩ :=
        ((Algebra.IsIntegral.isIntegral (R := ℤ_[p]) n).isAlgebraic).exists_nonzero_dvd hn
      exact ⟨algebraMap ℤ_[p] _ r, ⟨r, mem_nonZeroDivisors_of_ne_zero hr, rfl⟩, hdvd⟩
  exact Module.Finite.of_isLocalization ℤ_[p] (IntegralHeckeRing p J ⧸ 𝔓) (nonZeroDivisors ℤ_[p])

theorem algebraMap_residueField_natCast_ne_zero
    (hp𝔓 : algebraMap ℤ_[p] (IntegralHeckeRing p J) p ∉ 𝔓) :
    algebraMap ℤ_[p] 𝔓.ResidueField p ≠ 0 := by
  rw [IsScalarTower.algebraMap_apply ℤ_[p] (IntegralHeckeRing p J) 𝔓.ResidueField]
  exact fun h => hp𝔓 (Ideal.algebraMap_residueField_eq_zero.1 h)

theorem algebraMap_residueField_ne_zero
    (hp𝔓 : algebraMap ℤ_[p] (IntegralHeckeRing p J) p ∉ 𝔓) :
    algebraMap (IntegralHeckeRing p J) 𝔓.ResidueField (algebraMap ℤ_[p] (IntegralHeckeRing p J) p)
      ≠ 0 :=
  fun h => hp𝔓 (Ideal.algebraMap_residueField_eq_zero.1 h)

scoped instance algebra_padic_residueField [Fact (algebraMap ℤ_[p] (IntegralHeckeRing p J) p ∉ 𝔓)] :
    Algebra ℚ_[p] 𝔓.ResidueField :=
  padicAlgebraOfNeZero p _ (algebraMap_residueField_natCast_ne_zero p J 𝔓 Fact.out)

scoped instance isScalarTower_padic_residueField
    [Fact (algebraMap ℤ_[p] (IntegralHeckeRing p J) p ∉ 𝔓)] :
    IsScalarTower ℤ_[p] ℚ_[p] 𝔓.ResidueField :=
  padicAlgebraOfNeZero_isScalarTower p _ (algebraMap_residueField_natCast_ne_zero p J 𝔓 Fact.out)

scoped instance finite_padic_residueField [Fact (algebraMap ℤ_[p] (IntegralHeckeRing p J) p ∉ 𝔓)]
    [Module.Finite ℤ_[p] (TateModule p J)] [Module.Free ℤ_[p] (TateModule p J)] :
    Module.Finite ℚ_[p] 𝔓.ResidueField :=
  finite_padic_of_isFractionRing_quotient p J 𝔓 Fact.out 𝔓.ResidueField

theorem finrank_residueField_baseChange_eq_two {K L : Type} [Field K] [Field L] [Algebra K L]
    [DistribMulAction (L ≃ₐ[K] L) J] (N : ℕ)
    (h : RationalRankTwoCyclotomicOf (K := K) (L := L) N p J)
    [Module.Finite ℤ_[p] (TateModule p J)] [Module.Free ℤ_[p] (TateModule p J)]
    (hp𝔓 : algebraMap ℤ_[p] (IntegralHeckeRing p J) p ∉ 𝔓) :
    Module.finrank 𝔓.ResidueField (𝔓.ResidueField ⊗[IntegralHeckeRing p J] TateModule p J) = 2 :=
  finrank_baseChange_eq_two p J N h _ (algebraMap_residueField_ne_zero p J 𝔓 hp𝔓)

end ResidueField

section Lattice

variable (F : Type) [Field F] [Algebra ℤ_[p] F] [Algebra (IntegralHeckeRing p J) F]
  [IsScalarTower ℤ_[p] (IntegralHeckeRing p J) F]

def toBaseChange : TateModule p J →ₗ[ℤ_[p]] F ⊗[IntegralHeckeRing p J] TateModule p J :=
  (TensorProduct.mk (IntegralHeckeRing p J) F (TateModule p J) 1).restrictScalars ℤ_[p]

theorem toBaseChange_apply (x : TateModule p J) :
    toBaseChange p J F x = (1 : F) ⊗ₜ[IntegralHeckeRing p J] x :=
  rfl

def baseChangeLattice : Submodule ℤ_[p] (F ⊗[IntegralHeckeRing p J] TateModule p J) :=
  LinearMap.range (toBaseChange p J F)

theorem tmul_mem_baseChangeLattice (x : TateModule p J) :
    (1 : F) ⊗ₜ[IntegralHeckeRing p J] x ∈ baseChangeLattice p J F :=
  ⟨x, rfl⟩

scoped instance finite_baseChangeLattice [Module.Finite ℤ_[p] (TateModule p J)] :
    Module.Finite ℤ_[p] (baseChangeLattice p J F) :=
  Module.Finite.range _

theorem span_baseChangeLattice_eq_top :
    Submodule.span F (baseChangeLattice p J F : Set (F ⊗[IntegralHeckeRing p J] TateModule p J))
      = ⊤ := by
  refine Submodule.eq_top_iff'.2 fun w => ?_
  induction w using TensorProduct.induction_on with
  | zero => exact Submodule.zero_mem _
  | tmul f x =>
    have : f ⊗ₜ[IntegralHeckeRing p J] x = f • ((1 : F) ⊗ₜ[IntegralHeckeRing p J] x) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [this]
    exact Submodule.smul_mem _ f (Submodule.subset_span (tmul_mem_baseChangeLattice p J F x))
  | add w₁ w₂ h₁ h₂ => exact Submodule.add_mem _ h₁ h₂

theorem smul_mem_baseChangeLattice (a : IntegralHeckeRing p J)
    {w : F ⊗[IntegralHeckeRing p J] TateModule p J} (hw : w ∈ baseChangeLattice p J F) :
    algebraMap (IntegralHeckeRing p J) F a • w ∈ baseChangeLattice p J F := by
  obtain ⟨x, rfl⟩ := hw
  refine ⟨a • x, ?_⟩
  show (1 : F) ⊗ₜ[IntegralHeckeRing p J] (a • x)
    = algebraMap (IntegralHeckeRing p J) F a • ((1 : F) ⊗ₜ[IntegralHeckeRing p J] x)
  rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one, ← TensorProduct.smul_tmul, Algebra.smul_def,
    mul_one]

theorem baseChange_mem_baseChangeLattice (f : TateModule p J →ₗ[IntegralHeckeRing p J] TateModule p J)
    {w : F ⊗[IntegralHeckeRing p J] TateModule p J} (hw : w ∈ baseChangeLattice p J F) :
    f.baseChange F w ∈ baseChangeLattice p J F := by
  obtain ⟨x, rfl⟩ := hw
  exact ⟨f x, (LinearMap.baseChange_tmul f (1 : F) x).symm⟩

set_option synthInstance.maxHeartbeats 320000 in

theorem noZeroSMulDivisors_baseChange (hpF : algebraMap ℤ_[p] F p ≠ 0) :
    NoZeroSMulDivisors ℤ_[p] (F ⊗[IntegralHeckeRing p J] TateModule p J) :=
  ⟨fun {c w} h => or_iff_not_imp_left.2 fun hc => by
    rw [← algebraMap_smul F c w] at h
    exact (smul_eq_zero.1 h).resolve_left
      (map_ne_zero_of_mem_nonZeroDivisors _ (injective_of_map_natCast_ne_zero p _ hpF)
        (mem_nonZeroDivisors_of_ne_zero hc))⟩

end Lattice

section LatticePID

variable (F : Type) [Field F] [Algebra ℤ_[p] F] [Algebra (IntegralHeckeRing p J) F]
  [IsScalarTower ℤ_[p] (IntegralHeckeRing p J) F]
variable (𝒪 : Subalgebra ℤ_[p] F)

def pidLattice : Submodule 𝒪 (F ⊗[IntegralHeckeRing p J] TateModule p J) :=
  Submodule.span 𝒪 (baseChangeLattice p J F : Set (F ⊗[IntegralHeckeRing p J] TateModule p J))

theorem baseChangeLattice_le_pidLattice {w : F ⊗[IntegralHeckeRing p J] TateModule p J}
    (hw : w ∈ baseChangeLattice p J F) : w ∈ pidLattice p J F 𝒪 :=
  Submodule.subset_span hw

theorem tmul_mem_pidLattice (x : TateModule p J) :
    (1 : F) ⊗ₜ[IntegralHeckeRing p J] x ∈ pidLattice p J F 𝒪 :=
  baseChangeLattice_le_pidLattice p J F 𝒪 (tmul_mem_baseChangeLattice p J F x)

scoped instance isLattice_pidLattice [Module.Finite ℤ_[p] (TateModule p J)] :
    Submodule.IsLattice F (pidLattice p J F 𝒪) where
  fg := by
    obtain ⟨S, hS⟩ := Module.Finite.iff_fg.1 (finite_baseChangeLattice p J F)
    refine ⟨S, ?_⟩
    rw [pidLattice, ← hS, Submodule.span_span_of_tower]
  span_eq_top := eq_top_iff.2 ((span_baseChangeLattice_eq_top p J F).ge.trans
    (Submodule.span_mono Submodule.subset_span))

def pidLatticeEnd (e : Module.End (IntegralHeckeRing p J) (TateModule p J)) :
    Module.End 𝒪 (pidLattice p J F 𝒪) :=
  ((e.baseChange F).restrictScalars 𝒪).restrict (p := pidLattice p J F 𝒪)
    (q := pidLattice p J F 𝒪) fun w hw => by
      have hle : Submodule.map ((e.baseChange F).restrictScalars 𝒪) (pidLattice p J F 𝒪)
          ≤ pidLattice p J F 𝒪 :=
        Submodule.map_span_le _ _ _ |>.2 fun v hv =>
          baseChangeLattice_le_pidLattice p J F 𝒪 (baseChange_mem_baseChangeLattice p J F e hv)
      exact hle ⟨w, hw, rfl⟩

def LatticeMod : Type :=
  pidLattice p J F 𝒪

namespace LatticeMod

scoped instance addCommGroup : AddCommGroup (LatticeMod p J F 𝒪) :=
  inferInstanceAs (AddCommGroup (pidLattice p J F 𝒪))

scoped instance module : Module 𝒪 (LatticeMod p J F 𝒪) :=
  inferInstanceAs (Module 𝒪 (pidLattice p J F 𝒪))

scoped instance finite [Module.Finite ℤ_[p] (TateModule p J)] : Module.Finite 𝒪 (LatticeMod p J F 𝒪) :=
  inferInstanceAs (Module.Finite 𝒪 (pidLattice p J F 𝒪))

scoped instance free [Module.Finite ℤ_[p] (TateModule p J)] [IsPrincipalIdealRing 𝒪] :
    Module.Free 𝒪 (LatticeMod p J F 𝒪) :=
  Submodule.IsLattice.free F (pidLattice p J F 𝒪)

def val : LatticeMod p J F 𝒪 →ₗ[𝒪] F ⊗[IntegralHeckeRing p J] TateModule p J :=
  (pidLattice p J F 𝒪).subtype

theorem val_injective : Function.Injective (val p J F 𝒪) :=
  Subtype.val_injective

variable {p J F 𝒪} in
theorem ext {v w : LatticeMod p J F 𝒪} (h : val p J F 𝒪 v = val p J F 𝒪 w) : v = w :=
  val_injective p J F 𝒪 h

def mk (w : F ⊗[IntegralHeckeRing p J] TateModule p J) (hw : w ∈ pidLattice p J F 𝒪) :
    LatticeMod p J F 𝒪 :=
  ⟨w, hw⟩

@[scoped simp]
theorem val_mk (w : F ⊗[IntegralHeckeRing p J] TateModule p J) (hw : w ∈ pidLattice p J F 𝒪) :
    val p J F 𝒪 (mk p J F 𝒪 w hw) = w :=
  rfl

theorem val_smul (c : 𝒪) (w : LatticeMod p J F 𝒪) :
    val p J F 𝒪 (c • w) = (c : F) • val p J F 𝒪 w :=
  rfl

end LatticeMod
p2m_reactivate "P2MW.S_ModularCurve_residualRealization_of_occurs.ModularCurve.X4IntegralSide.LatticeMod"

theorem finrank_latticeMod_eq_two [Module.Finite ℤ_[p] (TateModule p J)]
    [Module.Free ℤ_[p] (TateModule p J)] [IsPrincipalIdealRing 𝒪] [IsFractionRing 𝒪 F]
    {K L : Type} [Field K] [Field L] [Algebra K L] [DistribMulAction (L ≃ₐ[K] L) J] (N : ℕ)
    (h : RationalRankTwoCyclotomicOf (K := K) (L := L) N p J)
    (hpF : algebraMap (IntegralHeckeRing p J) F (algebraMap ℤ_[p] (IntegralHeckeRing p J) p) ≠ 0) :
    Module.finrank 𝒪 (LatticeMod p J F 𝒪) = 2 := by
  have h2 := finrank_baseChange_eq_two p J N h F hpF
  haveI : Module.Finite F (F ⊗[IntegralHeckeRing p J] TateModule p J) :=
    Module.finite_of_finrank_eq_succ h2
  refine Module.finrank_eq_of_rank_eq ?_
  show Module.rank 𝒪 (pidLattice p J F 𝒪) = _
  rw [Submodule.IsLattice.rank' F (pidLattice p J F 𝒪), ← Module.finrank_eq_rank, h2]

def latticeEnd (e : Module.End (IntegralHeckeRing p J) (TateModule p J)) :
    Module.End 𝒪 (LatticeMod p J F 𝒪) :=
  pidLatticeEnd p J F 𝒪 e

theorem val_latticeEnd_apply (e : Module.End (IntegralHeckeRing p J) (TateModule p J))
    (w : LatticeMod p J F 𝒪) :
    LatticeMod.val p J F 𝒪 (latticeEnd p J F 𝒪 e w) = e.baseChange F (LatticeMod.val p J F 𝒪 w) :=
  rfl

variable (G : Type) [Group G]

def latticeRep (ρ₀ : G →* Module.End (IntegralHeckeRing p J) (TateModule p J)) :
    G →* Module.End 𝒪 (LatticeMod p J F 𝒪) where
  toFun g := latticeEnd p J F 𝒪 (ρ₀ g)
  map_one' := LinearMap.ext fun w => LatticeMod.ext <| by
    rw [val_latticeEnd_apply, map_one, LinearMap.baseChange_one]
    rfl
  map_mul' g h := LinearMap.ext fun w => LatticeMod.ext <| by
    rw [val_latticeEnd_apply, map_mul, LinearMap.baseChange_mul]
    rfl

theorem latticeRep_apply (ρ₀ : G →* Module.End (IntegralHeckeRing p J) (TateModule p J)) (g : G) :
    latticeRep p J F 𝒪 G ρ₀ g = latticeEnd p J F 𝒪 (ρ₀ g) :=
  rfl

theorem val_latticeRep_apply (ρ₀ : G →* Module.End (IntegralHeckeRing p J) (TateModule p J))
    (g : G) (w : LatticeMod p J F 𝒪) :
    LatticeMod.val p J F 𝒪 (latticeRep p J F 𝒪 G ρ₀ g w)
      = (ρ₀ g).baseChange F (LatticeMod.val p J F 𝒪 w) :=
  rfl

theorem repr_extendOfIsLattice_val [Module.Finite ℤ_[p] (TateModule p J)] [IsPrincipalIdealRing 𝒪]
    [IsFractionRing 𝒪 F] {ι' : Type} [Fintype ι'] (b : Module.Basis ι' 𝒪 (LatticeMod p J F 𝒪))
    (w : LatticeMod p J F 𝒪) (i : ι') :
    (Module.Basis.extendOfIsLattice F (M := pidLattice p J F 𝒪) b).repr (LatticeMod.val p J F 𝒪 w) i
      = algebraMap 𝒪 F (b.repr w i) := by
  have hw : LatticeMod.val p J F 𝒪 w
      = (Module.Basis.extendOfIsLattice F (M := pidLattice p J F 𝒪) b).equivFun.symm
          (fun j => algebraMap 𝒪 F (b.repr w j)) := by
    rw [Module.Basis.equivFun_symm_apply]
    conv_lhs => rw [← b.sum_repr w]
    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [LinearMap.map_smul, Module.Basis.extendOfIsLattice_apply]
    rfl
  calc (Module.Basis.extendOfIsLattice F (M := pidLattice p J F 𝒪) b).repr (LatticeMod.val p J F 𝒪 w) i
      = (Module.Basis.extendOfIsLattice F (M := pidLattice p J F 𝒪) b).equivFun
          (LatticeMod.val p J F 𝒪 w) i := rfl
    _ = algebraMap 𝒪 F (b.repr w i) := by rw [hw, LinearEquiv.apply_symm_apply]

theorem algebraMap_det_eq_det [Module.Finite ℤ_[p] (TateModule p J)] [IsPrincipalIdealRing 𝒪]
    [IsFractionRing 𝒪 F] (fΛ : Module.End 𝒪 (LatticeMod p J F 𝒪))
    (fW : Module.End F (F ⊗[IntegralHeckeRing p J] TateModule p J))
    (hf : ∀ w, LatticeMod.val p J F 𝒪 (fΛ w) = fW (LatticeMod.val p J F 𝒪 w)) :
    algebraMap 𝒪 F (LinearMap.det fΛ) = LinearMap.det fW := by
  classical
  let b := Module.Free.chooseBasis 𝒪 (LatticeMod p J F 𝒪)
  rw [← LinearMap.det_toMatrix b,
    ← LinearMap.det_toMatrix (Module.Basis.extendOfIsLattice F (M := pidLattice p J F 𝒪) b),
    RingHom.map_det]
  congr 1
  ext i j
  rw [RingHom.mapMatrix_apply, Matrix.map_apply, LinearMap.toMatrix_apply, LinearMap.toMatrix_apply,
    Module.Basis.extendOfIsLattice_apply]
  show algebraMap 𝒪 F (b.repr (fΛ (b j)) i)
    = (Module.Basis.extendOfIsLattice F (M := pidLattice p J F 𝒪) b).repr
        (fW (LatticeMod.val p J F 𝒪 (b j))) i
  rw [← hf, repr_extendOfIsLattice_val]

theorem algebraMap_det_latticeRep [Module.Finite ℤ_[p] (TateModule p J)] [IsPrincipalIdealRing 𝒪]
    [IsFractionRing 𝒪 F] (ρ₀ : G →* Module.End (IntegralHeckeRing p J) (TateModule p J)) (g : G) :
    algebraMap 𝒪 F (LinearMap.det (latticeRep p J F 𝒪 G ρ₀ g))
      = LinearMap.det ((ρ₀ g).baseChange F) :=
  algebraMap_det_eq_det p J F 𝒪 _ _ (val_latticeRep_apply p J F 𝒪 G ρ₀ g)

open scoped IsMulCommutative in

theorem det_latticeRep_eq_natCast {K L : Type} [Field K] [Field L] [Algebra K L]
    [DistribMulAction (L ≃ₐ[K] L) J] (N : ℕ)
    (h : RationalRankTwoCyclotomicOf (K := K) (L := L) N p J)
    [Module.Finite ℤ_[p] (TateModule p J)] [IsPrincipalIdealRing 𝒪] [IsFractionRing 𝒪 F]
    (hpF : algebraMap (IntegralHeckeRing p J) F (algebraMap ℤ_[p] (IntegralHeckeRing p J) p) ≠ 0)
    (ρ₀ : G →* Module.End (IntegralHeckeRing p J) (TateModule p J)) (g : G)
    (σV : Module.End (rationalHeckeAlgebra p J) (RationalTateModule p J))
    (hσ : ∀ x, σV (ι p J x) = ι p J (ρ₀ g x)) (ℓ : ℕ)
    (htop : LinearMap.det σV = (ℓ : rationalHeckeAlgebra p J)) :
    LinearMap.det (latticeRep p J F 𝒪 G ρ₀ g) = (ℓ : 𝒪) := by
  have htop' : LinearMap.det (show Module.End (RationalHeckeRing p J) (RationalTateModule p J)
      from σV) = (ℓ : RationalHeckeRing p J) := htop
  apply Subtype.val_injective
  show algebraMap 𝒪 F (LinearMap.det (latticeRep p J F 𝒪 G ρ₀ g)) = algebraMap 𝒪 F (ℓ : 𝒪)
  rw [algebraMap_det_latticeRep, det_baseChange_eq_rationalToField_det p J F N h hpF (ρ₀ g)
      (show Module.End (RationalHeckeRing p J) (RationalTateModule p J) from σV) hσ,
    htop', map_natCast, map_natCast]

end LatticePID
p2m_reactivate "P2MW.S_ModularCurve_residualRealization_of_occurs.ModularCurve.X4IntegralSide.LatticeMod"

section Residual

variable (F : Type) [Field F] [Algebra ℤ_[p] F] [Algebra (IntegralHeckeRing p J) F]
  [IsScalarTower ℤ_[p] (IntegralHeckeRing p J) F]
variable (𝒪 : Subalgebra ℤ_[p] F)
variable (kk : Type) [Field kk] [Algebra 𝒪 kk]

abbrev ResidualSpace : Type :=
  kk ⊗[𝒪] LatticeMod p J F 𝒪

scoped instance finite_residualSpace [Module.Finite ℤ_[p] (TateModule p J)] :
    Module.Finite kk (ResidualSpace p J F 𝒪 kk) :=
  inferInstance

theorem finrank_residualSpace_eq_two [Module.Finite ℤ_[p] (TateModule p J)]
    [Module.Free ℤ_[p] (TateModule p J)] [IsPrincipalIdealRing 𝒪] [IsFractionRing 𝒪 F]
    {K L : Type} [Field K] [Field L] [Algebra K L] [DistribMulAction (L ≃ₐ[K] L) J] (N : ℕ)
    (h : RationalRankTwoCyclotomicOf (K := K) (L := L) N p J)
    (hpF : algebraMap (IntegralHeckeRing p J) F (algebraMap ℤ_[p] (IntegralHeckeRing p J) p) ≠ 0) :
    Module.finrank kk (ResidualSpace p J F 𝒪 kk) = 2 := by
  rw [Module.finrank_baseChange, finrank_latticeMod_eq_two p J F 𝒪 N h hpF]

variable (G : Type) [Group G]

def residualRepEnd (ρ₀ : G →* Module.End (IntegralHeckeRing p J) (TateModule p J)) :
    G →* Module.End kk (ResidualSpace p J F 𝒪 kk) :=
  (Module.End.baseChangeHom 𝒪 kk (LatticeMod p J F 𝒪)).toMonoidHom.comp (latticeRep p J F 𝒪 G ρ₀)

theorem residualRepEnd_apply (ρ₀ : G →* Module.End (IntegralHeckeRing p J) (TateModule p J))
    (g : G) : residualRepEnd p J F 𝒪 kk G ρ₀ g = (latticeRep p J F 𝒪 G ρ₀ g).baseChange kk := by
  rfl

def residualRep (ρ₀ : G →* Module.End (IntegralHeckeRing p J) (TateModule p J)) :
    G →* (ResidualSpace p J F 𝒪 kk ≃ₗ[kk] ResidualSpace p J F 𝒪 kk) :=
  (LinearMap.GeneralLinearGroup.generalLinearEquiv kk (ResidualSpace p J F 𝒪 kk)).toMonoidHom.comp
    (residualRepEnd p J F 𝒪 kk G ρ₀).toHomUnits

theorem residualRep_apply (ρ₀ : G →* Module.End (IntegralHeckeRing p J) (TateModule p J))
    (g : G) (v : ResidualSpace p J F 𝒪 kk) :
    residualRep p J F 𝒪 kk G ρ₀ g v = (latticeRep p J F 𝒪 G ρ₀ g).baseChange kk v := by
  rfl

theorem residualRep_toLinearMap (ρ₀ : G →* Module.End (IntegralHeckeRing p J) (TateModule p J))
    (g : G) :
    (residualRep p J F 𝒪 kk G ρ₀ g).toLinearMap = (latticeRep p J F 𝒪 G ρ₀ g).baseChange kk :=
  LinearMap.ext fun v => residualRep_apply p J F 𝒪 kk G ρ₀ g v

theorem residualRep_tmul (ρ₀ : G →* Module.End (IntegralHeckeRing p J) (TateModule p J))
    (g : G) (c : kk) (w : LatticeMod p J F 𝒪) :
    residualRep p J F 𝒪 kk G ρ₀ g (c ⊗ₜ w) = c ⊗ₜ latticeRep p J F 𝒪 G ρ₀ g w := by
  rw [residualRep_apply, LinearMap.baseChange_tmul]

theorem det_residualRep (ρ₀ : G →* Module.End (IntegralHeckeRing p J) (TateModule p J))
    [Module.Finite ℤ_[p] (TateModule p J)] [IsPrincipalIdealRing 𝒪] (g : G) :
    LinearMap.det (residualRep p J F 𝒪 kk G ρ₀ g).toLinearMap
      = algebraMap 𝒪 kk (LinearMap.det (latticeRep p J F 𝒪 G ρ₀ g)) := by
  rw [residualRep_toLinearMap, LinearMap.det_baseChange]

open scoped IsMulCommutative in

theorem det_residualRep_eq_natCast {K L : Type} [Field K] [Field L] [Algebra K L]
    [DistribMulAction (L ≃ₐ[K] L) J] (N : ℕ)
    (h : RationalRankTwoCyclotomicOf (K := K) (L := L) N p J)
    [Module.Finite ℤ_[p] (TateModule p J)] [IsPrincipalIdealRing 𝒪] [IsFractionRing 𝒪 F]
    (hpF : algebraMap (IntegralHeckeRing p J) F (algebraMap ℤ_[p] (IntegralHeckeRing p J) p) ≠ 0)
    (ρ₀ : G →* Module.End (IntegralHeckeRing p J) (TateModule p J)) (g : G)
    (σV : Module.End (rationalHeckeAlgebra p J) (RationalTateModule p J))
    (hσ : ∀ x, σV (ι p J x) = ι p J (ρ₀ g x)) (ℓ : ℕ)
    (htop : LinearMap.det σV = (ℓ : rationalHeckeAlgebra p J)) :
    LinearMap.det (residualRep p J F 𝒪 kk G ρ₀ g).toLinearMap = (ℓ : kk) := by
  rw [det_residualRep, det_latticeRep_eq_natCast p J F 𝒪 G N h hpF ρ₀ g σV hσ ℓ htop, map_natCast]

def toLattice : TateModule p J →+ LatticeMod p J F 𝒪 where
  toFun x := LatticeMod.mk p J F 𝒪 ((1 : F) ⊗ₜ x) (tmul_mem_pidLattice p J F 𝒪 x)
  map_zero' := LatticeMod.ext (by rw [LatticeMod.val_mk, TensorProduct.tmul_zero, map_zero])
  map_add' _ _ := LatticeMod.ext (by rw [LatticeMod.val_mk, TensorProduct.tmul_add, map_add]; rfl)

theorem val_toLattice (x : TateModule p J) :
    LatticeMod.val p J F 𝒪 (toLattice p J F 𝒪 x) = (1 : F) ⊗ₜ x :=
  rfl

theorem latticeRep_toLattice (ρ₀ : G →* Module.End (IntegralHeckeRing p J) (TateModule p J))
    (g : G) (x : TateModule p J) :
    latticeRep p J F 𝒪 G ρ₀ g (toLattice p J F 𝒪 x) = toLattice p J F 𝒪 (ρ₀ g x) :=
  LatticeMod.ext (by
    rw [val_latticeRep_apply, val_toLattice, val_toLattice, LinearMap.baseChange_tmul])

def toResidual : TateModule p J →+ ResidualSpace p J F 𝒪 kk :=
  (TensorProduct.mk 𝒪 kk (LatticeMod p J F 𝒪) 1).toAddMonoidHom.comp (toLattice p J F 𝒪)

theorem toResidual_apply (x : TateModule p J) :
    toResidual p J F 𝒪 kk x = (1 : kk) ⊗ₜ[𝒪] toLattice p J F 𝒪 x :=
  rfl

theorem toResidual_smul (a : IntegralHeckeRing p J)
    (ha : algebraMap (IntegralHeckeRing p J) F a ∈ 𝒪) (x : TateModule p J) :
    toResidual p J F 𝒪 kk (a • x)
      = algebraMap 𝒪 kk ⟨algebraMap (IntegralHeckeRing p J) F a, ha⟩ • toResidual p J F 𝒪 kk x := by
  have h1 : toLattice p J F 𝒪 (a • x)
      = (⟨algebraMap (IntegralHeckeRing p J) F a, ha⟩ : 𝒪) • toLattice p J F 𝒪 x := by
    refine LatticeMod.ext ?_
    rw [LatticeMod.val_smul, val_toLattice, val_toLattice]
    show (1 : F) ⊗ₜ[IntegralHeckeRing p J] (a • x)
      = algebraMap (IntegralHeckeRing p J) F a • ((1 : F) ⊗ₜ[IntegralHeckeRing p J] x)
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one, ← TensorProduct.smul_tmul, Algebra.smul_def,
      mul_one]
  rw [toResidual_apply, toResidual_apply, h1, TensorProduct.tmul_smul, algebraMap_smul]

theorem toResidual_padicInt_smul (c : ℤ_[p]) (x : TateModule p J) :
    toResidual p J F 𝒪 kk (c • x)
      = algebraMap 𝒪 kk (algebraMap ℤ_[p] 𝒪 c) • toResidual p J F 𝒪 kk x := by
  have hc : algebraMap (IntegralHeckeRing p J) F (algebraMap ℤ_[p] (IntegralHeckeRing p J) c) ∈ 𝒪 := by
    rw [← IsScalarTower.algebraMap_apply]
    exact Subalgebra.algebraMap_mem 𝒪 c
  have hc' : (⟨algebraMap (IntegralHeckeRing p J) F (algebraMap ℤ_[p] (IntegralHeckeRing p J) c), hc⟩
      : 𝒪) = algebraMap ℤ_[p] 𝒪 c :=
    Subtype.ext (IsScalarTower.algebraMap_apply ℤ_[p] (IntegralHeckeRing p J) F c).symm
  rw [← IsScalarTower.algebraMap_smul (IntegralHeckeRing p J) c x, toResidual_smul p J F 𝒪 kk _ hc,
    hc']

theorem toResidual_natCast_smul (x : TateModule p J) :
    toResidual p J F 𝒪 kk ((p : ℤ_[p]) • x) = (p : kk) • toResidual p J F 𝒪 kk x := by
  rw [toResidual_padicInt_smul, map_natCast, map_natCast]

variable {G} in

theorem toResidual_rep (ρ₀ : G →* Module.End (IntegralHeckeRing p J) (TateModule p J)) (g : G)
    (x : TateModule p J) :
    toResidual p J F 𝒪 kk (ρ₀ g x) = residualRep p J F 𝒪 kk G ρ₀ g (toResidual p J F 𝒪 kk x) := by
  rw [toResidual_apply, toResidual_apply, residualRep_tmul, latticeRep_toLattice]

theorem span_range_toLattice :
    Submodule.span 𝒪 (Set.range (toLattice p J F 𝒪)) = ⊤ := by
  have hS : Set.range (toLattice p J F 𝒪) = ((↑) : pidLattice p J F 𝒪 →
      F ⊗[IntegralHeckeRing p J] TateModule p J) ⁻¹'
        (baseChangeLattice p J F : Set (F ⊗[IntegralHeckeRing p J] TateModule p J)) := by
    ext w
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨x, rfl⟩
    · rintro ⟨x, hx⟩
      exact ⟨x, LatticeMod.ext hx⟩
  rw [hS]
  exact Submodule.span_span_coe_preimage

theorem span_range_toResidual :
    Submodule.span kk (Set.range (toResidual p J F 𝒪 kk)) = ⊤ := by
  rw [toResidual, AddMonoidHom.coe_comp, Set.range_comp]
  show Submodule.span kk (TensorProduct.mk 𝒪 kk (LatticeMod p J F 𝒪) 1 ''
    Set.range (toLattice p J F 𝒪)) = ⊤
  rw [← Submodule.baseChange_span, span_range_toLattice, Submodule.baseChange_top]

end Residual
p2m_reactivate "P2MW.S_ModularCurve_residualRealization_of_occurs.ModularCurve.X4IntegralSide.LatticeMod"

end X4IntegralSide
p2m_reactivate "P2MW.S_ModularCurve_residualRealization_of_occurs.ModularCurve.X4IntegralSide.LatticeMod P2MW.S_ModularCurve_residualRealization_of_occurs.ModularCurve.X4IntegralSide"

end ModularCurve
p2m_reactivate "P2MW.S_ModularCurve_residualRealization_of_occurs.ModularCurve.X4IntegralSide.LatticeMod P2MW.S_ModularCurve_residualRealization_of_occurs.ModularCurve.X4IntegralSide P2MW.S_ModularCurve_residualRealization_of_occurs.ModularCurve"

end
p2m_reactivate "P2MW.S_ModularCurve_residualRealization_of_occurs.ModularCurve.X4IntegralSide.LatticeMod P2MW.S_ModularCurve_residualRealization_of_occurs.ModularCurve.X4IntegralSide P2MW.S_ModularCurve_residualRealization_of_occurs.ModularCurve"

set_option autoImplicit false

noncomputable section

section Checks
variable {p : ℕ} [Fact p.Prime]

#check (inferInstance : IsDiscreteValuationRing ℤ_[p])

#check @IsIntegralClosure.isDedekindDomain
#check @integralClosure.isDedekindDomain

#check @IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain

#check @Module.free_of_finite_type_torsion_free'

#check @Ideal.ResidueField
#check @Ideal.ResidueField.lift
#check @Ideal.ResidueField.map

#check @Ideal.exists_ideal_over_maximal_of_isIntegral

#check @isField_of_isIntegral_of_isField'

#check (inferInstance : IsFractionRing ℤ_[p] ℚ_[p])
end Checks
p2m_reactivate "P2MW.S_ModularCurve_residualRealization_of_occurs.ModularCurve.X4IntegralSide.LatticeMod P2MW.S_ModularCurve_residualRealization_of_occurs.ModularCurve.X4IntegralSide P2MW.S_ModularCurve_residualRealization_of_occurs.ModularCurve"

namespace ModularCurve
p2m_export "ModularCurve" "tateHeckeRep coe_tateHeckeRep_apply_apply RationalTateModule rationalGaloisRep rationalGaloisRep_apply rationalHeckeRep rationalHeckeRep_apply rationalHeckeRep_tmul rationalHeckeAlgebra rationalHeckeRep_mem_rationalHeckeAlgebra RationalRankTwoCyclotomicOf RationalRankTwoCyclotomic modularFunctionFieldBar JZero HeckeAlg heckeTorsion IsResidualRealization CyclotomicDeterminant heckeModuleBar rationalRankTwoCyclotomic_family JZero.torsion_fixed_by_open JZero.exists_abelJacobiCard heckeOperatorsCommuteBar smulCommClass_JZero_of_heckeOperatorsCommuteBar"
p2m_open "ModularCurve~baseChangeHom~baseChangeHom_injective"
namespace X4LocalRing

variable (p : ℕ) [Fact p.Prime]

theorem exists_dvr_localization_integralClosure
    (κ : Type) [Field κ] [Algebra ℚ_[p] κ] [FiniteDimensional ℚ_[p] κ]
    [Algebra ℤ_[p] κ] [IsScalarTower ℤ_[p] ℚ_[p] κ]
    (k : Type) [Field k] (ψ₀ : integralClosure ℤ_[p] κ →+* k) (hp : ψ₀ p = 0)
    (hmax : (RingHom.ker ψ₀).IsMaximal) :
    ∃ (𝔓₀ : Ideal (integralClosure ℤ_[p] κ)) (_ : 𝔓₀.IsMaximal) (_ : 𝔓₀ ≠ ⊥),
      𝔓₀ ≤ RingHom.ker ψ₀ ∧
      IsDiscreteValuationRing (Localization.AtPrime 𝔓₀) := by
  haveI : IsDedekindDomain (integralClosure ℤ_[p] κ) :=
    integralClosure.isDedekindDomain ℤ_[p] ℚ_[p] κ
  have hpmem : (p : integralClosure ℤ_[p] κ) ∈ RingHom.ker ψ₀ := RingHom.mem_ker.2 hp

  haveI : CharZero κ := charZero_of_injective_algebraMap (algebraMap ℚ_[p] κ).injective
  have hpne : (p : integralClosure ℤ_[p] κ) ≠ 0 := by
    intro h
    apply (Nat.cast_ne_zero (R := κ)).2 (Fact.out : p.Prime).ne_zero
    have := congrArg (algebraMap (integralClosure ℤ_[p] κ) κ) h
    rwa [map_natCast, map_zero] at this
  have hne : RingHom.ker ψ₀ ≠ ⊥ := fun h => hpne (Ideal.mem_bot.1 (h ▸ hpmem))
  exact ⟨RingHom.ker ψ₀, hmax, hne, le_refl _,
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain
      (integralClosure ℤ_[p] κ) hne _⟩

theorem ker_isMaximal_of_integralClosure
    (κ : Type) [Field κ] [Algebra ℚ_[p] κ] [FiniteDimensional ℚ_[p] κ]
    [Algebra ℤ_[p] κ] [IsScalarTower ℤ_[p] ℚ_[p] κ]
    (k : Type) [Field k] (ψ₀ : integralClosure ℤ_[p] κ →+* k) (hp : ψ₀ p = 0) :
    (RingHom.ker ψ₀).IsMaximal := by
  haveI : (RingHom.ker ψ₀).IsPrime := RingHom.ker_isPrime ψ₀
  refine Ideal.isMaximal_of_isIntegral_of_isMaximal_comap (R := ℤ_[p]) (RingHom.ker ψ₀) ?_

  have hpcomap : (p : ℤ_[p]) ∈ (RingHom.ker ψ₀).comap (algebraMap ℤ_[p] (integralClosure ℤ_[p] κ)) := by
    rw [Ideal.mem_comap, RingHom.mem_ker,
      map_natCast (algebraMap ℤ_[p] (integralClosure ℤ_[p] κ))]
    exact hp
  have hle : IsLocalRing.maximalIdeal ℤ_[p] ≤
      (RingHom.ker ψ₀).comap (algebraMap ℤ_[p] (integralClosure ℤ_[p] κ)) := by
    rw [PadicInt.maximalIdeal_eq_span_p, Ideal.span_le]
    exact Set.singleton_subset_iff.2 hpcomap
  haveI hcomap_prime : ((RingHom.ker ψ₀).comap
      (algebraMap ℤ_[p] (integralClosure ℤ_[p] κ))).IsPrime := Ideal.comap_isPrime _ _
  exact (IsLocalRing.maximalIdeal.isMaximal ℤ_[p]).eq_of_le hcomap_prime.ne_top hle ▸
    IsLocalRing.maximalIdeal.isMaximal ℤ_[p]

end X4LocalRing
p2m_reactivate "P2MW.S_ModularCurve_residualRealization_of_occurs.ModularCurve.X4IntegralSide.LatticeMod P2MW.S_ModularCurve_residualRealization_of_occurs.ModularCurve.X4IntegralSide P2MW.S_ModularCurve_residualRealization_of_occurs.ModularCurve"
end ModularCurve
p2m_reactivate "P2MW.S_ModularCurve_residualRealization_of_occurs.ModularCurve.X4IntegralSide.LatticeMod P2MW.S_ModularCurve_residualRealization_of_occurs.ModularCurve.X4IntegralSide P2MW.S_ModularCurve_residualRealization_of_occurs.ModularCurve"

end
p2m_reactivate "P2MW.S_ModularCurve_residualRealization_of_occurs.ModularCurve.X4IntegralSide.LatticeMod P2MW.S_ModularCurve_residualRealization_of_occurs.ModularCurve.X4IntegralSide P2MW.S_ModularCurve_residualRealization_of_occurs.ModularCurve"

set_option autoImplicit false

noncomputable section

namespace ModularCurve
p2m_export "ModularCurve" "tateHeckeRep coe_tateHeckeRep_apply_apply RationalTateModule rationalGaloisRep rationalGaloisRep_apply rationalHeckeRep rationalHeckeRep_apply rationalHeckeRep_tmul rationalHeckeAlgebra rationalHeckeRep_mem_rationalHeckeAlgebra RationalRankTwoCyclotomicOf RationalRankTwoCyclotomic modularFunctionFieldBar JZero HeckeAlg heckeTorsion IsResidualRealization CyclotomicDeterminant heckeModuleBar rationalRankTwoCyclotomic_family JZero.torsion_fixed_by_open JZero.exists_abelJacobiCard heckeOperatorsCommuteBar smulCommClass_JZero_of_heckeOperatorsCommuteBar"
p2m_open "ModularCurve~baseChangeHom~baseChangeHom_injective"

namespace X4DvrSource

section Generic

variable {R : Type} [CommRing R] [IsDedekindDomain R]
variable (κ : Type) [Field κ] [Algebra R κ] [IsFractionRing R κ]
variable (𝔓₀ : Ideal R) [𝔓₀.IsMaximal]
variable (Z : Type) [CommRing Z] [Algebra Z R] [Algebra Z κ] [IsScalarTower Z R κ]

def dvrSubalgebra : Subalgebra Z κ :=
  (Localization.subalgebra.ofField κ 𝔓₀.primeCompl 𝔓₀.primeCompl_le_nonZeroDivisors
    ).restrictScalars Z

theorem mem_dvrSubalgebra_iff {x : κ} : x ∈ dvrSubalgebra κ 𝔓₀ Z ↔
    x ∈ Localization.subalgebra.ofField κ 𝔓₀.primeCompl 𝔓₀.primeCompl_le_nonZeroDivisors :=
  Iff.rfl

theorem algebraMap_mem_dvrSubalgebra (r : R) : algebraMap R κ r ∈ dvrSubalgebra κ 𝔓₀ Z :=
  Subalgebra.algebraMap_mem _ r

scoped instance algebra_dvrSubalgebra : Algebra R (dvrSubalgebra κ 𝔓₀ Z) :=
  inferInstanceAs (Algebra R
    (Localization.subalgebra.ofField κ 𝔓₀.primeCompl 𝔓₀.primeCompl_le_nonZeroDivisors))

scoped instance isScalarTower_dvrSubalgebra : IsScalarTower R (dvrSubalgebra κ 𝔓₀ Z) κ :=
  inferInstanceAs (IsScalarTower R
    (Localization.subalgebra.ofField κ 𝔓₀.primeCompl 𝔓₀.primeCompl_le_nonZeroDivisors) κ)

scoped instance isLocalization_dvrSubalgebra : IsLocalization.AtPrime (dvrSubalgebra κ 𝔓₀ Z) 𝔓₀ :=
  inferInstanceAs (IsLocalization 𝔓₀.primeCompl
    (Localization.subalgebra.ofField κ 𝔓₀.primeCompl 𝔓₀.primeCompl_le_nonZeroDivisors))

scoped instance isFractionRing_dvrSubalgebra : IsFractionRing (dvrSubalgebra κ 𝔓₀ Z) κ :=
  inferInstanceAs (IsFractionRing
    (Localization.subalgebra.ofField κ 𝔓₀.primeCompl 𝔓₀.primeCompl_le_nonZeroDivisors) κ)

theorem algebraMap_dvrSubalgebra_apply (r : R) :
    (algebraMap R (dvrSubalgebra κ 𝔓₀ Z) r : κ) = algebraMap R κ r := rfl

theorem isDiscreteValuationRing_dvrSubalgebra (h0 : 𝔓₀ ≠ ⊥) :
    IsDiscreteValuationRing (dvrSubalgebra κ 𝔓₀ Z) :=
  IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain R h0 _

theorem isPrincipalIdealRing_dvrSubalgebra (h0 : 𝔓₀ ≠ ⊥) :
    IsPrincipalIdealRing (dvrSubalgebra κ 𝔓₀ Z) :=
  haveI := isDiscreteValuationRing_dvrSubalgebra κ 𝔓₀ Z h0
  inferInstance

variable {k : Type} [Field k] (ψ₀₀ : R →+* k)

omit [IsDedekindDomain R] in
theorem isUnit_map_primeCompl (hker : RingHom.ker ψ₀₀ ≤ 𝔓₀) (s : 𝔓₀.primeCompl) :
    IsUnit (ψ₀₀ s) :=
  isUnit_iff_ne_zero.2 fun h => s.2 (hker ((RingHom.mem_ker).2 h))

private def _root_.ModularCurve.X4DvrSource.lift (hker : RingHom.ker ψ₀₀ ≤ 𝔓₀) : dvrSubalgebra κ 𝔓₀ Z →+* k :=
  IsLocalization.lift (M := 𝔓₀.primeCompl) (isUnit_map_primeCompl 𝔓₀ ψ₀₀ hker)

p2m_export "ModularCurve.X4DvrSource" "lift"
theorem lift_algebraMap (hker : RingHom.ker ψ₀₀ ≤ 𝔓₀) (r : R) :
    lift κ 𝔓₀ Z ψ₀₀ hker (algebraMap R (dvrSubalgebra κ 𝔓₀ Z) r) = ψ₀₀ r :=
  IsLocalization.lift_eq _ r

theorem lift_mk (hker : RingHom.ker ψ₀₀ ≤ 𝔓₀) (r : R)
    (hx : algebraMap R κ r ∈ dvrSubalgebra κ 𝔓₀ Z) :
    lift κ 𝔓₀ Z ψ₀₀ hker ⟨algebraMap R κ r, hx⟩ = ψ₀₀ r :=
  lift_algebraMap κ 𝔓₀ Z ψ₀₀ hker r

end Generic
p2m_reactivate "P2MW.S_ModularCurve_residualRealization_of_occurs.ModularCurve.X4IntegralSide.LatticeMod P2MW.S_ModularCurve_residualRealization_of_occurs.ModularCurve.X4IntegralSide P2MW.S_ModularCurve_residualRealization_of_occurs.ModularCurve"

section Padic

variable (p : ℕ) [Fact p.Prime]

theorem exists_dvr_packet (κ : Type) [Field κ] [Algebra ℚ_[p] κ] [FiniteDimensional ℚ_[p] κ]
    [Algebra ℤ_[p] κ] [IsScalarTower ℤ_[p] ℚ_[p] κ]
    (k : Type) [Field k] (ψ₀₀ : integralClosure ℤ_[p] κ →+* k) (hp : ψ₀₀ p = 0) :
    ∃ (𝒪 : Subalgebra ℤ_[p] κ) (_ : IsPrincipalIdealRing 𝒪) (_ : IsFractionRing 𝒪 κ)
      (ψ : 𝒪 →+* k) (h𝒪 : ∀ r : integralClosure ℤ_[p] κ, (r : κ) ∈ 𝒪),
      (∀ r : integralClosure ℤ_[p] κ, ψ ⟨r, h𝒪 r⟩ = ψ₀₀ r) ∧ ψ (algebraMap ℤ_[p] 𝒪 p) = 0 := by
  haveI : IsDedekindDomain (integralClosure ℤ_[p] κ) :=
    integralClosure.isDedekindDomain ℤ_[p] ℚ_[p] κ
  haveI : IsFractionRing (integralClosure ℤ_[p] κ) κ :=
    integralClosure.isFractionRing_of_finite_extension ℚ_[p] κ
  obtain ⟨𝔓₀, hmax, h0, hle, -⟩ := X4LocalRing.exists_dvr_localization_integralClosure p κ k ψ₀₀ hp
    (X4LocalRing.ker_isMaximal_of_integralClosure p κ k ψ₀₀ hp)
  haveI := hmax
  have hker : RingHom.ker ψ₀₀ ≤ 𝔓₀ := (hmax.eq_of_le (RingHom.ker_ne_top ψ₀₀) hle).symm.le
  refine ⟨dvrSubalgebra κ 𝔓₀ ℤ_[p], isPrincipalIdealRing_dvrSubalgebra κ 𝔓₀ ℤ_[p] h0,
    inferInstance, lift κ 𝔓₀ ℤ_[p] ψ₀₀ hker,
    fun r => algebraMap_mem_dvrSubalgebra κ 𝔓₀ ℤ_[p] r,
    fun r => lift_mk κ 𝔓₀ ℤ_[p] ψ₀₀ hker r _, ?_⟩
  have hpp : algebraMap ℤ_[p] (dvrSubalgebra κ 𝔓₀ ℤ_[p]) p
      = algebraMap (integralClosure ℤ_[p] κ) (dvrSubalgebra κ 𝔓₀ ℤ_[p])
          (p : integralClosure ℤ_[p] κ) := by
    rw [map_natCast, map_natCast]
  rw [hpp, lift_algebraMap, hp]

end Padic
p2m_reactivate "P2MW.S_ModularCurve_residualRealization_of_occurs.ModularCurve.X4IntegralSide.LatticeMod P2MW.S_ModularCurve_residualRealization_of_occurs.ModularCurve.X4IntegralSide P2MW.S_ModularCurve_residualRealization_of_occurs.ModularCurve"

end X4DvrSource
p2m_reactivate "P2MW.S_ModularCurve_residualRealization_of_occurs.ModularCurve.X4IntegralSide.LatticeMod P2MW.S_ModularCurve_residualRealization_of_occurs.ModularCurve.X4IntegralSide P2MW.S_ModularCurve_residualRealization_of_occurs.ModularCurve P2MW.S_ModularCurve_residualRealization_of_occurs.ModularCurve.X4DvrSource"

end ModularCurve
p2m_reactivate "P2MW.S_ModularCurve_residualRealization_of_occurs.ModularCurve.X4IntegralSide.LatticeMod P2MW.S_ModularCurve_residualRealization_of_occurs.ModularCurve.X4IntegralSide P2MW.S_ModularCurve_residualRealization_of_occurs.ModularCurve P2MW.S_ModularCurve_residualRealization_of_occurs.ModularCurve.X4DvrSource"

end
p2m_reactivate "P2MW.S_ModularCurve_residualRealization_of_occurs.ModularCurve.X4IntegralSide.LatticeMod P2MW.S_ModularCurve_residualRealization_of_occurs.ModularCurve.X4IntegralSide P2MW.S_ModularCurve_residualRealization_of_occurs.ModularCurve P2MW.S_ModularCurve_residualRealization_of_occurs.ModularCurve.X4DvrSource"

set_option autoImplicit false

noncomputable section

open scoped TensorProduct

namespace ModularCurve
p2m_export "ModularCurve" "tateHeckeRep coe_tateHeckeRep_apply_apply RationalTateModule rationalGaloisRep rationalGaloisRep_apply rationalHeckeRep rationalHeckeRep_apply rationalHeckeRep_tmul rationalHeckeAlgebra rationalHeckeRep_mem_rationalHeckeAlgebra RationalRankTwoCyclotomicOf RationalRankTwoCyclotomic modularFunctionFieldBar JZero HeckeAlg heckeTorsion IsResidualRealization CyclotomicDeterminant heckeModuleBar rationalRankTwoCyclotomic_family JZero.torsion_fixed_by_open JZero.exists_abelJacobiCard heckeOperatorsCommuteBar smulCommClass_JZero_of_heckeOperatorsCommuteBar"
p2m_open "ModularCurve~baseChangeHom~baseChangeHom_injective"

namespace X4Fclause

section Checks
#check @IntermediateField.restrictNormalHom_ker
#check @IntermediateField.normal_iSup
#check @IntermediateField.finiteDimensional_iSup_of_finite
#check @IntermediateField.fixingSubgroup_antitone
#check @AlgHom.fieldRange
end Checks
p2m_reactivate "P2MW.S_ModularCurve_residualRealization_of_occurs.ModularCurve.X4IntegralSide.LatticeMod P2MW.S_ModularCurve_residualRealization_of_occurs.ModularCurve.X4IntegralSide P2MW.S_ModularCurve_residualRealization_of_occurs.ModularCurve P2MW.S_ModularCurve_residualRealization_of_occurs.ModularCurve.X4DvrSource"

theorem exists_uniform_number_field {ι : Type} [Finite ι]
    (Fam : ι → Type) [∀ i, Field (Fam i)] [∀ i, NumberField (Fam i)] [∀ i, IsGalois ℚ (Fam i)]
    [∀ i, Algebra (Fam i) (AlgebraicClosure ℚ)] [∀ i, IsScalarTower ℚ (Fam i) (AlgebraicClosure ℚ)] :
    ∃ (F : Type) (_ : Field F) (_ : NumberField F) (_ : IsGalois ℚ F)
      (_ : Algebra F (AlgebraicClosure ℚ)) (_ : IsScalarTower ℚ F (AlgebraicClosure ℚ)),
      ∀ i : ι, (AlgEquiv.restrictNormalHom (F := ℚ) (K₁ := AlgebraicClosure ℚ) F).ker
        ≤ (AlgEquiv.restrictNormalHom (F := ℚ) (K₁ := AlgebraicClosure ℚ) (Fam i)).ker := by
  classical

  let Efield : ι → IntermediateField ℚ (AlgebraicClosure ℚ) := fun i =>
    (IsScalarTower.toAlgHom ℚ (Fam i) (AlgebraicClosure ℚ)).fieldRange

  have hequiv : ∀ i, Fam i ≃ₐ[ℚ] Efield i := fun i =>
    AlgEquiv.ofInjectiveField (IsScalarTower.toAlgHom ℚ (Fam i) (AlgebraicClosure ℚ))

  have instNorm : ∀ i, Normal ℚ (Efield i) := fun i => Normal.of_algEquiv (hequiv i)
  have instFD : ∀ i, FiniteDimensional ℚ (Efield i) := fun i =>
    Module.Finite.equiv (hequiv i).toLinearEquiv

  let E : IntermediateField ℚ (AlgebraicClosure ℚ) := ⨆ i, Efield i
  haveI : Normal ℚ E := IntermediateField.normal_iSup (h := instNorm) ℚ (AlgebraicClosure ℚ) Efield
  haveI : FiniteDimensional ℚ E :=
    @IntermediateField.finiteDimensional_iSup_of_finite ℚ (AlgebraicClosure ℚ) _ _ _ ι Efield _ instFD
  haveI : IsGalois ℚ E := { }
  haveI : CharZero (AlgebraicClosure ℚ) :=
    charZero_of_injective_algebraMap (algebraMap ℚ (AlgebraicClosure ℚ)).injective
  haveI hNFE : NumberField E :=
    { to_charZero := SubsemiringClass.instCharZero E
      to_finiteDimensional := ‹FiniteDimensional ℚ E› }
  refine ⟨E, inferInstance, hNFE, inferInstance, inferInstance, inferInstance, fun i σ hσ => ?_⟩

  rw [MonoidHom.mem_ker] at hσ ⊢
  have hσE : σ ∈ E.fixingSubgroup :=
    (@IntermediateField.restrictNormalHom_ker ℚ (AlgebraicClosure ℚ) _ _ _ E ‹Normal ℚ E›) ▸
      (MonoidHom.mem_ker.2 hσ)
  have hfix : ∀ y : AlgebraicClosure ℚ, y ∈ Efield i → σ y = y := fun y hy =>
    (IntermediateField.mem_fixingSubgroup_iff E σ).1 hσE y (le_iSup Efield i hy)

  refine AlgEquiv.ext fun x => (algebraMap (Fam i) (AlgebraicClosure ℚ)).injective ?_
  rw [show (AlgEquiv.restrictNormalHom (Fam i) σ : Fam i → Fam i) = σ.restrictNormal (Fam i) from rfl,
    AlgEquiv.restrictNormal_commutes σ (Fam i) x, AlgEquiv.one_apply]
  exact hfix _ ⟨x, rfl⟩

theorem linearEquiv_eq_one_of_forall_fixed {G J k V : Type} [Monoid G] [AddCommGroup J]
    [DistribMulAction G J] [Field k] [AddCommGroup V] [Module k V]
    (s : Set J) (π : J → V) (ρ : G →* (V ≃ₗ[k] V))
    (hmap : ∀ (g : G) (x : J), x ∈ s → π (g • x) = ρ g (π x))
    (hspan : Submodule.span k (π '' s) = ⊤)
    (σ : G) (hfix : ∀ x ∈ s, σ • x = x) : ρ σ = 1 := by
  have key : ∀ v : V, (ρ σ).toLinearMap v = v := fun v => by
    have hv : v ∈ Submodule.span k (π '' s) := hspan ▸ Submodule.mem_top
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hv
    · rintro _ ⟨x, hx, rfl⟩
      show ρ σ (π x) = π x
      rw [← hmap σ x hx, hfix x hx]
    · exact map_zero _
    · intro x y _ _ hx hy; simp only [map_add, hx, hy]
    · intro c x _ hx; simp only [map_smul, hx]
  exact LinearEquiv.toLinearMap_injective (LinearMap.ext key)

end X4Fclause
p2m_reactivate "P2MW.S_ModularCurve_residualRealization_of_occurs.ModularCurve.X4IntegralSide.LatticeMod P2MW.S_ModularCurve_residualRealization_of_occurs.ModularCurve.X4IntegralSide P2MW.S_ModularCurve_residualRealization_of_occurs.ModularCurve P2MW.S_ModularCurve_residualRealization_of_occurs.ModularCurve.X4DvrSource"

namespace X4Det

variable (p : ℕ) [Fact p.Prime] (J : Type) [AddCommGroup J] [Module HeckeAlg J]
  (G : Type) [Monoid G] [DistribMulAction G J]

scoped instance isMulCommutative_rationalHeckeAlgebra : IsMulCommutative (rationalHeckeAlgebra p J) :=
  Algebra.isMulCommutative_adjoin ℚ_[p] (by
    rintro _ ⟨s, rfl⟩ _ ⟨t, rfl⟩
    rw [← map_mul, ← map_mul, mul_comm])

theorem rep_mul_tateHeckeRep [SMulCommClass G HeckeAlg J] (g : G) (t : HeckeAlg) :
    TateModule.rep p J G g * tateHeckeRep p J t = tateHeckeRep p J t * TateModule.rep p J G g := by
  refine LinearMap.ext fun x => Subtype.ext (funext fun n => ?_)
  show g • (t • (x : ℕ → J) n) = t • (g • (x : ℕ → J) n)
  exact smul_comm g t ((x : ℕ → J) n)

theorem rationalGaloisRep_mul_rationalHeckeRep [SMulCommClass G HeckeAlg J] (g : G) (t : HeckeAlg) :
    rationalGaloisRep p J G g * rationalHeckeRep p J t
      = rationalHeckeRep p J t * rationalGaloisRep p J G g := by
  rw [rationalGaloisRep_apply, rationalHeckeRep_apply, ← LinearMap.baseChange_mul,
    ← LinearMap.baseChange_mul, rep_mul_tateHeckeRep]

theorem commute_rationalGaloisRep_of_mem [SMulCommClass G HeckeAlg J] (g : G)
    {a : Module.End ℚ_[p] (RationalTateModule p J)} (ha : a ∈ rationalHeckeAlgebra p J) :
    Commute (rationalGaloisRep p J G g) a :=
  Algebra.commute_of_mem_adjoin_of_forall_mem_commute ha (by
    rintro _ ⟨t, rfl⟩
    exact rationalGaloisRep_mul_rationalHeckeRep p J G g t)

def rationalGaloisRepLinear [SMulCommClass G HeckeAlg J] :
    G →* (RationalTateModule p J →ₗ[rationalHeckeAlgebra p J] RationalTateModule p J) where
  toFun g :=
    { toFun := rationalGaloisRep p J G g
      map_add' := map_add _
      map_smul' := fun a v => by
        show rationalGaloisRep p J G g ((a : Module.End ℚ_[p] (RationalTateModule p J)) v)
          = (a : Module.End ℚ_[p] (RationalTateModule p J)) (rationalGaloisRep p J G g v)
        exact LinearMap.congr_fun (commute_rationalGaloisRep_of_mem p J G g a.2).eq v }
  map_one' := LinearMap.ext fun v => by
    show rationalGaloisRep p J G 1 v = v
    rw [map_one]
    rfl
  map_mul' g h := LinearMap.ext fun v => by
    show rationalGaloisRep p J G (g * h) v = rationalGaloisRep p J G g (rationalGaloisRep p J G h v)
    rw [map_mul]
    rfl

theorem rationalGaloisRepLinear_apply [SMulCommClass G HeckeAlg J] (g : G)
    (v : RationalTateModule p J) :
    rationalGaloisRepLinear p J G g v = rationalGaloisRep p J G g v :=
  rfl

open scoped IsMulCommutative in

theorem det_rationalGaloisRepLinear_eq [SMulCommClass G HeckeAlg J] (g : G)
    (b : Module.Basis (Fin 2) (rationalHeckeAlgebra p J) (RationalTateModule p J)) :
    LinearMap.det (rationalGaloisRepLinear p J G g)
      = (b.repr (rationalGaloisRep p J G g (b 0))) 0 * (b.repr (rationalGaloisRep p J G g (b 1))) 1
        - (b.repr (rationalGaloisRep p J G g (b 1))) 0
          * (b.repr (rationalGaloisRep p J G g (b 0))) 1 := by
  rw [← LinearMap.det_toMatrix b, Matrix.det_fin_two]
  simp only [LinearMap.toMatrix_apply, rationalGaloisRepLinear_apply]

end X4Det
p2m_reactivate "P2MW.S_ModularCurve_residualRealization_of_occurs.ModularCurve.X4IntegralSide.LatticeMod P2MW.S_ModularCurve_residualRealization_of_occurs.ModularCurve.X4IntegralSide P2MW.S_ModularCurve_residualRealization_of_occurs.ModularCurve P2MW.S_ModularCurve_residualRealization_of_occurs.ModularCurve.X4DvrSource P2MW.S_ModularCurve_residualRealization_of_occurs.ModularCurve.X4Det"

end ModularCurve
p2m_reactivate "P2MW.S_ModularCurve_residualRealization_of_occurs.ModularCurve.X4IntegralSide.LatticeMod P2MW.S_ModularCurve_residualRealization_of_occurs.ModularCurve.X4IntegralSide P2MW.S_ModularCurve_residualRealization_of_occurs.ModularCurve P2MW.S_ModularCurve_residualRealization_of_occurs.ModularCurve.X4DvrSource P2MW.S_ModularCurve_residualRealization_of_occurs.ModularCurve.X4Det"

end
p2m_reactivate "P2MW.S_ModularCurve_residualRealization_of_occurs.ModularCurve.X4IntegralSide.LatticeMod P2MW.S_ModularCurve_residualRealization_of_occurs.ModularCurve.X4IntegralSide P2MW.S_ModularCurve_residualRealization_of_occurs.ModularCurve P2MW.S_ModularCurve_residualRealization_of_occurs.ModularCurve.X4DvrSource P2MW.S_ModularCurve_residualRealization_of_occurs.ModularCurve.X4Det"

set_option autoImplicit false

noncomputable section

p2m_open "ModularCurve~baseChangeHom~baseChangeHom_injective P2MW.S_ModularCurve_residualRealization_of_occurs.ModularCurve P2MW.S_ModularCurve_residualRealization_of_occurs.ModularCurve.X4IntegralSide P2MW.S_ModularCurve_residualRealization_of_occurs.ModularCurve.X4LocalRing"

namespace ModularCurve
p2m_export "ModularCurve" "tateHeckeRep coe_tateHeckeRep_apply_apply RationalTateModule rationalGaloisRep rationalGaloisRep_apply rationalHeckeRep rationalHeckeRep_apply rationalHeckeRep_tmul rationalHeckeAlgebra rationalHeckeRep_mem_rationalHeckeAlgebra RationalRankTwoCyclotomicOf RationalRankTwoCyclotomic modularFunctionFieldBar JZero HeckeAlg heckeTorsion IsResidualRealization CyclotomicDeterminant heckeModuleBar rationalRankTwoCyclotomic_family JZero.torsion_fixed_by_open JZero.exists_abelJacobiCard heckeOperatorsCommuteBar smulCommClass_JZero_of_heckeOperatorsCommuteBar"
namespace X4Psi0Source
p2m_open "ModularCurve~baseChangeHom~baseChangeHom_injective"

variable (p : ℕ) [Fact p.Prime] (J : Type) [AddCommGroup J] [Module HeckeAlg J]
  [Module.Finite ℤ_[p] (TateModule p J)] [Module.Free ℤ_[p] (TateModule p J)]

section Checks
#check @Localization.subalgebra.ofField
#check @Localization.subalgebra.isLocalization_ofField
#check @RingHom.exists_comp_algebraMap_eq_of_isIntegral_of_isAlgClosed
end Checks
p2m_reactivate "P2MW.S_ModularCurve_residualRealization_of_occurs.ModularCurve.X4IntegralSide.LatticeMod P2MW.S_ModularCurve_residualRealization_of_occurs.ModularCurve.X4IntegralSide P2MW.S_ModularCurve_residualRealization_of_occurs.ModularCurve P2MW.S_ModularCurve_residualRealization_of_occurs.ModularCurve.X4DvrSource P2MW.S_ModularCurve_residualRealization_of_occurs.ModularCurve.X4Det"

variable (𝔓 : Ideal (IntegralHeckeRing p J)) [𝔓.IsPrime]
  [instFact : Fact ((algebraMap ℤ_[p] (IntegralHeckeRing p J) p) ∉ 𝔓)]

local notation "κ" => Ideal.ResidueField 𝔓
local notation "𝒪κ" => integralClosure ℤ_[p] (Ideal.ResidueField 𝔓)

omit instFact in

theorem algebraMap_mem_integralClosure (a : IntegralHeckeRing p J) :
    algebraMap (IntegralHeckeRing p J) κ a ∈ 𝒪κ :=
  ((Algebra.IsIntegral.isIntegral (R := ℤ_[p]) a).map
    (IsScalarTower.toAlgHom ℤ_[p] (IntegralHeckeRing p J) κ))

omit instFact in

def heckeToIntegralClosure : IntegralHeckeRing p J →+* 𝒪κ :=
  (algebraMap (IntegralHeckeRing p J) κ).codRestrict (𝒪κ).toSubring
    (algebraMap_mem_integralClosure p J 𝔓)

variable (k : Type) [Field k] [IsAlgClosed k] [Algebra ℤ_[p] k]
  (φ₀ : IntegralHeckeRing p J →ₐ[ℤ_[p]] k)

omit instFact in

theorem exists_integralClosure_ringHom (h𝔓 : 𝔓 ≤ RingHom.ker φ₀.toRingHom) :
    ∃ ψ₀₀ : 𝒪κ →+* k,
      ∀ a : IntegralHeckeRing p J, ψ₀₀ (heckeToIntegralClosure p J 𝔓 a) = φ₀ a := by

  letI : Algebra (IntegralHeckeRing p J) 𝒪κ := (heckeToIntegralClosure p J 𝔓).toAlgebra
  haveI : IsScalarTower ℤ_[p] (IntegralHeckeRing p J) 𝒪κ :=
    IsScalarTower.of_algebraMap_eq (fun r => Subtype.ext
      (IsScalarTower.algebraMap_apply ℤ_[p] (IntegralHeckeRing p J) κ r))
  haveI : Algebra.IsIntegral (IntegralHeckeRing p J) 𝒪κ :=
    Algebra.IsIntegral.tower_top (R := ℤ_[p])
  have hker : RingHom.ker (algebraMap (IntegralHeckeRing p J) 𝒪κ) ≤ RingHom.ker φ₀.toRingHom := by
    intro a ha
    apply h𝔓
    rw [← Ideal.ker_algebraMap_residueField (I := 𝔓), RingHom.mem_ker]
    have h0 : (algebraMap (IntegralHeckeRing p J) 𝒪κ a : κ) = ((0 : 𝒪κ) : κ) :=
      congrArg Subtype.val (RingHom.mem_ker.1 ha)
    exact h0.trans (ZeroMemClass.coe_zero _)
  obtain ⟨ψ₀₀, hψ₀₀⟩ :=
    RingHom.exists_comp_algebraMap_eq_of_isIntegral_of_isAlgClosed φ₀.toRingHom hker
  exact ⟨ψ₀₀, fun a => RingHom.congr_fun hψ₀₀ a⟩

theorem exists_sourced_subalgebra (hp : (p : k) = 0) (h𝔓 : 𝔓 ≤ RingHom.ker φ₀.toRingHom) :
    ∃ (𝒪 : Subalgebra ℤ_[p] κ) (_ : IsPrincipalIdealRing ↥𝒪) (_ : IsFractionRing ↥𝒪 κ)
      (ψ : ↥𝒪 →+* k)
      (h𝒪 : ∀ a : IntegralHeckeRing p J, algebraMap (IntegralHeckeRing p J) κ a ∈ 𝒪),
      (∀ a : IntegralHeckeRing p J, ψ ⟨_, h𝒪 a⟩ = φ₀ a) ∧
      ψ (algebraMap ℤ_[p] ↥𝒪 p) = 0 := by

  obtain ⟨ψ₀₀, hψ₀₀⟩ := exists_integralClosure_ringHom p J 𝔓 k φ₀ h𝔓
  have hψp : ψ₀₀ (p : 𝒪κ) = 0 := by rw [map_natCast ψ₀₀ p]; exact hp

  obtain ⟨𝒪, hPID, hFrac, ψ, h𝒪', hψ', hψp'⟩ :=
    X4DvrSource.exists_dvr_packet p κ k ψ₀₀ hψp

  refine ⟨𝒪, hPID, hFrac, ψ, fun a => h𝒪' (heckeToIntegralClosure p J 𝔓 a), fun a => ?_, hψp'⟩
  rw [show (⟨algebraMap (IntegralHeckeRing p J) κ a, h𝒪' (heckeToIntegralClosure p J 𝔓 a)⟩ : ↥𝒪)
        = ⟨heckeToIntegralClosure p J 𝔓 a, h𝒪' _⟩ from rfl, hψ', hψ₀₀]

end ModularCurve.X4Psi0Source
p2m_reactivate "P2MW.S_ModularCurve_residualRealization_of_occurs.ModularCurve.X4IntegralSide.LatticeMod P2MW.S_ModularCurve_residualRealization_of_occurs.ModularCurve.X4IntegralSide P2MW.S_ModularCurve_residualRealization_of_occurs.ModularCurve P2MW.S_ModularCurve_residualRealization_of_occurs.ModularCurve.X4DvrSource P2MW.S_ModularCurve_residualRealization_of_occurs.ModularCurve.X4Det"
p2m_reactivate "P2MW.S_ModularCurve_residualRealization_of_occurs.ModularCurve.X4IntegralSide.LatticeMod P2MW.S_ModularCurve_residualRealization_of_occurs.ModularCurve.X4IntegralSide P2MW.S_ModularCurve_residualRealization_of_occurs.ModularCurve P2MW.S_ModularCurve_residualRealization_of_occurs.ModularCurve.X4DvrSource P2MW.S_ModularCurve_residualRealization_of_occurs.ModularCurve.X4Det"

end
p2m_reactivate "P2MW.S_ModularCurve_residualRealization_of_occurs.ModularCurve.X4IntegralSide.LatticeMod P2MW.S_ModularCurve_residualRealization_of_occurs.ModularCurve.X4IntegralSide P2MW.S_ModularCurve_residualRealization_of_occurs.ModularCurve P2MW.S_ModularCurve_residualRealization_of_occurs.ModularCurve.X4DvrSource P2MW.S_ModularCurve_residualRealization_of_occurs.ModularCurve.X4Det"

set_option autoImplicit false

noncomputable section

namespace ModularCurve
p2m_export "ModularCurve" "tateHeckeRep coe_tateHeckeRep_apply_apply RationalTateModule rationalGaloisRep rationalGaloisRep_apply rationalHeckeRep rationalHeckeRep_apply rationalHeckeRep_tmul rationalHeckeAlgebra rationalHeckeRep_mem_rationalHeckeAlgebra RationalRankTwoCyclotomicOf RationalRankTwoCyclotomic modularFunctionFieldBar JZero HeckeAlg heckeTorsion IsResidualRealization CyclotomicDeterminant heckeModuleBar rationalRankTwoCyclotomic_family JZero.torsion_fixed_by_open JZero.exists_abelJacobiCard heckeOperatorsCommuteBar smulCommClass_JZero_of_heckeOperatorsCommuteBar"
namespace X4DetTop
p2m_open "ModularCurve~baseChangeHom~baseChangeHom_injective"

p2m_open "ModularCurve~baseChangeHom~baseChangeHom_injective P2MW.S_ModularCurve_residualRealization_of_occurs.ModularCurve P2MW.S_ModularCurve_residualRealization_of_occurs.ModularCurve.X4Det"

variable {K L : Type} [Field K] [Field L] [Algebra K L]
variable (N p : ℕ) [Fact p.Prime] (J : Type) [AddCommGroup J] [Module HeckeAlg J]
  [DistribMulAction (L ≃ₐ[K] L) J] [SMulCommClass (L ≃ₐ[K] L) HeckeAlg J]

open scoped IsMulCommutative in

theorem det_rationalGaloisRepLinear_eq_of_rationalRankTwo
    (h : RationalRankTwoCyclotomicOf (K := K) (L := L) N p J) :
    ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ N * p →
      ∀ A' : ValuationSubring L, A'.LiesOverPrime ℓ →
        ∀ σ : L ≃ₐ[K] L, A'.IsFrobeniusAt σ ℓ →
          LinearMap.det (rationalGaloisRepLinear p J (L ≃ₐ[K] L) σ)
            = (ℓ : rationalHeckeAlgebra p J) := by
  obtain ⟨b, hb⟩ := h
  intro ℓ hℓ hNp A' hA' σ hσ
  rw [det_rationalGaloisRepLinear_eq p J (L ≃ₐ[K] L) σ b]
  exact hb ℓ hℓ hNp A' hA' σ hσ

end ModularCurve.X4DetTop
p2m_reactivate "P2MW.S_ModularCurve_residualRealization_of_occurs.ModularCurve.X4IntegralSide.LatticeMod P2MW.S_ModularCurve_residualRealization_of_occurs.ModularCurve.X4IntegralSide P2MW.S_ModularCurve_residualRealization_of_occurs.ModularCurve P2MW.S_ModularCurve_residualRealization_of_occurs.ModularCurve.X4DvrSource P2MW.S_ModularCurve_residualRealization_of_occurs.ModularCurve.X4Det"
p2m_reactivate "P2MW.S_ModularCurve_residualRealization_of_occurs.ModularCurve.X4IntegralSide.LatticeMod P2MW.S_ModularCurve_residualRealization_of_occurs.ModularCurve.X4IntegralSide P2MW.S_ModularCurve_residualRealization_of_occurs.ModularCurve P2MW.S_ModularCurve_residualRealization_of_occurs.ModularCurve.X4DvrSource P2MW.S_ModularCurve_residualRealization_of_occurs.ModularCurve.X4Det"

end
p2m_reactivate "P2MW.S_ModularCurve_residualRealization_of_occurs.ModularCurve.X4IntegralSide.LatticeMod P2MW.S_ModularCurve_residualRealization_of_occurs.ModularCurve.X4IntegralSide P2MW.S_ModularCurve_residualRealization_of_occurs.ModularCurve P2MW.S_ModularCurve_residualRealization_of_occurs.ModularCurve.X4DvrSource P2MW.S_ModularCurve_residualRealization_of_occurs.ModularCurve.X4Det"

set_option autoImplicit false

noncomputable section

p2m_open "Submodule IsLocalRing AlgebraicCurve P2MW.S_ModularCurve_residualRealization_of_occurs.AlgebraicCurve"

namespace TateModule
p2m_export "TateModule" "torsion compat compat_pow coe_add coe_zero natCast_smul_eq_of_zmod_eq toZModPow_eq_appr smul_apply natCast_padicInt_smul_apply proj proj_apply proj_mem_torsionBy proj_eq_zero_iff rep rep_apply mem_torsionBy_one_of_smul_eq_zero smul_eq_zero_of_mem_torsionBy_one finite_torsionBy mulP kerMulPEquiv mulP_surjective liftFun liftFun_of_le coe_liftAux_congr liftFun_mem proj_surjective exists_pair_of_card_eq_sq exists_indep_pair_torsionBy_one dvd_of_rel_apply levelMap levelMap_injective levelMap_bijective exists_eq_levelMap linearIndependent_pair mem_span_pair exists_pair top_le_span_pair basisOfCard free finite finrank_eq_two"
p2m_open "TateModule"

variable {p : ℕ} {M : Type} [AddCommGroup M] [Fact p.Prime]

theorem finite_torsionBy_of_card_pow (d : ℕ)
    (hcard : ∀ n : ℕ, Nat.card (torsionBy ℤ M ((p ^ n : ℕ) : ℤ)) = (p ^ n) ^ d) (n : ℕ) :
    Finite (torsionBy ℤ M ((p ^ n : ℕ) : ℤ)) :=
  Nat.finite_of_card_ne_zero (by
    rw [hcard n]; exact pow_ne_zero _ (pow_ne_zero _ (Fact.out : p.Prime).ne_zero))

theorem mulP_surjective_of_card_pow (d : ℕ)
    (hcard : ∀ n : ℕ, Nat.card (torsionBy ℤ M ((p ^ n : ℕ) : ℤ)) = (p ^ n) ^ d) (n : ℕ) :
    Function.Surjective (mulP p M n) := by
  haveI := finite_torsionBy_of_card_pow d hcard (n + 1)
  haveI := finite_torsionBy_of_card_pow d hcard n
  have hker : Nat.card (mulP p M n).ker = p ^ d := by
    rw [Nat.card_congr (kerMulPEquiv p M n), hcard 1, pow_one]
  have h := AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup (mulP p M n).ker
  rw [hcard (n + 1),
    Nat.card_congr (QuotientAddGroup.quotientKerEquivRange (mulP p M n)).toEquiv, hker] at h
  have hrange : Nat.card (mulP p M n).range = Nat.card (torsionBy ℤ M ((p ^ n : ℕ) : ℤ)) := by
    rw [hcard n]
    refine Nat.eq_of_mul_eq_mul_right (pow_pos (Fact.out : p.Prime).pos d) ?_
    rw [← h]; ring
  rw [← AddMonoidHom.range_eq_top]
  exact AddSubgroup.eq_top_of_card_eq _ hrange

theorem proj_surjective_of_card_pow (d : ℕ)
    (hcard : ∀ n : ℕ, Nat.card (torsionBy ℤ M ((p ^ n : ℕ) : ℤ)) = (p ^ n) ^ d) (n : ℕ) :
    ∀ m ∈ torsionBy ℤ M ((p ^ n : ℕ) : ℤ), ∃ x : TateModule p M, proj p M n x = m := by
  intro m hm
  choose next hnext using fun k (m' : torsionBy ℤ M ((p ^ k : ℕ) : ℤ)) =>
    mulP_surjective_of_card_pow d hcard k m'
  refine ⟨⟨liftFun next n ⟨m, hm⟩,
    liftFun_mem (fun k m' => congrArg Subtype.val (hnext k m')) n ⟨m, hm⟩⟩, ?_⟩
  rw [proj_apply]
  change liftFun next n ⟨m, hm⟩ n = m
  rw [liftFun_of_le le_rfl, coe_liftAux_congr (Nat.sub_self n)]
  rfl

omit [Fact p.Prime] in

theorem coe_sum_apply {ι : Type} (s : Finset ι) (v : ι → TateModule p M) (n : ℕ) :
    ((↑(∑ i ∈ s, v i) : ℕ → M)) n = ∑ i ∈ s, (v i : ℕ → M) n :=
  map_sum (proj p M n) v s

theorem exists_tuple_of_card_pow {d : ℕ} {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    [Finite V] (hV : Nat.card V = p ^ d) :
    ∃ v : Fin d → V, ∀ a : Fin d → ℤ, ∑ i, a i • v i = 0 → ∀ i, (p : ℤ) ∣ a i := by
  have hp : p.Prime := Fact.out
  have hrank : Module.finrank (ZMod p) V = d := by
    have h := Module.natCard_eq_pow_finrank (K := ZMod p) (V := V)
    rw [hV, Nat.card_zmod] at h
    exact (Nat.pow_right_injective hp.two_le h).symm
  let b := Module.finBasisOfFinrankEq (ZMod p) V hrank
  refine ⟨⇑b, fun a h i => ?_⟩
  have h' : ∑ j, ((a j : ZMod p)) • b j = 0 := by
    calc ∑ j, ((a j : ZMod p)) • b j = ∑ j, a j • b j :=
          Finset.sum_congr rfl fun j _ => by rw [Int.cast_smul_eq_zsmul]
      _ = 0 := h
  have hli := (Fintype.linearIndependent_iff.mp b.linearIndependent)
    (fun j => (a j : ZMod p)) h'
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd (a i) p).mp (hli i)

theorem exists_indep_tuple_torsionBy_one (d : ℕ)
    (hcard : ∀ n : ℕ, Nat.card (torsionBy ℤ M ((p ^ n : ℕ) : ℤ)) = (p ^ n) ^ d) :
    ∃ e : Fin d → M, (∀ i, e i ∈ torsionBy ℤ M ((p ^ 1 : ℕ) : ℤ)) ∧
      ∀ a : Fin d → ℤ, ∑ i, a i • e i = 0 → ∀ i, (p : ℤ) ∣ a i := by
  haveI := finite_torsionBy_of_card_pow d hcard 1
  have hmod : ∀ m : torsionBy ℤ M ((p ^ 1 : ℕ) : ℤ), p • m = 0 := fun m =>
    Subtype.ext (by
      rw [coe_smul_of_tower, ← Nat.cast_smul_eq_nsmul ℤ, Submodule.coe_zero]
      exact smul_eq_zero_of_mem_torsionBy_one m.2)
  letI : Module (ZMod p) (torsionBy ℤ M ((p ^ 1 : ℕ) : ℤ)) := AddCommGroup.zmodModule hmod
  have h1 : Nat.card (torsionBy ℤ M ((p ^ 1 : ℕ) : ℤ)) = p ^ d := by rw [hcard 1, pow_one]
  obtain ⟨v, hv⟩ := exists_tuple_of_card_pow h1
  have hcoe : ∀ a : Fin d → ℤ,
      ((∑ i, a i • v i : torsionBy ℤ M ((p ^ 1 : ℕ) : ℤ)) : M) = ∑ i, a i • (v i : M) :=
    fun a => map_sum ((torsionBy ℤ M ((p ^ 1 : ℕ) : ℤ)).subtype) (fun i => a i • v i)
      Finset.univ
  exact ⟨fun i => (v i : M), fun i => (v i).2,
    fun a ha => hv a (Subtype.ext ((hcoe a).trans ha))⟩

omit [Fact p.Prime] in

theorem dvd_of_rel_apply_tuple {d : ℕ} {x : Fin d → TateModule p M}
    (h1 : ∀ a : Fin d → ℤ, ∑ i, a i • (x i : ℕ → M) 1 = 0 → ∀ i, (p : ℤ) ∣ a i) :
    ∀ (n : ℕ) (a : Fin d → ℤ), ∑ i, a i • (x i : ℕ → M) n = 0 →
      ∀ i, ((p ^ n : ℕ) : ℤ) ∣ a i := by
  intro n
  induction n with
  | zero => intro a _ i; simp
  | succ n ih =>
    intro a hab
    have hab1 : ∑ i, a i • (x i : ℕ → M) 1 = 0 := by
      have h := congrArg (((p ^ n : ℕ) : ℤ) • ·) hab
      simp only [smul_zero] at h
      rw [Finset.smul_sum] at h
      calc ∑ i, a i • (x i : ℕ → M) 1
          = ∑ i, ((p ^ n : ℕ) : ℤ) • a i • (x i : ℕ → M) (n + 1) := by
            refine Finset.sum_congr rfl fun i _ => ?_
            have hc : ((p ^ n : ℕ) : ℤ) • (x i : ℕ → M) (n + 1) = (x i : ℕ → M) 1 := by
              have h' := compat_pow (x i) 1 n
              rwa [Nat.add_comm 1 n] at h'
            rw [smul_comm, hc]
        _ = 0 := h
    choose a' ha' using h1 a hab1
    have hab' : ∑ i, a' i • (x i : ℕ → M) n = 0 := by
      calc ∑ i, a' i • (x i : ℕ → M) n
          = ∑ i, a i • (x i : ℕ → M) (n + 1) := by
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [ha' i, mul_comm, mul_smul, compat]
        _ = 0 := hab
    intro i
    rw [ha' i, pow_succ', Nat.cast_mul]
    exact mul_dvd_mul_left _ (ih a' hab' i)

noncomputable def levelMapTuple {d : ℕ} (x : Fin d → TateModule p M) (n : ℕ)
    (c : Fin d → ZMod (p ^ n)) : torsionBy ℤ M ((p ^ n : ℕ) : ℤ) :=
  ⟨∑ i, ((c i).val : ℤ) • (x i : ℕ → M) n, by
    rw [mem_torsionBy_iff, Finset.smul_sum]
    exact Finset.sum_eq_zero fun i _ => by rw [smul_comm, torsion, smul_zero]⟩

theorem levelMapTuple_injective {d : ℕ} {x : Fin d → TateModule p M}
    (h1 : ∀ a : Fin d → ℤ, ∑ i, a i • (x i : ℕ → M) 1 = 0 → ∀ i, (p : ℤ) ∣ a i) (n : ℕ) :
    Function.Injective (levelMapTuple x n) := by
  haveI : NeZero (p ^ n) := ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩
  intro c c' h
  have hsub : (∑ i, ((c i).val : ℤ) • (x i : ℕ → M) n)
      - ∑ i, ((c' i).val : ℤ) • (x i : ℕ → M) n = 0 := by
    have h' := sub_eq_zero.mpr (congrArg Subtype.val h)
    simpa only [levelMapTuple] using h'
  have h' : ∑ i, (((c i).val : ℤ) - ((c' i).val : ℤ)) • (x i : ℕ → M) n = 0 := by
    calc ∑ i, (((c i).val : ℤ) - ((c' i).val : ℤ)) • (x i : ℕ → M) n
        = (∑ i, ((c i).val : ℤ) • (x i : ℕ → M) n)
            - ∑ i, ((c' i).val : ℤ) • (x i : ℕ → M) n := by
          rw [← Finset.sum_sub_distrib]
          exact Finset.sum_congr rfl fun i _ => sub_smul _ _ _
      _ = 0 := hsub
  have hdvd := dvd_of_rel_apply_tuple h1 n _ h'
  have key : ∀ {u v : ZMod (p ^ n)}, ((p ^ n : ℕ) : ℤ) ∣ (u.val : ℤ) - v.val → u = v :=
    fun {u v} huv => by
      have h'' := (ZMod.intCast_eq_intCast_iff_dvd_sub (v.val : ℤ) (u.val : ℤ) (p ^ n)).mpr huv
      rwa [Int.cast_natCast, Int.cast_natCast, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val,
        eq_comm] at h''
  exact funext fun i => key (hdvd i)

theorem levelMapTuple_bijective (d : ℕ)
    (hcard : ∀ n : ℕ, Nat.card (torsionBy ℤ M ((p ^ n : ℕ) : ℤ)) = (p ^ n) ^ d)
    {x : Fin d → TateModule p M}
    (h1 : ∀ a : Fin d → ℤ, ∑ i, a i • (x i : ℕ → M) 1 = 0 → ∀ i, (p : ℤ) ∣ a i) (n : ℕ) :
    Function.Bijective (levelMapTuple x n) := by
  haveI := finite_torsionBy_of_card_pow d hcard n
  refine (levelMapTuple_injective h1 n).bijective_of_nat_card_le ?_
  rw [hcard n, Nat.card_fun, Nat.card_zmod, Nat.card_fin]

theorem exists_eq_levelMapTuple (d : ℕ)
    (hcard : ∀ n : ℕ, Nat.card (torsionBy ℤ M ((p ^ n : ℕ) : ℤ)) = (p ^ n) ^ d)
    {x : Fin d → TateModule p M}
    (h1 : ∀ a : Fin d → ℤ, ∑ i, a i • (x i : ℕ → M) 1 = 0 → ∀ i, (p : ℤ) ∣ a i) (n : ℕ)
    {m : M} (hm : m ∈ torsionBy ℤ M ((p ^ n : ℕ) : ℤ)) :
    ∃ c : Fin d → ℕ, ∑ i, (c i : ℤ) • (x i : ℕ → M) n = m := by
  obtain ⟨c, h⟩ := (levelMapTuple_bijective d hcard h1 n).2 ⟨m, hm⟩
  exact ⟨fun i => (c i).val, congrArg Subtype.val h⟩

theorem linearIndependent_tuple {d : ℕ} {x : Fin d → TateModule p M}
    (h1 : ∀ a : Fin d → ℤ, ∑ i, a i • (x i : ℕ → M) 1 = 0 → ∀ i, (p : ℤ) ∣ a i) :
    LinearIndependent ℤ_[p] x := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have hlev : ∀ (n : ℕ) (i : Fin d), ((p ^ n : ℕ) : ℤ) ∣ ((g i).appr n : ℤ) := fun n =>
    dvd_of_rel_apply_tuple h1 n _ (by
      have h := congrArg (fun z : TateModule p M => (z : ℕ → M) n) hg
      simpa only [coe_sum_apply, smul_apply, coe_zero, Pi.zero_apply] using h)
  have key : ∀ {u : ℤ_[p]}, (∀ n, ((p ^ n : ℕ) : ℤ) ∣ (u.appr n : ℤ)) → u = 0 := fun {u} hu =>
    PadicInt.ext_of_toZModPow.mp fun n => by
      rw [map_zero, toZModPow_eq_appr, ZMod.natCast_eq_zero_iff]
      exact Int.natCast_dvd_natCast.mp (hu n)
  exact fun i => key fun n => hlev n i

theorem mem_span_tuple (d : ℕ)
    (hcard : ∀ n : ℕ, Nat.card (torsionBy ℤ M ((p ^ n : ℕ) : ℤ)) = (p ^ n) ^ d)
    {x : Fin d → TateModule p M}
    (h1 : ∀ a : Fin d → ℤ, ∑ i, a i • (x i : ℕ → M) 1 = 0 → ∀ i, (p : ℤ) ∣ a i)
    (z : TateModule p M) : ∃ s : Fin d → ℤ_[p], ∑ i, s i • x i = z := by
  choose a ha using fun n => exists_eq_levelMapTuple d hcard h1 n (proj_mem_torsionBy n z)
  have ha' : ∀ n, ∑ i, (a n i : ℤ) • (x i : ℕ → M) n = (z : ℕ → M) n := fun n => ha n
  have hcompat : ∀ (n : ℕ) (i : Fin d),
      ((p ^ n : ℕ) : ℤ) ∣ (a (n + 1) i : ℤ) - (a n i : ℤ) := by
    intro n
    refine dvd_of_rel_apply_tuple h1 n (fun i => (a (n + 1) i : ℤ) - (a n i : ℤ)) ?_
    show ∑ i, ((a (n + 1) i : ℤ) - (a n i : ℤ)) • (x i : ℕ → M) n = 0
    have hstep : ∑ i, (a (n + 1) i : ℤ) • (x i : ℕ → M) n = (z : ℕ → M) n := by
      calc ∑ i, (a (n + 1) i : ℤ) • (x i : ℕ → M) n
          = ∑ i, ((p : ℕ) : ℤ) • (a (n + 1) i : ℤ) • (x i : ℕ → M) (n + 1) :=
            Finset.sum_congr rfl fun i _ => by rw [smul_comm, compat]
        _ = ((p : ℕ) : ℤ) • ∑ i, (a (n + 1) i : ℤ) • (x i : ℕ → M) (n + 1) :=
            (Finset.smul_sum).symm
        _ = ((p : ℕ) : ℤ) • (z : ℕ → M) (n + 1) := by rw [ha' (n + 1)]
        _ = (z : ℕ → M) n := compat z n
    calc ∑ i, ((a (n + 1) i : ℤ) - (a n i : ℤ)) • (x i : ℕ → M) n
        = (∑ i, (a (n + 1) i : ℤ) • (x i : ℕ → M) n)
            - ∑ i, (a n i : ℤ) • (x i : ℕ → M) n := by
          rw [← Finset.sum_sub_distrib]
          exact Finset.sum_congr rfl fun i _ => sub_smul _ _ _
      _ = 0 := by rw [hstep, ha' n, sub_self]
  have hca : ∀ (i : Fin d) (k : ℕ),
      (p : ℤ) ^ k ∣ (fun j => (a j i : ℤ)) (k + 1) - (fun j => (a j i : ℤ)) k := fun i k => by
    rw [← Nat.cast_pow]; exact hcompat k i
  refine ⟨fun i => PadicInt.ofIntSeq (fun j => (a j i : ℤ))
    (PadicInt.isCauSeq_padicNorm_of_pow_dvd_sub _ p (hca i)), Subtype.ext (funext fun n => ?_)⟩
  rw [coe_sum_apply, ← ha' n]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [smul_apply]
  refine natCast_smul_eq_of_zmod_eq (torsion (x i) n) ?_
  rw [← toZModPow_eq_appr,
    PadicInt.toZModPow_ofIntSeq_of_pow_dvd_sub (fun j => (a j i : ℤ)) p (hca i) n,
    Int.cast_natCast]

theorem exists_tuple_of_hcard (d : ℕ)
    (hcard : ∀ n : ℕ, Nat.card (torsionBy ℤ M ((p ^ n : ℕ) : ℤ)) = (p ^ n) ^ d) :
    ∃ x : Fin d → TateModule p M,
      ∀ a : Fin d → ℤ, ∑ i, a i • (x i : ℕ → M) 1 = 0 → ∀ i, (p : ℤ) ∣ a i := by
  obtain ⟨e, he, h1⟩ := exists_indep_tuple_torsionBy_one d hcard
  choose x hx using fun i => proj_surjective_of_card_pow d hcard 1 (e i) (he i)
  have hx' : ∀ i, (x i : ℕ → M) 1 = e i := fun i => hx i
  refine ⟨x, fun a ha => h1 a ?_⟩
  calc ∑ i, a i • e i = ∑ i, a i • (x i : ℕ → M) 1 :=
        Finset.sum_congr rfl fun i _ => by rw [hx' i]
    _ = 0 := ha

theorem top_le_span_tuple (d : ℕ)
    (hcard : ∀ n : ℕ, Nat.card (torsionBy ℤ M ((p ^ n : ℕ) : ℤ)) = (p ^ n) ^ d)
    {x : Fin d → TateModule p M}
    (h1 : ∀ a : Fin d → ℤ, ∑ i, a i • (x i : ℕ → M) 1 = 0 → ∀ i, (p : ℤ) ∣ a i) :
    ⊤ ≤ span ℤ_[p] (Set.range x) := by
  intro z _
  obtain ⟨s, hs⟩ := mem_span_tuple d hcard h1 z
  rw [← hs]
  exact Submodule.sum_smul_mem _ _ fun i _ => Submodule.subset_span ⟨i, rfl⟩

noncomputable def basisOfCardPow (d : ℕ)
    (hcard : ∀ n : ℕ, Nat.card (torsionBy ℤ M ((p ^ n : ℕ) : ℤ)) = (p ^ n) ^ d) :
    Module.Basis (Fin d) ℤ_[p] (TateModule p M) :=
  Module.Basis.mk (v := (exists_tuple_of_hcard d hcard).choose)
    (linearIndependent_tuple (exists_tuple_of_hcard d hcard).choose_spec)
    (top_le_span_tuple d hcard (exists_tuple_of_hcard d hcard).choose_spec)

theorem free_of_card_pow (d : ℕ)
    (hcard : ∀ n : ℕ, Nat.card (torsionBy ℤ M ((p ^ n : ℕ) : ℤ)) = (p ^ n) ^ d) :
    Module.Free ℤ_[p] (TateModule p M) :=
  Module.Free.of_basis (basisOfCardPow d hcard)

theorem finite_of_card_pow (d : ℕ)
    (hcard : ∀ n : ℕ, Nat.card (torsionBy ℤ M ((p ^ n : ℕ) : ℤ)) = (p ^ n) ^ d) :
    Module.Finite ℤ_[p] (TateModule p M) :=
  Module.Finite.of_basis (basisOfCardPow d hcard)

theorem finrank_eq_of_card_pow (d : ℕ)
    (hcard : ∀ n : ℕ, Nat.card (torsionBy ℤ M ((p ^ n : ℕ) : ℤ)) = (p ^ n) ^ d) :
    Module.finrank ℤ_[p] (TateModule p M) = d := by
  rw [Module.finrank_eq_card_basis (basisOfCardPow d hcard), Fintype.card_fin]

end TateModule
p2m_reactivate "P2MW.S_ModularCurve_residualRealization_of_occurs.ModularCurve.X4IntegralSide.LatticeMod P2MW.S_ModularCurve_residualRealization_of_occurs.ModularCurve.X4IntegralSide P2MW.S_ModularCurve_residualRealization_of_occurs.ModularCurve P2MW.S_ModularCurve_residualRealization_of_occurs.ModularCurve.X4DvrSource P2MW.S_ModularCurve_residualRealization_of_occurs.ModularCurve.X4Det"

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Pic0 Pic0.torsion AbelJacobiCard"
p2m_open "AlgebraicCurve"

variable {K F : Type} [Field K] [Field F] [Algebra K F]

theorem hcard_of_abelJacobiCard {p g : ℕ} (h : AbelJacobiCard K F p g) :
    ∀ n : ℕ, Nat.card (torsionBy ℤ (Pic0 K F) ((p ^ n : ℕ) : ℤ)) = (p ^ n) ^ (2 * g) := by
  intro n
  have hcarrier : Nat.card (Pic0.torsion K F (p ^ n))
      = Nat.card (torsionBy ℤ (Pic0 K F) ((p ^ n : ℕ) : ℤ)) := rfl
  rw [← hcarrier, h n, ← pow_mul, Nat.mul_comm]

end AlgebraicCurve
p2m_reactivate "P2MW.S_ModularCurve_residualRealization_of_occurs.ModularCurve.X4IntegralSide.LatticeMod P2MW.S_ModularCurve_residualRealization_of_occurs.ModularCurve.X4IntegralSide P2MW.S_ModularCurve_residualRealization_of_occurs.ModularCurve P2MW.S_ModularCurve_residualRealization_of_occurs.ModularCurve.X4DvrSource P2MW.S_ModularCurve_residualRealization_of_occurs.ModularCurve.X4Det"

namespace ModularCurve
p2m_export "ModularCurve" "tateHeckeRep coe_tateHeckeRep_apply_apply RationalTateModule rationalGaloisRep rationalGaloisRep_apply rationalHeckeRep rationalHeckeRep_apply rationalHeckeRep_tmul rationalHeckeAlgebra rationalHeckeRep_mem_rationalHeckeAlgebra RationalRankTwoCyclotomicOf RationalRankTwoCyclotomic modularFunctionFieldBar JZero HeckeAlg heckeTorsion IsResidualRealization CyclotomicDeterminant heckeModuleBar rationalRankTwoCyclotomic_family JZero.torsion_fixed_by_open JZero.exists_abelJacobiCard heckeOperatorsCommuteBar smulCommClass_JZero_of_heckeOperatorsCommuteBar"
p2m_open "ModularCurve~baseChangeHom~baseChangeHom_injective"

variable {p : ℕ} [Fact p.Prime] {J : Type} [AddCommGroup J] [Module HeckeAlg J]

theorem proj_tateHeckeRep (t : HeckeAlg) (x : TateModule p J) (n : ℕ) :
    TateModule.proj p J n (tateHeckeRep p J t x) = t • TateModule.proj p J n x :=
  rfl

omit [Module HeckeAlg J] in

theorem proj_rep_galois (G : Type) [Monoid G] [DistribMulAction G J] (g : G)
    (x : TateModule p J) (n : ℕ) :
    TateModule.proj p J n (TateModule.rep p J G g x) = g • TateModule.proj p J n x :=
  rfl

theorem tateModule_mod_p_equiv_torsion (d : ℕ)
    (hcard : ∀ n : ℕ, Nat.card (torsionBy ℤ J ((p ^ n : ℕ) : ℤ)) = (p ^ n) ^ d) :
    ∃ e : (TateModule p J ⧸ (Ideal.span {(p : ℤ_[p])} • (⊤ : Submodule ℤ_[p] (TateModule p J))))
        ≃+ (torsionBy ℤ J ((p : ℕ) : ℤ)),
      (∀ t : HeckeAlg, ∀ x, (e (Submodule.Quotient.mk (tateHeckeRep p J t x)) : J)
          = t • (e (Submodule.Quotient.mk x) : J)) ∧
      (∀ (G : Type) [Monoid G] [DistribMulAction G J], ∀ g : G, ∀ x,
          (e (Submodule.Quotient.mk (TateModule.rep p J G g x)) : J)
          = g • (e (Submodule.Quotient.mk x) : J)) := by
  have hker : ∀ x : TateModule p J, TateModule.proj p J 1 x = 0 ↔
      x ∈ (Ideal.span {(p : ℤ_[p])} • (⊤ : Submodule ℤ_[p] (TateModule p J))) := by
    intro x
    rw [← PadicInt.maximalIdeal_eq_span_p, ← pow_one (maximalIdeal ℤ_[p])]
    exact TateModule.proj_eq_zero_iff 1 x
  have hmem : ∀ x : TateModule p J,
      TateModule.proj p J 1 x ∈ torsionBy ℤ J ((p : ℕ) : ℤ) := fun x => by
    rw [show ((p : ℕ) : ℤ) = ((p ^ 1 : ℕ) : ℤ) by rw [pow_one]]
    exact TateModule.proj_mem_torsionBy 1 x
  let f : TateModule p J →+ torsionBy ℤ J ((p : ℕ) : ℤ) :=
    { toFun := fun x => ⟨TateModule.proj p J 1 x, hmem x⟩
      map_zero' := Subtype.ext (map_zero _)
      map_add' := fun x y => Subtype.ext (map_add _ _ _) }
  have hfN : ∀ x ∈ (Ideal.span {(p : ℤ_[p])} •
      (⊤ : Submodule ℤ_[p] (TateModule p J))).toAddSubgroup, f x = 0 := fun x hx =>
    Subtype.ext ((hker x).mpr hx)
  let g := QuotientAddGroup.lift _ f hfN
  have hinj : Function.Injective g := by
    rw [injective_iff_map_eq_zero]
    intro q
    induction q using QuotientAddGroup.induction_on with
    | H x =>
      intro hq
      rw [QuotientAddGroup.eq_zero_iff]
      exact (hker x).mp (congrArg Subtype.val hq)
  have hsurj : Function.Surjective g := fun m => by
    have hm1 : (m : J) ∈ torsionBy ℤ J ((p ^ 1 : ℕ) : ℤ) :=
      TateModule.mem_torsionBy_one_of_smul_eq_zero ((mem_torsionBy_iff _ _).mp m.2)
    obtain ⟨x, hx⟩ := TateModule.proj_surjective_of_card_pow d hcard 1 (m : J) hm1
    exact ⟨QuotientAddGroup.mk x, Subtype.ext hx⟩
  refine ⟨AddEquiv.ofBijective g ⟨hinj, hsurj⟩, fun t x => rfl, ?_⟩
  intro G _ _ σ x
  rfl

end ModularCurve
p2m_reactivate "P2MW.S_ModularCurve_residualRealization_of_occurs.ModularCurve.X4IntegralSide.LatticeMod P2MW.S_ModularCurve_residualRealization_of_occurs.ModularCurve.X4IntegralSide P2MW.S_ModularCurve_residualRealization_of_occurs.ModularCurve P2MW.S_ModularCurve_residualRealization_of_occurs.ModularCurve.X4DvrSource P2MW.S_ModularCurve_residualRealization_of_occurs.ModularCurve.X4Det"

namespace ModularCurve
p2m_export "ModularCurve" "tateHeckeRep coe_tateHeckeRep_apply_apply RationalTateModule rationalGaloisRep rationalGaloisRep_apply rationalHeckeRep rationalHeckeRep_apply rationalHeckeRep_tmul rationalHeckeAlgebra rationalHeckeRep_mem_rationalHeckeAlgebra RationalRankTwoCyclotomicOf RationalRankTwoCyclotomic modularFunctionFieldBar JZero HeckeAlg heckeTorsion IsResidualRealization CyclotomicDeterminant heckeModuleBar rationalRankTwoCyclotomic_family JZero.torsion_fixed_by_open JZero.exists_abelJacobiCard heckeOperatorsCommuteBar smulCommClass_JZero_of_heckeOperatorsCommuteBar"
p2m_open "ModularCurve~baseChangeHom~baseChangeHom_injective"

variable {p : ℕ} [Fact p.Prime] {J : Type} [AddCommGroup J] [Module HeckeAlg J]

omit [Module HeckeAlg J] in

theorem finiteDimensional_rationalTateModule (d : ℕ)
    (hcard : ∀ n : ℕ, Nat.card (torsionBy ℤ J ((p ^ n : ℕ) : ℤ)) = (p ^ n) ^ d) :
    FiniteDimensional ℚ_[p] (RationalTateModule p J) :=
  haveI := TateModule.finite_of_card_pow d hcard
  inferInstance

theorem finiteDimensional_rationalHeckeAlgebra (d : ℕ)
    (hcard : ∀ n : ℕ, Nat.card (torsionBy ℤ J ((p ^ n : ℕ) : ℤ)) = (p ^ n) ^ d) :
    FiniteDimensional ℚ_[p] (rationalHeckeAlgebra p J) :=
  haveI := finiteDimensional_rationalTateModule d hcard
  Module.Finite.of_injective (rationalHeckeAlgebra p J).val.toLinearMap Subtype.val_injective

theorem isMulCommutative_rationalHeckeAlgebra :
    IsMulCommutative (rationalHeckeAlgebra p J) :=
  Algebra.isMulCommutative_adjoin ℚ_[p] (by
    rintro _ ⟨s, rfl⟩ _ ⟨t, rfl⟩
    rw [← map_mul, ← map_mul, mul_comm])

open scoped IsMulCommutative in

theorem finite_maximalSpectrum_rationalHeckeAlgebra (d : ℕ)
    (hcard : ∀ n : ℕ, Nat.card (torsionBy ℤ J ((p ^ n : ℕ) : ℤ)) = (p ^ n) ^ d) :
    haveI := isMulCommutative_rationalHeckeAlgebra (p := p) (J := J)
    Finite {𝔭 : Ideal (rationalHeckeAlgebra p J) // 𝔭.IsMaximal} := by
  haveI := isMulCommutative_rationalHeckeAlgebra (p := p) (J := J)
  haveI := finiteDimensional_rationalHeckeAlgebra d hcard
  haveI : IsArtinianRing (rationalHeckeAlgebra p J) :=
    IsArtinianRing.of_finite ℚ_[p] (rationalHeckeAlgebra p J)
  exact (IsArtinianRing.setOf_isMaximal_finite (rationalHeckeAlgebra p J)).to_subtype

end ModularCurve
p2m_reactivate "P2MW.S_ModularCurve_residualRealization_of_occurs.ModularCurve.X4IntegralSide.LatticeMod P2MW.S_ModularCurve_residualRealization_of_occurs.ModularCurve.X4IntegralSide P2MW.S_ModularCurve_residualRealization_of_occurs.ModularCurve P2MW.S_ModularCurve_residualRealization_of_occurs.ModularCurve.X4DvrSource P2MW.S_ModularCurve_residualRealization_of_occurs.ModularCurve.X4Det"

namespace ModularCurve
p2m_export "ModularCurve" "tateHeckeRep coe_tateHeckeRep_apply_apply RationalTateModule rationalGaloisRep rationalGaloisRep_apply rationalHeckeRep rationalHeckeRep_apply rationalHeckeRep_tmul rationalHeckeAlgebra rationalHeckeRep_mem_rationalHeckeAlgebra RationalRankTwoCyclotomicOf RationalRankTwoCyclotomic modularFunctionFieldBar JZero HeckeAlg heckeTorsion IsResidualRealization CyclotomicDeterminant heckeModuleBar rationalRankTwoCyclotomic_family JZero.torsion_fixed_by_open JZero.exists_abelJacobiCard heckeOperatorsCommuteBar smulCommClass_JZero_of_heckeOperatorsCommuteBar"
p2m_open "ModularCurve~baseChangeHom~baseChangeHom_injective"

variable {p : ℕ} [Fact p.Prime] {J : Type} [AddCommGroup J] [Module HeckeAlg J]

def heckeToRationalHeckeAlgebra : HeckeAlg →+* rationalHeckeAlgebra p J where
  toFun t := ⟨rationalHeckeRep p J t, rationalHeckeRep_mem_rationalHeckeAlgebra p J t⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' _ _ := Subtype.ext (map_mul _ _ _)
  map_zero' := Subtype.ext (map_zero _)
  map_add' _ _ := Subtype.ext (map_add _ _ _)

theorem ker_heckeToRationalHeckeAlgebra_acts_zero_on_torsion (d : ℕ)
    (hcard : ∀ n : ℕ, Nat.card (torsionBy ℤ J ((p ^ n : ℕ) : ℤ)) = (p ^ n) ^ d)
    {t : HeckeAlg} (ht : t ∈ RingHom.ker (heckeToRationalHeckeAlgebra (p := p) (J := J)))
    {x : J} (hx : (p : ℤ) • x = 0) : t • x = 0 := by
  have h0 : rationalHeckeRep p J t = 0 := by
    rw [RingHom.mem_ker] at ht
    exact congrArg Subtype.val ht
  have hx1 : x ∈ torsionBy ℤ J ((p ^ 1 : ℕ) : ℤ) :=
    TateModule.mem_torsionBy_one_of_smul_eq_zero hx
  obtain ⟨y, hy⟩ := TateModule.proj_surjective_of_card_pow d hcard 1 x hx1
  have hz : (1 : ℚ_[p]) ⊗ₜ[ℤ_[p]] tateHeckeRep p J t y = (0 : RationalTateModule p J) := by
    have h1 := congrArg (fun F : Module.End ℚ_[p] (RationalTateModule p J) =>
      F ((1 : ℚ_[p]) ⊗ₜ[ℤ_[p]] y)) h0
    simpa only [rationalHeckeRep_tmul, LinearMap.zero_apply] using h1
  set b := TateModule.basisOfCardPow d hcard
  have hz0 : tateHeckeRep p J t y = 0 := by
    have hrepr : ∀ i, b.repr (tateHeckeRep p J t y) i = 0 := by
      intro i
      have h1 := congrArg (fun w : RationalTateModule p J =>
        ((Algebra.TensorProduct.basis ℚ_[p] b).repr w) i) hz
      simp only [map_zero, Finsupp.coe_zero, Pi.zero_apply,
        Algebra.TensorProduct.basis_repr_tmul, one_smul, Finsupp.mapRange_apply] at h1
      exact IsFractionRing.injective ℤ_[p] ℚ_[p] (by rw [h1, map_zero])
    exact (LinearEquiv.map_eq_zero_iff b.repr).mp (Finsupp.ext hrepr)
  have hstep : t • x = TateModule.proj p J 1 (tateHeckeRep p J t y) := by
    rw [← hy]
    exact (proj_tateHeckeRep t y 1).symm
  rw [hstep, hz0, map_zero]

end ModularCurve
p2m_reactivate "P2MW.S_ModularCurve_residualRealization_of_occurs.ModularCurve.X4IntegralSide.LatticeMod P2MW.S_ModularCurve_residualRealization_of_occurs.ModularCurve.X4IntegralSide P2MW.S_ModularCurve_residualRealization_of_occurs.ModularCurve P2MW.S_ModularCurve_residualRealization_of_occurs.ModularCurve.X4DvrSource P2MW.S_ModularCurve_residualRealization_of_occurs.ModularCurve.X4Det"

namespace ModularCurve
p2m_export "ModularCurve" "tateHeckeRep coe_tateHeckeRep_apply_apply RationalTateModule rationalGaloisRep rationalGaloisRep_apply rationalHeckeRep rationalHeckeRep_apply rationalHeckeRep_tmul rationalHeckeAlgebra rationalHeckeRep_mem_rationalHeckeAlgebra RationalRankTwoCyclotomicOf RationalRankTwoCyclotomic modularFunctionFieldBar JZero HeckeAlg heckeTorsion IsResidualRealization CyclotomicDeterminant heckeModuleBar rationalRankTwoCyclotomic_family JZero.torsion_fixed_by_open JZero.exists_abelJacobiCard heckeOperatorsCommuteBar smulCommClass_JZero_of_heckeOperatorsCommuteBar"
p2m_open "ModularCurve~baseChangeHom~baseChangeHom_injective"

open X4IntegralSide

variable (p : ℕ) [Fact p.Prime] (J : Type) [AddCommGroup J] [Module HeckeAlg J]
variable (F : Type) [Field F] [Algebra ℤ_[p] F]
  [Algebra (IntegralHeckeRing p J) F]
  [IsScalarTower ℤ_[p] (IntegralHeckeRing p J) F]
  (𝒪 : Subalgebra ℤ_[p] F)
variable (kk : Type) [Field kk] [Algebra ↥𝒪 kk]

theorem toResidual_eq_zero_of_mem_smul_top (hpk : (p : kk) = 0) {x : TateModule p J}
    (hx : x ∈ (Ideal.span {(p : ℤ_[p])} • (⊤ : Submodule ℤ_[p] (TateModule p J)))) :
    toResidual p J F 𝒪 kk x = 0 := by
  refine Submodule.smul_induction_on hx (fun r hr t _ => ?_) (fun a b ha hb => ?_)
  · obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hr
    rw [mul_smul, toResidual_padicInt_smul, toResidual_natCast_smul, hpk, zero_smul,
      smul_zero]
  · rw [map_add, ha, hb, add_zero]

noncomputable def residualBar (hpk : (p : kk) = 0) :
    (TateModule p J ⧸ (Ideal.span {(p : ℤ_[p])} • (⊤ : Submodule ℤ_[p] (TateModule p J))))
      →+ ResidualSpace p J F 𝒪 kk :=
  QuotientAddGroup.lift _ (toResidual p J F 𝒪 kk)
    (fun _ hx => toResidual_eq_zero_of_mem_smul_top p J F 𝒪 kk hpk hx)

@[scoped simp] theorem residualBar_mk (hpk : (p : kk) = 0) (x : TateModule p J) :
    residualBar p J F 𝒪 kk hpk (Submodule.Quotient.mk x) = toResidual p J F 𝒪 kk x :=
  rfl

variable (e : (TateModule p J ⧸ (Ideal.span {(p : ℤ_[p])} •
    (⊤ : Submodule ℤ_[p] (TateModule p J)))) ≃+ (torsionBy ℤ J ((p : ℕ) : ℤ)))

omit [Fact p.Prime] [Module HeckeAlg J] in

theorem mem_torsionBy_of_nsmul {x : J} (h : p • x = 0) : x ∈ torsionBy ℤ J ((p : ℕ) : ℤ) :=
  (mem_torsionBy_iff _ _).mpr ((Nat.cast_smul_eq_nsmul ℤ p x).trans h)

open scoped Classical in

noncomputable def piFun (hpk : (p : kk) = 0) : J → ResidualSpace p J F 𝒪 kk := fun x =>
  if h : p • x = 0 then
    residualBar p J F 𝒪 kk hpk (e.symm ⟨x, mem_torsionBy_of_nsmul p J h⟩)
  else 0

theorem piFun_zero (hpk : (p : kk) = 0) : piFun p J F 𝒪 kk e hpk 0 = 0 := by
  have h0 : (⟨(0 : J), mem_torsionBy_of_nsmul p J (smul_zero p)⟩ :
      torsionBy ℤ J ((p : ℕ) : ℤ)) = 0 := Subtype.ext rfl
  simp only [piFun]
  rw [dif_pos (smul_zero p), h0, map_zero, map_zero]

theorem piFun_add (hpk : (p : kk) = 0) {x y : J} (hx : p • x = 0) (hy : p • y = 0) :
    piFun p J F 𝒪 kk e hpk (x + y) =
      piFun p J F 𝒪 kk e hpk x + piFun p J F 𝒪 kk e hpk y := by
  have hxy : p • (x + y) = 0 := by rw [smul_add, hx, hy, add_zero]
  have hsub : (⟨x + y, mem_torsionBy_of_nsmul p J hxy⟩ : torsionBy ℤ J ((p : ℕ) : ℤ))
      = ⟨x, mem_torsionBy_of_nsmul p J hx⟩ + ⟨y, mem_torsionBy_of_nsmul p J hy⟩ :=
    Subtype.ext rfl
  simp only [piFun]
  rw [dif_pos hxy, dif_pos hx, dif_pos hy, hsub, map_add, map_add]

section Galois

variable (G : Type) [Group G] [DistribMulAction G J] [SMulCommClass G HeckeAlg J]

theorem piFun_galois (hpk : (p : kk) = 0)
    (heG : ∀ (g : G) (y : TateModule p J),
      ((e (Submodule.Quotient.mk (TateModule.rep p J G g y)) :
        torsionBy ℤ J ((p : ℕ) : ℤ)) : J)
        = g • ((e (Submodule.Quotient.mk y) : torsionBy ℤ J ((p : ℕ) : ℤ)) : J))
    (σ : G) {x : J} (hx : p • x = 0) :
    piFun p J F 𝒪 kk e hpk (σ • x) =
      residualRep p J F 𝒪 kk G (integralGaloisRep' p J G) σ (piFun p J F 𝒪 kk e hpk x) := by
  have hσx : p • (σ • x) = 0 := by rw [smul_comm, hx, smul_zero]
  obtain ⟨y, hy⟩ := Submodule.Quotient.mk_surjective _
    (e.symm ⟨x, mem_torsionBy_of_nsmul p J hx⟩)
  have hey : e (Submodule.Quotient.mk y) = ⟨x, mem_torsionBy_of_nsmul p J hx⟩ := by
    rw [hy, AddEquiv.apply_symm_apply]
  have hflip : e.symm ⟨σ • x, mem_torsionBy_of_nsmul p J hσx⟩
      = Submodule.Quotient.mk (TateModule.rep p J G σ y) := by
    apply e.injective
    rw [AddEquiv.apply_symm_apply]
    refine Subtype.ext (Eq.symm ((heG σ y).trans ?_))
    rw [hey]
  simp only [piFun]
  rw [dif_pos hσx, dif_pos hx, hflip, ← hy, residualBar_mk, residualBar_mk]
  show toResidual p J F 𝒪 kk ((integralGaloisRep' p J G σ) y) = _
  rw [toResidual_rep]

end Galois
p2m_reactivate "P2MW.S_ModularCurve_residualRealization_of_occurs.ModularCurve.X4IntegralSide.LatticeMod P2MW.S_ModularCurve_residualRealization_of_occurs.ModularCurve.X4IntegralSide P2MW.S_ModularCurve_residualRealization_of_occurs.ModularCurve P2MW.S_ModularCurve_residualRealization_of_occurs.ModularCurve.X4DvrSource P2MW.S_ModularCurve_residualRealization_of_occurs.ModularCurve.X4Det"

theorem piFun_hecke (hpk : (p : kk) = 0)
    (heH : ∀ (t : HeckeAlg) (y : TateModule p J),
      ((e (Submodule.Quotient.mk (tateHeckeRep p J t y)) :
        torsionBy ℤ J ((p : ℕ) : ℤ)) : J)
        = t • ((e (Submodule.Quotient.mk y) : torsionBy ℤ J ((p : ℕ) : ℤ)) : J))
    (h𝒪T : ∀ t : HeckeAlg, algebraMap (IntegralHeckeRing p J) F
      (IntegralHeckeRing.ofSubalgebra p J (heckeToIntegralHeckeAlgebra p J t)) ∈ 𝒪)
    (φ : HeckeAlg →+* kk)
    (hψφ : ∀ t : HeckeAlg, algebraMap ↥𝒪 kk
      ⟨algebraMap (IntegralHeckeRing p J) F
        (IntegralHeckeRing.ofSubalgebra p J (heckeToIntegralHeckeAlgebra p J t)), h𝒪T t⟩
      = φ t)
    (t : HeckeAlg) {x : J} (hx : p • x = 0) :
    piFun p J F 𝒪 kk e hpk (t • x) = φ t • piFun p J F 𝒪 kk e hpk x := by
  have htx : p • (t • x) = 0 := by rw [smul_comm, hx, smul_zero]
  obtain ⟨y, hy⟩ := Submodule.Quotient.mk_surjective _
    (e.symm ⟨x, mem_torsionBy_of_nsmul p J hx⟩)
  have hey : e (Submodule.Quotient.mk y) = ⟨x, mem_torsionBy_of_nsmul p J hx⟩ := by
    rw [hy, AddEquiv.apply_symm_apply]
  have hflip : e.symm ⟨t • x, mem_torsionBy_of_nsmul p J htx⟩
      = Submodule.Quotient.mk (tateHeckeRep p J t y) := by
    apply e.injective
    rw [AddEquiv.apply_symm_apply]
    refine Subtype.ext (Eq.symm ((heH t y).trans ?_))
    rw [hey]
  simp only [piFun]
  rw [dif_pos htx, dif_pos hx, hflip, ← hy, residualBar_mk, residualBar_mk]
  show toResidual p J F 𝒪 kk
    ((IntegralHeckeRing.ofSubalgebra p J (heckeToIntegralHeckeAlgebra p J t)) • y) = _
  rw [toResidual_smul p J F 𝒪 kk _ (h𝒪T t), hψφ t]

theorem piFun_spanning (hpk : (p : kk) = 0) :
    Submodule.span kk (piFun p J F 𝒪 kk e hpk '' {x : J | p • x = 0}) = ⊤ := by
  rw [← span_range_toResidual p J F 𝒪 kk]
  congr 1
  ext v
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hx' : p • x = 0 := hx
    obtain ⟨y, hy⟩ := Submodule.Quotient.mk_surjective _
      (e.symm ⟨x, mem_torsionBy_of_nsmul p J hx'⟩)
    refine ⟨y, ?_⟩
    simp only [piFun]
    rw [dif_pos hx', ← hy, residualBar_mk]
  · rintro ⟨y, rfl⟩
    have hmem : p • ((e (Submodule.Quotient.mk y) : torsionBy ℤ J ((p : ℕ) : ℤ)) : J) = 0 :=
      (Nat.cast_smul_eq_nsmul ℤ p _).symm.trans
        ((mem_torsionBy_iff _ _).mp (e (Submodule.Quotient.mk y)).2)
    refine ⟨((e (Submodule.Quotient.mk y) : torsionBy ℤ J ((p : ℕ) : ℤ)) : J), hmem, ?_⟩
    simp only [piFun]
    rw [dif_pos hmem]
    have hsub : (⟨((e (Submodule.Quotient.mk y) : torsionBy ℤ J ((p : ℕ) : ℤ)) : J),
        mem_torsionBy_of_nsmul p J hmem⟩ : torsionBy ℤ J ((p : ℕ) : ℤ))
        = e (Submodule.Quotient.mk y) := Subtype.ext rfl
    rw [hsub, AddEquiv.symm_apply_apply, residualBar_mk]

section Bundle

variable {K L : Type} [Field K] [Field L] [Algebra K L]
variable [DistribMulAction (L ≃ₐ[K] L) J] [SMulCommClass (L ≃ₐ[K] L) HeckeAlg J]

theorem isResidualRealization_piFun (hpk : (p : kk) = 0)
    (heH : ∀ (t : HeckeAlg) (y : TateModule p J),
      ((e (Submodule.Quotient.mk (tateHeckeRep p J t y)) :
        torsionBy ℤ J ((p : ℕ) : ℤ)) : J)
        = t • ((e (Submodule.Quotient.mk y) : torsionBy ℤ J ((p : ℕ) : ℤ)) : J))
    (heG : ∀ (g : L ≃ₐ[K] L) (y : TateModule p J),
      ((e (Submodule.Quotient.mk (TateModule.rep p J (L ≃ₐ[K] L) g y)) :
        torsionBy ℤ J ((p : ℕ) : ℤ)) : J)
        = g • ((e (Submodule.Quotient.mk y) : torsionBy ℤ J ((p : ℕ) : ℤ)) : J))
    (h𝒪T : ∀ t : HeckeAlg, algebraMap (IntegralHeckeRing p J) F
      (IntegralHeckeRing.ofSubalgebra p J (heckeToIntegralHeckeAlgebra p J t)) ∈ 𝒪)
    (φ : HeckeAlg →+* kk)
    (hψφ : ∀ t : HeckeAlg, algebraMap ↥𝒪 kk
      ⟨algebraMap (IntegralHeckeRing p J) F
        (IntegralHeckeRing.ofSubalgebra p J (heckeToIntegralHeckeAlgebra p J t)), h𝒪T t⟩
      = φ t)
    (hfin : Module.Finite kk (ResidualSpace p J F 𝒪 kk))
    (hfr : Module.finrank kk (ResidualSpace p J F 𝒪 kk) = 2) :
    IsResidualRealization p J kk φ (ResidualSpace p J F 𝒪 kk)
      (piFun p J F 𝒪 kk e hpk)
      (residualRep p J F 𝒪 kk (L ≃ₐ[K] L) (integralGaloisRep' p J (L ≃ₐ[K] L))) where
  finite := hfin
  finrank_eq := hfr
  map_zero := piFun_zero p J F 𝒪 kk e hpk
  map_add := fun _ _ hx hy => piFun_add p J F 𝒪 kk e hpk hx hy
  map_galois := fun σ _ hx => piFun_galois p J F 𝒪 kk e (L ≃ₐ[K] L) hpk heG σ hx
  map_hecke := fun t _ hx => piFun_hecke p J F 𝒪 kk e hpk heH h𝒪T φ hψφ t hx
  spanning := piFun_spanning p J F 𝒪 kk e hpk

end Bundle
p2m_reactivate "P2MW.S_ModularCurve_residualRealization_of_occurs.ModularCurve.X4IntegralSide.LatticeMod P2MW.S_ModularCurve_residualRealization_of_occurs.ModularCurve.X4IntegralSide P2MW.S_ModularCurve_residualRealization_of_occurs.ModularCurve P2MW.S_ModularCurve_residualRealization_of_occurs.ModularCurve.X4DvrSource P2MW.S_ModularCurve_residualRealization_of_occurs.ModularCurve.X4Det"

end ModularCurve
p2m_reactivate "P2MW.S_ModularCurve_residualRealization_of_occurs.ModularCurve.X4IntegralSide.LatticeMod P2MW.S_ModularCurve_residualRealization_of_occurs.ModularCurve.X4IntegralSide P2MW.S_ModularCurve_residualRealization_of_occurs.ModularCurve P2MW.S_ModularCurve_residualRealization_of_occurs.ModularCurve.X4DvrSource P2MW.S_ModularCurve_residualRealization_of_occurs.ModularCurve.X4Det"

namespace ModularCurve p2m_export "ModularCurve" "tateHeckeRep coe_tateHeckeRep_apply_apply RationalTateModule rationalGaloisRep rationalGaloisRep_apply rationalHeckeRep rationalHeckeRep_apply rationalHeckeRep_tmul rationalHeckeAlgebra rationalHeckeRep_mem_rationalHeckeAlgebra RationalRankTwoCyclotomicOf RationalRankTwoCyclotomic modularFunctionFieldBar JZero HeckeAlg heckeTorsion IsResidualRealization CyclotomicDeterminant heckeModuleBar rationalRankTwoCyclotomic_family JZero.torsion_fixed_by_open JZero.exists_abelJacobiCard heckeOperatorsCommuteBar smulCommClass_JZero_of_heckeOperatorsCommuteBar" end ModularCurve
p2m_open_scoped "ModularCurve" in

theorem ModularCurve.residualRealization_of_rationalRankTwo_of_abelJacobiCard
    (M p : ℕ) [NeZero M] [Fact p.Prime] :
    letI := ModularCurve.heckeModuleBar M;
    ModularCurve.RationalRankTwoCyclotomic M p →
    (∃ g : ℕ, AbelJacobiCard (AlgebraicClosure ℚ) (ModularCurve.modularFunctionFieldBar M) p g) →
    ∀ (k : Type) [Field k] [IsAlgClosed k] (φ : ModularCurve.HeckeAlg →+* k),
      (p : k) = 0 → (RingHom.ker φ).IsMaximal →
      ModularCurve.heckeTorsion (ModularCurve.JZero M) (RingHom.ker φ) ≠ ⊥ →
      ∃ (V : Type) (_ : AddCommGroup V) (_ : Module k V)
        (π : ModularCurve.JZero M → V)
        (ρ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* (V ≃ₗ[k] V))
        (F : Type) (_ : Field F) (_ : NumberField F) (_ : IsGalois ℚ F)
        (_ : Algebra F (AlgebraicClosure ℚ)) (_ : IsScalarTower ℚ F (AlgebraicClosure ℚ)),
        ModularCurve.IsResidualRealization p (ModularCurve.JZero M) k φ V π ρ ∧
        ModularCurve.CyclotomicDeterminant M p ρ ∧
        (AlgEquiv.restrictNormalHom (F := ℚ) (K₁ := AlgebraicClosure ℚ) F).ker ≤ ρ.ker := by
  intro hR2 hAJ k _ _ φ hpk hmax hT
  classical
  letI := ModularCurve.heckeModuleBar M

  haveI hchar : CharP k p := (CharP.charP_iff_prime_eq_zero (Fact.out : p.Prime)).mpr hpk
  letI : Algebra ℤ_[p] k := ((ZMod.castHom (dvd_refl p) k).comp PadicInt.toZMod).toAlgebra

  obtain ⟨g, hAJc⟩ := hAJ
  have hcard := AlgebraicCurve.hcard_of_abelJacobiCard hAJc
  haveI : Module.Finite ℤ_[p] (TateModule p (ModularCurve.JZero M)) :=
    TateModule.finite_of_card_pow (2 * g) hcard
  haveI : Module.Free ℤ_[p] (TateModule p (ModularCurve.JZero M)) :=
    TateModule.free_of_card_pow (2 * g) hcard
  have hsurj := TateModule.proj_surjective_of_card_pow (2 * g) hcard 1

  obtain ⟨e, heH, heG⟩ := ModularCurve.tateModule_mod_p_equiv_torsion (2 * g) hcard

  haveI : SMulCommClass (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
      ModularCurve.HeckeAlg (ModularCurve.JZero M) :=
    ModularCurve.smulCommClass_JZero_of_heckeOperatorsCommuteBar M
      (ModularCurve.heckeOperatorsCommuteBar M)

  obtain ⟨φ₀, hφ₀⟩ := ModularCurve.X4IntegralSide.exists_algHom_integralHeckeRing p
    (ModularCurve.JZero M) hsurj k φ hpk hmax hT

  obtain ⟨𝔓, h𝔓prime, h𝔓le, hP𝔓⟩ :=
    ModularCurve.X4IntegralSide.exists_prime_le_ker_not_mem p (ModularCurve.JZero M) k φ₀
  haveI := h𝔓prime
  haveI : Fact (algebraMap ℤ_[p]
      (ModularCurve.X4IntegralSide.IntegralHeckeRing p (ModularCurve.JZero M)) p ∉ 𝔓) := ⟨hP𝔓⟩

  obtain ⟨𝒪, hPID, hFrac, ψ, h𝒪, hψφ₀, hψp⟩ :=
    ModularCurve.X4Psi0Source.exists_sourced_subalgebra p (ModularCurve.JZero M) 𝔓 k φ₀ hpk h𝔓le
  haveI := hPID
  haveI := hFrac
  letI : Algebra ↥𝒪 k := ψ.toAlgebra

  have hpF : algebraMap (ModularCurve.X4IntegralSide.IntegralHeckeRing p (ModularCurve.JZero M))
      𝔓.ResidueField (algebraMap ℤ_[p]
        (ModularCurve.X4IntegralSide.IntegralHeckeRing p (ModularCurve.JZero M)) p) ≠ 0 := by
    rw [Ne, Ideal.algebraMap_residueField_eq_zero]
    exact hP𝔓
  haveI hfin : Module.Finite k (ModularCurve.X4IntegralSide.ResidualSpace p
      (ModularCurve.JZero M) 𝔓.ResidueField 𝒪 k) := inferInstance
  have hfr := ModularCurve.X4IntegralSide.finrank_residualSpace_eq_two p (ModularCurve.JZero M)
    𝔓.ResidueField 𝒪 k M hR2 hpF

  have h𝒪T : ∀ t : ModularCurve.HeckeAlg,
      algebraMap (ModularCurve.X4IntegralSide.IntegralHeckeRing p (ModularCurve.JZero M))
        𝔓.ResidueField (ModularCurve.X4IntegralSide.IntegralHeckeRing.ofSubalgebra p
          (ModularCurve.JZero M) (ModularCurve.X4IntegralSide.heckeToIntegralHeckeAlgebra p
            (ModularCurve.JZero M) t)) ∈ 𝒪 := fun t => h𝒪 _
  have hψφ : ∀ t : ModularCurve.HeckeAlg, algebraMap ↥𝒪 k
      ⟨algebraMap (ModularCurve.X4IntegralSide.IntegralHeckeRing p (ModularCurve.JZero M))
        𝔓.ResidueField (ModularCurve.X4IntegralSide.IntegralHeckeRing.ofSubalgebra p
          (ModularCurve.JZero M) (ModularCurve.X4IntegralSide.heckeToIntegralHeckeAlgebra p
            (ModularCurve.JZero M) t)), h𝒪T t⟩ = φ t := fun t => by
    show ψ _ = φ t
    rw [hψφ₀ _]
    exact hφ₀ t

  have hbundle := ModularCurve.isResidualRealization_piFun p (ModularCurve.JZero M)
    𝔓.ResidueField 𝒪 k e hpk heH
    (heG (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) h𝒪T φ hψφ hfin hfr

  haveI hsfin : Finite {x : ModularCurve.JZero M // p • x = 0} := by
    haveI := TateModule.finite_torsionBy_of_card_pow (2 * g) hcard 1
    have heq : {x : ModularCurve.JZero M //
          x ∈ Submodule.torsionBy ℤ (ModularCurve.JZero M) ((p ^ 1 : ℕ) : ℤ)}
        ≃ {x : ModularCurve.JZero M // p • x = 0} :=
      Equiv.subtypeEquivRight (fun x => by
        rw [Submodule.mem_torsionBy_iff, pow_one, Nat.cast_smul_eq_nsmul])
    exact Finite.of_equiv _ heq
  have hX6 := fun (x : {x : ModularCurve.JZero M // p • x = 0}) =>
    ModularCurve.JZero.torsion_fixed_by_open M p x.1 ⟨1, by rw [pow_one]; exact x.2⟩
  choose Fam iFf iNF iGal iAlg iTower hfix using hX6
  obtain ⟨F, iF', iNF', iGal', iAlg', iTower', hker⟩ :=
    @ModularCurve.X4Fclause.exists_uniform_number_field _ hsfin Fam iFf iNF iGal iAlg iTower

  refine ⟨ModularCurve.X4IntegralSide.ResidualSpace p (ModularCurve.JZero M) 𝔓.ResidueField 𝒪 k,
    inferInstance, inferInstance,
    ModularCurve.piFun p (ModularCurve.JZero M) 𝔓.ResidueField 𝒪 k e hpk,
    ModularCurve.X4IntegralSide.residualRep p (ModularCurve.JZero M) 𝔓.ResidueField 𝒪 k
      (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
      (ModularCurve.X4IntegralSide.integralGaloisRep' p (ModularCurve.JZero M)
        (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)),
    F, iF', iNF', iGal', iAlg', iTower', hbundle, ?_, ?_⟩
  ·

    intro ℓ hℓ hNp A' hA' σ hσfrob
    exact ModularCurve.X4IntegralSide.det_residualRep_eq_natCast p (ModularCurve.JZero M)
      𝔓.ResidueField 𝒪 k (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) M hR2 hpF
      (ModularCurve.X4IntegralSide.integralGaloisRep' p (ModularCurve.JZero M)
        (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) σ
      (ModularCurve.X4Det.rationalGaloisRepLinear p (ModularCurve.JZero M)
        (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) σ)
      (fun _ => rfl) ℓ
      (ModularCurve.X4DetTop.det_rationalGaloisRepLinear_eq_of_rationalRankTwo
        (p := p) (J := ModularCurve.JZero M) M hR2 ℓ hℓ hNp A' hA' σ hσfrob)
  ·
    intro σ hσ
    rw [MonoidHom.mem_ker]
    refine ModularCurve.X4Fclause.linearEquiv_eq_one_of_forall_fixed
      {x : ModularCurve.JZero M | p • x = 0}
      (ModularCurve.piFun p (ModularCurve.JZero M) 𝔓.ResidueField 𝒪 k e hpk) _
      (fun g' x hx => hbundle.map_galois g' x hx) hbundle.spanning σ
      (fun x hx => hfix ⟨x, hx⟩ σ (hker ⟨x, hx⟩ hσ))

end
p2m_reactivate "P2MW.S_ModularCurve_residualRealization_of_occurs.ModularCurve.X4IntegralSide.LatticeMod P2MW.S_ModularCurve_residualRealization_of_occurs.ModularCurve.X4IntegralSide P2MW.S_ModularCurve_residualRealization_of_occurs.ModularCurve P2MW.S_ModularCurve_residualRealization_of_occurs.ModularCurve.X4DvrSource P2MW.S_ModularCurve_residualRealization_of_occurs.ModularCurve.X4Det"

theorem solution (M p : ℕ) [NeZero M] [Fact p.Prime] :
    letI := ModularCurve.heckeModuleBar M;
    ∀ (k : Type) [Field k] [IsAlgClosed k] (φ : ModularCurve.HeckeAlg →+* k),
      (p : k) = 0 → (RingHom.ker φ).IsMaximal →
      ModularCurve.heckeTorsion (ModularCurve.JZero M) (RingHom.ker φ) ≠ ⊥ →
      ∃ (V : Type) (_ : AddCommGroup V) (_ : Module k V)
        (π : ModularCurve.JZero M → V)
        (ρ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* (V ≃ₗ[k] V))
        (F : Type) (_ : Field F) (_ : NumberField F) (_ : IsGalois ℚ F)
        (_ : Algebra F (AlgebraicClosure ℚ)) (_ : IsScalarTower ℚ F (AlgebraicClosure ℚ)),
        ModularCurve.IsResidualRealization p (ModularCurve.JZero M) k φ V π ρ ∧
        ModularCurve.CyclotomicDeterminant M p ρ ∧
        (AlgEquiv.restrictNormalHom (F := ℚ) (K₁ := AlgebraicClosure ℚ) F).ker ≤ ρ.ker := by
  have hM : 0 < M := Nat.pos_of_ne_zero (NeZero.ne M)
  have hp : p.Prime := Fact.out
  obtain ⟨g, hg⟩ := ModularCurve.JZero.exists_abelJacobiCard M
  exact ModularCurve.residualRealization_of_rationalRankTwo_of_abelJacobiCard M p
    (ModularCurve.rationalRankTwoCyclotomic_family M p hM hp) ⟨g, hg p⟩

end S_ModularCurve_residualRealization_of_occurs
end P2MW
export P2MW.S_ModularCurve_residualRealization_of_occurs (solution)
