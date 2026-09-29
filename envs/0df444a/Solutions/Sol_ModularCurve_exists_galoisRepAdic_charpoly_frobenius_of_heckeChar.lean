-- Prove2me | solution 1 for ModularCurve.exists_galoisRepAdic_charpoly_frobenius_of_heckeChar
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/b1d3703b-92ea-55e5-bf4b-e47af6638364

import Mathlib
import Definitions.Def_GaloisRep_Adic
import Definitions.Def_ModularCurve_JZeroTateModule
import Definitions.Def_ModularCurve_HeckeModule
import Definitions.Def_ModularCurve_HeckeInputsAll
import Theorems.Thm_ModularCurve_rationalRankTwoCyclotomic_family
import Theorems.Thm_ModularCurve_rep_tateModule_jZero_comm
import Theorems.Thm_ModularCurve_frobeniusQuadratic_tateModule_jZero
import Theorems.Thm_ModularCurve_rep_tateModule_jZero_eq_self_of_mem_inertiaSubgroupIn
import Theorems.Thm_ModularCurve_moduleFinite_padicInt_tateModule_jZero
import Theorems.Thm_ModularCurve_JZero_exists_finiteDimensional_smul_eq_self_of_torsion
import Theorems.Thm_ModularCurve_heckeOperatorsCommuteBar
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_galoisRepAdic_charpoly_frobenius_of_heckeChar
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois CuspForm.heckeAlgebra.instCommRing CuspForm.heckeAlgebra.instIsMulCommutative CuspForm.heckeAlgebra.instIsAddTorsionFree ModularCurve.CuspSpace.instNonempty ModularCurve.CuspSpace.instSubsingletonOfOne ModularCurve.CuspSpace.instFinite ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.instAlgebraIntermediateFieldLaurent ModularCurve.instIsScalarTowerKaehlerIntermediateFieldLaurent ModularCurve.instIsScalarTowerIntermediateFieldLaurent ModularCurve.instModuleKaehlerIntermediateFieldLaurent ModularCurve.Gamma0Pair.isElliptic ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.B3.instIsElliptic_goodModel"
p2m_attr_erase "instance" "AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.instIsScalarTowerJAdjoin HeckeEis.instFiniteIndexHeckeUpper ModularCurve.Period.parabolicHoms_int_moduleFinite ModularCurve.Period.instGroupFG_SL2Z ModularCurve.Period.instIsNoetherian_addHom_int ModularCurve.Period.instGroupFG_Gamma0 FLT.Gamma0FundamentalSet.instContinuousConstSMulSpecialLinearGroupFinOfNatNatIntUpperHalfPlane_definitions FLT.HyperbolicMeasure.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatIntUpperHalfPlaneVolume_definitions FLT.HyperbolicMeasure.instIsOpenPosMeasureUpperHalfPlaneVolume_definitions FLT.L2ProductionInstance.isFiniteMeasure_gamma0 FLT.L2ProductionInstance.countable_SL2Z FLT.L2ProductionInstance.countable_quotient FLT.L2ProductionInstance.nontrivial_gamma0L2 HeckeEis.instModuleCoeffH1par"
p2m_attr_erase "instance" "HeckeEis.instAddCommGroupCoeffH1par AlgebraicCurve.CellDissection.fintypeV AlgebraicCurve.CellDissection.fintypeC AlgebraicCurve.CellDissection.fintypeE AlgebraicCurve.CellDissection.decEqV AlgebraicCurve.CellDissection.decEqC AlgebraicCurve.CellDissection.decEqE ValuationSubring.instIsAlgClosedResidueField WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular"
p2m_attr_erase "simp" "ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff"
p2m_attr_erase "simp" "ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_cuspidalDivisor₀ ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five"
p2m_attr_erase "simp" "ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.dualHeckeRep_apply_apply ModularCurve.coe_segmentPath ModularCurve.cuspHeckeAeval_heckeGen ModularCurve.coe_periodLatticeRestrict_apply CuspForm.heckeAlgebra.coe_U CuspForm.heckeAlgebra.coe_T ModularForm.coe_heckeTLin_apply CuspForm.coe_heckeULin_apply CuspForm.coe_heckeTLin_apply ModularForm.coe_heckeULin_apply ModularCurve.Period.IsEquivariantPrimitive.periodHom_apply ModularCurve.Period.IsEquivariantPrimitive.period_one ModularCurve.cuspCount_one ModularCurve.CuspSpace.cuspDenomAux_infty ModularCurve.CuspSpace.cuspDenomAux_coe ModularCurve.CuspSpace.cuspDenom_mk_zero ModularCurve.CuspSpace.cuspDenom_mk_infty ModularCurve.mapGL_apply_coe ModularCurve.ratPoint_one_zero ModularCurve.ratPoint_zero_right ModularCurve.CuspSpace.fromCoset_mk ModularCurve.CuspSpace.cuspDenom_mk ModularCurve.ratPoint_zero_one ModularCurve.ProjectiveLine.map_mk ModularCurve.qEulerFun_coeff ModularCurve.diffQExp_D ModularCurve.qEulerOn_apply ModularCurve.qEuler_coeff AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord ModularCurve.gamma0PairMap_gen ModularCurve.moduliPointMapRingHom_mk ModularCurve.Gamma0Pair.mk.injEq ModularCurve.ModuliPoint.j_mk ModularCurve.Gamma0Pair.mk.sizeOf_spec ModularCurve.gamma0PairMap_toCurve"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero WeierstrassCurve.ratPointHom_apply WeierstrassCurve.ratPointMap_zero ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ WeierstrassCurve.veluX_empty WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg"
p2m_attr_erase "simp" "WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero"
p2m_attr_erase "simp" "ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply HahnSeries.ramScale_apply AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none WeierstrassCurve.veluPointMap2_zero AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule"
p2m_attr_erase "simp" "AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule ModularCurve.Period.jConjMat_apply_zero_one ModularCurve.Period.jConjSL_coe ModularCurve.Period.jConjMat_apply_one_zero ModularCurve.Period.jConjMat_apply_one_one ModularCurve.Period.jConjGamma0_coe ModularCurve.Period.charInvolution_apply ModularCurve.Period.jConjMat_apply_zero_zero HeckeEis.heckeConjMat_apply_one_one HeckeEis.coe_heckeConjSL HeckeEis.mem_heckeUpperSL HeckeEis.resHom_apply HeckeEis.heckeConjMat_apply_zero_one HeckeEis.coe_transferAux HeckeEis.coe_heckeConj HeckeEis.alphaMat_apply_one_one HeckeEis.heckeConjMat_apply_one_zero HeckeEis.alphaMat_apply_zero_one HeckeEis.pullbackHom_apply HeckeEis.alphaMat_apply_one_zero HeckeEis.alphaMat_apply_zero_zero HeckeEis.heckeConjMat_apply_zero_zero PowerSeries.coeff_heckeV PowerSeries.coeff_heckeU AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq ModularCurve.ComplexPlaceDictionary.mk.injEq ModularCurve.ComplexPlaceDictionary.mk.sizeOf_spec FLT.TruncatedDomainPartition.unipotentDiagonalSum_zero"
p2m_attr_erase "simp" "HeckeEis.coeffCoboundaryMap_apply AlgebraicCurve.DivisorialWeilPairingData.toChar_apply AlgebraicCurve.WeilDatum.coe_classRight AlgebraicCurve.WeilDatum.coe_degZeroRight AlgebraicCurve.DivisorialWeilPairingData.mk.sizeOf_spec AlgebraicCurve.WeilDatum.coe_classLeft AlgebraicCurve.WeilDatum.coe_degZeroLeft AlgebraicCurve.DivisorialWeilPairingData.mk.injEq AlgebraicCurve.DivisorialWeilPairingData.toHom_apply_apply AlgebraicCurve.WeilDatum.mk.sizeOf_spec AlgebraicCurve.WeilDatum.mk.injEq AlgebraicCurve.WeilPairingData.evalAddChar_zero AlgebraicCurve.PrincipalPolarization.mk.injEq AlgebraicCurve.WeilPairingData.evalAddChar_apply AlgebraicCurve.H1Gm.degree_ofPic0 AlgebraicCurve.WeilPairingData.mk.sizeOf_spec AlgebraicCurve.HomPic0Gm.map_one AlgebraicCurve.PrincipalPolarization.mk.sizeOf_spec AlgebraicCurve.WeilPairingData.autodualityEquiv_apply AlgebraicCurve.WeilPairingData.eval_zero_right AlgebraicCurve.H1Gm.ofPic0_mk AlgebraicCurve.WeilPairingData.eval_neg_left AlgebraicCurve.HomPic0Gm.map_apply AlgebraicCurve.H1Gm.degree_mk AlgebraicCurve.HomPic0Gm.map_id AlgebraicCurve.WeilPairingData.mk.injEq AlgebraicCurve.WeilPairingData.congr_eval AlgebraicCurve.WeilPairingData.eval_neg_right AlgebraicCurve.WeilPairingData.eval_zero_left AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap ModularCurve.tateMap_apply AlgebraicCurve.abelJacobiDiv_single AlgebraicCurve.AnalyticCoord.mk.injEq"
p2m_attr_erase "simp" "AlgebraicCurve.Cell.mk.sizeOf_spec AlgebraicCurve.RadialRegion.mk.sizeOf_spec AlgebraicCurve.RadialRegion.mk.injEq AlgebraicCurve.CellDissection.mk.sizeOf_spec AlgebraicCurve.Cell.mk.injEq AlgebraicCurve.CellDissection.mk.injEq AlgebraicCurve.AnalyticCoord.mk.sizeOf_spec ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong ModularCurve.qExpandAlgHomC_apply ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL ValuationSubring.reduceAt_coe ValuationSubring.reduceAt_one ValuationSubring.reduceAt_natCast ValuationSubring.reduceAt_intCast ValuationSubring.reduceAt_zero ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec"
p2m_attr_erase "simp" "WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff"

open scoped TensorProduct
noncomputable section
namespace W6BES
open ModularCurve

set_option synthInstance.maxHeartbeats 1600000
set_option linter.unusedSectionVars false

local notation "Gal" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)

variable (p : ℕ) [Fact p.Prime] (J : Type) [AddCommGroup J] [Module HeckeAlg J]

scoped instance isMulCommutative_rationalHeckeAlgebra :
    IsMulCommutative (rationalHeckeAlgebra p J) :=
  Algebra.isMulCommutative_adjoin ℚ_[p] (by
    rintro _ ⟨s, rfl⟩ _ ⟨t, rfl⟩
    rw [← map_mul, ← map_mul, mul_comm])

open scoped IsMulCommutative in
scoped instance instCommRingA : CommRing (rationalHeckeAlgebra p J) := inferInstance

scoped instance instSMulCommClassA : SMulCommClass (rationalHeckeAlgebra p J) (rationalHeckeAlgebra p J)
    (RationalTateModule p J) := inferInstance

scoped instance instAlgebraEndA : Algebra (rationalHeckeAlgebra p J)
    (Module.End (rationalHeckeAlgebra p J) (RationalTateModule p J)) := inferInstance

scoped instance instModuleEndA : Module (rationalHeckeAlgebra p J)
    (Module.End (rationalHeckeAlgebra p J) (RationalTateModule p J)) :=
  (instAlgebraEndA p J).toModule

scoped instance instSMulEndA : SMul (rationalHeckeAlgebra p J)
    (Module.End (rationalHeckeAlgebra p J) (RationalTateModule p J)) :=
  (instAlgebraEndA p J).toSMul

theorem subalgebra_smul_def (a : rationalHeckeAlgebra p J) (v : RationalTateModule p J) :
    a • v = (a : Module.End ℚ_[p] (RationalTateModule p J)) v := rfl

theorem algebraMap_smul_eq (c : ℚ_[p]) (v : RationalTateModule p J) :
    (algebraMap ℚ_[p] (rationalHeckeAlgebra p J) c) • v = c • v := by
  rw [subalgebra_smul_def, Subalgebra.coe_algebraMap, Module.algebraMap_end_apply]

def CommHyp [DistribMulAction Gal J] : Prop :=
  ∀ (σ : Gal) (t : HeckeAlg) (x : TateModule p J),
      TateModule.rep p J Gal σ (TateModule.rep p J HeckeAlg t x)
        = TateModule.rep p J HeckeAlg t (TateModule.rep p J Gal σ x)

section GaloisLinear

variable [DistribMulAction Gal J]

theorem commute_of_comm (hcomm : CommHyp p J) (σ : Gal) (a : rationalHeckeAlgebra p J) :
    (a : Module.End ℚ_[p] (RationalTateModule p J)) * rationalGaloisRep p J Gal σ
      = rationalGaloisRep p J Gal σ * a := by
  have hle : rationalHeckeAlgebra p J ≤
      Subalgebra.centralizer ℚ_[p] {rationalGaloisRep p J Gal σ} := by
    refine Algebra.adjoin_le ?_
    rintro _ ⟨t, rfl⟩
    rw [SetLike.mem_coe, Subalgebra.mem_centralizer_iff]
    rintro g rfl
    rw [rationalGaloisRep_apply, rationalHeckeRep_apply, ← LinearMap.baseChange_mul,
      ← LinearMap.baseChange_mul]
    exact congrArg _ (LinearMap.ext fun x => hcomm σ t x)
  have := (Subalgebra.mem_centralizer_iff ℚ_[p]).mp (hle a.2) _ rfl
  exact this.symm

def galA (hcomm : CommHyp p J) (σ : Gal) :
    RationalTateModule p J →ₗ[rationalHeckeAlgebra p J] RationalTateModule p J where
  toFun := rationalGaloisRep p J Gal σ
  map_add' := map_add _
  map_smul' a v := (LinearMap.congr_fun (commute_of_comm p J hcomm σ a) v).symm

@[scoped simp] theorem galA_apply (hcomm : CommHyp p J) (σ : Gal) (v : RationalTateModule p J) :
    galA p J hcomm σ v = rationalGaloisRep p J Gal σ v := rfl

def galAHom (hcomm : CommHyp p J) :
    Gal →* Module.End (rationalHeckeAlgebra p J) (RationalTateModule p J) where
  toFun := galA p J hcomm
  map_one' := LinearMap.ext fun v => by simp
  map_mul' σ τ := LinearMap.ext fun v => by simp

@[scoped simp] theorem galAHom_apply (hcomm : CommHyp p J) (σ : Gal) (v : RationalTateModule p J) :
    galAHom p J hcomm σ v = rationalGaloisRep p J Gal σ v := rfl

end GaloisLinear

section Transfer

variable (b : Module.Basis (Fin 2) (rationalHeckeAlgebra p J) (RationalTateModule p J))
variable {K : Type} [Field K] (Λ : rationalHeckeAlgebra p J →+* K)

def transfer :
    Module.End (rationalHeckeAlgebra p J) (RationalTateModule p J) →+* Module.End K (Fin 2 → K) :=
  ((Matrix.toLinAlgEquiv' (R := K) (n := Fin 2)).toRingEquiv.toRingHom.comp
    (RingHom.mapMatrix Λ)).comp (LinearMap.toMatrixAlgEquiv b).toRingEquiv.toRingHom

theorem transfer_apply (f : Module.End (rationalHeckeAlgebra p J) (RationalTateModule p J)) :
    transfer p J b Λ f = Matrix.toLin' ((LinearMap.toMatrix b b f).map Λ) := rfl

theorem transfer_smul (a : rationalHeckeAlgebra p J)
    (f : Module.End (rationalHeckeAlgebra p J) (RationalTateModule p J)) :
    transfer p J b Λ (a • f) = Λ a • transfer p J b Λ f := by
  rw [transfer_apply, transfer_apply, LinearEquiv.map_smul, ← LinearEquiv.map_smul]
  ext i j
  simp [Matrix.map_apply, smul_eq_mul]

def coordK : RationalTateModule p J →+ (Fin 2 → K) where
  toFun v i := Λ (b.repr v i)
  map_zero' := by ext i; simp
  map_add' v w := by ext i; simp

theorem coordK_apply (v : RationalTateModule p J) (i : Fin 2) :
    coordK p J b Λ v i = Λ (b.repr v i) := rfl

theorem coordK_smul (a : rationalHeckeAlgebra p J) (v : RationalTateModule p J) :
    coordK p J b Λ (a • v) = Λ a • coordK p J b Λ v := by
  ext i
  simp [coordK_apply, smul_eq_mul]

theorem coordK_basis (i : Fin 2) : coordK p J b Λ (b i) = Pi.single i 1 := by
  ext j
  rw [coordK_apply, Module.Basis.repr_self, Finsupp.single_apply, Pi.single_apply]
  by_cases h : j = i
  · subst h; simp
  · simp [h, Ne.symm h]

theorem coordK_endo (f : Module.End (rationalHeckeAlgebra p J) (RationalTateModule p J))
    (v : RationalTateModule p J) :
    coordK p J b Λ (f v) = transfer p J b Λ f (coordK p J b Λ v) := by
  ext i
  rw [transfer_apply, Matrix.toLin'_apply, coordK_apply, ← LinearMap.toMatrix_mulVec_repr b b f v]
  simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, coordK_apply, map_sum, map_mul]

theorem det_transfer (f : Module.End (rationalHeckeAlgebra p J) (RationalTateModule p J)) :
    LinearMap.det (transfer p J b Λ f) = Λ (LinearMap.det f) := by
  rw [transfer_apply, LinearMap.det_toLin', ← LinearMap.det_toMatrix b, RingHom.map_det]
  rfl

end Transfer

section Frobenius

variable [DistribMulAction Gal J]
variable (b : Module.Basis (Fin 2) (rationalHeckeAlgebra p J) (RationalTateModule p J))
variable {K : Type} [Field K] (Λ : rationalHeckeAlgebra p J →+* K)

def rhoK (hcomm : CommHyp p J) : Gal →* Module.End K (Fin 2 → K) :=
  (transfer p J b Λ).toMonoidHom.comp (galAHom p J hcomm)

theorem rhoK_apply (hcomm : CommHyp p J) (σ : Gal) :
    rhoK p J b Λ hcomm σ = transfer p J b Λ (galA p J hcomm σ) := rfl

def iotaK (x : TateModule p J) : Fin 2 → K := coordK p J b Λ ((1 : ℚ_[p]) ⊗ₜ[ℤ_[p]] x)

theorem iotaK_add (x y : TateModule p J) :
    iotaK p J b Λ (x + y) = iotaK p J b Λ x + iotaK p J b Λ y := by
  simp [iotaK, TensorProduct.tmul_add]

theorem iotaK_zero : iotaK p J b Λ 0 = 0 := by simp [iotaK]

theorem iotaK_sub (x y : TateModule p J) :
    iotaK p J b Λ (x - y) = iotaK p J b Λ x - iotaK p J b Λ y := by
  simp [iotaK, TensorProduct.tmul_sub]

theorem rhoK_iotaK (hcomm : CommHyp p J) (σ : Gal) (x : TateModule p J) :
    rhoK p J b Λ hcomm σ (iotaK p J b Λ x) = iotaK p J b Λ (TateModule.rep p J Gal σ x) := by
  rw [rhoK_apply, iotaK, iotaK, ← coordK_endo, galA_apply, rationalGaloisRep_tmul]

theorem galA_quadratic (hcomm : CommHyp p J) {ℓ : ℕ} (hℓ : ℓ.Prime) (σ : Gal)
    (hES : ∀ x : TateModule p J,
      TateModule.rep p J Gal σ (TateModule.rep p J Gal σ x)
        - TateModule.rep p J HeckeAlg (heckeGen ⟨ℓ, hℓ⟩) (TateModule.rep p J Gal σ x) + ℓ • x = 0) :
    galA p J hcomm σ * galA p J hcomm σ
      - (⟨rationalHeckeRep p J (heckeGen ⟨ℓ, hℓ⟩),
          rationalHeckeRep_mem_rationalHeckeAlgebra p J _⟩ : rationalHeckeAlgebra p J) • galA p J hcomm σ
      + ((ℓ : ℕ) : Module.End (rationalHeckeAlgebra p J) (RationalTateModule p J)) = 0 := by
  refine LinearMap.ext fun v => ?_
  simp only [LinearMap.add_apply, LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply,
    LinearMap.zero_apply, galA_apply, subalgebra_smul_def]
  induction v using TensorProduct.induction_on with
  | zero => simp
  | tmul c x =>
    rw [Module.End.natCast_apply, rationalGaloisRep_tmul, rationalGaloisRep_tmul, rationalHeckeRep_tmul,
      tateHeckeRep_apply, ← Nat.cast_smul_eq_nsmul ℤ_[p], ← TensorProduct.tmul_smul,
      Nat.cast_smul_eq_nsmul, ← TensorProduct.tmul_sub, ← TensorProduct.tmul_add, hES x,
      TensorProduct.tmul_zero]
  | add v w hv hw =>
    have e : rationalGaloisRep p J Gal σ (rationalGaloisRep p J Gal σ (v + w))
        - rationalHeckeRep p J (heckeGen ⟨ℓ, hℓ⟩) (rationalGaloisRep p J Gal σ (v + w))
        + ((ℓ : ℕ) : Module.End (rationalHeckeAlgebra p J) (RationalTateModule p J)) (v + w)
        = (rationalGaloisRep p J Gal σ (rationalGaloisRep p J Gal σ v)
            - rationalHeckeRep p J (heckeGen ⟨ℓ, hℓ⟩) (rationalGaloisRep p J Gal σ v)
            + ((ℓ : ℕ) : Module.End (rationalHeckeAlgebra p J) (RationalTateModule p J)) v)
          + (rationalGaloisRep p J Gal σ (rationalGaloisRep p J Gal σ w)
            - rationalHeckeRep p J (heckeGen ⟨ℓ, hℓ⟩) (rationalGaloisRep p J Gal σ w)
            + ((ℓ : ℕ) : Module.End (rationalHeckeAlgebra p J) (RationalTateModule p J)) w) := by
      simp only [map_add]
      abel
    rw [e, hv, hw, add_zero]

theorem rhoK_quadratic (hcomm : CommHyp p J) {ℓ : ℕ} (hℓ : ℓ.Prime) (σ : Gal)
    (hES : ∀ x : TateModule p J,
      TateModule.rep p J Gal σ (TateModule.rep p J Gal σ x)
        - TateModule.rep p J HeckeAlg (heckeGen ⟨ℓ, hℓ⟩) (TateModule.rep p J Gal σ x) + ℓ • x = 0) :
    rhoK p J b Λ hcomm σ * rhoK p J b Λ hcomm σ
      - Λ ⟨rationalHeckeRep p J (heckeGen ⟨ℓ, hℓ⟩), rationalHeckeRep_mem_rationalHeckeAlgebra p J _⟩
          • rhoK p J b Λ hcomm σ
      + ((ℓ : ℕ) : Module.End K (Fin 2 → K)) = 0 := by
  have h := congrArg (transfer p J b Λ) (galA_quadratic p J hcomm hℓ σ hES)
  rwa [map_add, map_sub, map_mul, transfer_smul, map_natCast, map_zero] at h

theorem det_rhoK (hcomm : CommHyp p J) (σ : Gal) :
    LinearMap.det (rhoK p J b Λ hcomm σ)
      = Λ ((b.repr (rationalGaloisRep p J Gal σ (b 0))) 0
              * (b.repr (rationalGaloisRep p J Gal σ (b 1))) 1
            - (b.repr (rationalGaloisRep p J Gal σ (b 1))) 0
              * (b.repr (rationalGaloisRep p J Gal σ (b 0))) 1) := by
  rw [rhoK_apply, det_transfer, ← LinearMap.det_toMatrix b, Matrix.det_fin_two]
  simp only [LinearMap.toMatrix_apply, galA_apply]

end Frobenius

section Lattice

variable [DistribMulAction Gal J]
variable (b : Module.Basis (Fin 2) (rationalHeckeAlgebra p J) (RationalTateModule p J))
variable {K : Type} [Field K] (Λ : rationalHeckeAlgebra p J →+* K)
variable (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra O K]
  [IsFractionRing O K] [Algebra ℤ_[p] O]

def lattice : Submodule O (Fin 2 → K) := Submodule.span O (Set.range (iotaK p J b Λ))

theorem iotaK_mem (x : TateModule p J) : iotaK p J b Λ x ∈ lattice p J b Λ O :=
  Submodule.subset_span ⟨x, rfl⟩

def Compat : Prop :=
  ∀ c : ℤ_[p], Λ (algebraMap ℚ_[p] (rationalHeckeAlgebra p J) (c : ℚ_[p]))
    = algebraMap O K (algebraMap ℤ_[p] O c)

theorem iotaK_smul (hc : Compat p J Λ O) (c : ℤ_[p]) (x : TateModule p J) :
    iotaK p J b Λ (c • x) = (algebraMap ℤ_[p] O c) • iotaK p J b Λ x := by
  rw [iotaK, iotaK, TensorProduct.tmul_smul, ← algebraMap_smul ℚ_[p] c, ← algebraMap_smul_eq,
    coordK_smul, show algebraMap ℤ_[p] ℚ_[p] c = (c : ℚ_[p]) from rfl, hc, algebraMap_smul]

theorem lattice_stable (hcomm : CommHyp p J) (σ : Gal) :
    ∀ v ∈ lattice p J b Λ O, rhoK p J b Λ hcomm σ v ∈ lattice p J b Λ O := by
  intro v hv
  have : lattice p J b Λ O ≤ (lattice p J b Λ O).comap ((rhoK p J b Λ hcomm σ).restrictScalars O) := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨x, rfl⟩
    simp only [SetLike.mem_coe, Submodule.mem_comap, LinearMap.coe_restrictScalars, rhoK_iotaK]
    exact iotaK_mem p J b Λ O _
  exact this hv

def rhoL (hcomm : CommHyp p J) (σ : Gal) : lattice p J b Λ O →ₗ[O] lattice p J b Λ O :=
  ((rhoK p J b Λ hcomm σ).restrictScalars O).restrict (lattice_stable p J b Λ O hcomm σ)

@[scoped simp] theorem coe_rhoL (hcomm : CommHyp p J) (σ : Gal) (v : lattice p J b Λ O) :
    ((rhoL p J b Λ O hcomm σ v : lattice p J b Λ O) : Fin 2 → K) = rhoK p J b Λ hcomm σ v := rfl

def rhoLHom (hcomm : CommHyp p J) : Gal →* Module.End O (lattice p J b Λ O) where
  toFun := rhoL p J b Λ O hcomm
  map_one' := LinearMap.ext fun v => Subtype.ext (by simp)
  map_mul' σ τ := LinearMap.ext fun v => Subtype.ext (by simp)

@[scoped simp] theorem rhoLHom_apply (hcomm : CommHyp p J) (σ : Gal) :
    rhoLHom p J b Λ O hcomm σ = rhoL p J b Λ O hcomm σ := rfl

theorem eq_top_of_forall_iotaK_mem (N : Submodule O (lattice p J b Λ O))
    (h : ∀ x, ⟨iotaK p J b Λ x, iotaK_mem p J b Λ O x⟩ ∈ N) : N = ⊤ := by
  rw [eq_top_iff]
  rintro ⟨v, hv⟩ -
  induction hv using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨x, rfl⟩ := hw
    exact h x
  | zero => exact N.zero_mem
  | add u w hu hw ihu ihw => exact N.add_mem ihu ihw
  | smul c w hw ih => exact N.smul_mem c ih

theorem lattice_finite [Module.Finite ℤ_[p] (TateModule p J)] (hc : Compat p J Λ O) :
    Module.Finite O (lattice p J b Λ O) := by
  obtain ⟨S, hS⟩ := Module.Finite.fg_top (R := ℤ_[p]) (M := TateModule p J)
  have hsub : Set.range (iotaK p J b Λ) ⊆ Submodule.span O (iotaK p J b Λ '' S) := by
    rintro _ ⟨x, rfl⟩
    have hx : x ∈ Submodule.span ℤ_[p] (S : Set (TateModule p J)) := hS ▸ Submodule.mem_top
    induction hx using Submodule.span_induction with
    | mem y hy => exact Submodule.subset_span ⟨y, hy, rfl⟩
    | zero => rw [iotaK_zero]; exact zero_mem _
    | add y z _ _ hy hz => rw [iotaK_add]; exact add_mem hy hz
    | smul c y _ hy => rw [iotaK_smul p J b Λ O hc]; exact Submodule.smul_mem _ _ hy
  rw [Module.Finite.iff_fg, Submodule.fg_def]
  refine ⟨iotaK p J b Λ '' S, S.finite_toSet.image _, le_antisymm ?_ ?_⟩
  · exact Submodule.span_mono (Set.image_subset_range _ _)
  · exact Submodule.span_le.mpr hsub

scoped instance : Module.IsTorsionFree O (Fin 2 → K) := by
  haveI : Module.IsTorsionFree O K :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr (IsFractionRing.injective O K)
  infer_instance

theorem lattice_free [Module.Finite ℤ_[p] (TateModule p J)] (hc : Compat p J Λ O) :
    Module.Free O (lattice p J b Λ O) := by
  haveI := lattice_finite p J b Λ O hc
  infer_instance

theorem coordK_mem_span (v : RationalTateModule p J) :
    coordK p J b Λ v ∈ Submodule.span K (Set.range (iotaK p J b Λ)) := by
  induction v using TensorProduct.induction_on with
  | zero => rw [map_zero]; exact zero_mem _
  | tmul c x =>
    have : c ⊗ₜ[ℤ_[p]] x = (algebraMap ℚ_[p] (rationalHeckeAlgebra p J) c) • ((1 : ℚ_[p]) ⊗ₜ[ℤ_[p]] x) := by
      rw [algebraMap_smul_eq, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [this, coordK_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨x, rfl⟩)
  | add v w hv hw => rw [map_add]; exact add_mem hv hw

theorem span_K_range_iotaK : Submodule.span K (Set.range (iotaK p J b Λ)) = ⊤ := by
  classical
  rw [eq_top_iff]
  rintro v -
  rw [← Finset.univ_sum_single v]
  refine Submodule.sum_mem _ fun i _ => ?_
  have : Pi.single i (v i) = v i • (Pi.single i (1 : K) : Fin 2 → K) := by
    rw [← Pi.single_smul, smul_eq_mul, mul_one]
  rw [this, ← coordK_basis p J b Λ]
  exact Submodule.smul_mem _ _ (coordK_mem_span p J b Λ _)

theorem lattice_le_span_K [Module.Finite ℤ_[p] (TateModule p J)] (hc : Compat p J Λ O) :
    letI := lattice_free p J b Λ O hc
    ((lattice p J b Λ O : Submodule O (Fin 2 → K)) : Set (Fin 2 → K))
      ⊆ Submodule.span K (Set.range fun i => ((Module.Free.chooseBasis O (lattice p J b Λ O) i
          : lattice p J b Λ O) : Fin 2 → K)) := by
  letI := lattice_free p J b Λ O hc
  letI := lattice_finite p J b Λ O hc
  intro z hz
  set f := Module.Free.chooseBasis O (lattice p J b Λ O)
  have hz' := f.sum_repr ⟨z, hz⟩
  have : z = ∑ i, (f.repr ⟨z, hz⟩ i) • ((f i : lattice p J b Λ O) : Fin 2 → K) := by
    conv_lhs => rw [show z = ((⟨z, hz⟩ : lattice p J b Λ O) : Fin 2 → K) from rfl, ← hz']
    rw [Submodule.coe_sum]
    rfl
  rw [SetLike.mem_coe, this]
  refine Submodule.sum_mem _ fun i _ => ?_
  rw [← algebraMap_smul K]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

def basisK [Module.Finite ℤ_[p] (TateModule p J)] (hc : Compat p J Λ O) :
    letI := lattice_free p J b Λ O hc
    Module.Basis (Module.Free.ChooseBasisIndex O (lattice p J b Λ O)) K (Fin 2 → K) :=
  letI := lattice_free p J b Λ O hc
  Module.Basis.mk
    (v := fun i => ((Module.Free.chooseBasis O (lattice p J b Λ O) i : lattice p J b Λ O) : Fin 2 → K))
    (((Module.Free.chooseBasis O (lattice p J b Λ O)).linearIndependent.map'
        (lattice p J b Λ O).subtype (Submodule.ker_subtype _)).localization K (nonZeroDivisors O))
    (by
      rw [← span_K_range_iotaK p J b Λ, Submodule.span_le]
      rintro _ ⟨x, rfl⟩
      exact lattice_le_span_K p J b Λ O hc (iotaK_mem p J b Λ O x))

theorem basisK_apply [Module.Finite ℤ_[p] (TateModule p J)] (hc : Compat p J Λ O) (i) :
    letI := lattice_free p J b Λ O hc
    basisK p J b Λ O hc i = ((Module.Free.chooseBasis O (lattice p J b Λ O) i : lattice p J b Λ O) : Fin 2 → K) := by
  simp [basisK]

theorem finrank_lattice [Module.Finite ℤ_[p] (TateModule p J)] (hc : Compat p J Λ O) :
    Module.finrank O (lattice p J b Λ O) = 2 := by
  letI := lattice_free p J b Λ O hc
  letI := lattice_finite p J b Λ O hc
  have h1 := Module.finrank_eq_card_basis (basisK p J b Λ O hc)
  rw [Module.finrank_fin_fun] at h1
  rw [Module.finrank_eq_card_chooseBasisIndex, ← h1]

theorem basisK_repr [Module.Finite ℤ_[p] (TateModule p J)] (hc : Compat p J Λ O)
    (z : lattice p J b Λ O) (i) :
    letI := lattice_free p J b Λ O hc
    (basisK p J b Λ O hc).repr (z : Fin 2 → K) i
      = algebraMap O K ((Module.Free.chooseBasis O (lattice p J b Λ O)).repr z i) := by
  letI := lattice_free p J b Λ O hc
  letI := lattice_finite p J b Λ O hc
  set f := Module.Free.chooseBasis O (lattice p J b Λ O)
  have hz : (z : Fin 2 → K) = ∑ j, algebraMap O K (f.repr z j) • basisK p J b Λ O hc j := by
    conv_lhs => rw [← f.sum_repr z]
    rw [Submodule.coe_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [basisK_apply, algebraMap_smul, Submodule.coe_smul_of_tower]
  rw [hz, Module.Basis.repr_sum_self]

theorem algebraMap_det_rhoL [Module.Finite ℤ_[p] (TateModule p J)] (hc : Compat p J Λ O)
    (hcomm : CommHyp p J) (σ : Gal) :
    algebraMap O K (LinearMap.det (rhoL p J b Λ O hcomm σ)) = LinearMap.det (rhoK p J b Λ hcomm σ) := by
  letI := lattice_free p J b Λ O hc
  letI := lattice_finite p J b Λ O hc
  classical
  set f := Module.Free.chooseBasis O (lattice p J b Λ O)
  rw [← LinearMap.det_toMatrix f, ← LinearMap.det_toMatrix (basisK p J b Λ O hc), RingHom.map_det]
  congr 1
  ext i j
  rw [RingHom.mapMatrix_apply, Matrix.map_apply, LinearMap.toMatrix_apply, LinearMap.toMatrix_apply,
    basisK_apply, ← coe_rhoL, basisK_repr p J b Λ O hc]

def ContHyp : Prop :=
  ∀ m : ℕ, ∃ L : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ L ∧
    ∀ σ : Gal, (∀ x ∈ L, σ x = x) → ∀ P : J, ((p ^ m : ℕ) : ℤ) • P = 0 → σ • P = P

theorem rhoL_sub_apply (hcomm : CommHyp p J) (σ : Gal) (v : lattice p J b Λ O) :
    (((rhoL p J b Λ O hcomm σ - 1) v : lattice p J b Λ O) : Fin 2 → K)
      = rhoK p J b Λ hcomm σ v - v := rfl

theorem rhoL_continuous [Module.Finite ℤ_[p] (TateModule p J)] (hc : Compat p J Λ O)
    (hcomm : CommHyp p J) (hcont : ContHyp p J)
    (hpm : (p : O) ∈ IsLocalRing.maximalIdeal O) :
    GaloisActionIsAdicContinuous O (rhoLHom p J b Λ O hcomm) := by
  intro n
  obtain ⟨L, hL, hfix⟩ := hcont n
  refine ⟨L, hL, fun σ hσ => ?_⟩
  suffices h : Submodule.comap (rhoL p J b Λ O hcomm σ - 1)
      ((IsLocalRing.maximalIdeal O ^ n) • (⊤ : Submodule O (lattice p J b Λ O))) = ⊤ by
    intro v
    have hv : v ∈ Submodule.comap (rhoL p J b Λ O hcomm σ - 1)
        ((IsLocalRing.maximalIdeal O ^ n) • (⊤ : Submodule O (lattice p J b Λ O))) := by
      rw [h]; exact Submodule.mem_top
    rw [Submodule.mem_comap, LinearMap.sub_apply, Module.End.one_apply] at hv
    exact hv
  refine eq_top_of_forall_iotaK_mem p J b Λ O _ fun x => ?_
  rw [Submodule.mem_comap]
  have hmem : TateModule.rep p J Gal σ x - x
      ∈ (IsLocalRing.maximalIdeal ℤ_[p] ^ n) • (⊤ : Submodule ℤ_[p] (TateModule p J)) :=
    TateModule.rep_sub_mem_of_forall_torsionBy σ n
      (fun m hm => hfix σ hσ m ((Submodule.mem_torsionBy_iff _ _).mp hm)) x
  rw [PadicInt.maximalIdeal_eq_span_p, Ideal.span_singleton_pow, Submodule.ideal_span_singleton_smul,
    Submodule.mem_smul_pointwise_iff_exists] at hmem
  obtain ⟨y, -, hy⟩ := hmem
  have hval : (((rhoL p J b Λ O hcomm σ - 1) ⟨iotaK p J b Λ x, iotaK_mem p J b Λ O x⟩
        : lattice p J b Λ O) : Fin 2 → K)
      = ((((p : O) ^ n) • (⟨iotaK p J b Λ y, iotaK_mem p J b Λ O y⟩ : lattice p J b Λ O)
        : lattice p J b Λ O) : Fin 2 → K) := by
    rw [rhoL_sub_apply, Submodule.coe_smul, rhoK_iotaK, ← iotaK_sub, ← hy,
      iotaK_smul p J b Λ O hc, map_pow, map_natCast]
  rw [Subtype.ext hval]
  exact Submodule.smul_mem_smul (Ideal.pow_mem_pow hpm n) Submodule.mem_top

theorem rhoL_eq_one (hcomm : CommHyp p J) (σ : Gal)
    (hfix : ∀ x : TateModule p J, TateModule.rep p J Gal σ x = x) :
    rhoL p J b Λ O hcomm σ = 1 := by
  have h := eq_top_of_forall_iotaK_mem p J b Λ O (LinearMap.ker (rhoL p J b Λ O hcomm σ - 1))
    fun x => by
      rw [LinearMap.mem_ker]
      apply Subtype.ext
      rw [rhoL_sub_apply, rhoK_iotaK, hfix, sub_self]
      rfl
  refine LinearMap.ext fun v => ?_
  have hv : v ∈ LinearMap.ker (rhoL p J b Λ O hcomm σ - 1) := h ▸ Submodule.mem_top
  rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero] at hv
  exact hv

theorem rhoL_quadratic (hcomm : CommHyp p J) {ℓ : ℕ} (hℓ : ℓ.Prime) (σ : Gal)
    (hES : ∀ x : TateModule p J,
      TateModule.rep p J Gal σ (TateModule.rep p J Gal σ x)
        - TateModule.rep p J HeckeAlg (heckeGen ⟨ℓ, hℓ⟩) (TateModule.rep p J Gal σ x) + ℓ • x = 0)
    (t : O) (ht : Λ ⟨rationalHeckeRep p J (heckeGen ⟨ℓ, hℓ⟩),
      rationalHeckeRep_mem_rationalHeckeAlgebra p J _⟩ = algebraMap O K t) :
    rhoL p J b Λ O hcomm σ * rhoL p J b Λ O hcomm σ - t • rhoL p J b Λ O hcomm σ
      + ((ℓ : ℕ) : Module.End O (lattice p J b Λ O)) = 0 := by
  have hK := rhoK_quadratic p J b Λ hcomm hℓ σ hES
  rw [ht] at hK
  refine LinearMap.ext fun v => Subtype.ext ?_
  have := LinearMap.congr_fun hK (v : Fin 2 → K)
  simp only [LinearMap.add_apply, LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply,
    LinearMap.zero_apply, Module.End.natCast_apply] at this
  simp only [LinearMap.add_apply, LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply,
    LinearMap.zero_apply, Module.End.natCast_apply, Submodule.coe_add, Submodule.coe_sub,
    Submodule.coe_smul, Submodule.coe_zero, coe_rhoL, Submodule.coe_smul_of_tower]
  rw [algebraMap_smul] at this
  exact this

theorem det_rhoL [Module.Finite ℤ_[p] (TateModule p J)] (hc : Compat p J Λ O)
    (hcomm : CommHyp p J) (σ : Gal) (d : O)
    (hd : LinearMap.det (rhoK p J b Λ hcomm σ) = algebraMap O K d) :
    LinearMap.det (rhoL p J b Λ O hcomm σ) = d :=
  IsFractionRing.injective O K (by rw [algebraMap_det_rhoL p J b Λ O hc, hd])

def adicRep [Module.Finite ℤ_[p] (TateModule p J)] (hc : Compat p J Λ O) (hcomm : CommHyp p J)
    (hcont : ContHyp p J) (hpm : (p : O) ∈ IsLocalRing.maximalIdeal O) : GaloisRepAdic O :=
  letI := lattice_free p J b Λ O hc
  letI := lattice_finite p J b Λ O hc
  { V := lattice p J b Λ O
    finrank_eq := finrank_lattice p J b Λ O hc
    ρ := rhoLHom p J b Λ O hcomm
    isAdicContinuous := rhoL_continuous p J b Λ O hc hcomm hcont hpm }

@[scoped simp] theorem adicRep_ρ [Module.Finite ℤ_[p] (TateModule p J)] (hc : Compat p J Λ O)
    (hcomm : CommHyp p J) (hcont : ContHyp p J) (hpm : (p : O) ∈ IsLocalRing.maximalIdeal O)
    (σ : Gal) : (adicRep p J b Λ O hc hcomm hcont hpm).ρ σ = rhoL p J b Λ O hcomm σ := rfl

end Lattice

section Main

variable [DistribMulAction Gal J]

theorem main [Module.Finite ℤ_[p] (TateModule p J)] (N : ℕ)
    (hcomm : CommHyp p J)
    (hi : RationalRankTwoCyclotomicOf (K := ℚ) (L := AlgebraicClosure ℚ) N p J)
    (hiii : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime), ¬ ℓ ∣ N * p →
      ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime ℓ →
        ∀ σ : Gal, A.IsFrobeniusAt σ ℓ → ∀ x : TateModule p J,
          TateModule.rep p J Gal σ (TateModule.rep p J Gal σ x)
            - TateModule.rep p J HeckeAlg (heckeGen ⟨ℓ, hℓ⟩) (TateModule.rep p J Gal σ x)
            + ℓ • x = 0)
    (hv : ∀ (ℓ : ℕ), ℓ.Prime → ¬ ℓ ∣ N * p →
      ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime ℓ →
        ∀ σ ∈ A.inertiaSubgroupIn ℚ, ∀ x : TateModule p J, TateModule.rep p J Gal σ x = x)
    (hcont : ContHyp p J)
    (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra ℤ_[p] O]
    (K : Type) [Field K] [Algebra O K] [IsFractionRing O K]
    (θ : HeckeAlg →+* O) (Λ : rationalHeckeAlgebra p J →+* K)
    (hc : Compat p J Λ O)
    (hθ : ∀ t : HeckeAlg, Λ ⟨rationalHeckeRep p J t, rationalHeckeRep_mem_rationalHeckeAlgebra p J t⟩
      = algebraMap O K (θ t))
    (hpm : (p : O) ∈ IsLocalRing.maximalIdeal O) :
    ∃ ρ : GaloisRepAdic O,
      (∀ ℓ : Nat.Primes, ¬ (ℓ : ℕ) ∣ N * p →
        ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime ℓ →
          ∀ σ : Gal, A.IsFrobeniusAt σ ℓ →
            ρ.ρ σ * ρ.ρ σ - θ (heckeGen ℓ) • ρ.ρ σ + ((ℓ : ℕ) : Module.End O ρ.V) = 0 ∧
            LinearMap.det (ρ.ρ σ) = ((ℓ : ℕ) : O)) ∧
      (∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ N * p → ρ.IsUnramifiedAt ℓ) := by
  obtain ⟨b, hb⟩ := hi
  refine ⟨adicRep p J b Λ O hc hcomm hcont hpm, ?_, ?_⟩
  · rintro ⟨ℓ, hℓ⟩ hℓNp A hA σ hσ
    refine ⟨?_, ?_⟩
    · exact rhoL_quadratic p J b Λ O hcomm hℓ σ (hiii ℓ hℓ hℓNp A hA σ hσ) _ (hθ _)
    · refine det_rhoL p J b Λ O hc hcomm σ _ ?_
      rw [det_rhoK, hb ℓ hℓ hℓNp A hA σ hσ, map_natCast, map_natCast]
  · intro ℓ hℓ hℓNp A hA σ hσ
    exact rhoL_eq_one p J b Λ O hcomm σ (hv ℓ hℓ hℓNp A hA σ hσ)

end Main

section TraceId

open Polynomial

variable {O : Type} [CommRing O] {V : Type} [AddCommGroup V] [Module O V]
  [Module.Free O V] [Module.Finite O V]

theorem eq_zero_of_smul_id_eq_zero (hV : 0 < Module.finrank O V) (c : O)
    (hc : c • (LinearMap.id : Module.End O V) = 0) : c = 0 := by
  classical
  nontriviality O
  let b := Module.Free.chooseBasis O V
  haveI : Nonempty (Module.Free.ChooseBasisIndex O V) := by
    rw [Module.finrank_eq_card_chooseBasisIndex] at hV
    exact Fintype.card_pos_iff.mp hV
  obtain ⟨i⟩ := ‹Nonempty (Module.Free.ChooseBasisIndex O V)›
  have h1 : c • b i = 0 := by
    have := LinearMap.congr_fun hc (b i)
    simpa using this
  have h2 := congrArg (fun v => b.repr v i) h1
  simpa using h2

theorem charpoly_eq_of_quadratic_of_det (hV : Module.finrank O V = 2)
    (f : Module.End O V) (hf : IsUnit f) (t d : O)
    (hq : f * f - t • f + algebraMap O (Module.End O V) d = 0) (hdet : LinearMap.det f = d) :
    f.charpoly = X ^ 2 - C t * X + C d := by
  nontriviality O
  have hdeg : f.charpoly.natDegree = 2 := by rw [LinearMap.charpoly_natDegree, hV]
  have hmonic := f.charpoly_monic
  have hc0 : f.charpoly.coeff 0 = d := by
    have h := LinearMap.det_eq_sign_charpoly_coeff f
    rw [hV] at h
    rw [← hdet, h]
    ring
  set c₁ := f.charpoly.coeff 1 with hc₁
  have hshape : f.charpoly = X ^ 2 + C c₁ * X + C d := by
    apply Polynomial.ext
    intro n
    rcases n with _ | _ | _ | n
    · simp [hc0]
    · simp [hc₁]
    · have : f.charpoly.coeff 2 = 1 := by
        have := hmonic.leadingCoeff
        rwa [Polynomial.leadingCoeff, hdeg] at this
      simp [this]
    · have hlt : f.charpoly.natDegree < n + 3 := by omega
      rw [Polynomial.coeff_eq_zero_of_natDegree_lt hlt]
      simp
  have hCH : f * f + c₁ • f + algebraMap O (Module.End O V) d = 0 := by
    have h := LinearMap.aeval_self_charpoly f
    rw [hshape] at h
    simpa [sq, Algebra.smul_def] using h
  have hdiff : (t + c₁) • f = 0 := by
    have := sub_eq_zero.mpr (hCH.trans hq.symm)
    have e : f * f + c₁ • f + algebraMap O (Module.End O V) d
        - (f * f - t • f + algebraMap O (Module.End O V) d) = (t + c₁) • f := by
      rw [add_smul]; abel
    rw [e] at this
    exact this
  obtain ⟨u, rfl⟩ := hf
  have hid : (t + c₁) • (LinearMap.id : Module.End O V) = 0 := by
    have : ((t + c₁) • (u : Module.End O V)) * (↑u⁻¹ : Module.End O V) = 0 := by
      rw [hdiff, zero_mul]
    rwa [smul_mul_assoc, Units.mul_inv] at this
  have hpos : 0 < Module.finrank O V := by rw [hV]; exact two_pos
  have htc : t + c₁ = 0 := eq_zero_of_smul_id_eq_zero hpos _ hid
  have : c₁ = -t := by linear_combination htc
  rw [hshape, this, C_neg]
  ring

end TraceId

section MainCharpoly

open Polynomial

variable [DistribMulAction Gal J]

theorem main_charpoly [Module.Finite ℤ_[p] (TateModule p J)] (N : ℕ)
    (hcomm : CommHyp p J)
    (hi : RationalRankTwoCyclotomicOf (K := ℚ) (L := AlgebraicClosure ℚ) N p J)
    (hiii : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime), ¬ ℓ ∣ N * p →
      ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime ℓ →
        ∀ σ : Gal, A.IsFrobeniusAt σ ℓ → ∀ x : TateModule p J,
          TateModule.rep p J Gal σ (TateModule.rep p J Gal σ x)
            - TateModule.rep p J HeckeAlg (heckeGen ⟨ℓ, hℓ⟩) (TateModule.rep p J Gal σ x)
            + ℓ • x = 0)
    (hv : ∀ (ℓ : ℕ), ℓ.Prime → ¬ ℓ ∣ N * p →
      ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime ℓ →
        ∀ σ ∈ A.inertiaSubgroupIn ℚ, ∀ x : TateModule p J, TateModule.rep p J Gal σ x = x)
    (hcont : ContHyp p J)
    (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra ℤ_[p] O]
    (K : Type) [Field K] [Algebra O K] [IsFractionRing O K]
    (Λ : rationalHeckeAlgebra p J →+* K)
    (hc : Compat p J Λ O)
    (hpm : (p : O) ∈ IsLocalRing.maximalIdeal O) :
    ∃ ρ : GaloisRepAdic O,
      (∀ (ℓ : ℕ) (hℓ : ℓ.Prime), ¬ ℓ ∣ N * p → ∀ a : O,
        Λ ⟨rationalHeckeRep p J (heckeGen ⟨ℓ, hℓ⟩), rationalHeckeRep_mem_rationalHeckeAlgebra p J _⟩
          = algebraMap O K a →
        ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime ℓ →
          ∀ σ : Gal, A.IsFrobeniusAt σ ℓ →
            LinearMap.charpoly (ρ.ρ σ) = X ^ 2 - C a * X + C (ℓ : O)) ∧
      (∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ N * p → ρ.IsUnramifiedAt ℓ) := by
  obtain ⟨b, hb⟩ := hi
  refine ⟨adicRep p J b Λ O hc hcomm hcont hpm, ?_, ?_⟩
  · intro ℓ hℓ hℓNp a ha A hA σ hσ
    have hq := rhoL_quadratic p J b Λ O hcomm hℓ σ (hiii ℓ hℓ hℓNp A hA σ hσ) a ha
    have hd : LinearMap.det (rhoL p J b Λ O hcomm σ) = (ℓ : O) := by
      refine det_rhoL p J b Λ O hc hcomm σ _ ?_
      rw [det_rhoK, hb ℓ hℓ hℓNp A hA σ hσ, map_natCast, map_natCast]
    rw [adicRep_ρ]
    refine charpoly_eq_of_quadratic_of_det (adicRep p J b Λ O hc hcomm hcont hpm).finrank_eq
      (rhoL p J b Λ O hcomm σ) ?_ a (ℓ : O) ?_ hd
    · rw [← rhoLHom_apply]
      exact (Group.isUnit σ).map (rhoLHom p J b Λ O hcomm)
    · rw [map_natCast]
      exact hq
  · intro ℓ hℓ hℓNp A hA σ hσ
    exact rhoL_eq_one p J b Λ O hcomm σ (hv ℓ hℓ hℓNp A hA σ hσ)

end MainCharpoly

end W6BES
p2m_reactivate "P2MW.S_ModularCurve_exists_galoisRepAdic_charpoly_frobenius_of_heckeChar.W6BES"

open Polynomial in
theorem solution
    (N p : ℕ) [NeZero N] [Fact p.Prime]
    (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (K : Type) [Field K] [Algebra O K] [IsFractionRing O K]
    (i₀ : ℤ_[p] →+* O) (hpO : (p : O) ∈ IsLocalRing.maximalIdeal O) :
    letI := ModularCurve.heckeModuleBar N
    ∀ (Λ : ↥(ModularCurve.rationalHeckeAlgebra p (ModularCurve.JZero N)) →+* K),
      (∀ c : ℤ_[p],
        Λ (algebraMap ℚ_[p] ↥(ModularCurve.rationalHeckeAlgebra p (ModularCurve.JZero N)) (c : ℚ_[p]))
          = algebraMap O K (i₀ c)) →
      ∃ ρ : GaloisRepAdic O,
        (∀ (ℓ : ℕ) (hℓ : ℓ.Prime), ¬ ℓ ∣ N * p → ∀ a : O,
          Λ ⟨ModularCurve.rationalHeckeRep p (ModularCurve.JZero N) (ModularCurve.heckeGen ⟨ℓ, hℓ⟩),
              ModularCurve.rationalHeckeRep_mem_rationalHeckeAlgebra p (ModularCurve.JZero N) _⟩
            = algebraMap O K a →
          ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime ℓ →
            ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, A.IsFrobeniusAt σ ℓ →
              LinearMap.charpoly (ρ.ρ σ) = X ^ 2 - C a * X + C (ℓ : O)) ∧
        (∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ N * p → ρ.IsUnramifiedAt ℓ) := by
  letI := ModularCurve.heckeModuleBar N
  intro Λ hΛ
  letI : Algebra ℤ_[p] O := i₀.toAlgebra
  have hp : p.Prime := Fact.out
  have hcb := ModularCurve.heckeOperatorsCommuteBar N
  haveI : Module.Finite ℤ_[p] (TateModule p (ModularCurve.JZero N)) :=
    ModularCurve.moduleFinite_padicInt_tateModule_jZero N p
  have hcomm : W6BES.CommHyp p (ModularCurve.JZero N) := fun σ t x =>
    ModularCurve.rep_tateModule_jZero_comm N p hcb σ t x
  have hi : ModularCurve.RationalRankTwoCyclotomic N p :=
    ModularCurve.rationalRankTwoCyclotomic_family N p (Nat.pos_of_ne_zero (NeZero.ne N)) hp
  have hcont : W6BES.ContHyp p (ModularCurve.JZero N) := fun m =>
    ModularCurve.JZero.exists_finiteDimensional_smul_eq_self_of_torsion N (p ^ m) (pow_pos hp.pos m)
  have hc : W6BES.Compat p (ModularCurve.JZero N) Λ O := fun c => hΛ c
  exact W6BES.main_charpoly p (ModularCurve.JZero N) N hcomm hi
    (fun ℓ hℓ hℓNp A hA σ hσ x =>
      ModularCurve.frobeniusQuadratic_tateModule_jZero N p hcb hℓ hℓNp A hA σ hσ x)
    (fun ℓ hℓ hℓNp A hA σ hσ x =>
      ModularCurve.rep_tateModule_jZero_eq_self_of_mem_inertiaSubgroupIn N p hcb hℓ hℓNp A hA σ hσ x)
    hcont O K Λ hc hpO

end
end S_ModularCurve_exists_galoisRepAdic_charpoly_frobenius_of_heckeChar
end P2MW
export P2MW.S_ModularCurve_exists_galoisRepAdic_charpoly_frobenius_of_heckeChar (solution)
