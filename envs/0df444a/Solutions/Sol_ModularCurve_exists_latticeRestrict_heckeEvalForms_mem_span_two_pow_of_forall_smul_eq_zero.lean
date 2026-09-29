-- Prove2me | solution 1 for ModularCurve.exists_latticeRestrict_heckeEvalForms_mem_span_two_pow_of_forall_smul_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/7af37e7b-6541-5e12-beb4-6b7bfc57c15f

import Mathlib
import Definitions.Def_ModularCurve_JZeroNeronTorsionSheafV4
import Definitions.Def_CuspForm_HeckeLocal
import Definitions.Def_CuspForm_HeckeEvalForms
import Definitions.Def_ModularCurve_JZeroTateModule
import Definitions.Def_ModularCurve_HeckeModule
import Definitions.Def_FLTPrelim_Ramification
import Theorems.Thm_exists_forall_eq_pow_smul_of_forall_smul_mem_of_faithful
import Theorems.Thm_ModularCurve_moduleFinite_padicInt_tateModule_jZero
import Definitions.Def_ModularCurve_ReductionModL
import Theorems.Thm_ModularCurve_exists_tateModule_inertia_fixed_linearIndependent_heckeLatticeAlgebra_orbit
import Theorems.Thm_ModularCurve_ker_heckeEvalForms_latticeRestrict_eq_ker_heckeEvalBar
import Theorems.Thm_ModularCurve_heckeOperatorsCommuteBar
import Theorems.Thm_CuspForm_heckeEvalForms_range_eq_top
import Theorems.Thm_ModularCurve_smul_eq_self_of_mem_inertiaSubgroupIn_of_nsmul_eq_zero_of_not_dvd
import Theorems.Thm_ValuationSubring_exists_liesOverPrime_algebraicClosure_rat
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_latticeRestrict_heckeEvalForms_mem_span_two_pow_of_forall_smul_eq_zero
p2m_attr_erase "instance" "AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion AlgebraicCurve.CellDissection.fintypeV AlgebraicCurve.CellDissection.fintypeC AlgebraicCurve.CellDissection.fintypeE AlgebraicCurve.CellDissection.decEqV AlgebraicCurve.CellDissection.decEqC"
p2m_attr_erase "instance" "AlgebraicCurve.CellDissection.decEqE ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.CuspSpace.instNonempty ModularCurve.CuspSpace.instSubsingletonOfOne ModularCurve.CuspSpace.instFinite ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.instAlgebraIntermediateFieldLaurent ModularCurve.instIsScalarTowerKaehlerIntermediateFieldLaurent ModularCurve.instIsScalarTowerIntermediateFieldLaurent ModularCurve.instModuleKaehlerIntermediateFieldLaurent ModularCurve.Gamma0Pair.isElliptic ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.B3.instIsElliptic_goodModel ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar ModularCurve.instIsScalarTowerJAdjoin HeckeEis.instFiniteIndexHeckeUpper ModularCurve.Period.parabolicHoms_int_moduleFinite ModularCurve.Period.instGroupFG_SL2Z ModularCurve.Period.instIsNoetherian_addHom_int ModularCurve.Period.instGroupFG_Gamma0 FLT.Gamma0FundamentalSet.instContinuousConstSMulSpecialLinearGroupFinOfNatNatIntUpperHalfPlane_definitions FLT.HyperbolicMeasure.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatIntUpperHalfPlaneVolume_definitions FLT.HyperbolicMeasure.instIsOpenPosMeasureUpperHalfPlaneVolume_definitions FLT.L2ProductionInstance.isFiniteMeasure_gamma0 FLT.L2ProductionInstance.countable_SL2Z FLT.L2ProductionInstance.countable_quotient FLT.L2ProductionInstance.nontrivial_gamma0L2"
p2m_attr_erase "instance" "HeckeEis.instModuleCoeffH1par HeckeEis.instAddCommGroupCoeffH1par WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular"
p2m_attr_erase "simp" "AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq"
p2m_attr_erase "simp" "AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule AlgebraicCurve.abelJacobiDiv_single AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one AlgebraicCurve.AnalyticCoord.mk.injEq AlgebraicCurve.Cell.mk.sizeOf_spec AlgebraicCurve.RadialRegion.mk.sizeOf_spec AlgebraicCurve.RadialRegion.mk.injEq AlgebraicCurve.CellDissection.mk.sizeOf_spec AlgebraicCurve.Cell.mk.injEq AlgebraicCurve.CellDissection.mk.injEq AlgebraicCurve.AnalyticCoord.mk.sizeOf_spec AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq"
p2m_attr_erase "simp" "AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar HahnSeries.ramScale_apply ModularCurve.dualHeckeRep_apply_apply ModularCurve.coe_segmentPath ModularCurve.cuspHeckeAeval_heckeGen ModularCurve.coe_periodLatticeRestrict_apply ModularCurve.Period.IsEquivariantPrimitive.periodHom_apply ModularCurve.Period.IsEquivariantPrimitive.period_one ModularCurve.cuspCount_one ModularCurve.CuspSpace.cuspDenomAux_infty ModularCurve.CuspSpace.cuspDenomAux_coe ModularCurve.CuspSpace.cuspDenom_mk_zero ModularCurve.CuspSpace.cuspDenom_mk_infty ModularCurve.mapGL_apply_coe ModularCurve.ratPoint_one_zero ModularCurve.ratPoint_zero_right"
p2m_attr_erase "simp" "ModularCurve.CuspSpace.fromCoset_mk ModularCurve.CuspSpace.cuspDenom_mk ModularCurve.ratPoint_zero_one ModularCurve.ProjectiveLine.map_mk ModularCurve.qEulerFun_coeff ModularCurve.diffQExp_D ModularCurve.qEulerOn_apply ModularCurve.qEuler_coeff ModularCurve.gamma0PairMap_gen ModularCurve.moduliPointMapRingHom_mk ModularCurve.Gamma0Pair.mk.injEq ModularCurve.ModuliPoint.j_mk ModularCurve.Gamma0Pair.mk.sizeOf_spec ModularCurve.gamma0PairMap_toCurve WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero WeierstrassCurve.ratPointHom_apply WeierstrassCurve.ratPointMap_zero ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ WeierstrassCurve.veluX_empty WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁"
p2m_attr_erase "simp" "WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual"
p2m_attr_erase "simp" "AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply WeierstrassCurve.veluPointMap2_zero ModularCurve.Period.jConjMat_apply_zero_one ModularCurve.Period.jConjSL_coe ModularCurve.Period.jConjMat_apply_one_zero ModularCurve.Period.jConjMat_apply_one_one ModularCurve.Period.jConjGamma0_coe ModularCurve.Period.charInvolution_apply ModularCurve.Period.jConjMat_apply_zero_zero HeckeEis.heckeConjMat_apply_one_one HeckeEis.coe_heckeConjSL HeckeEis.mem_heckeUpperSL HeckeEis.resHom_apply"
p2m_attr_erase "simp" "HeckeEis.heckeConjMat_apply_zero_one HeckeEis.coe_transferAux HeckeEis.coe_heckeConj HeckeEis.alphaMat_apply_one_one HeckeEis.heckeConjMat_apply_one_zero HeckeEis.alphaMat_apply_zero_one HeckeEis.pullbackHom_apply HeckeEis.alphaMat_apply_one_zero HeckeEis.alphaMat_apply_zero_zero HeckeEis.heckeConjMat_apply_zero_zero PowerSeries.coeff_heckeV PowerSeries.coeff_heckeU ModularCurve.ComplexPlaceDictionary.mk.injEq ModularCurve.ComplexPlaceDictionary.mk.sizeOf_spec FLT.TruncatedDomainPartition.unipotentDiagonalSum_zero HeckeEis.coeffCoboundaryMap_apply ModularForm.coe_atkinLehnerLin_apply CuspForm.coe_atkinLehnerLin_apply ModularForm.AtkinLehnerDatum.mk.injEq ModularForm.AtkinLehnerDatum.alGL_coe ModularForm.AtkinLehnerDatum.mk.sizeOf_spec ModularForm.AtkinLehnerDatum.sqUnitSL_coe ModularForm.AtkinLehnerDatum.det_sqUnit ModularForm.AtkinLehnerDatum.det_mat CuspForm.coe_traceLin_apply ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW"
p2m_attr_erase "simp" "WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄"
p2m_attr_erase "simp" "TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 3200000
set_option maxHeartbeats 8000000

p2m_open "ModularCurve P2MW.S_ModularCurve_exists_latticeRestrict_heckeEvalForms_mem_span_two_pow_of_forall_smul_eq_zero.ModularCurve CuspForm"

namespace ModularCurve
p2m_export "ModularCurve" "heckeModuleBar heckeModuleBar_smul_def JZero HeckeAlg tateHeckeRep coe_tateHeckeRep_apply_apply moduleFinite_padicInt_tateModule_jZero exists_tateModule_inertia_fixed_linearIndependent_heckeLatticeAlgebra_orbit ker_heckeEvalForms_latticeRestrict_eq_ker_heckeEvalBar heckeOperatorsCommuteBar smul_eq_self_of_mem_inertiaSubgroupIn_of_nsmul_eq_zero_of_not_dvd"
namespace Sat
p2m_open "ModularCurve"

variable (p : ℕ) [Fact p.Prime]

theorem noZeroSMulDivisors_tateModule : NoZeroSMulDivisors ℤ_[2] (TateModule 2 (JZero p)) := by
  refine ⟨fun {a x} h => ?_⟩
  by_cases ha : a = 0
  · exact Or.inl ha
  right
  have hval := PadicInt.unitCoeff_spec ha
  have hk : ((PadicInt.unitCoeff ha)⁻¹ : (ℤ_[2])ˣ).val * a = ((2 : ℕ) : ℤ_[2]) ^ a.valuation :=
    (congrArg (fun z => ((PadicInt.unitCoeff ha)⁻¹ : (ℤ_[2])ˣ).val * z) hval).trans
      (by rw [← mul_assoc, Units.inv_mul, one_mul])
  have hz : ((PadicInt.unitCoeff ha)⁻¹ : (ℤ_[2])ˣ).val • (0 : TateModule 2 (JZero p)) = 0 :=
    Subtype.ext (funext fun n => by
      rw [TateModule.smul_apply, TateModule.coe_zero, Pi.zero_apply, zsmul_zero])
  have h2 : ((2 : ℕ) : ℤ_[2]) ^ a.valuation • x = 0 := by
    rw [← hk, mul_smul, h]
    exact hz
  refine Subtype.ext (funext fun n => ?_)
  have hc := TateModule.compat_pow x n a.valuation
  have hn := congrArg (fun y : TateModule 2 (JZero p) => (y : ℕ → JZero p) (n + a.valuation)) h2
  simp only [TateModule.coe_zero, Pi.zero_apply] at hn
  rw [← Nat.cast_pow, TateModule.natCast_padicInt_smul_apply] at hn
  rw [TateModule.coe_zero, Pi.zero_apply, ← hc]
  exact hn

section hecke
variable [Module HeckeAlg (JZero p)]

theorem tateHeckeRep_comm :
    ∀ a ∈ (Set.range fun t : HeckeAlg => tateHeckeRep 2 (JZero p) t),
      ∀ b ∈ (Set.range fun t : HeckeAlg => tateHeckeRep 2 (JZero p) t), a * b = b * a := by
  rintro _ ⟨s, rfl⟩ _ ⟨t, rfl⟩
  show tateHeckeRep 2 (JZero p) s * tateHeckeRep 2 (JZero p) t =
    tateHeckeRep 2 (JZero p) t * tateHeckeRep 2 (JZero p) s
  rw [← map_mul, ← map_mul, mul_comm]

theorem exists_tateHeckeRep_eq_pow_smul (N : ℕ) (u : HeckeAlg)
    (hu : ∀ y : JZero p, 2 ^ N • y = 0 → u • y = 0) (x : TateModule 2 (JZero p)) :
    ∃ y : TateModule 2 (JZero p), tateHeckeRep 2 (JZero p) u x = ((2 : ℕ) : ℤ_[2]) ^ N • y := by

  have hyT : (fun n => u • (x : ℕ → JZero p) (n + N)) ∈ TateModule 2 (JZero p) := by
    intro n
    refine ⟨?_, ?_⟩
    ·
      show ((2 ^ n : ℕ) : ℤ) • (u • (x : ℕ → JZero p) (n + N)) = 0
      rw [smul_comm, show n + N = N + n from Nat.add_comm n N, TateModule.compat_pow x N n]
      apply hu
      have := TateModule.torsion x N
      rw [natCast_zsmul] at this
      exact this
    ·
      show ((2 : ℕ) : ℤ) • (u • (x : ℕ → JZero p) (n + 1 + N)) = u • (x : ℕ → JZero p) (n + N)
      rw [smul_comm, show n + 1 + N = (n + N) + 1 by omega, TateModule.compat x (n + N)]
  refine ⟨⟨_, hyT⟩, Subtype.ext (funext fun n => ?_)⟩
  rw [coe_tateHeckeRep_apply_apply, ← Nat.cast_pow, TateModule.natCast_padicInt_smul_apply]
  show u • (x : ℕ → JZero p) n = ((2 ^ N : ℕ) : ℤ) • (u • (x : ℕ → JZero p) (n + N))
  rw [smul_comm, TateModule.compat_pow x n N]

theorem exists_bound_tateHeckeRep_eq_pow_smul :
    ∃ b : ℕ, ∀ (m : ℕ) (u : HeckeAlg),
      (∀ y : JZero p, 2 ^ (m + b) • y = 0 → u • y = 0) →
      ∃ α ∈ Algebra.adjoin ℤ_[2] (Set.range fun t : HeckeAlg => tateHeckeRep 2 (JZero p) t),
        tateHeckeRep 2 (JZero p) u = ((2 : ℕ) : ℤ_[2]) ^ m • α := by
  have hp : p.Prime := Fact.out
  haveI : NeZero p := ⟨hp.ne_zero⟩
  haveI : Module.Finite ℤ_[2] (TateModule 2 (JZero p)) :=
    ModularCurve.moduleFinite_padicInt_tateModule_jZero p 2
  haveI := noZeroSMulDivisors_tateModule p
  let A₀ := Algebra.adjoin ℤ_[2] (Set.range fun t : HeckeAlg => tateHeckeRep 2 (JZero p) t)
  letI : CommRing ↥A₀ := Algebra.adjoinCommRingOfComm ℤ_[2] (tateHeckeRep_comm p)
  haveI : IsScalarTower ℤ_[2] ↥A₀ (TateModule 2 (JZero p)) := ⟨fun _ _ _ => rfl⟩
  have hsm : ∀ (t : ↥A₀) (x : TateModule 2 (JZero p)),
      t • x = (t : Module.End ℤ_[2] (TateModule 2 (JZero p))) x := fun _ _ => rfl
  have hfaith : ∀ t : ↥A₀, (∀ x : TateModule 2 (JZero p), t • x = 0) → t = 0 := by
    intro t ht
    exact Subtype.ext (LinearMap.ext fun x => (hsm t x).symm.trans (ht x))
  obtain ⟨b, hb⟩ := exists_forall_eq_pow_smul_of_forall_smul_mem_of_faithful
    (R := ℤ_[2]) ((2 : ℕ) : ℤ_[2]) PadicInt.irreducible_p (A := ↥A₀) (M := TateModule 2 (JZero p)) hfaith
  refine ⟨b, fun m u hu => ?_⟩
  have hρA₀ : tateHeckeRep 2 (JZero p) u ∈ A₀ := Algebra.subset_adjoin ⟨u, rfl⟩
  obtain ⟨t', ht'⟩ := hb m ⟨tateHeckeRep 2 (JZero p) u, hρA₀⟩ (fun x => by
    obtain ⟨y, hy⟩ := exists_tateHeckeRep_eq_pow_smul p (m + b) u hu x
    refine ⟨y, ?_⟩
    rw [hsm]
    exact hy)
  refine ⟨(t' : Module.End ℤ_[2] (TateModule 2 (JZero p))), t'.2, ?_⟩
  have := congrArg Subtype.val ht'
  simpa using this

end hecke

end ModularCurve.Sat

noncomputable section

namespace ModularCurve
p2m_export "ModularCurve" "heckeModuleBar heckeModuleBar_smul_def JZero HeckeAlg tateHeckeRep coe_tateHeckeRep_apply_apply moduleFinite_padicInt_tateModule_jZero exists_tateModule_inertia_fixed_linearIndependent_heckeLatticeAlgebra_orbit ker_heckeEvalForms_latticeRestrict_eq_ker_heckeEvalBar heckeOperatorsCommuteBar smul_eq_self_of_mem_inertiaSubgroupIn_of_nsmul_eq_zero_of_not_dvd"
namespace Sat
p2m_open "ModularCurve"

set_option maxHeartbeats 16000000
set_option synthInstance.maxHeartbeats 3200000

theorem exists_rhoL (p : ℕ) [Fact p.Prime] :
    letI := heckeModuleBar p
    ∃ ρL : ↥(heckeLatticeAlgebra p ∅) →+* Module.End ℤ_[2] (TateModule 2 (JZero p)),
      ∀ t : HeckeAlg, ρL (((latticeRestrictHom p ∅).toRingHom.comp (heckeEvalForms p 2)) t) =
        tateHeckeRep 2 (JZero p) t := by
  letI := heckeModuleBar p
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  set e : HeckeAlg →+* ↥(heckeLatticeAlgebra p ∅) :=
    (latticeRestrictHom p ∅).toRingHom.comp (heckeEvalForms p 2) with he
  have hsurj : Function.Surjective e := by
    rw [he, RingHom.coe_comp]
    exact (latticeRestrictHom_surjective p ∅).comp
      (RingHom.range_eq_top.mp (heckeEvalForms_range_eq_top p 2))
  have h := heckeOperatorsCommuteBar p
  have hker : RingHom.ker e ≤ RingHom.ker (tateHeckeRep 2 (JZero p)) := by
    intro t ht
    rw [he, ker_heckeEvalForms_latticeRestrict_eq_ker_heckeEvalBar p h, RingHom.mem_ker] at ht
    rw [RingHom.mem_ker]
    refine LinearMap.ext fun x => Subtype.ext (funext fun n => ?_)
    rw [coe_tateHeckeRep_apply_apply, heckeModuleBar_smul_def h, ht]
    rfl
  refine ⟨(e.liftOfRightInverse (Function.surjInv hsurj) (Function.rightInverse_surjInv hsurj))
    ⟨tateHeckeRep 2 (JZero p), hker⟩, fun t => ?_⟩
  exact RingHom.liftOfRightInverse_comp_apply e _ _ ⟨_, hker⟩ t

theorem exists_prime_ne (p : ℕ) : ∃ ℓ : ℕ, ℓ.Prime ∧ ℓ ≠ 2 ∧ ℓ ≠ p := by
  by_cases hp : p = 3
  · exact ⟨5, by norm_num, by norm_num, by omega⟩
  · exact ⟨3, Nat.prime_three, by norm_num, fun h => hp h.symm⟩

theorem tateModule_rep_eq_one_of_mem_inertiaSubgroupIn (p : ℕ) [Fact p.Prime] {ℓ : ℕ} [Fact ℓ.Prime]
    (hℓ2 : ℓ ≠ 2) (hℓp : ℓ ≠ p) (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime ℓ)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hσ : σ ∈ A.inertiaSubgroupIn ℚ) :
    TateModule.rep 2 (JZero p) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) σ = 1 := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  refine TateModule.rep_eq_one_of_forall_torsionBy σ fun n m hm => ?_
  have hℓN : ¬ ℓ ∣ p := fun h =>
    hℓp ((Nat.prime_dvd_prime_iff_eq Fact.out Fact.out).mp h)
  have hℓm : ¬ ℓ ∣ 2 ^ n := fun h =>
    hℓ2 ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).mp ((Fact.out : ℓ.Prime).dvd_of_dvd_pow h))
  have hz : (2 ^ n) • m = 0 := by
    have h1 : (((2 ^ n : ℕ) : ℤ)) • m = 0 := (Submodule.mem_torsionBy_iff _ _).mp hm
    rw [natCast_zsmul] at h1
    exact h1
  exact smul_eq_self_of_mem_inertiaSubgroupIn_of_nsmul_eq_zero_of_not_dvd p hℓN A hA (2 ^ n) hℓm m hz σ hσ

theorem exists_linearIndependent_orbit (p : ℕ) [Fact p.Prime]
    (ρL : ↥(heckeLatticeAlgebra p ∅) →+* Module.End ℤ_[2] (TateModule 2 (JZero p)))
    (hρL : letI := heckeModuleBar p
      ∀ t : HeckeAlg, ρL (((latticeRestrictHom p ∅).toRingHom.comp (heckeEvalForms p 2)) t) =
        tateHeckeRep 2 (JZero p) t) :
    ∃ v : TateModule 2 (JZero p),
      LinearIndependent ℤ_[2] (fun i => ρL (Module.Free.chooseBasis ℤ ↥(heckeLatticeAlgebra p ∅) i) v) := by
  obtain ⟨ℓ, hℓ, hℓ2, hℓp⟩ := exists_prime_ne p
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  obtain ⟨A, hA⟩ := ValuationSubring.exists_liesOverPrime_algebraicClosure_rat ⟨ℓ, hℓ⟩
  have hN : ∀ σ ∈ A.inertiaSubgroupIn ℚ, ∀ τ ∈ A.inertiaSubgroupIn ℚ,
      (TateModule.rep 2 (JZero p) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) σ - 1) *
        (TateModule.rep 2 (JZero p) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) τ - 1) = 0 := by
    intro σ hσ τ _
    rw [tateModule_rep_eq_one_of_mem_inertiaSubgroupIn p hℓ2 hℓp A hA σ hσ, sub_self, zero_mul]
  obtain ⟨v, -, hv⟩ :=
    exists_tateModule_inertia_fixed_linearIndependent_heckeLatticeAlgebra_orbit p 2 A hN ρL hρL
  exact ⟨v, hv⟩

theorem descent_core (p : ℕ) [Fact p.Prime]
    (ρL : ↥(heckeLatticeAlgebra p ∅) →+* Module.End ℤ_[2] (TateModule 2 (JZero p)))
    {ι : Type} [Fintype ι] (b : Module.Basis ι ℤ ↥(heckeLatticeAlgebra p ∅))
    (v : TateModule 2 (JZero p)) (hv : LinearIndependent ℤ_[2] (fun i => ρL (b i) v))
    (x : ↥(heckeLatticeAlgebra p ∅)) (m : ℕ) (c : ι → ℤ_[2])
    (hx : ρL x v = ∑ i, ((((2 : ℕ) : ℤ_[2]) ^ m) * c i) • ρL (b i) v) :
    x ∈ Ideal.span {((2 : ℕ) : ↥(heckeLatticeAlgebra p ∅)) ^ m} := by
  classical
  have hxrepr : x = ∑ i, (b.repr x i) • b i := (b.sum_repr x).symm
  have hL : ρL x v = ∑ i, ((b.repr x i : ℤ) : ℤ_[2]) • ρL (b i) v := by
    have e1 : ρL x = ∑ i, (b.repr x i : ℤ) • ρL (b i) := by
      conv_lhs => rw [hxrepr]
      rw [map_sum ρL]
      exact Finset.sum_congr rfl fun i _ => map_zsmul ρL _ _
    rw [e1, LinearMap.sum_apply]
    exact Finset.sum_congr rfl fun i _ => by
      rw [LinearMap.smul_apply]; exact (Int.cast_smul_eq_zsmul ℤ_[2] _ _).symm
  have hcoef : ∀ i, ((b.repr x i : ℤ) : ℤ_[2]) = (((2 : ℕ) : ℤ_[2]) ^ m) * c i := by
    have h0 : ∑ i, (((b.repr x i : ℤ) : ℤ_[2]) - (((2 : ℕ) : ℤ_[2]) ^ m) * c i) • ρL (b i) v = 0 := by
      rw [Finset.sum_congr rfl fun i _ => sub_smul _ _ (ρL (b i) v), Finset.sum_sub_distrib, ← hL, ← hx,
        sub_self]
    have h1 := (Fintype.linearIndependent_iff.mp hv) _ h0
    intro i
    exact sub_eq_zero.mp (h1 i)

  have h2 : ‖((2 : ℕ) : ℤ_[2])‖ = ((2 : ℕ) : ℝ)⁻¹ := PadicInt.norm_p
  have hdvd : ∀ i, ((2 : ℤ) ^ m) ∣ (b.repr x i : ℤ) := by
    intro i
    have hnorm : ‖((b.repr x i : ℤ) : ℤ_[2])‖ ≤ ((2 : ℕ) : ℝ) ^ (-(m : ℤ)) := by
      rw [hcoef i, zpow_neg, zpow_natCast, ← inv_pow, ← h2]
      calc ‖(((2 : ℕ) : ℤ_[2]) ^ m) * c i‖ ≤ ‖((2 : ℕ) : ℤ_[2]) ^ m‖ * ‖c i‖ := norm_mul_le _ _
        _ ≤ ‖((2 : ℕ) : ℤ_[2])‖ ^ m * 1 := by
            gcongr
            · exact norm_pow_le _ _
            · exact PadicInt.norm_le_one _
        _ = ‖((2 : ℕ) : ℤ_[2])‖ ^ m := mul_one _
    have := PadicInt.norm_int_le_pow_iff_dvd.mp hnorm
    exact_mod_cast this
  choose d hd using hdvd
  refine Ideal.mem_span_singleton'.mpr ⟨∑ i, (d i) • b i, ?_⟩
  rw [Finset.sum_mul]
  conv_rhs => rw [hxrepr]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hc2 : b i * ((2 : ℕ) : ↥(heckeLatticeAlgebra p ∅)) ^ m = ((2 : ℕ) : ↥(heckeLatticeAlgebra p ∅)) ^ m * b i :=
    ((Nat.cast_commute 2 (b i)).pow_left m).eq.symm
  rw [hd i, smul_mul_assoc, hc2, ← Nat.cast_pow, ← nsmul_eq_mul, ← natCast_zsmul, smul_smul]
  congr 1
  push_cast
  ring

theorem rhoL_mem_span (p : ℕ) [Fact p.Prime]
    (ρL : ↥(heckeLatticeAlgebra p ∅) →+* Module.End ℤ_[2] (TateModule 2 (JZero p)))
    {ι : Type} [Fintype ι] (b : Module.Basis ι ℤ ↥(heckeLatticeAlgebra p ∅))
    (x : ↥(heckeLatticeAlgebra p ∅)) :
    ρL x ∈ Submodule.span ℤ_[2] (Set.range fun i => ρL (b i)) := by
  have hx : x = ∑ i, (b.repr x i) • b i := (b.sum_repr x).symm
  rw [hx, map_sum ρL]
  refine Submodule.sum_mem _ fun i _ => ?_
  rw [map_zsmul]
  exact Submodule.smul_of_tower_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

theorem descent (p : ℕ) [Fact p.Prime]
    (ρL : ↥(heckeLatticeAlgebra p ∅) →+* Module.End ℤ_[2] (TateModule 2 (JZero p)))
    (hρL : letI := heckeModuleBar p
      ∀ t : HeckeAlg, ρL (((latticeRestrictHom p ∅).toRingHom.comp (heckeEvalForms p 2)) t) =
        tateHeckeRep 2 (JZero p) t)
    (x : ↥(heckeLatticeAlgebra p ∅)) (m : ℕ) (α : Module.End ℤ_[2] (TateModule 2 (JZero p)))
    (hα : letI := heckeModuleBar p
      α ∈ Algebra.adjoin ℤ_[2] (Set.range fun t : HeckeAlg => tateHeckeRep 2 (JZero p) t))
    (hx : ρL x = ((2 : ℕ) : ℤ_[2]) ^ m • α) :
    x ∈ Ideal.span {((2 : ℕ) : ↥(heckeLatticeAlgebra p ∅)) ^ m} := by
  classical
  letI := heckeModuleBar p
  let b := Module.Free.chooseBasis ℤ ↥(heckeLatticeAlgebra p ∅)

  have hrange : ∀ t : HeckeAlg,
      tateHeckeRep 2 (JZero p) t ∈ Submodule.span ℤ_[2] (Set.range fun i => ρL (b i)) := fun t => by
    rw [← hρL t]; exact rhoL_mem_span p ρL b _
  have hcl : (Submonoid.closure (Set.range fun t : HeckeAlg => tateHeckeRep 2 (JZero p) t) :
      Set (Module.End ℤ_[2] (TateModule 2 (JZero p)))) ⊆
        Submodule.span ℤ_[2] (Set.range fun i => ρL (b i)) := by
    intro y hy
    have hle : Submonoid.closure (Set.range fun t : HeckeAlg => tateHeckeRep 2 (JZero p) t) ≤
        (tateHeckeRep 2 (JZero p)).rangeS.toSubmonoid :=
      Submonoid.closure_le.mpr fun z hz => hz
    obtain ⟨t, rfl⟩ := (RingHom.mem_rangeS.mp (hle hy) : ∃ t, tateHeckeRep 2 (JZero p) t = y)
    exact hrange t
  have hα' : α ∈ Subalgebra.toSubmodule
      (Algebra.adjoin ℤ_[2] (Set.range fun t : HeckeAlg => tateHeckeRep 2 (JZero p) t)) := hα
  rw [Algebra.adjoin_eq_span] at hα'
  have hαS : α ∈ Submodule.span ℤ_[2] (Set.range fun i => ρL (b i)) := (Submodule.span_le.mpr hcl) hα'
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ_[2]).mp hαS

  obtain ⟨v, hv⟩ := exists_linearIndependent_orbit p ρL hρL
  refine descent_core p ρL b v hv x m c ?_
  rw [hx, ← hc, LinearMap.smul_apply, LinearMap.sum_apply, Finset.smul_sum]
  exact Finset.sum_congr rfl fun i _ => by rw [LinearMap.smul_apply, smul_smul]

end ModularCurve.Sat

end

namespace ModularCurve
p2m_export "ModularCurve" "heckeModuleBar heckeModuleBar_smul_def JZero HeckeAlg tateHeckeRep coe_tateHeckeRep_apply_apply moduleFinite_padicInt_tateModule_jZero exists_tateModule_inertia_fixed_linearIndependent_heckeLatticeAlgebra_orbit ker_heckeEvalForms_latticeRestrict_eq_ker_heckeEvalBar heckeOperatorsCommuteBar smul_eq_self_of_mem_inertiaSubgroupIn_of_nsmul_eq_zero_of_not_dvd"
namespace Sat
p2m_open "ModularCurve"

theorem main (p : ℕ) [Fact p.Prime] :
    letI := heckeModuleBar p
    ∃ d : ℕ, ∀ m : ℕ, ∀ u : HeckeAlg,
      (∀ y : JZero p, 2 ^ (m + d) • y = 0 → u • y = 0) →
        ((latticeRestrictHom p ∅).toRingHom.comp (heckeEvalForms p 2)) u ∈
          Ideal.span {((2 : ℕ) : ↥(heckeLatticeAlgebra p ∅)) ^ m} := by
  letI := heckeModuleBar p
  obtain ⟨ρL, hρL⟩ := exists_rhoL p
  obtain ⟨b, hb⟩ := exists_bound_tateHeckeRep_eq_pow_smul p
  refine ⟨b, fun m u hu => ?_⟩
  obtain ⟨α, hα, hu'⟩ := hb m u hu
  exact descent p ρL hρL _ m α hα (by rw [hρL]; exact hu')

end ModularCurve.Sat

theorem solution (p : ℕ) [Fact p.Prime] :
    letI := heckeModuleBar p
    ∃ d : ℕ, ∀ m : ℕ, ∀ u : HeckeAlg,
      (∀ y : JZero p, 2 ^ (m + d) • y = 0 → u • y = 0) →
        ((latticeRestrictHom p ∅).toRingHom.comp (heckeEvalForms p 2)) u ∈
          Ideal.span {((2 : ℕ) : ↥(heckeLatticeAlgebra p ∅)) ^ m} :=
  ModularCurve.Sat.main p

end S_ModularCurve_exists_latticeRestrict_heckeEvalForms_mem_span_two_pow_of_forall_smul_eq_zero
end P2MW
export P2MW.S_ModularCurve_exists_latticeRestrict_heckeEvalForms_mem_span_two_pow_of_forall_smul_eq_zero (solution)
