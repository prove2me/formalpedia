-- Prove2me | solution 1 for ModularCurve.smul_smul_sub_smul_add_eq_zero_of_mem_torsionBySet_eisensteinMaximalIdeal
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/4e41380a-d6bd-53a6-94f6-cf9c43df77c3

import Mathlib
import Definitions.Def_ModularCurve_HeckeModule
import Definitions.Def_ModularCurve_EisensteinIdeal
import Definitions.Def_HeckeGalois_EichlerShimura
import Definitions.Def_GaloisRep_FrobeniusPowerDense
import Definitions.Def_EllipticCurve_FrobeniusTrace
import Theorems.Thm_ModularCurve_frobeniusQuadratic_JZero
import Theorems.Thm_ModularCurve_cayleyHamilton_forall_of_frobeniusQuadratic_of_dense
import Theorems.Thm_Subgroup_exists_prime_isFrobeniusAt_conj_pow_mem_of_isOpen
import Theorems.Thm_ValuationSubring_IsFrobeniusAt_apply_eq_pow_of_pow_eq_one
import Theorems.Thm_ModularCurve_JZero_isOpen_stabilizer
import Theorems.Thm_ModularCurve_smulCommClass_JZero_of_heckeOperatorsCommuteBar
import Theorems.Thm_ModularCurve_finite_torsionBySet_eisensteinMaximalIdeal_pow
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_smul_smul_sub_smul_add_eq_zero_of_mem_torsionBySet_eisensteinMaximalIdeal
p2m_attr_erase "instance" "AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois CuspForm.heckeAlgebra.instCommRing CuspForm.heckeAlgebra.instIsMulCommutative CuspForm.heckeAlgebra.instIsAddTorsionFree WeierstrassCurve.Affine.Point.instFinite ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver"
p2m_attr_erase "instance" "AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.CuspSpace.instNonempty ModularCurve.CuspSpace.instSubsingletonOfOne ModularCurve.CuspSpace.instFinite ModularCurve.instAlgebraIntermediateFieldLaurent ModularCurve.instIsScalarTowerKaehlerIntermediateFieldLaurent ModularCurve.instIsScalarTowerIntermediateFieldLaurent ModularCurve.instModuleKaehlerIntermediateFieldLaurent ModularCurve.Gamma0Pair.isElliptic ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.B3.instIsElliptic_goodModel ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar ModularCurve.instIsScalarTowerJAdjoin FLT.Gamma0FundamentalSet.instContinuousConstSMulSpecialLinearGroupFinOfNatNatIntUpperHalfPlane_definitions FLT.HyperbolicMeasure.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatIntUpperHalfPlaneVolume_definitions FLT.HyperbolicMeasure.instIsOpenPosMeasureUpperHalfPlaneVolume_definitions FLT.L2ProductionInstance.isFiniteMeasure_gamma0 FLT.L2ProductionInstance.countable_SL2Z FLT.L2ProductionInstance.countable_quotient FLT.L2ProductionInstance.nontrivial_gamma0L2 HeckeEis.instModuleCoeffH1par HeckeEis.instAddCommGroupCoeffH1par HeckeEis.instFiniteIndexHeckeUpper WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation"
p2m_attr_erase "instance" "ModularCurve.ElevenA1.instDecidableNonsingular FrobeniusDensity.isMaximal_ratPrimeIdeal FrobeniusDensity.liesOver_ratBelow"
p2m_attr_erase "simp" "ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong ModularCurve.qExpandAlgHomC_apply ModularCurve.jqNModC_one ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero"
p2m_attr_erase "simp" "ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_cuspidalDivisor₀ ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div"
p2m_attr_erase "simp" "ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.dualHeckeRep_apply_apply ModularCurve.coe_segmentPath ModularCurve.cuspHeckeAeval_heckeGen ModularCurve.coe_periodLatticeRestrict_apply CuspForm.heckeAlgebra.coe_U CuspForm.heckeAlgebra.coe_T ModularForm.coe_heckeTLin_apply CuspForm.coe_heckeULin_apply CuspForm.coe_heckeTLin_apply ModularForm.coe_heckeULin_apply ModularCurve.ComplexPlaceDictionary.mk.injEq ModularCurve.ComplexPlaceDictionary.mk.sizeOf_spec ModularCurve.Period.IsEquivariantPrimitive.periodHom_apply ModularCurve.Period.IsEquivariantPrimitive.period_one PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem"
p2m_attr_erase "simp" "PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ ModularCurve.ProjectiveLine.map_mk AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule ModularCurve.cuspCount_one"
p2m_attr_erase "simp" "ModularCurve.CuspSpace.cuspDenomAux_infty ModularCurve.CuspSpace.cuspDenomAux_coe ModularCurve.CuspSpace.cuspDenom_mk_zero ModularCurve.CuspSpace.cuspDenom_mk_infty ModularCurve.mapGL_apply_coe ModularCurve.ratPoint_one_zero ModularCurve.ratPoint_zero_right ModularCurve.CuspSpace.fromCoset_mk ModularCurve.CuspSpace.cuspDenom_mk ModularCurve.ratPoint_zero_one ModularCurve.qEulerFun_coeff ModularCurve.diffQExp_D ModularCurve.qEulerOn_apply ModularCurve.qEuler_coeff ModularCurve.gamma0PairMap_gen ModularCurve.moduliPointMapRingHom_mk ModularCurve.Gamma0Pair.mk.injEq ModularCurve.ModuliPoint.j_mk ModularCurve.Gamma0Pair.mk.sizeOf_spec ModularCurve.gamma0PairMap_toCurve WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero WeierstrassCurve.ratPointHom_apply WeierstrassCurve.ratPointMap_zero ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ WeierstrassCurve.veluX_empty WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty"
p2m_attr_erase "simp" "WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec"
p2m_attr_erase "simp" "EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃"
p2m_attr_erase "simp" "WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply HahnSeries.ramScale_apply WeierstrassCurve.veluPointMap2_zero FLT.TruncatedDomainPartition.unipotentDiagonalSum_zero HeckeEis.coeffCoboundaryMap_apply HeckeEis.heckeConjMat_apply_one_one HeckeEis.coe_heckeConjSL HeckeEis.mem_heckeUpperSL HeckeEis.resHom_apply HeckeEis.heckeConjMat_apply_zero_one HeckeEis.coe_transferAux HeckeEis.coe_heckeConj HeckeEis.alphaMat_apply_one_one HeckeEis.heckeConjMat_apply_one_zero HeckeEis.alphaMat_apply_zero_one HeckeEis.pullbackHom_apply HeckeEis.alphaMat_apply_one_zero HeckeEis.alphaMat_apply_zero_zero HeckeEis.heckeConjMat_apply_zero_zero"
p2m_attr_erase "simp" "AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ"
p2m_attr_erase "simp" "TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec"

set_option autoImplicit false

open ModularCurve

noncomputable section

namespace P2mWs11Esq

attribute [local instance] ModularCurve.heckeModuleBar

local notation "Gal" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)

theorem zmod_natCast_eq_of_pow_eq_pow {q : ℕ} (hq : q.Prime) {ζ : AlgebraicClosure ℚ}
    (hζ : IsPrimitiveRoot ζ q) {a b : ℕ} (h : ζ ^ a = ζ ^ b) : (a : ZMod q) = (b : ZMod q) := by
  have hζ0 : ζ ≠ 0 := hζ.ne_zero hq.ne_zero
  have hdvd : (q : ℤ) ∣ (b : ℤ) - a := by
    rw [← hζ.zpow_eq_one_iff_dvd, zpow_sub₀ hζ0, zpow_natCast, zpow_natCast, h,
      div_self (pow_ne_zero _ hζ0)]
  have := (ZMod.intCast_eq_intCast_iff_dvd_sub (a : ℤ) (b : ℤ) q).mpr hdvd
  simpa using this

section Residue

variable (p q : ℕ) [hq : Fact q.Prime]

theorem natCast_mem_iff (n : ℕ) : (n : HeckeAlg) ∈ eisensteinMaximalIdeal p q ↔ q ∣ n := by
  rw [mem_eisensteinMaximalIdeal_iff, map_natCast, Int.natCast_dvd_natCast]

scoped instance charP_quotient : CharP (HeckeAlg ⧸ eisensteinMaximalIdeal p q) q := by
  refine ⟨fun n => ?_⟩
  rw [← map_natCast (Ideal.Quotient.mk (eisensteinMaximalIdeal p q)), Ideal.Quotient.eq_zero_iff_mem,
    natCast_mem_iff]

def ψ : ZMod q →+* HeckeAlg ⧸ eisensteinMaximalIdeal p q :=
  ZMod.castHom (dvd_refl q) (HeckeAlg ⧸ eisensteinMaximalIdeal p q)

def rho (χ : Gal →* (ZMod q)ˣ) : Gal →* Matrix (Fin 2) (Fin 2) (HeckeAlg ⧸ eisensteinMaximalIdeal p q) where
  toFun σ := Matrix.diagonal ![1, ψ p q (χ σ : ZMod q)]
  map_one' := by
    rw [map_one, Units.val_one, map_one, ← Matrix.diagonal_one]
    congr 1
    ext i
    fin_cases i <;> rfl
  map_mul' σ τ := by
    rw [Matrix.diagonal_mul_diagonal, map_mul, Units.val_mul, map_mul]
    congr 1
    ext i
    fin_cases i
    · simp
    · simp

theorem rho_apply (χ : Gal →* (ZMod q)ˣ) (σ : Gal) :
    rho p q χ σ = Matrix.diagonal ![1, ψ p q (χ σ : ZMod q)] := rfl

theorem trace_rho (χ : Gal →* (ZMod q)ˣ) (σ : Gal) :
    (rho p q χ σ).trace = 1 + ψ p q (χ σ : ZMod q) := by
  rw [rho_apply, Matrix.trace_diagonal, Fin.sum_univ_two]
  rfl

theorem det_rho (χ : Gal →* (ZMod q)ˣ) (σ : Gal) :
    (rho p q χ σ).det = ψ p q (χ σ : ZMod q) := by
  rw [rho_apply, Matrix.det_diagonal, Fin.prod_univ_two]
  show (1 : HeckeAlg ⧸ eisensteinMaximalIdeal p q) * _ = _
  rw [one_mul]
  rfl

theorem mk_heckeGen_eq {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓp : ¬ ℓ ∣ p) :
    Ideal.Quotient.mk (eisensteinMaximalIdeal p q) (heckeGen ⟨ℓ, hℓ⟩) =
      1 + ((ℓ : ℕ) : HeckeAlg ⧸ eisensteinMaximalIdeal p q) := by
  have hmem : heckeGen ⟨ℓ, hℓ⟩ - (1 + (ℓ : HeckeAlg)) ∈ eisensteinMaximalIdeal p q := by
    rw [mem_eisensteinMaximalIdeal_iff, map_sub, eisensteinEval_heckeGen, map_add, map_one, map_natCast,
      eisensteinSystem_of_not_dvd (ℓ := ⟨ℓ, hℓ⟩) hℓp]
    simp
  rw [← sub_eq_zero, ← map_natCast (Ideal.Quotient.mk (eisensteinMaximalIdeal p q)), ← map_one
    (Ideal.Quotient.mk (eisensteinMaximalIdeal p q)), ← map_add, ← map_sub, Ideal.Quotient.eq_zero_iff_mem]
  exact hmem

end Residue

theorem main (p : ℕ) [Fact p.Prime] (hcomm : HeckeOperatorsCommuteBar p) (q : ℕ) (hq : q.Prime)
    (σ : Gal) (ζ : AlgebraicClosure ℚ) (hζ : IsPrimitiveRoot ζ q) (a : ℕ) (ha : σ ζ = ζ ^ a)
    (x : JZero p)
    (hx : x ∈ Submodule.torsionBySet HeckeAlg (JZero p) (↑(eisensteinMaximalIdeal p q) : Set HeckeAlg)) :
    σ • σ • x - (1 + a) • (σ • x) + a • x = 0 := by
  classical
  haveI : Fact q.Prime := ⟨hq⟩
  haveI : NeZero q := ⟨hq.ne_zero⟩
  haveI : SMulCommClass Gal HeckeAlg (JZero p) :=
    ModularCurve.smulCommClass_JZero_of_heckeOperatorsCommuteBar p hcomm

  let χ : Gal →* (ZMod q)ˣ := hζ.autToPow ℚ
  have hχ : ∀ τ : Gal, τ ζ = ζ ^ (χ τ : ZMod q).val := fun τ => (hζ.autToPow_spec ℚ τ).symm
  have hχ_eq : ∀ (τ : Gal) (b : ℕ), τ ζ = ζ ^ b → (χ τ : ZMod q) = (b : ZMod q) := by
    intro τ b hb
    have h := zmod_natCast_eq_of_pow_eq_pow hq hζ ((hχ τ).symm.trans hb)
    rwa [ZMod.natCast_zmod_val] at h

  let ρ := rho p q χ

  have hχker : IsOpen (χ.ker : Set Gal) := by
    haveI : FiniteDimensional ℚ (IntermediateField.adjoin ℚ {ζ}) :=
      IntermediateField.adjoin.finiteDimensional
        (IsIntegral.of_pow hq.pos (by rw [hζ.pow_eq_one]; exact isIntegral_one))
    apply Subgroup.isOpen_mono _ (IntermediateField.fixingSubgroup_isOpen (IntermediateField.adjoin ℚ {ζ}))
    intro τ hτ
    rw [IntermediateField.mem_fixingSubgroup_iff] at hτ
    have hτζ : τ ζ = ζ := hτ ζ (IntermediateField.mem_adjoin_simple_self ℚ ζ)
    rw [MonoidHom.mem_ker]
    have h1 : (χ τ : ZMod q) = ((1 : ℕ) : ZMod q) := hχ_eq τ 1 (by rw [pow_one]; exact hτζ)
    rw [Nat.cast_one] at h1
    exact Units.ext h1
  have hρker : IsOpen (ρ.ker : Set Gal) := by
    apply Subgroup.isOpen_mono _ hχker
    intro τ hτ
    rw [MonoidHom.mem_ker] at hτ ⊢
    show rho p q χ τ = 1
    rw [← (rho p q χ).map_one, rho_apply, rho_apply, hτ, map_one χ]

  haveI hfin : Finite ↥(Submodule.torsionBySet HeckeAlg (JZero p)
      (↑(eisensteinMaximalIdeal p q) : Set HeckeAlg)) := by
    have := ModularCurve.finite_torsionBySet_eisensteinMaximalIdeal_pow p q hq 1
    rwa [pow_one] at this
  have hfix : IsOpen (fixingSubgroup Gal
      (heckeTorsion (JZero p) (eisensteinMaximalIdeal p q) : Set (JZero p)) : Set Gal) := by
    have hset : (fixingSubgroup Gal
        (heckeTorsion (JZero p) (eisensteinMaximalIdeal p q) : Set (JZero p)) : Set Gal) =
        ⋂ y ∈ (heckeTorsion (JZero p) (eisensteinMaximalIdeal p q) : Set (JZero p)),
          (MulAction.stabilizer Gal y : Set Gal) := by
      ext τ
      simp only [SetLike.mem_coe, mem_fixingSubgroup_iff, Set.mem_iInter, MulAction.mem_stabilizer_iff]
    rw [hset]
    apply Set.Finite.isOpen_biInter (Set.toFinite _)
    intro y _
    exact ModularCurve.JZero.isOpen_stabilizer p y
  have hH : IsOpen ((ρ.ker ⊓ fixingSubgroup Gal
      (heckeTorsion (JZero p) (eisensteinMaximalIdeal p q) : Set (JZero p)) : Subgroup Gal) : Set Gal) := by
    rw [Subgroup.coe_inf]
    exact hρker.inter hfix

  let S : Finset ℕ := {p, q}
  have hS : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∉ S → ¬ ℓ ∣ p * q := by
    intro ℓ hℓ hℓS hdvd
    apply hℓS
    rcases (Nat.Prime.dvd_mul hℓ).mp hdvd with h | h
    · rw [(Nat.prime_dvd_prime_iff_eq hℓ (Fact.out : p.Prime)).mp h]
      exact Finset.mem_insert_self _ _
    · rw [(Nat.prime_dvd_prime_iff_eq hℓ hq).mp h]
      exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  have hdense : FrobeniusPowerDense S (ρ.ker ⊓ fixingSubgroup Gal
      (heckeTorsion (JZero p) (eisensteinMaximalIdeal p q) : Set (JZero p))) := by
    intro τ
    obtain ⟨ℓ, A, τ', g, n, hℓ, hℓM, hA, hτ', hmem⟩ :=
      Subgroup.exists_prime_isFrobeniusAt_conj_pow_mem_of_isOpen _ hH τ
        (M := p * q) (Nat.mul_pos (Fact.out : p.Prime).pos hq.pos)
    refine ⟨ℓ, A, τ', g, n, hℓ, ?_, hA, hτ', hmem⟩
    intro hℓS
    apply hℓM
    rw [Finset.mem_insert, Finset.mem_singleton] at hℓS
    rcases hℓS with rfl | rfl
    · exact dvd_mul_right _ _
    · exact dvd_mul_left _ _

  have hatt : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime), ℓ ∉ S → ∀ (A : ValuationSubring (AlgebraicClosure ℚ)),
      A.LiesOverPrime ℓ → ∀ (τ : Gal), A.IsFrobeniusAt τ ℓ →
        Ideal.Quotient.mk (eisensteinMaximalIdeal p q) (heckeGen ⟨ℓ, hℓ⟩) = (ρ τ).trace ∧
          Ideal.Quotient.mk (eisensteinMaximalIdeal p q) ((ℓ : HeckeAlg)) = (ρ τ).det := by
    intro ℓ hℓ hℓS A hA τ hτ
    rw [Finset.mem_insert, Finset.mem_singleton, not_or] at hℓS
    have hℓp : ¬ ℓ ∣ p := fun h => hℓS.1 ((Nat.prime_dvd_prime_iff_eq hℓ (Fact.out : p.Prime)).mp h)
    have hcop : q.Coprime ℓ := (Nat.coprime_primes hq hℓ).mpr (Ne.symm hℓS.2)
    have hτζ : τ ζ = ζ ^ ℓ :=
      ValuationSubring.IsFrobeniusAt.apply_eq_pow_of_pow_eq_one A τ ℓ q hA hτ hcop ζ hζ.pow_eq_one
    have hχτ : (χ τ : ZMod q) = (ℓ : ZMod q) := hχ_eq τ ℓ hτζ
    constructor
    · show _ = (rho p q χ τ).trace
      rw [trace_rho, hχτ, map_natCast, mk_heckeGen_eq p q hℓ hℓp]
    · show _ = (rho p q χ τ).det
      rw [det_rho, hχτ, map_natCast, map_natCast]

  have hES : FrobeniusQuadratic (K := ℚ) (L := AlgebraicClosure ℚ) p q (JZero p) :=
    ModularCurve.frobeniusQuadratic_JZero p q hcomm inferInstance

  have hCH := ModularCurve.cayleyHamilton_forall_of_frobeniusQuadratic_of_dense p q
    (eisensteinMaximalIdeal p q) (natCast_mem_eisensteinMaximalIdeal p q) ρ hES hS hatt hdense σ x hx
    ((1 + a : ℕ) : HeckeAlg) (a : HeckeAlg)
    (by
      show _ = (rho p q χ σ).trace
      rw [trace_rho, hχ_eq σ a ha, map_natCast, map_natCast, Nat.cast_add, Nat.cast_one])
    (by
      show _ = (rho p q χ σ).det
      rw [det_rho, hχ_eq σ a ha, map_natCast, map_natCast])
  rw [Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul] at hCH
  exact hCH

end P2mWs11Esq
p2m_reactivate "P2MW.S_ModularCurve_smul_smul_sub_smul_add_eq_zero_of_mem_torsionBySet_eisensteinMaximalIdeal.P2mWs11Esq"

end
p2m_reactivate "P2MW.S_ModularCurve_smul_smul_sub_smul_add_eq_zero_of_mem_torsionBySet_eisensteinMaximalIdeal.P2mWs11Esq"

theorem solution
    (p : ℕ) [Fact p.Prime] (hcomm : HeckeOperatorsCommuteBar p) (q : ℕ) (hq : q.Prime)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (ζ : AlgebraicClosure ℚ)
    (hζ : IsPrimitiveRoot ζ q) (a : ℕ) (ha : σ ζ = ζ ^ a) (x : JZero p)
    (hx : letI := heckeModuleBar p
      x ∈ Submodule.torsionBySet HeckeAlg (JZero p)
        (↑(eisensteinMaximalIdeal p q) : Set HeckeAlg)) :
    σ • σ • x - (1 + a) • (σ • x) + a • x = 0 :=
  P2mWs11Esq.main p hcomm q hq σ ζ hζ a ha x hx

end S_ModularCurve_smul_smul_sub_smul_add_eq_zero_of_mem_torsionBySet_eisensteinMaximalIdeal
end P2MW
export P2MW.S_ModularCurve_smul_smul_sub_smul_add_eq_zero_of_mem_torsionBySet_eisensteinMaximalIdeal (solution)
