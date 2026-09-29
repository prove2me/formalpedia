-- Prove2me | solution 1 for ModularCurve.natCard_heckeTorsion_span_sup_eq_sq_natCard_heckeLatticeAlgebra_quotient
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/fd3605d8-c6b7-59e7-a231-0ad76e92c54c

import Definitions.Def_ModularCurve_JZeroNeronTorsionSheafV4
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_CuspForm_HeckeLocal
import Definitions.Def_CuspForm_HeckeEvalForms
import Definitions.Def_ModularCurve_JZeroTateModule
import Theorems.Thm_ModularCurve_heckeOperatorsCommuteBar
import Theorems.Thm_ModularCurve_ker_heckeEvalForms_latticeRestrict_eq_ker_heckeEvalBar
import Theorems.Thm_ModularCurve_heckeInputsAll
import Theorems.Thm_ModularCurve_exists_heckeEquivariant_linearEquiv_rationalTateModule_jZero_fun_two
import Theorems.Thm_ModularCurve_linearIndependent_rationalHeckeRep_of_linearIndependent
import Theorems.Thm_ModularCurve_moduleFinite_padicInt_tateModule_jZero
import Theorems.Thm_ModularCurve_JZero_divisible
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_natCard_heckeTorsion_span_sup_eq_sq_natCard_heckeLatticeAlgebra_quotient
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.CuspSpace.instNonempty ModularCurve.CuspSpace.instSubsingletonOfOne"
p2m_attr_erase "instance" "ModularCurve.CuspSpace.instFinite ModularCurve.instAlgebraIntermediateFieldLaurent ModularCurve.instIsScalarTowerKaehlerIntermediateFieldLaurent ModularCurve.instIsScalarTowerIntermediateFieldLaurent ModularCurve.instModuleKaehlerIntermediateFieldLaurent ModularCurve.Gamma0Pair.isElliptic ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.B3.instIsElliptic_goodModel ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar ModularCurve.instIsScalarTowerJAdjoin FLT.Gamma0FundamentalSet.instContinuousConstSMulSpecialLinearGroupFinOfNatNatIntUpperHalfPlane_definitions FLT.HyperbolicMeasure.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatIntUpperHalfPlaneVolume_definitions FLT.HyperbolicMeasure.instIsOpenPosMeasureUpperHalfPlaneVolume_definitions FLT.L2ProductionInstance.isFiniteMeasure_gamma0 FLT.L2ProductionInstance.countable_SL2Z FLT.L2ProductionInstance.countable_quotient FLT.L2ProductionInstance.nontrivial_gamma0L2 HeckeEis.instModuleCoeffH1par HeckeEis.instAddCommGroupCoeffH1par HeckeEis.instFiniteIndexHeckeUpper ModularCurve.Period.parabolicHoms_int_moduleFinite ModularCurve.Period.instGroupFG_SL2Z ModularCurve.Period.instIsNoetherian_addHom_int ModularCurve.Period.instGroupFG_Gamma0 AlgebraicCurve.CellDissection.fintypeV AlgebraicCurve.CellDissection.fintypeC AlgebraicCurve.CellDissection.fintypeE AlgebraicCurve.CellDissection.decEqV"
p2m_attr_erase "instance" "AlgebraicCurve.CellDissection.decEqC AlgebraicCurve.CellDissection.decEqE"
p2m_attr_erase "simp" "ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff"
p2m_attr_erase "simp" "ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.dualHeckeRep_apply_apply ModularCurve.coe_segmentPath ModularCurve.cuspHeckeAeval_heckeGen ModularCurve.coe_periodLatticeRestrict_apply AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularCurve.ComplexPlaceDictionary.mk.injEq ModularCurve.ComplexPlaceDictionary.mk.sizeOf_spec ModularCurve.Period.IsEquivariantPrimitive.periodHom_apply ModularCurve.Period.IsEquivariantPrimitive.period_one"
p2m_attr_erase "simp" "PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ ModularCurve.ProjectiveLine.map_mk AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule ModularCurve.cuspCount_one ModularCurve.CuspSpace.cuspDenomAux_infty ModularCurve.CuspSpace.cuspDenomAux_coe ModularCurve.CuspSpace.cuspDenom_mk_zero ModularCurve.CuspSpace.cuspDenom_mk_infty ModularCurve.mapGL_apply_coe ModularCurve.ratPoint_one_zero ModularCurve.ratPoint_zero_right ModularCurve.CuspSpace.fromCoset_mk ModularCurve.CuspSpace.cuspDenom_mk"
p2m_attr_erase "simp" "ModularCurve.ratPoint_zero_one ModularCurve.qEulerFun_coeff ModularCurve.diffQExp_D ModularCurve.qEulerOn_apply ModularCurve.qEuler_coeff ModularCurve.gamma0PairMap_gen ModularCurve.moduliPointMapRingHom_mk ModularCurve.Gamma0Pair.mk.injEq ModularCurve.ModuliPoint.j_mk ModularCurve.Gamma0Pair.mk.sizeOf_spec ModularCurve.gamma0PairMap_toCurve WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero WeierstrassCurve.ratPointHom_apply WeierstrassCurve.ratPointMap_zero ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ WeierstrassCurve.veluX_empty WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec"
p2m_attr_erase "simp" "WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply"
p2m_attr_erase "simp" "ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply HahnSeries.ramScale_apply WeierstrassCurve.veluPointMap2_zero FLT.TruncatedDomainPartition.unipotentDiagonalSum_zero HeckeEis.coeffCoboundaryMap_apply HeckeEis.heckeConjMat_apply_one_one HeckeEis.coe_heckeConjSL HeckeEis.mem_heckeUpperSL HeckeEis.resHom_apply HeckeEis.heckeConjMat_apply_zero_one HeckeEis.coe_transferAux HeckeEis.coe_heckeConj HeckeEis.alphaMat_apply_one_one HeckeEis.heckeConjMat_apply_one_zero HeckeEis.alphaMat_apply_zero_one HeckeEis.pullbackHom_apply HeckeEis.alphaMat_apply_one_zero HeckeEis.alphaMat_apply_zero_zero HeckeEis.heckeConjMat_apply_zero_zero ModularCurve.Period.jConjMat_apply_zero_one ModularCurve.Period.jConjSL_coe ModularCurve.Period.jConjMat_apply_one_zero ModularCurve.Period.jConjMat_apply_one_one ModularCurve.Period.jConjGamma0_coe ModularCurve.Period.charInvolution_apply ModularCurve.Period.jConjMat_apply_zero_zero PowerSeries.coeff_heckeV PowerSeries.coeff_heckeU"
p2m_attr_erase "simp" "AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap AlgebraicCurve.abelJacobiDiv_single AlgebraicCurve.AnalyticCoord.mk.injEq AlgebraicCurve.Cell.mk.sizeOf_spec AlgebraicCurve.RadialRegion.mk.sizeOf_spec AlgebraicCurve.RadialRegion.mk.injEq AlgebraicCurve.CellDissection.mk.sizeOf_spec AlgebraicCurve.Cell.mk.injEq AlgebraicCurve.CellDissection.mk.injEq AlgebraicCurve.AnalyticCoord.mk.sizeOf_spec"

set_option autoImplicit false

noncomputable section

open ModularCurve CuspForm
open scoped TensorProduct Pointwise

attribute [local instance] ModularCurve.heckeModuleBar

namespace TotN

section Newton

variable {R : Type*} [CommRing R]

private def newton (y : R) : R := 3 * y ^ 2 - 2 * y ^ 3

private theorem newton_defect (y : R) :
    newton y * newton y - newton y = (y * y - y) ^ 2 * (4 * (y * y - y) - 3) := by
  unfold newton; ring

private theorem one_sub_newton (y : R) : 1 - newton y = (1 - y) * (1 + y - 2 * y ^ 2) := by
  unfold newton; ring

private theorem newton_sub (y : R) : newton y - y = (1 - 2 * y) * (y * y - y) := by
  unfold newton; ring

private theorem span_pow_le_span_pow (c : R) {m n : ℕ} (h : m ≤ n) :
    Ideal.span {c ^ n} ≤ Ideal.span {c ^ m} :=
  (Ideal.span_singleton_le_iff_mem _).mpr (Ideal.mem_span_singleton.mpr (pow_dvd_pow c h))

private theorem span_pow_succ_le_span (c : R) (n : ℕ) : Ideal.span {c ^ (n + 1)} ≤ Ideal.span {c} :=
  (Ideal.span_singleton_le_iff_mem _).mpr (Ideal.mem_span_singleton.mpr (dvd_pow_self c n.succ_ne_zero))

private theorem exists_idempotent_of_complete (c : R) (M : Ideal R) (hcM : c ∈ M) (x₀ : R)
    (hu : x₀ * x₀ - x₀ ∈ Ideal.span {c}) (hm : 1 - x₀ ∈ M)
    (hcomplete : ∀ x : ℕ → R, (∀ n, x (n + 1) - x n ∈ Ideal.span {c ^ (n + 1)}) →
      ∃ e : R, ∀ n, e - x n ∈ Ideal.span {c ^ n})
    (hhaus : ∀ y : R, (∀ n, y ∈ Ideal.span {c ^ n}) → y = 0) :
    ∃ e : R, IsIdempotentElem e ∧ 1 - e ∈ M ∧ e - x₀ ∈ Ideal.span {c} := by
  let x : ℕ → R := fun n => newton^[n] x₀
  have hx0 : x 0 = x₀ := rfl
  have hxs : ∀ n, x (n + 1) = newton (x n) := fun n => Function.iterate_succ_apply' newton n x₀
  have hdef : ∀ n, x n * x n - x n ∈ Ideal.span {c ^ (n + 1)} := by
    intro n
    induction n with
    | zero => rwa [hx0, zero_add, pow_one]
    | succ n ih =>
      obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.mp ih
      rw [hxs, newton_defect, ← ha]
      refine Ideal.mem_span_singleton'.mpr ⟨a * a * (4 * (a * c ^ (n + 1)) - 3) * c ^ n, ?_⟩
      ring
  have hone : ∀ n, 1 - x n ∈ M := by
    intro n
    induction n with
    | zero => rwa [hx0]
    | succ n ih => rw [hxs, one_sub_newton]; exact M.mul_mem_right _ ih
  have hstep : ∀ n, x (n + 1) - x n ∈ Ideal.span {c ^ (n + 1)} := by
    intro n
    rw [hxs, newton_sub]
    exact Ideal.mul_mem_left _ _ (hdef n)
  have hstart : ∀ n, x n - x₀ ∈ Ideal.span {c} := by
    intro n
    induction n with
    | zero => rw [hx0, sub_self]; exact Ideal.zero_mem _
    | succ n ih =>
      rw [← sub_add_sub_cancel (x (n + 1)) (x n) x₀]
      exact Ideal.add_mem _ (span_pow_succ_le_span c n (hstep n)) ih
  obtain ⟨e, he⟩ := hcomplete x hstep
  refine ⟨e, ?_, ?_, ?_⟩
  · have hzero : e * e - e = 0 := by
      refine hhaus _ fun n => ?_
      have : e * e - e = (x n * x n - x n) + (e - x n) * (e + x n - 1) := by ring
      rw [this]
      exact Ideal.add_mem _ (span_pow_le_span_pow c n.le_succ (hdef n))
        (Ideal.mul_mem_right _ _ (he n))
    exact sub_eq_zero.mp hzero
  · rw [← sub_sub_sub_cancel_right (1 : R) e (x 1)]
    refine M.sub_mem (hone 1) ?_
    have h1 := he 1
    rw [pow_one] at h1
    exact (Ideal.span_singleton_le_iff_mem _).mpr hcM h1
  · rw [← sub_add_sub_cancel e (x 1) x₀]
    refine Ideal.add_mem _ ?_ (hstart 1)
    have h1 := he 1
    rwa [pow_one] at h1

end Newton

section Carrier

variable (q : ℕ) [Fact q.Prime] (A : Type) [CommRing A]

private abbrev BA : Type :=
  @TensorProduct ℤ _ ℤ_[q] A
    (@NonUnitalNonAssocSemiring.toAddCommMonoid ℤ_[q]
      (@NonAssocSemiring.toNonUnitalNonAssocSemiring ℤ_[q] Semiring.toNonAssocSemiring))
    (@NonUnitalNonAssocSemiring.toAddCommMonoid A
      (@NonAssocSemiring.toNonUnitalNonAssocSemiring A Semiring.toNonAssocSemiring))
    Algebra.toModule Algebra.toModule

end Carrier

section Kit

variable {q : ℕ} [Fact q.Prime]

private theorem mem_span_pow_smul_top_iff {L : Type*} [AddCommGroup L] [Module ℤ_[q] L] {ι : Type*} [Fintype ι]
    (b : Module.Basis ι ℤ_[q] L) (k : ℕ) (x : L) :
    x ∈ Ideal.span {((q : ℤ_[q]) ^ k)} • (⊤ : Submodule ℤ_[q] L) ↔
      ∀ i, (q : ℤ_[q]) ^ k ∣ b.equivFun x i := by
  rw [Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists]
  constructor
  · rintro ⟨y, -, rfl⟩ i
    exact ⟨b.equivFun y i, by simp [map_smul]⟩
  · intro h
    choose d hd using h
    refine ⟨b.equivFun.symm d, Submodule.mem_top, b.equivFun.injective ?_⟩
    ext i
    simp only [map_smul, LinearEquiv.apply_symm_apply, Pi.smul_apply, smul_eq_mul]
    exact (hd i).symm

private noncomputable def coordMod {L : Type*} [AddCommGroup L] [Module ℤ_[q] L] {ι : Type*} [Fintype ι]
    (b : Module.Basis ι ℤ_[q] L) (k : ℕ) : L →+ (ι → ZMod (q ^ k)) where
  toFun x i := PadicInt.toZModPow k (b.equivFun x i)
  map_zero' := by ext i; simp
  map_add' x y := by ext i; simp [map_add]

private theorem coordMod_surjective {L : Type*} [AddCommGroup L] [Module ℤ_[q] L] {ι : Type*} [Fintype ι]
    (b : Module.Basis ι ℤ_[q] L) (k : ℕ) : Function.Surjective (coordMod b k) := by
  intro c
  have h : ∀ i, ∃ a : ℤ_[q], PadicInt.toZModPow k a = c i := fun i =>
    ZMod.ringHom_surjective (PadicInt.toZModPow k) (c i)
  choose a ha using h
  refine ⟨b.equivFun.symm a, ?_⟩
  ext i
  show PadicInt.toZModPow k (b.equivFun (b.equivFun.symm a) i) = c i
  rw [LinearEquiv.apply_symm_apply]
  exact ha i

private theorem ker_coordMod {L : Type*} [AddCommGroup L] [Module ℤ_[q] L] {ι : Type*} [Fintype ι]
    (b : Module.Basis ι ℤ_[q] L) (k : ℕ) :
    (coordMod b k).ker = (Ideal.span {((q : ℤ_[q]) ^ k)} • (⊤ : Submodule ℤ_[q] L)).toAddSubgroup := by
  ext x
  rw [AddMonoidHom.mem_ker, Submodule.mem_toAddSubgroup, mem_span_pow_smul_top_iff b k x]
  constructor
  · intro h i
    have hi : PadicInt.toZModPow k (b.equivFun x i) = 0 := congrFun h i
    have hk : b.equivFun x i ∈ RingHom.ker (PadicInt.toZModPow k : ℤ_[q] →+* ZMod (q ^ k)) :=
      RingHom.mem_ker.mpr hi
    rw [PadicInt.ker_toZModPow, Ideal.mem_span_singleton] at hk
    exact hk
  · intro h
    ext i
    have hk : b.equivFun x i ∈ RingHom.ker (PadicInt.toZModPow k : ℤ_[q] →+* ZMod (q ^ k)) := by
      rw [PadicInt.ker_toZModPow, Ideal.mem_span_singleton]
      exact h i
    exact RingHom.mem_ker.mp hk

private theorem natCard_quotient_span_pow_smul_top (L : Type*) [AddCommGroup L] [Module ℤ_[q] L]
    [Module.Free ℤ_[q] L] [Module.Finite ℤ_[q] L] (k : ℕ) :
    Nat.card (L ⧸ (Ideal.span {((q : ℤ_[q]) ^ k)} • (⊤ : Submodule ℤ_[q] L))) =
      q ^ (k * Module.finrank ℤ_[q] L) := by
  classical
  let b := Module.Free.chooseBasis ℤ_[q] L
  have e1 : (L ⧸ (Ideal.span {((q : ℤ_[q]) ^ k)} • (⊤ : Submodule ℤ_[q] L)).toAddSubgroup) ≃+
      (L ⧸ (coordMod b k).ker) :=
    QuotientAddGroup.quotientAddEquivOfEq (ker_coordMod b k).symm
  have e2 : (L ⧸ (coordMod b k).ker) ≃+ (Module.Free.ChooseBasisIndex ℤ_[q] L → ZMod (q ^ k)) :=
    QuotientAddGroup.quotientKerEquivOfSurjective (coordMod b k) (coordMod_surjective b k)
  have h := Nat.card_congr (e1.trans e2).toEquiv
  refine h.trans ?_
  rw [Nat.card_pi, Nat.card_zmod, Finset.prod_const, Finset.card_univ,
    ← Module.finrank_eq_card_chooseBasisIndex, ← pow_mul]

private theorem finrank_rat_tensor (L : Type*) [AddCommGroup L] [Module ℤ_[q] L] [Module.Free ℤ_[q] L] :
    Module.finrank ℚ_[q] (ℚ_[q] ⊗[ℤ_[q]] L) = Module.finrank ℤ_[q] L :=
  Module.finrank_baseChange

private theorem flat_rat : Module.Flat ℤ_[q] ℚ_[q] :=
  IsLocalization.flat ℚ_[q] (nonZeroDivisors ℤ_[q])

private theorem finrank_range_baseChange {L : Type*} [AddCommGroup L] [Module ℤ_[q] L] [Module.Free ℤ_[q] L]
    [Module.Finite ℤ_[q] L] (f : L →ₗ[ℤ_[q]] L) :
    Module.finrank ℚ_[q] (LinearMap.range (f.baseChange ℚ_[q])) =
      Module.finrank ℤ_[q] (LinearMap.range f) := by
  haveI : Module.Flat ℤ_[q] ℚ_[q] := flat_rat
  have hf : f = (LinearMap.range f).subtype ∘ₗ f.rangeRestrict := LinearMap.ext fun _ => rfl
  have hinj : Function.Injective ((LinearMap.range f).subtype.baseChange ℚ_[q]) := by
    rw [LinearMap.baseChange_eq_ltensor]
    exact Module.Flat.lTensor_preserves_injective_linearMap _ (Submodule.injective_subtype _)
  have hrange : LinearMap.range (f.baseChange ℚ_[q]) =
      LinearMap.range ((LinearMap.range f).subtype.baseChange ℚ_[q]) := by
    conv_lhs => rw [hf, LinearMap.baseChange_comp]
    exact LinearMap.range_comp_of_range_eq_top _
      (LinearMap.range_eq_top.mpr
        (LinearMap.baseChange_surjective ℚ_[q] (LinearMap.surjective_rangeRestrict f)))
  rw [hrange, ← (LinearEquiv.ofInjective _ hinj).finrank_eq, finrank_rat_tensor]

section Kdelta

variable {R : Type*} [CommRing R] {L : Type*} [AddCommGroup L] [Module R L]

private theorem mem_span_singleton_smul_top_iff (r : R) (x : L) :
    x ∈ Ideal.span {r} • (⊤ : Submodule R L) ↔ ∃ y, r • y = x := by
  rw [Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists]
  simp

private theorem span_singleton_smul_top_le_comap (r : R) (f : L →ₗ[R] L) :
    Ideal.span {r} • (⊤ : Submodule R L) ≤
      (Ideal.span {r} • (⊤ : Submodule R L)).comap f := by
  intro x hx
  rw [mem_span_singleton_smul_top_iff] at hx
  obtain ⟨y, rfl⟩ := hx
  rw [Submodule.mem_comap, map_smul, mem_span_singleton_smul_top_iff]
  exact ⟨f y, rfl⟩

private noncomputable def quotMap (r : R) (f : L →ₗ[R] L) :
    (L ⧸ Ideal.span {r} • (⊤ : Submodule R L)) →ₗ[R] (L ⧸ Ideal.span {r} • (⊤ : Submodule R L)) :=
  Submodule.mapQ _ _ f (span_singleton_smul_top_le_comap r f)

private theorem quotMap_mk (r : R) (f : L →ₗ[R] L) (x : L) :
    quotMap r f (Submodule.Quotient.mk x) = Submodule.Quotient.mk (f x) :=
  rfl

private theorem apply_eq_self_of_mem_range {f : L →ₗ[R] L} (hf : f ∘ₗ f = f) {x : L}
    (hx : x ∈ LinearMap.range f) : f x = x := by
  obtain ⟨z, rfl⟩ := hx
  exact congrArg (fun g : L →ₗ[R] L => g z) hf

private noncomputable def rangeToQuotRange (r : R) (f : L →ₗ[R] L) (hf : f ∘ₗ f = f) :
    LinearMap.range f →+ LinearMap.range (quotMap r f) where
  toFun x := ⟨Submodule.Quotient.mk (x : L), Submodule.Quotient.mk (x : L), by
    rw [quotMap_mk, apply_eq_self_of_mem_range hf x.2]⟩
  map_zero' := Subtype.ext (by simp)
  map_add' x y := Subtype.ext (by simp)

private theorem rangeToQuotRange_surjective (r : R) (f : L →ₗ[R] L) (hf : f ∘ₗ f = f) :
    Function.Surjective (rangeToQuotRange r f hf) := by
  rintro ⟨z, w, rfl⟩
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ w
  refine ⟨⟨f y, y, rfl⟩, Subtype.ext ?_⟩
  simp [rangeToQuotRange, quotMap_mk]

private theorem ker_rangeToQuotRange (r : R) (f : L →ₗ[R] L) (hf : f ∘ₗ f = f) :
    (rangeToQuotRange r f hf).ker =
      (Ideal.span {r} • (⊤ : Submodule R (LinearMap.range f))).toAddSubgroup := by
  ext x
  rw [AddMonoidHom.mem_ker, Submodule.mem_toAddSubgroup, mem_span_singleton_smul_top_iff]
  constructor
  · intro h
    have h' : (Submodule.Quotient.mk (x : L) :
        L ⧸ Ideal.span {r} • (⊤ : Submodule R L)) = 0 := congrArg Subtype.val h
    rw [Submodule.Quotient.mk_eq_zero, mem_span_singleton_smul_top_iff] at h'
    obtain ⟨y, hy⟩ := h'
    refine ⟨⟨f y, y, rfl⟩, Subtype.ext ?_⟩
    change r • f y = (x : L)
    rw [← map_smul f, hy, apply_eq_self_of_mem_range hf x.2]
  · rintro ⟨y, rfl⟩
    refine Subtype.ext ?_
    change (Submodule.Quotient.mk ((r • y : LinearMap.range f) : L) :
        L ⧸ Ideal.span {r} • (⊤ : Submodule R L)) = 0
    rw [Submodule.Quotient.mk_eq_zero, mem_span_singleton_smul_top_iff]
    exact ⟨y, rfl⟩

private theorem natCard_range_quotMap (r : R) (f : L →ₗ[R] L) (hf : f ∘ₗ f = f) :
    Nat.card (LinearMap.range (quotMap r f)) =
      Nat.card (LinearMap.range f ⧸ (Ideal.span {r} • (⊤ : Submodule R (LinearMap.range f)))) := by
  have e1 : (LinearMap.range f ⧸ (rangeToQuotRange r f hf).ker) ≃+ LinearMap.range (quotMap r f) :=
    QuotientAddGroup.quotientKerEquivOfSurjective _ (rangeToQuotRange_surjective r f hf)
  have e2 : (LinearMap.range f ⧸
      (Ideal.span {r} • (⊤ : Submodule R (LinearMap.range f))).toAddSubgroup) ≃+
      (LinearMap.range f ⧸ (rangeToQuotRange r f hf).ker) :=
    QuotientAddGroup.quotientAddEquivOfEq (ker_rangeToQuotRange r f hf).symm
  exact (Nat.card_congr (e2.trans e1).toEquiv).symm

end Kdelta

private theorem natCard_range_quotMap_eq_pow_finrank {L : Type*} [AddCommGroup L] [Module ℤ_[q] L]
    [Module.Free ℤ_[q] L] [Module.Finite ℤ_[q] L] (f : L →ₗ[ℤ_[q]] L) (hf : f ∘ₗ f = f) (k : ℕ) :
    Nat.card (LinearMap.range (quotMap ((q : ℤ_[q]) ^ k) f)) =
      q ^ (k * Module.finrank ℤ_[q] (LinearMap.range f)) := by
  rw [natCard_range_quotMap _ f hf, natCard_quotient_span_pow_smul_top]

section SpecGeneric

variable {A : Type*} [CommRing A]

private theorem span_mul_pow_le_of_spec {e : A} (he : IsIdempotentElem e) {𝔪 : Ideal A} {c : A} {L : ℕ}
    (hL : Ideal.span {e} * 𝔪 ^ L ≤ Ideal.span {c}) (n : ℕ) :
    Ideal.span {e} * 𝔪 ^ (L * n) ≤ Ideal.span {c ^ n} := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · have hspan : Ideal.span {e} ^ n = Ideal.span {e} := by
      rw [Ideal.span_singleton_pow, he.pow_eq hn.ne']
    calc Ideal.span {e} * 𝔪 ^ (L * n) = (Ideal.span {e} * 𝔪 ^ L) ^ n := by
          rw [mul_pow, hspan, pow_mul]
      _ ≤ Ideal.span {c} ^ n := Ideal.pow_right_mono hL n
      _ = Ideal.span {c ^ n} := Ideal.span_singleton_pow c n

private theorem dvd_mul_of_mem_pow {e : A} (he : IsIdempotentElem e) {𝔪 : Ideal A} {c : A} {L : ℕ}
    (hL : Ideal.span {e} * 𝔪 ^ L ≤ Ideal.span {c}) {n j : ℕ} (hj : L * n ≤ j) {b : A}
    (hb : b ∈ 𝔪 ^ j) : c ^ n ∣ e * b := by
  have h1 : e * b ∈ Ideal.span {e} * 𝔪 ^ (L * n) :=
    Ideal.mul_mem_mul (Ideal.mem_span_singleton_self e) (Ideal.pow_le_pow_right hj hb)
  exact Ideal.mem_span_singleton.mp (span_mul_pow_le_of_spec he hL n h1)

private theorem one_sub_mem_pow {e : A} (he : IsIdempotentElem e) {𝔪 : Ideal A} (h1 : 1 - e ∈ 𝔪) {j : ℕ}
    (hj : 1 ≤ j) : 1 - e ∈ 𝔪 ^ j := by
  have := Ideal.pow_mem_pow h1 j
  rwa [he.one_sub.pow_eq (Nat.one_le_iff_ne_zero.mp hj)] at this

private theorem span_pow_sup_pow_eq {e : A} (he : IsIdempotentElem e) {𝔪 : Ideal A} (h1 : 1 - e ∈ 𝔪)
    {c : A} {L : ℕ} (hL : Ideal.span {e} * 𝔪 ^ L ≤ Ideal.span {c}) {n j : ℕ} (hj1 : 1 ≤ j)
    (hj : L * n ≤ j) :
    Ideal.span {c ^ n} ⊔ 𝔪 ^ j = Ideal.span {c ^ n} ⊔ Ideal.span {1 - e} := by
  apply le_antisymm
  · refine sup_le le_sup_left fun b hb => ?_
    obtain ⟨d, hd⟩ := dvd_mul_of_mem_pow he hL hj hb
    have hsplit : b = c ^ n * d + (1 - e) * b := by rw [← hd]; ring
    rw [hsplit]
    exact Ideal.add_mem _
      (Ideal.mem_sup_left (Ideal.mul_mem_right d _ (Ideal.mem_span_singleton_self _)))
      (Ideal.mem_sup_right (Ideal.mul_mem_right b _ (Ideal.mem_span_singleton_self _)))
  · refine sup_le le_sup_left ?_
    rw [Ideal.span_singleton_le_iff_mem]
    exact Ideal.mem_sup_right (one_sub_mem_pow he h1 hj1)

end SpecGeneric

section G3

variable {S : Type*} [CommRing S] {A : Type*} [CommRing A] [Algebra S A]

private noncomputable def mulLeftModQ (s : S) (e : A) :
    A →ₗ[S] (A ⧸ Ideal.span {s} • (⊤ : Submodule S A)) :=
  (Ideal.span {s} • (⊤ : Submodule S A)).mkQ ∘ₗ LinearMap.mulLeft S e

private theorem ker_mulLeftModQ (s : S) {e : A} (he : IsIdempotentElem e) :
    LinearMap.ker (mulLeftModQ s e) =
      (Ideal.span {algebraMap S A s} ⊔ Ideal.span {1 - e}).restrictScalars S := by
  ext a
  rw [LinearMap.mem_ker, Submodule.restrictScalars_mem, mulLeftModQ, LinearMap.comp_apply,
    Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, LinearMap.mulLeft_apply,
    mem_span_singleton_smul_top_iff]
  constructor
  · rintro ⟨d, hd⟩
    have hsplit : a = algebraMap S A s * d + (1 - e) * a := by
      rw [Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul, hd]; ring
    rw [hsplit]
    exact Ideal.add_mem _
      (Ideal.mem_sup_left (Ideal.mul_mem_right d _ (Ideal.mem_span_singleton_self _)))
      (Ideal.mem_sup_right (Ideal.mul_mem_right a _ (Ideal.mem_span_singleton_self _)))
  · intro ha
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp ha
    obtain ⟨d, rfl⟩ := Ideal.mem_span_singleton'.mp hy
    obtain ⟨d', rfl⟩ := Ideal.mem_span_singleton'.mp hz
    have hz0 : e * (d' * (1 - e)) = 0 := by rw [mul_left_comm, he.mul_one_sub_self, mul_zero]
    refine ⟨e * d, ?_⟩
    rw [mul_add, hz0, add_zero, Algebra.smul_def]
    ring

private theorem range_mulLeftModQ (s : S) (e : A) :
    LinearMap.range (mulLeftModQ s e) = LinearMap.range (quotMap s (LinearMap.mulLeft S e)) := by
  ext x
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨Submodule.Quotient.mk a, quotMap_mk s (LinearMap.mulLeft S e) a⟩
  · rintro ⟨y, rfl⟩
    obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    exact ⟨a, (quotMap_mk s (LinearMap.mulLeft S e) a).symm⟩

private theorem natCard_quotient_span_sup_span_one_sub (s : S) {e : A} (he : IsIdempotentElem e) :
    Nat.card (A ⧸ (Ideal.span {algebraMap S A s} ⊔ Ideal.span {1 - e})) =
      Nat.card (LinearMap.range (quotMap s (LinearMap.mulLeft S e))) := by
  rw [← range_mulLeftModQ]
  have e1 := (Submodule.Quotient.restrictScalarsEquiv (S := S)
    (Ideal.span {algebraMap S A s} ⊔ Ideal.span {1 - e})).symm
  have e2 := Submodule.quotEquivOfEq _ _ (ker_mulLeftModQ s he).symm
  have e3 := (mulLeftModQ s e).quotKerEquivRange
  exact Nat.card_congr ((e1.trans e2).trans e3).toEquiv

private theorem mulLeft_comp_self {e : A} (he : IsIdempotentElem e) :
    LinearMap.mulLeft S e ∘ₗ LinearMap.mulLeft S e = LinearMap.mulLeft S e := by
  rw [← LinearMap.mulLeft_mul, he.eq]

end G3

private theorem natCard_quotient_span_pow_sup_pow_eq_pow {A : Type*} [CommRing A] [Algebra ℤ_[q] A]
    [Module.Free ℤ_[q] A] [Module.Finite ℤ_[q] A] {e : A} (he : IsIdempotentElem e) {𝔪 : Ideal A}
    (h1 : 1 - e ∈ 𝔪) {Ls : ℕ} (hLs : Ideal.span {e} * 𝔪 ^ Ls ≤ Ideal.span {((q : ℕ) : A)}) (k : ℕ)
    {L : ℕ} (hL1 : 1 ≤ L) (hLk : Ls * k ≤ L) :
    Nat.card (A ⧸ (Ideal.span {((q : ℕ) : A) ^ k} ⊔ 𝔪 ^ L)) =
      q ^ (k * Module.finrank ℤ_[q] (LinearMap.range (LinearMap.mulLeft ℤ_[q] e))) := by
  rw [span_pow_sup_pow_eq he h1 hLs hL1 hLk]
  have hq : ((q : ℕ) : A) ^ k = algebraMap ℤ_[q] A (((q : ℕ) : ℤ_[q]) ^ k) := by
    rw [map_pow, map_natCast]
  rw [hq, natCard_quotient_span_sup_span_one_sub (S := ℤ_[q]) _ he,
    natCard_range_quotMap_eq_pow_finrank _ (mulLeft_comp_self he) k]

section LevelCore

variable {S : Type*} [CommRing S]

private abbrev levelKer (q₀ : ℕ) [Fact q₀.Prime] (M : Type*) [AddCommGroup M] [Module ℤ_[q₀] M] (k : ℕ) :
    Submodule ℤ_[q₀] M :=
  Ideal.span {(q₀ : ℤ_[q₀]) ^ k} • (⊤ : Submodule ℤ_[q₀] M)

variable {M : Type*} [AddCommGroup M] [Module ℤ_[q] M]

private theorem mem_levelKer_iff (k : ℕ) (x : M) : x ∈ levelKer q M k ↔ ∃ y : M, (q : ℤ_[q]) ^ k • y = x :=
  mem_span_singleton_smul_top_iff _ _

private theorem map_mem_levelKer (g : M →ₗ[ℤ_[q]] M) (k : ℕ) {y : M} (hy : y ∈ levelKer q M k) :
    g y ∈ levelKer q M k := by
  obtain ⟨z, rfl⟩ := (mem_levelKer_iff k y).1 hy
  exact (mem_levelKer_iff k _).2 ⟨g z, (map_smul g _ z).symm⟩

private theorem natCast_pow_apply_mem_levelKer (θ : S →+* Module.End ℤ_[q] M) (k : ℕ) (y : M) :
    θ (((q : ℕ) : S) ^ k) y ∈ levelKer q M k := by
  refine (mem_levelKer_iff k _).2 ⟨y, ?_⟩
  rw [← Nat.cast_pow, ← Nat.cast_pow, map_natCast θ, Module.End.natCast_apply,
    Nat.cast_smul_eq_nsmul]

private theorem forall_apply_mem_iff_sub_mem (θ : S →+* Module.End ℤ_[q] M) {e : S}
    (he : IsIdempotentElem e) {𝔪 : Ideal S} (h1 : 1 - e ∈ 𝔪) {c : S} {L : ℕ}
    (hL : Ideal.span {e} * 𝔪 ^ L ≤ Ideal.span {c}) {n j : ℕ} (hj1 : 1 ≤ j) (hj : L * n ≤ j)
    (N : Submodule ℤ_[q] M) (hNs : ∀ (a : S) (y : M), y ∈ N → θ a y ∈ N)
    (hNc : ∀ y : M, θ (c ^ n) y ∈ N) (x : M) :
    (∀ b ∈ 𝔪 ^ j, θ b x ∈ N) ↔ x - θ e x ∈ N := by
  constructor
  · intro h
    have h' := h (1 - e) (one_sub_mem_pow he h1 hj1)
    rw [map_sub θ 1 e, map_one θ, LinearMap.sub_apply, Module.End.one_apply] at h'
    exact h'
  · intro hx b hb
    obtain ⟨d, hd⟩ := dvd_mul_of_mem_pow he hL hj hb
    have hsplit : b = c ^ n * d + b * (1 - e) := by rw [← hd]; ring
    have hbx : θ b x = θ (c ^ n) (θ d x) + θ b (x - θ e x) := by
      conv_lhs => rw [hsplit]
      rw [map_add θ, LinearMap.add_apply, map_mul θ (c ^ n) d, map_mul θ b (1 - e),
        Module.End.mul_apply, Module.End.mul_apply, map_sub θ 1 e, map_one θ, LinearMap.sub_apply,
        Module.End.one_apply]
    rw [hbx]
    exact N.add_mem (hNc _) (hNs b _ hx)

private def carryIdeal (θ : S →+* Module.End ℤ_[q] M) (N : Submodule ℤ_[q] M)
    (hNs : ∀ (a : S) (y : M), y ∈ N → θ a y ∈ N) (x : M) : Ideal S where
  carrier := {b | θ b x ∈ N}
  zero_mem' := by
    show θ 0 x ∈ N
    rw [map_zero θ, LinearMap.zero_apply]
    exact N.zero_mem
  add_mem' := by
    intro a b ha hb
    show θ (a + b) x ∈ N
    rw [map_add θ, LinearMap.add_apply]
    exact N.add_mem ha hb
  smul_mem' := by
    intro a b hb
    show θ (a * b) x ∈ N
    rw [map_mul θ, Module.End.mul_apply]
    exact hNs a _ hb

private theorem mem_carryIdeal (θ : S →+* Module.End ℤ_[q] M) (N : Submodule ℤ_[q] M)
    (hNs : ∀ (a : S) (y : M), y ∈ N → θ a y ∈ N) (x : M) (b : S) :
    b ∈ carryIdeal θ N hNs x ↔ θ b x ∈ N :=
  Iff.rfl

private theorem forall_mem_map_pow_iff {R : Type*} [CommRing R] (ι : R →+* S)
    (θ : S →+* Module.End ℤ_[q] M) (N : Submodule ℤ_[q] M)
    (hNs : ∀ (a : S) (y : M), y ∈ N → θ a y ∈ N) (𝔓 : Ideal R) (L : ℕ) (x : M) :
    (∀ b ∈ Ideal.map ι 𝔓 ^ L, θ b x ∈ N) ↔ ∀ t ∈ 𝔓 ^ L, θ (ι t) x ∈ N := by
  rw [← Ideal.map_pow]
  constructor
  · intro h t ht
    exact h _ (Ideal.mem_map_of_mem ι ht)
  · intro h
    have hle : Ideal.map ι (𝔓 ^ L) ≤ carryIdeal θ N hNs x :=
      Ideal.map_le_iff_le_comap.2 fun t ht => Ideal.mem_comap.2 ((mem_carryIdeal θ N hNs x _).2 (h t ht))
    exact fun b hb => (mem_carryIdeal θ N hNs x b).1 (hle hb)

private theorem natCard_subtype_eq_pow [Module.Free ℤ_[q] M] [Module.Finite ℤ_[q] M]
    (θ : S →+* Module.End ℤ_[q] M) {e : S} (he : IsIdempotentElem e) (k : ℕ) {J' : Type*}
    [AddCommGroup J'] (π : M →+ J') (hker : ∀ x : M, π x = 0 ↔ x ∈ levelKer q M k) (P : J' → Prop)
    (hlift : ∀ y : J', P y → ∃ x : M, π x = y)
    (hP : ∀ x : M, P (π x) ↔ x - θ e x ∈ levelKer q M k) :
    Nat.card {y : J' // P y} = q ^ (k * Module.finrank ℤ_[q] (LinearMap.range (θ e))) := by
  have hf : θ e ∘ₗ θ e = θ e := by
    rw [← Module.End.mul_eq_comp, ← map_mul θ, he.eq]
  have hsub : ∀ x x' : M, π x = π x' ↔ x - x' ∈ levelKer q M k := fun x x' => by
    rw [← hker, map_sub π, sub_eq_zero]
  rw [← natCard_range_quotMap_eq_pow_finrank (θ e) hf k]
  choose lift hlift using hlift
  have hmem : ∀ y : {y : J' // P y},
      (Submodule.Quotient.mk (lift y.1 y.2) : M ⧸ levelKer q M k) ∈
        LinearMap.range (quotMap ((q : ℤ_[q]) ^ k) (θ e)) := by
    intro y
    refine ⟨Submodule.Quotient.mk (lift y.1 y.2), ?_⟩
    rw [quotMap_mk, Submodule.Quotient.eq]
    have h := (hP (lift y.1 y.2)).1 (by rw [hlift]; exact y.2)
    have h' := (levelKer q M k).neg_mem h
    rw [neg_sub] at h'
    exact h'
  let Φ : {y : J' // P y} → LinearMap.range (quotMap ((q : ℤ_[q]) ^ k) (θ e)) :=
    fun y => ⟨Submodule.Quotient.mk (lift y.1 y.2), hmem y⟩
  have hΦ : Function.Bijective Φ := by
    constructor
    · intro y₁ y₂ h
      have h1 : (Submodule.Quotient.mk (lift y₁.1 y₁.2) : M ⧸ levelKer q M k) =
          Submodule.Quotient.mk (lift y₂.1 y₂.2) := congrArg Subtype.val h
      rw [Submodule.Quotient.eq] at h1
      have h2 := (hsub _ _).2 h1
      rw [hlift, hlift] at h2
      exact Subtype.ext h2
    · rintro ⟨z, w, rfl⟩
      obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ w
      have hPx : P (π (θ e x)) := by
        rw [hP, ← Module.End.mul_apply, ← map_mul θ, he.eq, sub_self]
        exact Submodule.zero_mem _
      refine ⟨⟨_, hPx⟩, Subtype.ext ?_⟩
      show (Submodule.Quotient.mk (lift _ hPx) : M ⧸ levelKer q M k) =
        quotMap ((q : ℤ_[q]) ^ k) (θ e) (Submodule.Quotient.mk x)
      rw [quotMap_mk, Submodule.Quotient.eq]
      exact (hsub _ _).1 (hlift _ hPx)
  exact Nat.card_congr (Equiv.ofBijective Φ hΦ)

end LevelCore

end Kit

section Complete

variable (q : ℕ) [Fact q.Prime] (A : Type) [CommRing A]

private theorem mem_smul_top_iff (n : ℕ) (a : ℤ_[q]) :
    a ∈ (IsLocalRing.maximalIdeal ℤ_[q] ^ n • ⊤ : Submodule ℤ_[q] ℤ_[q]) ↔
      a ∈ Ideal.span {(q : ℤ_[q]) ^ n} := by
  rw [PadicInt.maximalIdeal_eq_span_p, Ideal.span_singleton_pow, Ideal.smul_eq_mul, Ideal.mul_top]

private theorem natCast_pow_eq_algebraMap (n : ℕ) :
    ((q : ℕ) : BA q A) ^ n = algebraMap ℤ_[q] (BA q A) ((q : ℤ_[q]) ^ n) := by
  rw [map_pow, map_natCast]

private theorem smul_eq_natCast_pow_mul (n : ℕ) (z : BA q A) :
    ((q : ℤ_[q]) ^ n) • z = ((q : ℕ) : BA q A) ^ n * z := by
  rw [natCast_pow_eq_algebraMap]
  exact Algebra.smul_def ((q : ℤ_[q]) ^ n) z

private theorem mem_span_pow_iff_exists_smul (n : ℕ) (y : BA q A) :
    y ∈ Ideal.span {((q : ℕ) : BA q A) ^ n} ↔ ∃ z : BA q A, y = ((q : ℤ_[q]) ^ n) • z := by
  constructor
  · intro h
    obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.mp h
    exact ⟨a, by rw [smul_eq_natCast_pow_mul, mul_comm]; exact ha.symm⟩
  · rintro ⟨z, rfl⟩
    rw [smul_eq_natCast_pow_mul]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)

variable [Module.Free ℤ A] [Module.Finite ℤ A]

private def bBA : Module.Basis (Module.Free.ChooseBasisIndex ℤ A) ℤ_[q] (BA q A) :=
  Algebra.TensorProduct.basis ℤ_[q] (Module.Free.chooseBasis ℤ A)

omit [Module.Finite ℤ A] in
private theorem repr_mem_of_mem_span_pow (n : ℕ) (y : BA q A)
    (h : y ∈ Ideal.span {((q : ℕ) : BA q A) ^ n}) (i : Module.Free.ChooseBasisIndex ℤ A) :
    (bBA q A).repr y i ∈ Ideal.span {(q : ℤ_[q]) ^ n} := by
  obtain ⟨z, rfl⟩ := (mem_span_pow_iff_exists_smul q A n y).mp h
  rw [LinearEquiv.map_smul, Finsupp.smul_apply, smul_eq_mul, mul_comm]
  exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)

private theorem mem_span_pow_of_repr_mem (n : ℕ) (y : BA q A)
    (h : ∀ i, (bBA q A).repr y i ∈ Ideal.span {(q : ℤ_[q]) ^ n}) :
    y ∈ Ideal.span {((q : ℕ) : BA q A) ^ n} := by
  choose d hd using fun i => Ideal.mem_span_singleton'.mp (h i)
  refine (mem_span_pow_iff_exists_smul q A n y).mpr
    ⟨(bBA q A).repr.symm (Finsupp.equivFunOnFinite.symm d), ?_⟩
  apply (bBA q A).repr.injective
  rw [LinearEquiv.map_smul, LinearEquiv.apply_symm_apply]
  ext i
  rw [Finsupp.smul_apply, smul_eq_mul, Finsupp.coe_equivFunOnFinite_symm, mul_comm, hd]

private theorem tensor_complete (x : ℕ → BA q A)
    (hx : ∀ n, x (n + 1) - x n ∈ Ideal.span {((q : ℕ) : BA q A) ^ (n + 1)}) :
    ∃ e : BA q A, ∀ n, e - x n ∈ Ideal.span {((q : ℕ) : BA q A) ^ n} := by
  have htel : ∀ m d, x (m + d) - x m ∈ Ideal.span {((q : ℕ) : BA q A) ^ m} := by
    intro m d
    induction d with
    | zero => rw [Nat.add_zero, sub_self]; exact Ideal.zero_mem _
    | succ d ih =>
      show x (m + d + 1) - x m ∈ _
      rw [← sub_add_sub_cancel (x (m + d + 1)) (x (m + d)) (x m)]
      exact Ideal.add_mem _
        (span_pow_le_span_pow _ (show m ≤ m + d + 1 by omega) (hx (m + d))) ih
  have hcauchy : ∀ i, ∀ {m n : ℕ}, m ≤ n →
      (bBA q A).repr (x m) i ≡ (bBA q A).repr (x n) i
        [SMOD (IsLocalRing.maximalIdeal ℤ_[q] ^ m • ⊤ : Submodule ℤ_[q] ℤ_[q])] := by
    intro i m n hmn
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hmn
    refine SModEq.sub_mem.mpr ((mem_smul_top_iff q m _).mpr ?_)
    have h := repr_mem_of_mem_span_pow q A m _ (htel m d) i
    rw [map_sub, Finsupp.sub_apply] at h
    rw [← neg_sub]
    exact neg_mem_iff.mpr h
  have hlim : ∀ i, ∃ a : ℤ_[q], ∀ n, (bBA q A).repr (x n) i - a ∈ Ideal.span {(q : ℤ_[q]) ^ n} := by
    intro i
    obtain ⟨a, ha⟩ := IsPrecomplete.prec
      (inferInstance : IsPrecomplete (IsLocalRing.maximalIdeal ℤ_[q]) ℤ_[q])
      (f := fun n => (bBA q A).repr (x n) i) (hcauchy i)
    exact ⟨a, fun n => (mem_smul_top_iff q n _).mp (SModEq.sub_mem.mp (ha n))⟩
  choose a ha using hlim
  refine ⟨(bBA q A).repr.symm (Finsupp.equivFunOnFinite.symm a), fun n => ?_⟩
  refine mem_span_pow_of_repr_mem q A n _ fun i => ?_
  rw [map_sub, Finsupp.sub_apply, LinearEquiv.apply_symm_apply, Finsupp.coe_equivFunOnFinite_symm,
    ← neg_sub]
  exact neg_mem_iff.mpr (ha i n)

omit [Module.Finite ℤ A] in

private theorem tensor_haus (y : BA q A) (hy : ∀ n, y ∈ Ideal.span {((q : ℕ) : BA q A) ^ n}) :
    y = 0 := by
  refine (bBA q A).ext_elem_iff.mpr fun i => ?_
  rw [map_zero, Finsupp.zero_apply]
  refine IsHausdorff.haus (inferInstance : IsHausdorff (IsLocalRing.maximalIdeal ℤ_[q]) ℤ_[q]) _
    fun n => ?_
  refine SModEq.sub_mem.mpr ?_
  rw [sub_zero]
  exact (mem_smul_top_iff q n _).mpr (repr_mem_of_mem_span_pow q A n y (hy n) i)

end Complete

section LevelOne

variable (q : ℕ) [Fact q.Prime] (A : Type) [CommRing A]

private theorem finite_quotient_span_natCast [Module.Free ℤ A] [Module.Finite ℤ A] :
    Finite (A ⧸ Ideal.span {((q : ℕ) : A)}) := by
  haveI : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
  set Q : Ideal A := Ideal.span {((q : ℕ) : A)}
  have hle : LinearMap.range (LinearMap.lsmul ℤ A (q : ℤ)) ≤
      LinearMap.ker (Ideal.Quotient.mk Q).toAddMonoidHom.toIntLinearMap := by
    rintro _ ⟨a, rfl⟩
    rw [LinearMap.mem_ker]
    show Ideal.Quotient.mk Q ((q : ℤ) • a) = 0
    refine Ideal.Quotient.eq_zero_iff_mem.mpr ?_
    rw [zsmul_eq_mul, Int.cast_natCast]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
  refine Finite.of_surjective
    ((LinearMap.range (LinearMap.lsmul ℤ A (q : ℤ))).liftQ
      (Ideal.Quotient.mk Q).toAddMonoidHom.toIntLinearMap hle) fun y => ?_
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective y
  exact ⟨Submodule.Quotient.mk a, rfl⟩

private theorem level_one [Nontrivial A] [IsAddTorsionFree A] [Module.Free ℤ A] [Module.Finite ℤ A]
    (K : Ideal A) (hqK : ((q : ℕ) : A) ∈ K) :
    ∃ t : A, ∃ L : ℕ, t * t - t ∈ Ideal.span {((q : ℕ) : A)} ∧ 1 - t ∈ K ∧
      ∀ s ∈ K ^ L, t * s ∈ Ideal.span {((q : ℕ) : A)} := by
  set Q : Ideal A := Ideal.span {((q : ℕ) : A)} with hQ
  haveI : Finite (A ⧸ Q) := finite_quotient_span_natCast q A
  haveI : IsArtinian (A ⧸ Q) (A ⧸ Q) := isArtinian_of_finite
  set π : A →+* A ⧸ Q := Ideal.Quotient.mk Q with hπ
  set 𝔫 : Ideal (A ⧸ Q) := Ideal.map π K with h𝔫
  let f : ℕ →o (Submodule (A ⧸ Q) (A ⧸ Q))ᵒᵈ :=
    ⟨fun L => OrderDual.toDual (𝔫 ^ L), fun L L' h =>
      OrderDual.toDual_le_toDual.mpr (Ideal.pow_le_pow_right h)⟩
  obtain ⟨L, hL⟩ := IsArtinian.monotone_stabilizes f
  have hstab : ∀ m, L ≤ m → 𝔫 ^ L = 𝔫 ^ m := fun m hm => by
    have h : OrderDual.toDual (𝔫 ^ L) = OrderDual.toDual (𝔫 ^ m) := hL m hm
    exact OrderDual.toDual.injective h
  set C : Ideal (A ⧸ Q) := 𝔫 ^ (L + 1) with hC
  have hCC : C * C = C := by
    rw [hC, ← pow_add, ← hstab (L + 1 + (L + 1)) (by omega), ← hstab (L + 1) (by omega)]
  have hCfg : C.FG := Submodule.fg_def.mpr ⟨C, Set.toFinite _, Submodule.span_eq C⟩
  obtain ⟨r, hr1, hr⟩ :=
    Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul C C hCfg
      (by rw [Ideal.smul_eq_mul, hCC])
  obtain ⟨t, ht⟩ := Ideal.Quotient.mk_surjective (I := Q) r
  have hπt : π t = r := ht
  refine ⟨t, L + 1, ?_, ?_, ?_⟩
  · refine Ideal.Quotient.eq_zero_iff_mem.mp ?_
    show π (t * t - t) = 0
    rw [map_sub, map_mul, hπt]
    have h := hr (r - 1) hr1
    rw [smul_eq_mul, mul_sub, mul_one] at h
    exact h
  · have hC1 : C ≤ 𝔫 := by rw [hC]; exact Ideal.pow_le_self (Nat.succ_ne_zero L)
    have hmem : π (1 - t) ∈ 𝔫 := by
      rw [map_sub, map_one, hπt, ← neg_sub]
      exact neg_mem_iff.mpr (hC1 hr1)
    have hcomap : (1 - t) ∈ Ideal.comap π 𝔫 := Ideal.mem_comap.mpr hmem
    rw [h𝔫, Ideal.comap_map_of_surjective π Ideal.Quotient.mk_surjective,
      ← RingHom.ker_eq_comap_bot, hπ, Ideal.mk_ker] at hcomap
    have hQK : Q ≤ K := by
      rw [hQ]
      exact (Ideal.span_singleton_le_iff_mem _).mpr hqK
    rwa [sup_eq_left.mpr hQK] at hcomap
  · intro s hs
    refine Ideal.Quotient.eq_zero_iff_mem.mp ?_
    show π (t * s) = 0
    rw [map_mul, hπt]
    have hmem : π s ∈ C := by
      rw [hC, h𝔫, ← Ideal.map_pow]
      exact Ideal.mem_map_of_mem π hs
    have h := hr _ hmem
    rwa [smul_eq_mul] at h

end LevelOne

section Idempotent

variable (q : ℕ) [Fact q.Prime] (A : Type) [CommRing A]

private def inclR : A →+* BA q A := (Algebra.TensorProduct.includeRight : A →ₐ[ℤ] BA q A).toRingHom

private theorem inclR_natCast : inclR q A ((q : ℕ) : A) = ((q : ℕ) : BA q A) := map_natCast _ q

private theorem inclR_mem_span_of_mem_span (y : A) (hy : y ∈ Ideal.span {((q : ℕ) : A)}) :
    inclR q A y ∈ Ideal.span {((q : ℕ) : BA q A)} := by
  obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.mp hy
  rw [map_mul, inclR_natCast]
  exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)

private theorem tensor_eq_zero_of_subsingleton (h : Subsingleton A) : ∀ b : BA q A, b = 0 := by
  have h1 : (1 : BA q A) = 0 := by
    rw [Algebra.TensorProduct.one_def, Subsingleton.elim (1 : A) 0, TensorProduct.tmul_zero]
  intro b
  rw [← mul_one b, h1, mul_zero]

private theorem exists_idempotent [IsAddTorsionFree A] [Module.Free ℤ A] [Module.Finite ℤ A]
    (K : Ideal A) (hqK : ((q : ℕ) : A) ∈ K) :
    ∃ e : BA q A, IsIdempotentElem e ∧ 1 - e ∈ K.map (inclR q A) ∧
      ∃ L : ℕ, Ideal.span {e} * K.map (inclR q A) ^ L ≤ Ideal.span {((q : ℕ) : BA q A)} := by
  rcases subsingleton_or_nontrivial A with hA | hA
  · refine ⟨0, IsIdempotentElem.zero, ?_, 0, ?_⟩
    · rw [tensor_eq_zero_of_subsingleton q A hA 1, zero_sub, neg_mem_iff]
      exact Ideal.zero_mem _
    · rw [Ideal.span_singleton_eq_bot.mpr rfl, Ideal.bot_mul]; exact bot_le
  · obtain ⟨t, L, hu, hm, hγ⟩ := level_one q A K hqK
    have hqM : ((q : ℕ) : BA q A) ∈ K.map (inclR q A) := by
      rw [← inclR_natCast]; exact Ideal.mem_map_of_mem _ hqK
    have hu₀ : inclR q A t * inclR q A t - inclR q A t ∈ Ideal.span {((q : ℕ) : BA q A)} := by
      rw [← map_mul, ← map_sub]
      exact inclR_mem_span_of_mem_span q A _ hu
    have hm₀ : 1 - inclR q A t ∈ K.map (inclR q A) := by
      rw [← map_one (inclR q A), ← map_sub]
      exact Ideal.mem_map_of_mem _ hm
    have hγ₀ : ∀ m ∈ K.map (inclR q A) ^ L,
        inclR q A t * m ∈ Ideal.span {((q : ℕ) : BA q A)} := by
      intro m hm'
      rw [← Ideal.map_pow, Ideal.map] at hm'
      refine Submodule.span_induction
        (p := fun m _ => inclR q A t * m ∈ Ideal.span {((q : ℕ) : BA q A)}) ?_ ?_ ?_ ?_ hm'
      · rintro _ ⟨s, hs, rfl⟩
        show inclR q A t * inclR q A s ∈ _
        rw [← map_mul]
        exact inclR_mem_span_of_mem_span q A _ (hγ s hs)
      · show inclR q A t * 0 ∈ _
        rw [mul_zero]; exact Ideal.zero_mem _
      · intro a b _ _ ha hb
        show inclR q A t * (a + b) ∈ _
        rw [mul_add]; exact Ideal.add_mem _ ha hb
      · intro a b _ hb
        show inclR q A t * (a • b) ∈ _
        rw [smul_eq_mul, mul_left_comm]
        exact Ideal.mul_mem_left _ _ hb
    obtain ⟨e, he, h1e, hex⟩ :=
      exists_idempotent_of_complete ((q : ℕ) : BA q A) (K.map (inclR q A)) hqM (inclR q A t)
        hu₀ hm₀ (tensor_complete q A) (tensor_haus q A)
    refine ⟨e, he, h1e, L, Ideal.mul_le.mpr ?_⟩
    intro r hr s hs
    obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.mp hr
    have : a * e * s = a * ((e - inclR q A t) * s) + a * (inclR q A t * s) := by ring
    rw [this]
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ (Ideal.mul_mem_right _ _ hex))
      (Ideal.mul_mem_left _ _ (hγ₀ s hs))

end Idempotent

section LinAlg

variable (q : ℕ) [Fact q.Prime]

private theorem finrank_range_eq_of_conj {V V' : Type*} [AddCommGroup V] [Module ℚ_[q] V] [AddCommGroup V']
    [Module ℚ_[q] V'] (σ : V ≃ₗ[ℚ_[q]] V') (g : V →ₗ[ℚ_[q]] V) (g' : V' →ₗ[ℚ_[q]] V')
    (h : ∀ x, σ (g x) = g' (σ x)) :
    Module.finrank ℚ_[q] (LinearMap.range g') = Module.finrank ℚ_[q] (LinearMap.range g) := by
  have hr : LinearMap.range g' = (LinearMap.range g).map σ.toLinearMap := by
    ext y
    constructor
    · rintro ⟨x', rfl⟩
      refine ⟨g (σ.symm x'), ⟨σ.symm x', rfl⟩, ?_⟩
      show σ (g (σ.symm x')) = g' x'
      rw [h, LinearEquiv.apply_symm_apply]
    · rintro ⟨x, ⟨z, rfl⟩, rfl⟩
      exact ⟨σ z, (h z).symm⟩
  rw [hr, LinearEquiv.finrank_map_eq]

private def diag {T' : Type*} [CommRing T'] [Algebra ℚ_[q] T'] (c : T') : (Fin 2 → T') →ₗ[ℚ_[q]] (Fin 2 → T') :=
  (LinearMap.mulLeft ℚ_[q] c).compLeft (Fin 2)

private theorem diag_apply {T' : Type*} [CommRing T'] [Algebra ℚ_[q] T'] (c : T') (w : Fin 2 → T') :
    diag q c w = c • w := rfl

private theorem finrank_range_diag {T' : Type*} [CommRing T'] [Algebra ℚ_[q] T'] [Module.Finite ℚ_[q] T']
    (c : T') :
    Module.finrank ℚ_[q] (LinearMap.range (diag q c)) =
      2 * Module.finrank ℚ_[q] (LinearMap.range (LinearMap.mulLeft ℚ_[q] c)) := by
  set E : Submodule ℚ_[q] T' := LinearMap.range (LinearMap.mulLeft ℚ_[q] c)
  have iso : LinearMap.range (diag q c) ≃ₗ[ℚ_[q]] (Fin 2 → E) :=
    { toFun := fun w => fun i => ⟨w.1 i, by
        obtain ⟨v, hv⟩ := LinearMap.mem_range.mp w.2
        exact LinearMap.mem_range.mpr ⟨v i, congr_fun hv i⟩⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      invFun := fun g => ⟨fun i => (g i).1, LinearMap.mem_range.mpr
        ⟨fun i => Classical.choose (LinearMap.mem_range.mp (g i).2),
          funext fun i => Classical.choose_spec (LinearMap.mem_range.mp (g i).2)⟩⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [iso.finrank_eq, Module.finrank_pi_fintype ℚ_[q], Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, smul_eq_mul]

private def conjε {V : Type*} {_ : AddCommMonoid V} {_ : Module ℚ_[q] V} {T' : Type*} [CommRing T']
    [Algebra ℚ_[q] T'] (ε : V ≃ₗ[ℚ_[q]] (Fin 2 → T')) : T' →ₗ[ℚ_[q]] Module.End ℚ_[q] V where
  toFun c := ε.symm.toLinearMap ∘ₗ diag q c ∘ₗ ε.toLinearMap
  map_add' c₁ c₂ := by
    refine LinearMap.ext fun v => ?_
    show ε.symm (diag q (c₁ + c₂) (ε v)) = ε.symm (diag q c₁ (ε v)) + ε.symm (diag q c₂ (ε v))
    rw [diag_apply, diag_apply, diag_apply, add_smul, map_add]
  map_smul' a c := by
    refine LinearMap.ext fun v => ?_
    show ε.symm (diag q (a • c) (ε v)) = a • ε.symm (diag q c (ε v))
    rw [diag_apply, diag_apply, smul_assoc, map_smul]

private theorem conjε_eq_of {V : Type*} {_ : AddCommMonoid V} {_ : Module ℚ_[q] V} {T' : Type*} [CommRing T']
    [Algebra ℚ_[q] T'] (ε : V ≃ₗ[ℚ_[q]] (Fin 2 → T')) (c : T') (F : Module.End ℚ_[q] V)
    (h : ∀ v, ε (F v) = c • ε v) : conjε q ε c = F := by
  refine LinearMap.ext fun v => ?_
  show ε.symm (diag q c (ε v)) = F v
  rw [LinearEquiv.symm_apply_eq, diag_apply, h]

private theorem linearIndependent_of_conj {ι : Type*} {V : Type*} {_ : AddCommMonoid V} {_ : Module ℚ_[q] V}
    {T' : Type*} [CommRing T'] [Algebra ℚ_[q] T'] (ε : V ≃ₗ[ℚ_[q]] (Fin 2 → T')) (c : ι → T')
    (F : ι → Module.End ℚ_[q] V) (h : ∀ i v, ε (F i v) = c i • ε v)
    (hF : LinearIndependent ℚ_[q] F) : LinearIndependent ℚ_[q] c := by
  refine LinearIndependent.of_comp (conjε q ε) ?_
  have hcomp : (conjε q ε) ∘ c = F := funext fun i => conjε_eq_of q ε (c i) (F i) (h i)
  rw [hcomp]
  exact hF

end LinAlg

section Core

variable (q : ℕ) [Fact q.Prime] (A : Type) [CommRing A]
  (M : Type) [AddCommGroup M] [Module ℤ_[q] M] (ρ : A →+* Module.End ℤ_[q] M)

private def ΘG : BA q A →ₐ[ℤ_[q]] Module.End ℤ_[q] M :=
  Algebra.TensorProduct.lift (Algebra.ofId ℤ_[q] (Module.End ℤ_[q] M)) ρ.toIntAlgHom
    (fun a _ => Algebra.commutes a _)

private theorem ΘG_tmul (a : ℤ_[q]) (s : A) :
    ΘG q A M ρ (a ⊗ₜ[ℤ] s) = algebraMap ℤ_[q] (Module.End ℤ_[q] M) a * ρ s := by
  rw [ΘG, Algebra.TensorProduct.lift_tmul, Algebra.ofId_apply, RingHom.toIntAlgHom_apply]

private theorem ΘG_tmul_eq_smul (a : ℤ_[q]) (s : A) : ΘG q A M ρ (a ⊗ₜ[ℤ] s) = a • ρ s := by
  rw [ΘG_tmul, Algebra.smul_def]

private theorem ΘG_one_tmul (s : A) : ΘG q A M ρ ((1 : ℤ_[q]) ⊗ₜ[ℤ] s) = ρ s := by
  rw [ΘG_tmul, map_one, one_mul]

variable {T' : Type} [CommRing T'] [Algebra ℤ_[q] T'] (χ : A →+* T')

private def χ₀ : BA q A →ₐ[ℤ_[q]] T' :=
  Algebra.TensorProduct.lift (Algebra.ofId ℤ_[q] T') χ.toIntAlgHom (fun a _ => Algebra.commutes a _)

private theorem χ₀_tmul (c : ℤ_[q]) (s : A) : χ₀ q A χ (c ⊗ₜ[ℤ] s) = algebraMap ℤ_[q] T' c * χ s := by
  rw [χ₀, Algebra.TensorProduct.lift_tmul, Algebra.ofId_apply, RingHom.toIntAlgHom_apply]

variable [Algebra ℚ_[q] T'] [IsScalarTower ℤ_[q] ℚ_[q] T']
  (ε : (ℚ_[q] ⊗[ℤ_[q]] M) ≃ₗ[ℚ_[q]] (Fin 2 → T'))
  (hequiv : ∀ (s : A) (v : ℚ_[q] ⊗[ℤ_[q]] M), ε ((ρ s).baseChange ℚ_[q] v) = χ s • ε v)

private def τ : (ℚ_[q] ⊗[ℤ_[q]] (BA q A)) →ₐ[ℚ_[q]] T' :=
  Algebra.TensorProduct.lift (Algebra.ofId ℚ_[q] T') (χ₀ q A χ) (fun a _ => Algebra.commutes a _)

private theorem τ_tmul (a : ℚ_[q]) (b : BA q A) :
    τ q A χ (a ⊗ₜ[ℤ_[q]] b) = algebraMap ℚ_[q] T' a * χ₀ q A χ b := by
  rw [τ, Algebra.TensorProduct.lift_tmul, Algebra.ofId_apply]

private theorem τ_one_tmul (b : BA q A) : τ q A χ ((1 : ℚ_[q]) ⊗ₜ[ℤ_[q]] b) = χ₀ q A χ b := by
  rw [τ_tmul, map_one, one_mul]

private theorem τ_one_tmul_one_tmul (s : A) :
    τ q A χ ((1 : ℚ_[q]) ⊗ₜ[ℤ_[q]] ((1 : ℤ_[q]) ⊗ₜ[ℤ] s)) = χ s := by
  rw [τ_one_tmul, χ₀_tmul, map_one, one_mul]

private theorem τ_surjective (hadj : Algebra.adjoin ℚ_[q] (Set.range χ) = ⊤) :
    Function.Surjective (τ q A χ) := by
  rw [← AlgHom.range_eq_top, eq_top_iff, ← hadj]
  refine Algebra.adjoin_le ?_
  rintro _ ⟨s, rfl⟩
  exact ⟨(1 : ℚ_[q]) ⊗ₜ[ℤ_[q]] ((1 : ℤ_[q]) ⊗ₜ[ℤ] s), τ_one_tmul_one_tmul q A χ s⟩

private theorem finrank_tensor_tensor [Module.Free ℤ A] {ι : Type} [Fintype ι] (b : Module.Basis ι ℤ A) :
    Module.finrank ℚ_[q] (ℚ_[q] ⊗[ℤ_[q]] (BA q A)) = Fintype.card ι := by
  rw [Module.finrank_baseChange, Module.finrank_baseChange, Module.finrank_eq_card_basis b]

private theorem τ_bijective [Module.Free ℤ A] [Module.Finite ℤ A]
    (hadj : Algebra.adjoin ℚ_[q] (Set.range χ) = ⊤) {ι : Type} [Fintype ι]
    (b : Module.Basis ι ℤ A) (hli : LinearIndependent ℚ_[q] (fun i => χ (b i))) :
    Function.Bijective (τ q A χ) := by
  have hsurj := τ_surjective q A χ hadj
  haveI : Module.Finite ℚ_[q] T' := Module.Finite.of_surjective (τ q A χ).toLinearMap hsurj
  have hcard : Fintype.card ι ≤ Module.finrank ℚ_[q] T' := hli.fintype_card_le_finrank
  have hle : Module.finrank ℚ_[q] T' ≤ Module.finrank ℚ_[q] (ℚ_[q] ⊗[ℤ_[q]] (BA q A)) := by
    have h := LinearMap.finrank_range_le (τ q A χ).toLinearMap
    rwa [(LinearMap.range_eq_top (f := (τ q A χ).toLinearMap)).mpr hsurj, finrank_top] at h
  have heq : Module.finrank ℚ_[q] (ℚ_[q] ⊗[ℤ_[q]] (BA q A)) = Module.finrank ℚ_[q] T' :=
    le_antisymm ((finrank_tensor_tensor q A b).le.trans hcard) hle
  exact ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (f := (τ q A χ).toLinearMap) heq).mpr hsurj, hsurj⟩

private def τE [Module.Free ℤ A] [Module.Finite ℤ A] (hadj : Algebra.adjoin ℚ_[q] (Set.range χ) = ⊤)
    {ι : Type} [Fintype ι] (b : Module.Basis ι ℤ A) (hli : LinearIndependent ℚ_[q] (fun i => χ (b i))) :
    (ℚ_[q] ⊗[ℤ_[q]] (BA q A)) ≃ₐ[ℚ_[q]] T' :=
  AlgEquiv.ofBijective (τ q A χ) (τ_bijective q A χ hadj b hli)

private theorem τE_apply [Module.Free ℤ A] [Module.Finite ℤ A] (hadj : Algebra.adjoin ℚ_[q] (Set.range χ) = ⊤)
    {ι : Type} [Fintype ι] (b : Module.Basis ι ℤ A) (hli : LinearIndependent ℚ_[q] (fun i => χ (b i)))
    (w : ℚ_[q] ⊗[ℤ_[q]] (BA q A)) :
    τE q A χ hadj b hli w = τ q A χ w :=
  AlgEquiv.ofBijective_apply _ _ w

include hequiv in

private theorem equivariance (b : BA q A) (v : ℚ_[q] ⊗[ℤ_[q]] M) :
    ε ((ΘG q A M ρ b).baseChange ℚ_[q] v) = τ q A χ ((1 : ℚ_[q]) ⊗ₜ[ℤ_[q]] b) • ε v := by
  induction b using TensorProduct.induction_on generalizing v with
  | zero =>
    rw [map_zero (ΘG q A M ρ), LinearMap.baseChange_zero, LinearMap.zero_apply, map_zero ε,
      TensorProduct.tmul_zero, map_zero (τ q A χ), zero_smul]
  | tmul c s =>
    have hL : (ΘG q A M ρ (c ⊗ₜ[ℤ] s)).baseChange ℚ_[q] v =
        algebraMap ℤ_[q] ℚ_[q] c • (ρ s).baseChange ℚ_[q] v := by
      rw [ΘG_tmul_eq_smul, LinearMap.baseChange_smul, LinearMap.smul_apply, algebraMap_smul]
    have hR : τ q A χ ((1 : ℚ_[q]) ⊗ₜ[ℤ_[q]] (c ⊗ₜ[ℤ] s)) =
        algebraMap ℚ_[q] T' (algebraMap ℤ_[q] ℚ_[q] c) * χ s := by
      rw [τ_one_tmul, χ₀_tmul, IsScalarTower.algebraMap_apply ℤ_[q] ℚ_[q] T']
    rw [hL, hR, map_smul, hequiv, mul_smul, algebraMap_smul T']
  | add b₁ b₂ h₁ h₂ =>
    rw [map_add (ΘG q A M ρ), LinearMap.baseChange_add, LinearMap.add_apply, map_add ε, h₁, h₂,
      TensorProduct.tmul_add, map_add (τ q A χ), add_smul]

private theorem mulLeft_baseChange_apply (e : BA q A) (w : ℚ_[q] ⊗[ℤ_[q]] (BA q A)) :
    (LinearMap.mulLeft ℤ_[q] e).baseChange ℚ_[q] w =
      LinearMap.mulLeft ℚ_[q] ((1 : ℚ_[q]) ⊗ₜ[ℤ_[q]] e) w := by
  induction w using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | tmul a b =>
    rw [LinearMap.baseChange_tmul, LinearMap.mulLeft_apply, LinearMap.mulLeft_apply,
      Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

include hequiv in

private theorem finrank_range_ΘG_eq [Module.Free ℤ A] [Module.Finite ℤ A] [Module.Free ℤ_[q] M]
    [Module.Finite ℤ_[q] M] (hadj : Algebra.adjoin ℚ_[q] (Set.range χ) = ⊤) {ι : Type} [Fintype ι]
    (b : Module.Basis ι ℤ A) (hli : LinearIndependent ℚ_[q] (fun i => χ (b i))) (e : BA q A) :
    Module.finrank ℤ_[q] (LinearMap.range (ΘG q A M ρ e)) =
      2 * Module.finrank ℤ_[q] (LinearMap.range (LinearMap.mulLeft ℤ_[q] e)) := by
  haveI : Module.Finite ℚ_[q] T' :=
    Module.Finite.of_surjective (τ q A χ).toLinearMap (τ_surjective q A χ hadj)
  have hV : Module.finrank ℤ_[q] (LinearMap.range (ΘG q A M ρ e)) =
      Module.finrank ℚ_[q] (LinearMap.range ((ΘG q A M ρ e).baseChange ℚ_[q])) :=
    (finrank_range_baseChange (ΘG q A M ρ e)).symm
  have hB : Module.finrank ℤ_[q] (LinearMap.range (LinearMap.mulLeft ℤ_[q] e)) =
      Module.finrank ℚ_[q] (LinearMap.range ((LinearMap.mulLeft ℤ_[q] e).baseChange ℚ_[q])) :=
    (finrank_range_baseChange (LinearMap.mulLeft ℤ_[q] e)).symm
  have h1 : Module.finrank ℚ_[q]
        (LinearMap.range (diag q (τ q A χ ((1 : ℚ_[q]) ⊗ₜ[ℤ_[q]] e)))) =
      Module.finrank ℚ_[q] (LinearMap.range ((ΘG q A M ρ e).baseChange ℚ_[q])) :=
    finrank_range_eq_of_conj q ε ((ΘG q A M ρ e).baseChange ℚ_[q])
      (diag q (τ q A χ ((1 : ℚ_[q]) ⊗ₜ[ℤ_[q]] e))) fun v => by
      rw [diag_apply]; exact equivariance q A M ρ χ ε hequiv e v
  have h2 : Module.finrank ℚ_[q]
        (LinearMap.range (LinearMap.mulLeft ℚ_[q] (τ q A χ ((1 : ℚ_[q]) ⊗ₜ[ℤ_[q]] e)))) =
      Module.finrank ℚ_[q] (LinearMap.range ((LinearMap.mulLeft ℤ_[q] e).baseChange ℚ_[q])) :=
    finrank_range_eq_of_conj q (τE q A χ hadj b hli).toLinearEquiv
      ((LinearMap.mulLeft ℤ_[q] e).baseChange ℚ_[q])
      (LinearMap.mulLeft ℚ_[q] (τ q A χ ((1 : ℚ_[q]) ⊗ₜ[ℤ_[q]] e))) fun w => by
      rw [AlgEquiv.toLinearEquiv_apply, AlgEquiv.toLinearEquiv_apply, LinearMap.mulLeft_apply,
        τE_apply, τE_apply, mulLeft_baseChange_apply, LinearMap.mulLeft_apply, map_mul]
  have h3 := finrank_range_diag q (τ q A χ ((1 : ℚ_[q]) ⊗ₜ[ℤ_[q]] e))
  omega

end Core

private theorem map_sum_zsmul {R S : Type*} [Ring R] [Ring S] (f : R →+* S) {ι : Type*} (s : Finset ι)
    (g : ι → ℤ) (x : ι → R) : f (∑ j ∈ s, g j • x j) = ∑ j ∈ s, g j • f (x j) := by
  rw [map_sum]
  exact Finset.sum_congr rfl fun j _ => map_zsmul f (g j) (x j)

section StableChains

variable {R : Type*} [CommRing R]

private theorem pow_le_sup_pow_succ_of_stable {I P : Ideal R} {M : ℕ}
    (h : I ⊔ P ^ (M + 1) = I ⊔ P ^ M) (j : ℕ) : P ^ (M + j) ≤ I ⊔ P ^ (M + j + 1) := by
  have h1 : P ^ M ≤ I ⊔ P ^ (M + 1) := by
    rw [h]
    exact le_sup_right
  calc P ^ (M + j) = P ^ M * P ^ j := pow_add P M j
    _ ≤ (I ⊔ P ^ (M + 1)) * P ^ j := Ideal.mul_mono_left h1
    _ = I * P ^ j ⊔ P ^ (M + 1) * P ^ j := Ideal.sup_mul I (P ^ (M + 1)) (P ^ j)
    _ ≤ I ⊔ P ^ (M + j + 1) := by
        refine sup_le_sup Ideal.mul_le_left (le_of_eq ?_)
        rw [← pow_add, Nat.add_right_comm]

private theorem sup_pow_add_eq_of_stable {I P : Ideal R} {M : ℕ}
    (h : I ⊔ P ^ (M + 1) = I ⊔ P ^ M) (j : ℕ) : I ⊔ P ^ (M + j) = I ⊔ P ^ M := by
  induction j with
  | zero => rfl
  | succ j ih =>
    refine le_antisymm ?_ ?_
    · rw [← ih]
      exact sup_le_sup_left (Ideal.pow_le_pow_right (Nat.le_succ _)) I
    · rw [← ih]
      exact sup_le le_sup_left (pow_le_sup_pow_succ_of_stable h j)

variable {J : Type*} [AddCommGroup J] [Module R J]

private theorem mem_torsionBySet_ideal_iff (K : Ideal R) (x : J) :
    x ∈ Submodule.torsionBySet R J (K : Set R) ↔ K ≤ Ideal.torsionOf R J x := by
  rw [Submodule.mem_torsionBySet_iff]
  exact ⟨fun hx t ht => (Ideal.mem_torsionOf_iff x t).mpr (hx ⟨t, ht⟩),
    fun hK a => (Ideal.mem_torsionOf_iff x (a : R)).mp (hK a.2)⟩

private theorem torsionBySet_sup_pow_add_eq_of_stable {I P : Ideal R} {M : ℕ}
    (h : Submodule.torsionBySet R J ((I ⊔ P ^ (M + 1) : Ideal R) : Set R) =
      Submodule.torsionBySet R J ((I ⊔ P ^ M : Ideal R) : Set R)) (j : ℕ) :
    Submodule.torsionBySet R J ((I ⊔ P ^ (M + j) : Ideal R) : Set R) =
      Submodule.torsionBySet R J ((I ⊔ P ^ M : Ideal R) : Set R) := by
  induction j with
  | zero => rfl
  | succ j ih =>
    refine le_antisymm ?_ ?_
    · intro x hx
      rw [mem_torsionBySet_ideal_iff] at hx
      rw [← h, mem_torsionBySet_ideal_iff]
      refine sup_le (le_sup_left.trans hx) ?_
      rw [pow_succ, Ideal.mul_le]
      intro b hb a ha
      have hmul : (I ⊔ P ^ (M + j)) * P ≤ I ⊔ P ^ (M + (j + 1)) := by
        rw [Ideal.sup_mul, ← pow_succ]
        exact sup_le_sup Ideal.mul_le_left (le_of_eq rfl)
      have hax : a • x ∈ Submodule.torsionBySet R J ((I ⊔ P ^ (M + j) : Ideal R) : Set R) := by
        rw [mem_torsionBySet_ideal_iff]
        intro t ht
        rw [Ideal.mem_torsionOf_iff, smul_smul]
        exact (Ideal.mem_torsionOf_iff x (t * a)).mp (hx (hmul (Ideal.mul_mem_mul ht ha)))
      rw [ih, mem_torsionBySet_ideal_iff] at hax
      have hb' := hax (Ideal.mem_sup_right hb)
      rw [Ideal.mem_torsionOf_iff, smul_smul] at hb'
      exact (Ideal.mem_torsionOf_iff x (b * a)).mpr hb'
    · rw [← ih]
      apply Submodule.torsionBySet_le_torsionBySet_of_subset
      exact SetLike.coe_subset_coe.mpr
        (sup_le_sup_left (Ideal.pow_le_pow_right (Nat.le_succ _)) I)

end StableChains

section TateLevel

private theorem exists_proj_eq_of_forall_exists_nsmul_eq {p : ℕ} {M : Type} [AddCommGroup M]
    (hdiv : ∀ x : M, ∃ y : M, p • y = x) (n : ℕ) (m : M)
    (hm : m ∈ Submodule.torsionBy ℤ M ((p ^ n : ℕ) : ℤ)) :
    ∃ x : TateModule p M, TateModule.proj p M n x = m := by
  have hroot : ∀ (k : ℕ) (z : Submodule.torsionBy ℤ M ((p ^ k : ℕ) : ℤ)),
      ∃ w : Submodule.torsionBy ℤ M ((p ^ (k + 1) : ℕ) : ℤ), ((p : ℕ) : ℤ) • (w : M) = z := by
    intro k z
    obtain ⟨y, hy⟩ := hdiv (z : M)
    have hy' : ((p : ℕ) : ℤ) • y = (z : M) := by
      rw [natCast_zsmul]
      exact hy
    refine ⟨⟨y, ?_⟩, hy'⟩
    rw [Submodule.mem_torsionBy_iff, pow_succ, Nat.cast_mul, mul_smul, hy']
    exact (Submodule.mem_torsionBy_iff _ _).mp z.2
  choose next hnext using hroot
  refine ⟨⟨TateModule.liftFun next n ⟨m, hm⟩, TateModule.liftFun_mem hnext n ⟨m, hm⟩⟩, ?_⟩
  rw [TateModule.proj_apply]
  change TateModule.liftFun next n ⟨m, hm⟩ n = m
  rw [TateModule.liftFun_of_le le_rfl, TateModule.coe_liftAux_congr (Nat.sub_self n)]
  rfl

private theorem tateModule_eq_zero_of_pow_smul_eq_zero {p : ℕ} [Fact p.Prime] {M : Type}
    [AddCommGroup M] (v : ℕ) (x : TateModule p M) (hx : ((p : ℤ_[p]) ^ v) • x = 0) : x = 0 := by
  refine Subtype.ext (funext fun n => ?_)
  have h2 := congrArg (fun y : TateModule p M => (y : ℕ → M) (n + v)) hx
  rw [← Nat.cast_pow] at h2
  simp only [TateModule.natCast_padicInt_smul_apply, TateModule.coe_zero, Pi.zero_apply] at h2
  rw [TateModule.coe_zero, Pi.zero_apply, ← TateModule.compat_pow x n v, h2]

private theorem noZeroSMulDivisors_tateModule (p : ℕ) [Fact p.Prime] (M : Type) [AddCommGroup M] :
    NoZeroSMulDivisors ℤ_[p] (TateModule p M) := by
  refine ⟨fun {c x} hcx => ?_⟩
  by_cases hc : c = 0
  · exact Or.inl hc
  · refine Or.inr ?_
    rw [PadicInt.unitCoeff_spec hc, mul_smul] at hcx
    exact tateModule_eq_zero_of_pow_smul_eq_zero c.valuation x
      ((IsUnit.smul_eq_zero (PadicInt.unitCoeff hc).isUnit).mp hcx)

end TateLevel

variable (p q : ℕ) [Fact p.Prime] [Fact q.Prime]

private abbrev TL : Type := ↥(heckeLatticeAlgebra p ∅)

private abbrev B : Type := BA q (TL p)

private theorem hc : HeckeOperatorsCommuteBar p := ModularCurve.heckeOperatorsCommuteBar p

private def ψ : HeckeAlg →+* TL p := (latticeRestrictHom p ∅).toRingHom.comp (heckeEvalForms p 2)

private theorem heckeEvalForms_surjective (N : ℕ) [NeZero N] (k : ℤ) :
    Function.Surjective (CuspForm.heckeEvalForms N k) := by
  rintro ⟨x, hx⟩
  change x ∈ Algebra.adjoin ℤ (CuspForm.heckeGenerators N k ∅) at hx
  induction hx using Algebra.adjoin_induction with
  | mem y hy =>
    rcases hy with ⟨ℓ, hℓ, hℓN, -, rfl⟩ | ⟨ℓ, hℓN, hℓ, -, rfl⟩
    · exact ⟨ModularCurve.heckeGen ⟨ℓ, hℓ⟩,
        (CuspForm.heckeEvalForms_heckeGen_of_not_dvd (ℓ := ⟨ℓ, hℓ⟩) hℓN).trans rfl⟩
    · exact ⟨ModularCurve.heckeGen ⟨ℓ, hℓ⟩,
        (CuspForm.heckeEvalForms_heckeGen_of_dvd (q := ⟨ℓ, hℓ⟩) hℓN).trans rfl⟩
  | algebraMap r => exact ⟨MvPolynomial.C r, (CuspForm.heckeEvalForms_C N k r).trans rfl⟩
  | add y z _ _ hy hz =>
    obtain ⟨a, ha⟩ := hy
    obtain ⟨b, hb⟩ := hz
    exact ⟨a + b, (map_add (CuspForm.heckeEvalForms N k) a b).trans ((congrArg₂ (· + ·) ha hb).trans rfl)⟩
  | mul y z _ _ hy hz =>
    obtain ⟨a, ha⟩ := hy
    obtain ⟨b, hb⟩ := hz
    exact ⟨a * b, (map_mul (CuspForm.heckeEvalForms N k) a b).trans ((congrArg₂ (· * ·) ha hb).trans rfl)⟩

private theorem ψ_surjective : Function.Surjective (ψ p) := by
  intro y
  obtain ⟨z, rfl⟩ := CuspForm.latticeRestrictHom_surjective p ∅ y
  obtain ⟨x, rfl⟩ := heckeEvalForms_surjective p 2 z
  exact ⟨x, rfl⟩

private theorem ker_ψ : RingHom.ker (ψ p) = RingHom.ker (heckeEvalBar (hc p)) :=
  ModularCurve.ker_heckeEvalForms_latticeRestrict_eq_ker_heckeEvalBar p (hc p)

private def ι : HeckeAlg →+* B p q :=
  (Algebra.TensorProduct.includeRight : TL p →ₐ[ℤ] B p q).toRingHom.comp (ψ p)

private def 𝔪 : Ideal (B p q) := Ideal.map (ι p q) (eisensteinMaximalIdeal p q)

private theorem 𝔪_eq_map_map : 𝔪 p q = ((eisensteinMaximalIdeal p q).map (ψ p)).map (inclR q (TL p)) :=
  (Ideal.map_map (ψ p) (inclR q (TL p))).symm

omit [Fact q.Prime] in
private theorem natCast_mem_map_ψ : ((q : ℕ) : TL p) ∈ (eisensteinMaximalIdeal p q).map (ψ p) := by
  have h := Ideal.mem_map_of_mem (ψ p) (natCast_mem_eisensteinMaximalIdeal p q)
  rwa [map_natCast] at h

private def Spec (e : B p q) : Prop :=
  IsIdempotentElem e ∧ 1 - e ∈ 𝔪 p q ∧
    ∃ L : ℕ, Ideal.span {e} * 𝔪 p q ^ L ≤ Ideal.span {((q : ℕ) : B p q)}

private theorem exists_spec : ∃ e : B p q, Spec p q e := by
  haveI : IsAddTorsionFree (TL p) := heckeLatticeAlgebra.isAddTorsionFree p ∅
  obtain ⟨e, he, h1, L, hL⟩ :=
    exists_idempotent q (TL p) ((eisensteinMaximalIdeal p q).map (ψ p)) (natCast_mem_map_ψ p q)
  refine ⟨e, he, ?_, L, ?_⟩
  · rw [𝔪_eq_map_map]; exact h1
  · rw [𝔪_eq_map_map]; exact hL

private def eB (e : B p q) : Submodule ℤ_[q] (B p q) := LinearMap.range (LinearMap.mulLeft ℤ_[q] e)

private abbrev T : Type := TateModule q (JZero p)

private theorem ker_ψ_le_ker_tateHeckeRep :
    RingHom.ker (ψ p) ≤ RingHom.ker (tateHeckeRep q (JZero p)) := by
  intro t ht
  rw [ker_ψ, RingHom.mem_ker] at ht
  rw [RingHom.mem_ker]
  refine LinearMap.ext fun x => Subtype.ext (funext fun n => ?_)
  show t • (x : ℕ → JZero p) n = 0
  rw [heckeModuleBar_smul_def (hc p), ht, LinearMap.zero_apply]

private def ρT : TL p →+* Module.End ℤ_[q] (T p q) :=
  (ψ p).liftOfSurjective (ψ_surjective p)
    ⟨tateHeckeRep q (JZero p), ker_ψ_le_ker_tateHeckeRep p q⟩

private theorem ρT_ψ (t : HeckeAlg) : ρT p q (ψ p t) = tateHeckeRep q (JZero p) t :=
  (ψ p).liftOfSurjective_comp_apply (ψ_surjective p) _ t

private def Θ : B p q →ₐ[ℤ_[q]] Module.End ℤ_[q] (T p q) := ΘG q (TL p) (T p q) (ρT p q)

private theorem Θ_ι (t : HeckeAlg) : Θ p q (ι p q t) = tateHeckeRep q (JZero p) t :=
  (ΘG_one_tmul q (TL p) (T p q) (ρT p q) (ψ p t)).trans (ρT_ψ p q t)

private def eT (e : B p q) : Submodule ℤ_[q] (T p q) := LinearMap.range (Θ p q e)

private scoped instance instModuleFiniteT : Module.Finite ℤ_[q] (T p q) :=
  moduleFinite_padicInt_tateModule_jZero p q

private scoped instance instNoZeroSMulDivisorsT : NoZeroSMulDivisors ℤ_[q] (T p q) :=
  noZeroSMulDivisors_tateModule q (JZero p)

private scoped instance instModuleFreeT : Module.Free ℤ_[q] (T p q) := inferInstance

private abbrev VJ (k L : ℕ) : Submodule HeckeAlg (JZero p) :=
  heckeTorsion (JZero p)
    (Ideal.span {((q : ℕ) ^ k : HeckeAlg)} ⊔ (eisensteinMaximalIdeal p q) ^ L)

private abbrev RI (k L : ℕ) : Ideal (TL p) :=
  Ideal.span {((q : ℕ) ^ k : TL p)} ⊔
    (Ideal.map ((latticeRestrictHom p ∅).toRingHom.comp (heckeEvalForms p 2))
      (eisensteinMaximalIdeal p q)) ^ L

section QuotientBaseChange

private def incA (A : Type) [CommRing A] : A →+* BA q A :=
  (Algebra.TensorProduct.includeRight : A →ₐ[ℤ] BA q A).toRingHom

private theorem incA_apply {A : Type} [CommRing A] (t : A) :
    incA q A t = (1 : ℤ_[q]) ⊗ₜ[ℤ] t := rfl

private abbrev IB {A : Type} [CommRing A] (J : Ideal A) (k L : ℕ) : Ideal (BA q A) :=
  Ideal.span {((q : ℕ) : BA q A) ^ k} ⊔ (Ideal.map (incA q A) J) ^ L

private theorem sup_le_comap_IB {A : Type} [CommRing A] (J : Ideal A) (k L : ℕ) :
    Ideal.span {((q : ℕ) : A) ^ k} ⊔ J ^ L ≤ Ideal.comap (incA q A) (IB q J k L) := by
  refine sup_le ?_ ?_
  · rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap, map_pow,
      map_natCast]
    exact Submodule.mem_sup_left (Ideal.mem_span_singleton_self _)
  · rw [← Ideal.map_le_iff_le_comap, Ideal.map_pow]
    exact le_sup_right

private def quotTo {A : Type} [CommRing A] (J : Ideal A) (k L : ℕ) :
    A ⧸ (Ideal.span {((q : ℕ) : A) ^ k} ⊔ J ^ L) →+* (BA q A) ⧸ IB q J k L :=
  Ideal.quotientMap (IB q J k L) (incA q A) (sup_le_comap_IB q J k L)

private theorem quotTo_mk {A : Type} [CommRing A] (J : Ideal A) (k L : ℕ) (t : A) :
    quotTo q J k L (Ideal.Quotient.mk (Ideal.span {((q : ℕ) : A) ^ k} ⊔ J ^ L) t) =
      Ideal.Quotient.mk (IB q J k L) ((1 : ℤ_[q]) ⊗ₜ[ℤ] t) :=
  Ideal.quotientMap_mk

private def zqTo {A : Type} [CommRing A] (J : Ideal A) (k L : ℕ) :
    ℤ_[q] →+* A ⧸ (Ideal.span {((q : ℕ) : A) ^ k} ⊔ J ^ L) :=
  (ZMod.castHom (ringChar.dvd (show ((q ^ k : ℕ) : A ⧸ (Ideal.span {((q : ℕ) : A) ^ k} ⊔ J ^ L)) = 0 by
      rw [Nat.cast_pow, ← map_natCast (Ideal.Quotient.mk (Ideal.span {((q : ℕ) : A) ^ k} ⊔ J ^ L)),
        ← map_pow, Ideal.Quotient.eq_zero_iff_mem]
      exact Submodule.mem_sup_left (Ideal.mem_span_singleton_self _)))
    (A ⧸ (Ideal.span {((q : ℕ) : A) ^ k} ⊔ J ^ L))).comp (PadicInt.toZModPow k)

private theorem zqTo_apply {A : Type} [CommRing A] (J : Ideal A) (k L : ℕ) (a : ℤ_[q]) :
    zqTo q J k L a = ((a.appr k : ℕ) : A ⧸ (Ideal.span {((q : ℕ) : A) ^ k} ⊔ J ^ L)) := by
  rw [zqTo, RingHom.comp_apply, TateModule.toZModPow_eq_appr, map_natCast]

private def fromTensor {A : Type} [CommRing A] (J : Ideal A) (k L : ℕ) :
    BA q A →+* A ⧸ (Ideal.span {((q : ℕ) : A) ^ k} ⊔ J ^ L) :=
  (Algebra.TensorProduct.lift (zqTo q J k L).toIntAlgHom
    (Ideal.Quotient.mk (Ideal.span {((q : ℕ) : A) ^ k} ⊔ J ^ L)).toIntAlgHom
    (fun _ _ => Commute.all _ _)).toRingHom

private theorem fromTensor_tmul {A : Type} [CommRing A] (J : Ideal A) (k L : ℕ) (a : ℤ_[q])
    (t : A) :
    fromTensor q J k L (a ⊗ₜ[ℤ] t) =
      zqTo q J k L a * Ideal.Quotient.mk (Ideal.span {((q : ℕ) : A) ^ k} ⊔ J ^ L) t := by
  simp only [fromTensor, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, Algebra.TensorProduct.lift_tmul,
    RingHom.toIntAlgHom_apply]

private theorem fromTensor_one_tmul {A : Type} [CommRing A] (J : Ideal A) (k L : ℕ) (t : A) :
    fromTensor q J k L ((1 : ℤ_[q]) ⊗ₜ[ℤ] t) =
      Ideal.Quotient.mk (Ideal.span {((q : ℕ) : A) ^ k} ⊔ J ^ L) t := by
  rw [fromTensor_tmul, map_one, one_mul]

private theorem IB_le_ker_fromTensor {A : Type} [CommRing A] (J : Ideal A) (k L : ℕ) :
    IB q J k L ≤ RingHom.ker (fromTensor q J k L) := by
  refine sup_le ?_ ?_
  · rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, RingHom.mem_ker, map_pow,
      map_natCast, ← map_natCast (Ideal.Quotient.mk (Ideal.span {((q : ℕ) : A) ^ k} ⊔ J ^ L)),
      ← map_pow, Ideal.Quotient.eq_zero_iff_mem]
    exact Submodule.mem_sup_left (Ideal.mem_span_singleton_self _)
  · rw [← Ideal.map_pow, Ideal.map_le_iff_le_comap]
    intro x hx
    rw [Ideal.mem_comap, RingHom.mem_ker, incA_apply, fromTensor_one_tmul,
      Ideal.Quotient.eq_zero_iff_mem]
    exact Submodule.mem_sup_right hx

private def quotFrom {A : Type} [CommRing A] (J : Ideal A) (k L : ℕ) :
    (BA q A) ⧸ IB q J k L →+* A ⧸ (Ideal.span {((q : ℕ) : A) ^ k} ⊔ J ^ L) :=
  Ideal.Quotient.lift (IB q J k L) (fromTensor q J k L)
    (fun _ ha => RingHom.mem_ker.mp (IB_le_ker_fromTensor q J k L ha))

private theorem quotFrom_mk {A : Type} [CommRing A] (J : Ideal A) (k L : ℕ) (b : BA q A) :
    quotFrom q J k L (Ideal.Quotient.mk (IB q J k L) b) = fromTensor q J k L b :=
  Ideal.Quotient.lift_mk _ _ _

private theorem mk_natCast_appr_tmul {A : Type} [CommRing A] (J : Ideal A) (k L : ℕ) (a : ℤ_[q])
    (t : A) :
    Ideal.Quotient.mk (IB q J k L) (((a.appr k : ℕ) : ℤ_[q]) ⊗ₜ[ℤ] t) =
      Ideal.Quotient.mk (IB q J k L) (a ⊗ₜ[ℤ] t) := by
  rw [Ideal.Quotient.eq, ← TensorProduct.sub_tmul]
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.mp (PadicInt.appr_spec k a)
  refine Submodule.mem_sup_left (Ideal.mem_span_singleton.mpr ⟨(-c) ⊗ₜ[ℤ] t, ?_⟩)
  rw [← neg_sub, hc, ← mul_neg, Algebra.TensorProduct.natCast_def, Algebra.TensorProduct.tmul_pow,
    Algebra.TensorProduct.tmul_mul_tmul, one_pow, one_mul]

private def quotEquivQuotTensor {A : Type} [CommRing A] (J : Ideal A) (k L : ℕ) :
    A ⧸ (Ideal.span {((q : ℕ) : A) ^ k} ⊔ J ^ L) ≃+* (BA q A) ⧸ IB q J k L :=
  RingEquiv.ofRingHom (quotTo q J k L) (quotFrom q J k L)
    (Ideal.Quotient.ringHom_ext (RingHom.ext fun b => by
      simp only [RingHom.comp_apply, RingHom.id_apply, quotFrom_mk]
      induction b using TensorProduct.induction_on with
      | zero => simp only [map_zero]
      | tmul a t =>
        rw [fromTensor_tmul, zqTo_apply, map_mul, map_natCast, quotTo_mk,
          ← map_natCast (Ideal.Quotient.mk (IB q J k L)), ← map_mul,
          Algebra.TensorProduct.natCast_def, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul,
          mk_natCast_appr_tmul]
      | add x y hx hy =>
        rw [(fromTensor q J k L).map_add, (quotTo q J k L).map_add, hx, hy,
          (Ideal.Quotient.mk (IB q J k L)).map_add]))
    (Ideal.Quotient.ringHom_ext (RingHom.ext fun t => by
      simp only [RingHom.comp_apply, RingHom.id_apply, quotTo_mk, quotFrom_mk, fromTensor_one_tmul]))

private theorem natCard_quot_eq_natCard_quotTensor {A : Type} [CommRing A] (J : Ideal A)
    (k L : ℕ) :
    Nat.card (A ⧸ (Ideal.span {((q : ℕ) : A) ^ k} ⊔ J ^ L)) =
      Nat.card ((BA q A) ⧸ IB q J k L) :=
  Nat.card_congr (quotEquivQuotTensor q J k L).toEquiv

private abbrev tensorQuotCard (A : Type) [CommRing A] (M : Ideal (BA q A)) (k L : ℕ) : ℕ :=
  Nat.card ((BA q A) ⧸ (Ideal.span {((q : ℕ) : BA q A) ^ k} ⊔ M ^ L))

private theorem natCard_quot_eq_tensorQuotCard {R A : Type} [CommRing R] [CommRing A] (f : R →+* A)
    (P : Ideal R) (M : Ideal (BA q A)) (hM : M = Ideal.map ((incA q A).comp f) P) (k L : ℕ) :
    Nat.card (A ⧸ (Ideal.span {((q : ℕ) : A) ^ k} ⊔ (Ideal.map f P) ^ L)) =
      tensorQuotCard q A M k L := by
  subst hM
  rw [← Ideal.map_map]
  exact natCard_quot_eq_natCard_quotTensor q (Ideal.map f P) k L

end QuotientBaseChange

private theorem legD_surj (k : ℕ) (y : JZero p) (hy : (q : ℤ) ^ k • y = 0) :
    ∃ x : T p q, (x : ℕ → JZero p) k = y := by
  obtain ⟨x, hx⟩ := exists_proj_eq_of_forall_exists_nsmul_eq
    (fun z => JZero.divisible p q (Fact.out : q.Prime).ne_zero z) k y
    (by rw [Submodule.mem_torsionBy_iff, Nat.cast_pow]; exact hy)
  exact ⟨x, (TateModule.proj_apply k x).symm.trans hx⟩

omit [Fact q.Prime] in
private theorem legS_V (k M : ℕ) (h : VJ p q k (M + 1) = VJ p q k M) (L : ℕ) (hL : M ≤ L) :
    VJ p q k L = VJ p q k M := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hL
  exact torsionBySet_sup_pow_add_eq_of_stable h j

omit [Fact q.Prime] in
private theorem legS_R (k M : ℕ) (h : RI p q k (M + 1) = RI p q k M) (L : ℕ) (hL : M ≤ L) :
    RI p q k L = RI p q k M := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hL
  exact sup_pow_add_eq_of_stable h j

private theorem natCard_quotRI_eq_tensorQuotCard (k L : ℕ) :
    Nat.card (TL p ⧸ RI p q k L) = tensorQuotCard q (TL p) (𝔪 p q) k L :=
  natCard_quot_eq_tensorQuotCard q (ψ p) (eisensteinMaximalIdeal p q) (𝔪 p q) rfl k L

private theorem legΛ (e : B p q) (he : Spec p q e) (k : ℕ) :
    ∃ L₀ : ℕ, ∀ L, L₀ ≤ L →
      Nat.card (TL p ⧸ RI p q k L) = q ^ (k * Module.finrank ℤ_[q] (eB p q e)) := by
  obtain ⟨hidem, h1, Ls, hLs⟩ := he
  refine ⟨max 1 (Ls * k), fun L hL => ?_⟩
  exact (natCard_quotRI_eq_tensorQuotCard p q k L).trans
    (natCard_quotient_span_pow_sup_pow_eq_pow hidem h1 hLs k (le_trans (le_max_left _ _) hL)
      (le_trans (le_max_right _ _) hL))

private abbrev θT : B p q →+* Module.End ℤ_[q] (T p q) := (Θ p q).toRingHom

private theorem θT_mem_levelKer (k : ℕ) (b : B p q) {y : T p q} (hy : y ∈ levelKer q (T p q) k) :
    θT p q b y ∈ levelKer q (T p q) k :=
  map_mem_levelKer (θT p q b) k hy

private theorem proj_θT_ι (k : ℕ) (t : HeckeAlg) (x : T p q) :
    TateModule.proj q (JZero p) k (θT p q (ι p q t) x) = t • TateModule.proj q (JZero p) k x := by
  have h : θT p q (ι p q t) = Θ p q (ι p q t) := rfl
  rw [h, Θ_ι, TateModule.proj_apply, TateModule.proj_apply]
  exact ModularCurve.coe_tateHeckeRep_apply_apply q (JZero p) t x k

omit [Fact (Nat.Prime p)] in

private theorem proj_eq_zero_iff_mem_levelKer (k : ℕ) (x : T p q) :
    TateModule.proj q (JZero p) k x = 0 ↔ x ∈ levelKer q (T p q) k := by
  rw [TateModule.proj_eq_zero_iff, PadicInt.maximalIdeal_eq_span_p, Ideal.span_singleton_pow]

omit [Fact (Nat.Prime q)] in

private theorem mem_VJ_iff' (k L : ℕ) (y : JZero p) :
    y ∈ VJ p q k L ↔
      ∀ a : (↑(Ideal.span {((q : ℕ) ^ k : HeckeAlg)} ⊔ eisensteinMaximalIdeal p q ^ L) :
          Set HeckeAlg), (a : HeckeAlg) • y = 0 :=
  Submodule.mem_torsionBySet_iff _ _

omit [Fact (Nat.Prime q)] in
private theorem zsmul_eq_zero_of_mem_VJ (k L : ℕ) {y : JZero p} (hy : y ∈ VJ p q k L) :
    (q : ℤ) ^ k • y = 0 := by
  have hgen : ((q : ℕ) ^ k : HeckeAlg) ∈
      Ideal.span {((q : ℕ) ^ k : HeckeAlg)} ⊔ eisensteinMaximalIdeal p q ^ L :=
    Ideal.mem_sup_left (Ideal.mem_span_singleton_self _)
  have h := (mem_VJ_iff' p q k L y).1 hy ⟨((q : ℕ) ^ k : HeckeAlg), hgen⟩
  change ((q : ℕ) ^ k : HeckeAlg) • y = 0 at h
  have h' : (q ^ k : ℕ) • y = 0 := by exact_mod_cast h
  exact_mod_cast h'

omit [Fact (Nat.Prime q)] in
private theorem natCast_pow_smul_proj (k : ℕ) (x : T p q) :
    ((q : ℕ) ^ k : HeckeAlg) • TateModule.proj q (JZero p) k x = 0 := by
  have h := TateModule.torsionBy_proj k x
  rw [natCast_zsmul] at h
  exact_mod_cast h

private theorem proj_mem_VJ_iff (k L : ℕ) (x : T p q) :
    TateModule.proj q (JZero p) k x ∈ VJ p q k L ↔
      ∀ t ∈ eisensteinMaximalIdeal p q ^ L, θT p q (ι p q t) x ∈ levelKer q (T p q) k := by
  constructor
  · intro hmem t ht
    have ht' : t ∈ Ideal.span {((q : ℕ) ^ k : HeckeAlg)} ⊔ eisensteinMaximalIdeal p q ^ L :=
      Ideal.mem_sup_right ht
    have h := (mem_VJ_iff' p q k L _).1 hmem ⟨t, ht'⟩
    rw [← proj_eq_zero_iff_mem_levelKer, proj_θT_ι]
    exact h
  · intro h
    refine (mem_VJ_iff' p q k L _).2 ?_
    rintro ⟨a, ha⟩
    have ha' : a ∈ Ideal.span {((q : ℕ) ^ k : HeckeAlg)} ⊔ eisensteinMaximalIdeal p q ^ L := ha
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 ha'
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hy
    have hz' : z • TateModule.proj q (JZero p) k x = 0 := by
      rw [← proj_θT_ι, proj_eq_zero_iff_mem_levelKer]
      exact h z hz
    change (c * ((q : ℕ) ^ k : HeckeAlg) + z) • TateModule.proj q (JZero p) k x = 0
    rw [add_smul, hz', add_zero, mul_smul, natCast_pow_smul_proj, heckeModuleBar_smul_def (hc p),
      LinearMap.map_zero]

private theorem eT_eq_range (e : B p q) : eT p q e = LinearMap.range (θT p q e) := rfl

private theorem legJ (e : B p q) (he : Spec p q e) (k : ℕ) :
    ∃ L₀ : ℕ, ∀ L, L₀ ≤ L →
      Nat.card (VJ p q k L) = q ^ (k * Module.finrank ℤ_[q] (eT p q e)) := by
  obtain ⟨he1, he2, Ls, hLs⟩ := he
  refine ⟨max 1 (Ls * k), fun L hL => ?_⟩
  have hNs : ∀ (b : B p q) (y : T p q), y ∈ levelKer q (T p q) k → θT p q b y ∈ levelKer q (T p q) k :=
    fun b _ hy => θT_mem_levelKer p q k b hy
  have hP := fun x : T p q =>
    (proj_mem_VJ_iff p q k L x).trans
      ((forall_mem_map_pow_iff (ι p q) (θT p q) (levelKer q (T p q) k) hNs
          (eisensteinMaximalIdeal p q) L x).symm.trans
        (forall_apply_mem_iff_sub_mem (θT p q) he1 he2 hLs (le_trans (le_max_left _ _) hL)
          (le_trans (le_max_right _ _) hL) (levelKer q (T p q) k) hNs
          (natCast_pow_apply_mem_levelKer (θT p q) k) x))
  rw [eT_eq_range]
  exact natCard_subtype_eq_pow (θT p q) he1 k (TateModule.proj q (JZero p) k)
    (proj_eq_zero_iff_mem_levelKer p q k) (· ∈ VJ p q k L)
    (fun y hy => by
      obtain ⟨x, hx⟩ := legD_surj p q k y (zsmul_eq_zero_of_mem_VJ p q k L hy)
      exact ⟨x, by rw [TateModule.proj_apply]; exact hx⟩)
    hP

private theorem annihilator_eq_ker_ψ : Module.annihilator HeckeAlg (JZero p) = RingHom.ker (ψ p) := by
  ext t
  rw [Module.mem_annihilator, ker_ψ, RingHom.mem_ker]
  constructor
  · intro h
    exact LinearMap.ext fun x => by rw [← heckeModuleBar_smul_def (hc p)]; exact h x
  · intro h x
    rw [heckeModuleBar_smul_def (hc p), h, LinearMap.zero_apply]

private abbrev ιB : Type := Module.Free.ChooseBasisIndex ℤ (TL p)

private def bTL : Module.Basis (ιB p) ℤ (TL p) := Module.Free.chooseBasis ℤ (TL p)

private def tt (i : ιB p) : HeckeAlg := (ψ_surjective p (bTL p i)).choose

private theorem ψ_tt (i : ιB p) : ψ p (tt p i) = bTL p i := (ψ_surjective p (bTL p i)).choose_spec

private theorem linearIndependent_mk_tt :
    LinearIndependent ℤ
      (fun i => Ideal.Quotient.mk (Module.annihilator HeckeAlg (JZero p)) (tt p i)) := by
  refine linearIndependent_iff'.mpr fun s g hg i hi => ?_
  have h1 : Ideal.Quotient.mk (Module.annihilator HeckeAlg (JZero p)) (∑ j ∈ s, g j • tt p j) = 0 := by
    rw [map_sum_zsmul]; exact hg
  have h2 : ∑ j ∈ s, g j • tt p j ∈ RingHom.ker (ψ p) := by
    rw [← annihilator_eq_ker_ψ]
    exact Ideal.Quotient.eq_zero_iff_mem.mp h1
  have h3 : ∑ j ∈ s, g j • bTL p j = 0 := by
    have h := RingHom.mem_ker.mp h2
    rw [map_sum_zsmul] at h
    rw [← h]
    exact Finset.sum_congr rfl fun j _ => by rw [ψ_tt]
  exact linearIndependent_iff'.mp (bTL p).linearIndependent s g h3 i hi

section FactorTwo

variable {T' : Type} [CommRing T'] [Algebra ℚ_[q] T'] (φ : HeckeAlg →+* T')
  (ε : RationalTateModule q (JZero p) ≃ₗ[ℚ_[q]] (Fin 2 → T'))
  (hequiv : ∀ (t : HeckeAlg) (v : RationalTateModule q (JZero p)),
    ε (rationalHeckeRep q (JZero p) t v) = φ t • ε v)

set_option maxHeartbeats 1600000 in
include hequiv in

private theorem ker_ψ_le_ker : RingHom.ker (ψ p) ≤ RingHom.ker φ := by
  intro t ht
  have h0 : tateHeckeRep q (JZero p) t = 0 := ker_ψ_le_ker_tateHeckeRep p q ht
  have hR : rationalHeckeRep q (JZero p) t = 0 := by
    rw [rationalHeckeRep_apply, h0, LinearMap.baseChange_zero]
  have key := hequiv t (ε.symm (fun _ => 1))
  rw [hR, LinearMap.zero_apply, ε.map_zero, LinearEquiv.apply_symm_apply] at key
  have h1 := congr_fun key 0
  rw [Pi.zero_apply, Pi.smul_apply, smul_eq_mul, mul_one] at h1
  exact RingHom.mem_ker.mpr h1.symm

include hequiv in

private theorem exists_factor : ∃ χ : TL p →+* T', ∀ t, χ (ψ p t) = φ t :=
  ⟨(ψ p).liftOfSurjective (ψ_surjective p) ⟨φ, ker_ψ_le_ker p q φ ε hequiv⟩, fun t =>
    (ψ p).liftOfSurjective_comp_apply (ψ_surjective p) ⟨φ, ker_ψ_le_ker p q φ ε hequiv⟩ t⟩

include hequiv in

private theorem equivariant_factor (χ : TL p →+* T') (hχ : ∀ t, χ (ψ p t) = φ t) (s : TL p)
    (v : RationalTateModule q (JZero p)) : ε ((ρT p q s).baseChange ℚ_[q] v) = χ s • ε v := by
  obtain ⟨t, rfl⟩ := ψ_surjective p s
  rw [ρT_ψ, hχ, ← rationalHeckeRep_apply]
  exact hequiv t v

private theorem adjoin_range_factor (χ : TL p →+* T') (hχ : ∀ t, χ (ψ p t) = φ t)
    (hadj : Algebra.adjoin ℚ_[q] (Set.range φ) = ⊤) : Algebra.adjoin ℚ_[q] (Set.range χ) = ⊤ := by
  rw [eq_top_iff, ← hadj]
  refine Algebra.adjoin_mono ?_
  rintro _ ⟨t, rfl⟩
  exact ⟨ψ p t, hχ t⟩

include hequiv in

private theorem linearIndependent_factor (χ : TL p →+* T') (hχ : ∀ t, χ (ψ p t) = φ t) :
    LinearIndependent ℚ_[q] (fun i => χ (bTL p i)) := by
  have hli0 := ModularCurve.linearIndependent_rationalHeckeRep_of_linearIndependent p q
    (ModularCurve.heckeInputsAll p) (hc p) (tt p) (linearIndependent_mk_tt p)
  have hcb : ∀ i, χ (bTL p i) = φ (tt p i) := fun i =>
    (congrArg χ (ψ_tt p i)).symm.trans (hχ (tt p i))
  exact linearIndependent_of_conj q ε (fun i => χ (bTL p i))
    (fun i => rationalHeckeRep q (JZero p) (tt p i))
    (fun i v => (hequiv (tt p i) v).trans (congrArg (fun c : T' => c • ε v) (hcb i).symm)) hli0

include hequiv in
private theorem legC_of (hadj : Algebra.adjoin ℚ_[q] (Set.range φ) = ⊤) (e : B p q) :
    Module.finrank ℤ_[q] (eT p q e) = 2 * Module.finrank ℤ_[q] (eB p q e) := by
  letI : Algebra ℤ_[q] T' := ((algebraMap ℚ_[q] T').comp (algebraMap ℤ_[q] ℚ_[q])).toAlgebra
  haveI : IsScalarTower ℤ_[q] ℚ_[q] T' := IsScalarTower.of_algebraMap_eq' rfl
  obtain ⟨χ, hχ⟩ := exists_factor p q φ ε hequiv
  exact finrank_range_ΘG_eq q (TL p) (T p q) (ρT p q) χ ε (equivariant_factor p q φ ε hequiv χ hχ)
    (adjoin_range_factor p q φ χ hχ hadj) (bTL p) (linearIndependent_factor p q φ ε hequiv χ hχ) e

end FactorTwo

private theorem legC (e : B p q) : Module.finrank ℤ_[q] (eT p q e) = 2 * Module.finrank ℤ_[q] (eB p q e) := by
  have hx := ModularCurve.exists_heckeEquivariant_linearEquiv_rationalTateModule_jZero_fun_two p q
    (ModularCurve.heckeInputsAll p) (hc p)
  obtain ⟨T', _i1, _i2, φ, ε, hadj, hequiv⟩ := hx
  exact legC_of p q φ ε hequiv hadj e

private theorem total (k M : ℕ)
    (hV : VJ p q k (M + 1) = VJ p q k M) (hR : RI p q k (M + 1) = RI p q k M) :
    Nat.card (VJ p q k M) = Nat.card (TL p ⧸ RI p q k M) ^ 2 := by
  obtain ⟨e, he⟩ := exists_spec p q
  obtain ⟨L₁, hL₁⟩ := legJ p q e he k
  obtain ⟨L₂, hL₂⟩ := legΛ p q e he k
  have h1 := hL₁ (M + L₁ + L₂) (by omega)
  have h2 := hL₂ (M + L₁ + L₂) (by omega)
  rw [legS_V p q k M hV (M + L₁ + L₂) (by omega)] at h1
  rw [legS_R p q k M hR (M + L₁ + L₂) (by omega)] at h2
  rw [h1, h2, legC p q e, ← pow_mul]
  ring_nf

end TotN
p2m_reactivate "P2MW.S_ModularCurve_natCard_heckeTorsion_span_sup_eq_sq_natCard_heckeLatticeAlgebra_quotient.TotN"

theorem solution
    (p : ℕ) [Fact p.Prime] (q : ℕ) [Fact q.Prime] (hqp : q ≠ p) :
    letI := heckeModuleBar p
    ∀ k M : ℕ,
      heckeTorsion (JZero p)
          (Ideal.span {((q : ℕ) ^ k : HeckeAlg)} ⊔ (eisensteinMaximalIdeal p q) ^ (M + 1)) =
        heckeTorsion (JZero p)
          (Ideal.span {((q : ℕ) ^ k : HeckeAlg)} ⊔ (eisensteinMaximalIdeal p q) ^ M) →
      (Ideal.span {((q : ℕ) ^ k : ↥(heckeLatticeAlgebra p ∅))} ⊔
          (Ideal.map ((latticeRestrictHom p ∅).toRingHom.comp (heckeEvalForms p 2))
            (eisensteinMaximalIdeal p q)) ^ (M + 1)) =
        (Ideal.span {((q : ℕ) ^ k : ↥(heckeLatticeAlgebra p ∅))} ⊔
          (Ideal.map ((latticeRestrictHom p ∅).toRingHom.comp (heckeEvalForms p 2))
            (eisensteinMaximalIdeal p q)) ^ M) →
      Nat.card ↥(heckeTorsion (JZero p)
          (Ideal.span {((q : ℕ) ^ k : HeckeAlg)} ⊔ (eisensteinMaximalIdeal p q) ^ M)) =
        Nat.card (↥(heckeLatticeAlgebra p ∅) ⧸
          (Ideal.span {((q : ℕ) ^ k : ↥(heckeLatticeAlgebra p ∅))} ⊔
            (Ideal.map ((latticeRestrictHom p ∅).toRingHom.comp (heckeEvalForms p 2))
              (eisensteinMaximalIdeal p q)) ^ M)) ^ 2 := by
  have _ := hqp
  exact fun k M hV hR => TotN.total p q k M hV hR

end
p2m_reactivate "P2MW.S_ModularCurve_natCard_heckeTorsion_span_sup_eq_sq_natCard_heckeLatticeAlgebra_quotient.TotN"

end S_ModularCurve_natCard_heckeTorsion_span_sup_eq_sq_natCard_heckeLatticeAlgebra_quotient
end P2MW
export P2MW.S_ModularCurve_natCard_heckeTorsion_span_sup_eq_sq_natCard_heckeLatticeAlgebra_quotient (solution)
