-- Prove2me | solution 1 for ModularCurve.exists_heckeEquivariant_linearEquiv_rationalTateModule_jZero_fun_two
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/57477b7d-9545-5348-b380-92ca092ea8c6

import Mathlib
import Definitions.Def_ModularCurve_JZeroTateModule
import Definitions.Def_ModularCurve_HeckeModule
import Definitions.Def_ModularCurve_HeckeInputsAll
import Definitions.Def_ModularCurve_PeriodLattice
import Definitions.Def_CuspForm_HeckeAlgebra
import Definitions.Def_FLTPrelim_Modularity
import Theorems.Thm_ModularCurve_periodLatticeHeckeStable
import Theorems.Thm_ModularCurve_exists_basis_periodLattice_linearIndependent_real_span_eq_top
import Theorems.Thm_CuspForm_exists_basis_repr_heckeTLin_heckeULin_mem_range_ratCast
import Theorems.Thm_ModularCurve_exists_heckeEquivariant_linearEquiv_tateModule_jZero_padicInt_tensor_periodLattice
import Theorems.Thm_CuspForm_eq_zero_of_mem_span_heckeAlgebra_of_forall_qCoeff_one_eq_zero
import Theorems.Thm_CuspForm_finrank_span_heckeAlgebra_eq_finrank
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_heckeEquivariant_linearEquiv_rationalTateModule_jZero_fun_two
p2m_attr_erase "instance" "ModularCurve.CuspSpace.instNonempty ModularCurve.CuspSpace.instSubsingletonOfOne ModularCurve.CuspSpace.instFinite ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instAlgebraIntermediateFieldLaurent ModularCurve.instIsScalarTowerKaehlerIntermediateFieldLaurent ModularCurve.instIsScalarTowerIntermediateFieldLaurent ModularCurve.instModuleKaehlerIntermediateFieldLaurent AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois ModularCurve.Gamma0Pair.isElliptic ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.B3.instIsElliptic_goodModel AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar"
p2m_attr_erase "instance" "AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.instIsScalarTowerJAdjoin HeckeEis.instFiniteIndexHeckeUpper ModularCurve.Period.parabolicHoms_int_moduleFinite ModularCurve.Period.instGroupFG_SL2Z ModularCurve.Period.instIsNoetherian_addHom_int ModularCurve.Period.instGroupFG_Gamma0 FLT.Gamma0FundamentalSet.instContinuousConstSMulSpecialLinearGroupFinOfNatNatIntUpperHalfPlane_definitions FLT.HyperbolicMeasure.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatIntUpperHalfPlaneVolume_definitions FLT.HyperbolicMeasure.instIsOpenPosMeasureUpperHalfPlaneVolume_definitions FLT.L2ProductionInstance.isFiniteMeasure_gamma0 FLT.L2ProductionInstance.countable_SL2Z FLT.L2ProductionInstance.countable_quotient FLT.L2ProductionInstance.nontrivial_gamma0L2 HeckeEis.instModuleCoeffH1par HeckeEis.instAddCommGroupCoeffH1par"
p2m_attr_erase "simp" "ModularCurve.Period.IsEquivariantPrimitive.periodHom_apply ModularCurve.Period.IsEquivariantPrimitive.period_one ModularCurve.cuspCount_one ModularCurve.CuspSpace.cuspDenomAux_infty ModularCurve.CuspSpace.cuspDenomAux_coe ModularCurve.CuspSpace.cuspDenom_mk_zero ModularCurve.CuspSpace.cuspDenom_mk_infty ModularCurve.mapGL_apply_coe ModularCurve.ratPoint_one_zero ModularCurve.ratPoint_zero_right ModularCurve.CuspSpace.fromCoset_mk ModularCurve.CuspSpace.cuspDenom_mk ModularCurve.ratPoint_zero_one ModularCurve.ProjectiveLine.map_mk ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.qEulerFun_coeff ModularCurve.diffQExp_D ModularCurve.qEulerOn_apply ModularCurve.qEuler_coeff AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord ModularCurve.coe_cuspidalDivisor₀ ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff"
p2m_attr_erase "simp" "ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.gamma0PairMap_gen ModularCurve.moduliPointMapRingHom_mk ModularCurve.Gamma0Pair.mk.injEq ModularCurve.ModuliPoint.j_mk ModularCurve.Gamma0Pair.mk.sizeOf_spec ModularCurve.gamma0PairMap_toCurve WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero WeierstrassCurve.ratPointHom_apply WeierstrassCurve.ratPointMap_zero ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.jqNModC_one WeierstrassCurve.veluX_empty WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero"
p2m_attr_erase "simp" "WeierstrassCurve.veluY_empty WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal"
p2m_attr_erase "simp" "AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial"
p2m_attr_erase "simp" "WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace"
p2m_attr_erase "simp" "AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply HahnSeries.ramScale_apply AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen"
p2m_attr_erase "simp" "ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar WeierstrassCurve.veluPointMap2_zero AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule ModularCurve.Period.jConjMat_apply_zero_one ModularCurve.Period.jConjSL_coe ModularCurve.Period.jConjMat_apply_one_zero ModularCurve.Period.jConjMat_apply_one_one ModularCurve.Period.jConjGamma0_coe ModularCurve.Period.charInvolution_apply ModularCurve.Period.jConjMat_apply_zero_zero HeckeEis.heckeConjMat_apply_one_one HeckeEis.coe_heckeConjSL HeckeEis.mem_heckeUpperSL HeckeEis.resHom_apply"
p2m_attr_erase "simp" "HeckeEis.heckeConjMat_apply_zero_one HeckeEis.coe_transferAux HeckeEis.coe_heckeConj HeckeEis.alphaMat_apply_one_one HeckeEis.heckeConjMat_apply_one_zero HeckeEis.alphaMat_apply_zero_one HeckeEis.pullbackHom_apply HeckeEis.alphaMat_apply_one_zero HeckeEis.alphaMat_apply_zero_zero HeckeEis.heckeConjMat_apply_zero_zero PowerSeries.coeff_heckeV PowerSeries.coeff_heckeU AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq ModularCurve.ComplexPlaceDictionary.mk.injEq ModularCurve.ComplexPlaceDictionary.mk.sizeOf_spec FLT.TruncatedDomainPartition.unipotentDiagonalSum_zero HeckeEis.coeffCoboundaryMap_apply"

noncomputable section

open Module
open scoped Matrix

namespace W1C

variable {E : Type*} [AddCommGroup E] [Module ℂ E]

def mulI : E →ₗ[ℝ] E := (LinearMap.lsmul ℂ E Complex.I).restrictScalars ℝ

@[scoped simp] theorem mulI_apply (x : E) : mulI x = Complex.I • x := rfl

theorem mulI_injective : Function.Injective (mulI : E →ₗ[ℝ] E) := by
  intro x y h
  simp only [mulI_apply] at h
  have := congrArg (fun z => Complex.I • z) h
  simpa [smul_smul] using this

theorem complex_smul_eq (z : ℂ) (x : E) : z • x = z.re • x + z.im • (Complex.I • x) := by
  conv_lhs => rw [← Complex.re_add_im z]
  rw [add_smul, mul_smul, Complex.coe_smul, Complex.coe_smul]

theorem mem_sup_of_mem_span_complex (S : Set E) {x : E} (hx : x ∈ Submodule.span ℂ S) :
    x ∈ Submodule.span ℝ S ⊔ (Submodule.span ℝ S).map mulI := by
  induction hx using Submodule.span_induction with
  | mem y hy => exact Submodule.mem_sup_left (Submodule.subset_span hy)
  | zero => exact Submodule.zero_mem _
  | add y z _ _ hy hz => exact Submodule.add_mem _ hy hz
  | smul c y _ hy =>
    obtain ⟨u, hu, v, hv, rfl⟩ := Submodule.mem_sup.mp hy
    obtain ⟨v', hv', rfl⟩ := Submodule.mem_map.mp hv
    rw [smul_add, complex_smul_eq, complex_smul_eq c (mulI v')]
    refine Submodule.add_mem _ (Submodule.add_mem _ ?_ ?_) (Submodule.add_mem _ ?_ ?_)
    · exact Submodule.mem_sup_left (Submodule.smul_mem _ _ hu)
    · exact Submodule.mem_sup_right ⟨c.im • u, Submodule.smul_mem _ _ hu, by simp⟩
    · exact Submodule.mem_sup_right ⟨c.re • v', Submodule.smul_mem _ _ hv', by simp⟩
    · refine Submodule.mem_sup_left ?_
      have : c.im • (Complex.I • (mulI v' : E)) = (-c.im) • v' := by
        simp [smul_smul, neg_smul]
      rw [this]
      exact Submodule.smul_mem _ _ hv'

theorem restrictScalars_span_complex (S : Set E) :
    (Submodule.span ℂ S).restrictScalars ℝ = Submodule.span ℝ S ⊔ (Submodule.span ℝ S).map mulI := by
  refine le_antisymm (fun x hx => mem_sup_of_mem_span_complex S hx) ?_
  refine sup_le ?_ ?_
  · exact (Submodule.span_le_restrictScalars ℝ ℂ S)
  · rintro _ ⟨y, hy, rfl⟩
    have hy' : y ∈ Submodule.span ℂ S := Submodule.span_le_restrictScalars ℝ ℂ S hy
    exact Submodule.smul_mem _ Complex.I hy'

end W1C
p2m_reactivate "P2MW.S_ModularCurve_exists_heckeEquivariant_linearEquiv_rationalTateModule_jZero_fun_two.W1C"

namespace W1A

open ModularCurve W1C

variable (N : ℕ) [NeZero N]

abbrev V : Type := CuspForm (CongruenceSubgroup.Gamma0 N) 2
abbrev D : Type := Module.Dual ℂ (V N)

theorem one_mem_strictPeriods :
    (1 : ℝ) ∈ (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
  simp

def a1 : D N where
  toFun f := ModularFormClass.qCoeff (⇑f) 1
  map_add' f g := by
    simp only [ModularFormClass.qCoeff]
    rw [show (⇑(f + g) : UpperHalfPlane → ℂ) = ⇑f + ⇑g from rfl,
      ModularForm.qExpansion_add one_pos (one_mem_strictPeriods N) f g, map_add]
  map_smul' c f := by
    simp only [ModularFormClass.qCoeff, RingHom.id_apply, smul_eq_mul]
    rw [show (⇑(c • f) : UpperHalfPlane → ℂ) = c • ⇑f from rfl,
      ModularForm.qExpansion_smul one_pos (one_mem_strictPeriods N) c f]
    simp

@[scoped simp] theorem a1_apply (f : V N) : a1 N f = ModularFormClass.qCoeff (⇑f) 1 := rfl

def Θ : Module.End ℂ (V N) →ₗ[ℂ] D N where
  toFun S := (a1 N).comp S
  map_add' S S' := LinearMap.comp_add _ _ _
  map_smul' c S := LinearMap.comp_smul _ _ _

@[scoped simp] theorem Θ_apply (S : Module.End ℂ (V N)) (f : V N) : Θ N S f = a1 N (S f) := rfl

theorem Θ_eq_dualHeckeRep (t : HeckeAlg) : Θ N (cuspHeckeRep N t) = dualHeckeRep N t (a1 N) := rfl

abbrev C : Submodule ℂ (Module.End ℂ (V N)) :=
  Submodule.span ℂ (CuspForm.heckeAlgebra N 2 (∅ : Set ℕ) : Set (Module.End ℂ (V N)))

theorem C_eq_span_range : C N = Submodule.span ℂ (Set.range (cuspHeckeRep N)) := by
  rw [range_cuspHeckeRep]

section Generation

variable
  (hB3a : ∀ T : Module.End ℂ (V N), T ∈ C N →
    (∀ f : V N, ModularFormClass.qCoeff (⇑(T f)) 1 = 0) → T = 0)
  (hB3c : finrank ℂ (C N) = finrank ℂ (V N))
  [FiniteDimensional ℂ (V N)]

include hB3a hB3c

theorem map_C_Θ_eq_top : (C N).map (Θ N) = ⊤ := by
  have hinj : Function.Injective ((Θ N).domRestrict (C N)) := by
    intro S S' h
    have h' : Θ N (S : Module.End ℂ (V N)) = Θ N S' := h
    have hd : Θ N ((S : Module.End ℂ (V N)) - S') = 0 := by rw [map_sub, h', sub_self]
    have h0 := hB3a ((S : Module.End ℂ (V N)) - S') (Submodule.sub_mem _ S.2 S'.2) (fun f => by
      have := congrArg (fun φ : D N => φ f) hd
      simpa only [Θ_apply, a1_apply, LinearMap.zero_apply] using this)
    exact Subtype.ext (sub_eq_zero.mp h0)
  apply Submodule.eq_top_of_finrank_eq
  rw [← LinearMap.range_domRestrict]
  rw [LinearMap.finrank_range_of_inj hinj, hB3c]
  exact (Subspace.dual_finrank_eq).symm

theorem span_range_dualHeckeRep_a1 :
    Submodule.span ℂ (Set.range fun t : HeckeAlg => dualHeckeRep N t (a1 N)) = ⊤ := by
  apply top_le_iff.mp
  rw [← map_C_Θ_eq_top N hB3a hB3c, C_eq_span_range, Submodule.map_span, Submodule.span_le]
  rintro _ ⟨_, ⟨t, rfl⟩, rfl⟩
  exact Submodule.subset_span ⟨t, (Θ_eq_dualHeckeRep N t).symm⟩

def u : Fin 2 → D N := ![a1 N, Complex.I • a1 N]

theorem span_real_eq_top :
    Submodule.span ℝ (Set.range fun ta : HeckeAlg × Fin 2 => dualHeckeRep N ta.1 (u N ta.2)) = ⊤ := by
  apply top_le_iff.mp
  intro δ _
  have hδ : δ ∈ Submodule.span ℂ (Set.range fun t : HeckeAlg => dualHeckeRep N t (a1 N)) := by
    rw [span_range_dualHeckeRep_a1 N hB3a hB3c]; trivial
  have h := mem_sup_of_mem_span_complex _ hδ
  set S := Submodule.span ℝ (Set.range fun ta : HeckeAlg × Fin 2 => dualHeckeRep N ta.1 (u N ta.2))
  have h1 : Submodule.span ℝ (Set.range fun t : HeckeAlg => dualHeckeRep N t (a1 N)) ≤ S := by
    apply Submodule.span_mono
    rintro _ ⟨t, rfl⟩
    exact ⟨(t, 0), by simp [u]⟩
  have h2 : (Submodule.span ℝ (Set.range fun t : HeckeAlg => dualHeckeRep N t (a1 N))).map mulI ≤ S := by
    rw [Submodule.map_span, Submodule.span_le]
    rintro _ ⟨_, ⟨t, rfl⟩, rfl⟩
    refine Submodule.subset_span ⟨(t, 1), ?_⟩
    simp [u, map_smul]
  exact sup_le h1 h2 h

end Generation
p2m_reactivate "P2MW.S_ModularCurve_exists_heckeEquivariant_linearEquiv_rationalTateModule_jZero_fun_two.W1C"

section Lattice

variable {n : ℕ} (b : Module.Basis (Fin n) ℤ (periodLattice N))
  (hli : LinearIndependent ℝ (fun i => ((b i : periodLattice N) : D N)))
  (hsp : Submodule.span ℝ (Set.range fun i => ((b i : periodLattice N) : D N)) = ⊤)
  (hst : PeriodLatticeHeckeStable N)

def bℝ : Module.Basis (Fin n) ℝ (D N) := Module.Basis.mk hli hsp.ge

theorem bℝ_apply (i : Fin n) : bℝ N b hli hsp i = ((b i : periodLattice N) : D N) := by
  rw [bℝ, Module.Basis.mk_apply]

theorem bℝ_repr_coe (x : periodLattice N) (i : Fin n) :
    (bℝ N b hli hsp).repr (x : D N) i = (b.repr x i : ℝ) := by
  have hx : (x : D N) = ∑ j, ((b.repr x j : ℤ) : ℝ) • bℝ N b hli hsp j := by
    conv_lhs => rw [← b.sum_repr x]
    rw [Submodule.coe_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Submodule.coe_smul, bℝ_apply, Int.cast_smul_eq_zsmul]
  rw [hx, (bℝ N b hli hsp).repr_sum_self]

def Mℤ : HeckeAlg →+* Matrix (Fin n) (Fin n) ℤ :=
  (LinearMap.toMatrixAlgEquiv b).toRingEquiv.toRingHom.comp (periodLatticeHeckeEnd N)

theorem Mℤ_apply (t : HeckeAlg) : Mℤ N b t = LinearMap.toMatrix b b (periodLatticeHeckeEnd N t) := rfl

include hst in

theorem toMatrix_dualHeckeRep (t : HeckeAlg) :
    LinearMap.toMatrix (bℝ N b hli hsp) (bℝ N b hli hsp) ((dualHeckeRep N t).restrictScalars ℝ) =
      (Mℤ N b t).map (Int.cast : ℤ → ℝ) := by
  ext i j
  rw [LinearMap.toMatrix_apply, LinearMap.restrictScalars_apply, bℝ_apply,
    ← coe_periodLatticeHeckeEnd_apply hst, bℝ_repr_coe, Matrix.map_apply, Mℤ_apply,
    LinearMap.toMatrix_apply]

include hst in
theorem equivFun_dualHeckeRep (t : HeckeAlg) (δ : D N) :
    (bℝ N b hli hsp).equivFun (dualHeckeRep N t δ) =
      (Mℤ N b t).map (Int.cast : ℤ → ℝ) *ᵥ (bℝ N b hli hsp).equivFun δ := by
  have h := LinearMap.toMatrix_mulVec_repr (bℝ N b hli hsp) (bℝ N b hli hsp)
    ((dualHeckeRep N t).restrictScalars ℝ) δ
  rw [toMatrix_dualHeckeRep N b hli hsp hst] at h
  simp only [Module.Basis.equivFun_apply]
  exact h.symm

include hli hsp hst in

theorem exists_w
    (hgen : Submodule.span ℝ (Set.range fun ta : HeckeAlg × Fin 2 => dualHeckeRep N ta.1 (u N ta.2)) = ⊤) :
    ∃ w : Fin 2 → Fin n → ℝ,
      Submodule.span ℝ (Set.range fun ta : HeckeAlg × Fin 2 =>
        (Mℤ N b ta.1).map (Int.cast : ℤ → ℝ) *ᵥ w ta.2) = ⊤ := by
  refine ⟨fun a => (bℝ N b hli hsp).equivFun (u N a), ?_⟩
  have : (Set.range fun ta : HeckeAlg × Fin 2 => (Mℤ N b ta.1).map (Int.cast : ℤ → ℝ) *ᵥ
      (bℝ N b hli hsp).equivFun (u N ta.2)) =
      (bℝ N b hli hsp).equivFun '' (Set.range fun ta : HeckeAlg × Fin 2 => dualHeckeRep N ta.1 (u N ta.2)) := by
    rw [← Set.range_comp]
    congr 1
    funext ta
    simp only [Function.comp_apply]
    exact (equivFun_dualHeckeRep N b hli hsp hst ta.1 (u N ta.2)).symm
  rw [this]
  change Submodule.span ℝ (((bℝ N b hli hsp).equivFun : D N →ₗ[ℝ] (Fin n → ℝ)) '' _) = ⊤
  rw [Submodule.span_image, hgen, Submodule.map_top, LinearMap.range_eq_top]
  exact (bℝ N b hli hsp).equivFun.surjective

end Lattice
p2m_reactivate "P2MW.S_ModularCurve_exists_heckeEquivariant_linearEquiv_rationalTateModule_jZero_fun_two.W1C"

end W1A
p2m_reactivate "P2MW.S_ModularCurve_exists_heckeEquivariant_linearEquiv_rationalTateModule_jZero_fun_two.W1C P2MW.S_ModularCurve_exists_heckeEquivariant_linearEquiv_rationalTateModule_jZero_fun_two.W1A"

namespace W1A

open ModularCurve W1C

variable (N : ℕ) [NeZero N]

section Dimension

variable {n : ℕ} (b : Module.Basis (Fin n) ℤ (periodLattice N))
  (hli : LinearIndependent ℝ (fun i => ((b i : periodLattice N) : D N)))
  (hsp : Submodule.span ℝ (Set.range fun i => ((b i : periodLattice N) : D N)) = ⊤)
  (hst : PeriodLatticeHeckeStable N)
  [FiniteDimensional ℂ (V N)]

theorem dualMap_injective' : Function.Injective
    (fun S : Module.End ℂ (V N) => (S.dualMap : Module.End ℂ (D N))) := by
  intro S S' h
  refine LinearMap.ext fun f => ?_
  have : ∀ φ : D N, φ (S f) = φ (S' f) := fun φ => by
    have := congrArg (fun T : Module.End ℂ (D N) => T φ f) h
    simpa using this
  have h0 : ∀ φ : D N, φ (S f - S' f) = 0 := fun φ => by rw [map_sub, this φ, sub_self]
  exact sub_eq_zero.mp ((Module.forall_dual_apply_eq_zero_iff ℂ _).mp h0)

def Ψ₁ : Module.End ℂ (V N) →ₗ[ℝ] Matrix (Fin n) (Fin n) ℝ where
  toFun S := LinearMap.toMatrix (bℝ N b hli hsp) (bℝ N b hli hsp) ((S.dualMap).restrictScalars ℝ)
  map_add' S S' := by
    have : (S + S').dualMap = S.dualMap + S'.dualMap := map_add (Module.Dual.transpose (R := ℂ)) S S'
    rw [this, LinearMap.restrictScalars_add, map_add]
  map_smul' r S := by
    ext i j
    simp only [LinearMap.toMatrix_apply, LinearMap.restrictScalars_apply, LinearMap.dualMap_apply',
      RingHom.id_apply, Matrix.smul_apply, smul_eq_mul]
    have : (bℝ N b hli hsp j).comp (r • S) = r • ((bℝ N b hli hsp j).comp S) := by
      ext f; simp
    rw [this, map_smul, Finsupp.smul_apply, smul_eq_mul]

theorem Ψ₁_injective : Function.Injective (Ψ₁ N b hli hsp) := by
  intro S S' h
  apply dualMap_injective' N
  have h' := (LinearMap.toMatrix (bℝ N b hli hsp) (bℝ N b hli hsp)).injective h
  exact LinearMap.restrictScalars_injective ℝ h'

include hst in
theorem Ψ₁_cuspHeckeRep (t : HeckeAlg) :
    Ψ₁ N b hli hsp (cuspHeckeRep N t) = (Mℤ N b t).map (Int.cast : ℤ → ℝ) := by
  show LinearMap.toMatrix (bℝ N b hli hsp) (bℝ N b hli hsp) ((dualHeckeRep N t).restrictScalars ℝ) = _
  exact toMatrix_dualHeckeRep N b hli hsp hst t

abbrev RVℝ : Submodule ℝ (Module.End ℂ (V N)) := Submodule.span ℝ (Set.range (cuspHeckeRep N))

include hli hsp hst in
theorem finrank_span_MK_real_eq :
    finrank ℝ (Submodule.span ℝ (Set.range fun t : HeckeAlg => (Mℤ N b t).map (Int.cast : ℤ → ℝ))) =
      finrank ℝ (RVℝ N) := by
  have hr : (Set.range fun t : HeckeAlg => (Mℤ N b t).map (Int.cast : ℤ → ℝ)) =
      Set.range ((Ψ₁ N b hli hsp) ∘ (cuspHeckeRep N)) := by
    congr 1
    funext t
    exact (Ψ₁_cuspHeckeRep N b hli hsp hst t).symm
  have : Submodule.span ℝ (Set.range fun t : HeckeAlg => (Mℤ N b t).map (Int.cast : ℤ → ℝ)) =
      (RVℝ N).map (Ψ₁ N b hli hsp) := by
    rw [hr, Set.range_comp, Submodule.map_span]
  rw [this]
  exact (LinearEquiv.finrank_eq (Submodule.equivMapOfInjective (Ψ₁ N b hli hsp)
    (Ψ₁_injective N b hli hsp) (RVℝ N))).symm

end Dimension
p2m_reactivate "P2MW.S_ModularCurve_exists_heckeEquivariant_linearEquiv_rationalTateModule_jZero_fun_two.W1C P2MW.S_ModularCurve_exists_heckeEquivariant_linearEquiv_rationalTateModule_jZero_fun_two.W1A"

section Rational

variable {m : ℕ} (β : Module.Basis (Fin m) ℂ (V N))
  (hT : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (i j : Fin m),
    β.repr (CuspForm.heckeTLin 2 hℓ hℓN (β i)) j ∈ Set.range ((↑) : ℚ → ℂ))
  (hU : ∀ (q : ℕ) (hq : q.Prime) (hqN : q ∣ N) (i j : Fin m),
    β.repr (CuspForm.heckeULin 2 hqN (β i)) j ∈ Set.range ((↑) : ℚ → ℂ))

def A : HeckeAlg →+* Matrix (Fin m) (Fin m) ℂ :=
  (LinearMap.toMatrixAlgEquiv β).toRingEquiv.toRingHom.comp (cuspHeckeRep N)

theorem A_apply (t : HeckeAlg) : A N β t = LinearMap.toMatrix β β (cuspHeckeRep N t) := rfl

abbrev RatMat : Subring (Matrix (Fin m) (Fin m) ℂ) := ((Rat.castHom ℂ).mapMatrix).range

theorem mem_RatMat_iff (B : Matrix (Fin m) (Fin m) ℂ) :
    B ∈ RatMat (m := m) ↔ ∀ i j, B i j ∈ Set.range ((↑) : ℚ → ℂ) := by
  constructor
  · rintro ⟨B', rfl⟩ i j
    exact ⟨B' i j, rfl⟩
  · intro h
    choose g hg using h
    refine ⟨Matrix.of g, ?_⟩
    ext i j
    simp [hg]

include hT hU in
theorem A_heckeGen_mem (ℓ : Nat.Primes) : A N β (heckeGen ℓ) ∈ RatMat (m := m) := by
  rw [mem_RatMat_iff]
  intro i j
  rw [A_apply, cuspHeckeRep_heckeGen, LinearMap.toMatrix_apply]
  by_cases h : (ℓ : ℕ) ∣ N
  · rw [cuspHeckeGen_of_dvd N ℓ h]
    exact hU ℓ ℓ.prop h j i
  · rw [cuspHeckeGen_of_not_dvd N ℓ h]
    exact hT ℓ ℓ.prop h j i

include hT hU in
theorem A_mem (t : HeckeAlg) : A N β t ∈ RatMat (m := m) := by
  induction t using MvPolynomial.induction_on with
  | C a =>
    rw [← MvPolynomial.algebraMap_eq, show algebraMap ℤ HeckeAlg a = (a : HeckeAlg) from
      (eq_intCast _ a), map_intCast]
    exact intCast_mem _ a
  | add p q hp hq => rw [map_add]; exact Subring.add_mem _ hp hq
  | mul_X p ℓ hp =>
    rw [map_mul]
    exact Subring.mul_mem _ hp (A_heckeGen_mem N β hT hU ℓ)

def ReMat : Submodule ℝ (Matrix (Fin m) (Fin m) ℂ) where
  carrier := {B | ∀ i j, (B i j).im = 0}
  add_mem' ha hb i j := by simp [ha i j, hb i j]
  zero_mem' i j := by simp
  smul_mem' r B hB i j := by simp [hB i j]

def ImMat : Submodule ℝ (Matrix (Fin m) (Fin m) ℂ) where
  carrier := {B | ∀ i j, (B i j).re = 0}
  add_mem' ha hb i j := by simp [ha i j, hb i j]
  zero_mem' i j := by simp
  smul_mem' r B hB i j := by simp [hB i j]

theorem ReMat_inf_ImMat : ReMat (m := m) ⊓ ImMat = ⊥ := by
  rw [eq_bot_iff]
  rintro B ⟨hre, him⟩
  rw [Submodule.mem_bot]
  ext i j
  apply Complex.ext
  · simpa using him i j
  · simpa using hre i j

theorem RatMat_le_ReMat (B : Matrix (Fin m) (Fin m) ℂ) (hB : B ∈ RatMat (m := m)) : B ∈ ReMat (m := m) := by
  rw [mem_RatMat_iff] at hB
  intro i j
  obtain ⟨q, hq⟩ := hB i j
  rw [← hq]
  exact Complex.ratCast_im q

theorem map_mulI_ReMat_le : (ReMat (m := m)).map mulI ≤ ImMat := by
  rintro _ ⟨B, hB, rfl⟩ i j
  simp [Matrix.smul_apply, hB i j]

abbrev RV' : Submodule ℝ (Matrix (Fin m) (Fin m) ℂ) := Submodule.span ℝ (Set.range (A N β))

abbrev CV' : Submodule ℂ (Matrix (Fin m) (Fin m) ℂ) := Submodule.span ℂ (Set.range (A N β))

include hT hU in
theorem RV'_le_ReMat : RV' N β ≤ ReMat := by
  rw [Submodule.span_le]
  rintro _ ⟨t, rfl⟩
  exact RatMat_le_ReMat _ (A_mem N β hT hU t)

include hT hU in
theorem RV'_inf_eq_bot : RV' N β ⊓ (RV' N β).map mulI = ⊥ := by
  rw [eq_bot_iff, ← ReMat_inf_ImMat]
  exact inf_le_inf (RV'_le_ReMat N β hT hU)
    ((Submodule.map_mono (RV'_le_ReMat N β hT hU)).trans map_mulI_ReMat_le)

def restrictEquiv : ((CV' N β).restrictScalars ℝ) ≃ₗ[ℝ] (CV' N β) where
  toFun x := ⟨x.1, x.2⟩
  invFun x := ⟨x.1, x.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

include hT hU in

theorem finrank_RV' : finrank ℝ (RV' N β) = finrank ℂ (CV' N β) := by
  have hsup := restrictScalars_span_complex (E := Matrix (Fin m) (Fin m) ℂ) (Set.range (A N β))
  have hdim := Submodule.finrank_sup_add_finrank_inf_eq (RV' N β) ((RV' N β).map mulI)
  rw [RV'_inf_eq_bot N β hT hU, finrank_bot, add_zero, ← hsup] at hdim
  have hmap : finrank ℝ ((RV' N β).map mulI) = finrank ℝ (RV' N β) :=
    (LinearEquiv.finrank_eq (Submodule.equivMapOfInjective _ mulI_injective (RV' N β))).symm
  have h2 : finrank ℝ ((CV' N β).restrictScalars ℝ) = 2 * finrank ℂ (CV' N β) := by
    rw [LinearEquiv.finrank_eq (restrictEquiv N β)]
    exact finrank_real_of_complex _
  have h3 : 2 * finrank ℂ (CV' N β) = finrank ℝ (RV' N β) + finrank ℝ (RV' N β) := by
    rw [← h2, hdim, hmap]
  omega

theorem finrank_CV' : finrank ℂ (CV' N β) = finrank ℂ (C N) := by
  have : CV' N β = (C N).map ((LinearMap.toMatrix β β : Module.End ℂ (V N) ≃ₗ[ℂ] _) :
      Module.End ℂ (V N) →ₗ[ℂ] Matrix (Fin m) (Fin m) ℂ) := by
    rw [C_eq_span_range, Submodule.map_span, ← Set.range_comp]
    rfl
  rw [this]
  exact (LinearEquiv.finrank_eq (Submodule.equivMapOfInjective _
    (LinearMap.toMatrix β β).injective (C N))).symm

theorem finrank_RV'_eq_RVℝ : finrank ℝ (RV' N β) = finrank ℝ (RVℝ N) := by
  let Ψ₂ : Module.End ℂ (V N) →ₗ[ℝ] Matrix (Fin m) (Fin m) ℂ :=
    ((LinearMap.toMatrix β β : Module.End ℂ (V N) ≃ₗ[ℂ] _) :
      Module.End ℂ (V N) →ₗ[ℂ] Matrix (Fin m) (Fin m) ℂ).restrictScalars ℝ
  have : RV' N β = (RVℝ N).map Ψ₂ := by
    rw [Submodule.map_span, ← Set.range_comp]
    rfl
  rw [this]
  exact (LinearEquiv.finrank_eq (Submodule.equivMapOfInjective Ψ₂
    (by exact (LinearMap.toMatrix β β).injective) (RVℝ N))).symm

end Rational
p2m_reactivate "P2MW.S_ModularCurve_exists_heckeEquivariant_linearEquiv_rationalTateModule_jZero_fun_two.W1C P2MW.S_ModularCurve_exists_heckeEquivariant_linearEquiv_rationalTateModule_jZero_fun_two.W1A"

theorem two_mul_g_eq {n : ℕ} (b : Module.Basis (Fin n) ℤ (periodLattice N))
    (hli : LinearIndependent ℝ (fun i => ((b i : periodLattice N) : D N)))
    (hsp : Submodule.span ℝ (Set.range fun i => ((b i : periodLattice N) : D N)) = ⊤)
    (hst : PeriodLatticeHeckeStable N)
    {m : ℕ} (β : Module.Basis (Fin m) ℂ (V N))
    (hT : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (i j : Fin m),
      β.repr (CuspForm.heckeTLin 2 hℓ hℓN (β i)) j ∈ Set.range ((↑) : ℚ → ℂ))
    (hU : ∀ (q : ℕ) (hq : q.Prime) (hqN : q ∣ N) (i j : Fin m),
      β.repr (CuspForm.heckeULin 2 hqN (β i)) j ∈ Set.range ((↑) : ℚ → ℂ))
    (hB3c : finrank ℂ (C N) = finrank ℂ (V N)) :
    2 * finrank ℝ (Submodule.span ℝ (Set.range fun t : HeckeAlg => (Mℤ N b t).map (Int.cast : ℤ → ℝ))) = n := by
  haveI : FiniteDimensional ℂ (V N) := Module.Finite.of_basis β
  rw [finrank_span_MK_real_eq N b hli hsp hst, ← finrank_RV'_eq_RVℝ N β, finrank_RV' N β hT hU,
    finrank_CV', hB3c, ← Subspace.dual_finrank_eq (K := ℂ) (V := V N), ← finrank_real_of_complex,
    finrank_eq_card_basis (bℝ N b hli hsp), Fintype.card_fin]

end W1A
p2m_reactivate "P2MW.S_ModularCurve_exists_heckeEquivariant_linearEquiv_rationalTateModule_jZero_fun_two.W1C P2MW.S_ModularCurve_exists_heckeEquivariant_linearEquiv_rationalTateModule_jZero_fun_two.W1A"

namespace W1D

p2m_open "Module Matrix.Module Matrix"

variable {R₀ : Type} [CommRing R₀] {n : ℕ} (Mℤ : R₀ →+* Matrix (Fin n) (Fin n) ℤ)

def MK (K : Type) [CommRing K] : R₀ →+* Matrix (Fin n) (Fin n) K :=
  ((Int.castRingHom K).mapMatrix).comp Mℤ

theorem MK_apply (K : Type) [CommRing K] (t : R₀) : MK Mℤ K t = (Mℤ t).map (Int.cast : ℤ → K) := rfl

theorem MK_map (K : Type) [Field K] [CharZero K] (t : R₀) :
    (MK Mℤ ℚ t).map (algebraMap ℚ K) = MK Mℤ K t := by
  rw [MK_apply, MK_apply, Matrix.map_map]
  congr 1
  funext z
  simp

def Tℚ : Submodule ℚ (Matrix (Fin n) (Fin n) ℚ) := Submodule.span ℚ (Set.range (MK Mℤ ℚ))

def g : ℕ := finrank ℚ (Tℚ Mℤ)

def c : Basis (Fin (g Mℤ)) ℚ (Tℚ Mℤ) := Module.finBasis ℚ (Tℚ Mℤ)

def cK (K : Type) [Field K] [CharZero K] (k : Fin (g Mℤ)) : Matrix (Fin n) (Fin n) K :=
  ((c Mℤ k : Tℚ Mℤ) : Matrix (Fin n) (Fin n) ℚ).map (algebraMap ℚ K)

theorem smul_map_algebraMap (K : Type) [Field K] [CharZero K] (q : ℚ) (A : Matrix (Fin n) (Fin n) ℚ) :
    (q • A).map (algebraMap ℚ K) = (q : K) • A.map (algebraMap ℚ K) := by
  ext i j; simp

theorem eq_sum_of_mem_Tℚ (x : Tℚ Mℤ) :
    (x : Matrix (Fin n) (Fin n) ℚ) = ∑ k, (c Mℤ).repr x k • ((c Mℤ k : Tℚ Mℤ) : Matrix (Fin n) (Fin n) ℚ) := by
  have h := congrArg (Submodule.subtype (Tℚ Mℤ)) ((c Mℤ).sum_repr x).symm
  rw [map_sum] at h
  simpa using h

theorem map_mem_span_cK (K : Type) [Field K] [CharZero K] (x : Tℚ Mℤ) :
    (x : Matrix (Fin n) (Fin n) ℚ).map (algebraMap ℚ K) ∈ Submodule.span K (Set.range (cK Mℤ K)) := by
  rw [eq_sum_of_mem_Tℚ Mℤ x]
  rw [show (∑ k, (c Mℤ).repr x k • ((c Mℤ k : Tℚ Mℤ) : Matrix (Fin n) (Fin n) ℚ)).map (algebraMap ℚ K)
      = (algebraMap ℚ K).mapMatrix (∑ k, (c Mℤ).repr x k • ((c Mℤ k : Tℚ Mℤ) : Matrix (Fin n) (Fin n) ℚ))
      from rfl, map_sum]
  refine Submodule.sum_mem _ fun k _ => ?_
  rw [RingHom.mapMatrix_apply, smul_map_algebraMap]
  exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self k))

theorem MK_mem_span_cK (K : Type) [Field K] [CharZero K] (t : R₀) :
    MK Mℤ K t ∈ Submodule.span K (Set.range (cK Mℤ K)) := by
  have hmem : MK Mℤ ℚ t ∈ Tℚ Mℤ := Submodule.subset_span (Set.mem_range_self t)
  rw [← MK_map Mℤ K t]
  exact map_mem_span_cK Mℤ K ⟨MK Mℤ ℚ t, hmem⟩

theorem map_mem_of_mem_Tℚ (K : Type) [Field K] [CharZero K] (S : Submodule K (Matrix (Fin n) (Fin n) K))
    (hS : ∀ t, MK Mℤ K t ∈ S) {x : Matrix (Fin n) (Fin n) ℚ} (hx : x ∈ Tℚ Mℤ) :
    x.map (algebraMap ℚ K) ∈ S := by
  refine Submodule.span_induction (p := fun x _ => x.map (algebraMap ℚ K) ∈ S) ?_ ?_ ?_ ?_ hx
  · rintro _ ⟨t, rfl⟩
    rw [MK_map]; exact hS t
  · simp only [Matrix.map_zero, map_zero]; exact S.zero_mem
  · intro x y _ _ hx hy
    rw [Matrix.map_add _ (map_add (algebraMap ℚ K))]; exact S.add_mem hx hy
  · intro r x _ hx
    rw [smul_map_algebraMap]; exact S.smul_mem _ hx

section Square

variable (hn : 2 * g Mℤ = n)

def σ : Fin 2 × Fin (g Mℤ) ≃ Fin n :=
  Fintype.equivOfCardEq (by simp [hn])

def Φ (K : Type) [Field K] [CharZero K] (v : Fin 2 → Fin n → K) : Matrix (Fin n) (Fin n) K :=
  Matrix.of fun i j => (cK Mℤ K ((σ Mℤ hn).symm j).2 *ᵥ v ((σ Mℤ hn).symm j).1) i

theorem Φ_col (K : Type) [Field K] [CharZero K] (v : Fin 2 → Fin n → K) (ak : Fin 2 × Fin (g Mℤ)) :
    (Φ Mℤ hn K v).col (σ Mℤ hn ak) = cK Mℤ K ak.2 *ᵥ v ak.1 := by
  funext i
  simp [Φ]

theorem Φ_map (K : Type) [Field K] [CharZero K] (v : Fin 2 → Fin n → ℚ) :
    (Φ Mℤ hn ℚ v).map (algebraMap ℚ K) = Φ Mℤ hn K (fun a => (algebraMap ℚ K) ∘ v a) := by
  ext i j
  simp only [Φ, Matrix.map_apply, Matrix.of_apply]
  rw [RingHom.map_mulVec]
  simp only [cK, Matrix.map_map]
  congr 2

theorem span_cols_Φ_eq_top (K : Type) [Field K] [CharZero K] (w : Fin 2 → Fin n → K)
    (hw : Submodule.span K (Set.range fun ta : R₀ × Fin 2 => MK Mℤ K ta.1 *ᵥ w ta.2) = ⊤) :
    Submodule.span K (Set.range (Φ Mℤ hn K w).col) = ⊤ := by
  apply top_le_iff.mp
  rw [← hw]
  apply Submodule.span_le.mpr
  rintro _ ⟨⟨t, a⟩, rfl⟩
  have hmem := MK_mem_span_cK Mℤ K t
  simp only [SetLike.mem_coe]

  refine Submodule.span_induction (p := fun x _ => x *ᵥ w a ∈ Submodule.span K (Set.range (Φ Mℤ hn K w).col))
    ?_ ?_ ?_ ?_ hmem
  · rintro _ ⟨k, rfl⟩
    refine Submodule.subset_span ⟨σ Mℤ hn (a, k), ?_⟩
    exact Φ_col Mℤ hn K w (a, k)
  · simp
  · intro x y _ _ hx hy
    rw [Matrix.add_mulVec]; exact Submodule.add_mem _ hx hy
  · intro r x _ hx
    rw [Matrix.smul_mulVec]; exact Submodule.smul_mem _ r hx

theorem isUnit_Φ (K : Type) [Field K] [CharZero K] (w : Fin 2 → Fin n → K)
    (hw : Submodule.span K (Set.range fun ta : R₀ × Fin 2 => MK Mℤ K ta.1 *ᵥ w ta.2) = ⊤) :
    IsUnit (Φ Mℤ hn K w) := by
  rw [← Matrix.linearIndependent_cols_iff_isUnit]
  exact linearIndependent_of_top_le_span_of_card_eq_finrank
    (span_cols_Φ_eq_top Mℤ hn K w hw).ge (by simp)

theorem span_cols_Φ_of_isUnit (K : Type) [Field K] [CharZero K] (v : Fin 2 → Fin n → K)
    (hv : IsUnit (Φ Mℤ hn K v)) :
    Submodule.span K (Set.range (Φ Mℤ hn K v).col) = ⊤ := by
  rw [← Matrix.linearIndependent_cols_iff_isUnit] at hv
  exact hv.span_eq_top_of_card_eq_finrank' (by simp)

theorem continuous_det_Φ : Continuous fun v : Fin 2 → Fin n → ℝ => (Φ Mℤ hn ℝ v).det := by
  refine Continuous.matrix_det ?_
  refine continuous_pi fun i => continuous_pi fun j => ?_
  simp only [Φ, Matrix.of_apply, Matrix.mulVec, dotProduct]
  fun_prop

theorem exists_rat_isUnit_Φ
    (hw : ∃ w : Fin 2 → Fin n → ℝ,
      Submodule.span ℝ (Set.range fun ta : R₀ × Fin 2 => MK Mℤ ℝ ta.1 *ᵥ w ta.2) = ⊤) :
    ∃ v : Fin 2 → Fin n → ℚ, IsUnit (Φ Mℤ hn ℚ v) := by
  obtain ⟨w, hw⟩ := hw
  have hU : IsOpen {v : Fin 2 → Fin n → ℝ | (Φ Mℤ hn ℝ v).det ≠ 0} :=
    isOpen_ne_fun (continuous_det_Φ Mℤ hn) continuous_const
  have hne : {v : Fin 2 → Fin n → ℝ | (Φ Mℤ hn ℝ v).det ≠ 0}.Nonempty :=
    ⟨w, by
      have := isUnit_Φ Mℤ hn ℝ w hw
      rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero] at this
      exact this⟩
  have hdense : DenseRange (fun v : Fin 2 → Fin n → ℚ => fun a => fun j => ((v a j : ℚ) : ℝ)) := by
    have h1 : DenseRange (fun x : Fin n → ℚ => fun j => ((x j : ℚ) : ℝ)) :=
      DenseRange.piMap fun _ => Rat.denseRange_cast
    exact DenseRange.piMap fun _ => h1
  obtain ⟨v, hv⟩ := hdense.exists_mem_open hU hne
  refine ⟨v, ?_⟩
  rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
  intro h0
  apply hv
  have hmap := RingHom.map_det (algebraMap ℚ ℝ) (Φ Mℤ hn ℚ v)
  rw [h0, map_zero, RingHom.mapMatrix_apply, Φ_map] at hmap
  exact hmap.symm

end Square
p2m_reactivate "P2MW.S_ModularCurve_exists_heckeEquivariant_linearEquiv_rationalTateModule_jZero_fun_two.W1C P2MW.S_ModularCurve_exists_heckeEquivariant_linearEquiv_rationalTateModule_jZero_fun_two.W1A"

section Padic

variable (p : ℕ) [Fact p.Prime]

def Tp : Subalgebra ℚ_[p] (Matrix (Fin n) (Fin n) ℚ_[p]) :=
  Algebra.adjoin ℚ_[p] (Set.range (MK Mℤ ℚ_[p]))

scoped instance : IsMulCommutative (Tp Mℤ p) :=
  Algebra.isMulCommutative_adjoin ℚ_[p] (by
    rintro _ ⟨s, rfl⟩ _ ⟨t, rfl⟩
    rw [← map_mul, ← map_mul, mul_comm])

open scoped IsMulCommutative in
scoped instance instCommRingTp : CommRing (Tp Mℤ p) := inferInstance

def φ : R₀ →+* Tp Mℤ p :=
  (MK Mℤ ℚ_[p]).codRestrict (Tp Mℤ p).toSubring
    fun t => Algebra.subset_adjoin (Set.mem_range_self t)

@[scoped simp] theorem coe_φ (t : R₀) : (φ Mℤ p t : Matrix (Fin n) (Fin n) ℚ_[p]) = MK Mℤ ℚ_[p] t := rfl

theorem adjoin_range_φ : Algebra.adjoin ℚ_[p] (Set.range (φ Mℤ p)) = ⊤ := by
  apply Subalgebra.map_injective (f := (Tp Mℤ p).val) Subtype.val_injective
  rw [AlgHom.map_adjoin, Algebra.map_top, Subalgebra.range_val, ← Set.range_comp]
  rfl

theorem toSubmodule_Tp_le : Subalgebra.toSubmodule (Tp Mℤ p) ≤
    Submodule.span ℚ_[p] (Set.range (cK Mℤ ℚ_[p])) := by
  rw [Tp, Algebra.adjoin_eq_span]
  have hcl : (Submonoid.closure (Set.range (MK Mℤ ℚ_[p])) : Set (Matrix (Fin n) (Fin n) ℚ_[p])) =
      Set.range (MK Mℤ ℚ_[p]) := by
    refine le_antisymm ?_ Submonoid.subset_closure
    have : Set.range (MK Mℤ ℚ_[p]) = (MonoidHom.mrange (MK Mℤ ℚ_[p] : R₀ →* Matrix (Fin n) (Fin n) ℚ_[p]) :
        Set (Matrix (Fin n) (Fin n) ℚ_[p])) := (MonoidHom.coe_mrange _).symm
    rw [this]
    exact Submonoid.closure_le.mpr (le_of_eq this)
  rw [hcl]
  exact Submodule.span_le.mpr (by rintro _ ⟨t, rfl⟩; exact MK_mem_span_cK Mℤ ℚ_[p] t)

theorem finrank_Tp_le : finrank ℚ_[p] (Tp Mℤ p) ≤ g Mℤ := by
  calc finrank ℚ_[p] (Tp Mℤ p)
      = finrank ℚ_[p] (Subalgebra.toSubmodule (Tp Mℤ p)) := (Subalgebra.finrank_toSubmodule _).symm
    _ ≤ finrank ℚ_[p] (Submodule.span ℚ_[p] (Set.range (cK Mℤ ℚ_[p]))) :=
        Submodule.finrank_mono (toSubmodule_Tp_le Mℤ p)
    _ ≤ Fintype.card (Fin (g Mℤ)) := finrank_range_le_card _
    _ = g Mℤ := Fintype.card_fin _

theorem cK_mem_Tp (k : Fin (g Mℤ)) : cK Mℤ ℚ_[p] k ∈ Tp Mℤ p := by

  have h := map_mem_of_mem_Tℚ Mℤ ℚ_[p] (Subalgebra.toSubmodule (Tp Mℤ p))
    (fun t => Algebra.subset_adjoin (Set.mem_range_self t)) (c Mℤ k).2
  exact h

variable (hn : 2 * g Mℤ = n) (vq : Fin 2 → Fin n → ℚ)

def vp : Fin 2 → Fin n → ℚ_[p] := fun a => (algebraMap ℚ ℚ_[p]) ∘ vq a

def ψ : (Fin 2 → Tp Mℤ p) →ₗ[ℚ_[p]] (Fin n → ℚ_[p]) where
  toFun s := ∑ a, ((s a : Tp Mℤ p) : Matrix (Fin n) (Fin n) ℚ_[p]) *ᵥ vp p vq a
  map_add' s s' := by
    simp only [Pi.add_apply, Subalgebra.coe_add, Matrix.add_mulVec, Finset.sum_add_distrib]
  map_smul' r s := by
    simp only [Pi.smul_apply, Subalgebra.coe_smul, Matrix.smul_mulVec, RingHom.id_apply,
      Finset.smul_sum]

theorem ψ_apply (s : Fin 2 → Tp Mℤ p) :
    ψ Mℤ p vq s = ∑ a, ((s a : Tp Mℤ p) : Matrix (Fin n) (Fin n) ℚ_[p]) *ᵥ vp p vq a := rfl

theorem ψ_equivariant (t : R₀) (s : Fin 2 → Tp Mℤ p) :
    ψ Mℤ p vq (φ Mℤ p t • s) = MK Mℤ ℚ_[p] t *ᵥ ψ Mℤ p vq s := by
  simp only [ψ_apply, Pi.smul_apply, smul_eq_mul, Subalgebra.coe_mul, coe_φ, Matrix.mulVec_sum,
    Matrix.mulVec_mulVec]

theorem ψ_surjective (hv : IsUnit (Φ Mℤ hn ℚ vq)) : Function.Surjective (ψ Mℤ p vq) := by
  rw [← LinearMap.range_eq_top, eq_top_iff]
  have hvp : IsUnit (Φ Mℤ hn ℚ_[p] (vp p vq)) := by
    have := (RingHom.mapMatrix (algebraMap ℚ ℚ_[p])).isUnit_map hv
    rwa [RingHom.mapMatrix_apply, Φ_map] at this
  rw [← span_cols_Φ_of_isUnit Mℤ hn ℚ_[p] (vp p vq) hvp, Submodule.span_le]
  rintro _ ⟨j, rfl⟩
  obtain ⟨⟨a, k⟩, rfl⟩ := (σ Mℤ hn).surjective j
  rw [Φ_col]
  refine ⟨Pi.single a ⟨cK Mℤ ℚ_[p] k, cK_mem_Tp Mℤ p k⟩, ?_⟩
  rw [ψ_apply, Finset.sum_eq_single a]
  · simp
  · intro b _ hb; simp [Pi.single_eq_of_ne hb]
  · intro h; exact absurd (Finset.mem_univ a) h

theorem finrank_source_le : finrank ℚ_[p] (Fin 2 → Tp Mℤ p) ≤ 2 * g Mℤ := by
  rw [Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  exact Nat.mul_le_mul_left 2 (finrank_Tp_le Mℤ p)

theorem ψ_bijective (hv : IsUnit (Φ Mℤ hn ℚ vq)) : Function.Bijective (ψ Mℤ p vq) := by
  have hsurj := ψ_surjective Mℤ p hn vq hv
  refine ⟨?_, hsurj⟩
  have hrk := LinearMap.finrank_range_add_finrank_ker (ψ Mℤ p vq)
  rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, Module.finrank_fin_fun] at hrk
  have hle := finrank_source_le Mℤ p
  rw [hn] at hle
  have hker : finrank ℚ_[p] (LinearMap.ker (ψ Mℤ p vq)) = 0 := by omega
  rw [← LinearMap.ker_eq_bot]
  exact Submodule.finrank_eq_zero.mp hker

theorem exists_equiv (hv : IsUnit (Φ Mℤ hn ℚ vq)) :
    ∃ e : (Fin n → ℚ_[p]) ≃ₗ[ℚ_[p]] (Fin 2 → Tp Mℤ p),
      ∀ (t : R₀) (v : Fin n → ℚ_[p]), e (MK Mℤ ℚ_[p] t *ᵥ v) = φ Mℤ p t • e v := by
  let e := (LinearEquiv.ofBijective (ψ Mℤ p vq) (ψ_bijective Mℤ p hn vq hv)).symm
  refine ⟨e, fun t v => ?_⟩
  apply e.symm.injective
  rw [LinearEquiv.symm_apply_apply]
  change MK Mℤ ℚ_[p] t *ᵥ v = ψ Mℤ p vq (φ Mℤ p t • e v)
  rw [ψ_equivariant]
  congr 1
  exact (LinearEquiv.ofBijective (ψ Mℤ p vq) (ψ_bijective Mℤ p hn vq hv)).apply_symm_apply v |>.symm

end Padic
p2m_reactivate "P2MW.S_ModularCurve_exists_heckeEquivariant_linearEquiv_rationalTateModule_jZero_fun_two.W1C P2MW.S_ModularCurve_exists_heckeEquivariant_linearEquiv_rationalTateModule_jZero_fun_two.W1A"

theorem descent (p : ℕ) [Fact p.Prime] (hn : 2 * g Mℤ = n)
    (hw : ∃ w : Fin 2 → Fin n → ℝ,
      Submodule.span ℝ (Set.range fun ta : R₀ × Fin 2 => MK Mℤ ℝ ta.1 *ᵥ w ta.2) = ⊤) :
    ∃ (T : Type) (_ : CommRing T) (_ : Algebra ℚ_[p] T) (φ : R₀ →+* T)
      (e : (Fin n → ℚ_[p]) ≃ₗ[ℚ_[p]] (Fin 2 → T)),
      Algebra.adjoin ℚ_[p] (Set.range φ) = ⊤ ∧
        ∀ (t : R₀) (v : Fin n → ℚ_[p]), e (MK Mℤ ℚ_[p] t *ᵥ v) = φ t • e v := by
  obtain ⟨vq, hv⟩ := exists_rat_isUnit_Φ Mℤ hn hw
  obtain ⟨e, he⟩ := exists_equiv Mℤ p hn vq hv
  exact ⟨Tp Mℤ p, inferInstance, inferInstance, φ Mℤ p, e, adjoin_range_φ Mℤ p, he⟩

end W1D
p2m_reactivate "P2MW.S_ModularCurve_exists_heckeEquivariant_linearEquiv_rationalTateModule_jZero_fun_two.W1C P2MW.S_ModularCurve_exists_heckeEquivariant_linearEquiv_rationalTateModule_jZero_fun_two.W1A P2MW.S_ModularCurve_exists_heckeEquivariant_linearEquiv_rationalTateModule_jZero_fun_two.W1D"

namespace W1D

p2m_open "Module Matrix.Module"

variable {n : ℕ}

def flat (K : Type) [CommRing K] : Matrix (Fin n) (Fin n) K →ₗ[K] (Fin n × Fin n → K) where
  toFun A := fun ij => A ij.1 ij.2
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem flat_injective (K : Type) [CommRing K] : Function.Injective (flat (n := n) K) := by
  intro A B h
  ext i j
  exact congrFun h (i, j)

theorem ker_flat (K : Type) [CommRing K] : LinearMap.ker (flat (n := n) K) = ⊥ :=
  LinearMap.ker_eq_bot.mpr (flat_injective K)

def castMat : Matrix (Fin n) (Fin n) ℚ →ₗ[ℚ] Matrix (Fin n) (Fin n) ℝ :=
  ((Algebra.ofId ℚ ℝ).mapMatrix).toLinearMap

@[scoped simp] theorem castMat_apply (A : Matrix (Fin n) (Fin n) ℚ) :
    castMat A = A.map (algebraMap ℚ ℝ) := rfl

theorem linearIndependent_real_of_rat {ι : Type*} (v : ι → Matrix (Fin n) (Fin n) ℚ)
    (hv : LinearIndependent ℚ v) :
    LinearIndependent ℝ (fun i => (v i).map (algebraMap ℚ ℝ)) := by

  have h1 : LinearIndependent ℚ (fun i => flat ℚ (v i)) := hv.map' (flat ℚ) (ker_flat ℚ)
  have h2 : LinearIndependent ℝ (fun i => (algebraMap ℚ ℝ) ∘ (flat ℚ (v i))) :=
    (linearIndependent_algebraMap_comp_iff (R := ℚ) (S := ℝ)).mpr h1
  have h3 : (fun i => (algebraMap ℚ ℝ) ∘ (flat ℚ (v i))) = fun i => flat ℝ ((v i).map (algebraMap ℚ ℝ)) := by
    funext i; funext ij; rfl
  rw [h3] at h2
  exact LinearIndependent.of_comp (flat ℝ) h2

theorem finrank_real_span_eq {ι : Type*} (f : ι → Matrix (Fin n) (Fin n) ℚ) :
    finrank ℝ (Submodule.span ℝ (Set.range fun i => (f i).map (algebraMap ℚ ℝ))) =
      finrank ℚ (Submodule.span ℚ (Set.range f)) := by
  obtain ⟨s, hs, hspan, hli⟩ := exists_linearIndependent ℚ (Set.range f)
  have hfin : s.Finite := LinearIndependent.set_finite_of_isNoetherian hli
  haveI : Fintype s := hfin.fintype

  have hq : finrank ℚ (Submodule.span ℚ (Set.range f)) = Fintype.card s := by
    rw [← hspan, ← finrank_span_eq_card (b := ((↑) : s → Matrix (Fin n) (Fin n) ℚ)) hli]
    rw [Subtype.range_coe_subtype, Set.setOf_mem_eq]

  have hli' : LinearIndependent ℝ (fun i : s => ((i : Matrix (Fin n) (Fin n) ℚ)).map (algebraMap ℚ ℝ)) :=
    linearIndependent_real_of_rat _ hli
  have hspan' : Submodule.span ℝ (Set.range fun i : s => ((i : Matrix (Fin n) (Fin n) ℚ)).map (algebraMap ℚ ℝ))
      = Submodule.span ℝ (Set.range fun i => (f i).map (algebraMap ℚ ℝ)) := by
    apply le_antisymm
    · apply Submodule.span_mono
      rintro _ ⟨⟨x, hx⟩, rfl⟩
      obtain ⟨i, rfl⟩ := hs hx
      exact ⟨i, rfl⟩
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      have hi : f i ∈ Submodule.span ℚ s := by rw [hspan]; exact Submodule.subset_span ⟨i, rfl⟩

      have : castMat (f i) ∈ (Submodule.span ℚ s).map castMat := Submodule.mem_map_of_mem hi
      rw [Submodule.map_span] at this
      have hle : Submodule.span ℚ (castMat '' s) ≤
          (Submodule.span ℝ (Set.range fun i : s =>
            ((i : Matrix (Fin n) (Fin n) ℚ)).map (algebraMap ℚ ℝ))).restrictScalars ℚ := by
        rw [Submodule.span_le]
        rintro _ ⟨x, hx, rfl⟩
        exact Submodule.subset_span ⟨⟨x, hx⟩, rfl⟩
      exact hle this
  rw [← hspan', finrank_span_eq_card hli', hq]

end W1D
p2m_reactivate "P2MW.S_ModularCurve_exists_heckeEquivariant_linearEquiv_rationalTateModule_jZero_fun_two.W1C P2MW.S_ModularCurve_exists_heckeEquivariant_linearEquiv_rationalTateModule_jZero_fun_two.W1A P2MW.S_ModularCurve_exists_heckeEquivariant_linearEquiv_rationalTateModule_jZero_fun_two.W1D"

open scoped TensorProduct

namespace W1T

open ModularCurve

variable (p : ℕ) [Fact p.Prime] (J : Type) [AddCommGroup J] [Module HeckeAlg J]
variable {Λ : Type} [AddCommGroup Λ] (ρΛ : HeckeAlg →+* Module.End ℤ Λ)
variable {n : ℕ} (bΛ : Module.Basis (Fin n) ℤ Λ)

def M : HeckeAlg →+* Matrix (Fin n) (Fin n) ℤ :=
  (LinearMap.toMatrixAlgEquiv bΛ).toRingEquiv.toRingHom.comp ρΛ

theorem M_apply (t : HeckeAlg) : M ρΛ bΛ t = LinearMap.toMatrix bΛ bΛ (ρΛ t) := rfl

def Mp : HeckeAlg →+* Matrix (Fin n) (Fin n) ℚ_[p] :=
  ((Int.castRingHom ℚ_[p]).mapMatrix).comp (M ρΛ bΛ)

theorem Mp_apply (t : HeckeAlg) : Mp p ρΛ bΛ t = (M ρΛ bΛ t).map (Int.cast : ℤ → ℚ_[p]) := rfl

variable (e₁ : TateModule p J ≃ₗ[ℤ_[p]] ℤ_[p] ⊗[ℤ] Λ)

def E1 : RationalTateModule p J ≃ₗ[ℚ_[p]] ℚ_[p] ⊗[ℤ_[p]] (ℤ_[p] ⊗[ℤ] Λ) :=
  e₁.baseChange ℤ_[p] ℚ_[p] _ _

def E2 : ℚ_[p] ⊗[ℤ_[p]] (ℤ_[p] ⊗[ℤ] Λ) ≃ₗ[ℚ_[p]] ℚ_[p] ⊗[ℤ] Λ :=
  TensorProduct.AlgebraTensorModule.cancelBaseChange ℤ ℤ_[p] ℚ_[p] ℚ_[p] Λ

def E3 : ℚ_[p] ⊗[ℤ] Λ ≃ₗ[ℚ_[p]] (Fin n → ℚ_[p]) :=
  (Algebra.TensorProduct.basis ℚ_[p] bΛ).equivFun

def E : RationalTateModule p J ≃ₗ[ℚ_[p]] (Fin n → ℚ_[p]) :=
  (E1 p J e₁).trans ((E2 p).trans (E3 p bΛ))

theorem E1_equivariant (t : HeckeAlg)
    (he : ∀ t x, e₁ (tateHeckeRep p J t x) = (ρΛ t).baseChange ℤ_[p] (e₁ x))
    (v : RationalTateModule p J) :
    E1 p J e₁ (rationalHeckeRep p J t v) = ((ρΛ t).baseChange ℤ_[p]).baseChange ℚ_[p] (E1 p J e₁ v) := by
  induction v using TensorProduct.induction_on with
  | zero => simp
  | tmul a x =>
    simp [E1, rationalHeckeRep_tmul, LinearEquiv.baseChange, he]
  | add x y hx hy => simp [map_add, hx, hy]

theorem E2_equivariant (t : HeckeAlg) (v : ℚ_[p] ⊗[ℤ_[p]] (ℤ_[p] ⊗[ℤ] Λ)) :
    E2 p (((ρΛ t).baseChange ℤ_[p]).baseChange ℚ_[p] v) = (ρΛ t).baseChange ℚ_[p] (E2 p v) := by
  induction v using TensorProduct.induction_on with
  | zero => simp
  | tmul a x =>
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul b y => simp [E2]
    | add x y hx hy =>
      rw [TensorProduct.tmul_add, map_add, map_add, map_add, hx, hy, map_add]
  | add x y hx hy => simp [map_add, hx, hy]

theorem E3_equivariant (t : HeckeAlg) (v : ℚ_[p] ⊗[ℤ] Λ) :
    E3 p bΛ ((ρΛ t).baseChange ℚ_[p] v) = (Mp p ρΛ bΛ t).mulVec (E3 p bΛ v) := by
  have h := LinearMap.toMatrix_mulVec_repr (Algebra.TensorProduct.basis ℚ_[p] bΛ)
    (Algebra.TensorProduct.basis ℚ_[p] bΛ) ((ρΛ t).baseChange ℚ_[p]) v
  rw [LinearMap.toMatrix_baseChange] at h
  simp only [E3, Module.Basis.equivFun_apply]
  rw [← h]
  congr 1

theorem E_equivariant
    (he : ∀ t x, e₁ (tateHeckeRep p J t x) = (ρΛ t).baseChange ℤ_[p] (e₁ x))
    (t : HeckeAlg) (v : RationalTateModule p J) :
    E p J bΛ e₁ (rationalHeckeRep p J t v) = (Mp p ρΛ bΛ t).mulVec (E p J bΛ e₁ v) := by
  simp only [E, LinearEquiv.trans_apply]
  rw [E1_equivariant p J ρΛ e₁ t he, E2_equivariant, E3_equivariant]

end W1T
p2m_reactivate "P2MW.S_ModularCurve_exists_heckeEquivariant_linearEquiv_rationalTateModule_jZero_fun_two.W1C P2MW.S_ModularCurve_exists_heckeEquivariant_linearEquiv_rationalTateModule_jZero_fun_two.W1A P2MW.S_ModularCurve_exists_heckeEquivariant_linearEquiv_rationalTateModule_jZero_fun_two.W1D"

namespace W1Final

p2m_open "ModularCurve Module Matrix.Module"
open scoped TensorProduct Matrix

set_option maxHeartbeats 1600000 in
theorem main (N p : ℕ) [NeZero N] [Fact p.Prime]
    (hin : ModularCurve.HeckeInputsAll N) (hcomm : ModularCurve.HeckeOperatorsCommuteBar N) :
    letI := ModularCurve.heckeModuleBar N
    ∃ (T : Type) (_ : CommRing T) (_ : Algebra ℚ_[p] T) (φ : ModularCurve.HeckeAlg →+* T)
      (e : ModularCurve.RationalTateModule p (ModularCurve.JZero N) ≃ₗ[ℚ_[p]] (Fin 2 → T)),
      Algebra.adjoin ℚ_[p] (Set.range φ) = ⊤ ∧
        ∀ (t : ModularCurve.HeckeAlg) (v : ModularCurve.RationalTateModule p (ModularCurve.JZero N)),
          e (ModularCurve.rationalHeckeRep p (ModularCurve.JZero N) t v) = φ t • e v := by
  letI := ModularCurve.heckeModuleBar N

  have hst : PeriodLatticeHeckeStable N := ModularCurve.periodLatticeHeckeStable N
  obtain ⟨n, b, hli, hsp⟩ :=
    ModularCurve.exists_basis_periodLattice_linearIndependent_real_span_eq_top N
  obtain ⟨m, β, hT, hU⟩ := CuspForm.exists_basis_repr_heckeTLin_heckeULin_mem_range_ratCast N
  obtain ⟨e₁, he₁⟩ :=
    ModularCurve.exists_heckeEquivariant_linearEquiv_tateModule_jZero_padicInt_tensor_periodLattice
      N p hin hcomm hst
  have hB3a : ∀ T : Module.End ℂ (W1A.V N), T ∈ W1A.C N →
      (∀ f : W1A.V N, ModularFormClass.qCoeff (⇑(T f)) 1 = 0) → T = 0 :=
    fun T hT h => CuspForm.eq_zero_of_mem_span_heckeAlgebra_of_forall_qCoeff_one_eq_zero N T hT h
  have hB3c : finrank ℂ (W1A.C N) = finrank ℂ (W1A.V N) :=
    CuspForm.finrank_span_heckeAlgebra_eq_finrank N
  haveI : FiniteDimensional ℂ (W1A.V N) := Module.Finite.of_basis β

  let Mℤ : HeckeAlg →+* Matrix (Fin n) (Fin n) ℤ := W1A.Mℤ N b

  have hn : 2 * W1D.g Mℤ = n := by
    have h := W1A.two_mul_g_eq N b hli hsp hst β hT hU hB3c
    have hr : (fun t : HeckeAlg => (W1A.Mℤ N b t).map (Int.cast : ℤ → ℝ)) =
        fun t : HeckeAlg => (W1D.MK Mℤ ℚ t).map (algebraMap ℚ ℝ) := by
      funext t
      rw [W1D.MK_map]
      rfl
    rw [hr, W1D.finrank_real_span_eq] at h
    exact h

  have hw : ∃ w : Fin 2 → Fin n → ℝ,
      Submodule.span ℝ (Set.range fun ta : HeckeAlg × Fin 2 => W1D.MK Mℤ ℝ ta.1 *ᵥ w ta.2) = ⊤ :=
    W1A.exists_w N b hli hsp hst (W1A.span_real_eq_top N hB3a hB3c)

  obtain ⟨T, _, _, φ, e₂, hgen, he₂⟩ := W1D.descent Mℤ p hn hw

  let E := W1T.E p (JZero N) b e₁
  have hE : ∀ (t : HeckeAlg) (v : RationalTateModule p (JZero N)),
      E (rationalHeckeRep p (JZero N) t v) = W1D.MK Mℤ ℚ_[p] t *ᵥ E v :=
    fun t v => W1T.E_equivariant p (JZero N) (periodLatticeHeckeEnd N) b e₁ he₁ t v
  refine ⟨T, inferInstance, inferInstance, φ, E.trans e₂, hgen, fun t v => ?_⟩
  rw [LinearEquiv.trans_apply, hE, he₂, LinearEquiv.trans_apply]

end W1Final
p2m_reactivate "P2MW.S_ModularCurve_exists_heckeEquivariant_linearEquiv_rationalTateModule_jZero_fun_two.W1C P2MW.S_ModularCurve_exists_heckeEquivariant_linearEquiv_rationalTateModule_jZero_fun_two.W1A P2MW.S_ModularCurve_exists_heckeEquivariant_linearEquiv_rationalTateModule_jZero_fun_two.W1D"

theorem solution
    (N p : ℕ) [NeZero N] [Fact p.Prime]
    (hin : ModularCurve.HeckeInputsAll N) (hcomm : ModularCurve.HeckeOperatorsCommuteBar N) :
    letI := ModularCurve.heckeModuleBar N
    ∃ (T : Type) (_ : CommRing T) (_ : Algebra ℚ_[p] T) (φ : ModularCurve.HeckeAlg →+* T)
      (e : ModularCurve.RationalTateModule p (ModularCurve.JZero N) ≃ₗ[ℚ_[p]] (Fin 2 → T)),
      Algebra.adjoin ℚ_[p] (Set.range φ) = ⊤ ∧
        ∀ (t : ModularCurve.HeckeAlg) (v : ModularCurve.RationalTateModule p (ModularCurve.JZero N)),
          e (ModularCurve.rationalHeckeRep p (ModularCurve.JZero N) t v) = φ t • e v :=
  W1Final.main N p hin hcomm

end
end S_ModularCurve_exists_heckeEquivariant_linearEquiv_rationalTateModule_jZero_fun_two
end P2MW
export P2MW.S_ModularCurve_exists_heckeEquivariant_linearEquiv_rationalTateModule_jZero_fun_two (solution)
