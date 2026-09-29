-- Prove2me | solution 1 for ModularCurve.exists_heckeAlg_idempotent_tower_smul_eq_self_of_mem_eisensteinTorsionBar
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/5e0bbb4a-ccd7-5edb-9dce-d7e6fd6c62f8

import Definitions.Def_ModularCurve_JZeroNeronTorsionSheafV4
import Definitions.Def_CuspForm_HeckeLocal
import Definitions.Def_CuspForm_HeckeEvalForms
import Theorems.Thm_exists_idempotent_tower_of_finite_quotient_of_isMaximal
import Theorems.Thm_ModularCurve_heckeOperatorsCommuteBar
import Theorems.Thm_ModularCurve_ker_heckeEvalForms_latticeRestrict_eq_ker_heckeEvalBar
import Theorems.Thm_CuspForm_heckeEvalForms_range_eq_top
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_heckeAlg_idempotent_tower_smul_eq_self_of_mem_eisensteinTorsionBar
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.CuspSpace.instNonempty ModularCurve.CuspSpace.instSubsingletonOfOne"
p2m_attr_erase "instance" "ModularCurve.CuspSpace.instFinite ModularCurve.instAlgebraIntermediateFieldLaurent ModularCurve.instIsScalarTowerKaehlerIntermediateFieldLaurent ModularCurve.instIsScalarTowerIntermediateFieldLaurent ModularCurve.instModuleKaehlerIntermediateFieldLaurent ModularCurve.Gamma0Pair.isElliptic ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.B3.instIsElliptic_goodModel ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar ModularCurve.instIsScalarTowerJAdjoin FLT.Gamma0FundamentalSet.instContinuousConstSMulSpecialLinearGroupFinOfNatNatIntUpperHalfPlane_definitions FLT.HyperbolicMeasure.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatIntUpperHalfPlaneVolume_definitions FLT.HyperbolicMeasure.instIsOpenPosMeasureUpperHalfPlaneVolume_definitions FLT.L2ProductionInstance.isFiniteMeasure_gamma0 FLT.L2ProductionInstance.countable_SL2Z FLT.L2ProductionInstance.countable_quotient FLT.L2ProductionInstance.nontrivial_gamma0L2 HeckeEis.instModuleCoeffH1par HeckeEis.instAddCommGroupCoeffH1par HeckeEis.instFiniteIndexHeckeUpper ModularCurve.Period.parabolicHoms_int_moduleFinite ModularCurve.Period.instGroupFG_SL2Z ModularCurve.Period.instIsNoetherian_addHom_int ModularCurve.Period.instGroupFG_Gamma0"
p2m_attr_erase "simp" "ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff"
p2m_attr_erase "simp" "ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.dualHeckeRep_apply_apply ModularCurve.coe_segmentPath ModularCurve.cuspHeckeAeval_heckeGen ModularCurve.coe_periodLatticeRestrict_apply AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularCurve.ComplexPlaceDictionary.mk.injEq ModularCurve.ComplexPlaceDictionary.mk.sizeOf_spec ModularCurve.Period.IsEquivariantPrimitive.periodHom_apply ModularCurve.Period.IsEquivariantPrimitive.period_one"
p2m_attr_erase "simp" "PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ ModularCurve.ProjectiveLine.map_mk AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule ModularCurve.cuspCount_one ModularCurve.CuspSpace.cuspDenomAux_infty ModularCurve.CuspSpace.cuspDenomAux_coe ModularCurve.CuspSpace.cuspDenom_mk_zero ModularCurve.CuspSpace.cuspDenom_mk_infty ModularCurve.mapGL_apply_coe ModularCurve.ratPoint_one_zero ModularCurve.ratPoint_zero_right ModularCurve.CuspSpace.fromCoset_mk ModularCurve.CuspSpace.cuspDenom_mk"
p2m_attr_erase "simp" "ModularCurve.ratPoint_zero_one ModularCurve.qEulerFun_coeff ModularCurve.diffQExp_D ModularCurve.qEulerOn_apply ModularCurve.qEuler_coeff ModularCurve.gamma0PairMap_gen ModularCurve.moduliPointMapRingHom_mk ModularCurve.Gamma0Pair.mk.injEq ModularCurve.ModuliPoint.j_mk ModularCurve.Gamma0Pair.mk.sizeOf_spec ModularCurve.gamma0PairMap_toCurve WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero WeierstrassCurve.ratPointHom_apply WeierstrassCurve.ratPointMap_zero ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ WeierstrassCurve.veluX_empty WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec"
p2m_attr_erase "simp" "WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply"
p2m_attr_erase "simp" "ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply HahnSeries.ramScale_apply WeierstrassCurve.veluPointMap2_zero FLT.TruncatedDomainPartition.unipotentDiagonalSum_zero HeckeEis.coeffCoboundaryMap_apply HeckeEis.heckeConjMat_apply_one_one HeckeEis.coe_heckeConjSL HeckeEis.mem_heckeUpperSL HeckeEis.resHom_apply HeckeEis.heckeConjMat_apply_zero_one HeckeEis.coe_transferAux HeckeEis.coe_heckeConj HeckeEis.alphaMat_apply_one_one HeckeEis.heckeConjMat_apply_one_zero HeckeEis.alphaMat_apply_zero_one HeckeEis.pullbackHom_apply HeckeEis.alphaMat_apply_one_zero HeckeEis.alphaMat_apply_zero_zero HeckeEis.heckeConjMat_apply_zero_zero ModularCurve.Period.jConjMat_apply_zero_one ModularCurve.Period.jConjSL_coe ModularCurve.Period.jConjMat_apply_one_zero ModularCurve.Period.jConjMat_apply_one_one ModularCurve.Period.jConjGamma0_coe ModularCurve.Period.charInvolution_apply ModularCurve.Period.jConjMat_apply_zero_zero PowerSeries.coeff_heckeV PowerSeries.coeff_heckeU"
p2m_attr_erase "simp" "AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap"

set_option autoImplicit false

open ModularCurve CuspForm

private theorem smul_eq_zero_of_idem_smul_of_pow_smul {T V : Type*} [CommRing T]
    [AddCommGroup V] [Module T V] (w : T) (x : V) (hidem : (w * w - w) • x = 0) :
    ∀ M : ℕ, w ^ M • x = 0 → w • x = 0
  | 0, h => by
      rw [pow_zero, one_smul] at h
      rw [h, smul_zero]
  | M + 1, h => by
      have key : ∀ n : ℕ, (w ^ (n + 1) - w) • x = 0 := by
        intro n
        induction n with
        | zero => rw [zero_add, pow_one, sub_self, zero_smul]
        | succ n ih =>
            have e : w ^ (n + 1 + 1) - w = w * (w ^ (n + 1) - w) + (w * w - w) := by ring
            rw [e, add_smul, mul_smul, ih, smul_zero, zero_add, hidem]
      have hk := key M
      rwa [sub_smul, h, zero_sub, neg_eq_zero] at hk

private theorem smul_eq_self_of_apply_idem_of_one_sub_apply_mem_map
    {T L V : Type*} [CommRing T] [CommRing L] [AddCommGroup V] [Module T V]
    (π : T →+* L) (hπ : Function.Surjective π) (hker : ∀ k : T, π k = 0 → ∀ v : V, k • v = 0)
    (P : Ideal T) (a u : T) (b : L) (hab : π a = b) (M : ℕ)
    (hidem : π u * π u - π u ∈ Ideal.span {b})
    (hone : 1 - π u ∈ Ideal.map π P)
    (x : V) (hP : ∀ t ∈ P ^ M, t • x = 0) (ha : a • x = 0) : u • x = x := by
  have hcongr : ∀ s t : T, π s = π t → s • x = t • x := fun s t hst => by
    have h0 : (s - t) • x = 0 := hker _ (by rw [map_sub, hst, sub_self]) x
    rwa [sub_smul, sub_eq_zero] at h0
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 hidem
  obtain ⟨c', rfl⟩ := hπ c
  have hidem' : (u * u - u) • x = 0 := by
    have h := hcongr (u * u - u) (c' * a) (by simp only [map_sub, map_mul]; rw [hab, hc])
    rw [h, mul_smul, ha, smul_zero]
  have hw_idem : ((1 - u) * (1 - u) - (1 - u)) • x = 0 := by
    have e : (1 - u) * (1 - u) - (1 - u) = u * u - u := by ring
    rw [e, hidem']
  have hwP : π ((1 - u) ^ M) ∈ Ideal.map π (P ^ M) := by
    rw [Ideal.map_pow, map_pow, map_sub, map_one]
    exact Ideal.pow_mem_pow hone M
  obtain ⟨t, ht, hteq⟩ := (Ideal.mem_map_iff_of_surjective π hπ).1 hwP
  have hwM : (1 - u) ^ M • x = 0 := by
    rw [hcongr _ _ hteq.symm]
    exact hP t ht
  have hw : (1 - u) • x = 0 :=
    smul_eq_zero_of_idem_smul_of_pow_smul (1 - u) x hw_idem M hwM
  rw [sub_smul, one_smul, sub_eq_zero] at hw
  exact hw.symm

private theorem exists_forall_mem_pow_smul_smul_eq_zero
    {T L V : Type*} [CommRing T] [CommRing L] [AddCommGroup V] [Module T V]
    (π : T →+* L) (hπ : Function.Surjective π) (hker : ∀ k : T, π k = 0 → ∀ v : V, k • v = 0)
    (P : Ideal T) (a u : T) (b : L) (hab : π a = b)
    (hann : ∃ N : ℕ, ∀ z ∈ (Ideal.map π P) ^ N, π u * z ∈ Ideal.span {b})
    (y : V) (ha : a • y = 0) : ∃ N : ℕ, ∀ t ∈ P ^ N, t • (u • y) = 0 := by
  obtain ⟨N, hN⟩ := hann
  refine ⟨N, fun t ht => ?_⟩
  have hz : π t ∈ (Ideal.map π P) ^ N := by
    rw [← Ideal.map_pow]
    exact Ideal.mem_map_of_mem π ht
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 (hN _ hz)
  obtain ⟨c', rfl⟩ := hπ c
  have h0 : (u * t - c' * a) • y = 0 :=
    hker _ (by simp only [map_sub, map_mul]; rw [hab, hc, sub_self]) y
  rw [sub_smul, sub_eq_zero, mul_smul, mul_smul, ha, smul_zero] at h0
  rw [← mul_smul, mul_comm t u, mul_smul, h0]

private theorem smul_eq_self_and_smul_mem_eisensteinTorsionBar (p : ℕ) [Fact p.Prime]
    (e : ℕ → HeckeAlg)
    (hidem : ∀ m : ℕ,
        ((latticeRestrictHom p ∅).toRingHom.comp (heckeEvalForms p 2)) (e m) *
            ((latticeRestrictHom p ∅).toRingHom.comp (heckeEvalForms p 2)) (e m) -
          ((latticeRestrictHom p ∅).toRingHom.comp (heckeEvalForms p 2)) (e m) ∈
            Ideal.span {((2 : ℕ) : ↥(heckeLatticeAlgebra p ∅)) ^ m})
    (hone : ∀ m : ℕ,
        1 - ((latticeRestrictHom p ∅).toRingHom.comp (heckeEvalForms p 2)) (e m) ∈
          Ideal.map ((latticeRestrictHom p ∅).toRingHom.comp (heckeEvalForms p 2))
            (eisensteinMaximalIdeal p 2))
    (hann : ∀ m : ℕ, ∃ N : ℕ,
        ∀ x ∈ (Ideal.map ((latticeRestrictHom p ∅).toRingHom.comp (heckeEvalForms p 2))
            (eisensteinMaximalIdeal p 2)) ^ N,
          ((latticeRestrictHom p ∅).toRingHom.comp (heckeEvalForms p 2)) (e m) * x ∈
            Ideal.span {((2 : ℕ) : ↥(heckeLatticeAlgebra p ∅)) ^ m}) :
    letI := heckeModuleBar p
    (∀ m M : ℕ, ∀ x ∈ eisensteinTorsionBar p 2 M, 2 ^ m • x = 0 → e m • x = x) ∧
      (∀ m : ℕ, ∀ y : JZero p, 2 ^ m • y = 0 →
        ∃ M : ℕ, e m • y ∈ eisensteinTorsionBar p 2 M) := by
  letI := heckeModuleBar p
  have hcomm : HeckeOperatorsCommuteBar p := ModularCurve.heckeOperatorsCommuteBar p
  have hπ : Function.Surjective ((latticeRestrictHom p ∅).toRingHom.comp (heckeEvalForms p 2)) := by
    intro z
    obtain ⟨t, rfl⟩ := latticeRestrictHom_surjective p ∅ z
    obtain ⟨s, rfl⟩ := (RingHom.range_eq_top.mp (heckeEvalForms_range_eq_top p 2)) t
    exact ⟨s, rfl⟩
  have hker : ∀ k : HeckeAlg, ((latticeRestrictHom p ∅).toRingHom.comp (heckeEvalForms p 2)) k = 0 →
      ∀ v : JZero p, k • v = 0 := by
    intro k hk v
    have hk' : k ∈ RingHom.ker (heckeEvalBar hcomm) := by
      rw [← ModularCurve.ker_heckeEvalForms_latticeRestrict_eq_ker_heckeEvalBar p hcomm]
      exact RingHom.mem_ker.mpr hk
    exact (heckeModuleBar_smul_def hcomm k v).trans
      (by rw [RingHom.mem_ker.mp hk', LinearMap.zero_apply])
  have hab : ∀ m : ℕ,
      ((latticeRestrictHom p ∅).toRingHom.comp (heckeEvalForms p 2)) ((2 ^ m : ℕ) : HeckeAlg) =
        ((2 : ℕ) : ↥(heckeLatticeAlgebra p ∅)) ^ m := fun m => by
    rw [map_natCast, Nat.cast_pow]
  have hcast : ∀ (m : ℕ) (v : JZero p), 2 ^ m • v = 0 → ((2 ^ m : ℕ) : HeckeAlg) • v = 0 :=
    fun m v hv => by rw [Nat.cast_smul_eq_nsmul]; exact hv
  refine ⟨fun m M x hx hmx => ?_, fun m y hmy => ?_⟩
  · have hx' : x ∈ Submodule.torsionBySet HeckeAlg (JZero p)
        (↑((eisensteinMaximalIdeal p 2) ^ M) : Set HeckeAlg) := hx
    rw [Submodule.mem_torsionBySet_iff] at hx'
    exact smul_eq_self_of_apply_idem_of_one_sub_apply_mem_map
      ((latticeRestrictHom p ∅).toRingHom.comp (heckeEvalForms p 2)) hπ hker
      (eisensteinMaximalIdeal p 2) ((2 ^ m : ℕ) : HeckeAlg) (e m)
      (((2 : ℕ) : ↥(heckeLatticeAlgebra p ∅)) ^ m) (hab m) M (hidem m) (hone m)
      x (fun t ht => hx' ⟨t, ht⟩) (hcast m x hmx)
  · obtain ⟨N, hN⟩ := exists_forall_mem_pow_smul_smul_eq_zero
      ((latticeRestrictHom p ∅).toRingHom.comp (heckeEvalForms p 2)) hπ hker
      (eisensteinMaximalIdeal p 2) ((2 ^ m : ℕ) : HeckeAlg) (e m)
      (((2 : ℕ) : ↥(heckeLatticeAlgebra p ∅)) ^ m) (hab m) (hann m) y (hcast m y hmy)
    refine ⟨N, ?_⟩
    show e m • y ∈ Submodule.torsionBySet HeckeAlg (JZero p)
        (↑((eisensteinMaximalIdeal p 2) ^ N) : Set HeckeAlg)
    rw [Submodule.mem_torsionBySet_iff]
    exact fun t => hN t.1 t.2

private theorem finite_quotient_natCast (L : Type) [CommRing L] [Module.Finite ℤ L] (n : ℕ) (hn : n ≠ 0) :
    Finite (L ⧸ Ideal.span {((n : ℕ) : L)}) := by
  haveI : Module.Finite ℤ (L ⧸ Ideal.span {((n : ℕ) : L)}) :=
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ ℤ (Ideal.span {((n : ℕ) : L)})).toLinearMap
      Ideal.Quotient.mk_surjective
  refine Module.finite_of_fg_torsion _ (AddMonoid.isTorsion_iff_isTorsion_int.mp ?_)
  intro x
  rw [isOfFinAddOrder_iff_nsmul_eq_zero]
  refine ⟨n, Nat.pos_of_ne_zero hn, ?_⟩
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [← map_nsmul, Ideal.Quotient.eq_zero_iff_mem, nsmul_eq_mul]
  exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)

private theorem hfin (p : ℕ) [Fact p.Prime] :
    Finite (↥(heckeLatticeAlgebra p ∅) ⧸ Ideal.span {((2 : ℕ) : ↥(heckeLatticeAlgebra p ∅))}) :=
  finite_quotient_natCast _ 2 two_ne_zero

private theorem eisensteinMaximalIdeal_two_isMaximal (p : ℕ) :
    (eisensteinMaximalIdeal p 2).IsMaximal := by
  haveI : (Ideal.span {(2 : ℤ)}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible Int.prime_two.irreducible
  have hsurj : Function.Surjective (eisensteinEval p) := fun n =>
    ⟨algebraMap ℤ HeckeAlg n, (eisensteinEval p).commutes n⟩
  unfold eisensteinMaximalIdeal
  exact_mod_cast Ideal.comap_isMaximal_of_surjective (eisensteinEval p) hsurj

private theorem pi_surjective (p : ℕ) [Fact p.Prime] :
    Function.Surjective ((latticeRestrictHom p ∅).toRingHom.comp (heckeEvalForms p 2)) := by
  intro z
  obtain ⟨t, rfl⟩ := latticeRestrictHom_surjective p ∅ z
  obtain ⟨a, rfl⟩ := (RingHom.range_eq_top.mp (heckeEvalForms_range_eq_top p 2)) t
  exact ⟨a, rfl⟩

private theorem map_eisenstein_eq_top_or_isMaximal (p : ℕ) [Fact p.Prime] :
    Ideal.map ((latticeRestrictHom p ∅).toRingHom.comp (heckeEvalForms p 2)) (eisensteinMaximalIdeal p 2) = ⊤ ∨
      (Ideal.map ((latticeRestrictHom p ∅).toRingHom.comp (heckeEvalForms p 2)) (eisensteinMaximalIdeal p 2)).IsMaximal :=
  Ideal.map_eq_top_or_isMaximal_of_surjective _ (pi_surjective p) (eisensteinMaximalIdeal_two_isMaximal p)

private theorem two_mem_map_eisenstein (p : ℕ) [Fact p.Prime] :
    ((2 : ℕ) : ↥(heckeLatticeAlgebra p ∅)) ∈
      Ideal.map ((latticeRestrictHom p ∅).toRingHom.comp (heckeEvalForms p 2)) (eisensteinMaximalIdeal p 2) := by
  have h := Ideal.mem_map_of_mem ((latticeRestrictHom p ∅).toRingHom.comp (heckeEvalForms p 2))
    (natCast_mem_eisensteinMaximalIdeal p 2)
  rwa [map_natCast] at h

private theorem hdense_of_surjective {L : Type} [CommRing L] (ℓ : L) {T : Type} [CommRing T]
    (π : T →+* L) (hsurj : Function.Surjective π) :
    ∀ (m : ℕ) (x : L), ∃ y : T, π y - x ∈ Ideal.span {ℓ ^ m} := by
  intro m x
  obtain ⟨y, hy⟩ := hsurj x
  exact ⟨y, by rw [hy, sub_self]; exact Ideal.zero_mem _⟩

private theorem solution_of_map_eq_top (p : ℕ) [Fact p.Prime]
    (htop : Ideal.map ((latticeRestrictHom p ∅).toRingHom.comp (heckeEvalForms p 2)) (eisensteinMaximalIdeal p 2) = ⊤) :
    letI := heckeModuleBar p
    ∃ te : ℕ → HeckeAlg,
      (∀ m : ℕ,
        ((latticeRestrictHom p ∅).toRingHom.comp (heckeEvalForms p 2)) (te m) *
            ((latticeRestrictHom p ∅).toRingHom.comp (heckeEvalForms p 2)) (te m) -
          ((latticeRestrictHom p ∅).toRingHom.comp (heckeEvalForms p 2)) (te m) ∈
            Ideal.span {((2 : ℕ) : ↥(heckeLatticeAlgebra p ∅)) ^ m}) ∧
      (∀ m : ℕ,
        ((latticeRestrictHom p ∅).toRingHom.comp (heckeEvalForms p 2)) (te (m + 1)) -
          ((latticeRestrictHom p ∅).toRingHom.comp (heckeEvalForms p 2)) (te m) ∈
            Ideal.span {((2 : ℕ) : ↥(heckeLatticeAlgebra p ∅)) ^ m}) ∧
      (∀ m M : ℕ, ∀ x ∈ eisensteinTorsionBar p 2 M, 2 ^ m • x = 0 → te m • x = x) ∧
      (∀ m : ℕ, ∀ y : JZero p, 2 ^ m • y = 0 → ∃ M : ℕ, te m • y ∈ eisensteinTorsionBar p 2 M) := by
  have h := smul_eq_self_and_smul_mem_eisensteinTorsionBar p 0
    (fun m => by simp)
    (fun m => by rw [htop]; exact Submodule.mem_top)
    (fun m => ⟨0, fun x _ => by simp⟩)
  exact ⟨0, fun m => by simp, fun m => by simp, h.1, h.2⟩

private theorem solution_of_map_isMaximal (p : ℕ) [Fact p.Prime]
    (hmax : (Ideal.map ((latticeRestrictHom p ∅).toRingHom.comp (heckeEvalForms p 2)) (eisensteinMaximalIdeal p 2)).IsMaximal) :
    letI := heckeModuleBar p
    ∃ te : ℕ → HeckeAlg,
      (∀ m : ℕ,
        ((latticeRestrictHom p ∅).toRingHom.comp (heckeEvalForms p 2)) (te m) *
            ((latticeRestrictHom p ∅).toRingHom.comp (heckeEvalForms p 2)) (te m) -
          ((latticeRestrictHom p ∅).toRingHom.comp (heckeEvalForms p 2)) (te m) ∈
            Ideal.span {((2 : ℕ) : ↥(heckeLatticeAlgebra p ∅)) ^ m}) ∧
      (∀ m : ℕ,
        ((latticeRestrictHom p ∅).toRingHom.comp (heckeEvalForms p 2)) (te (m + 1)) -
          ((latticeRestrictHom p ∅).toRingHom.comp (heckeEvalForms p 2)) (te m) ∈
            Ideal.span {((2 : ℕ) : ↥(heckeLatticeAlgebra p ∅)) ^ m}) ∧
      (∀ m M : ℕ, ∀ x ∈ eisensteinTorsionBar p 2 M, 2 ^ m • x = 0 → te m • x = x) ∧
      (∀ m : ℕ, ∀ y : JZero p, 2 ^ m • y = 0 → ∃ M : ℕ, te m • y ∈ eisensteinTorsionBar p 2 M) := by
  haveI := hmax
  obtain ⟨e, h1, h2, h3, -, h5⟩ :=
    exists_idempotent_tower_of_finite_quotient_of_isMaximal
      ((2 : ℕ) : ↥(heckeLatticeAlgebra p ∅)) (hfin p) (Ideal.map ((latticeRestrictHom p ∅).toRingHom.comp (heckeEvalForms p 2)) (eisensteinMaximalIdeal p 2)) (two_mem_map_eisenstein p)
      ((latticeRestrictHom p ∅).toRingHom.comp (heckeEvalForms p 2))
      (hdense_of_surjective ((2 : ℕ) : ↥(heckeLatticeAlgebra p ∅)) ((latticeRestrictHom p ∅).toRingHom.comp (heckeEvalForms p 2)) (pi_surjective p))
  have h := smul_eq_self_and_smul_mem_eisensteinTorsionBar p e h1 h3 h5
  exact ⟨e, h1, h2, h.1, h.2⟩

theorem solution
    (p : ℕ) [Fact p.Prime] :
    letI := heckeModuleBar p
    ∃ te : ℕ → HeckeAlg,
      (∀ m : ℕ,
        ((latticeRestrictHom p ∅).toRingHom.comp (heckeEvalForms p 2)) (te m) *
            ((latticeRestrictHom p ∅).toRingHom.comp (heckeEvalForms p 2)) (te m) -
          ((latticeRestrictHom p ∅).toRingHom.comp (heckeEvalForms p 2)) (te m) ∈
            Ideal.span {((2 : ℕ) : ↥(heckeLatticeAlgebra p ∅)) ^ m}) ∧
      (∀ m : ℕ,
        ((latticeRestrictHom p ∅).toRingHom.comp (heckeEvalForms p 2)) (te (m + 1)) -
          ((latticeRestrictHom p ∅).toRingHom.comp (heckeEvalForms p 2)) (te m) ∈
            Ideal.span {((2 : ℕ) : ↥(heckeLatticeAlgebra p ∅)) ^ m}) ∧
      (∀ m M : ℕ, ∀ x ∈ eisensteinTorsionBar p 2 M, 2 ^ m • x = 0 → te m • x = x) ∧
      (∀ m : ℕ, ∀ y : JZero p, 2 ^ m • y = 0 → ∃ M : ℕ, te m • y ∈ eisensteinTorsionBar p 2 M) := by
  rcases map_eisenstein_eq_top_or_isMaximal p with h | h
  · exact solution_of_map_eq_top p h
  · exact solution_of_map_isMaximal p h

end S_ModularCurve_exists_heckeAlg_idempotent_tower_smul_eq_self_of_mem_eisensteinTorsionBar
end P2MW
export P2MW.S_ModularCurve_exists_heckeAlg_idempotent_tower_smul_eq_self_of_mem_eisensteinTorsionBar (solution)
