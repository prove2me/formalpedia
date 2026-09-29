-- Prove2me | solution 1 for ModularCurve.ComplexPlaceDictionaryOf.isPrincipal_of_abelJacobi_mem_periodLatticeOf_gammaH
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/7e85fbb0-e134-5796-8544-995706b6e66f

import Mathlib
import Definitions.Def_ModularCurve_ComplexPlaceDictionaryOf
import Definitions.Def_ModularCurve_XH
import Definitions.Def_ModularCurve_PeriodOf
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_JqCoeff
import Theorems.Thm_ModularCurve_ComplexPlaceDictionaryOf_exists_meromorphic_meromorphicOrderAt_eq_of_abelJacobi_mem_periodLatticeOf_gammaH
import Theorems.Thm_ModularCurve_exists_realizeOf_eventuallyEq_of_meromorphic_gammaH
import Theorems.Thm_ModularCurve_ord_eq_zero_of_not_mem_of_realizeOf_tendsto
import Theorems.Thm_ModularCurve_ComplexPlaceDictionaryOf_exists_pt_eq_of_mem
import Theorems.Thm_ModularCurve_jqModC_mem_intFormRatiosC
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_ComplexPlaceDictionaryOf_isPrincipal_of_abelJacobi_mem_periodLatticeOf_gammaH
p2m_attr_erase "instance" "AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom"
p2m_attr_erase "instance" "AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.Period.parabolicHoms_int_moduleFinite ModularCurve.Period.instGroupFG_SL2Z ModularCurve.Period.instIsNoetherian_addHom_int ModularCurve.Period.instGroupFG_Gamma0 HeckeEis.instFiniteIndexHeckeUpper FLT.Gamma0FundamentalSet.instContinuousConstSMulSpecialLinearGroupFinOfNatNatIntUpperHalfPlane_definitions FLT.HyperbolicMeasure.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatIntUpperHalfPlaneVolume_definitions FLT.HyperbolicMeasure.instIsOpenPosMeasureUpperHalfPlaneVolume_definitions FLT.L2ProductionInstance.isFiniteMeasure_gamma0 FLT.L2ProductionInstance.countable_SL2Z FLT.L2ProductionInstance.countable_quotient FLT.L2ProductionInstance.nontrivial_gamma0L2 HeckeEis.instModuleCoeffH1par HeckeEis.instAddCommGroupCoeffH1par"
p2m_attr_erase "simp" "AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom ModularCurve.qExpandAlgHomC_apply WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_cuspidalDivisor₀ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk"
p2m_attr_erase "simp" "ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.eisensteinNumerator_nineteen"
p2m_attr_erase "simp" "ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one"
p2m_attr_erase "simp" "AlgebraicCurve.Place.mem_poleSubmodule PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ HeckeEis.heckeConjMat_apply_one_one HeckeEis.coe_heckeConjSL HeckeEis.mem_heckeUpperSL HeckeEis.resHom_apply HeckeEis.heckeConjMat_apply_zero_one HeckeEis.coe_transferAux HeckeEis.coe_heckeConj HeckeEis.alphaMat_apply_one_one HeckeEis.heckeConjMat_apply_one_zero HeckeEis.alphaMat_apply_zero_one HeckeEis.pullbackHom_apply HeckeEis.alphaMat_apply_one_zero HeckeEis.alphaMat_apply_zero_zero HeckeEis.heckeConjMat_apply_zero_zero ModularCurve.LevelN.coe_jGen AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq FLT.TruncatedDomainPartition.unipotentDiagonalSum_zero HeckeEis.coeffCoboundaryMap_apply"

noncomputable section

open UpperHalfPlane
open scoped MatrixGroups Topology

namespace ModularCurve
p2m_export "ModularCurve" "realizeOf realizeOf_def ComplexPlaceDictionaryOf coeffEmb laurentBaseChange coeffEmb_mem_laurentBaseChange ComplexPlaceDictionary translation_mem_GammaH Gamma1_le_GammaH xHFunctionField qExpFunctionFieldC intFormRatiosC_subset periodAlongOf periodLatticeOf period jqModC map_jqModC ComplexPlaceDictionaryOf.exists_meromorphic_meromorphicOrderAt_eq_of_abelJacobi_mem_periodLatticeOf_gammaH exists_realizeOf_eventuallyEq_of_meromorphic_gammaH ord_eq_zero_of_not_mem_of_realizeOf_tendsto ComplexPlaceDictionaryOf.exists_pt_eq_of_mem jqModC_mem_intFormRatiosC"
namespace AbelConverseGlueH
p2m_open "ModularCurve"

theorem realizeOf_zero {Γ : Subgroup SL(2, ℤ)} (hT : ModularGroup.T ∈ Γ) (τ : ℍ) :
    ModularCurve.realizeOf Γ 0 τ = 0 := by
  rw [ModularCurve.realizeOf_def]
  split_ifs with H
  · obtain ⟨-, hx⟩ := H.choose_spec
    rw [zero_mul] at hx
    have h1 : (1 : ℝ) ∈ (Γ : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
      rw [Subgroup.strictPeriods_eq_zmultiples_one_of_T_mem hT]
      exact AddSubgroup.mem_zmultiples _
    have hg : H.choose.2.1 = 0 := by
      rw [← ModularForm.qExpansion_eq_zero_iff one_pos h1]
      apply HahnSeries.ofPowerSeries_injective (Γ := ℤ) (R := ℂ)
      simpa using hx.symm
    simp [hg]
  · rfl

theorem isBigO_of_tendsto {F : ℍ → ℂ}
    (hcusp : ∀ σ : SL(2, ℤ), ∃ L : ℂ, L ≠ 0 ∧
      Filter.Tendsto (fun τ : ℍ => F (σ • τ)) atImInfty (𝓝 L)) :
    ∀ σ : SL(2, ℤ), ∃ C : ℝ,
      Asymptotics.IsBigO atImInfty (fun τ : ℍ => F (σ • τ)) fun τ : ℍ => Real.exp (C * τ.im) := by
  intro σ
  obtain ⟨L, -, hL⟩ := hcusp σ
  refine ⟨0, ?_⟩
  simpa only [zero_mul, Real.exp_zero] using hL.isBigO_one ℝ

theorem jqModC_mem_laurentBaseChange (Γ : Subgroup SL(2, ℤ)) :
    ModularCurve.jqModC ℂ ∈ ModularCurve.laurentBaseChange ℂ (ModularCurve.qExpFunctionFieldC ℚ Γ) := by
  have h := ModularCurve.coeffEmb_mem_laurentBaseChange ℂ
    (ModularCurve.intFormRatiosC_subset ℚ Γ (ModularCurve.jqModC_mem_intFormRatiosC ℚ Γ))
  have e : ModularCurve.coeffEmb ℂ (ModularCurve.jqModC ℚ) = ModularCurve.jqModC ℂ :=
    ModularCurve.map_jqModC (algebraMap ℚ ℂ)
  rwa [e] at h

variable (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ)

scoped instance finiteIndex_gammaH : (CohCarrier.GammaH M H).FiniteIndex :=
  Subgroup.finiteIndex_of_le (ModularCurve.Gamma1_le_GammaH M H)

theorem isCongruenceSubgroup_gammaH :
    CongruenceSubgroup.IsCongruenceSubgroup (CohCarrier.GammaH M H) :=
  CongruenceSubgroup.isCongruenceSubgroup_trans _ _ (ModularCurve.Gamma1_le_GammaH M H)
    (CongruenceSubgroup.Gamma1_is_congruence M)

end ModularCurve.AbelConverseGlueH
p2m_reactivate "P2MW.S_ModularCurve_ComplexPlaceDictionaryOf_isPrincipal_of_abelJacobi_mem_periodLatticeOf_gammaH.ModularCurve P2MW.S_ModularCurve_ComplexPlaceDictionaryOf_isPrincipal_of_abelJacobi_mem_periodLatticeOf_gammaH.ModularCurve.AbelConverseGlueH"
p2m_reactivate "P2MW.S_ModularCurve_ComplexPlaceDictionaryOf_isPrincipal_of_abelJacobi_mem_periodLatticeOf_gammaH.ModularCurve"

end
p2m_reactivate "P2MW.S_ModularCurve_ComplexPlaceDictionaryOf_isPrincipal_of_abelJacobi_mem_periodLatticeOf_gammaH.ModularCurve P2MW.S_ModularCurve_ComplexPlaceDictionaryOf_isPrincipal_of_abelJacobi_mem_periodLatticeOf_gammaH.ModularCurve.AbelConverseGlueH"

open UpperHalfPlane ModularCurve.AbelConverseGlueH in
open scoped MatrixGroups Topology in
theorem solution
    (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ)
    (D : ModularCurve.ComplexPlaceDictionaryOf (CohCarrier.GammaH M H) (ModularCurve.xHFunctionField M H))
    (c : UpperHalfPlane →₀ ℤ)
    (hdeg : AlgebraicCurve.Divisor.degree (Finsupp.mapDomain D.pt c) = 0)
    (hΛ : (c.sum fun τ n => n • ModularCurve.periodAlongOf (CohCarrier.GammaH M H) UpperHalfPlane.I τ) ∈
      ModularCurve.periodLatticeOf (CohCarrier.GammaH M H)) :
    AlgebraicCurve.Divisor.IsPrincipal (Finsupp.mapDomain D.pt c) := by
  have hT : ModularGroup.T ∈ CohCarrier.GammaH M H := ModularCurve.translation_mem_GammaH M H

  obtain ⟨F, hmer, hinv, hcusp, hord⟩ :=
    ModularCurve.ComplexPlaceDictionaryOf.exists_meromorphic_meromorphicOrderAt_eq_of_abelJacobi_mem_periodLatticeOf_gammaH
      M H D c hdeg hΛ

  obtain ⟨x₀, hx₀, hFx⟩ := ModularCurve.exists_realizeOf_eventuallyEq_of_meromorphic_gammaH M H F hmer hinv
    (isBigO_of_tendsto hcusp)
  set x : ModularCurve.laurentBaseChange ℂ (ModularCurve.xHFunctionField M H) := ⟨x₀, hx₀⟩
  have hFx' : ∀ τ : ℍ, (fun z : ℂ => F (ofComplex z)) =ᶠ[𝓝[≠] (τ : ℂ)]
      fun z : ℂ => ModularCurve.realizeOf (CohCarrier.GammaH M H) (x : LaurentSeries ℂ) (ofComplex z) := hFx

  have hx0 : x ≠ 0 := by
    intro h0
    have hz : (x : LaurentSeries ℂ) = 0 := by simp [h0]
    have h2 : meromorphicOrderAt (fun z : ℂ => F (ofComplex z)) (UpperHalfPlane.I : ℂ) = ⊤ := by
      rw [meromorphicOrderAt_eq_top_iff]
      filter_upwards [hFx' UpperHalfPlane.I] with z hz'
      rw [hz', hz, realizeOf_zero hT]
    have h1 := hord UpperHalfPlane.I
    rw [h2] at h1
    exact WithTop.top_ne_coe h1

  set y : ModularCurve.laurentBaseChange ℂ (ModularCurve.xHFunctionField M H) :=
    ⟨ModularCurve.jqModC ℂ, jqModC_mem_laurentBaseChange (CohCarrier.GammaH M H)⟩ with hy_def
  have hy : (y : LaurentSeries ℂ) = ModularCurve.jqModC ℂ := rfl
  refine ⟨x, hx0, fun v => ?_⟩
  by_cases hv : v ∈ Set.range D.pt
  ·
    obtain ⟨τ, rfl⟩ := hv
    have h1 := D.meromorphicOrderAt_realizeOf τ x hx0
    rw [← meromorphicOrderAt_congr (hFx' τ), hord τ] at h1
    have hr : (D.ramification τ : ℤ) ≠ 0 := by exact_mod_cast (D.ramification_pos τ).ne'
    exact mul_left_cancel₀ hr (WithTop.coe_injective h1)
  ·
    rw [Finsupp.mapDomain_notin_range _ _ hv]
    refine (ModularCurve.ord_eq_zero_of_not_mem_of_realizeOf_tendsto (CohCarrier.GammaH M H) hT
      (isCongruenceSubgroup_gammaH M H) (ModularCurve.xHFunctionField M H) rfl x F hFx' hcusp v y hy
      fun hj => hv ?_).symm
    obtain ⟨τ, hτ⟩ := ModularCurve.ComplexPlaceDictionaryOf.exists_pt_eq_of_mem (CohCarrier.GammaH M H) hT
      (ModularCurve.xHFunctionField M H) rfl D v y hy hj
    exact ⟨τ, hτ⟩

end S_ModularCurve_ComplexPlaceDictionaryOf_isPrincipal_of_abelJacobi_mem_periodLatticeOf_gammaH
end P2MW
export P2MW.S_ModularCurve_ComplexPlaceDictionaryOf_isPrincipal_of_abelJacobi_mem_periodLatticeOf_gammaH (solution)
