-- Prove2me | solution 1 for ModularCurve.ComplexPlaceDictionaryOf.exists_meromorphic_meromorphicOrderAt_eq_of_abelJacobi_mem_periodLatticeOf_gammaH
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/791d3466-5604-5419-b680-a6a9a4c348f5

import Mathlib
import Definitions.Def_ModularCurve_ComplexPlaceDictionaryOf
import Definitions.Def_ModularCurve_XH
import Definitions.Def_ModularCurve_PeriodOf
import Theorems.Thm_ModularCurve_exists_hasEquivariantPrimitiveOf
import Theorems.Thm_ModularCurve_periodOf_apply_eq_sub_of_hasEquivariantPrimitiveOf
import Theorems.Thm_ModularCurve_ComplexPlaceDictionaryOf_exists_slashInvariant_residue_eq_of_degree_eq_zero_gammaH
import Theorems.Thm_ModularCurve_exists_meromorphic_smul_eq_mul_of_slashInvariant_residue
import Theorems.Thm_ModularCurve_ComplexPlaceDictionaryOf_exists_cuspForm_mul_exp_periodOf_eq_one_of_abelJacobi_mem_periodLatticeOf_gammaH
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_ComplexPlaceDictionaryOf_exists_meromorphic_meromorphicOrderAt_eq_of_abelJacobi_mem_periodLatticeOf_gammaH
p2m_attr_erase "instance" "AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom"
p2m_attr_erase "instance" "AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.Period.parabolicHoms_int_moduleFinite ModularCurve.Period.instGroupFG_SL2Z ModularCurve.Period.instIsNoetherian_addHom_int ModularCurve.Period.instGroupFG_Gamma0 HeckeEis.instFiniteIndexHeckeUpper FLT.Gamma0FundamentalSet.instContinuousConstSMulSpecialLinearGroupFinOfNatNatIntUpperHalfPlane_definitions FLT.HyperbolicMeasure.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatIntUpperHalfPlaneVolume_definitions FLT.HyperbolicMeasure.instIsOpenPosMeasureUpperHalfPlaneVolume_definitions FLT.L2ProductionInstance.isFiniteMeasure_gamma0 FLT.L2ProductionInstance.countable_SL2Z FLT.L2ProductionInstance.countable_quotient FLT.L2ProductionInstance.nontrivial_gamma0L2 HeckeEis.instModuleCoeffH1par HeckeEis.instAddCommGroupCoeffH1par"
p2m_attr_erase "simp" "AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom ModularCurve.qExpandAlgHomC_apply ModularCurve.jqNModC_one WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_cuspidalDivisor₀ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply"
p2m_attr_erase "simp" "ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ"
p2m_attr_erase "simp" "ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ HeckeEis.heckeConjMat_apply_one_one HeckeEis.coe_heckeConjSL HeckeEis.mem_heckeUpperSL HeckeEis.resHom_apply HeckeEis.heckeConjMat_apply_zero_one HeckeEis.coe_transferAux HeckeEis.coe_heckeConj HeckeEis.alphaMat_apply_one_one HeckeEis.heckeConjMat_apply_one_zero HeckeEis.alphaMat_apply_zero_one HeckeEis.pullbackHom_apply HeckeEis.alphaMat_apply_one_zero HeckeEis.alphaMat_apply_zero_zero HeckeEis.heckeConjMat_apply_zero_zero ModularCurve.LevelN.coe_jGen AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq FLT.TruncatedDomainPartition.unipotentDiagonalSum_zero HeckeEis.coeffCoboundaryMap_apply"

set_option autoImplicit false

open UpperHalfPlane
open scoped MatrixGroups Topology ModularForm

namespace ModularCurve
p2m_export "ModularCurve" "ComplexPlaceDictionaryOf ComplexPlaceDictionary Gamma1_le_GammaH xHFunctionField periodAlongOf periodOf periodLatticeOf period exists_hasEquivariantPrimitiveOf periodOf_apply_eq_sub_of_hasEquivariantPrimitiveOf ComplexPlaceDictionaryOf.exists_slashInvariant_residue_eq_of_degree_eq_zero_gammaH exists_meromorphic_smul_eq_mul_of_slashInvariant_residue ComplexPlaceDictionaryOf.exists_cuspForm_mul_exp_periodOf_eq_one_of_abelJacobi_mem_periodLatticeOf_gammaH"
namespace AbelSufficiencyAssemblyH
p2m_open "ModularCurve"

open Filter Complex

theorem analyticAt_exp_comp {Φ : ℍ → ℂ} {f : ℍ → ℂ}
    (hΦ : ∀ τ : ℍ, HasDerivAt (Φ ∘ ofComplex) (f τ) (τ : ℂ)) (τ : ℍ) :
    AnalyticAt ℂ (fun z : ℂ => Complex.exp (Φ (ofComplex z))) (τ : ℂ) := by
  have hd : DifferentiableOn ℂ (Φ ∘ ofComplex) {z : ℂ | 0 < z.im} := by
    intro z hz
    have h := hΦ ⟨z, hz⟩
    exact h.differentiableAt.differentiableWithinAt
  have ha : AnalyticAt ℂ (Φ ∘ ofComplex) (τ : ℂ) :=
    hd.analyticAt (isOpen_upperHalfPlaneSet.mem_nhds τ.im_pos)
  exact ha.cexp

theorem meromorphicOrderAt_exp_comp {Φ : ℍ → ℂ} {f : ℍ → ℂ}
    (hΦ : ∀ τ : ℍ, HasDerivAt (Φ ∘ ofComplex) (f τ) (τ : ℂ)) (τ : ℍ) :
    meromorphicOrderAt (fun z : ℂ => Complex.exp (Φ (ofComplex z))) (τ : ℂ) = 0 := by
  have ha := analyticAt_exp_comp hΦ τ
  rw [ha.meromorphicOrderAt_eq]
  have h0 : analyticOrderAt (fun z : ℂ => Complex.exp (Φ (ofComplex z))) (τ : ℂ) = 0 := by
    rw [ha.analyticOrderAt_eq_zero]
    exact Complex.exp_ne_zero _
  simp [h0]

end ModularCurve.AbelSufficiencyAssemblyH

open ModularCurve.AbelSufficiencyAssemblyH in
theorem solution
    (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ)
    (D : ModularCurve.ComplexPlaceDictionaryOf (CohCarrier.GammaH M H) (ModularCurve.xHFunctionField M H))
    (c : UpperHalfPlane →₀ ℤ)
    (hdeg : AlgebraicCurve.Divisor.degree (Finsupp.mapDomain D.pt c) = 0)
    (hΛ : (c.sum fun τ n => n • ModularCurve.periodAlongOf (CohCarrier.GammaH M H) UpperHalfPlane.I τ) ∈
      ModularCurve.periodLatticeOf (CohCarrier.GammaH M H)) :
    ∃ F : UpperHalfPlane → ℂ,
      (∀ τ : UpperHalfPlane, MeromorphicAt (fun z : ℂ => F (UpperHalfPlane.ofComplex z)) (τ : ℂ)) ∧
      (∀ γ ∈ CohCarrier.GammaH M H, ∀ τ : UpperHalfPlane, F (γ • τ) = F τ) ∧
      (∀ σ : SL(2, ℤ), ∃ L : ℂ, L ≠ 0 ∧
        Filter.Tendsto (fun τ : UpperHalfPlane => F (σ • τ)) UpperHalfPlane.atImInfty (𝓝 L)) ∧
      ∀ τ : UpperHalfPlane, meromorphicOrderAt (fun z : ℂ => F (UpperHalfPlane.ofComplex z)) (τ : ℂ) =
        (((D.ramification τ : ℤ) * Finsupp.mapDomain D.pt c (D.pt τ) : ℤ) : WithTop ℤ) := by
  classical
  haveI : (CohCarrier.GammaH M H).FiniteIndex :=
    Subgroup.finiteIndex_of_le (ModularCurve.Gamma1_le_GammaH M H)

  obtain ⟨ω, hωΓ, hωcusp, hωres⟩ :=
    ModularCurve.ComplexPlaceDictionaryOf.exists_slashInvariant_residue_eq_of_degree_eq_zero_gammaH
      M H D c hdeg

  obtain ⟨F₁, χ, hmer, hχ, hcusp₁, hord⟩ :=
    ModularCurve.exists_meromorphic_smul_eq_mul_of_slashInvariant_residue
      (CohCarrier.GammaH M H)
      (fun τ => (D.ramification τ : ℤ) * Finsupp.mapDomain D.pt c (D.pt τ)) ω hωΓ hωcusp hωres

  obtain ⟨f, hf⟩ :=
    ModularCurve.ComplexPlaceDictionaryOf.exists_cuspForm_mul_exp_periodOf_eq_one_of_abelJacobi_mem_periodLatticeOf_gammaH
      M H D c hdeg hΛ F₁ χ hmer hχ hcusp₁ hord

  obtain ⟨Φ, hΦ⟩ := ModularCurve.exists_hasEquivariantPrimitiveOf (CohCarrier.GammaH M H) f
  have hperiod : ∀ γ : CohCarrier.GammaH M H, ∀ τ : ℍ,
      Φ ((γ : SL(2, ℤ)) • τ) = Φ τ + ModularCurve.periodOf (CohCarrier.GammaH M H) γ f := by
    intro γ τ
    have h1 := hΦ.2.2.1.sub_eq_period γ τ
    have h2 := ModularCurve.periodOf_apply_eq_sub_of_hasEquivariantPrimitiveOf (CohCarrier.GammaH M H) f hΦ γ
    have h3 : hΦ.2.2.1.period γ = Φ ((γ : SL(2, ℤ)) • UpperHalfPlane.I) - Φ UpperHalfPlane.I :=
      rfl
    rw [h2, ← h3, ← h1]; ring

  refine ⟨fun τ => F₁ τ * Complex.exp (Φ τ), ?_, ?_, ?_, ?_⟩
  · intro τ
    exact (hmer τ).mul (analyticAt_exp_comp hΦ.1 τ).meromorphicAt
  · intro γ hγ τ
    have hχ' := hχ ⟨γ, hγ⟩ τ
    have hp := hperiod ⟨γ, hγ⟩ τ
    have hf' := hf ⟨γ, hγ⟩
    show F₁ (γ • τ) * Complex.exp (Φ (γ • τ)) = F₁ τ * Complex.exp (Φ τ)
    rw [hχ', hp, Complex.exp_add]
    calc χ ⟨γ, hγ⟩ * F₁ τ *
          (Complex.exp (Φ τ) * Complex.exp (ModularCurve.periodOf (CohCarrier.GammaH M H) ⟨γ, hγ⟩ f))
        = (χ ⟨γ, hγ⟩ * Complex.exp (ModularCurve.periodOf (CohCarrier.GammaH M H) ⟨γ, hγ⟩ f)) *
            (F₁ τ * Complex.exp (Φ τ)) := by ring
      _ = F₁ τ * Complex.exp (Φ τ) := by rw [hf', one_mul]
  · intro σ
    obtain ⟨L₁, hL₁, hT₁⟩ := hcusp₁ σ
    obtain ⟨L₂, hT₂⟩ := hΦ.2.2.2 σ
    refine ⟨L₁ * Complex.exp L₂, mul_ne_zero hL₁ (Complex.exp_ne_zero _), ?_⟩
    exact hT₁.mul ((Complex.continuous_exp.tendsto L₂).comp hT₂)
  · intro τ
    have h := fun_meromorphicOrderAt_mul (hmer τ) (analyticAt_exp_comp hΦ.1 τ).meromorphicAt
    rw [h, hord τ, meromorphicOrderAt_exp_comp hΦ.1 τ, add_zero]

end S_ModularCurve_ComplexPlaceDictionaryOf_exists_meromorphic_meromorphicOrderAt_eq_of_abelJacobi_mem_periodLatticeOf_gammaH
end P2MW
export P2MW.S_ModularCurve_ComplexPlaceDictionaryOf_exists_meromorphic_meromorphicOrderAt_eq_of_abelJacobi_mem_periodLatticeOf_gammaH (solution)
