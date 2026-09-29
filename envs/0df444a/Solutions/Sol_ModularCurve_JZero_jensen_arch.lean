-- Prove2me | solution 1 for ModularCurve.JZero.jensen_arch
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/99afb83e-71cb-5021-b408-e9082fcb89c2

import Definitions.Def_ModularCurve_JZeroHeightForm
import Definitions.Def_AlgebraicCurve_ChordalProximity
import Theorems.Thm_ModularCurve_JZero_jensen_arch_embedding
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_JZero_jensen_arch
p2m_attr_erase "instance" "AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK"
p2m_attr_erase "instance" "AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar ModularCurve.CuspSpace.instNonempty ModularCurve.CuspSpace.instSubsingletonOfOne ModularCurve.CuspSpace.instFinite ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid"
p2m_attr_erase "simp" "AlgebraicCurve.chowForm_zero AlgebraicCurve.secProd_zero AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.jqNModC_one ModularCurve.coe_cuspidalDivisor₀ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply"
p2m_attr_erase "simp" "AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL"
p2m_attr_erase "simp" "ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar"
p2m_attr_erase "simp" "HahnSeries.ramScale_apply AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq ModularCurve.cuspCount_one ModularCurve.ComplexPlaceDictionary.mk.injEq ModularCurve.ComplexPlaceDictionary.mk.sizeOf_spec ModularCurve.qExpandAlgHomC_apply ModularCurve.CuspSpace.cuspDenomAux_infty ModularCurve.CuspSpace.cuspDenomAux_coe ModularCurve.CuspSpace.cuspDenom_mk_zero ModularCurve.CuspSpace.cuspDenom_mk_infty ModularCurve.mapGL_apply_coe ModularCurve.ratPoint_one_zero ModularCurve.ratPoint_zero_right ModularCurve.CuspSpace.fromCoset_mk ModularCurve.CuspSpace.cuspDenom_mk ModularCurve.ratPoint_zero_one ModularCurve.ProjectiveLine.map_mk PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ ModularCurve.coe_frobeniusModL"
p2m_attr_erase "simp" "ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL MvPolynomial.logMahlerMeasure_C MvPolynomial.logMahlerMeasure_X MvPolynomial.logMahlerMeasure_zero MvPolynomial.volume_torusBox MvPolynomial.logMahlerMeasure_monomial MvPolynomial.logMahlerMeasure_one MvPolynomial.norm_circleMap_zero_one MvPolynomial.volume_real_torusBox"

set_option Elab.async false
set_option autoImplicit false
set_option maxHeartbeats 3200000

open AlgebraicCurve ModularCurve

noncomputable section

set_option backward.isDefEq.respectTransparency false in

private theorem E4A (L : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField ↥L]
    (ν : NumberField.InfinitePlace ↥L) :
    ∃ σ : (AlgebraicClosure ℚ) →+* ℂ, ∀ a : ↥L, ν a = ‖σ (a : AlgebraicClosure ℚ)‖ := by
  letI algLC : Algebra ↥L ℂ := RingHom.toAlgebra ν.embedding
  let σ₀ : (AlgebraicClosure ℚ) →ₐ[↥L] ℂ := IsAlgClosed.lift
  refine ⟨σ₀.toRingHom, fun a => ?_⟩
  have hcomm : σ₀.toRingHom ((a : ↥L) : AlgebraicClosure ℚ) = ν.embedding a := by
    have h1 := σ₀.commutes a
    have h2 : (algebraMap ↥L (AlgebraicClosure ℚ)) a = ((a : ↥L) : AlgebraicClosure ℚ) := rfl
    have h3 : (algebraMap ↥L ℂ) a = ν.embedding a := by
      rw [RingHom.algebraMap_toAlgebra]
    rw [h2, h3] at h1
    exact h1
  rw [hcomm]
  exact (NumberField.InfinitePlace.norm_embedding_eq ν a).symm

private theorem prox_transport {L : IntermediateField ℚ (AlgebraicClosure ℚ)}
    (σ : (AlgebraicClosure ℚ) →+* ℂ)
    {r : ℕ} (x y : Fin r → ↥L) (ex ey : Fin r → AlgebraicClosure ℚ)
    (hx : ∀ i, ((x i : ↥L) : AlgebraicClosure ℚ) = ex i)
    (hy : ∀ i, ((y i : ↥L) : AlgebraicClosure ℚ) = ey i)
    (ν : ↥L → ℝ) (hν : ∀ a : ↥L, ν a = ‖σ (a : AlgebraicClosure ℚ)‖) :
    prox ν x y = prox (fun a => ‖σ a‖) ex ey := by
  unfold prox
  have hA : (⨆ i, ν (x i)) = ⨆ i, ‖σ (ex i)‖ :=
    iSup_congr fun i => by rw [hν, hx]
  have hB : (⨆ i, ν (y i)) = ⨆ i, ‖σ (ey i)‖ :=
    iSup_congr fun i => by rw [hν, hy]
  have hC : (⨆ p : Fin r × Fin r, ν (x p.1 * y p.2 - x p.2 * y p.1))
      = ⨆ p : Fin r × Fin r, ‖σ (ex p.1 * ey p.2 - ex p.2 * ey p.1)‖ := by
    refine iSup_congr fun p => ?_
    rw [hν]
    congr 1
    have : ((x p.1 * y p.2 - x p.2 * y p.1 : ↥L) : AlgebraicClosure ℚ)
        = ex p.1 * ey p.2 - ex p.2 * ey p.1 := by
      push_cast
      rw [hx, hx, hy, hy]
    rw [this]
  rw [hA, hB, hC]

theorem solution (N : ℕ) [NeZero N] {r : ℕ}
    (s : Fin r → modularFunctionFieldBar N) (hs : IsEmbBasis N s)
    (t : modularFunctionFieldBar N) (ht : (cuspInftyBar N).ord t = 1) :
    ∃ c : ℝ, ∀ (k : ℕ) (u : modularFunctionFieldBar N), u ≠ 0 →
      u ∈ riemannRochSpace ((k : ℤ) • embDivisor N) →
      ∀ B : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N),
      (∀ w, B w = w.ord u + ((k : ℤ) • embDivisor N) w) →
      ∀ (L : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField ↥L]
        (ν : NumberField.InfinitePlace ↥L),
      ∀ x : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N) → Fin r → ↥L,
      (∀ w ∈ B.support, ∀ i, ((x w i : ↥L) : AlgebraicClosure ℚ) = evalVec s w i) →
      (∀ i, ((x (cuspInftyBar N) i : ↥L) : AlgebraicClosure ℚ) = evalVec s (cuspInftyBar N) i) →
      ∀ c' : ↥L, (c' : AlgebraicClosure ℚ) = regVal s (cuspInftyBar N) t k (B (cuspInftyBar N)).toNat u →
      ∃ m : ℝ,
        |((B.erase (cuspInftyBar N)).sum fun w n => (n : ℝ) * prox ν (x (cuspInftyBar N)) (x w))
            - ((k : ℝ) * Real.log (⨆ i, ν (x (cuspInftyBar N) i)) - Real.log (ν c') - m)|
          ≤ c * k ∧
        ∀ v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N), B v = 0 →
          (∀ i, ((x v i : ↥L) : AlgebraicClosure ℚ) = evalVec s v i) →
          ∀ a : ↥L, (a : AlgebraicClosure ℚ) = secVal s v k u →
          |(B.sum fun w n => (n : ℝ) * prox ν (x v) (x w))
              - ((k : ℝ) * Real.log (⨆ i, ν (x v i)) - Real.log (ν a) - m)|
            ≤ c * k := by
  obtain ⟨c, hc⟩ := JZero.jensen_arch_embedding N s hs t ht
  refine ⟨c, fun k u hu humem B hB L _ ν x hxsupp hxinf c' hc' => ?_⟩
  obtain ⟨σ, hσ⟩ := E4A L ν
  obtain ⟨m, hmbase, hmv⟩ := hc σ k u hu humem B hB
  refine ⟨m, ?_, fun v hBv hxv a ha => ?_⟩
  ·
    have hsup : (⨆ i, (ν (x (cuspInftyBar N) i) : ℝ)) = ⨆ i, ‖σ (evalVec s (cuspInftyBar N) i)‖ :=
      iSup_congr fun i => by rw [hσ, hxinf]
    have hcval : (ν c' : ℝ) = ‖σ (regVal s (cuspInftyBar N) t k (B (cuspInftyBar N)).toNat u)‖ := by
      rw [hσ, hc']
    have hsum : ((B.erase (cuspInftyBar N)).sum fun w n =>
          (n : ℝ) * prox (ν : ↥L → ℝ) (x (cuspInftyBar N)) (x w))
        = (B.erase (cuspInftyBar N)).sum fun w n =>
          (n : ℝ) * prox (fun a => ‖σ a‖) (evalVec s (cuspInftyBar N)) (evalVec s w) := by
      refine Finsupp.sum_congr fun w hw => ?_
      have hwne : w ≠ cuspInftyBar N := by
        rintro rfl; exact (Finsupp.mem_support_iff.mp hw) Finsupp.erase_same
      have hwB : w ∈ B.support := by
        rw [Finsupp.mem_support_iff] at hw ⊢; rwa [Finsupp.erase_ne hwne] at hw
      congr 1
      exact prox_transport σ (x (cuspInftyBar N)) (x w)
        (evalVec s (cuspInftyBar N)) (evalVec s w) hxinf (hxsupp w hwB) (ν : ↥L → ℝ) hσ
    rw [hsum, hsup, hcval]
    exact hmbase
  ·
    have hsup : (⨆ i, (ν (x v i) : ℝ)) = ⨆ i, ‖σ (evalVec s v i)‖ :=
      iSup_congr fun i => by rw [hσ, hxv]
    have haval : (ν a : ℝ) = ‖σ (secVal s v k u)‖ := by rw [hσ, ha]
    have hsum : (B.sum fun w n => (n : ℝ) * prox (ν : ↥L → ℝ) (x v) (x w))
        = B.sum fun w n => (n : ℝ) * prox (fun a => ‖σ a‖) (evalVec s v) (evalVec s w) := by
      refine Finsupp.sum_congr fun w hw => ?_
      congr 1
      exact prox_transport σ (x v) (x w) (evalVec s v) (evalVec s w)
        hxv (hxsupp w hw) (ν : ↥L → ℝ) hσ
    rw [hsum, hsup, haval]
    exact hmv v hBv

end

end S_ModularCurve_JZero_jensen_arch
end P2MW
export P2MW.S_ModularCurve_JZero_jensen_arch (solution)
