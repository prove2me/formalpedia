-- Prove2me | solution 1 for ModularCurve.JZero.chowSide_cusp_of_off_support
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/4440599a-7a75-5580-a53e-c6df5fbd2992

import Definitions.Def_ModularCurve_JZeroHeightForm
import Definitions.Def_AlgebraicCurve_ChordalProximity
import Definitions.Def_AlgebraicCurve_CycleChowForm
import Theorems.Thm_ModularCurve_JZero_prox_sum_chowSide
import Theorems.Thm_ModularCurve_JZero_sum_toNat_sectionCycle_eq_mul_embDegree
import Theorems.Thm_ModularCurve_JZero_exists_seq_tendsto_cuspInftyBar
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_JZero_chowSide_cusp_of_off_support
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK"
p2m_attr_erase "instance" "AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar"
p2m_attr_erase "simp" "MvPolynomial.logMahlerMeasure_C MvPolynomial.logMahlerMeasure_X MvPolynomial.logMahlerMeasure_zero MvPolynomial.volume_torusBox MvPolynomial.logMahlerMeasure_monomial MvPolynomial.logMahlerMeasure_one MvPolynomial.norm_circleMap_zero_one MvPolynomial.volume_real_torusBox ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.jqNModC_one AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe"
p2m_attr_erase "simp" "ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero"
p2m_attr_erase "simp" "ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.coe_cuspidalDivisor₀ ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one"
p2m_attr_erase "simp" "AlgebraicCurve.Place.mem_poleSubmodule ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar HahnSeries.ramScale_apply AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq ModularCurve.ComplexPlaceDictionary.mk.injEq ModularCurve.ComplexPlaceDictionary.mk.sizeOf_spec ModularCurve.cuspCount_one"

set_option autoImplicit false

open AlgebraicCurve ModularCurve

theorem solution (N : ℕ) [NeZero N] {r : ℕ}
    (s : Fin r → modularFunctionFieldBar N) (hs : IsEmbBasis N s)
    (t : modularFunctionFieldBar N) (ht : (cuspInftyBar N).ord t = 1) :
    ∃ C : ℝ, ∀ (σ : (AlgebraicClosure ℚ) →+* ℂ) (k : ℕ) (u : modularFunctionFieldBar N), u ≠ 0 →
      u ∈ riemannRochSpace ((k : ℤ) • embDivisor N) →
      ∀ B : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N),
      (∀ w, B w = w.ord u + ((k : ℤ) • embDivisor N) w) →
      ∀ (m c : ℝ),
      (∀ v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N), B v = 0 →
          |chowSide (fun a => ‖σ a‖) s B v
              - ((k : ℝ) * Real.log (⨆ i, ‖σ (evalVec s v i)‖)
                  - Real.log ‖σ (secVal s v k u)‖ - m)| ≤ c * k) →
      |chowSide (fun a => ‖σ a‖) s (B.erase (cuspInftyBar N)) (cuspInftyBar N)
          - ((k : ℝ) * Real.log (⨆ i, ‖σ (evalVec s (cuspInftyBar N) i)‖)
              - Real.log ‖σ (regVal s (cuspInftyBar N) t k (B (cuspInftyBar N)).toNat u)‖ - m)|
        ≤ (c + C) * k := by
  classical
  obtain ⟨c₃, hCF⟩ := ModularCurve.JZero.prox_sum_chowSide N s hs
  obtain ⟨κ₀, hSEQ⟩ := ModularCurve.JZero.exists_seq_tendsto_cuspInftyBar N s hs t ht
  refine ⟨2 * c₃ + (embDegree N : ℝ) * κ₀, ?_⟩
  intro σ k u hu huL B hB m c H
  obtain ⟨hCFo, hCFv⟩ := hCF σ k u hu huL B hB

  have hBnn : ∀ w, 0 ≤ B w := by
    intro w
    rw [hB w]
    have hval : w.adicValuation u ≤ WithZero.exp (((k : ℤ) • embDivisor N) w) := huL w
    have hlog := (WithZero.log_le_iff_le_exp (w.adicValuation_ne_zero hu)).2 hval
    simp only [AlgebraicCurve.Place.ord]
    linarith
  set o := cuspInftyBar N with ho
  set ν : AlgebraicClosure ℚ → ℝ := fun a => ‖σ a‖ with hν
  set e : ℕ := (B o).toNat with he
  have heZ : (e : ℤ) = B o := Int.toNat_of_nonneg (hBnn o)
  have heZ' : (e : ℤ) = o.ord u + k * embDegree N := by
    rw [heZ, hB o]
    simp [ho, embDivisor]
  have hed : (e : ℝ) ≤ k * embDegree N := by
    have hsum := ModularCurve.JZero.sum_toNat_sectionCycle_eq_mul_embDegree N k u hu huL B hB
    have hle : (B o).toNat ≤ B.sum fun _ n => n.toNat := by
      by_cases hmem : o ∈ B.support
      · exact Finset.single_le_sum (f := fun w => (B w).toNat) (fun _ _ => Nat.zero_le _) hmem
      · simp [Finsupp.notMem_support_iff.1 hmem]
    have : e ≤ k * embDegree N := hle.trans_eq hsum
    exact_mod_cast this
  have hκ₀ : 0 ≤ κ₀ := by
    obtain ⟨κ, v, hκ, -⟩ := hSEQ σ B.support k u hu huL e heZ'
    exact (abs_nonneg κ).trans hκ
  obtain ⟨κ, v, hκ, hvS, hprox, hasym⟩ := hSEQ σ B.support k u hu huL e heZ'
  have hBv : ∀ n, B (v n) = 0 := fun n => Finsupp.notMem_support_iff.1 (hvS n)

  set T : ℕ → ℝ := fun n => (B.erase o).sum fun w mlt => (mlt : ℝ) * prox ν (evalVec s (v n)) (evalVec s w) with hT
  set R : ℕ → ℝ := fun n => (k : ℝ) * Real.log (⨆ i, ‖σ (evalVec s (v n) i)‖)
      - Real.log ‖σ (secVal s (v n) k u)‖ - (e : ℝ) * prox ν (evalVec s (v n)) (evalVec s o) with hR
  have hsplit : ∀ n, (B.sum fun w mlt => (mlt : ℝ) * prox ν (evalVec s (v n)) (evalVec s w))
      = (e : ℝ) * prox ν (evalVec s (v n)) (evalVec s o) + T n := by
    intro n
    rw [← Finsupp.add_sum_erase' B o _ (fun _ => by simp)]
    congr 1
    have : ((B o : ℤ) : ℝ) = (e : ℝ) := by rw [← heZ]; simp
    rw [this]
  have hn : ∀ n, |T n - (R n - m)| ≤ (c + c₃) * k := by
    intro n
    have h1 := H (v n) (hBv n)
    have h2 := hCFv (v n) (hBv n)
    rw [hsplit n] at h2
    have eq : T n - (R n - m)
        = ((e : ℝ) * prox ν (evalVec s (v n)) (evalVec s o) + T n - chowSide ν s B (v n))
          + (chowSide ν s B (v n) - ((k : ℝ) * Real.log (⨆ i, ‖σ (evalVec s (v n) i)‖)
              - Real.log ‖σ (secVal s (v n) k u)‖ - m)) := by
      simp only [hR]; ring
    rw [eq]
    refine (abs_add_le _ _).trans ?_
    have := add_le_add h2 h1
    linarith

  have hTlim : Filter.Tendsto T Filter.atTop
      (nhds ((B.erase o).sum fun w mlt => (mlt : ℝ) * prox ν (evalVec s o) (evalVec s w))) := by
    simp only [hT, Finsupp.sum]
    refine tendsto_finsetSum _ fun w hw => ?_
    rw [Finsupp.support_erase, Finset.mem_erase] at hw
    exact (hprox w hw.2 hw.1).const_mul _
  have hRlim := hasym.sub_const m
  have hlim : |((B.erase o).sum fun w mlt => (mlt : ℝ) * prox ν (evalVec s o) (evalVec s w))
      - (((k : ℝ) * Real.log (⨆ i, ‖σ (evalVec s o i)‖)
          - Real.log ‖σ (regVal s o t k e u)‖ + (e : ℝ) * κ) - m)| ≤ (c + c₃) * k :=
    le_of_tendsto' ((hTlim.sub hRlim).abs) hn

  have hek : (e : ℝ) * |κ| ≤ (embDegree N : ℝ) * κ₀ * k := by
    calc (e : ℝ) * |κ| ≤ (k * embDegree N) * κ₀ :=
          mul_le_mul hed hκ (abs_nonneg _) (by positivity)
      _ = (embDegree N : ℝ) * κ₀ * k := by ring
  have key : chowSide ν s (B.erase o) o
        - ((k : ℝ) * Real.log (⨆ i, ‖σ (evalVec s o i)‖) - Real.log ‖σ (regVal s o t k e u)‖ - m)
      = -(((B.erase o).sum fun w mlt => (mlt : ℝ) * prox ν (evalVec s o) (evalVec s w))
            - chowSide ν s (B.erase o) o)
        + (((B.erase o).sum fun w mlt => (mlt : ℝ) * prox ν (evalVec s o) (evalVec s w))
            - (((k : ℝ) * Real.log (⨆ i, ‖σ (evalVec s o i)‖)
                - Real.log ‖σ (regVal s o t k e u)‖ + (e : ℝ) * κ) - m))
        + (e : ℝ) * κ := by ring
  rw [key]
  refine (abs_add_le _ _).trans ((add_le_add (abs_add_le _ _) le_rfl).trans ?_)
  rw [abs_neg, abs_mul, Nat.abs_cast]
  have := add_le_add (add_le_add hCFo hlim) hek
  linarith

end S_ModularCurve_JZero_chowSide_cusp_of_off_support
end P2MW
export P2MW.S_ModularCurve_JZero_chowSide_cusp_of_off_support (solution)
