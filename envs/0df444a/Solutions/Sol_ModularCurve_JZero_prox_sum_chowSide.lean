-- Prove2me | solution 1 for ModularCurve.JZero.prox_sum_chowSide
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/924180d3-a450-5171-bdf2-b8c10ef2007c

import Definitions.Def_ModularCurve_JZeroHeightForm
import Definitions.Def_AlgebraicCurve_ChordalProximity
import Definitions.Def_AlgebraicCurve_CycleChowForm
import Theorems.Thm_Pencil_norm_dotProduct_mul_sup_le
import Theorems.Thm_Pencil_exists_covector_sum_log_ge_of_ringHom
import Theorems.Thm_AlgebraicCurve_bddAbove_chowLogAt_range
import Theorems.Thm_ModularCurve_JZero_sum_toNat_sectionCycle_eq_mul_embDegree
import Theorems.Thm_ModularCurve_JZero_chordVec_ne_zero_of_ne
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_JZero_prox_sum_chowSide
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK"
p2m_attr_erase "instance" "AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "MvPolynomial.logMahlerMeasure_C MvPolynomial.logMahlerMeasure_X MvPolynomial.logMahlerMeasure_zero MvPolynomial.volume_torusBox MvPolynomial.logMahlerMeasure_monomial MvPolynomial.logMahlerMeasure_one MvPolynomial.norm_circleMap_zero_one MvPolynomial.volume_real_torusBox ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.jqNModC_one AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe"
p2m_attr_erase "simp" "ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero"
p2m_attr_erase "simp" "ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.coe_cuspidalDivisor₀ ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one"
p2m_attr_erase "simp" "AlgebraicCurve.Place.mem_poleSubmodule ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar HahnSeries.ramScale_apply AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq"

set_option autoImplicit false

open AlgebraicCurve ModularCurve

namespace ChordalChow

theorem norm_le_iSup {r : ℕ} (σ : AlgebraicClosure ℚ →+* ℂ) (a : Fin r → AlgebraicClosure ℚ) (i : Fin r) :
    ‖σ (a i)‖ ≤ ⨆ j, ‖σ (a j)‖ :=
  le_ciSup (f := fun j => ‖σ (a j)‖) (Finite.bddAbove_range _) i

theorem norm_le_iSup₂ {r : ℕ} (σ : AlgebraicClosure ℚ →+* ℂ) (c : Fin r × Fin r → AlgebraicClosure ℚ)
    (p : Fin r × Fin r) : ‖σ (c p)‖ ≤ ⨆ q, ‖σ (c q)‖ :=
  le_ciSup (f := fun q => ‖σ (c q)‖) (Finite.bddAbove_range _) p

theorem norm_map_pos (σ : AlgebraicClosure ℚ →+* ℂ) {z : AlgebraicClosure ℚ} (hz : z ≠ 0) : 0 < ‖σ z‖ :=
  norm_pos_iff.mpr ((map_ne_zero_iff σ σ.injective).mpr hz)

theorem norm_map_ne_zero (σ : AlgebraicClosure ℚ →+* ℂ) {z : AlgebraicClosure ℚ} (hz : z ≠ 0) : ‖σ z‖ ≠ 0 :=
  (norm_map_pos σ hz).ne'

theorem iSup_pos_of_ne_zero {r : ℕ} (σ : AlgebraicClosure ℚ →+* ℂ) (a : Fin r → AlgebraicClosure ℚ)
    (ha : a ≠ 0) : 0 < ⨆ j, ‖σ (a j)‖ := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp ha
  have hi' : a i ≠ 0 := hi
  exact (norm_map_pos σ hi').trans_le (norm_le_iSup σ a i)

theorem norm_factor_mul_sup_le {r : ℕ} (σ : AlgebraicClosure ℚ →+* ℂ) (x y a : Fin r → AlgebraicClosure ℚ)
    (hxa : ∑ i, x i * a i = 0) :
    ‖σ (∑ i, y i * a i)‖ * (⨆ i, ‖σ (x i)‖)
      ≤ r * (⨆ i, ‖σ (a i)‖) * ⨆ p : Fin r × Fin r, ‖σ (x p.1 * y p.2 - x p.2 * y p.1)‖ := by
  have h0 : ∑ i, σ (a i) * σ (x i) = 0 := by
    have h := congrArg σ hxa
    rw [map_sum, map_zero] at h
    rw [← h]
    exact Finset.sum_congr rfl fun i _ => by rw [map_mul, mul_comm]
  have key := Pencil.norm_dotProduct_mul_sup_le (fun i => σ (a i)) (fun i => σ (x i)) (fun i => σ (y i)) h0
  have h1 : ∑ i, σ (a i) * σ (y i) = σ (∑ i, y i * a i) := by
    rw [map_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [map_mul, mul_comm]
  have h2 : (fun p : Fin r × Fin r => ‖σ (x p.1) * σ (y p.2) - σ (x p.2) * σ (y p.1)‖)
      = fun p => ‖σ (x p.1 * y p.2 - x p.2 * y p.1)‖ := by
    funext p
    rw [map_sub, map_mul, map_mul]
  simp only [h1, h2] at key
  refine key.trans (mul_le_mul_of_nonneg_right ?_ (Real.iSup_nonneg fun _ => norm_nonneg _))
  calc ∑ i, ‖σ (a i)‖ ≤ ∑ _i : Fin r, ⨆ j, ‖σ (a j)‖ := Finset.sum_le_sum fun i _ => norm_le_iSup σ a i
    _ = r * ⨆ j, ‖σ (a j)‖ := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

theorem norm_factor_le {r : ℕ} (σ : AlgebraicClosure ℚ →+* ℂ) (x y a : Fin r → AlgebraicClosure ℚ)
    (hxa : ∑ i, x i * a i = 0) (hx : 0 < ⨆ i, ‖σ (x i)‖) :
    ‖σ (∑ i, y i * a i)‖
      ≤ r * (⨆ i, ‖σ (a i)‖) * (⨆ p : Fin r × Fin r, ‖σ (x p.1 * y p.2 - x p.2 * y p.1)‖) / ⨆ i, ‖σ (x i)‖ := by
  rw [le_div_iff₀ hx]
  exact norm_factor_mul_sup_le σ x y a hxa

theorem exists_covector {r : ℕ} (σ : AlgebraicClosure ℚ →+* ℂ) (x : Fin r → AlgebraicClosure ℚ) (hx : x ≠ 0)
    {ι : Type} (T : Finset ι) (hT : T.Nonempty) (y : ι → Fin r → AlgebraicClosure ℚ) (n : ι → ℕ)
    (hn : ∀ t ∈ T, 1 ≤ n t)
    (hM : ∀ t ∈ T, 0 < ⨆ p : Fin r × Fin r, ‖σ (x p.1 * y t p.2 - x p.2 * y t p.1)‖) :
    ∃ a : Fin r → AlgebraicClosure ℚ, ∑ i, x i * a i = 0 ∧ (∀ t ∈ T, ∑ i, y t i * a i ≠ 0) ∧
      0 < (⨆ i, ‖σ (a i)‖) ∧ (⨆ i, ‖σ (a i)‖) ≤ r * ⨆ i, ‖σ (x i)‖ ∧
      ∑ t ∈ T, (n t : ℝ) * Real.log (⨆ p : Fin r × Fin r, ‖σ (x p.1 * y t p.2 - x p.2 * y t p.1)‖)
          - (∑ t ∈ T, (n t : ℝ)) * (r * Real.log 2 + 1)
        ≤ ∑ t ∈ T, (n t : ℝ) * Real.log ‖σ (∑ i, y t i * a i)‖ := by
  classical

  have hr : Nonempty (Fin r) := by
    by_contra h
    rw [not_nonempty_iff] at h
    exact hx (funext fun i => h.elim i)
  obtain ⟨i₀, -, hi₀⟩ := Finset.exists_max_image Finset.univ (fun i => ‖σ (x i)‖) Finset.univ_nonempty
  replace hi₀ : ∀ i, ‖σ (x i)‖ ≤ ‖σ (x i₀)‖ := fun i => hi₀ i (Finset.mem_univ i)
  set S : ℝ := ⨆ i, ‖σ (x i)‖ with hSdef
  have hS : S = ‖σ (x i₀)‖ := le_antisymm (ciSup_le hi₀) (norm_le_iSup σ x i₀)
  have hSpos : 0 < S := iSup_pos_of_ne_zero σ x hx

  set M : ι → ℝ := fun t => ⨆ p : Fin r × Fin r, ‖σ (x p.1 * y t p.2 - x p.2 * y t p.1)‖ with hMdef
  have hr1 : (1 : ℝ) ≤ r := by
    have : 1 ≤ r := Fin.pos_iff_nonempty.mpr hr
    exact_mod_cast this
  have hlogr : 0 ≤ Real.log r := Real.log_nonneg hr1
  set deg : ℝ := ∑ t ∈ T, (n t : ℝ) with hdegdef
  have hdeg0 : 0 ≤ deg := Finset.sum_nonneg fun t _ => Nat.cast_nonneg _
  set K : ℝ := deg * (r * Real.log 2 + 1 + 2 * Real.log r) with hKdef
  have hc₁ : 0 ≤ r * Real.log 2 + 1 + 2 * Real.log r := by
    have : 0 ≤ (r : ℝ) * Real.log 2 := mul_nonneg (zero_le_one.trans hr1) (Real.log_nonneg one_le_two)
    linarith
  have hK0 : 0 ≤ K := mul_nonneg hdeg0 hc₁
  set lam : ι → ℝ := fun t => Real.exp (K + 1) / M t with hlamdef
  have hlam : ∀ t ∈ T, 0 < lam t := fun t ht => div_pos (Real.exp_pos _) (hM t ht)
  have hlamM : ∀ t ∈ T, lam t * M t = Real.exp (K + 1) := fun t ht => div_mul_cancel₀ _ (hM t ht).ne'

  have hw : ∀ t ∈ T, ∃ p : Fin r × Fin r,
      σ (x p.1) * ((lam t : ℂ) * σ (y t p.2)) - σ (x p.2) * ((lam t : ℂ) * σ (y t p.1)) ≠ 0 := by
    intro t ht
    have hne : (fun p : Fin r × Fin r => x p.1 * y t p.2 - x p.2 * y t p.1) ≠ 0 := by
      intro h0
      have : M t = 0 := by
        simp only [hMdef]
        rw [show (fun p : Fin r × Fin r => ‖σ (x p.1 * y t p.2 - x p.2 * y t p.1)‖) = fun p => 0 from
          funext fun p => by rw [show x p.1 * y t p.2 - x p.2 * y t p.1 = 0 from congrFun h0 p, map_zero,
            norm_zero]]
        exact ciSup_const
      exact (hM t ht).ne' this
    obtain ⟨p, hp⟩ := Function.ne_iff.mp hne
    have hp' : x p.1 * y t p.2 - x p.2 * y t p.1 ≠ 0 := hp
    refine ⟨p, ?_⟩
    have h1 : σ (x p.1) * ((lam t : ℂ) * σ (y t p.2)) - σ (x p.2) * ((lam t : ℂ) * σ (y t p.1))
        = (lam t : ℂ) * σ (x p.1 * y t p.2 - x p.2 * y t p.1) := by
      rw [map_sub, map_mul, map_mul]; ring
    rw [h1]
    exact mul_ne_zero (Complex.ofReal_ne_zero.mpr (hlam t ht).ne') ((map_ne_zero_iff σ σ.injective).mpr hp')
  obtain ⟨a, hxa, hale, haeq, hineq⟩ := Pencil.exists_covector_sum_log_ge_of_ringHom σ x hi₀ T
    (fun t i => (lam t : ℂ) * σ (y t i)) n hw

  have hsupL : ∀ t ∈ T, (⨆ p : Fin r × Fin r,
      ‖σ (x p.1) * ((lam t : ℂ) * σ (y t p.2)) - σ (x p.2) * ((lam t : ℂ) * σ (y t p.1))‖) = Real.exp (K + 1) := by
    intro t ht
    have h1 : (fun p : Fin r × Fin r =>
        ‖σ (x p.1) * ((lam t : ℂ) * σ (y t p.2)) - σ (x p.2) * ((lam t : ℂ) * σ (y t p.1))‖)
        = fun p => lam t * ‖σ (x p.1 * y t p.2 - x p.2 * y t p.1)‖ := by
      funext p
      rw [map_sub, map_mul, map_mul, show σ (x p.1) * ((lam t : ℂ) * σ (y t p.2)) - σ (x p.2) * ((lam t : ℂ)
        * σ (y t p.1)) = (lam t : ℂ) * (σ (x p.1) * σ (y t p.2) - σ (x p.2) * σ (y t p.1)) by ring, norm_mul,
        Complex.norm_real, Real.norm_of_nonneg (hlam t ht).le]
    rw [h1, ← Real.mul_iSup_of_nonneg (hlam t ht).le]
    exact hlamM t ht
  have hfacR : ∀ t ∈ T, ‖∑ i, (lam t : ℂ) * σ (y t i) * σ (a i)‖ = lam t * ‖σ (∑ i, y t i * a i)‖ := by
    intro t ht
    have h1 : ∑ i, (lam t : ℂ) * σ (y t i) * σ (a i) = (lam t : ℂ) * σ (∑ i, y t i * a i) := by
      rw [map_sum, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by rw [map_mul, mul_assoc]
    rw [h1, norm_mul, Complex.norm_real, Real.norm_of_nonneg (hlam t ht).le]
  have hineq' : deg * (K + 1) - deg * (r * Real.log 2 + 1)
      ≤ ∑ t ∈ T, (n t : ℝ) * Real.log (lam t * ‖σ (∑ i, y t i * a i)‖) := by
    have hL : ∑ t ∈ T, (n t : ℝ) * Real.log (⨆ p : Fin r × Fin r,
        ‖σ (x p.1) * ((lam t : ℂ) * σ (y t p.2)) - σ (x p.2) * ((lam t : ℂ) * σ (y t p.1))‖) = deg * (K + 1) := by
      rw [Finset.sum_congr rfl fun t ht => by rw [hsupL t ht, Real.log_exp], ← Finset.sum_mul]
    have hR : ∑ t ∈ T, (n t : ℝ) * Real.log ‖∑ i, σ (a i) * ((lam t : ℂ) * σ (y t i))‖
        = ∑ t ∈ T, (n t : ℝ) * Real.log (lam t * ‖σ (∑ i, y t i * a i)‖) := by
      refine Finset.sum_congr rfl fun t ht => ?_
      rw [← hfacR t ht]
      congr 3
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [hL, hR] at hineq
    exact hineq

  set A : ℝ := ⨆ i, ‖σ (a i)‖ with hAdef
  have hAle : A ≤ r * S := by
    rw [hS]
    exact ciSup_le hale

  have hbound : ∀ t ∈ T, Real.log (lam t * ‖σ (∑ i, y t i * a i)‖) ≤ K + 1 + 2 * Real.log r := by
    intro t ht
    by_cases h0 : ‖σ (∑ i, y t i * a i)‖ = 0
    · rw [h0, mul_zero, Real.log_zero]
      linarith
    have hpos : 0 < ‖σ (∑ i, y t i * a i)‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm h0)
    have hA0 : 0 ≤ A := Real.iSup_nonneg fun _ => norm_nonneg _
    have h1 : ‖σ (∑ i, y t i * a i)‖ ≤ r * A * M t / S := norm_factor_le σ x (y t) a hxa hSpos
    have h2 : r * A * M t / S ≤ r * r * M t := by
      rw [div_le_iff₀ hSpos]
      have : (r : ℝ) * A * M t ≤ r * (r * S) * M t :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hAle (zero_le_one.trans hr1)) (hM t ht).le
      linarith [this]
    have h3 : lam t * ‖σ (∑ i, y t i * a i)‖ ≤ Real.exp (K + 1) * (r * r) := by
      calc lam t * ‖σ (∑ i, y t i * a i)‖ ≤ lam t * (r * r * M t) :=
            mul_le_mul_of_nonneg_left (h1.trans h2) (hlam t ht).le
        _ = Real.exp (K + 1) * (r * r) := by rw [← hlamM t ht]; ring
    have h4 : Real.log (lam t * ‖σ (∑ i, y t i * a i)‖) ≤ Real.log (Real.exp (K + 1) * (r * r)) :=
      Real.log_le_log (mul_pos (hlam t ht) hpos) h3
    have hr0 : (r : ℝ) ≠ 0 := (zero_lt_one.trans_le hr1).ne'
    rw [Real.log_mul (Real.exp_pos _).ne' (mul_ne_zero hr0 hr0), Real.log_exp, Real.log_mul hr0 hr0] at h4
    linarith
  have hfac : ∀ t ∈ T, ∑ i, y t i * a i ≠ 0 := by
    intro t₀ ht₀ hzero
    have hz : Real.log (lam t₀ * ‖σ (∑ i, y t₀ i * a i)‖) = 0 := by
      rw [hzero, map_zero, norm_zero, mul_zero, Real.log_zero]

    have hterm : ∀ t ∈ T, (n t : ℝ) * Real.log (lam t * ‖σ (∑ i, y t i * a i)‖)
        ≤ (n t : ℝ) * (K + 1 + 2 * Real.log r)
          - if t = t₀ then (n t : ℝ) * (K + 1 + 2 * Real.log r) else 0 := by
      intro t ht
      have hnt : (0 : ℝ) ≤ n t := Nat.cast_nonneg _
      split_ifs with h
      · subst h
        rw [hz, mul_zero, sub_self]
      · rw [sub_zero]
        exact mul_le_mul_of_nonneg_left (hbound t ht) hnt
    have hsum := Finset.sum_le_sum hterm
    rw [Finset.sum_sub_distrib, Finset.sum_ite_eq' T t₀, if_pos ht₀, ← Finset.sum_mul] at hsum
    have hn₀ : (1 : ℝ) ≤ n t₀ := by exact_mod_cast hn t₀ ht₀
    have h5 : (K + 1 + 2 * Real.log r) ≤ (n t₀ : ℝ) * (K + 1 + 2 * Real.log r) :=
      le_mul_of_one_le_left (by linarith) hn₀

    have h6 : deg * (K + 1) - deg * (r * Real.log 2 + 1)
        ≤ deg * (K + 1 + 2 * Real.log r) - (n t₀ : ℝ) * (K + 1 + 2 * Real.log r) := hineq'.trans hsum
    have h7 : K = deg * (r * Real.log 2 + 1 + 2 * Real.log r) := hKdef
    linarith

  have hApos : 0 < A := by
    obtain ⟨t, ht⟩ := hT
    have ha : a ≠ 0 := by
      intro h0
      apply hfac t ht
      rw [h0]
      simp
    exact iSup_pos_of_ne_zero σ a ha
  refine ⟨a, hxa, hfac, hApos, hAle, ?_⟩
  have hsplit : ∑ t ∈ T, (n t : ℝ) * Real.log (lam t * ‖σ (∑ i, y t i * a i)‖)
      = ∑ t ∈ T, (n t : ℝ) * Real.log (lam t) + ∑ t ∈ T, (n t : ℝ) * Real.log ‖σ (∑ i, y t i * a i)‖ := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun t ht => ?_
    rw [Real.log_mul (hlam t ht).ne' (norm_map_ne_zero σ (hfac t ht)), mul_add]
  have hsplitM : deg * (K + 1) = ∑ t ∈ T, (n t : ℝ) * Real.log (lam t) + ∑ t ∈ T, (n t : ℝ) * Real.log (M t) := by
    rw [← Finset.sum_add_distrib, hdegdef, Finset.sum_mul]
    refine Finset.sum_congr rfl fun t ht => ?_
    rw [← mul_add, ← Real.log_mul (hlam t ht).ne' (hM t ht).ne', hlamM t ht, Real.log_exp]
  rw [hsplit] at hineq'
  linarith

theorem abs_sum_prox_sub_chowSide_le {F : Type} [Field F] [Algebra (AlgebraicClosure ℚ) F] {r : ℕ}
    (σ : AlgebraicClosure ℚ →+* ℂ) (s : Fin r → F) (Z : Divisor (AlgebraicClosure ℚ) F)
    (v : Place (AlgebraicClosure ℚ) F) (hZ : ∀ w, 0 ≤ Z w) (hsep : ∀ w ∈ Z.support, chordVec s v w ≠ 0) :
    |(Z.sum fun w n => (n : ℝ) * prox (fun a => ‖σ a‖) (evalVec s v) (evalVec s w))
        - chowSide (fun a => ‖σ a‖) s Z v|
      ≤ ((Z.sum fun _ n => n.toNat : ℕ) : ℝ) * (r * Real.log 2 + 1 + Real.log r) := by
  classical

  set x : Fin r → AlgebraicClosure ℚ := evalVec s v with hxdef
  set y : Place (AlgebraicClosure ℚ) F → Fin r → AlgebraicClosure ℚ := fun w => evalVec s w with hydef
  set T := Z.support with hTdef
  set n : Place (AlgebraicClosure ℚ) F → ℕ := fun w => (Z w).toNat with hndef
  set S : ℝ := ⨆ i, ‖σ (x i)‖ with hSdef
  set M : Place (AlgebraicClosure ℚ) F → ℝ :=
    fun w => ⨆ p : Fin r × Fin r, ‖σ (x p.1 * y w p.2 - x p.2 * y w p.1)‖ with hMdef
  set Y : Place (AlgebraicClosure ℚ) F → ℝ := fun w => ⨆ i, ‖σ (y w i)‖ with hYdef
  set deg : ℝ := ∑ w ∈ T, (n w : ℝ) with hdegdef
  set Q : ℝ := ⨆ b : {b : Fin r → AlgebraicClosure ℚ // ∑ i, evalVec s v i * b i = 0 ∧ b ≠ 0},
    ‖σ (MvPolynomial.eval b.1 (chowForm s Z))‖ / (⨆ i, ‖σ (b.1 i)‖) ^ (Z.sum fun _ m => m.toNat) with hQdef
  have hcast : ∀ w, ((Z w : ℤ) : ℝ) = (n w : ℝ) := fun w => by
    rw [hndef, ← Int.cast_natCast, Int.toNat_of_nonneg (hZ w)]
  have hdegN : ((Z.sum fun _ m => m.toNat : ℕ) : ℝ) = deg := by
    rw [Finsupp.sum, Nat.cast_sum]
  have hdeg0 : 0 ≤ deg := Finset.sum_nonneg fun w _ => Nat.cast_nonneg _

  have hLQ : chowLogAt (fun a => ‖σ a‖) s Z v = Real.log Q := rfl
  have hdiff : (Z.sum fun w m => (m : ℝ) * prox (fun a => ‖σ a‖) (evalVec s v) (evalVec s w))
      - chowSide (fun a => ‖σ a‖) s Z v
      = deg * Real.log S - ∑ w ∈ T, (n w : ℝ) * Real.log (M w) + Real.log Q := by
    have h1 : (Z.sum fun w m => (m : ℝ) * prox (fun a => ‖σ a‖) (evalVec s v) (evalVec s w))
        = ∑ w ∈ T, (n w : ℝ) * (Real.log S + Real.log (Y w) - Real.log (M w)) := by
      rw [Finsupp.sum]
      exact Finset.sum_congr rfl fun w _ => by rw [hcast w]; rfl
    have h2 : chowSide (fun a => ‖σ a‖) s Z v = ∑ w ∈ T, (n w : ℝ) * Real.log (Y w) - Real.log Q := by
      rw [← hLQ, chowSide, Finsupp.sum]
      exact congrArg₂ _ (Finset.sum_congr rfl fun w _ => by rw [hcast w]) rfl
    rw [h1, h2, hdegdef, Finset.sum_mul]
    have h3 : ∑ w ∈ T, (n w : ℝ) * (Real.log S + Real.log (Y w) - Real.log (M w))
        = ∑ w ∈ T, (n w : ℝ) * Real.log S + ∑ w ∈ T, (n w : ℝ) * Real.log (Y w)
          - ∑ w ∈ T, (n w : ℝ) * Real.log (M w) := by
      rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun w _ => by ring
    rw [h3]
    ring
  rw [hdiff, hdegN]

  by_cases hZ0 : Z = 0
  · have hT0 : T = ∅ := by rw [hTdef, hZ0, Finsupp.support_zero]
    have hQ0 : Real.log Q = 0 := by
      have hQ' : Q = ⨆ b : {b : Fin r → AlgebraicClosure ℚ // ∑ i, evalVec s v i * b i = 0 ∧ b ≠ 0}, (1 : ℝ) := by
        rw [hQdef]
        congr 1
        funext b
        rw [hZ0, chowForm_zero, map_one, map_one, norm_one, Finsupp.sum_zero_index, pow_zero, div_one]
      rw [hQ']
      cases isEmpty_or_nonempty {b : Fin r → AlgebraicClosure ℚ // ∑ i, evalVec s v i * b i = 0 ∧ b ≠ 0} with
      | inl h => rw [Real.iSup_of_isEmpty, Real.log_zero]
      | inr h => rw [ciSup_const, Real.log_one]
    rw [hdegdef, hT0, Finset.sum_empty, Finset.sum_empty, hQ0]
    simp

  have hT : T.Nonempty := by
    rw [hTdef, Finsupp.support_nonempty_iff]
    exact hZ0
  have hM : ∀ w ∈ T, 0 < M w := by
    intro w hw
    obtain ⟨p, hp⟩ := Function.ne_iff.mp (hsep w hw)
    have hp' : x p.1 * y w p.2 - x p.2 * y w p.1 ≠ 0 := hp
    exact (norm_map_pos σ hp').trans_le (norm_le_iSup₂ σ (fun q => x q.1 * y w q.2 - x q.2 * y w q.1) p)
  have hx : x ≠ 0 := by
    obtain ⟨w, hw⟩ := hT
    intro h0
    apply hsep w hw
    funext p
    show evalVec s v p.1 * evalVec s w p.2 - evalVec s v p.2 * evalVec s w p.1 = 0
    rw [← hxdef, h0]
    simp
  have hSpos : 0 < S := iSup_pos_of_ne_zero σ x hx
  have hn : ∀ w ∈ T, 1 ≤ n w := by
    intro w hw
    have h1 : Z w ≠ 0 := Finsupp.mem_support_iff.mp hw
    have h2 : 0 < Z w := lt_of_le_of_ne (hZ w) (Ne.symm h1)
    show 1 ≤ (Z w).toNat
    omega
  have hr1 : (1 : ℝ) ≤ r := by
    have : Nonempty (Fin r) := by
      by_contra h
      rw [not_nonempty_iff] at h
      exact hx (funext fun i => h.elim i)
    have h1 : 1 ≤ r := Fin.pos_iff_nonempty.mpr this
    exact_mod_cast h1
  have hr0 : (r : ℝ) ≠ 0 := (zero_lt_one.trans_le hr1).ne'
  have hlogr : 0 ≤ Real.log r := Real.log_nonneg hr1

  have hnormF : ∀ b : Fin r → AlgebraicClosure ℚ,
      ‖σ (MvPolynomial.eval b (chowForm s Z))‖ = ∏ w ∈ T, ‖σ (∑ i, y w i * b i)‖ ^ n w := by
    intro b
    rw [eval_chowForm, map_finsuppProd, Finsupp.prod, norm_prod]
    exact Finset.prod_congr rfl fun w _ => by rw [map_pow, norm_pow]

  set U : ℝ := (r / S) ^ (Z.sum fun _ m => m.toNat) * ∏ w ∈ T, M w ^ n w with hUdef
  have hU0 : 0 < U := mul_pos (pow_pos (div_pos (zero_lt_one.trans_le hr1) hSpos) _)
    (Finset.prod_pos fun w hw => pow_pos (hM w hw) _)
  have hqle : ∀ b : {b : Fin r → AlgebraicClosure ℚ // ∑ i, evalVec s v i * b i = 0 ∧ b ≠ 0},
      ‖σ (MvPolynomial.eval b.1 (chowForm s Z))‖ / (⨆ i, ‖σ (b.1 i)‖) ^ (Z.sum fun _ m => m.toNat) ≤ U := by
    rintro ⟨b, hxb, hb0⟩
    have hB : 0 < ⨆ i, ‖σ (b i)‖ := iSup_pos_of_ne_zero σ b hb0
    rw [div_le_iff₀ (pow_pos hB _), hnormF b, hUdef, Finsupp.sum, mul_assoc, ← Finset.prod_pow_eq_pow_sum,
      ← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    refine Finset.prod_le_prod (fun w _ => pow_nonneg (norm_nonneg _) _) fun w hw => ?_
    rw [← mul_pow, ← mul_pow]
    refine pow_le_pow_left₀ (norm_nonneg _) ?_ _
    have h1 := norm_factor_le σ x (y w) b hxb hSpos
    calc ‖σ (∑ i, y w i * b i)‖ ≤ r * (⨆ i, ‖σ (b i)‖) * M w / S := h1
      _ = r / S * (M w * ⨆ i, ‖σ (b i)‖) := by ring
  have hQle : Q ≤ U := Real.iSup_le hqle hU0.le
  have hlogU : Real.log U = deg * (Real.log r - Real.log S) + ∑ w ∈ T, (n w : ℝ) * Real.log (M w) := by
    rw [hUdef, Real.log_mul (pow_ne_zero _ (div_ne_zero hr0 hSpos.ne'))
      (Finset.prod_ne_zero_iff.mpr fun w hw => pow_ne_zero _ (hM w hw).ne'), Real.log_pow,
      Real.log_div hr0 hSpos.ne', hdegN, Real.log_prod fun w hw => pow_ne_zero _ (hM w hw).ne']
    exact congrArg₂ _ rfl (Finset.sum_congr rfl fun w _ => by rw [Real.log_pow])

  obtain ⟨a, hxa, hfac, hApos, hAle, hineq⟩ := exists_covector σ x hx T hT y n hn hM
  set A : ℝ := ⨆ i, ‖σ (a i)‖ with hAdef
  have ha0 : a ≠ 0 := by
    obtain ⟨w, hw⟩ := hT
    intro h0
    apply hfac w hw
    rw [h0]
    simp
  have hqa_pos : 0 < ‖σ (MvPolynomial.eval a (chowForm s Z))‖ / A ^ (Z.sum fun _ m => m.toNat) := by
    refine div_pos ?_ (pow_pos hApos _)
    rw [hnormF a]
    exact Finset.prod_pos fun w hw => pow_pos (norm_map_pos σ (hfac w hw)) _
  have hqa_le : ‖σ (MvPolynomial.eval a (chowForm s Z))‖ / A ^ (Z.sum fun _ m => m.toNat) ≤ Q :=
    le_ciSup (bddAbove_chowLogAt_range σ s Z v) ⟨a, hxa, ha0⟩
  have hQpos : 0 < Q := hqa_pos.trans_le hqa_le
  have hlogqa : Real.log (‖σ (MvPolynomial.eval a (chowForm s Z))‖ / A ^ (Z.sum fun _ m => m.toNat))
      = ∑ w ∈ T, (n w : ℝ) * Real.log ‖σ (∑ i, y w i * a i)‖ - deg * Real.log A := by
    rw [Real.log_div _ (pow_ne_zero _ hApos.ne'), Real.log_pow, hdegN, hnormF a,
      Real.log_prod fun w hw => pow_ne_zero _ (norm_map_ne_zero σ (hfac w hw))]
    · exact congrArg₂ _ (Finset.sum_congr rfl fun w _ => by rw [Real.log_pow]) rfl
    · rw [hnormF a]
      exact Finset.prod_ne_zero_iff.mpr fun w hw => pow_ne_zero _ (norm_map_ne_zero σ (hfac w hw))
  have hlogA : Real.log A ≤ Real.log r + Real.log S := by
    rw [← Real.log_mul hr0 hSpos.ne']
    exact Real.log_le_log hApos hAle

  have hup : Real.log Q ≤ deg * (Real.log r - Real.log S) + ∑ w ∈ T, (n w : ℝ) * Real.log (M w) := by
    rw [← hlogU]
    exact Real.log_le_log hQpos hQle
  have hlow : ∑ w ∈ T, (n w : ℝ) * Real.log (M w) - deg * (r * Real.log 2 + 1) - deg * (Real.log r + Real.log S)
      ≤ Real.log Q := by
    have h1 : Real.log (‖σ (MvPolynomial.eval a (chowForm s Z))‖ / A ^ (Z.sum fun _ m => m.toNat))
        ≤ Real.log Q := Real.log_le_log hqa_pos hqa_le
    rw [hlogqa] at h1
    have h2 : deg * Real.log A ≤ deg * (Real.log r + Real.log S) := mul_le_mul_of_nonneg_left hlogA hdeg0
    linarith
  have hc₂ : 0 ≤ deg * (r * Real.log 2 + 1) := by
    have h2 : (0 : ℝ) ≤ r * Real.log 2 := mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg one_le_two)
    exact mul_nonneg hdeg0 (by linarith)
  have hc₃ : 0 ≤ deg * Real.log r := mul_nonneg hdeg0 hlogr
  rw [abs_le]
  constructor
  · linarith
  · linarith

end ChordalChow

theorem ChordalChow.cycle_nonneg {F : Type} [Field F] [Algebra (AlgebraicClosure ℚ) F]
    (D : Divisor (AlgebraicClosure ℚ) F) (u : F) (hu : u ≠ 0) (huL : u ∈ riemannRochSpace D)
    (B : Divisor (AlgebraicClosure ℚ) F) (hB : ∀ w, B w = w.ord u + D w) (w : Place (AlgebraicClosure ℚ) F) :
    0 ≤ B w := by
  rcases mem_riemannRochSpace_iff.mp huL w with h0 | h
  · exact absurd h0 hu
  · rw [hB w]
    linarith

theorem ChordalChow.sum_toNat_erase_le {F : Type} [Field F] [Algebra (AlgebraicClosure ℚ) F]
    (B : Divisor (AlgebraicClosure ℚ) F) (c : Place (AlgebraicClosure ℚ) F) :
    ((B.erase c).sum fun _ n => n.toNat) ≤ B.sum fun _ n => n.toNat := by
  classical
  rw [Finsupp.sum, Finsupp.sum, Finsupp.support_erase]
  calc ∑ w ∈ B.support.erase c, ((B.erase c) w).toNat = ∑ w ∈ B.support.erase c, (B w).toNat :=
        Finset.sum_congr rfl fun w hw => by rw [Finsupp.erase_ne (Finset.ne_of_mem_erase hw)]
    _ ≤ ∑ w ∈ B.support, (B w).toNat := Finset.sum_le_sum_of_subset (Finset.erase_subset _ _)

theorem solution (N : ℕ) [NeZero N] {r : ℕ}
    (s : Fin r → modularFunctionFieldBar N) (hs : IsEmbBasis N s) :
    ∃ c : ℝ, ∀ (σ : (AlgebraicClosure ℚ) →+* ℂ) (k : ℕ) (u : modularFunctionFieldBar N), u ≠ 0 →
      u ∈ riemannRochSpace ((k : ℤ) • embDivisor N) →
      ∀ B : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N),
      (∀ w, B w = w.ord u + ((k : ℤ) • embDivisor N) w) →
        |((B.erase (cuspInftyBar N)).sum fun w n => (n : ℝ) *
            prox (fun a => ‖σ a‖) (evalVec s (cuspInftyBar N)) (evalVec s w))
            - chowSide (fun a => ‖σ a‖) s (B.erase (cuspInftyBar N)) (cuspInftyBar N)| ≤ c * k ∧
        ∀ v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N), B v = 0 →
          |(B.sum fun w n => (n : ℝ) * prox (fun a => ‖σ a‖) (evalVec s v) (evalVec s w))
              - chowSide (fun a => ‖σ a‖) s B v| ≤ c * k := by
  classical
  set C : ℝ := r * Real.log 2 + 1 + Real.log r with hCdef
  have hC0 : 0 ≤ C := by
    have h1 : 0 ≤ (r : ℝ) * Real.log 2 := mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg one_le_two)
    have h2 : 0 ≤ Real.log r := Real.log_natCast_nonneg r
    simp only [hCdef]
    linarith
  refine ⟨embDegree N * C, fun σ k u hu huL B hB => ?_⟩
  have hB0 : ∀ w, 0 ≤ B w := ChordalChow.cycle_nonneg _ u hu huL B hB
  have hdegB : (B.sum fun _ n => n.toNat) = k * embDegree N :=
    ModularCurve.JZero.sum_toNat_sectionCycle_eq_mul_embDegree N k u hu huL B hB
  have hfinal : ∀ m : ℕ, m ≤ k * embDegree N → (m : ℝ) * C ≤ embDegree N * C * k := by
    intro m hm
    have h1 : (m : ℝ) ≤ k * embDegree N := by exact_mod_cast hm
    calc (m : ℝ) * C ≤ (k * embDegree N : ℝ) * C := mul_le_mul_of_nonneg_right h1 hC0
      _ = embDegree N * C * k := by ring
  constructor
  · have hZ : ∀ w, 0 ≤ (B.erase (cuspInftyBar N)) w := by
      intro w
      by_cases h : w = cuspInftyBar N
      · rw [h, Finsupp.erase_same]
      · rw [Finsupp.erase_ne h]
        exact hB0 w
    have hsep : ∀ w ∈ (B.erase (cuspInftyBar N)).support, chordVec s (cuspInftyBar N) w ≠ 0 := by
      intro w hw
      rw [Finsupp.support_erase] at hw
      exact ModularCurve.JZero.chordVec_ne_zero_of_ne N s hs _ _ (Finset.ne_of_mem_erase hw).symm
    refine (ChordalChow.abs_sum_prox_sub_chowSide_le σ s _ _ hZ hsep).trans (hfinal _ ?_)
    rw [← hdegB]
    exact ChordalChow.sum_toNat_erase_le B _
  · intro v hv
    have hsep : ∀ w ∈ B.support, chordVec s v w ≠ 0 := by
      intro w hw
      refine ModularCurve.JZero.chordVec_ne_zero_of_ne N s hs v w fun h => ?_
      rw [Finsupp.mem_support_iff] at hw
      exact hw (h ▸ hv)
    exact (ChordalChow.abs_sum_prox_sub_chowSide_le σ s B v hB0 hsep).trans (hfinal _ hdegB.le)

end S_ModularCurve_JZero_prox_sum_chowSide
end P2MW
export P2MW.S_ModularCurve_JZero_prox_sum_chowSide (solution)
