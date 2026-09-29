-- Prove2me | solution 1 for HairerSPDE.evalAt_bounded_of_finite_cameronMartinNorm
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-14T21:09:54.937113+00:00
-- url     : https://prove2.me/submissions/d4fe99b2-6360-442c-b9fe-49fab497d5c7

import Mathlib
import Definitions.Def_HairerSPDE_CameronMartin

set_option autoImplicit false
set_option maxHeartbeats 1600000

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology

open HairerSPDE

theorem solution {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B] [MeasurableSpace B]
    [BorelSpace B] [CompleteSpace B] [SecondCountableTopology B]
    (μ : Measure B) [IsGaussian μ] (hμ : μ[id] = 0) (h : B)
    (hh : cameronMartinNorm μ h ≠ ∞) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ L : StrongDual ℝ B, |L h| ≤ C * (eLpNorm (fun x => L x) 2 μ).toReal := by
  refine ⟨(cameronMartinNorm μ h).toReal, ENNReal.toReal_nonneg, fun L => ?_⟩
  -- Variance of a dual evaluation equals the squared `eLpNorm`.
  have hvar : ∀ K : StrongDual ℝ B,
      variance (fun x => K x) μ = ((eLpNorm (fun x => K x) 2 μ).toReal) ^ 2 := by
    intro K
    have hfK : MemLp (fun x => K x) 2 μ := IsGaussian.memLp_dual μ K 2 (by norm_num)
    have hmean : (∫ x, x ∂μ) = 0 := by simpa using hμ
    have hmeanK : μ[(fun x => K x)] = 0 := by
      rw [IsGaussian.integral_dual (μ := μ) (L := K), hmean, map_zero]
    rw [variance_of_integral_eq_zero hfK.aemeasurable hmeanK]
    have hnorm := hfK.eLpNorm_eq_integral_rpow_norm two_ne_zero ENNReal.ofNat_ne_top
    simp only [ENNReal.toReal_ofNat] at hnorm
    have hbase : 0 ≤ (∫ a, ‖K a‖ ^ (2:ℝ) ∂μ) :=
      integral_nonneg (fun a => by positivity)
    have hnpos : 0 ≤ (∫ a, ‖K a‖ ^ (2:ℝ) ∂μ) ^ (2:ℝ)⁻¹ :=
      Real.rpow_nonneg hbase _
    have hsq : ((eLpNorm (fun x => K x) 2 μ).toReal) ^ 2
        = ∫ a, ‖K a‖ ^ (2:ℝ) ∂μ := by
      have e1 : (eLpNorm (fun x => K x) 2 μ).toReal
          = (∫ a, ‖K a‖ ^ (2:ℝ) ∂μ) ^ (2:ℝ)⁻¹ := by
        rw [hnorm, ENNReal.toReal_ofReal hnpos]
      rw [e1, show (2:ℝ) = ((((2:ℕ)):ℝ)) by norm_cast]
      exact Real.rpow_inv_natCast_pow hbase two_ne_zero
    rw [hsq]
    apply integral_congr_ae
    filter_upwards with a
    simp only [Real.rpow_natCast, Real.rpow_two, Real.norm_eq_abs, sq_abs]
  -- Covariance diagonal in the same form.
  have hQ : ∀ K : StrongDual ℝ B,
      covarianceBilinDual μ K K = ((eLpNorm (fun x => K x) 2 μ).toReal) ^ 2 := by
    intro K
    rw [covarianceBilinDual_self_eq_variance (IsGaussian.memLp_two_id (μ := μ)) K]
    exact hvar K
  -- Unit-ball bound straight from the definition of the Cameron-Martin norm.
  have hball : ∀ K : StrongDual ℝ B, covarianceBilinDual μ K K ≤ 1 →
      K h ≤ (cameronMartinNorm μ h).toReal := by
    intro K hK
    have hmem : ENNReal.ofReal (K h) ≤
        ⨆ LK : {LK : StrongDual ℝ B // covarianceBilinDual μ LK LK ≤ 1},
          ENNReal.ofReal ((LK : StrongDual ℝ B) h) :=
      le_iSup (fun LK : {LK : StrongDual ℝ B // covarianceBilinDual μ LK LK ≤ 1} =>
        ENNReal.ofReal ((LK : StrongDual ℝ B) h)) ⟨K, hK⟩
    rw [show (⨆ LK : {LK : StrongDual ℝ B // covarianceBilinDual μ LK LK ≤ 1},
        ENNReal.ofReal ((LK : StrongDual ℝ B) h)) = cameronMartinNorm μ h from rfl] at hmem
    exact (ENNReal.ofReal_le_iff_le_toReal hh).mp hmem
  -- One-sided bound for every dual element, by scaling into the unit ball.
  have hone : ∀ K : StrongDual ℝ B,
      K h ≤ (cameronMartinNorm μ h).toReal * (eLpNorm (fun x => K x) 2 μ).toReal := by
    intro K
    have htK : 0 ≤ (eLpNorm (fun x => K x) 2 μ).toReal := ENNReal.toReal_nonneg
    by_cases hq0 : covarianceBilinDual μ K K = 0
    · have hKh : K h = 0 := by
        have hall : ∀ s : ℝ, s * K h ≤ (cameronMartinNorm μ h).toReal := by
          intro s
          have hsK : covarianceBilinDual μ (s • K) (s • K) ≤ 1 := by
            have e1 : covarianceBilinDual μ (s • K) (s • K)
                = variance (fun x => (s • K) x) μ :=
              covarianceBilinDual_self_eq_variance
                (IsGaussian.memLp_two_id (μ := μ)) (s • K)
            have hfun : (fun x => (s • K) x) = s • (fun x => K x) := by
              funext x
              simp only [smul_apply, Pi.smul_apply]
            have hvar0 : variance (fun x => K x) μ = 0 := by
              rw [hvar K, ← hQ K]
              exact hq0
            rw [e1, hfun, variance_smul, hvar0, mul_zero]
            exact zero_le_one
          have hle := hball (s • K) hsK
          have hsmul : (s • K) h = s * K h := by simp only [smul_apply, smul_eq_mul]
          rw [hsmul] at hle
          exact hle
        by_contra hne
        have hbig := hall (((cameronMartinNorm μ h).toReal + 1) / K h)
        rw [div_mul_cancel₀ _ hne] at hbig
        linarith
      have ht0 : (eLpNorm (fun x => K x) 2 μ).toReal = 0 := by
        have h2 : ((eLpNorm (fun x => K x) 2 μ).toReal) ^ 2 = 0 := by
          rw [← hQ K]
          exact hq0
        exact (pow_eq_zero_iff two_ne_zero).mp h2
      rw [hKh, ht0, mul_zero]
    · have htne : (eLpNorm (fun x => K x) 2 μ).toReal ≠ 0 := by
        intro hz
        apply hq0
        rw [hQ K, hz]
        norm_num
      have htpos : 0 < (eLpNorm (fun x => K x) 2 μ).toReal :=
        lt_of_le_of_ne htK htne.symm
      have hunit : covarianceBilinDual μ
          (((eLpNorm (fun x => K x) 2 μ).toReal)⁻¹ • K)
          (((eLpNorm (fun x => K x) 2 μ).toReal)⁻¹ • K) ≤ 1 := by
        have e1 : covarianceBilinDual μ
              (((eLpNorm (fun x => K x) 2 μ).toReal)⁻¹ • K)
              (((eLpNorm (fun x => K x) 2 μ).toReal)⁻¹ • K)
            = variance (fun x => (((eLpNorm (fun x => K x) 2 μ).toReal)⁻¹ • K) x) μ :=
          covarianceBilinDual_self_eq_variance
            (IsGaussian.memLp_two_id (μ := μ)) _
        have hfun : (fun x => (((eLpNorm (fun x => K x) 2 μ).toReal)⁻¹ • K) x)
            = ((eLpNorm (fun x => K x) 2 μ).toReal)⁻¹ • (fun x => K x) := by
          funext x
          simp only [smul_apply, Pi.smul_apply]
        rw [e1, hfun, variance_smul, hvar K, inv_pow,
          inv_mul_cancel₀ (pow_ne_zero 2 htne)]
      have hle := hball _ hunit
      have hsmul : ((((eLpNorm (fun x => K x) 2 μ).toReal)⁻¹ • K)) h
          = ((eLpNorm (fun x => K x) 2 μ).toReal)⁻¹ * K h := by
        simp only [smul_apply, smul_eq_mul]
      rw [hsmul] at hle
      have hdecomp : K h = (eLpNorm (fun x => K x) 2 μ).toReal
          * (((eLpNorm (fun x => K x) 2 μ).toReal)⁻¹ * K h) := by
        rw [← mul_assoc, mul_inv_cancel₀ htne, one_mul]
      rw [hdecomp]
      calc (eLpNorm (fun x => K x) 2 μ).toReal
            * (((eLpNorm (fun x => K x) 2 μ).toReal)⁻¹ * K h)
          ≤ (eLpNorm (fun x => K x) 2 μ).toReal * (cameronMartinNorm μ h).toReal :=
            mul_le_mul_of_nonneg_left hle (le_of_lt htpos)
        _ = (cameronMartinNorm μ h).toReal * (eLpNorm (fun x => K x) 2 μ).toReal := by
            ring
  -- Two-sided bound from the one-sided bound applied to `L` and `-L`.
  have h1 := hone L
  have h2 := hone (-L)
  have hneg : (-L) h = -(L h) := by simp only [neg_apply]
  have htneg : (eLpNorm (fun x => (-L) x) 2 μ).toReal
      = (eLpNorm (fun x => L x) 2 μ).toReal := by
    have hfun : (fun x => (-L) x) = -(fun x => L x) := by
      funext x
      simp only [neg_apply, Pi.neg_apply]
    rw [hfun, eLpNorm_neg]
  rw [hneg, htneg] at h2
  rw [abs_le]
  constructor <;> linarith
