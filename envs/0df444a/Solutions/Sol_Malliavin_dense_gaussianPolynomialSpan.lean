-- Prove2me | solution 1 for Malliavin.dense_gaussianPolynomialSpan
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:53:08.750027+00:00
-- url     : https://prove2.me/submissions/5d0a09fb-0bd3-4458-bd15-4a88c3211ec6

import Definitions.Def_Malliavin_PastCylinderDensity
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Definitions.Def_Malliavin_BrownianCylinderDensity
import Theorems.Thm_Malliavin_CameronMartin_covarianceMap_apply
import Theorems.Thm_Malliavin_CameronMartin_densityExponent_zero
import Theorems.Thm_Malliavin_CameronMartin_density_toReal
import Theorems.Thm_Malliavin_CameronMartin_density_zero
import Theorems.Thm_Malliavin_CameronMartin_expectationMap_apply
import Theorems.Thm_Malliavin_CameronMartin_inclusion_apply
import Theorems.Thm_Malliavin_CameronMartin_realDensity_zero
import Theorems.Thm_Malliavin_CameronMartin_translated_zero
import Theorems.Thm_Malliavin_IsWienerGenerated_measurable
import Theorems.Thm_Malliavin_bestNaturalItoIntegrand_centeredNaturalItoIntegral
import Theorems.Thm_Malliavin_centeredNaturalItoEquiv_apply
import Theorems.Thm_Malliavin_centeredNaturalItoIntegralIsometry_apply
import Theorems.Thm_Malliavin_centeredPartL2_coe
import Theorems.Thm_Malliavin_centeredWienerIntegral_coe
import Theorems.Thm_Malliavin_elementaryBrownianCoefficientCLM_apply
import Theorems.Thm_Malliavin_elementaryBrownianValueLinear_apply
import Theorems.Thm_Malliavin_elementaryPredictableCoefficientCLM_apply
import Theorems.Thm_Malliavin_expectationL2_wienerIntegral
import Theorems.Thm_Malliavin_mem_symmetricSubmodule
attribute [local simp] Malliavin.CameronMartin.covarianceMap_apply
attribute [local simp] Malliavin.CameronMartin.densityExponent_zero
attribute [local simp] Malliavin.CameronMartin.density_toReal
attribute [local simp] Malliavin.CameronMartin.density_zero
attribute [local simp] Malliavin.CameronMartin.expectationMap_apply
attribute [local simp] Malliavin.CameronMartin.inclusion_apply
attribute [local simp] Malliavin.CameronMartin.realDensity_zero
attribute [local simp] Malliavin.CameronMartin.translated_zero
attribute [local simp] Malliavin.bestNaturalItoIntegrand_centeredNaturalItoIntegral
attribute [local simp] Malliavin.centeredNaturalItoEquiv_apply
attribute [local simp] Malliavin.centeredNaturalItoIntegralIsometry_apply
attribute [local simp] Malliavin.centeredPartL2_coe
attribute [local simp] Malliavin.centeredWienerIntegral_coe
attribute [local simp] Malliavin.elementaryBrownianCoefficientCLM_apply
attribute [local simp] Malliavin.elementaryBrownianValueLinear_apply
attribute [local simp] Malliavin.elementaryPredictableCoefficientCLM_apply
attribute [local simp] Malliavin.expectationL2_wienerIntegral
attribute [local simp] Malliavin.mem_symmetricSubmodule


section
open MeasureTheory ProbabilityTheory Filter Topology
open NormedSpace
open scoped ENNReal NNReal InnerProductSpace
noncomputable section
namespace Malliavin
variable {E W : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
section GaussianPolynomial
variable [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
  [SecondCountableTopology E]
  (μ : Measure E) [IsGaussian μ]
omit [CompleteSpace E] [SecondCountableTopology E] in
private theorem integrable_exp_mul_dual (L : StrongDual ℝ E) (t : ℝ) :
    Integrable (fun x ↦ Real.exp (t * L x)) μ := by
  have h := integrable_exp_mul_gaussianReal
    (μ := μ[L]) (v := Var[L; μ].toNNReal) t
  rw [← IsGaussian.map_eq_gaussianReal (μ := μ) L] at h
  exact h.comp_measurable L.measurable
omit [CompleteSpace E] [SecondCountableTopology E] in
private theorem memLp_two_exp_abs_dual (L : StrongDual ℝ E) :
    MemLp (fun x ↦ Real.exp |L x|) 2 μ := by
  rw [memLp_two_iff_integrable_sq (by fun_prop)]
  have hsum := (integrable_exp_mul_dual μ L 2).add
    (integrable_exp_mul_dual μ L (-2))
  refine hsum.mono (by fun_prop) ?_
  filter_upwards with x
  rw [Real.norm_eq_abs, abs_of_pos (sq_pos_of_pos (Real.exp_pos _))]
  calc
    Real.exp |L x| ^ 2 = Real.exp |2 * L x| := by
      rw [← Real.exp_nat_mul]
      congr 2
      simp [abs_mul]
    _ ≤ Real.exp (2 * L x) + Real.exp (-(2 * L x)) := Real.exp_abs_le _
    _ = ‖((fun x ↦ Real.exp (2 * L x)) +
        fun x ↦ Real.exp (-2 * L x)) x‖ := by
      simp only [Pi.add_apply, Real.norm_eq_abs]
      rw [abs_of_pos (by positivity)]
      congr 1
      ring_nf
omit [CompleteSpace E] [SecondCountableTopology E] in
private theorem integrable_abs_coe_mul_exp_abs_dual
    (g : Lp ℝ 2 μ) (L : StrongDual ℝ E) :
    Integrable (fun x ↦ |g x| * Real.exp |L x|) μ := by
  have hmul := (Lp.memLp g).integrable_mul (memLp_two_exp_abs_dual μ L)
  have hnorm := hmul.norm
  simpa only [Pi.mul_apply, Real.norm_eq_abs, abs_mul,
    abs_of_pos (Real.exp_pos _)] using hnorm
end GaussianPolynomial
section BrownianPolynomial
variable [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  {P : Measure W} [IsGaussian P]
  {B : ℝ≥0 → W → ℝ}
end BrownianPolynomial
end Malliavin
end
end

set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology
open NormedSpace
open scoped ENNReal NNReal InnerProductSpace
noncomputable section
open Malliavin
variable {E W : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
variable [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
  [SecondCountableTopology E]
  (μ : Measure E) [IsGaussian μ]
namespace Malliavin
theorem _root_.solution :
    Dense (gaussianPolynomialSpan μ : Set (Lp ℝ 2 μ)) := by
  rw [Submodule.dense_iff_topologicalClosure_eq_top,
    Submodule.topologicalClosure_eq_top_iff, Submodule.eq_bot_iff]
  intro g hg
  rw [Submodule.mem_orthogonal] at hg
  have key (L : StrongDual ℝ E) (n : ℕ) :
      ∫ x, L x ^ n * g x ∂μ = 0 := by
    have hinner := hg (gaussianLinearPowerLp μ L n)
      (Submodule.subset_span ⟨(L, n), rfl⟩)
    rw [L2.inner_def] at hinner
    rw [← hinner]
    apply integral_congr_ae
    filter_upwards [MemLp.coeFn_toLp (memLp_two_dual_pow μ L n)] with x hx
    have hx' : gaussianLinearPowerLp μ L n x = L x ^ n := hx
    rw [hx']
    simp only [RCLike.inner_apply, conj_trivial]
    ring
  have hchar (L : StrongDual ℝ E) :
      ∫ x, Complex.exp (L x * Complex.I) * (g x : ℂ) ∂μ = 0 := by
    let F : ℕ → E → ℂ := fun n x ↦
      ((L x : ℂ) * Complex.I) ^ n / (Nat.factorial n : ℂ) * (g x : ℂ)
    let bound : ℕ → E → ℝ := fun n x ↦
      |g x| * (|L x| ^ n / Nat.factorial n)
    have hbound_sum (x : E) :
        HasSum (fun n ↦ bound n x) (|g x| * Real.exp |L x|) := by
      simpa only [bound, mul_div_assoc, ← Real.exp_eq_exp_ℝ] using
        (expSeries_div_hasSum_exp |L x|).mul_left |g x|
    have hsum : HasSum (fun n ↦ ∫ x, F n x ∂μ)
        (∫ x, Complex.exp ((L x : ℂ) * Complex.I) * (g x : ℂ) ∂μ) :=
      hasSum_integral_of_dominated_convergence (F := F)
      (f := fun x ↦ Complex.exp ((L x : ℂ) * Complex.I) * (g x : ℂ)) bound
      (fun n ↦ by dsimp only [F]; fun_prop)
      (fun n ↦ by
        filter_upwards with x
        dsimp only [F, bound]
        rw [norm_mul, norm_div, norm_pow]
        simp only [Complex.norm_mul, Complex.norm_real, Complex.norm_I, mul_one,
          norm_natCast, Real.norm_eq_abs]
        rw [mul_comm])
      (Filter.Eventually.of_forall fun x ↦ (hbound_sum x).summable)
      (by
        convert integrable_abs_coe_mul_exp_abs_dual μ g L using 1
        funext x
        exact (hbound_sum x).tsum_eq)
      (Filter.Eventually.of_forall fun x ↦ by
        dsimp only [F]
        simpa only [← Complex.exp_eq_exp_ℂ] using
          (expSeries_div_hasSum_exp ((L x : ℂ) * Complex.I)).mul_right (g x : ℂ))
    have hterm (n : ℕ) : ∫ x, F n x ∂μ = 0 := by
      calc
        ∫ x, F n x ∂μ =
            (Complex.I ^ n / (Nat.factorial n : ℂ)) *
              ∫ x, ((L x ^ n * g x : ℝ) : ℂ) ∂μ := by
          rw [← integral_const_mul]
          apply integral_congr_ae
          filter_upwards with x
          dsimp only [F]
          push_cast
          rw [mul_pow]
          ring
        _ = (Complex.I ^ n / (Nat.factorial n : ℂ)) *
              ((∫ x, L x ^ n * g x ∂μ : ℝ) : ℂ) := by
          rw [integral_complex_ofReal]
        _ = 0 := by rw [key L n]; simp
    rw [← hsum.tsum_eq]
    simp only [hterm, tsum_zero]
  have hg_int : Integrable (g : E → ℝ) μ :=
    (Lp.memLp g).integrable one_le_two
  have hcos (L : StrongDual ℝ E) :
      ∫ x, Real.cos (L x) * g x ∂μ = 0 := by
    have hc : Integrable (fun x ↦ Real.cos (L x) * g x) μ :=
      hg_int.bdd_mul (by fun_prop)
        (Filter.Eventually.of_forall fun x ↦ by
          simpa [Real.norm_eq_abs] using Real.abs_cos_le_one (L x))
    have hs : Integrable (fun x ↦ Real.sin (L x) * g x) μ :=
      hg_int.bdd_mul (by fun_prop)
        (Filter.Eventually.of_forall fun x ↦ by
          simpa [Real.norm_eq_abs] using Real.abs_sin_le_one (L x))
    have hz := hchar L
    have heq : ∀ x, Complex.exp (L x * Complex.I) * (g x : ℂ) =
        ((Real.cos (L x) * g x : ℝ) : ℂ) +
          ((Real.sin (L x) * g x : ℝ) : ℂ) * Complex.I := by
      intro x
      rw [Complex.exp_mul_I]
      push_cast
      ring
    simp_rw [heq] at hz
    rw [integral_add hc.ofReal (hs.ofReal.mul_const _), integral_mul_const,
      integral_complex_ofReal, integral_complex_ofReal] at hz
    have hre := congrArg Complex.re hz
    simpa using hre
  have hsin (L : StrongDual ℝ E) :
      ∫ x, Real.sin (L x) * g x ∂μ = 0 := by
    have hc : Integrable (fun x ↦ Real.cos (L x) * g x) μ :=
      hg_int.bdd_mul (by fun_prop)
        (Filter.Eventually.of_forall fun x ↦ by
          simpa [Real.norm_eq_abs] using Real.abs_cos_le_one (L x))
    have hs : Integrable (fun x ↦ Real.sin (L x) * g x) μ :=
      hg_int.bdd_mul (by fun_prop)
        (Filter.Eventually.of_forall fun x ↦ by
          simpa [Real.norm_eq_abs] using Real.abs_sin_le_one (L x))
    have hz := hchar L
    have heq : ∀ x, Complex.exp (L x * Complex.I) * (g x : ℂ) =
        ((Real.cos (L x) * g x : ℝ) : ℂ) +
          ((Real.sin (L x) * g x : ℝ) : ℂ) * Complex.I := by
      intro x
      rw [Complex.exp_mul_I]
      push_cast
      ring
    simp_rw [heq] at hz
    rw [integral_add hc.ofReal (hs.ofReal.mul_const _), integral_mul_const,
      integral_complex_ofReal, integral_complex_ofReal] at hz
    have him := congrArg Complex.im hz
    simpa using him
  exact Lp.eq_zero_iff_ae_eq_zero.mpr
    (ae_eq_zero_of_forall_integral_cos_sin μ hg_int hcos hsin)
end Malliavin
