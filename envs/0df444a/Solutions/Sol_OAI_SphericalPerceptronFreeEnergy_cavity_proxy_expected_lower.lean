-- Prove2me | solution 1 for OAI.SphericalPerceptronFreeEnergy.cavity_proxy_expected_lower
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T22:23:03.485002+00:00
-- url     : https://prove2.me/submissions/c71872b2-92a4-4993-a025-c441b9e09efe

import Mathlib
import Definitions.Def_PerceptronFreeEnergy
import Definitions.Def_OAIQ61Pf000

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_StableLaplaceConstant
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy
open Matrix
open scoped InnerProductSpace
variable {H : Type*} [SeminormedAddCommGroup H] [InnerProductSpace ℝ H]

section Tilt
variable {S : Type*} [MeasurableSpace S] (μ : Measure S) [IsProbabilityMeasure μ]

lemma tilt_integrable {v F : S → ℝ} (hv : Measurable v) (hF : Measurable F)
    {C D : ℝ} (_hC : 0 ≤ C) (_hD : 0 ≤ D)
    (hvC : ∀ x, |v x| ≤ C) (hFD : ∀ x, |F x| ≤ D) (t : ℝ) :
    Integrable (fun x => Real.exp (t * v x) * F x) μ := by
  refine Integrable.of_bound (hv.const_mul t |>.exp.mul hF).aestronglyMeasurable
    (Real.exp (|t| * C) * D) (ae_of_all _ fun x => ?_)
  rw [Real.norm_eq_abs,abs_mul,abs_of_pos (Real.exp_pos _)]
  apply mul_le_mul _ (hFD x) (abs_nonneg _) (Real.exp_pos _).le
  apply Real.exp_le_exp.mpr
  exact (le_abs_self (t * v x)).trans (by rw [abs_mul]; gcongr; exact hvC x)

lemma tilt_integral_deriv {v F : S → ℝ} (hv : Measurable v) (hF : Measurable F)
    {C D : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hvC : ∀ x, |v x| ≤ C) (hFD : ∀ x, |F x| ≤ D) (t : ℝ) :
    HasDerivAt (tiltIntegral μ v F)
      (∫ x, Real.exp (t * v x) * v x * F x ∂μ) t := by
  apply (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (s := Metric.ball t 1) (bound := fun _ => Real.exp ((|t|+1)*C) * C * D)
    (F' := fun u x => Real.exp (u * v x) * v x * F x) (Metric.ball_mem_nhds t zero_lt_one)
    (Filter.Eventually.of_forall fun u => (hv.const_mul u |>.exp.mul hF).aestronglyMeasurable)
    (tilt_integrable μ hv hF hC hD hvC hFD t)
    (by fun_prop) (ae_of_all _ fun x u hu => ?_) (integrable_const _)
    (ae_of_all _ fun x u _ => ?_)).2
  · have hu' : |u| ≤ |t|+1 := by
      have hh : |u-t| < 1 := by simpa only [Metric.mem_ball,Real.dist_eq] using hu
      calc
        |u| = |(u-t)+t| := by congr 1; ring
        _ ≤ |u-t|+|t| := abs_add_le _ _
        _ ≤ |t|+1 := by linarith
    rw [Real.norm_eq_abs,abs_mul,abs_mul,abs_of_pos (Real.exp_pos _)]
    have hexp : Real.exp (u * v x) ≤ Real.exp ((|t|+1)*C) := by
      apply Real.exp_le_exp.mpr
      apply (le_abs_self (u * v x)).trans
      rw [abs_mul]
      exact mul_le_mul hu' (hvC x) (abs_nonneg _) (by positivity)
    exact mul_le_mul (mul_le_mul hexp (hvC x) (abs_nonneg _) (Real.exp_pos _).le)
      (hFD x) (abs_nonneg _) (mul_nonneg (Real.exp_pos _).le hC)
  · convert! (((hasDerivAt_id u).mul_const (v x)).exp.mul_const (F x)) using 1
    all_goals try with_reducible_and_instances rfl
    simp only [one_mul,id_eq]

lemma tilt_partition_pos {v : S → ℝ} (hv : Measurable v)
    {C : ℝ} (hC : 0 ≤ C) (hvC : ∀ x, |v x| ≤ C) (t : ℝ) :
    0 < tiltPartition μ v t := by
  have hi : Integrable (fun x => Real.exp (t * v x)) μ := by
    simpa only [mul_one] using tilt_integrable μ (F := fun _ => 1) hv measurable_const hC (by norm_num : (0:ℝ) ≤ 1)
      hvC (fun _ => by norm_num) t
  have he : Real.exp (- |t| * C) ≤ tiltPartition μ v t := by
    calc
      Real.exp (- |t| * C) = ∫ _ : S, Real.exp (- |t| * C) ∂μ := by simp
      _ ≤ tiltPartition μ v t := integral_mono_ae (integrable_const _) hi (ae_of_all _ fun x => by
        apply Real.exp_le_exp.mpr
        have hh : |t*v x| ≤ |t| * C := by rw [abs_mul]; gcongr; exact hvC x
        nlinarith [neg_abs_le (t*v x)])
  exact (Real.exp_pos _).trans_le he

lemma tilt_partition_deriv {v : S → ℝ} (hv : Measurable v)
    {C : ℝ} (hC : 0 ≤ C) (hvC : ∀ x, |v x| ≤ C) (t : ℝ) :
    HasDerivAt (tiltPartition μ v) (tiltIntegral μ v v t) t := by
  have hd := tilt_integral_deriv μ (F := fun _ => 1) hv measurable_const hC
    (by norm_num : (0:ℝ) ≤ 1) hvC (fun _ => by norm_num) t
  change HasDerivAt (fun u => ∫ x, Real.exp (u * v x) * 1 ∂μ)
    (∫ x, Real.exp (t*v x) * v x * 1 ∂μ) t at hd
  change HasDerivAt (fun u => ∫ x, Real.exp (u * v x) ∂μ)
    (∫ x, Real.exp (t * v x) * v x ∂μ) t
  simpa only [mul_one] using hd

lemma tilt_mean_deriv {v F : S → ℝ} (hv : Measurable v) (hF : Measurable F)
    {C D : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hvC : ∀ x, |v x| ≤ C) (hFD : ∀ x, |F x| ≤ D) (t : ℝ) :
    HasDerivAt (tiltMean μ v F)
      (tiltMean μ v (fun x => v x * F x) t - tiltMean μ v F t * tiltMean μ v v t) t := by
  have hp := (tilt_partition_pos μ hv hC hvC t).ne'
  have hd := (tilt_integral_deriv μ hv hF hC hD hvC hFD t).div
    (tilt_partition_deriv μ hv hC hvC t) hp
  convert! hd using 1
  all_goals try with_reducible_and_instances rfl
  simp only [tiltMean,tiltIntegral,mul_assoc]
  field_simp

lemma tilt_law_probability {v : S → ℝ} (hv : Measurable v)
    {C : ℝ} (hC : 0 ≤ C) (hvC : ∀ x, |v x| ≤ C) (t : ℝ) :
    IsProbabilityMeasure (tiltLaw μ v t) := by
  have hp := tilt_partition_pos μ hv hC hvC t
  have hi : Integrable (fun x => Real.exp (t * v x)) μ := by
    simpa only [mul_one] using tilt_integrable μ (F := fun _ => 1) hv measurable_const hC
      (by norm_num : (0:ℝ) ≤ 1) hvC (fun _ => by norm_num) t
  constructor
  rw [tiltLaw,Measure.smul_apply,smul_eq_mul,withDensity_apply _ .univ,
    Measure.restrict_univ,← ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ fun x => (Real.exp_pos _).le)]
  exact ENNReal.inv_mul_cancel (ne_of_gt (ENNReal.ofReal_pos.mpr hp)) ENNReal.ofReal_ne_top

lemma tilt_law_integral {v F : S → ℝ} (hv : Measurable v)
    {C : ℝ} (hC : 0 ≤ C) (hvC : ∀ x, |v x| ≤ C) (t : ℝ) :
    ∫ x, F x ∂tiltLaw μ v t = tiltMean μ v F t := by
  rw [tiltLaw,integral_smul_measure,integral_withDensity_eq_integral_toReal_smul
    (show Measurable (fun x => ENNReal.ofReal (Real.exp (t * v x))) from (hv.const_mul t).exp.ennreal_ofReal)
    (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_inv,ENNReal.toReal_ofReal (tilt_partition_pos μ hv hC hvC t).le,
    ENNReal.toReal_ofReal (Real.exp_pos _).le,smul_eq_mul,tiltMean,tiltIntegral]
  exact (div_eq_inv_mul _ _).symm

end Tilt

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Brownian_GaussianField
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy
open Matrix
open scoped InnerProductSpace
variable {H : Type*} [SeminormedAddCommGroup H] [InnerProductSpace ℝ H]

section GibbsProducts
variable {S : Type*} [MeasurableSpace S] (μ : Measure S) [IsProbabilityMeasure μ]

lemma tilt_mean_twice {v w F : S → ℝ} (hw : Measurable w)
    {D : ℝ} (hD : 0 ≤ D) (hwD : ∀ x, |w x| ≤ D) (s t : ℝ) :
    tiltMean (tiltLaw μ w s) v F t = tiltMean μ (fun x => s*w x+t*v x) F 1 := by
  have := tilt_law_probability μ hw hD hwD s
  have hp := (tilt_partition_pos μ hw hD hwD s).ne'
  unfold tiltMean tiltIntegral tiltPartition
  rw [tilt_law_integral μ hw hD hwD s,tilt_law_integral μ hw hD hwD s]
  simp only [tiltMean,tiltIntegral,one_mul,Real.exp_add]
  have he (x : S) : Real.exp (s*w x) * (Real.exp (t*v x)*F x) =
      Real.exp (s*w x) * Real.exp (t*v x) * F x := by ring
  simp_rw [he]
  change ((∫ x, Real.exp (s*w x) * Real.exp (t*v x) * F x ∂μ) / tiltPartition μ w s) /
    ((∫ x, Real.exp (s*w x) * Real.exp (t*v x) ∂μ) / tiltPartition μ w s) = _
  rw [div_div_div_cancel_right₀ hp]

end GibbsProducts

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Interpolation_TiltReplicaCoordinate
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy
open Matrix
open scoped InnerProductSpace
variable {H : Type*} [SeminormedAddCommGroup H] [InnerProductSpace ℝ H]

section GibbsConvex
variable {S : Type*} [MeasurableSpace S] (μ : Measure S) [IsProbabilityMeasure μ]

lemma tilt_log_partition_deriv {v : S → ℝ} (hv : Measurable v)
    {C : ℝ} (hC : 0 ≤ C) (hvC : ∀ x, |v x| ≤ C) (t : ℝ) :
    HasDerivAt (fun u => Real.log (tiltPartition μ v u)) (tiltMean μ v v t) t := by
  exact (tilt_partition_deriv μ hv hC hvC t).log (tilt_partition_pos μ hv hC hvC t).ne'

lemma tilt_variance_eq {v : S → ℝ} (hv : Measurable v)
    {C : ℝ} (hC : 0 ≤ C) (hvC : ∀ x, |v x| ≤ C) (t : ℝ) :
    tiltMean μ v (fun x => v x * v x) t - tiltMean μ v v t * tiltMean μ v v t =
      variance v (tiltLaw μ v t) := by
  have := tilt_law_probability μ hv hC hvC t
  have hLp : MemLp v 2 (tiltLaw μ v t) := memLp_of_bounded
    (ae_of_all _ fun x => abs_le.mp (hvC x)) hv.aestronglyMeasurable 2
  rw [variance_eq_sub hLp]
  simp_rw [tilt_law_integral μ hv hC hvC t]
  simp only [pow_two]
  rfl

lemma tilt_mean_potential_monotone {v : S → ℝ} (hv : Measurable v)
    {C : ℝ} (hC : 0 ≤ C) (hvC : ∀ x, |v x| ≤ C) : Monotone (tiltMean μ v v) := by
  apply monotone_of_hasDerivAt_nonneg (tilt_mean_deriv μ hv hv hC hC hvC hvC)
  intro t
  change 0 ≤ tiltMean μ v (fun x => v x*v x) t - tiltMean μ v v t*tiltMean μ v v t
  rw [tilt_variance_eq μ hv hC hvC]
  exact variance_nonneg _ _

lemma tilt_log_partition_convex {v : S → ℝ} (hv : Measurable v)
    {C : ℝ} (hC : 0 ≤ C) (hvC : ∀ x, |v x| ≤ C) :
    ConvexOn ℝ Set.univ (fun t => Real.log (tiltPartition μ v t)) := by
  have hd := tilt_log_partition_deriv μ hv hC hvC
  apply Monotone.convexOn_univ_of_deriv (fun t => (hd t).differentiableAt)
  have he : deriv (fun t => Real.log (tiltPartition μ v t)) = tiltMean μ v v :=
    funext fun t => (hd t).deriv
  rw [he]
  exact tilt_mean_potential_monotone μ hv hC hvC

end GibbsConvex

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_CovarianceMatrix
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal BigOperators Topology RealInnerProductSpace
open scoped Pointwise
namespace SphericalPerceptronFreeEnergy
open Matrix
open scoped RealInnerProductSpace MatrixOrder

section GaussianRows
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Fintype ι] [DecidableEq ι] in
lemma gaussianRows_apply (v : ι → E) (x : E) (i : ι) :
    gaussianRows v x i = inner ℝ (v i) x := rfl

omit [MeasurableSpace E] [BorelSpace E] in
lemma gaussianRows_adjoint_basis (v : ι → E) (i : ι) :
    (gaussianRows v).adjoint (EuclideanSpace.basisFun ι ℝ i) = v i := by
  apply ext_inner_left ℝ
  intro x
  rw [ContinuousLinearMap.adjoint_inner_right]
  simp [PiLp.inner_apply, gaussianRows_apply,real_inner_comm]

lemma gaussianRows_map_stdGaussian (v : ι → E) :
    (stdGaussian E).map (gaussianRows v) = multivariateGaussian 0 (Matrix.gram ℝ v) := by
  apply IsGaussian.ext
  · simp only [id_eq]
    rw [ContinuousLinearMap.integral_id_map IsGaussian.integrable_id]
    simp only [integral_id_stdGaussian,map_zero,integral_id_multivariateGaussian]
  rw [← ContinuousLinearMap.toBilinForm_inj]
  apply LinearMap.BilinForm.ext_basis (EuclideanSpace.basisFun ι ℝ).toBasis
  intro i j
  simp only [ContinuousLinearMap.toBilinForm_apply,OrthonormalBasis.coe_toBasis]
  rw [covarianceBilin_map IsGaussian.memLp_two_id,gaussianRows_adjoint_basis,
    gaussianRows_adjoint_basis,covarianceBilin_stdGaussian,
    covarianceBilin_multivariateGaussian (Matrix.posSemidef_gram ℝ v)]
  simp
  rfl

end GaussianRows

open TopologicalSpace

open scoped Polynomial

end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_Trial
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy
open Matrix
open scoped InnerProductSpace
variable {H : Type*} [SeminormedAddCommGroup H] [InnerProductSpace ℝ H]

lemma log_integral_exp_sub_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) {F G : Ω → ℝ} {c : ℝ}
    (hF : Integrable (fun x => Real.exp (F x)) μ)
    (hG : Integrable (fun x => Real.exp (G x)) μ)
    (pF : 0 < ∫ x, Real.exp (F x) ∂μ) (pG : 0 < ∫ x, Real.exp (G x) ∂μ)
    (h : ∀ x, F x ≤ G x + c) :
    Real.log (∫ x, Real.exp (F x) ∂μ) - Real.log (∫ x, Real.exp (G x) ∂μ) ≤ c := by
  have hi : (∫ x, Real.exp (F x) ∂μ) ≤
      Real.exp c * ∫ x, Real.exp (G x) ∂μ := by
    rw [← integral_const_mul]
    apply integral_mono hF (hG.const_mul _)
    intro x
    calc
      Real.exp (F x) ≤ Real.exp (G x + c) := Real.exp_le_exp.mpr (h x)
      _ = Real.exp c * Real.exp (G x) := by rw [Real.exp_add, mul_comm]
  have hl := Real.log_le_log pF hi
  rw [Real.log_mul (Real.exp_ne_zero _) (ne_of_gt pG), Real.log_exp] at hl
  linarith

lemma abs_log_integral_exp_sub_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) {F G : Ω → ℝ} {c : ℝ}
    (hF : Integrable (fun x => Real.exp (F x)) μ)
    (hG : Integrable (fun x => Real.exp (G x)) μ)
    (pF : 0 < ∫ x, Real.exp (F x) ∂μ) (pG : 0 < ∫ x, Real.exp (G x) ∂μ)
    (h : ∀ x, |F x - G x| ≤ c) :
    |Real.log (∫ x, Real.exp (F x) ∂μ) - Real.log (∫ x, Real.exp (G x) ∂μ)| ≤ c := by
  apply abs_le.mpr
  constructor
  · have hh := log_integral_exp_sub_le μ hG hF pG pF (fun x => by
      have := (abs_le.mp (h x)).1
      linarith)
    linarith
  · exact log_integral_exp_sub_le μ hF hG pF pG (fun x => by
      have := (abs_le.mp (h x)).2
      linarith)

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_GaussianAverage
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy
open Matrix
open scoped InnerProductSpace
variable {H : Type*} [SeminormedAddCommGroup H] [InnerProductSpace ℝ H]

lemma second_order_taylor_bound {f : ℝ → ℝ} (hf : ContDiff ℝ 3 f)
    (C : ℝ) (hC : ∀ x, |iteratedDeriv 3 f x| ≤ C) (x y : ℝ) :
    |f y - f x - deriv f x * (y-x) - iteratedDeriv 2 f x * (y-x)^2/2| ≤
      C * |y-x|^3 / 6 := by
  by_cases hxy : x = y
  · subst y; simp
  have hs := uniqueDiffOn_uIcc hxy
  have hd₁ : iteratedDerivWithin 1 f (uIcc x y) x = deriv f x := by
    rw [iteratedDerivWithin_eq_iteratedDeriv hs ((hf.of_le (by norm_num)).contDiffAt)
      left_mem_uIcc, iteratedDeriv_one]
  have hd₂ : iteratedDerivWithin 2 f (uIcc x y) x = iteratedDeriv 2 f x :=
    iteratedDerivWithin_eq_iteratedDeriv hs ((hf.of_le (by norm_num)).contDiffAt)
      left_mem_uIcc
  have hp : taylorWithinEval f 2 (uIcc x y) x y =
      f x + deriv f x * (y-x) + iteratedDeriv 2 f x * (y-x)^2/2 := by
    rw [show (2 : ℕ) = 1+1 from rfl, taylorWithinEval_succ,
      taylorWithinEval_succ, taylor_within_zero_eval, hd₁, hd₂]
    norm_num
    ring
  obtain ⟨z, -, hz⟩ := taylor_mean_remainder_lagrange_iteratedDeriv (n := 2) hxy hf.contDiffOn
  rw [hp] at hz
  have he : f y - f x - deriv f x * (y-x) - iteratedDeriv 2 f x * (y-x)^2/2 =
      iteratedDeriv 3 f z * (y-x)^3/6 := by
    norm_num at hz
    linarith only [hz]
  rw [he, abs_div, abs_mul, abs_pow]
  norm_num
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (hC z) (by positivity)) (by norm_num)

lemma first_order_taylor_bound {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (C : ℝ) (hC : ∀ x, |iteratedDeriv 2 f x| ≤ C) (x y : ℝ) :
    |f y - f x - deriv f x * (y-x)| ≤ C * (y-x)^2 / 2 := by
  by_cases hxy : x = y
  · subst y; simp
  have hs := uniqueDiffOn_uIcc hxy
  have hd : iteratedDerivWithin 1 f (uIcc x y) x = deriv f x := by
    rw [iteratedDerivWithin_eq_iteratedDeriv hs ((hf.of_le (by norm_num)).contDiffAt)
      left_mem_uIcc, iteratedDeriv_one]
  have hp : taylorWithinEval f 1 (uIcc x y) x y = f x + deriv f x * (y-x) := by
    rw [show (1 : ℕ) = 0+1 from rfl, taylorWithinEval_succ, taylor_within_zero_eval, hd]
    norm_num
    ring
  obtain ⟨z, -, hz⟩ := taylor_mean_remainder_lagrange_iteratedDeriv (n := 1) hxy hf.contDiffOn
  rw [hp] at hz
  have he : f y - f x - deriv f x * (y-x) = iteratedDeriv 2 f z * (y-x)^2/2 := by
    norm_num at hz
    linarith only [hz]
  rw [he, abs_div, abs_mul, abs_of_nonneg (sq_nonneg (y-x))]
  norm_num
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (hC z) (sq_nonneg _)) (by norm_num)

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_HeatLogBCF
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy
open Matrix
open scoped InnerProductSpace
variable {H : Type*} [SeminormedAddCommGroup H] [InnerProductSpace ℝ H]

lemma Jet3.deriv_eq (g : Jet3) : deriv (g.f : ℝ → ℝ) = g.d1 := funext fun x => (g.has1 x).deriv
lemma Jet3.deriv2_eq (g : Jet3) : iteratedDeriv 2 (g.f : ℝ → ℝ) = g.d2 := by
  rw [iteratedDeriv_succ, iteratedDeriv_one, g.deriv_eq]
  exact funext fun x => (g.has2 x).deriv
lemma Jet3.deriv3_eq (g : Jet3) : iteratedDeriv 3 (g.f : ℝ → ℝ) = g.d3 := by
  rw [iteratedDeriv_succ, g.deriv2_eq]
  exact funext fun x => (g.has3 x).deriv

lemma Jet3.contDiff (g : Jet3) : ContDiff ℝ 3 (g.f : ℝ → ℝ) := by
  rw [show (3 : WithTop ℕ∞) = 2+1 by norm_num, contDiff_succ_iff_deriv]
  refine ⟨fun x => (g.has1 x).differentiableAt, by norm_num, ?_⟩
  rw [g.deriv_eq, show (2 : WithTop ℕ∞) = 1+1 by norm_num, contDiff_succ_iff_deriv]
  refine ⟨fun x => (g.has2 x).differentiableAt, by norm_num, ?_⟩
  rw [show deriv (g.d1 : ℝ → ℝ) = g.d2 from funext fun x => (g.has2 x).deriv,
    show (1 : WithTop ℕ∞) = 0+1 by norm_num, contDiff_succ_iff_deriv]
  refine ⟨fun x => (g.has3 x).differentiableAt, by norm_num, ?_⟩
  rw [show deriv (g.d2 : ℝ → ℝ) = g.d3 from funext fun x => (g.has3 x).deriv]
  exact contDiff_zero.mpr g.d3.continuous

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_NormSquareBand
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.bulkFiniteReplicaLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.bulkSpinKernel_markov _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.enrichedIndexedBaseMeasure_probability _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceBaseDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceSpinLeafKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceCountDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceCountKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityIncrementRandomCavityIncrementLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityProxyRandomCavityProxyLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal BigOperators Topology RealInnerProductSpace
open scoped Pointwise
namespace SphericalPerceptronFreeEnergy
open Matrix
open scoped RealInnerProductSpace MatrixOrder
open TopologicalSpace
open scoped Polynomial
open scoped ContDiff

lemma sphericalExp_mono (n : ℕ) (z : Spin (n+1)) {r s : ℝ}
    (hr : 0 ≤ r) (hrs : r ≤ s) : sphericalExp n z r ≤ sphericalExp n z s := by
  rw [sphericalExp_eq_cosh,sphericalExp_eq_cosh]
  apply integral_mono (unitSphere_continuous_integrable (by fun_prop))
    (unitSphere_continuous_integrable (by fun_prop))
  intro u
  apply Real.cosh_le_cosh.mpr
  rw [abs_mul,abs_mul,abs_of_nonneg hr,abs_of_nonneg (hr.trans hrs)]
  exact mul_le_mul_of_nonneg_right hrs (abs_nonneg _)

end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_PiMarkLaw
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal BigOperators Topology RealInnerProductSpace
open scoped Pointwise
namespace SphericalPerceptronFreeEnergy

lemma gaussian_square_memLp_two (r : ℝ≥0) : MemLp (fun y : ℝ => y^2) 2 (gaussianReal 0 r) := by
  have : ENNReal.HolderTriple (4 : ℝ≥0∞) 4 2 := by
    apply (ENNReal.holderTriple_coe_iff (p := 4) (q := 4) (r := 2) (by norm_num)).mpr
    norm_num [NNReal.holderTriple_iff]
  have h4 : MemLp (fun y : ℝ => y) (4 : ℝ≥0∞) (gaussianReal 0 r) := memLp_id_gaussianReal 4
  have hm : MemLp (fun y : ℝ => y*y) 2 (gaussianReal 0 r) :=
    h4.mul h4
  simpa [pow_two] using hm

lemma gaussian_square_mean (r : ℝ≥0) : (∫ y, y^2 ∂gaussianReal 0 r) = r := by
  have he := variance_fun_id_gaussianReal (μ := 0) (v := r)
  rw [variance_eq_integral (by fun_prop : AEMeasurable (fun x : ℝ => x) (gaussianReal 0 r))] at he
  simpa only [integral_id_gaussianReal,sub_zero] using he

end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cavity_CavityGaussianQuadratic
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped Topology NNReal ENNReal
namespace SphericalPerceptronFreeEnergy

lemma squareGaussianVariance_nonneg : 0 ≤ squareGaussianVariance := variance_nonneg _ _

lemma gaussian_square_variance_scale (r : ℝ≥0) :
    variance (fun y : ℝ=>y^2) (gaussianReal 0 r)=(r:ℝ)^2*squareGaussianVariance := by
  have hg : (gaussianReal 0 1).map (fun y : ℝ=>Real.sqrt (r:ℝ)*y)=gaussianReal 0 r := by
    convert gaussianReal_map_const_mul (μ:=0) (v:=1) (Real.sqrt (r:ℝ)) using 1
    all_goals try with_reducible_and_instances rfl
    simp only [mul_zero,mul_one]
    congr 1
    exact NNReal.coe_injective (Real.sq_sqrt r.coe_nonneg).symm
  rw [←hg,variance_map (by fun_prop) (by fun_prop)]
  simp only [Function.comp_def,mul_pow,Real.sq_sqrt r.coe_nonneg]
  exact variance_const_mul (r:ℝ) (fun y : ℝ=>y^2) _

lemma cavityQuadraticScalar_memLp (M : ℕ) (a : Fin M→ℝ) (t : ℝ) (r : ℝ≥0) :
    MemLp (cavityQuadraticScalar M a t r) 2 (Measure.pi (fun _=>gaussianReal 0 r)) := by
  exact (memLp_finsetSum _ (fun i _=>
    (((gaussian_square_memLp_two r).comp_measurePreserving (measurePreserving_eval _ i)).sub
      (memLp_const (r:ℝ))).const_mul (a i))).const_mul t

lemma cavityQuadraticScalar_mean (M : ℕ) (a : Fin M→ℝ) (t : ℝ) (r : ℝ≥0) :
    (∫ y,cavityQuadraticScalar M a t r y ∂Measure.pi (fun _=>gaussianReal 0 r))=0 := by
  unfold cavityQuadraticScalar
  rw [integral_const_mul,integral_finsetSum]
  · have he i : (∫ y : Fin M→ℝ,a i*((y i)^2-r) ∂Measure.pi (fun _=>gaussianReal 0 r))=0 := by
      rw [integral_const_mul,integral_comp_eval (μ:=fun _ : Fin M=>gaussianReal 0 r) (i:=i) (f:=fun y : ℝ=>y^2-r) (by fun_prop)]
      rw [integral_sub ((gaussian_square_memLp_two r).integrable (by norm_num)) (integrable_const _),gaussian_square_mean]
      simp
    simp_rw [he]
    simp
  · intro i _
    exact ((((gaussian_square_memLp_two r).comp_measurePreserving (measurePreserving_eval _ i)).sub
      (memLp_const (r:ℝ))).const_mul (a i)).integrable (by norm_num)

lemma cavityQuadraticScalar_second_moment (M : ℕ) (a : Fin M→ℝ) (t : ℝ) (r : ℝ≥0) :
    (∫ y,(cavityQuadraticScalar M a t r y)^2 ∂Measure.pi (fun _=>gaussianReal 0 r))=
      t^2*(r:ℝ)^2*squareGaussianVariance*∑ i,(a i)^2 := by
  have hv := variance_eq_sub (cavityQuadraticScalar_memLp M a t r)
  rw [cavityQuadraticScalar_mean] at hv
  simp only [Pi.pow_apply,zero_pow (by norm_num : (2:ℕ)≠0),sub_zero] at hv
  rw [←hv]
  unfold cavityQuadraticScalar
  rw [variance_const_mul]
  have hs := variance_sum_pi (μ:=fun _ : Fin M=>gaussianReal 0 r)
    (X:=fun i y=>a i*(y^2-r)) (fun i=>((gaussian_square_memLp_two r).sub (memLp_const (r:ℝ))).const_mul (a i))
  have he : (∑ i : Fin M,fun y : Fin M→ℝ=>a i*((y i)^2-r))=(fun y=>∑ i,a i*((y i)^2-r)) := by ext y; simp
  rw [he] at hs
  rw [hs]
  simp_rw [variance_const_mul,variance_sub_const (show AEStronglyMeasurable (fun y : ℝ=>y^2) (gaussianReal 0 r) from by fun_prop),gaussian_square_variance_scale]
  rw [←Finset.sum_mul]
  ring

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_EntropicParameter
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [IsGaussian μ]

lemma gaussian_integrable_exp_norm (a : ℝ) : Integrable (fun y : E => Real.exp (a*‖y‖)) μ := by
  obtain ⟨c,hc,hI⟩ := IsGaussian.exists_integrable_exp_sq μ
  have hh (y : E) : a*‖y‖ ≤ c*‖y‖^2+a^2/(4*c) := by
    have h := sq_nonneg (2*c*‖y‖-a)
    have hd : a^2/(4*c)*(4*c)=a^2 := div_mul_cancel₀ _ (by positivity)
    nlinarith
  apply (hI.const_mul (Real.exp (a^2/(4*c)))).mono' (by fun_prop)
  exact ae_of_all _ fun y => by
    rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _),← Real.exp_add]
    apply Real.exp_le_exp.mpr
    linarith [hh y]

end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Sphere_SphereHeat
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.bulkFiniteReplicaLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.bulkSpinKernel_markov _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.enrichedIndexedBaseMeasure_probability _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceBaseDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceSpinLeafKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceCountDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceCountKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityIncrementRandomCavityIncrementLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityProxyRandomCavityProxyLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal
namespace SphericalPerceptronFreeEnergy

lemma sphericalExp_gaussian_average (n : ℕ) (R σ : ℝ) (x : Spin (n+1)) :
    (∫ y, sphericalExp n (x+σ • y) R ∂stdGaussian (Spin (n+1)))=
      Real.exp (R^2*σ^2/2)*sphericalExp n x R := by
  let μ := stdGaussian (Spin (n+1))
  let ν := unitSphereLaw (n+1)
  have hI : Integrable (fun p : Spin (n+1)×Metric.sphere (0:Spin (n+1)) 1 =>
      Real.exp (R*inner ℝ (x+σ • p.1) (p.2:Spin (n+1)))) (μ.prod ν) := by
    apply (((gaussian_integrable_exp_norm μ (|R| *|σ|)).const_mul (Real.exp (|R| *‖x‖))).comp_fst ν).mono' (by fun_prop)
    exact ae_of_all _ fun p => by
      rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _),← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have hu : ‖(p.2:Spin (n+1))‖=1 := by simp
      have hh := abs_real_inner_le_norm (x+σ • p.1) (p.2:Spin (n+1))
      rw [hu,mul_one] at hh
      have ht := norm_add_le x (σ • p.1)
      rw [norm_smul,Real.norm_eq_abs] at ht
      have hb := mul_le_mul_of_nonneg_left (hh.trans ht) (abs_nonneg R)
      rw [← abs_mul] at hb
      have hl := (le_abs_self (R*inner ℝ (x+σ • p.1) (p.2:Spin (n+1)))).trans hb
      nlinarith
  have H := integral_integral_swap (f := fun (y : Spin (n+1)) (u : Metric.sphere (0:Spin (n+1)) 1) =>
    Real.exp (R*inner ℝ (x+σ • y) (u:Spin (n+1)))) hI
  change (∫ y, ∫ u, Real.exp (R*inner ℝ (x+σ • y) (u:Spin (n+1))) ∂ν ∂μ)=_ at H
  change (∫ y, ∫ u, Real.exp (R*inner ℝ (x+σ • y) (u:Spin (n+1))) ∂ν ∂μ)=_
  rw [H]
  have he (u : Metric.sphere (0:Spin (n+1)) 1) :
      (∫ y : Spin (n+1), Real.exp (R*inner ℝ (x+σ • y) (u:Spin (n+1))) ∂μ)=
        Real.exp (R^2*σ^2/2)*Real.exp (R*inner ℝ x (u:Spin (n+1))) := by
    simp only [inner_add_left,real_inner_smul_left,mul_add,Real.exp_add]
    rw [integral_const_mul]
    have hh := integral_exp_inner_stdGaussian (u:Spin (n+1)) (R*σ)
    have hu : ‖(u:Spin (n+1))‖=1 := by simp
    rw [hu] at hh
    simp only [one_pow,mul_one] at hh
    have hinner : (fun y : Spin (n+1) => Real.exp (R*(σ*inner ℝ y (u:Spin (n+1)))))=
        (fun y => Real.exp ((R*σ)*inner ℝ (u:Spin (n+1)) y)) := by
      funext y
      rw [real_inner_comm y (u:Spin (n+1))]
      congr 1
      ring
    rw [hinner,hh,mul_pow]
    ring
  simp_rw [he]
  rw [integral_const_mul]
  rfl

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Brownian_CavityGaussianFields
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.bulkFiniteReplicaLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.bulkSpinKernel_markov _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.enrichedIndexedBaseMeasure_probability _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceBaseDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceSpinLeafKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceCountDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceCountKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityIncrementRandomCavityIncrementLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityProxyRandomCavityProxyLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped Topology NNReal ENNReal
namespace SphericalPerceptronFreeEnergy

lemma gaussian_inner_preserving (L : ℕ) (z : Spin L) :
    MeasurePreserving (fun y : Spin L=>inner ℝ z y) (stdGaussian (Spin L))
      (gaussianReal 0 (‖z‖₊^2)) := by
  refine ⟨by fun_prop,?_⟩
  have h := IsGaussian.map_eq_gaussianReal (μ:=stdGaussian (Spin L)) (innerSL ℝ z)
  simp only [integral_strongDual_stdGaussian,variance_dual_stdGaussian,innerSL_apply_norm] at h
  have he : (‖z‖^2).toNNReal = (‖z‖₊^2) := by
    ext; simp
  simpa only [he,coe_innerSL_apply] using h

lemma gaussian_cavity_projection (M L : ℕ) (z : Spin L) :
    MeasurePreserving (fun y : Fin M→Spin L=>fun i=>inner ℝ z (y i))
      (Measure.pi (fun _=>stdGaussian (Spin L)))
      (Measure.pi (fun _ : Fin M=>gaussianReal 0 (‖z‖₊^2))) := by
  have (_index : Fin M) : SigmaFinite (gaussianReal 0 (‖z‖₊^2)) := inferInstance
  exact measurePreserving_pi _ _ (fun _=>gaussian_inner_preserving L z)

lemma cavityQuadraticField_memLp (M L : ℕ) (a : Fin M→ℝ) (t : ℝ) (z : Spin L) :
    MemLp (cavityQuadraticField M L a t z) 2 (Measure.pi (fun _=>stdGaussian (Spin L))) := by
  have h := (cavityQuadraticScalar_memLp M a t (‖z‖₊^2)).comp_measurePreserving
    (gaussian_cavity_projection M L z)
  change MemLp (fun y : Fin M→Spin L=>t*∑ i,a i*((inner ℝ z (y i))^2-‖z‖^2)) 2 _
  simpa only [Function.comp_def,cavityQuadraticScalar,NNReal.coe_pow,coe_nnnorm] using h

lemma cavityQuadraticField_second_moment (M L : ℕ) (a : Fin M→ℝ) (t : ℝ) (z : Spin L) :
    (∫ y,(cavityQuadraticField M L a t z y)^2 ∂Measure.pi (fun _=>stdGaussian (Spin L)))=
      t^2*‖z‖^4*squareGaussianVariance*∑ i,(a i)^2 := by
  have hm := gaussian_cavity_projection M L z
  have he := (integral_map hm.aemeasurable (f:=fun y=>(cavityQuadraticScalar M a t (‖z‖₊^2) y)^2) (show AEStronglyMeasurable (fun y : Fin M→ℝ=>(cavityQuadraticScalar M a t (‖z‖₊^2) y)^2) _ from (show Continuous (fun y : Fin M→ℝ=>(cavityQuadraticScalar M a t (‖z‖₊^2) y)^2) from by unfold cavityQuadraticScalar; fun_prop).aestronglyMeasurable)).symm
  rw [hm.map_eq] at he
  rw [cavityQuadraticScalar_second_moment] at he
  simp only [cavityQuadraticScalar,NNReal.coe_pow,coe_nnnorm] at he
  calc
    _ = ∫ y : Fin M→Spin L,(t*∑ i,a i*((inner ℝ z (y i))^2-‖z‖^2))^2 ∂Measure.pi (fun _=>stdGaussian (Spin L)) := rfl
    _ = _ := he
    _ = t^2*‖z‖^4*squareGaussianVariance*∑ i,(a i)^2 := by ring

lemma cavityLinearField_exp_moment (M L : ℕ) (a : Fin M→ℝ) (t : ℝ) (z : Spin L) (p : ℝ) :
    (∫ y,Real.exp (p*cavityLinearField M L a t z y) ∂Measure.pi (fun _=>stdGaussian (Spin L)))=
      Real.exp (p^2*t^2*‖z‖^2/2*∑ i,(a i)^2) := by
  have he y : Real.exp (p*cavityLinearField M L a t z y)=
      ∏ i,Real.exp ((p*t*a i)*inner ℝ z (y i)) := by
    unfold cavityLinearField
    rw [←mul_assoc,Finset.mul_sum,Real.exp_sum]
    congr 1
    ext i
    congr 1
    ring
  simp_rw [he]
  rw [integral_fintype_prod_eq_prod (fun i (x : Spin L)=>Real.exp ((p*t*a i)*inner ℝ z x))]
  simp_rw [integral_exp_inner_stdGaussian]
  rw [←Real.exp_sum]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_IntegrableGibbs
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators

section
variable {S : Type*} [MeasurableSpace S] (μ : Measure S) [IsProbabilityMeasure μ]

lemma tiltMean_bound_of_integrable {H F : S → ℝ} (hH : Measurable H) (_hF : Measurable F)
    {t C : ℝ} (hi : Integrable (fun x => Real.exp (t*H x)) μ)
    (hC : ∀ x, |F x| ≤ C) : |tiltMean μ H F t| ≤ C := by
  let := tilt_law_probability_of_integrable μ hi
  rw [← tilt_law_integral_of_integrable μ hH hi]
  have hh := norm_integral_le_of_norm_le_const (μ := tiltLaw μ H t) (f := F)
    (C := C) (ae_of_all _ fun x => by simpa only [Real.norm_eq_abs] using hC x)
  simpa only [Real.norm_eq_abs,probReal_univ,mul_one] using hh

end

end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Pressure_VectorPartition
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal BigOperators Topology RealInnerProductSpace
namespace SphericalPerceptronFreeEnergy
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable {S : Type*} [MeasurableSpace S] (ρ : Measure S) [IsProbabilityMeasure ρ]
  {W : S → ℝ} {V : S → StrongDual ℝ E}

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [MeasurableSpace S] in
lemma vectorEnergy_bound {K C : ℝ} (hW : ∀ s, |W s| ≤ K) (hV : ∀ s, ‖V s‖ ≤ C)
    (x : E) (s : S) : |W s + V s x| ≤ K+C*‖x‖ := by
  apply (abs_add_le _ _).trans
  apply add_le_add (hW s)
  exact (ContinuousLinearMap.le_opNorm _ _).trans
    (mul_le_mul_of_nonneg_right (hV s) (norm_nonneg x))

omit [MeasurableSpace E] [BorelSpace E] in
lemma vectorPartition_integrable (hWm : Measurable W) (hVm : Measurable V)
    {K C : ℝ} (hW : ∀ s, |W s| ≤ K) (hV : ∀ s, ‖V s‖ ≤ C) (x : E) :
    Integrable (fun s => Real.exp (W s + V s x)) ρ := by
  refine Integrable.of_bound (by fun_prop) (Real.exp (K+C*‖x‖)) (ae_of_all _ fun s => ?_)
  rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
  exact Real.exp_le_exp.mpr ((le_abs_self _).trans (vectorEnergy_bound hW hV x s))

omit [MeasurableSpace E] [BorelSpace E] in
lemma vectorPartition_pos (hWm : Measurable W) (hVm : Measurable V)
    {K C : ℝ} (hW : ∀ s, |W s| ≤ K) (hV : ∀ s, ‖V s‖ ≤ C) (x : E) :
    0 < vectorPartition ρ W V x := by
  apply integral_pos_iff_support_of_nonneg (fun s => (Real.exp_pos _).le)
    (vectorPartition_integrable ρ hWm hVm hW hV x) |>.mpr
  simp [Function.support,Real.exp_ne_zero]

end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_VarianceProdMemLp
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal BigOperators Topology RealInnerProductSpace
namespace SphericalPerceptronFreeEnergy

section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {S : Type*} [MeasurableSpace S] (ρ : Measure S) [IsProbabilityMeasure ρ]

omit [MeasurableSpace E] [BorelSpace E] in
lemma vectorLogPartition_bound {W : S → ℝ} {V : S → StrongDual ℝ E}
    (hWm : Measurable W) (hVm : Measurable V) {K C : ℝ}
    (hW : ∀ s, |W s| ≤ K) (hV : ∀ s, ‖V s‖ ≤ C) (x : E) :
    |vectorLogPartition ρ W V x| ≤ K+C*‖x‖ := by
  have hh := abs_log_integral_exp_sub_le ρ
    (vectorPartition_integrable ρ hWm hVm hW hV x)
    (show Integrable (fun _ : S => Real.exp 0) ρ by simp)
    (vectorPartition_pos ρ hWm hVm hW hV x)
    (show 0 < ∫ _ : S, Real.exp 0 ∂ρ by simp)
    (c := K+C*‖x‖) (fun s => by simpa using vectorEnergy_bound hW hV x s)
  simpa [vectorLogPartition,vectorPartition] using hh

end

end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_LocalMaxSecondDerivNonpos
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal BigOperators Topology RealInnerProductSpace
namespace SphericalPerceptronFreeEnergy

section

variable {S : Type*} [MeasurableSpace S] (μ : Measure S) [IsProbabilityMeasure μ]

lemma affineLogRoot_eq {H Y : S → ℝ} (hH : Measurable H) (hY : Measurable Y)
    {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hHA : ∀ x, |H x| ≤ A)
    (hYB : ∀ x, |Y x| ≤ B) (t : ℝ) :
    affineLogRoot μ H Y t = Real.log (tiltPartition (tiltLaw μ H 1) Y t) +
      Real.log (tiltPartition μ H 1) := by
  have := tilt_law_probability μ hH hA hHA 1
  have hp := tilt_partition_pos μ hH hA hHA 1
  have hy := tilt_partition_pos (tiltLaw μ H 1) hY hB hYB t
  have he : tiltPartition (tiltLaw μ H 1) Y t * tiltPartition μ H 1 =
      tiltPartition μ (fun x => H x+t*Y x) 1 := by
    unfold tiltPartition
    rw [tilt_law_integral μ hH hA hHA 1]
    simp only [tiltMean,tiltIntegral,tiltPartition,one_mul]
    rw [div_mul_cancel₀ _ (by simpa only [tiltPartition,one_mul] using hp.ne')]
    simp_rw [Real.exp_add]
  rw [affineLogRoot,← he,Real.log_mul hy.ne' hp.ne']

lemma affineLogRoot_deriv {H Y : S → ℝ} (hH : Measurable H) (hY : Measurable Y)
    {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hHA : ∀ x, |H x| ≤ A)
    (hYB : ∀ x, |Y x| ≤ B) (t : ℝ) :
    HasDerivAt (affineLogRoot μ H Y) (tiltMean μ (fun x => H x+t*Y x) Y 1) t := by
  have := tilt_law_probability μ hH hA hHA 1
  have hh := (tilt_log_partition_deriv (tiltLaw μ H 1) hY hB hYB t).add_const
    (Real.log (tiltPartition μ H 1))
  simp_rw [tilt_mean_twice μ hH hA hHA,one_mul] at hh
  exact hh.congr_of_eventuallyEq (Eventually.of_forall fun u => affineLogRoot_eq μ hH hY hA hB hHA hYB u)

lemma tilt_log_partition_bound {H : S → ℝ} (hH : Measurable H)
    {A : ℝ} (hA : 0 ≤ A) (hHA : ∀ x, |H x| ≤ A) :
    |Real.log (tiltPartition μ H 1)| ≤ A := by
  have hp := tilt_partition_pos μ hH hA hHA 1
  have hi : Integrable (fun x => Real.exp (H x)) μ := by
    simpa only [one_mul,mul_one] using tilt_integrable μ (F := fun _ => 1) hH measurable_const hA (by norm_num : (0:ℝ) ≤ 1) hHA (fun _ => by norm_num) 1
  have hlo : Real.exp (-A) ≤ tiltPartition μ H 1 := by
    calc
      _ = ∫ _ : S, Real.exp (-A) ∂μ := by simp
      _ ≤ _ := by simpa only [tiltPartition,one_mul] using integral_mono (integrable_const _) hi (fun x => Real.exp_le_exp.mpr (abs_le.mp (hHA x)).1)
  have hhi : tiltPartition μ H 1 ≤ Real.exp A := by
    calc
      _ ≤ ∫ _ : S, Real.exp A ∂μ := by simpa only [tiltPartition,one_mul] using integral_mono hi (integrable_const _) (fun x => Real.exp_le_exp.mpr (abs_le.mp (hHA x)).2)
      _ = _ := by simp
  exact abs_le.mpr ⟨by simpa using Real.log_le_log (Real.exp_pos (-A)) hlo,by simpa using Real.log_le_log hp hhi⟩

lemma affineLogRoot_convex {H Y : S → ℝ} (hH : Measurable H) (hY : Measurable Y)
    {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hHA : ∀ x, |H x| ≤ A)
    (hYB : ∀ x, |Y x| ≤ B) : ConvexOn ℝ Set.univ (affineLogRoot μ H Y) := by
  have := tilt_law_probability μ hH hA hHA 1
  have he := funext fun t => affineLogRoot_eq μ hH hY hA hB hHA hYB t
  rw [he]
  exact (tilt_log_partition_convex (tiltLaw μ H 1) hY hB hYB).add (convexOn_const _ (convex_univ))

end

end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Interpolation_IntegrableReplicaGibbs
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators
namespace SphericalPerceptronFreeEnergy
variable {S : Type*} [MeasurableSpace S] (μ : Measure S) [IsProbabilityMeasure μ]

lemma tiltMean_bound_general {H F : S → ℝ} (hH : Measurable H) (hF : Measurable F)
    {t C : ℝ} (hC : 0 ≤ C) (hFC : ∀ x, |F x| ≤ C) :
    |tiltMean μ H F t| ≤ C := by
  by_cases hi : Integrable (fun x => Real.exp (t*H x)) μ
  · exact tiltMean_bound_of_integrable μ hH hF hi hFC
  · simp only [tiltMean,tiltPartition,integral_undef hi,div_zero,abs_zero]
    exact hC

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cavity_BulkModel
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.bulkFiniteReplicaLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceCountDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceCountKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityIncrementRandomCavityIncrementLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityProxyRandomCavityProxyLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureTwoFreshDisorderTwoFreshDisorderLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators BoundedContinuousFunction

lemma bulkLogPartition_eq (n M : ℕ) (f : ℝ →ᵇ ℝ) (v : ℕ → ℝ)
    (a : Fin M → Fin (n+1) → ℝ) (g : BulkMark (n+1)) :
    bulkLogPartition n M f v a g =
      Real.log (tiltPartition (unitSphereLaw (n+1)) (bulkHamiltonian (n+1) M f v a g) 1) := by
  simp only [bulkLogPartition, vectorLogPartition, vectorPartition, tiltPartition, one_mul, bulkHamiltonian,
    innerSL_apply_apply]

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cavity_BulkConcentration
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.bulkFiniteReplicaLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceCountDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceCountKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityIncrementRandomCavityIncrementLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityProxyRandomCavityProxyLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureTwoFreshDisorderTwoFreshDisorderLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

lemma bulkLogPartition_measurable (n M : ℕ) (f : ℝ→ᵇℝ) (v : ℕ→ℝ) :
    Measurable (fun a : BulkDisorder (n+1) M => bulkLogPartition n M f v a.1 a.2) := by
  simp_rw [bulkLogPartition_eq]
  change Measurable (fun a : BulkDisorder (n+1) M => Real.log (∫ x,
    Real.exp (1*bulkHamiltonian (n+1) M f v a.1 a.2 x) ∂unitSphereLaw (n+1)))
  simp only [one_mul]
  exact (bulkHamiltonian_continuous (n+1) M f v).measurable.exp.stronglyMeasurable.integral_prod_right'.measurable.log

lemma bulkLogPartition_bound (n M : ℕ) (f : ℝ→ᵇℝ) (v : ℕ→ℝ)
    (a : BulkDisorder (n+1) M) :
    |bulkLogPartition n M f v a.1 a.2| ≤ M*‖f‖+bulkFeatureBound (n+1) v*‖a.2‖ := by
  apply vectorLogPartition_bound (unitSphereLaw (n+1))
    ((normalizedPatternEnergy_continuous (n+1) M f).measurable.comp (measurable_const.prodMk measurable_id))
    (((innerSL ℝ).continuous.comp (bulkFeature_continuous (n+1) v)).measurable)
    (normalizedPatternEnergy_bound (n+1) M f a.1)
  intro x
  simp only [Function.comp_apply,innerSL_apply_norm,bulkFeature_norm,bulkFeatureBound,le_refl]

lemma bulkLogPartition_memLp (n M : ℕ) (f : ℝ→ᵇℝ) (v : ℕ→ℝ) :
    MemLp (fun a : BulkDisorder (n+1) M => bulkLogPartition n M f v a.1 a.2) 2
      (bulkDisorderLaw (n+1) M) := by
  have hi : MemLp (id : BulkMark (n+1) → BulkMark (n+1)) 2 (stdGaussian (BulkMark (n+1))) :=
    IsGaussian.memLp_id (stdGaussian (BulkMark (n+1))) 2 (by simp)
  have hn : MemLp (fun g : BulkMark (n+1) => ‖g‖) 2 (stdGaussian (BulkMark (n+1))) := hi.norm
  have hc : MemLp (fun _ : BulkMark (n+1) => (M:ℝ)*‖f‖) 2 (stdGaussian (BulkMark (n+1))) := memLp_const _
  have hg : MemLp (fun g : BulkMark (n+1) => M*‖f‖+bulkFeatureBound (n+1) v*‖g‖) 2
      (stdGaussian (BulkMark (n+1))) := hc.add (hn.const_mul (bulkFeatureBound (n+1) v))
  apply (hg.comp_snd (Measure.pi (fun _ : Fin M => Measure.pi (fun _ : Fin (n+1) => gaussianReal 0 1)))).mono'
    (bulkLogPartition_measurable n M f v).aestronglyMeasurable
  exact ae_of_all _ fun a => by simpa only [Real.norm_eq_abs] using bulkLogPartition_bound n M f v a

lemma bulkHamiltonian_section_measurable (N M : ℕ) (f : ℝ →ᵇ ℝ) (v : ℕ → ℝ)
    (a : BulkDisorder N M) : Measurable (bulkHamiltonian N M f v a.1 a.2) := by
  exact ((bulkHamiltonian_continuous N M f v).comp
    (continuous_const.prodMk continuous_id)).measurable

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cavity_BulkSingleLimit
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.bulkFiniteReplicaLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceCountDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceCountKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityIncrementRandomCavityIncrementLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityProxyRandomCavityProxyLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal BigOperators BoundedContinuousFunction

lemma singleFieldMark_bound (w : ℝ→ᵇℝ) (z : Fin 1→ℝ) : |singleFieldMark w z|≤‖w‖ := w.norm_coe_le_norm _

lemma bulkSingleAverage_bound (n M : ℕ) (w : ℝ→ᵇℝ) (a : BulkDisorder (n+1) M)
    (x : Fin 1→NormalizedSpin (n+1)) : |bulkSingleAverage n M w a x|≤M/(n+1:ℕ)*‖w‖ := by
  unfold bulkSingleAverage
  rw [abs_mul,abs_of_nonneg (by positivity : 0≤(((n+1:ℕ):ℝ)⁻¹))]
  have h : |∑ i : Fin M,singleFieldMark w (bulkPatternFields i a x)|≤M*‖w‖ :=
    (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum fun i _ => singleFieldMark_bound w _).trans_eq (by simp))
  exact (mul_le_mul_of_nonneg_left h (by positivity)).trans_eq (by ring)

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cavity_CavityBulkCoefficients
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceCountDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceCountKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityIncrementRandomCavityIncrementLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityProxyRandomCavityProxyLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology BigOperators BoundedContinuousFunction

lemma cavityBulkFeature_inner (n d m M : ℕ) (f : Jet3) (a : BulkDisorder (m+1) M)
    (x y : NormalizedSpin (m+1)) (j k : Fin (n+1)⊕Fin d) :
    inner ℝ (cavityBulkFeature n d m M f a x j) (cavityBulkFeature n d m M f a y k)=
      if j=k then Sum.elim (fun _=>bulkB (m+1) M f a.1 x y)
        (fun _=>inner ℝ x.val y.val) j else 0 := by
  classical
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp only [dotProduct,star_trivial,cavityBulkFeature]
  rw [Fintype.sum_prod_type]
  by_cases hjk : j=k
  · subst k
    simp only [ite_true]
    have he (p : Fin (n+1)⊕Fin d) :
        (∑ t : Fin M⊕Fin (m+1),
          (if p=j then cavityBulkBase n d m M f a y j t else 0)*
          (if p=j then cavityBulkBase n d m M f a x j t else 0))=
        if p=j then ∑ t : Fin M⊕Fin (m+1),
          cavityBulkBase n d m M f a y j t*cavityBulkBase n d m M f a x j t else 0 := by
      split_ifs <;> simp_all
    simp_rw [he]
    rw [Finset.sum_ite_eq']
    simp only [Finset.mem_univ,ite_true]
    cases j with
    | inl _index =>
      simp only [Fintype.sum_sum_type,cavityBulkBase,Sum.elim_inl,mul_zero,Finset.sum_const_zero,add_zero]
      unfold bulkB
      rw [Finset.mul_sum]
      simp only [EuclideanSpace.inner_eq_star_dotProduct,dotProduct,star_trivial]
      apply Finset.sum_congr rfl
      intro i _hi
      have hn : (0:ℝ)<(m+1:ℕ) := by positivity
      have hs : Real.sqrt ((m+1:ℕ):ℝ)^2=(m+1:ℕ) := Real.sq_sqrt hn.le
      have hp : Real.sqrt ((m+1:ℕ):ℝ)≠0 := ne_of_gt (Real.sqrt_pos.mpr hn)
      field_simp
      rw [hs]
      ring
    | inr _index =>
      simp only [Fintype.sum_sum_type,cavityBulkBase,Sum.elim_inr,mul_zero,Finset.sum_const_zero,zero_add]
      rw [EuclideanSpace.inner_eq_star_dotProduct]
      rfl
  · rw [ite_eq_right hjk]
    apply Finset.sum_eq_zero
    intro p _hp
    apply Finset.sum_eq_zero
    intro t _ht
    by_cases hpj : p=j
    · subst p
      simp [hjk]
    · simp [hpj]

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cavity_CavityBulkLog
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology BigOperators BoundedContinuousFunction

lemma log_sub_le_div_sub {a b : ℝ} (ha : 0<a) (hb : 0<b) :
    Real.log a-Real.log b≤(a-b)/b := by
  have h:=Real.log_le_sub_one_of_pos (div_pos ha hb)
  rw [Real.log_div ha.ne' hb.ne'] at h
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  field_simp

lemma cavity_cap_tail {x Λ : ℝ} (hx : 0≤x) (hΛ : 0<Λ) :
    0≤x-min x Λ ∧ x-min x Λ≤x^2/Λ := by
  constructor
  · exact sub_nonneg.mpr (min_le_left _ _)
  · apply (le_div_iff₀ hΛ).mpr
    by_cases h : x≤Λ
    · rw [min_eq_left h]; nlinarith
    · rw [min_eq_right (le_of_not_ge h)]; nlinarith

lemma cavity_capped_log_bound {S : Type*} [MeasurableSpace S]
    (μ : Measure S) [IsProbabilityMeasure μ] {W F : S→ℝ} {C Λ : ℝ}
    (hW : Measurable W) (hWC : ∀ x,|W x|≤C) (hF : MemLp F 2 μ)
    (hF1 : ∀ x,1≤F x) (hΛ : 1≤Λ) :
    let A:=∫ x,Real.exp (W x)*F x ∂μ
    let B:=∫ x,Real.exp (W x)*min (F x) Λ ∂μ
    0≤Real.log A-Real.log B ∧
      Real.log A-Real.log B≤Real.exp (2*C)/Λ*(∫ x,(F x)^2 ∂μ) := by
  dsimp only
  let G : S→ℝ:=fun x=>min (F x) Λ
  have hFp x : 0≤F x := (by norm_num : (0:ℝ)≤1).trans (hF1 x)
  have hGp x : 1≤G x := le_min (hF1 x) hΛ
  have hGb x : ‖G x‖≤Λ := by
    rw [Real.norm_eq_abs,abs_of_nonneg ((by norm_num : (0:ℝ)≤1).trans (hGp x))]
    exact min_le_right _ _
  have hGm : AEStronglyMeasurable G μ := (hF.aestronglyMeasurable.aemeasurable.min aemeasurable_const).aestronglyMeasurable
  have hGi : Integrable G μ := Integrable.of_bound hGm Λ (ae_of_all _ hGb)
  have hFi := hF.integrable (by norm_num)
  have hF2 : Integrable (fun x=>(F x)^2) μ := (memLp_two_iff_integrable_sq hF.aestronglyMeasurable).mp hF
  have hWF : Integrable (fun x=>Real.exp (W x)*F x) μ := by
    apply (hFi.const_mul (Real.exp C)).mono' (hW.exp.aestronglyMeasurable.mul hF.aestronglyMeasurable)
    filter_upwards [] with x
    simp only [Pi.mul_apply]
    rw [Real.norm_eq_abs,abs_mul,abs_of_pos (Real.exp_pos _),abs_of_nonneg (hFp x)]
    exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (abs_le.mp (hWC x)).2) (hFp x)
  have hWG : Integrable (fun x=>Real.exp (W x)*G x) μ := by
    apply (hGi.const_mul (Real.exp C)).mono' (hW.exp.aestronglyMeasurable.mul hGm)
    filter_upwards [] with x
    simp only [Pi.mul_apply]
    rw [Real.norm_eq_abs,abs_mul,abs_of_pos (Real.exp_pos _),abs_of_nonneg ((by norm_num : (0:ℝ)≤1).trans (hGp x))]
    exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (abs_le.mp (hWC x)).2)
      ((by norm_num : (0:ℝ)≤1).trans (hGp x))
  have hBlo : Real.exp (-C)≤∫ x,Real.exp (W x)*G x ∂μ := by
    calc
      _=∫ _ : S,Real.exp (-C) ∂μ := by simp
      _≤_ := integral_mono (integrable_const _) hWG fun x=>by
        calc
          Real.exp (-C)≤Real.exp (W x) := Real.exp_le_exp.mpr (abs_le.mp (hWC x)).1
          _≤Real.exp (W x)*G x := by nlinarith [Real.exp_pos (W x),hGp x]
  have hBA : (∫ x,Real.exp (W x)*G x ∂μ)≤∫ x,Real.exp (W x)*F x ∂μ :=
    integral_mono hWG hWF fun x=>mul_le_mul_of_nonneg_left (min_le_left _ _) (Real.exp_pos _).le
  have hBp: 0<∫ x,Real.exp (W x)*G x ∂μ := (Real.exp_pos _).trans_le hBlo
  have hAp:=hBp.trans_le hBA
  have htail : (∫ x,Real.exp (W x)*F x ∂μ)-(∫ x,Real.exp (W x)*G x ∂μ)≤
      Real.exp C/Λ*(∫ x,(F x)^2 ∂μ) := by
    rw [←integral_sub hWF hWG,←integral_const_mul]
    apply integral_mono (hWF.sub hWG) (hF2.const_mul _)
    intro x
    have ht:=cavity_cap_tail (hFp x) ((by norm_num : (0:ℝ)<1).trans_le hΛ)
    calc
      _=Real.exp (W x)*(F x-G x)  := by simp only [Pi.sub_apply]; ring
      _≤Real.exp C*(F x-G x) := mul_le_mul_of_nonneg_right
        (Real.exp_le_exp.mpr (abs_le.mp (hWC x)).2) ht.1
      _≤Real.exp C*((F x)^2/Λ) := mul_le_mul_of_nonneg_left ht.2 (Real.exp_pos _).le
      _=_ := by ring
  refine ⟨sub_nonneg.mpr (Real.log_le_log hBp hBA),?_⟩
  calc
    _≤((∫ x,Real.exp (W x)*F x ∂μ)-(∫ x,Real.exp (W x)*G x ∂μ))/
      (∫ x,Real.exp (W x)*G x ∂μ) := log_sub_le_div_sub hAp hBp
    _≤(Real.exp C/Λ*(∫ x,(F x)^2 ∂μ))/(Real.exp (-C)) :=
      (div_le_div_of_nonneg_right htail hBp.le).trans
        (div_le_div_of_nonneg_left (mul_nonneg (div_nonneg (Real.exp_pos _).le (le_trans (by norm_num) hΛ))
          (integral_nonneg fun x=>sq_nonneg _)) (Real.exp_pos _) hBlo)
    _=_ := by rw [Real.exp_neg,div_inv_eq_mul,show 2*C=C+C by ring,Real.exp_add]; ring

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cavity_CavityCompensator
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceCountDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceCountKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityIncrementRandomCavityIncrementLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityProxyRandomCavityProxyLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

lemma cavity_exp_local_lipschitz {a b K : ℝ} (ha : a≤K) (hb : b≤K) :
    |Real.exp a-Real.exp b|≤Real.exp K*|a-b| := by
  have h:=Convex.norm_image_sub_le_of_norm_deriv_le
    (f:=Real.exp) (s:=Iic K) (C:=Real.exp K)
    (fun x _hx=>Real.differentiableAt_exp)
    (fun x hx=>by simpa only [Real.deriv_exp,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)] using Real.exp_le_exp.mpr hx)
    (convex_Iic K) hb ha
  simpa only [Real.norm_eq_abs] using h

lemma cavity_log_local_lipschitz {a b m : ℝ} (hm : 0 < m) (ha : m ≤ a) (hb : m ≤ b) :
    |Real.log a-Real.log b|≤|a-b|/m := by
  have h:=Convex.norm_image_sub_le_of_norm_deriv_le
    (f:=Real.log) (s:=Ici m) (C:=m⁻¹)
    (fun x hx=>Real.differentiableAt_log (hm.trans_le hx).ne')
    (fun x hx=>by
      rw [Real.deriv_log,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr (hm.trans_le hx))]
      exact inv_anti₀ hm hx)
    (convex_Ici m) hb ha
  simpa only [Real.norm_eq_abs,div_eq_mul_inv,mul_comm] using h

lemma cavity_compensator_bound {S : Type*} [MeasurableSpace S]
    (μ : Measure S) [IsProbabilityMeasure μ] {W C : S→ℝ} {a b K c t : ℝ}
    (hW : Measurable W) (hC : Measurable C) (ha : 0<a) (ht : 0≤t)
    (hw : ∀ x,a≤W x ∧ W x≤b) (hc : |c|≤K) (hcb : ∀ x,|C x|≤K) :
    |Real.log (∫ x,Real.exp (t*C x)*W x ∂μ)-
      (t*c+Real.log (∫ x,W x ∂μ))|≤
      (Real.exp (t*K)*b/(Real.exp (-(t*K))*a))*t*(∫ x,|C x-c| ∂μ) := by
  have hb : 0≤b := by
    by_contra hh
    have hfalse : ∀ x : S, False := fun x=>not_le.mpr (ha.trans_le ((hw x).1.trans (hw x).2)) (le_of_not_ge hh)
    have he : (univ : Set S)=∅ := Set.ext (fun x=>⟨fun _=>(hfalse x).elim,fun h=>h.elim⟩)
    have hμ := measure_univ (μ:=μ)
    rw [he,measure_empty] at hμ
    exact zero_ne_one hμ
  have hK : 0≤K := (abs_nonneg c).trans hc
  have hWi : Integrable W μ := Integrable.of_bound hW.aestronglyMeasurable b
    (ae_of_all _ fun x=>by rw [Real.norm_eq_abs,abs_of_pos (ha.trans_le (hw x).1)]; exact (hw x).2)
  have hEi : Integrable (fun x=>Real.exp (t*C x)*W x) μ :=
    Integrable.of_bound (hC.const_mul t |>.exp |>.aestronglyMeasurable |>.mul hW.aestronglyMeasurable)
      (Real.exp (t*K)*b) (ae_of_all _ fun x=>by
        rw [Real.norm_eq_abs,abs_mul,abs_of_pos (Real.exp_pos _),abs_of_pos (ha.trans_le (hw x).1)]
        exact mul_le_mul (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (abs_le.mp (hcb x)).2 ht))
          (hw x).2 (ha.trans_le (hw x).1).le (Real.exp_pos _).le)
  have hBi := hWi.const_mul (Real.exp (t*c))
  have hlo : Real.exp (-(t*K))*a≤∫ x,Real.exp (t*C x)*W x ∂μ := by
    calc
      _=∫ _ : S,Real.exp (-(t*K))*a ∂μ := by simp
      _≤_ := integral_mono (integrable_const _) hEi fun x=>by
        apply mul_le_mul _ (hw x).1 ha.le (Real.exp_pos _).le
        apply Real.exp_le_exp.mpr
        nlinarith [(abs_le.mp (hcb x)).1]
  have hWlo : a≤∫ x,W x ∂μ := by
    simpa using integral_mono (integrable_const a) hWi fun x=>(hw x).1
  have hbLo : Real.exp (-(t*K))*a≤Real.exp (t*c)*(∫ x,W x ∂μ) := by
    apply mul_le_mul _ hWlo ha.le (Real.exp_pos _).le
    exact Real.exp_le_exp.mpr (by nlinarith [(abs_le.mp hc).1])
  have hCi : Integrable (fun x=>|C x-c|) μ :=
    Integrable.of_bound (hC.sub_const c).abs.aestronglyMeasurable (K+|c|)
      (ae_of_all _ fun x=>by simpa only [Real.norm_eq_abs,abs_abs] using
        (abs_sub (C x) c).trans (add_le_add (hcb x) (le_refl |c|)))
  have hdiff : |(∫ x,Real.exp (t*C x)*W x ∂μ)-Real.exp (t*c)*(∫ x,W x ∂μ)|≤
      Real.exp (t*K)*b*t*(∫ x,|C x-c| ∂μ) := by
    rw [←integral_const_mul,←integral_sub hEi hBi]
    apply (abs_integral_le_integral_abs).trans
    rw [←integral_const_mul]
    apply integral_mono (hEi.sub hBi).abs (hCi.const_mul _)
    intro x
    simp only [Pi.sub_apply]
    rw [←sub_mul,abs_mul,abs_of_pos (ha.trans_le (hw x).1)]
    have hex:=cavity_exp_local_lipschitz
      (mul_le_mul_of_nonneg_left (abs_le.mp (hcb x)).2 ht)
      (mul_le_mul_of_nonneg_left (abs_le.mp hc).2 ht)
    rw [←mul_sub,abs_mul,abs_of_nonneg ht] at hex
    calc
      _≤(Real.exp (t*K)*(t*|C x-c|))*b := mul_le_mul hex (hw x).2 (ha.trans_le (hw x).1).le (by positivity)
      _=_ := by ring
  have hlog:=cavity_log_local_lipschitz (mul_pos (Real.exp_pos _) ha) hlo hbLo
  rw [Real.log_mul (Real.exp_pos _).ne' (ha.trans_le hWlo).ne',Real.log_exp] at hlog
  exact hlog.trans (by
    apply (div_le_div_of_nonneg_right hdiff (mul_pos (Real.exp_pos _) ha).le).trans
    apply le_of_eq
    ring)


lemma bulkC_measurable (m M : ℕ) (f : Jet3) :
    Measurable (fun p : BulkDisorder (m+1) M×NormalizedSpin (m+1)=>bulkC (m+1) M f p.1.1 p.2) := by
  unfold bulkC
  fun_prop

lemma bulkC_bound (m M : ℕ) (f : Jet3) (hf : HasCompactSupport (f.d1 : ℝ→ℝ))
    (a : BulkDisorder (m+1) M) (x : NormalizedSpin (m+1)) :
    |bulkC (m+1) M f a.1 x|≤M/(m+1:ℕ)*‖f.dilationMark hf‖ := by
  exact bulkSingleAverage_bound m M (f.dilationMark hf) a (fun _=>x)

lemma cavity_comp_partition_joint_measurable {A S J E : Type*}
    [MeasurableSpace A] [MeasurableSpace S] [Fintype J] [DecidableEq J]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure S) [SFinite μ]
    (v : A→S→J→E) (hv : Measurable (Function.uncurry v))
    (H C : A→S→ℝ) (hH : Measurable (Function.uncurry H))
    (hC : Measurable (Function.uncurry C)) (t : ℝ) (Ψ : EuclideanSpace ℝ J→ᵇℝ) :
    Measurable (fun p : A×E=>tiltMean μ (H p.1)
      (fun x=>Real.exp (t*C p.1 x)*Ψ (gaussianRows (v p.1 x) p.2)) 1) := by
  let κ : Kernel (A×E) S := Kernel.const _ μ
  have hproj : Measurable (fun p : (A×E)×S=>(p.1.1,p.2)) :=
    measurable_fst.fst.prodMk measurable_snd
  apply kernel_tiltMean_measurable κ (H:=fun p x=>H p.1 x)
    (Y:=fun p x=>Real.exp (t*C p.1 x)*Ψ (gaussianRows (v p.1 x) p.2)) (hH.comp hproj)
  exact ((hC.comp hproj).const_mul t).exp.mul
    (Ψ.measurable.comp (cavity_rows_joint_measurable (hv.comp hproj) measurable_fst.snd))

lemma cavityBulkCompPartition_measurable (n d m M : ℕ) (f : Jet3) (v : ℕ→ℝ)
    (Λ : ℝ) (hΛ : 1≤Λ) : Measurable (cavityBulkCompPartition n d m M f v Λ hΛ) := by
  exact cavity_comp_partition_joint_measurable (unitSphereLaw (m+1))
    (cavityBulkFeature n d m M f) (cavityBulkFeature_measurable n d m M f)
    (bulkGibbsHamiltonian m M f.f v) (fun a x=>bulkC (m+1) M f a.1 x)
    (bulkGibbsHamiltonian_measurable m M f.f v) (bulkC_measurable m M f) _ _

lemma cavityCompensatorConstant_nonneg (n d : ℕ) (f : ℝ→ᵇℝ) {Λ K : ℝ} (hΛ : 1≤Λ) :
    0 ≤ cavityCompensatorConstant n d f Λ K := by
  unfold cavityCompensatorConstant
  have : 0≤Λ := (by norm_num : (0:ℝ)≤1).trans hΛ
  positivity

lemma tilt_cavity_compensator_bound {S : Type*} [MeasurableSpace S]
    (μ : Measure S) [IsProbabilityMeasure μ] {H W C : S→ℝ} {a b K c t : ℝ}
    (hH : Measurable H) (he : Integrable (fun x=>Real.exp (1*H x)) μ)
    (hW : Measurable W) (hC : Measurable C) (ha : 0<a) (ht : 0≤t)
    (hw : ∀ x,a≤W x ∧ W x≤b) (hc : |c|≤K) (hcb : ∀ x,|C x|≤K) :
    |Real.log (tiltMean μ H (fun x=>Real.exp (t*C x)*W x) 1)-
      (t*c+Real.log (tiltMean μ H W 1))|≤
      (Real.exp (t*K)*b/(Real.exp (-(t*K))*a))*t*(tiltMean μ H (fun x=>|C x-c|) 1) := by
  have := tilt_law_probability_of_integrable μ he
  simp_rw [←tilt_law_integral_of_integrable μ hH he]
  exact cavity_compensator_bound _ hW hC ha ht hw hc hcb

lemma cavityBulkSingleWeight_measurable (n d m M : ℕ) (f : Jet3)
    (Λ : ℝ) (hΛ : 1≤Λ)
    (p : BulkDisorder (m+1) M×EuclideanSpace ℝ (CavityBulkNoiseIndex n d m M)) :
    Measurable (fun x=>cavitySingleTest n d f.f Λ hΛ
      (gaussianRows (cavityBulkFeature n d m M f p.1 x) p.2)) := by
  exact (cavitySingleTest n d f.f Λ hΛ).measurable.comp
    (cavity_rows_joint_measurable ((cavityBulkFeature_measurable n d m M f).of_uncurry_left) measurable_const)

lemma cavityBulkCompPartition_error (n d m M : ℕ) (f : Jet3) (v : ℕ→ℝ)
    (Λ : ℝ) (hΛ : 1≤Λ) (c K : ℝ) (hc : |c|≤K)
    (hC : ∀ (a : BulkDisorder (m+1) M) x,|bulkC (m+1) M f a.1 x|≤K)
    (p : BulkDisorder (m+1) M×EuclideanSpace ℝ (CavityBulkNoiseIndex n d m M)) :
    |Real.log (cavityBulkCompPartition n d m M f v Λ hΛ p)-
      ((n+1:ℕ)/2*c+Real.log (cavityBulkPartition n d m M f v Λ hΛ p))|≤
    cavityCompensatorConstant n d f.f Λ K*
      tiltMean (unitSphereLaw (m+1)) (bulkGibbsHamiltonian m M f.f v p.1)
        (fun x=>|bulkC (m+1) M f p.1.1 x-c|) 1 := by
  apply tilt_cavity_compensator_bound (unitSphereLaw (m+1))
    ((bulkGibbsHamiltonian_measurable m M f.f v).of_uncurry_left)
    (by simpa only [one_mul,bulkGibbsHamiltonian] using bulkHamiltonian_exp_integrable m M f.f v p.1)
    (cavityBulkSingleWeight_measurable n d m M f Λ hΛ p)
    ((bulkC_measurable m M f).comp (measurable_const.prodMk measurable_id))
    (Real.exp_pos _) (by positivity) (fun x=>cavitySingleTest_bounds n d f.f Λ hΛ _) hc (hC p.1)

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Sphere_GaussianPolar
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.bulkFiniteReplicaLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.bulkSpinKernel_markov _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.enrichedIndexedBaseMeasure_probability _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceBaseDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceSpinLeafKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceCountDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceCountKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityIncrementRandomCavityIncrementLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityProxyRandomCavityProxyLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal NNReal
namespace SphericalPerceptronFreeEnergy

lemma normalizedGaussian_smul (n : ℕ) (r : Ioi (0:ℝ))
    (u : Metric.sphere (0:Spin (n+1)) 1) :
    ‖r.val • u.val‖⁻¹ • (r.val • u.val)=u.val := by
  have hn : ‖u.val‖=1 := by simpa only [Metric.mem_sphere,dist_zero_right] using u.prop
  rw [norm_smul,Real.norm_eq_abs,abs_of_pos r.prop,hn,mul_one,smul_smul,
    inv_mul_cancel₀ (ne_of_gt r.prop),one_smul]

lemma normalizedGaussian_polar_law (n : ℕ) :
    (stdGaussian (Spin (n+1))).map (fun x => (‖x‖,‖x‖⁻¹ • x))=
      ((gaussianRadiusLaw n).map Subtype.val).prod
        ((unitSphereLaw (n+1)).map Subtype.val) := by
  apply Measure.ext_of_lintegral
  intro F hF
  rw [lintegral_map hF (by fun_prop)]
  rw [stdGaussian_polar_lintegral n (fun x => F (‖x‖,‖x‖⁻¹ • x)) (by fun_prop),
    lintegral_prod _ hF.aemeasurable]
  rw [lintegral_map (by fun_prop) (by fun_prop)]
  apply lintegral_congr
  intro r
  rw [lintegral_map (f:=fun y : Spin (n+1) => F (r.val,y)) (by fun_prop) measurable_subtype_coe]
  apply lintegral_congr
  intro u
  rw [normalizedGaussian_smul]
  have hn : ‖u.val‖=1 := by simpa only [Metric.mem_sphere,dist_zero_right] using u.prop
  rw [norm_smul,Real.norm_eq_abs,abs_of_pos r.prop,hn,mul_one]

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_GaussianBlock
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.bulkFiniteReplicaLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.bulkSpinKernel_markov _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.enrichedIndexedBaseMeasure_probability _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceBaseDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceSpinLeafKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceCountDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceCountKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityIncrementRandomCavityIncrementLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityProxyRandomCavityProxyLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped Topology ENNReal NNReal
namespace SphericalPerceptronFreeEnergy

lemma gaussianBlockSplit_measurable (N L : ℕ) : Measurable (gaussianBlockSplit N L) := by
  unfold gaussianBlockSplit
  fun_prop

lemma gaussianBlockSplit_preserving (N L : ℕ) :
    MeasurePreserving (gaussianBlockSplit N L) (stdGaussian (Spin (N+L)))
      ((stdGaussian (Spin N)).prod (stdGaussian (Spin L))) := by
  have hp := (measurePreserving_sumPiEquivProdPi (fun _ : Fin N ⊕ Fin L => gaussianReal 0 1)).comp
    (measurePreserving_piCongrLeft (fun _ : Fin N ⊕ Fin L => gaussianReal 0 1) finSumFinEquiv.symm)
  have hN : MeasurePreserving (WithLp.toLp 2 : (Fin N→ℝ)→Spin N)
      (Measure.pi fun _ => gaussianReal 0 1) (stdGaussian (Spin N)) :=
    ⟨(PiLp.continuous_toLp 2 _).measurable,map_pi_eq_stdGaussian⟩
  have hL : MeasurePreserving (WithLp.toLp 2 : (Fin L→ℝ)→Spin L)
      (Measure.pi fun _ => gaussianReal 0 1) (stdGaussian (Spin L)) :=
    ⟨(PiLp.continuous_toLp 2 _).measurable,map_pi_eq_stdGaussian⟩
  refine ⟨gaussianBlockSplit_measurable N L,?_⟩
  rw [←map_pi_eq_stdGaussian,Measure.map_map (gaussianBlockSplit_measurable N L)
    (PiLp.continuous_toLp 2 _).measurable]
  convert ((hN.prod hL).comp hp).map_eq using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  funext x
  apply Prod.ext <;> ext i <;>
    simp [gaussianBlockSplit,MeasurableEquiv.piCongrLeft,MeasurableEquiv.sumPiEquivProdPi,
      Equiv.piCongrLeft,Equiv.piCongrLeft',eq_rec_constant]

lemma stdGaussian_direction_law (n : ℕ) :
    (stdGaussian (Spin (n+1))).map (fun x => ‖x‖⁻¹ •x)=
      (unitSphereLaw (n+1)).map Subtype.val := by
  have : IsProbabilityMeasure ((gaussianRadiusLaw n).map Subtype.val) := by first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
  have h := congrArg (fun μ : Measure (ℝ×Spin (n+1)) => μ.map Prod.snd) (normalizedGaussian_polar_law n)
  rwa [Measure.map_map measurable_snd (by fun_prop),Measure.map_snd_prod,measure_univ,one_smul] at h

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cavity_CavityGeometry
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.bulkFiniteReplicaLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceCountDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceCountKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityIncrementRandomCavityIncrementLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityProxyRandomCavityProxyLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped Topology BigOperators
namespace SphericalPerceptronFreeEnergy

lemma gaussianBlockJoin_measurable (N L : ℕ) : Measurable (gaussianBlockJoin N L) := by
  apply (PiLp.continuous_toLp 2 _).measurable.comp
  apply Measurable.of_eval
  intro i
  induction i using Fin.addCases <;> simp only [Fin.addCases_left,Fin.addCases_right] <;> fun_prop

lemma gaussianBlockJoin_split (N L : ℕ) (x : Spin (N+L)) :
    gaussianBlockJoin N L (gaussianBlockSplit N L x)=x := by
  ext i
  induction i using Fin.addCases <;> simp [gaussianBlockSplit,gaussianBlockJoin]

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cavity_CavityDisintegration
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.bulkFiniteReplicaLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.bulkSpinKernel_markov _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.enrichedIndexedBaseMeasure_probability _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceBaseDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceSpinLeafKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceCountDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceCountKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityIncrementRandomCavityIncrementLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityProxyRandomCavityProxyLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal NNReal BigOperators

lemma stdGaussian_radial_preserving (n : ℕ) :
    MeasurePreserving (fun p : Ioi (0:ℝ)×Metric.sphere (0:Spin (n+1)) 1 => p.1.val •p.2.val)
      ((gaussianRadiusLaw n).prod (unitSphereLaw (n+1))) (stdGaussian (Spin (n+1))) := by
  refine ⟨by fun_prop,?_⟩
  apply Measure.ext_of_lintegral
  intro F hF
  rw [lintegral_map hF (by fun_prop),lintegral_prod _ (by fun_prop)]
  exact (stdGaussian_polar_lintegral n F hF).symm

lemma cavityBlockNormalize_measurable (N L : ℕ) : Measurable (cavityBlockNormalize N L) := by
  unfold cavityBlockNormalize
  fun_prop

lemma gaussianBlockSplit_normalize (N L : ℕ) (x : Spin (N+L)) :
    gaussianBlockSplit N L (‖x‖⁻¹ •x)=cavityBlockNormalize N L (gaussianBlockSplit N L x) := by
  unfold cavityBlockNormalize
  rw [←gaussianBlockSplit_norm_sq,Real.sqrt_sq (norm_nonneg x)]
  apply Prod.ext <;> ext i <;> rfl

lemma sphereBlock_gaussian_law (n L : ℕ) :
    (unitSphereLaw (n+1+L)).map (fun u => gaussianBlockSplit (n+1) L u.val)=
      ((stdGaussian (Spin (n+1))).prod (stdGaussian (Spin L))).map (cavityBlockNormalize (n+1) L) := by
  have hd : (stdGaussian (Spin (n+1+L))).map (fun x => ‖x‖⁻¹ •x)=
      (unitSphereLaw (n+1+L)).map Subtype.val := by
    have he : n+1+L=(n+L)+1 := by omega
    rw [he]
    exact stdGaussian_direction_law (n+L)
  have h := congrArg (fun μ : Measure (Spin (n+1+L)) => μ.map (gaussianBlockSplit (n+1) L)) hd
  rw [Measure.map_map (gaussianBlockSplit_measurable _ _) (by fun_prop),
    Measure.map_map (gaussianBlockSplit_measurable _ _) measurable_subtype_coe] at h
  simp only [Function.comp_def] at h
  rw [←h,←(gaussianBlockSplit_preserving (n+1) L).map_eq,
    Measure.map_map (cavityBlockNormalize_measurable _ _) (gaussianBlockSplit_measurable _ _)]
  congr 1
  funext x
  exact gaussianBlockSplit_normalize (n+1) L x

lemma cavityRadialBlock_eq (n L : ℕ) (p : (Ioi (0:ℝ)×Metric.sphere (0:Spin (n+1)) 1)×Spin L) :
    cavityRadialBlock n L p=cavityBlockNormalize (n+1) L (p.1.1.val •p.1.2.val,p.2) := by
  have hn : ‖p.1.2.val‖=1 := by simpa only [Metric.mem_sphere,dist_zero_right] using p.1.2.prop
  simp only [cavityRadialBlock,cavityBlockNormalize,norm_smul,Real.norm_eq_abs,
    abs_of_pos (show (0:ℝ)<p.1.1.val from p.1.1.prop),hn,mul_one,smul_smul]

theorem sphereBlock_radial_law (n L : ℕ) :
    (unitSphereLaw (n+1+L)).map (fun u => gaussianBlockSplit (n+1) L u.val)=
      (((gaussianRadiusLaw n).prod (unitSphereLaw (n+1))).prod (stdGaussian (Spin L))).map
        (cavityRadialBlock n L) := by
  rw [sphereBlock_gaussian_law]
  have hp := (stdGaussian_radial_preserving n).prod (MeasurePreserving.id (stdGaussian (Spin L)))
  rw [←hp.map_eq,Measure.map_map (cavityBlockNormalize_measurable _ _) hp.measurable]
  congr 1
  funext p
  exact (cavityRadialBlock_eq n L p).symm

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cavity_CavityShellLimit
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.bulkFiniteReplicaLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.bulkSpinKernel_markov _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.enrichedIndexedBaseMeasure_probability _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceBaseDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceSpinLeafKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceCountDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceCountKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityIncrementRandomCavityIncrementLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityProxyRandomCavityProxyLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal NNReal BigOperators BoundedContinuousFunction

lemma cavityShell_measurable (L : ℕ) : MeasurableSet (cavityShell L) := by
  exact (isClosed_Icc.preimage (show Continuous (fun z : Spin L=>‖z‖^2) from continuous_norm.pow 2)).measurableSet

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cavity_CavityShellPerturbation
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.bulkFiniteReplicaLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceCountDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceCountKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityIncrementRandomCavityIncrementLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityProxyRandomCavityProxyLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology BigOperators ENNReal BoundedContinuousFunction

lemma cavityRho_measurable (N L : ℕ) : Measurable (cavityRho N L) := by
  unfold cavityRho
  fun_prop

lemma cavityNormalizedVec_measurable (N L : ℕ) :
    Measurable (fun p : NormalizedSpin N×Spin L=>cavityNormalizedVec N L p.1 p.2) := by
  unfold cavityNormalizedVec
  apply (gaussianBlockJoin_measurable N L).comp
  exact (((cavityRho_measurable N L).comp measurable_snd).smul measurable_fst.subtype_val).prodMk
    (measurable_snd.const_smul ((Real.sqrt (N+L:ℕ))⁻¹))

lemma cavityShellProbability_probability (n L : ℕ)
    (hp : (cavitySphereLaw n L : Measure (Spin L)) (cavityShell L)≠0) :
    IsProbabilityMeasure (cavityShellProbability n L) := by
  let ν := (cavitySphereLaw n L : Measure (Spin L))
  let := cond_isProbabilityMeasure (μ:=ν) hp
  apply (MeasurableEmbedding.subtype_coe (cavityShell_measurable L)).isProbabilityMeasure_comap
  simp only [Subtype.range_coe]
  apply (mem_ae_iff_prob_eq_one (cavityShell_measurable L)).mpr
  exact cond_apply_self hp (measure_ne_top _ _)

lemma cavityShellBaseLaw_probability (n L : ℕ)
    (hp : (cavitySphereLaw n L : Measure (Spin L)) (cavityShell L)≠0) :
    IsProbabilityMeasure (cavityShellBaseLaw n L) := by
  let := cavityShellProbability_probability n L hp
  unfold cavityShellBaseLaw
  first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

lemma cavityShellSpinEmbedding_measurable (n L : ℕ) : Measurable (cavityShellSpinEmbedding n L) := by
  apply Measurable.subtype_mk
  exact (cavityNormalizedVec_measurable (n+1) L).comp
    (f:=fun s : CavityShellSpin n L=>(s.1,s.2.val))
    (measurable_fst.prodMk measurable_snd.subtype_val)

lemma cavityShellPatternEnergy_bound (n L M : ℕ) (f : ℝ→ᵇℝ)
    (a : Fin M→Fin (n+1+L)→ℝ) (s : CavityShellSpin n L) :
    |cavityShellPatternEnergy n L M f a s|≤M*‖f‖ :=
  normalizedPatternEnergy_bound _ _ _ _ _

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cavity_CavityQuadraticDrop
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.bulkFiniteReplicaLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.bulkSpinKernel_markov _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.enrichedIndexedBaseMeasure_probability _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceBaseDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceSpinLeafKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceCountDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceCountKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityIncrementRandomCavityIncrementLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityProxyRandomCavityProxyLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal BigOperators

lemma cavity_log_drop_quadratic {S : Type*} [MeasurableSpace S]
    (μ : Measure S) [IsProbabilityMeasure μ] {H Q : S→ℝ}
    (hH : Measurable H) (hQ : Measurable Q) {A B : ℝ}
    (hA : 0≤A) (hB : 0≤B) (hHA : ∀ x,|H x|≤A) (hQB : ∀ x,|Q x|≤B) :
    Real.log (∫ x,Real.exp (H x+Q x) ∂μ)≥
      Real.log (∫ x,Real.exp (H x) ∂μ)-
        (∫ x,Real.exp (H x)*|Q x| ∂μ)/(∫ x,Real.exp (H x) ∂μ) := by
  have hc := affineLogRoot_convex μ hH hQ hA hB hHA hQB
  have hd := affineLogRoot_deriv μ hH hQ hA hB hHA hQB 0
  have hs := hc.le_slope_of_hasDerivAt (mem_univ 0) (mem_univ 1) (by norm_num : (0:ℝ)<1) hd
  simp only [affineLogRoot,tiltPartition,slope,zero_mul,add_zero,one_mul,sub_zero,inv_one,one_smul,vsub_eq_sub] at hs
  have hqq : -(∫ x,Real.exp (H x)*|Q x| ∂μ)≤∫ x,Real.exp (H x)*Q x ∂μ := by
    rw [←integral_neg]
    apply integral_mono
    · have hi : Integrable (fun x=>Real.exp (H x)*|Q x|) μ := by
        simpa only [one_mul] using tilt_integrable μ hH hQ.abs hA hB hHA (fun x=>by simpa only [abs_abs] using hQB x) 1
      exact hi.neg
    · simpa only [one_mul] using tilt_integrable μ hH hQ hA hB hHA hQB 1
    · intro x
      have := mul_le_mul_of_nonneg_left (neg_abs_le (Q x)) (Real.exp_pos (H x)).le
      simpa only [mul_neg] using this
  have hp : 0<∫ x,Real.exp (H x) ∂μ := by
    simpa only [tiltPartition,one_mul] using tilt_partition_pos μ hH hA hHA 1
  have hdiv := (div_le_div_of_nonneg_right hqq hp.le)
  simp only [tiltMean,tiltIntegral,tiltPartition,one_mul] at hs
  rw [neg_div] at hdiv
  linarith

lemma cavity_exp_abs_cauchy {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    {H Q : Ω→ℝ} (hE : MemLp (fun y=>Real.exp (H y)) 2 P) (hQ : MemLp Q 2 P) :
    (∫ y,Real.exp (H y)*|Q y| ∂P)≤
      Real.sqrt (∫ y,Real.exp (2*H y) ∂P)*Real.sqrt (∫ y,(Q y)^2 ∂P) := by
  have hp : Real.HolderConjugate 2 2 := by norm_num [Real.holderConjugate_iff]
  have he := integral_mul_norm_le_Lp_mul_Lq hp (by simpa using hE) (by simpa using hQ)
  simp only [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _),Real.rpow_two, sq_abs] at he
  simp_rw [←Real.exp_nat_mul] at he
  norm_num only [Nat.cast_ofNat] at he
  simpa only [Real.sqrt_eq_rpow,one_div] using he

lemma cavityLinearField_exp_integrable (M L : ℕ) (a : Fin M→ℝ) (t : ℝ) (z : Spin L) (p : ℝ) :
    Integrable (fun y=>Real.exp (p*cavityLinearField M L a t z y))
      (Measure.pi (fun _=>stdGaussian (Spin L))) := by
  by_contra hi
  have h:=cavityLinearField_exp_moment M L a t z p
  rw [integral_undef hi] at h
  exact (Real.exp_pos _).ne' h.symm

lemma cavityLinearField_exp_memLp (M L : ℕ) (a : Fin M→ℝ) (t : ℝ) (z : Spin L) (p : ℝ) :
    MemLp (fun y=>Real.exp (p*cavityLinearField M L a t z y)) 2
      (Measure.pi (fun _=>stdGaussian (Spin L))) := by
  apply (memLp_two_iff_integrable_sq (show AEStronglyMeasurable
    (fun y=>Real.exp (p*cavityLinearField M L a t z y)) _ from
      (show Continuous (fun y=>Real.exp (p*cavityLinearField M L a t z y)) from by
        unfold cavityLinearField; fun_prop).aestronglyMeasurable)).mpr
  have hi:=cavityLinearField_exp_integrable M L a t z (2*p)
  convert hi using 1
  all_goals try with_reducible_and_instances rfl
  ext y
  rw [←Real.exp_nat_mul]
  congr 1
  norm_num only [Nat.cast_ofNat]
  ring

lemma cavity_tilted_Q_conditional (M L : ℕ) (a b : Fin M→ℝ) (t u : ℝ) (z : Spin L) :
    (∫ y,Real.exp (cavityLinearField M L a t z y)*|cavityQuadraticField M L b u z y|
      ∂Measure.pi (fun _=>stdGaussian (Spin L)))≤
      Real.exp (t^2*‖z‖^2*∑ i,(a i)^2)*
        Real.sqrt (u^2*‖z‖^4*squareGaussianVariance*∑ i,(b i)^2) := by
  have he : MemLp (fun y=>Real.exp (cavityLinearField M L a t z y)) 2
      (Measure.pi (fun _=>stdGaussian (Spin L))) := by
    simpa only [one_mul] using cavityLinearField_exp_memLp M L a t z 1
  have h:=cavity_exp_abs_cauchy _ he (cavityQuadraticField_memLp M L b u z)
  rw [cavityLinearField_exp_moment,cavityQuadraticField_second_moment] at h
  have hx : (2:ℝ)^2*t^2*‖z‖^2/2*(∑ i,(a i)^2)=2*(t^2*‖z‖^2*∑ i,(a i)^2) := by ring
  have he2 (r : ℝ) : Real.exp (2*r)=(Real.exp r)^2 := Real.exp_nat_mul r 2
  rw [hx,he2,Real.sqrt_sq (Real.exp_pos _).le] at h
  exact h

lemma cavity_tilted_Q_uniform (M L : ℕ) (a b : Fin M→ℝ) (t u : ℝ) (z : Spin L)
    {A B D : ℝ} (_hA : 0≤A) (_hB : 0≤B) (hD : 0≤D)
    (ha : ∀ i,|a i|≤A) (hb : ∀ i,|b i|≤B) (hz : ‖z‖^2≤D) :
    (∫ y,Real.exp (cavityLinearField M L a t z y)*|cavityQuadraticField M L b u z y|
      ∂Measure.pi (fun _=>stdGaussian (Spin L)))≤
      Real.exp (t^2*D*M*A^2)*Real.sqrt (u^2*D^2*squareGaussianVariance*M*B^2) := by
  have hs {c : Fin M→ℝ} {C : ℝ} (hc : ∀ i, |c i|≤C) : ∑ i,(c i)^2≤M*C^2 := by
    calc
      _≤∑ _ : Fin M,C^2 := Finset.sum_le_sum fun i _=>by
        simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg (c i)) (hc i) 2
      _=_ := by simp
  apply (cavity_tilted_Q_conditional M L a b t u z).trans
  apply mul_le_mul
  · apply Real.exp_le_exp.mpr
    calc
      _≤t^2*D*(M*A^2) := mul_le_mul
        (mul_le_mul_of_nonneg_left hz (sq_nonneg t)) (hs ha)
        (Finset.sum_nonneg fun _ _=>sq_nonneg _) (mul_nonneg (sq_nonneg t) hD)
      _=_ := by ring
  · apply Real.sqrt_le_sqrt
    calc
      _=u^2*(‖z‖^2)^2*squareGaussianVariance*(∑ i,(b i)^2) := by ring
      _≤u^2*D^2*squareGaussianVariance*(M*B^2) := mul_le_mul
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (sq_nonneg _) hz 2) (sq_nonneg _)) squareGaussianVariance_nonneg)
        (hs hb) (Finset.sum_nonneg fun _ _=>sq_nonneg _)
        (mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _)) squareGaussianVariance_nonneg)
      _=_ := by ring
  · exact Real.sqrt_nonneg _
  · exact (Real.exp_pos _).le

lemma cavity_tilted_Q_integrable (M L : ℕ) (a b : Fin M→ℝ) (t u : ℝ) (z : Spin L) :
    Integrable (fun y=>Real.exp (cavityLinearField M L a t z y)*|cavityQuadraticField M L b u z y|)
      (Measure.pi (fun _=>stdGaussian (Spin L))) := by
  have he : MemLp (fun y=>Real.exp (cavityLinearField M L a t z y)) 2
      (Measure.pi (fun _=>stdGaussian (Spin L))) := by
    simpa only [one_mul] using cavityLinearField_exp_memLp M L a t z 1
  exact he.integrable_mul (cavityQuadraticField_memLp M L b u z).abs

lemma cavityLinearField_measurable {S : Type*} [MeasurableSpace S] (M L : ℕ)
    (a : S→Fin M→ℝ) (z : S→Spin L) (ha : Measurable a) (hz : Measurable z) (t : ℝ) :
    Measurable (fun p : S×(Fin M→Spin L)=>cavityLinearField M L (a p.1) t (z p.1) p.2) := by
  unfold cavityLinearField
  have hac : Measurable (fun p : S×(Fin M→Spin L)=>a p.1) := ha.comp measurable_fst
  have hzc : Measurable (fun p : S×(Fin M→Spin L)=>z p.1) := hz.comp measurable_fst
  fun_prop

lemma cavityQuadraticField_measurable {S : Type*} [MeasurableSpace S] (M L : ℕ)
    (b : S→Fin M→ℝ) (z : S→Spin L) (hb : Measurable b) (hz : Measurable z) (u : ℝ) :
    Measurable (fun p : S×(Fin M→Spin L)=>cavityQuadraticField M L (b p.1) u (z p.1) p.2) := by
  unfold cavityQuadraticField
  have hbc : Measurable (fun p : S×(Fin M→Spin L)=>b p.1) := hb.comp measurable_fst
  have hzc : Measurable (fun p : S×(Fin M→Spin L)=>z p.1) := hz.comp measurable_fst
  fun_prop

lemma cavity_Q_product_integrable {S : Type*} [MeasurableSpace S]
    (μ : Measure S) [IsProbabilityMeasure μ] (M L : ℕ)
    (a b : S→Fin M→ℝ) (z : S→Spin L) (W : S→ℝ)
    (ha : Measurable a) (hb : Measurable b) (hz : Measurable z) (hW : Measurable W)
    (t u : ℝ) {A B C D : ℝ} (hA : 0≤A) (hB : 0≤B) (hD : 0≤D)
    (haB : ∀ s i,|a s i|≤A) (hbB : ∀ s i,|b s i|≤B)
    (hzB : ∀ s,‖z s‖^2≤D) (hWB : ∀ s,|W s|≤C) :
    Integrable (fun p : S×(Fin M→Spin L)=>Real.exp (W p.1+cavityLinearField M L (a p.1) t (z p.1) p.2)*
      |cavityQuadraticField M L (b p.1) u (z p.1) p.2|)
      (μ.prod (Measure.pi (fun _=>stdGaussian (Spin L)))) := by
  let P:=Measure.pi (fun _ : Fin M=>stdGaussian (Spin L))
  let F : S×(Fin M→Spin L)→ℝ:=fun p=>
    Real.exp (W p.1+cavityLinearField M L (a p.1) t (z p.1) p.2)*
      |cavityQuadraticField M L (b p.1) u (z p.1) p.2|
  have hm : Measurable F :=
    ((hW.comp measurable_fst).add (cavityLinearField_measurable M L a z ha hz t)).exp.mul
      (cavityQuadraticField_measurable M L b z hb hz u).abs
  have hf s : Integrable (fun y=>F (s,y)) P := by
    simpa only [F,Real.exp_add,mul_assoc] using
      (cavity_tilted_Q_integrable M L (a s) (b s) t u (z s)).const_mul (Real.exp (W s))
  have hbound s : (∫ y,F (s,y) ∂P)≤Real.exp C*
      (Real.exp (t^2*D*M*A^2)*Real.sqrt (u^2*D^2*squareGaussianVariance*M*B^2)) := by
    conv_lhs => simp only [F,Real.exp_add,mul_assoc,integral_const_mul]
    exact mul_le_mul (Real.exp_le_exp.mpr (abs_le.mp (hWB s)).2)
      (cavity_tilted_Q_uniform M L (a s) (b s) t u (z s) hA hB hD (haB s) (hbB s) (hzB s))
      (integral_nonneg fun _=>mul_nonneg (Real.exp_pos _).le (abs_nonneg _)) (Real.exp_pos _).le
  apply (integrable_prod_iff hm.aestronglyMeasurable).mpr
  refine ⟨ae_of_all _ hf,?_⟩
  apply Integrable.of_bound (hm.aestronglyMeasurable.norm.integral_prod_right')
    (Real.exp C*(Real.exp (t^2*D*M*A^2)*Real.sqrt (u^2*D^2*squareGaussianVariance*M*B^2)))
  filter_upwards [] with s
  have hp : ∀ y,0≤F (s,y) := fun y=>mul_nonneg (Real.exp_pos _).le (abs_nonneg _)
  simp only [Real.norm_eq_abs]
  simp_rw [abs_of_nonneg (hp _)]
  rw [abs_of_nonneg (integral_nonneg hp)]
  exact hbound s

lemma cavity_Q_normalized_bound {S : Type*} [MeasurableSpace S]
    (μ : Measure S) [IsProbabilityMeasure μ] (M L : ℕ)
    (a b : S→Fin M→ℝ) (z : S→Spin L) (W : S→ℝ)
    (ha : Measurable a) (hb : Measurable b) (hz : Measurable z) (hW : Measurable W)
    (t u : ℝ) {A B C D : ℝ} (hA : 0≤A) (hB : 0≤B) (hD : 0≤D)
    (haB : ∀ s i,|a s i|≤A) (hbB : ∀ s i,|b s i|≤B)
    (hzB : ∀ s,‖z s‖^2≤D) (hWB : ∀ s,|W s|≤C)
    (hden : ∀ y,Real.exp (-C)≤∫ s,Real.exp (W s+cavityLinearField M L (a s) t (z s) y) ∂μ) :
    (∫ y,(∫ s,Real.exp (W s+cavityLinearField M L (a s) t (z s) y)*
        |cavityQuadraticField M L (b s) u (z s) y| ∂μ)/
      (∫ s,Real.exp (W s+cavityLinearField M L (a s) t (z s) y) ∂μ)
      ∂Measure.pi (fun _=>stdGaussian (Spin L)))≤
      Real.exp (2*C+t^2*D*M*A^2)*Real.sqrt (u^2*D^2*squareGaussianVariance*M*B^2) := by
  let P:=Measure.pi (fun _ : Fin M=>stdGaussian (Spin L))
  let F : S×(Fin M→Spin L)→ℝ:=fun p=>
    Real.exp (W p.1+cavityLinearField M L (a p.1) t (z p.1) p.2)*
      |cavityQuadraticField M L (b p.1) u (z p.1) p.2|
  let Z : (Fin M→Spin L)→ℝ:=fun y=>∫ s,Real.exp (W s+cavityLinearField M L (a s) t (z s) y) ∂μ
  have hi : Integrable F (μ.prod P) := cavity_Q_product_integrable μ M L a b z W ha hb hz hW t u hA hB hD haB hbB hzB hWB
  have hZm : AEStronglyMeasurable Z P := by
    exact (((hW.comp measurable_fst).add (cavityLinearField_measurable M L a z ha hz t)).exp.stronglyMeasurable).integral_prod_left'.aestronglyMeasurable
  have hnorm y : 0≤∫ s,F (s,y) ∂μ := integral_nonneg fun _=>mul_nonneg (Real.exp_pos _).le (abs_nonneg _)
  have hratio y : (∫ s,F (s,y) ∂μ)/Z y≤Real.exp C*(∫ s,F (s,y) ∂μ) := by
    rw [div_eq_mul_inv,mul_comm (Real.exp C)]
    apply mul_le_mul_of_nonneg_left _ (hnorm y)
    calc
      (Z y)⁻¹≤(Real.exp (-C))⁻¹ := inv_anti₀ (Real.exp_pos _) (hden y)
      _=Real.exp C := by rw [Real.exp_neg,inv_inv]
  have hrI : Integrable (fun y=>(∫ s,F (s,y) ∂μ)/Z y) P := by
    apply (hi.integral_prod_right.const_mul (Real.exp C)).mono'
      (hi.integral_prod_right.aestronglyMeasurable.div₀ hZm)
    filter_upwards [] with y
    change ‖(∫ s,F (s,y) ∂μ)/Z y‖≤_
    rw [Real.norm_eq_abs,abs_of_nonneg (div_nonneg (hnorm y) ((Real.exp_pos _).le.trans (hden y)))]
    exact hratio y
  calc
    _≤∫ y,Real.exp C*(∫ s,F (s,y) ∂μ) ∂P := integral_mono hrI (hi.integral_prod_right.const_mul _) hratio
    _=Real.exp C*(∫ s,∫ y,F (s,y) ∂P ∂μ) := by
      rw [integral_const_mul,←integral_integral_swap hi]
    _≤Real.exp C*(Real.exp C*(Real.exp (t^2*D*M*A^2)*Real.sqrt (u^2*D^2*squareGaussianVariance*M*B^2))) := by
      apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
      calc
        _≤∫ _ : S,Real.exp C*(Real.exp (t^2*D*M*A^2)*Real.sqrt (u^2*D^2*squareGaussianVariance*M*B^2)) ∂μ := by
          apply integral_mono hi.integral_prod_left (integrable_const _)
          intro s
          conv_lhs => simp only [F,Real.exp_add,mul_assoc,integral_const_mul]
          exact mul_le_mul (Real.exp_le_exp.mpr (abs_le.mp (hWB s)).2)
            (cavity_tilted_Q_uniform M L (a s) (b s) t u (z s) hA hB hD (haB s) (hbB s) (hzB s))
            (integral_nonneg fun _=>mul_nonneg (Real.exp_pos _).le (abs_nonneg _)) (Real.exp_pos _).le
        _=_ := by simp
    _=_ := by
      have he : Real.exp (2*C)=(Real.exp C)^2 := Real.exp_nat_mul C 2
      rw [Real.exp_add,he]
      ring

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cavity_CavitySphericalMoments
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceCountDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceCountKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityIncrementRandomCavityIncrementLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityProxyRandomCavityProxyLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped Topology NNReal ENNReal BigOperators
namespace SphericalPerceptronFreeEnergy

lemma cavityLinearField_inner (M L : ℕ) (a : Fin M→ℝ) (t : ℝ) (z : Spin L) (y : Fin M→Spin L) :
    cavityLinearField M L a t z y=inner ℝ (cavityVectorField M L a t y) z := by
  simp only [cavityLinearField,cavityVectorField,real_inner_smul_left, sum_inner, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [real_inner_comm z (y i)]

lemma sphericalExp_square_le (n : ℕ) (R : ℝ) (x : Spin (n+1)) :
    sphericalExp n x R ^2 ≤ sphericalExp n x (2*R) := by
  let F : NormalizedSpin (n+1)→ℝ:=fun u=>Real.exp (R*inner ℝ x u.val)
  have hm : MemLp F 2 (unitSphereLaw (n+1)) := by
    apply (memLp_two_iff_integrable_sq (show AEStronglyMeasurable F _ from
      (show Continuous F from by unfold F; fun_prop).aestronglyMeasurable)).mpr
    exact unitSphere_continuous_integrable (by unfold F; fun_prop)
  have hv:=variance_nonneg F (unitSphereLaw (n+1))
  rw [variance_eq_sub hm] at hv
  have he : (∫ u,F u^2 ∂unitSphereLaw (n+1))=sphericalExp n x (2*R) := by
    apply integral_congr_ae
    filter_upwards [] with u
    dsimp [F]
    rw [←Real.exp_nat_mul]
    congr 1
    norm_num only [Nat.cast_ofNat]
    ring
  change 0≤(∫ u,F u^2 ∂unitSphereLaw (n+1))-(∫ u,F u ∂unitSphereLaw (n+1))^2 at hv
  rw [he] at hv
  exact sub_nonneg.mp hv


lemma cavityLinearField_abs_bound (M L : ℕ) (a : Fin M→ℝ) (t : ℝ)
    (z : Spin L) (y : Fin M→Spin L) {A D : ℝ} (hA : 0≤A)
    (ha : ∀ i,|a i|≤A) (hz : ‖z‖≤D) :
    |cavityLinearField M L a t z y|≤|t| * ∑ i,A*D*‖y i‖ := by
  unfold cavityLinearField
  rw [abs_mul]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro i hi
  rw [abs_mul]
  calc
    _≤A*(‖z‖*‖y i‖) := mul_le_mul (ha i) (abs_real_inner_le_norm z (y i))
      (abs_nonneg _) hA
    _≤A*(D*‖y i‖) := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right hz (norm_nonneg _)) hA
    _=_ := by ring

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Variational_DilationExpansion
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set
open scoped BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

lemma weightedDerivative_bound (w : ℝ→ᵇℝ) (hw : HasCompactSupport (w : ℝ→ℝ)) (k : ℕ) (z : ℝ) :
    |z^k*w z|≤‖weightedDerivative w hw k‖ := (weightedDerivative w hw k).norm_coe_le_norm z

lemma Jet3.dilation_has1 (g : Jet3) (s t : ℝ) :
    HasDerivAt (fun u => g.f (Real.exp u*s)) (Real.exp t*s*g.d1 (Real.exp t*s)) t := by
  simpa only [Function.comp_def, mul_comm] using (g.has1 (Real.exp t*s)).comp t ((Real.hasDerivAt_exp t).mul_const s)

lemma Jet3.dilation_has2 (g : Jet3) (s t : ℝ) :
    HasDerivAt (fun u => Real.exp u*s*g.d1 (Real.exp u*s))
      (Real.exp t*s*g.d1 (Real.exp t*s)+(Real.exp t*s)^2*g.d2 (Real.exp t*s)) t := by
  have h := ((Real.hasDerivAt_exp t).mul_const s).mul
    ((g.has2 (Real.exp t*s)).comp t ((Real.hasDerivAt_exp t).mul_const s))
  convert h using 1 <;> first | rfl | (simp only [Function.comp_apply]; ring)

lemma Jet3.dilation_remainder (g : Jet3)
    (h1 : HasCompactSupport (g.d1 : ℝ→ℝ)) (h2 : HasCompactSupport (g.d2 : ℝ→ℝ)) (s t : ℝ) :
    |g.f (Real.exp t*s)-g.f s-t*s*g.d1 s|≤
      (‖weightedDerivative g.d1 h1 1‖+‖weightedDerivative g.d2 h2 2‖)*t^2/2 := by
  have hd : deriv (fun u => g.f (Real.exp u*s))=fun u => Real.exp u*s*g.d1 (Real.exp u*s) :=
    funext fun u => (g.dilation_has1 s u).deriv
  have hd2 : iteratedDeriv 2 (fun u => g.f (Real.exp u*s))=
      fun u => Real.exp u*s*g.d1 (Real.exp u*s)+(Real.exp u*s)^2*g.d2 (Real.exp u*s) := by
    rw [iteratedDeriv_succ,iteratedDeriv_one,hd]
    exact funext fun u => (g.dilation_has2 s u).deriv
  have hc : ContDiff ℝ 2 (fun u => g.f (Real.exp u*s)) :=
    (g.contDiff.of_le (by norm_num)).comp (Real.contDiff_exp.mul contDiff_const)
  have ht := first_order_taylor_bound hc _ (fun u => by
    rw [hd2]
    apply (abs_add_le _ _).trans
    simpa only [pow_one] using add_le_add
      (weightedDerivative_bound g.d1 h1 1 (Real.exp u*s)) (weightedDerivative_bound g.d2 h2 2 (Real.exp u*s))) 0 t
  simp only [hd,Real.exp_zero,one_mul,sub_zero] at ht
  convert ht using 1; ring_nf

lemma dilation_lipschitz_bound (w w' : ℝ→ᵇℝ) (hw' : HasCompactSupport (w' : ℝ→ℝ))
    (hd : ∀ x,HasDerivAt (w : ℝ→ℝ) (w' x) x) (s t : ℝ) :
    |w (Real.exp t*s)-w s|≤‖weightedDerivative w' hw' 1‖*|t| := by
  have hh u : HasDerivAt (fun u => w (Real.exp u*s)) (Real.exp u*s*w' (Real.exp u*s)) u := by
    simpa only [Function.comp_def, mul_comm] using (hd (Real.exp u*s)).comp u ((Real.hasDerivAt_exp u).mul_const s)
  have hl := lipschitzWith_of_nnnorm_deriv_le (C:=‖weightedDerivative w' hw' 1‖₊)
    (fun u => (hh u).differentiableAt) (fun u => by
      apply NNReal.coe_le_coe.mp
      rw [coe_nnnorm,Real.norm_eq_abs,(hh u).deriv]
      simpa only [pow_one,coe_nnnorm] using weightedDerivative_bound w' hw' 1 (Real.exp u*s))
  simpa only [Real.dist_eq,sub_zero,Real.exp_zero,one_mul,coe_nnnorm] using hl.dist_le_mul t 0

theorem Jet3.cavity_log_dilation_expansion (g : Jet3)
    (h1 : HasCompactSupport (g.d1 : ℝ→ℝ)) (h2 : HasCompactSupport (g.d2 : ℝ→ℝ))
    (h3 : HasCompactSupport (g.d3 : ℝ→ℝ)) (s t u : ℝ) :
    |g.f (Real.exp t*s+u)-g.f s-t*s*g.d1 s-u*g.d1 s-u^2/2*g.d2 s|≤
      (‖weightedDerivative g.d1 h1 1‖+‖weightedDerivative g.d2 h2 2‖)*t^2/2+
      ‖weightedDerivative g.d2 h2 1‖*|t| * |u|+
      ‖weightedDerivative g.d3 h3 1‖*|t| * u^2/2+‖g.d3‖*|u| ^3/6 := by
  have ht := second_order_taylor_bound g.contDiff ‖g.d3‖ (fun z => by rw [g.deriv3_eq]; exact g.d3.norm_coe_le_norm z)
    (Real.exp t*s) (Real.exp t*s+u)
  simp only [g.deriv_eq,g.deriv2_eq,add_sub_cancel_left] at ht
  have hd := g.dilation_remainder h1 h2 s t
  have h₁ := dilation_lipschitz_bound g.d1 g.d2 h2 g.has2 s t
  have h₂ := dilation_lipschitz_bound g.d2 g.d3 h3 g.has3 s t
  calc
    _ = |(g.f (Real.exp t*s+u)-g.f (Real.exp t*s)-g.d1 (Real.exp t*s)*u-g.d2 (Real.exp t*s)*u^2/2)+
      (g.f (Real.exp t*s)-g.f s-t*s*g.d1 s)+
      (g.d1 (Real.exp t*s)-g.d1 s)*u+(g.d2 (Real.exp t*s)-g.d2 s)*u^2/2| := by congr 1; ring
    _ ≤ |g.f (Real.exp t*s+u)-g.f (Real.exp t*s)-g.d1 (Real.exp t*s)*u-g.d2 (Real.exp t*s)*u^2/2|+
      |g.f (Real.exp t*s)-g.f s-t*s*g.d1 s|+
      |(g.d1 (Real.exp t*s)-g.d1 s)*u|+|(g.d2 (Real.exp t*s)-g.d2 s)*u^2/2| := by
      exact (abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)) le_rfl)
    _ ≤ _ := by
      rw [abs_mul,abs_div,abs_mul,abs_pow,abs_of_nonneg (by norm_num : (0:ℝ)≤2),sq_abs]
      have h₁u := mul_le_mul_of_nonneg_right h₁ (abs_nonneg u)
      have h₂u := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right h₂ (sq_nonneg u)) (by norm_num : (0:ℝ)≤2)
      linarith

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cavity_CavityTaylorFinite
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.bulkFiniteReplicaLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceCountDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceCountKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityIncrementRandomCavityIncrementLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityProxyRandomCavityProxyLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Set
open scoped Topology NNReal ENNReal BigOperators

lemma Jet3.cavity_finite_expansion (g : Jet3)
    (h1 : HasCompactSupport (g.d1 : ℝ→ℝ)) (h2 : HasCompactSupport (g.d2 : ℝ→ℝ))
    (h3 : HasCompactSupport (g.d3 : ℝ→ℝ)) (N L q s v : ℝ)
    (hρ : 0<1-q/(N+L)) :
    |g.f (Real.sqrt (1-q/(N+L))*s+v/Real.sqrt (N+L))-g.f s-
      (v/Real.sqrt N*g.d1 s+q/(2*N)*(g.d2 s-s*g.d1 s)+
        1/(2*N)*g.d2 s*(v^2-q))| ≤ cavityTaylorError g h1 h2 h3 N L q v := by
  let t:=Real.log (Real.sqrt (1-q/(N+L)))
  let u:=v/Real.sqrt (N+L)
  have he : Real.exp t=Real.sqrt (1-q/(N+L)) := Real.exp_log (Real.sqrt_pos.mpr hρ)
  have ht:=g.cavity_log_dilation_expansion h1 h2 h3 s t u
  rw [he] at ht
  have hlin : |(t+q/(2*N))*(s*g.d1 s)|≤|t+q/(2*N)| * ‖weightedDerivative g.d1 h1 1‖ := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (by simpa using weightedDerivative_bound g.d1 h1 1 s) (abs_nonneg _)
  have hshift : |(u-v/Real.sqrt N)*g.d1 s|≤|u-v/Real.sqrt N| * ‖g.d1‖ := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (g.d1.norm_coe_le_norm s) (abs_nonneg _)
  have hquad : |(u^2/2-v^2/(2*N))*g.d2 s|≤|u^2/2-v^2/(2*N)| * ‖g.d2‖ := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (g.d2.norm_coe_le_norm s) (abs_nonneg _)
  calc
    _=|(g.f (Real.sqrt (1-q/(N+L))*s+u)-g.f s-t*s*g.d1 s-u*g.d1 s-u^2/2*g.d2 s)+
      (t+q/(2*N))*(s*g.d1 s)+(u-v/Real.sqrt N)*g.d1 s+
        (u^2/2-v^2/(2*N))*g.d2 s| := by dsimp [u]; congr 1; ring
    _≤|g.f (Real.sqrt (1-q/(N+L))*s+u)-g.f s-t*s*g.d1 s-u*g.d1 s-u^2/2*g.d2 s|+
      |(t+q/(2*N))*(s*g.d1 s)|+|(u-v/Real.sqrt N)*g.d1 s|+
      |(u^2/2-v^2/(2*N))*g.d2 s| := by
      exact (abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans
        (add_le_add (abs_add_le _ _) le_rfl)) le_rfl)
    _≤_ := add_le_add (add_le_add (add_le_add ht hlin) hshift) hquad

theorem cavity_pattern_sum_expansion (n M L : ℕ) (g : Jet3)
    (h1 : HasCompactSupport (g.d1 : ℝ→ℝ)) (h2 : HasCompactSupport (g.d2 : ℝ→ℝ))
    (h3 : HasCompactSupport (g.d3 : ℝ→ℝ))
    (a : Fin M→Fin (n+1)→ℝ) (x : NormalizedSpin (n+1)) (z : Spin L)
    (y : Fin M→Spin L) (hρ : ‖z‖^2<(n+1:ℕ)+L) :
    |(∑ i,g.f (Real.sqrt (1-‖z‖^2/((n+1:ℕ)+L))*(∑ j,a i j*x.val j)+
        inner ℝ z (y i)/Real.sqrt ((n+1:ℕ)+L)))-
      normalizedPatternEnergy (n+1) M g.f a x-
      (cavityLinearField M L (fun i=>g.d1 (∑ j,a i j*x.val j))
          (Real.sqrt (n+1:ℕ))⁻¹ z y+
        ‖z‖^2/2*bulkC (n+1) M g a x+
        cavityQuadraticField M L (fun i=>g.d2 (∑ j,a i j*x.val j))
          (1/(2*(n+1:ℕ))) z y)|≤
      ∑ i,cavityTaylorError g h1 h2 h3 (n+1:ℕ) L (‖z‖^2) (inner ℝ z (y i)) := by
  have hp : (0:ℝ)<((n+1:ℕ):ℝ)+L := by positivity
  have hr : 0<1-‖z‖^2/((n+1:ℕ)+L) := sub_pos.mpr ((div_lt_one hp).mpr hρ)
  have hs:=Finset.sum_le_sum (s:=Finset.univ) (fun i _=>
    g.cavity_finite_expansion h1 h2 h3 (n+1:ℕ) L (‖z‖^2)
      (∑ j,a i j*x.val j) (inner ℝ z (y i)) hr)
  have he : cavityLinearField M L (fun i=>g.d1 (∑ j,a i j*x.val j))
          (Real.sqrt (n+1:ℕ))⁻¹ z y+
        ‖z‖^2/2*bulkC (n+1) M g a x+
        cavityQuadraticField M L (fun i=>g.d2 (∑ j,a i j*x.val j))
          (1/(2*(n+1:ℕ))) z y =
      ∑ i, (inner ℝ z (y i)/Real.sqrt (n+1:ℕ)*g.d1 (∑ j,a i j*x.val j)+
        ‖z‖^2/(2*(n+1:ℕ))*(g.d2 (∑ j,a i j*x.val j)-
          (∑ j,a i j*x.val j)*g.d1 (∑ j,a i j*x.val j))+
        1/(2*(n+1:ℕ))*g.d2 (∑ j,a i j*x.val j)*((inner ℝ z (y i))^2-‖z‖^2)) := by
    unfold cavityLinearField cavityQuadraticField bulkC
    simp only [←mul_assoc,Finset.mul_sum,←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [he]
  unfold normalizedPatternEnergy
  rw [←Finset.sum_sub_distrib,←Finset.sum_sub_distrib]
  exact (Finset.abs_sum_le_sum_abs _ _).trans hs

lemma cavity_log_small {x : ℝ} (hx : 0≤x) (hx' : x≤1/2) :
    |Real.log (1-x)|≤2*x ∧ |Real.log (1-x)+x|≤2*x^2 := by
  have ha : |x|<1 := by rw [abs_of_nonneg hx]; linarith
  have h₀:=Real.abs_log_sub_add_sum_range_le ha 0
  have h₁:=Real.abs_log_sub_add_sum_range_le ha 1
  simp only [Finset.range_zero,Finset.sum_empty,zero_add,pow_one,abs_of_nonneg hx] at h₀
  simp only [Finset.sum_range_succ,Finset.range_zero,Finset.sum_empty,
    zero_add,Nat.cast_zero,pow_one,div_one,abs_of_nonneg hx] at h₁
  constructor
  · apply h₀.trans
    apply (div_le_iff₀ (by linarith : 0<1-x)).mpr
    nlinarith
  · apply (by simpa only [add_comm] using h₁ : |Real.log (1-x)+x|≤x^2/(1-x)).trans
    apply (div_le_iff₀ (by linarith : 0<1-x)).mpr
    nlinarith [mul_nonneg (sq_nonneg x) (show 0≤1-2*x by linarith)]

lemma cavity_scale_log_bounds {N L D q : ℝ} (hN : 0<N) (hL : 0≤L)
    (hD : 0≤D) (hDN : 2*D≤N) (hq : 0≤q) (hqD : q≤D) :
    |Real.log (Real.sqrt (1-q/(N+L)))|≤D/N ∧
    |Real.log (Real.sqrt (1-q/(N+L)))+q/(2*N)|≤(D^2+D*L/2)/N^2 := by
  have hNL : 0<N+L := by linarith
  have hx : 0≤q/(N+L) := div_nonneg hq hNL.le
  have hx' : q/(N+L)≤1/2 := (div_le_iff₀ hNL).mpr (by linarith)
  have hxN : q/(N+L)≤D/N := by
    apply (div_le_div_of_nonneg_right hqD hNL.le).trans
    exact div_le_div_of_nonneg_left hD hN (by linarith)
  have hb:=cavity_log_small hx hx'
  have hp : 0≤1-q/(N+L) := by linarith
  rw [Real.log_sqrt hp]
  constructor
  · rw [abs_div,abs_of_pos (by norm_num : (0:ℝ)<2)]
    exact (div_le_div_of_nonneg_right hb.1 (by norm_num)).trans (by linarith)
  · have he : Real.log (1-q/(N+L))/2+q/(2*N)=
        (Real.log (1-q/(N+L))+q/(N+L))/2+q*L/(2*N*(N+L)) := by
        field_simp
        ring
    rw [he]
    apply (abs_add_le _ _).trans
    rw [abs_div,abs_of_pos (by norm_num : (0:ℝ)<2),abs_of_nonneg (by positivity : 0≤q*L/(2*N*(N+L)))]
    have ht : |Real.log (1-q/(N+L))+q/(N+L)|/2≤(D/N)^2 :=
      (div_le_div_of_nonneg_right hb.2 (by norm_num)).trans (by
        have hh:=pow_le_pow_left₀ hx hxN 2
        nlinarith)
    have hc : q*L/(2*N*(N+L))≤D*L/(2*N^2) := by
      apply (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hqD hL) (by positivity)).trans
      exact div_le_div_of_nonneg_left (mul_nonneg hD hL) (by positivity)
        (by nlinarith)
    calc
      _≤(D/N)^2+D*L/(2*N^2) := add_le_add ht hc
      _=_ := by ring

lemma cavity_inv_sqrt_difference {N L : ℝ} (hN : 0<N) (hL : 0≤L) :
    |(Real.sqrt (N+L))⁻¹-(Real.sqrt N)⁻¹|≤L/(N*Real.sqrt N) := by
  have hNL : 0<N+L := by linarith
  have ha:=Real.sqrt_pos.mpr hN
  have hb:=Real.sqrt_pos.mpr hNL
  have hab : Real.sqrt N≤Real.sqrt (N+L) := Real.sqrt_le_sqrt (by linarith)
  have he : |(Real.sqrt (N+L))⁻¹-(Real.sqrt N)⁻¹|=
      L/(Real.sqrt N*Real.sqrt (N+L)*(Real.sqrt N+Real.sqrt (N+L))) := by
    rw [abs_of_nonpos (sub_nonpos.mpr (inv_anti₀ ha hab))]
    apply (eq_div_iff (by positivity : Real.sqrt N*Real.sqrt (N+L)*(Real.sqrt N+Real.sqrt (N+L))≠0)).mpr
    field_simp
    nlinarith [Real.sq_sqrt hN.le,Real.sq_sqrt hNL.le]
  rw [he]
  apply div_le_div_of_nonneg_left hL (by positivity)
  calc
    N*Real.sqrt N=(Real.sqrt N*Real.sqrt N)*Real.sqrt N := by rw [←pow_two,Real.sq_sqrt hN.le]
    _≤(Real.sqrt N*Real.sqrt (N+L))*(Real.sqrt N+Real.sqrt (N+L)) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hab ha.le) (by linarith) ha.le (by positivity)

lemma cavity_shift_difference {N L v : ℝ} (hN : 0<N) (hL : 0≤L) :
    |v/Real.sqrt (N+L)-v/Real.sqrt N|≤|v| * L/(N*Real.sqrt N) := by
  rw [div_eq_mul_inv,div_eq_mul_inv,←mul_sub,abs_mul]
  simpa only [mul_div_assoc] using
    mul_le_mul_of_nonneg_left (cavity_inv_sqrt_difference hN hL) (abs_nonneg v)

lemma cavity_square_shift_difference {N L v : ℝ} (hN : 0<N) (hL : 0≤L) :
    |(v/Real.sqrt (N+L))^2/2-v^2/(2*N)|≤v^2*L/(2*N^2) := by
  have hNL : 0<N+L := by linarith
  rw [div_pow,Real.sq_sqrt hNL.le]
  have he : v^2/(N+L)/2-v^2/(2*N)= -(v^2*L/(2*N*(N+L))) := by field_simp; ring
  rw [he,abs_neg,abs_of_nonneg (by positivity)]
  exact div_le_div_of_nonneg_left (by positivity) (by positivity) (by nlinarith)

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cavity_CavityUniformRemainder
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.bulkFiniteReplicaLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceCountDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceCountKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityIncrementRandomCavityIncrementLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityProxyRandomCavityProxyLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators
namespace SphericalPerceptronFreeEnergy

lemma cavityTaylorError_le_majorant (g : Jet3)
    (h1 : HasCompactSupport (g.d1 : ℝ→ℝ)) (h2 : HasCompactSupport (g.d2 : ℝ→ℝ))
    (h3 : HasCompactSupport (g.d3 : ℝ→ℝ)) {N L D q v u : ℝ}
    (hN : 0<N) (hL : 0≤L) (hD : 0≤D) (hDN : 2*D≤N)
    (hq : 0≤q) (hqD : q≤D) (hu : 0≤u) (hv : |v|≤Real.sqrt D*u) :
    cavityTaylorError g h1 h2 h3 N L q v≤
      cavityRemainderMajorant (cavityRemainderCoefficients g h1 h2 h3 L D) N u := by
  have hsN:=Real.sqrt_pos.mpr hN
  have hsNL : 0<Real.sqrt (N+L) := Real.sqrt_pos.mpr (by linarith)
  have hs : Real.sqrt N≤Real.sqrt (N+L) := Real.sqrt_le_sqrt (by linarith)
  have hlog:=cavity_scale_log_bounds hN hL hD hDN hq hqD
  have hshift:=cavity_shift_difference (v:=v) hN hL
  have hsq:=cavity_square_shift_difference (v:=v) hN hL
  have hv2 : v^2≤D*u^2 := by
    have hh:=pow_le_pow_left₀ (abs_nonneg v) hv 2
    simpa only [sq_abs,mul_pow,Real.sq_sqrt hD] using hh
  have hscaled : |v/Real.sqrt (N+L)|≤Real.sqrt D*u/Real.sqrt N := by
    rw [abs_div,abs_of_pos hsNL]
    exact (div_le_div_of_nonneg_right hv hsNL.le).trans
      (div_le_div_of_nonneg_left (by positivity) hsN hs)
  have ht2 : (Real.log (Real.sqrt (1-q/(N+L))))^2≤(D/N)^2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) hlog.1 2
  have hu2 : (v/Real.sqrt (N+L))^2≤D*u^2/N := by
    rw [div_pow,Real.sq_sqrt (by linarith : 0≤N+L)]
    exact (div_le_div_of_nonneg_right hv2 (by linarith)).trans
      (div_le_div_of_nonneg_left (by positivity) hN (by linarith))
  have h1':=div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left ht2 (by positivity : 0≤‖weightedDerivative g.d1 h1 1‖+‖weightedDerivative g.d2 h2 2‖))
    (by norm_num : (0:ℝ)≤2)
  have h2':=mul_le_mul_of_nonneg_left (mul_le_mul hlog.1 hscaled (abs_nonneg _) (by positivity))
    (norm_nonneg (weightedDerivative g.d2 h2 1))
  have h3':=div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left (mul_le_mul hlog.1 hu2 (sq_nonneg _) (by positivity))
      (norm_nonneg (weightedDerivative g.d3 h3 1))) (by norm_num : (0:ℝ)≤2)
  have h4':=div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg _) hscaled 3) (norm_nonneg g.d3))
    (by norm_num : (0:ℝ)≤6)
  have h5':=mul_le_mul_of_nonneg_right hlog.2 (norm_nonneg (weightedDerivative g.d1 h1 1))
  have h6':=mul_le_mul_of_nonneg_right (hshift.trans
    (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hv hL) (by positivity))) (norm_nonneg g.d1)
  have h7':=mul_le_mul_of_nonneg_right (hsq.trans
    (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hv2 hL) (by positivity))) (norm_nonneg g.d2)
  have ht:=add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add h1' h2') h3') h4') h5') h6') h7'
  simp only [mul_assoc] at ht
  dsimp only [cavityTaylorError]
  simp only [mul_assoc]
  apply ht.trans_eq
  dsimp [cavityRemainderMajorant,cavityRemainderCoefficients]
  simp only [div_pow]
  rw [show (Real.sqrt N)^3=N*Real.sqrt N by
    rw [pow_succ,Real.sq_sqrt hN.le]]
  field_simp
  ring

lemma cavityTaylorError_inner_le (g : Jet3)
    (h1 : HasCompactSupport (g.d1 : ℝ→ℝ)) (h2 : HasCompactSupport (g.d2 : ℝ→ℝ))
    (h3 : HasCompactSupport (g.d3 : ℝ→ℝ)) {N D : ℝ} (L : ℕ)
    (hN : 0<N) (hD : 0≤D) (hDN : 2*D≤N) (z y : Spin L) (hz : ‖z‖^2≤D) :
    cavityTaylorError g h1 h2 h3 N L (‖z‖^2) (inner ℝ z y)≤
      cavityRemainderMajorant (cavityRemainderCoefficients g h1 h2 h3 L D) N ‖y‖ := by
  apply cavityTaylorError_le_majorant g h1 h2 h3 hN (Nat.cast_nonneg _) hD hDN
    (sq_nonneg _) hz (norm_nonneg _)
  exact (abs_real_inner_le_norm _ _).trans
    (mul_le_mul_of_nonneg_right ((Real.le_sqrt (norm_nonneg _) hD).mpr hz) (norm_nonneg _))


lemma cavityNormMoment_integrable (L p : ℕ) :
    Integrable (fun y : Spin L=>‖y‖^p) (stdGaussian (Spin L)) := by
  simpa only [id_eq] using
    (IsGaussian.memLp_id (stdGaussian (Spin L)) (p:ℝ≥0∞) (by simp)).integrable_norm_pow'

lemma cavityRemainderMajorant_integrable (L : ℕ) (c : Fin 4→ℝ) (N : ℝ) :
    Integrable (fun y : Spin L=>cavityRemainderMajorant c N ‖y‖) (stdGaussian (Spin L)) := by
  have h1 : Integrable (fun y : Spin L=>‖y‖) (stdGaussian (Spin L)) := by
    simpa using cavityNormMoment_integrable L 1
  exact (((integrable_const (c 0/N^2)).add ((h1.const_mul (c 1)).div_const _)).add
    (((cavityNormMoment_integrable L 2).const_mul (c 2)).div_const _)).add
    (((cavityNormMoment_integrable L 3).const_mul (c 3)).div_const _)

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cavity_CavityShellExpansion
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceCountDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceCountKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityIncrementRandomCavityIncrementLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityProxyRandomCavityProxyLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology BigOperators BoundedContinuousFunction

lemma cavityJoinedPatterns_projection (N L M : ℕ) (a : Fin M→Fin N→ℝ)
    (y : Fin M→Spin L) (x : NormalizedSpin N) (z : Spin L) (i : Fin M) :
    (∑ j,cavityJoinedPatterns N L M a y i j*cavityNormalizedVec N L x z j)=
      cavityRho N L z*(∑ j,a i j*x.val j)+inner ℝ z (y i)/Real.sqrt (N+L:ℕ) := by
  rw [Fin.sum_univ_add]
  simp only [cavityJoinedPatterns,cavityNormalizedVec,gaussianBlockJoin,PiLp.toLp_apply,
    Fin.addCases_left,Fin.addCases_right,PiLp.smul_apply,smul_eq_mul]
  simp only [EuclideanSpace.inner_eq_star_dotProduct,dotProduct,star_trivial]
  rw [Finset.mul_sum,Finset.sum_div]
  apply congrArg₂ (·+·)
  · apply Finset.sum_congr rfl
    intro j _hj
    ring
  · apply Finset.sum_congr rfl
    intro j _hj
    ring

lemma cavityShellPatternEnergy_join (n L M : ℕ) (f : ℝ→ᵇℝ)
    (a : Fin M→Fin (n+1)→ℝ) (y : Fin M→Spin L) (s : CavityShellSpin n L) :
    cavityShellPatternEnergy n L M f (cavityJoinedPatterns (n+1) L M a y) s=
      ∑ i,f (Real.sqrt (1-‖s.2.val‖^2/((n+1:ℕ)+L))*(∑ j,a i j*s.1.val j)+
        inner ℝ s.2.val (y i)/Real.sqrt ((n+1:ℕ)+L)) := by
  unfold cavityShellPatternEnergy normalizedPatternEnergy
  apply Finset.sum_congr rfl
  intro i _hi
  congr 1
  change (∑ j,cavityJoinedPatterns (n+1) L M a y i j*cavityNormalizedVec (n+1) L s.1 s.2.val j)=_
  rw [cavityJoinedPatterns_projection]
  simp only [cavityRho,Nat.cast_add]

theorem cavity_true_shell_expansion (n L M : ℕ) (f : Jet3)
    (h1 : HasCompactSupport (f.d1 : ℝ→ℝ)) (h2 : HasCompactSupport (f.d2 : ℝ→ℝ))
    (h3 : HasCompactSupport (f.d3 : ℝ→ℝ)) (hn : 2*(L+1)≤n+1)
    (a : Fin M→Fin (n+1)→ℝ) (y : Fin M→Spin L) (s : CavityShellSpin n L) :
    |cavityShellPatternEnergy n L M f.f (cavityJoinedPatterns (n+1) L M a y) s-
      cavityShellTaylorModel n L M f a y s|≤
      ∑ i,cavityRemainderMajorant (cavityRemainderCoefficients f h1 h2 h3 L (L+1)) (n+1:ℕ) ‖y i‖ := by
  have hnR : (2:ℝ)*((L:ℝ)+1)≤(n+1:ℕ) := by exact_mod_cast hn
  have hz : ‖s.2.val‖^2≤(L:ℝ)+1:=s.2.prop.2
  have hρ : ‖s.2.val‖^2<(n+1:ℕ)+L := by nlinarith [Nat.cast_nonneg (α:=ℝ) L]
  rw [cavityShellPatternEnergy_join]
  change |(∑ i,_) - (_+_)|≤_
  rw [←sub_sub]
  exact (cavity_pattern_sum_expansion n M L f h1 h2 h3 a s.1 s.2.val y hρ).trans
    (Finset.sum_le_sum fun i _hi=>cavityTaylorError_inner_le f h1 h2 h3 L (by positivity)
      (by positivity) hnR s.2.val (y i) hz)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma gaussianRows_basis (n : ℕ) (σ : ℝ) (y : Spin (n+1)) :
    gaussianRows (fun i : Fin (n+1)=>σ • EuclideanSpace.single i (1:ℝ)) y=σ •y := by
  ext i
  simp [gaussianRows_apply,real_inner_smul_left,EuclideanSpace.inner_single_left]

lemma gaussianRows_isotropic_law (n : ℕ) (v : Fin (n+1)→E) {b : ℝ} (hb : 0≤b)
    (hv : ∀ i j,inner ℝ (v i) (v j)=if i=j then b else 0) :
    (stdGaussian E).map (gaussianRows v)=
      (stdGaussian (Spin (n+1))).map (fun y=>Real.sqrt b •y) := by
  have hg : Matrix.gram ℝ v=Matrix.gram ℝ (fun i : Fin (n+1)=>Real.sqrt b • EuclideanSpace.single i (1:ℝ)) := by
    ext i j
    simp only [Matrix.gram_apply,hv,inner_smul_left,inner_smul_right,conj_trivial]
    by_cases h : i=j
    · subst j
      simp [Real.sq_sqrt hb,←pow_two]
    · simp [EuclideanSpace.inner_single_left,h]
  rw [gaussianRows_map_stdGaussian,hg,←gaussianRows_map_stdGaussian]
  congr 1
  funext y
  exact gaussianRows_basis n (Real.sqrt b) y

lemma gaussianRows_spherical_average (n : ℕ) (v : Fin (n+1)→E) {b : ℝ} (hb : 0≤b)
    (hv : ∀ i j,inner ℝ (v i) (v j)=if i=j then b else 0) (R : ℝ) :
    (∫ g,sphericalExp n (gaussianRows v g) R ∂stdGaussian E)=Real.exp (R^2*b/2) := by
  rw [←integral_map (gaussianRows v).measurable.aemeasurable
    (sphericalExp_continuous n R).aestronglyMeasurable,gaussianRows_isotropic_law n v hb hv,
    integral_map (by fun_prop) (sphericalExp_continuous n R).aestronglyMeasurable]
  have h:=sphericalExp_gaussian_average n R (Real.sqrt b) 0
  have hz : sphericalExp n 0 R=1 := by simp [sphericalExp]
  simpa only [zero_add,Real.sq_sqrt hb,hz,mul_one] using h

lemma gaussianRows_spherical_memLp (n : ℕ) (v : Fin (n+1)→E) {b : ℝ} (hb : 0≤b)
    (hv : ∀ i j,inner ℝ (v i) (v j)=if i=j then b else 0) (R : ℝ) :
    MemLp (fun g=>sphericalExp n (gaussianRows v g) R) 2 (stdGaussian E) := by
  have hm := (sphericalExp_continuous n R).comp (gaussianRows v).continuous
  apply (memLp_two_iff_integrable_sq hm.aestronglyMeasurable).mpr
  have hi : Integrable (fun g=>sphericalExp n (gaussianRows v g) (2*R)) (stdGaussian E) := by
    by_contra hn
    have h:=gaussianRows_spherical_average n v hb hv (2*R)
    rw [integral_undef hn] at h
    exact (Real.exp_pos _).ne' h.symm
  apply hi.mono' (hm.pow 2).aestronglyMeasurable
  filter_upwards [] with g
  rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
  exact sphericalExp_square_le n R _

lemma gaussianRows_spherical_second (n : ℕ) (v : Fin (n+1)→E) {b : ℝ} (hb : 0≤b)
    (hv : ∀ i j,inner ℝ (v i) (v j)=if i=j then b else 0) (R : ℝ) :
    (∫ g,sphericalExp n (gaussianRows v g) R^2 ∂stdGaussian E)≤Real.exp (2*R^2*b) := by
  have hs := (memLp_two_iff_integrable_sq
    ((gaussianRows_spherical_memLp n v hb hv R).aestronglyMeasurable)).mp
    (gaussianRows_spherical_memLp n v hb hv R)
  have hi := (gaussianRows_spherical_memLp n v hb hv (2*R)).integrable (by norm_num)
  apply (integral_mono hs hi (fun g=>sphericalExp_square_le n R _)).trans_eq
  rw [gaussianRows_spherical_average n v hb hv]
  congr 1
  ring
end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cavity_CavityMeanCap
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceCountDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceCountKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityIncrementRandomCavityIncrementLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityProxyRandomCavityProxyLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Set
open scoped Topology BigOperators BoundedContinuousFunction

lemma cavity_expected_cap {S G : Type*} [MeasurableSpace S] [MeasurableSpace G]
    (μ : Measure S) (P : Measure G) [IsProbabilityMeasure μ] [IsProbabilityMeasure P]
    (W F : G×S→ℝ) (hW : Measurable W) (hF : Measurable F) {C Λ K : ℝ}
    (hWC : ∀ p,|W p|≤C) (hF1 : ∀ p,1≤F p) (hΛ : 1≤Λ)
    (hFx : ∀ g,MemLp (fun x=>F (g,x)) 2 μ)
    (hFg : ∀ x,MemLp (fun g=>F (g,x)) 2 P)
    (h2 : ∀ x,(∫ g,F (g,x)^2 ∂P)≤K) :
    let D:=fun g=>Real.log (∫ x,Real.exp (W (g,x))*F (g,x) ∂μ)-
      Real.log (∫ x,Real.exp (W (g,x))*min (F (g,x)) Λ ∂μ)
    Integrable D P ∧ 0≤∫ g,D g ∂P ∧
      (∫ g,D g ∂P)≤Real.exp (2*C)/Λ*K := by
  let Q : S×G→ℝ := fun p=>F (p.2,p.1)^2
  have hQ : Measurable Q := (hF.comp measurable_swap).pow_const 2
  have hi : Integrable Q (μ.prod P) := by
    apply (integrable_prod_iff hQ.aestronglyMeasurable).mpr
    constructor
    · exact ae_of_all _ fun x=>(memLp_two_iff_integrable_sq (hFg x).aestronglyMeasurable).mp (hFg x)
    · apply Integrable.of_bound (hQ.norm.stronglyMeasurable.integral_prod_right).aestronglyMeasurable K
      filter_upwards [] with x
      have he : (∫ g,‖Q (x,g)‖ ∂P)=(∫ g,F (g,x)^2 ∂P) := by
        simp only [Q,Real.norm_eq_abs,abs_sq]
      rw [he,Real.norm_eq_abs,abs_of_nonneg (integral_nonneg fun g=>sq_nonneg _)]
      exact h2 x
  have hS : Integrable (fun g=>∫ x,F (g,x)^2 ∂μ) P := hi.integral_prod_right
  have hB : (∫ g,∫ x,F (g,x)^2 ∂μ ∂P)≤K := by
    rw [←integral_integral_swap hi]
    calc
      _≤∫ _ : S,K ∂μ := integral_mono hi.integral_prod_left (integrable_const _) h2
      _=K := by simp
  let D:=fun g=>Real.log (∫ x,Real.exp (W (g,x))*F (g,x) ∂μ)-
    Real.log (∫ x,Real.exp (W (g,x))*min (F (g,x)) Λ ∂μ)
  have hD : Measurable D := by
    exact ((hW.exp.mul hF).stronglyMeasurable.integral_prod_right.measurable.log).sub
      ((hW.exp.mul (hF.min measurable_const)).stronglyMeasurable.integral_prod_right.measurable.log)
  have hp g : 0≤D g ∧ D g≤Real.exp (2*C)/Λ*(∫ x,F (g,x)^2 ∂μ) :=
    cavity_capped_log_bound μ (hW.comp (measurable_const.prodMk measurable_id)) (fun x=>hWC (g,x)) (hFx g) (fun x=>hF1 (g,x)) hΛ
  have hc : 0≤Real.exp (2*C)/Λ := div_nonneg (Real.exp_pos _).le ((by norm_num : (0:ℝ)≤1).trans hΛ)
  have hDi : Integrable D P := by
    apply (hS.const_mul (Real.exp (2*C)/Λ)).mono' hD.aestronglyMeasurable
    exact ae_of_all _ fun g=>by simpa only [Real.norm_eq_abs,abs_of_nonneg (hp g).1] using (hp g).2
  refine ⟨hDi,integral_nonneg (fun g=>(hp g).1),?_⟩
  calc
    _≤∫ g,Real.exp (2*C)/Λ*(∫ x,F (g,x)^2 ∂μ) ∂P :=
      integral_mono hDi (hS.const_mul _) (fun g=>(hp g).2)
    _=Real.exp (2*C)/Λ*(∫ g,∫ x,F (g,x)^2 ∂μ ∂P) := integral_const_mul _ _
    _≤_ := mul_le_mul_of_nonneg_left hB hc

lemma cavity_rows_joint_continuous {A J E : Type*} [TopologicalSpace A]
    [Fintype J] [DecidableEq J] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {v : A→J→E} {y : A→E} (hv : Continuous v) (hy : Continuous y) :
    Continuous (fun a=>gaussianRows (v a) (y a)) := by
  change Continuous (fun a=>WithLp.toLp 2 (fun i=>inner ℝ (v a i) (y a)))
  apply (PiLp.continuous_toLp 2 _).comp
  exact continuous_pi fun i=>((continuous_apply i).comp hv).inner hy

lemma cavityBulkFeature_continuous (n d m M : ℕ) (f : Jet3) (a : BulkDisorder (m+1) M) :
    Continuous (cavityBulkFeature n d m M f a) := by
  apply continuous_pi
  intro j
  unfold cavityBulkFeature
  apply (PiLp.continuous_toLp 2 _).comp
  apply continuous_pi
  intro p
  split_ifs
  · cases j <;> cases p.2 <;> dsimp [cavityBulkBase] <;> fun_prop
  · exact continuous_const

lemma cavityBulk_full_vector_second (n d m M : ℕ) (f : Jet3) (a : BulkDisorder (m+1) M)
    (x : NormalizedSpin (m+1)) (K : ℝ) (hK : M/(m+1:ℕ)*‖f.d1‖^2≤K) :
    MemLp (fun y=>sphericalExp n
      (gaussianRows (fun i=>cavityBulkFeature n d m M f a x (Sum.inl i)) y)
      (Real.sqrt (n+1:ℕ))) 2 (stdGaussian (EuclideanSpace ℝ (CavityBulkNoiseIndex n d m M))) ∧
    (∫ y,sphericalExp n
      (gaussianRows (fun i=>cavityBulkFeature n d m M f a x (Sum.inl i)) y)
      (Real.sqrt (n+1:ℕ))^2 ∂stdGaussian (EuclideanSpace ℝ (CavityBulkNoiseIndex n d m M)))≤
      Real.exp (2*(n+1:ℕ)*K) := by
  let w := fun i : Fin (n+1)=>cavityBulkFeature n d m M f a x (Sum.inl i)
  have hw i j : inner ℝ (w i) (w j)=if i=j then bulkB (m+1) M f a.1 x x else 0 := by
    simp only [w,cavityBulkFeature_inner,Sum.inl.injEq,Sum.elim_inl]
  have hb : 0≤bulkB (m+1) M f a.1 x x := by
    have hh : 0 ≤ inner ℝ (w 0) (w 0) := real_inner_self_nonneg
    rwa [hw,ite_eq_left rfl] at hh
  refine ⟨gaussianRows_spherical_memLp n w hb hw _,?_⟩
  apply (gaussianRows_spherical_second n w hb hw _).trans
  apply Real.exp_le_exp.mpr
  rw [Real.sq_sqrt (by positivity : 0≤((n+1:ℕ):ℝ))]
  exact mul_le_mul_of_nonneg_left
    ((le_abs_self _).trans ((bulkB_bound _ _ _ _ _ _).trans hK)) (by positivity)

lemma cavityBulk_unclipped_cap (n d m M : ℕ) (f : Jet3) (v : ℕ→ℝ)
    (Λ : ℝ) (hΛ : 1≤Λ) (K KC : ℝ)
    (hK : M/(m+1:ℕ)*‖f.d1‖^2≤K)
    (hC : ∀ (a : BulkDisorder (m+1) M) x,|bulkC (m+1) M f a.1 x|≤KC)
    (a : BulkDisorder (m+1) M) :
    let D:=fun y=>Real.log (cavityBulkFullCompPartition n d m M f v (a,y))-
      Real.log (cavityBulkCompPartition n d m M f v Λ hΛ (a,y))
    Integrable D (stdGaussian (EuclideanSpace ℝ (CavityBulkNoiseIndex n d m M))) ∧
      (∀ y,0≤D y) ∧ 0≤∫ y,D y ∂stdGaussian (EuclideanSpace ℝ (CavityBulkNoiseIndex n d m M)) ∧
      (∫ y,D y ∂stdGaussian (EuclideanSpace ℝ (CavityBulkNoiseIndex n d m M)))≤
        Real.exp (2*((n+1:ℕ)/2*KC+(d:ℝ)*‖f.f‖)+2*(n+1:ℕ)*K)/Λ := by
  let E:=EuclideanSpace ℝ (CavityBulkNoiseIndex n d m M)
  let μ:=tiltLaw (unitSphereLaw (m+1)) (bulkGibbsHamiltonian m M f.f v a) 1
  have he : Integrable (fun x=>Real.exp (1*bulkGibbsHamiltonian m M f.f v a x)) (unitSphereLaw (m+1)) := by
    simpa only [one_mul,bulkGibbsHamiltonian] using bulkHamiltonian_exp_integrable m M f.f v a
  let : IsProbabilityMeasure μ := tilt_law_probability_of_integrable _ he
  let w:=fun x i=>cavityBulkFeature n d m M f a x (Sum.inl i)
  let F : E×NormalizedSpin (m+1)→ℝ:=fun p=>sphericalExp n (gaussianRows (w p.2) p.1) (Real.sqrt (n+1:ℕ))
  let W : E×NormalizedSpin (m+1)→ℝ:=fun p=>(n+1:ℕ)/2*bulkC (m+1) M f a.1 p.2+
    ∑ t : Fin d,f.f (inner ℝ (cavityBulkFeature n d m M f a p.2 (Sum.inr t)) p.1)
  have hw : Continuous w := by
    apply continuous_pi
    intro i
    exact (continuous_apply (Sum.inl i)).comp (cavityBulkFeature_continuous n d m M f a)
  have hFr : Continuous (fun p : E×NormalizedSpin (m+1)=>gaussianRows (w p.2) p.1) :=
    cavity_rows_joint_continuous (hw.comp continuous_snd) continuous_fst
  have hF : Continuous F := (sphericalExp_continuous n _).comp hFr
  have hW : Measurable W := by
    unfold W bulkC
    have hc:=cavityBulkFeature_continuous n d m M f a
    fun_prop
  have hWC p : |W p|≤(n+1:ℕ)/2*KC+(d:ℝ)*‖f.f‖ := by
    calc
      _≤|(n+1:ℕ)/2*bulkC (m+1) M f a.1 p.2|+
        |∑ t : Fin d,f.f (inner ℝ (cavityBulkFeature n d m M f a p.2 (Sum.inr t)) p.1)| := abs_add_le _ _
      _≤(n+1:ℕ)/2*KC+∑ _ : Fin d,‖f.f‖ := by
        apply add_le_add
        · rw [abs_mul,abs_of_nonneg (by positivity : 0≤((n+1:ℕ):ℝ)/2)]
          exact mul_le_mul_of_nonneg_left (hC a p.2) (by positivity)
        · exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun t ht=>f.f.norm_coe_le_norm _)
      _=_ := by simp
  have hFx y : MemLp (fun x=>F (y,x)) 2 μ :=
    (hF.comp (continuous_const.prodMk continuous_id)).memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hfg x:=cavityBulk_full_vector_second n d m M f a x K hK
  have hc:=cavity_expected_cap μ (stdGaussian E) W F hW hF.measurable hWC
    (fun p=>one_le_sphericalExp n _ _) hΛ hFx (fun x=>(hfg x).1) (fun x=>(hfg x).2)
  have hH:=(bulkGibbsHamiltonian_measurable m M f.f v).of_uncurry_left (x:=a)
  have hfull y : (∫ x,Real.exp (W (y,x))*F (y,x) ∂μ)=cavityBulkFullCompPartition n d m M f v (a,y) :=
    tilt_law_integral_of_integrable _ hH he
  have hcap y : (∫ x,Real.exp (W (y,x))*min (F (y,x)) Λ ∂μ)=cavityBulkCompPartition n d m M f v Λ hΛ (a,y) := by
    rw [tilt_law_integral_of_integrable _ hH he]
    unfold cavityBulkCompPartition
    congr 1
    funext x
    simp only [W,F,w,cavitySingleTest_apply,gaussianRows_apply,Real.exp_add,Real.exp_sum]
    change Real.exp _ * (∏ t, _) * min (sphericalExp n (WithLp.toLp 2 _) _) Λ = _
    ring_nf
    rfl
  have hp y:=cavity_capped_log_bound μ
    (hW.comp (measurable_const.prodMk measurable_id)) (fun x=>hWC (y,x))
    (hFx y) (fun x=>one_le_sphericalExp n _ _) hΛ
  dsimp only [Function.comp_apply,id_eq] at hc hp ⊢
  simp_rw [hfull,hcap] at hc hp
  refine ⟨hc.1,fun y=>(hp y).1,hc.2.1,hc.2.2.trans_eq ?_⟩
  rw [Real.exp_add]
  ring

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cavity_CavityAnnealedUncap
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceCountDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceCountKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityIncrementRandomCavityIncrementLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityProxyRandomCavityProxyLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped Topology BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

lemma cavity_comp_partition_unbounded_measurable {A S J E : Type*}
    [MeasurableSpace A] [MeasurableSpace S] [Fintype J] [DecidableEq J]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure S) [SFinite μ]
    (v : A→S→J→E) (hv : Measurable (Function.uncurry v))
    (H C : A→S→ℝ) (hH : Measurable (Function.uncurry H))
    (hC : Measurable (Function.uncurry C)) (t : ℝ) (Ψ : EuclideanSpace ℝ J→ℝ)
    (hΨ : Measurable Ψ) :
    Measurable (fun p : A×E=>tiltMean μ (H p.1)
      (fun x=>Real.exp (t*C p.1 x)*Ψ (gaussianRows (v p.1 x) p.2)) 1) := by
  let κ : Kernel (A×E) S := Kernel.const _ μ
  have hproj : Measurable (fun p : (A×E)×S=>(p.1.1,p.2)) :=
    measurable_fst.fst.prodMk measurable_snd
  apply kernel_tiltMean_measurable κ (H := fun p x=>H p.1 x)
    (Y := fun p x=>Real.exp (t*C p.1 x)*Ψ (gaussianRows (v p.1 x) p.2)) (hH.comp hproj)
  exact ((hC.comp hproj).const_mul t).exp.mul
    (hΨ.comp (cavity_rows_joint_measurable (hv.comp hproj) measurable_fst.snd))

lemma cavityFullSingleTest_measurable (n d : ℕ) (f : ℝ→ᵇℝ) :
    Measurable (fun z : EuclideanSpace ℝ (Fin (n+1)⊕Fin d)=>
      Real.exp (∑ t,f (z (Sum.inr t)))*
        sphericalExp n (WithLp.toLp 2 (fun i=>z (Sum.inl i))) (Real.sqrt (n+1:ℕ))) := by
  apply Measurable.mul (by fun_prop)
  apply (sphericalExp_continuous n _).measurable.comp
  fun_prop

lemma cavityBulkFullCompPartition_measurable (n d m M : ℕ) (f : Jet3) (v : ℕ→ℝ) :
    Measurable (cavityBulkFullCompPartition n d m M f v) := by
  have h:=cavity_comp_partition_unbounded_measurable (unitSphereLaw (m+1))
    (cavityBulkFeature n d m M f) (cavityBulkFeature_measurable n d m M f)
    (bulkGibbsHamiltonian m M f.f v) (fun a x=>bulkC (m+1) M f a.1 x)
    (bulkGibbsHamiltonian_measurable m M f.f v) (bulkC_measurable m M f) ((n+1:ℕ)/2)
    _ (cavityFullSingleTest_measurable n d f.f)
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  funext p
  unfold cavityBulkFullCompPartition
  congr 1
  funext x
  simp only [Real.exp_add,gaussianRows_apply]
  rw [mul_assoc]
  rfl

lemma cavityBulkUncapError_measurable (n d m M : ℕ) (f : Jet3) (v : ℕ→ℝ)
    (Λ : ℝ) (hΛ : 1≤Λ) : Measurable (cavityBulkUncapError n d m M f v Λ hΛ) :=
  (cavityBulkFullCompPartition_measurable n d m M f v).log.sub
    (cavityBulkCompPartition_measurable n d m M f v Λ hΛ).log

theorem cavityBulk_uncap_annealed (n d m M : ℕ) (f : Jet3) (v : ℕ→ℝ)
    (Λ : ℝ) (hΛ : 1≤Λ) (K KC : ℝ)
    (hK : M/(m+1:ℕ)*‖f.d1‖^2≤K)
    (hC : ∀ (a : BulkDisorder (m+1) M) x,|bulkC (m+1) M f a.1 x|≤KC) :
    let D:=cavityBulkUncapError n d m M f v Λ hΛ
    let P:=(bulkDisorderLaw (m+1) M).prod (stdGaussian (EuclideanSpace ℝ (CavityBulkNoiseIndex n d m M)))
    Integrable D P ∧ 0≤∫ p,D p ∂P ∧ (∫ p,D p ∂P)≤
      Real.exp (2*((n+1:ℕ)/2*KC+(d:ℝ)*‖f.f‖)+2*(n+1:ℕ)*K)/Λ := by
  let D:=cavityBulkUncapError n d m M f v Λ hΛ
  let E:=EuclideanSpace ℝ (CavityBulkNoiseIndex n d m M)
  let B:=Real.exp (2*((n+1:ℕ)/2*KC+(d:ℝ)*‖f.f‖)+2*(n+1:ℕ)*K)/Λ
  have hsec a:=cavityBulk_unclipped_cap n d m M f v Λ hΛ K KC hK hC a
  have hD : Measurable D:=cavityBulkUncapError_measurable n d m M f v Λ hΛ
  have hnorm a : (∫ y,‖D (a,y)‖ ∂stdGaussian E)=∫ y,D (a,y) ∂stdGaussian E := by
    apply integral_congr_ae
    exact ae_of_all _ fun y=>by
      change ‖D (a,y)‖=D (a,y)
      exact Real.norm_of_nonneg ((hsec a).2.1 y)
  have hi : Integrable D ((bulkDisorderLaw (m+1) M).prod (stdGaussian E)) := by
    apply (integrable_prod_iff hD.aestronglyMeasurable).mpr
    constructor
    · exact ae_of_all _ fun a=>(hsec a).1
    · apply Integrable.of_bound (hD.norm.stronglyMeasurable.integral_prod_right).aestronglyMeasurable B
      filter_upwards [] with a
      rw [hnorm,Real.norm_eq_abs]
      have hp : 0≤∫ y,D (a,y) ∂stdGaussian E := (hsec a).2.2.1
      rw [abs_of_nonneg hp]
      exact (hsec a).2.2.2
  refine ⟨hi,integral_nonneg (fun p=>(hsec p.1).2.1 p.2),?_⟩
  rw [integral_prod _ hi]
  calc
    _≤∫ _ : BulkDisorder (m+1) M,B ∂bulkDisorderLaw (m+1) M :=
      integral_mono hi.integral_prod_left (integrable_const B) (fun a=>(hsec a).2.2.2)
    _=B := by simp

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cavity_CavityBlockProduct
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.bulkFiniteReplicaLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.bulkSpinKernel_markov _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.enrichedIndexedBaseMeasure_probability _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceBaseDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceSpinLeafKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceCountDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceCountKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityIncrementRandomCavityIncrementLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityProxyRandomCavityProxyLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped Topology ENNReal NNReal
namespace SphericalPerceptronFreeEnergy

lemma cavityUnitEmbed_measurable (n L : ℕ) : Measurable (cavityUnitEmbed n L) := by
  unfold cavityUnitEmbed
  fun_prop

lemma cavity_radial_rho {r b : ℝ} (hr : 0 < r) (_hb : 0≤b) :
    Real.sqrt (1-((Real.sqrt (r^2+b^2))⁻¹*b)^2)=(Real.sqrt (r^2+b^2))⁻¹*r := by
  have hs : 0<Real.sqrt (r^2+b^2) := Real.sqrt_pos.mpr (by positivity)
  have hs2:=Real.sq_sqrt (show 0 ≤ r^2+b^2 by positivity)
  have hsum : ((Real.sqrt (r^2+b^2))⁻¹*r)^2+((Real.sqrt (r^2+b^2))⁻¹*b)^2=1 := by
    field_simp
    nlinarith
  rw [show 1-((Real.sqrt (r^2+b^2))⁻¹*b)^2=((Real.sqrt (r^2+b^2))⁻¹*r)^2 by linarith,
    Real.sqrt_sq (by positivity)]

lemma cavityRadialBlock_unitEmbed (n L : ℕ)
    (p : (Ioi (0:ℝ)×Metric.sphere (0:Spin (n+1)) 1)×Spin L) :
    cavityRadialBlock n L p=cavityUnitEmbed n L (p.1.2,cavityRadialUnit n L (p.1.1,p.2)) := by
  have ha : 0≤(Real.sqrt (p.1.1.val^2+‖p.2‖^2))⁻¹ := by positivity
  unfold cavityRadialBlock cavityUnitEmbed cavityRadialUnit
  rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg ha,cavity_radial_rho p.1.1.prop (norm_nonneg p.2)]

lemma cavityRadial_reorder_preserving (n L : ℕ) :
    MeasurePreserving (fun p : (Ioi (0:ℝ)×Metric.sphere (0:Spin (n+1)) 1)×Spin L=>(p.1.2,(p.1.1,p.2)))
      (((gaussianRadiusLaw n).prod (unitSphereLaw (n+1))).prod (stdGaussian (Spin L)))
      ((unitSphereLaw (n+1)).prod ((gaussianRadiusLaw n).prod (stdGaussian (Spin L)))) :=
  by
    let : IsProbabilityMeasure (unitSphereLaw (n+1)) := by first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
    have hs : MeasurePreserving (Prod.swap : Ioi (0:ℝ)×Metric.sphere (0:Spin (n+1)) 1 →
        Metric.sphere (0:Spin (n+1)) 1×Ioi (0:ℝ))
        ((gaussianRadiusLaw n).prod (unitSphereLaw (n+1)))
        ((unitSphereLaw (n+1)).prod (gaussianRadiusLaw n)) := Measure.measurePreserving_swap
    exact (measurePreserving_prodAssoc (unitSphereLaw (n+1)) (gaussianRadiusLaw n) (stdGaussian (Spin L))).comp
      (hs.prod (MeasurePreserving.id (stdGaussian (Spin L))))

lemma cavityUnitPair_preserving (n L : ℕ) :
    MeasurePreserving (fun p : (Ioi (0:ℝ)×Metric.sphere (0:Spin (n+1)) 1)×Spin L=>
      (p.1.2,cavityRadialUnit n L (p.1.1,p.2)))
      (((gaussianRadiusLaw n).prod (unitSphereLaw (n+1))).prod (stdGaussian (Spin L)))
      ((unitSphereLaw (n+1)).prod (cavityUnitLaw n L)) :=
  by
    have h1 := MeasurePreserving.id (unitSphereLaw (n+1))
    have h2 : MeasurePreserving (cavityRadialUnit n L)
        ((gaussianRadiusLaw n).prod (stdGaussian (Spin L))) (cavityUnitLaw n L) :=
      ⟨cavityRadialUnit_measurable n L,rfl⟩
    exact (h1.prod h2).comp (cavityRadial_reorder_preserving n L)

theorem sphereBlock_product_law (n L : ℕ) :
    (unitSphereLaw (n+1+L)).map (fun u=>gaussianBlockSplit (n+1) L u.val)=
      ((unitSphereLaw (n+1)).prod (cavityUnitLaw n L)).map (cavityUnitEmbed n L) := by
  rw [sphereBlock_radial_law,←(cavityUnitPair_preserving n L).map_eq,
    Measure.map_map (cavityUnitEmbed_measurable n L) (cavityUnitPair_preserving n L).measurable]
  congr 1
  funext p
  exact cavityRadialBlock_unitEmbed n L p

lemma cavityUnitLaw_actual (n L : ℕ) :
    (cavityUnitLaw n L : Measure (Spin L))=
      (unitSphereLaw (n+1+L)).map (fun u=>(gaussianBlockSplit (n+1) L u.val).2) := by
  have he:=congrArg (fun μ : Measure (Spin (n+1)×Spin L)=>μ.map Prod.snd) (sphereBlock_product_law n L)
  have hm : Measurable (fun u : Metric.sphere (0:Spin (n+1+L)) 1=>gaussianBlockSplit (n+1) L u.val) :=
    (gaussianBlockSplit_measurable (n+1) L).comp measurable_subtype_coe
  rw [Measure.map_map measurable_snd hm,
    Measure.map_map measurable_snd (cavityUnitEmbed_measurable n L)] at he
  change _=((unitSphereLaw (n+1)).prod (cavityUnitLaw n L : Measure (Spin L))).map Prod.snd at he
  rw [Measure.map_snd_prod,measure_univ,one_smul] at he
  exact he.symm

lemma cavitySphereLaw_unit (n L : ℕ) :
    (cavitySphereLaw n L : Measure (Spin L))=
      (cavityUnitLaw n L : Measure (Spin L)).map (fun z=>Real.sqrt (n+1+L:ℕ) •z) := by
  have hm : Measurable (fun u : Metric.sphere (0:Spin (n+1+L)) 1 =>
      (gaussianBlockSplit (n+1) L u.val).2) :=
    (((gaussianBlockSplit_measurable (n+1) L).comp measurable_subtype_coe).snd)
  rw [cavityUnitLaw_actual,Measure.map_map (by fun_prop) hm]
  rfl

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cavity_CavityExpectedCompensator
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceCountDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceCountKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityIncrementRandomCavityIncrementLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityProxyRandomCavityProxyLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

lemma bulkCDefect_bound (m M : ℕ) (f : Jet3) (v : ℕ→ℝ) (c K : ℝ) (hK : 0≤K)
    (hC : ∀ (a : BulkDisorder (m+1) M) x,|bulkC (m+1) M f a.1 x|≤K)
    (a : BulkDisorder (m+1) M) : |bulkCDefect m M f v c a|≤K+|c| := by
  apply tiltMean_bound_general (unitSphereLaw (m+1))
    ((bulkGibbsHamiltonian_measurable m M f.f v).of_uncurry_left)
    ((((bulkC_measurable m M f).comp (measurable_const.prodMk measurable_id)).sub_const c).abs)
    (by positivity)
  intro x
  rw [abs_abs]
  exact (abs_sub _ _).trans (add_le_add (hC a x) le_rfl)

lemma cavityBulkCompError_measurable (n d m M : ℕ) (f : Jet3) (v : ℕ→ℝ)
    (Λ : ℝ) (hΛ : 1≤Λ) (c : ℝ) : Measurable (cavityBulkCompError n d m M f v Λ hΛ c) :=
  (cavityBulkCompPartition_measurable n d m M f v Λ hΛ).log.sub
    ((cavityBulkPartition_measurable n d m M f v Λ hΛ).log.const_add _)

lemma cavityBulkCompError_integrable (n d m M : ℕ) (f : Jet3) (v : ℕ→ℝ)
    (Λ : ℝ) (hΛ : 1≤Λ) (c K : ℝ) (hc : |c|≤K)
    (hC : ∀ (a : BulkDisorder (m+1) M) x,|bulkC (m+1) M f a.1 x|≤K) :
    Integrable (cavityBulkCompError n d m M f v Λ hΛ c)
      ((bulkDisorderLaw (m+1) M).prod (stdGaussian (EuclideanSpace ℝ (CavityBulkNoiseIndex n d m M)))) := by
  apply Integrable.of_bound (cavityBulkCompError_measurable n d m M f v Λ hΛ c).aestronglyMeasurable
    (cavityCompensatorConstant n d f.f Λ K*(K+|c|))
  filter_upwards [] with p
  rw [Real.norm_eq_abs]
  refine (cavityBulkCompPartition_error n d m M f v Λ hΛ c K hc hC p).trans ?_
  exact mul_le_mul_of_nonneg_left
    ((le_abs_self _).trans (bulkCDefect_bound m M f v c K ((abs_nonneg _).trans hc) hC p.1))
    (cavityCompensatorConstant_nonneg n d f.f hΛ)

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Sphere_GaussianCoordinateProjection
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceCountDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceCountKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityIncrementRandomCavityIncrementLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityProxyRandomCavityProxyLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped Topology
namespace SphericalPerceptronFreeEnergy

lemma finiteGaussian_coordinate_projection {I J : Type*} [Fintype I] [Fintype J]
    (e : J→I) (he : Function.Injective e) :
    MeasurePreserving (fun x : EuclideanSpace ℝ I=>fun j=>x (e j))
      (stdGaussian (EuclideanSpace ℝ I)) (Measure.pi fun _ : J=>gaussianReal 0 1) := by
  refine ⟨by fun_prop,?_⟩
  rw [←map_pi_eq_stdGaussian,Measure.map_map (by fun_prop) (PiLp.continuous_toLp 2 _).measurable]
  change (Measure.pi fun _ : I=>gaussianReal 0 1).map (fun x j=>x (e j))=_
  rw [←Measure.infinitePi_eq_pi,Measure.map_infinitePi_infinitePi_of_inj he,Measure.infinitePi_eq_pi]

lemma finiteGaussian_curry_preserving (I J : Type*) [Fintype I] [Fintype J] :
    MeasurePreserving (fun x : I×J→ℝ=>fun i j=>x (i,j))
      (Measure.pi fun _ : I×J=>gaussianReal 0 1)
      (Measure.pi fun _ : I=>Measure.pi fun _ : J=>gaussianReal 0 1) := by
  refine ⟨by fun_prop,?_⟩
  have h:=Measure.infinitePi_map_curry (μ:=fun (_ : I) (_ : J)=>gaussianReal 0 1)
  simp only [Measure.infinitePi_eq_pi] at h
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  rfl

lemma cavityBulkNoiseSplit_preserving (n d m M : ℕ) :
    MeasurePreserving (cavityBulkNoiseSplit n d m M)
      (stdGaussian (EuclideanSpace ℝ (CavityBulkNoiseIndex n d m M)))
      ((Measure.pi fun _ : Fin M=>stdGaussian (Spin (n+1))).prod
        (finitePatternRowsLaw (m+1) d)) := by
  let e : (Fin M×Fin (n+1))⊕(Fin d×Fin (m+1))→CavityBulkNoiseIndex n d m M :=
    Sum.elim (fun p=>(Sum.inl p.2,Sum.inl p.1)) (fun p=>(Sum.inr p.1,Sum.inr p.2))
  have he : Function.Injective e := by
    intro a b h
    cases a <;> cases b <;> simp only [e,Sum.elim_inl,Sum.elim_inr,Prod.mk.injEq,Sum.inl.injEq,
      Sum.inr.injEq,Sum.inl_ne_inr,Sum.inr_ne_inl,false_and] at h
    · exact congrArg Sum.inl (Prod.ext h.2 h.1)
    · exact congrArg Sum.inr (Prod.ext h.1 h.2)
  have hp:=(measurePreserving_sumPiEquivProdPi
    (fun _ : (Fin M×Fin (n+1))⊕(Fin d×Fin (m+1))=>gaussianReal 0 1)).comp
    (finiteGaussian_coordinate_projection e he)
  have ht : MeasurePreserving (WithLp.toLp 2 : (Fin (n+1)→ℝ)→Spin (n+1))
      (Measure.pi fun _=>gaussianReal 0 1) (stdGaussian (Spin (n+1))) :=
    ⟨(PiLp.continuous_toLp 2 _).measurable,map_pi_eq_stdGaussian⟩
  have hleft:=(measurePreserving_pi (fun _ : Fin M=>Measure.pi fun _ : Fin (n+1)=>gaussianReal 0 1)
    (fun _=>stdGaussian (Spin (n+1))) (fun _=>ht)).comp (finiteGaussian_curry_preserving (Fin M) (Fin (n+1)))
  convert (hleft.prod (finiteGaussian_curry_preserving (Fin d) (Fin (m+1)))).comp hp using 1
  · rfl
  · rfl

lemma cavityBulkNoiseSplit_scalar (n d m M : ℕ) (f : Jet3) (a : BulkDisorder (m+1) M)
    (x : NormalizedSpin (m+1)) (y : EuclideanSpace ℝ (CavityBulkNoiseIndex n d m M)) (t : Fin d) :
    inner ℝ (cavityBulkFeature n d m M f a x (Sum.inr t)) y=
      ∑ i,(cavityBulkNoiseSplit n d m M y).2 t i*x.val i := by
  classical
  simp only [EuclideanSpace.inner_eq_star_dotProduct,dotProduct,cavityBulkFeature,
    star_trivial,Fintype.sum_prod_type]
  simp only [mul_ite,mul_zero,cavityBulkBase,Fintype.sum_sum_type,cavityBulkNoiseSplit]
  simp only [Sum.inl_ne_inr,Sum.inr.injEq,ite_false,ite_self,Finset.sum_const_zero,zero_add]
  rw [Finset.sum_comm]
  simp

lemma cavityBulkNoiseSplit_vector (n d m M : ℕ) (f : Jet3) (a : BulkDisorder (m+1) M)
    (x : NormalizedSpin (m+1)) (y : EuclideanSpace ℝ (CavityBulkNoiseIndex n d m M)) :
    gaussianRows (fun i=>cavityBulkFeature n d m M f a x (Sum.inl i)) y=
      cavityVectorField M (n+1) (fun t=>f.d1 (∑ i,a.1 t i*x.val i))
        (Real.sqrt (m+1:ℕ))⁻¹ (cavityBulkNoiseSplit n d m M y).1 := by
  classical
  ext i
  simp only [gaussianRows_apply,EuclideanSpace.inner_eq_star_dotProduct,dotProduct,cavityBulkFeature,
    star_trivial,Fintype.sum_prod_type]
  simp only [mul_ite,mul_zero,cavityBulkBase,Fintype.sum_sum_type,
    cavityBulkNoiseSplit,cavityVectorField,PiLp.smul_apply,smul_eq_mul]
  simp only [EuclideanSpace.inner_eq_star_dotProduct,dotProduct,star_trivial]
  simp only [Sum.inl.injEq,Sum.inr_ne_inl,ite_false,ite_self,Finset.sum_const_zero,add_zero]
  rw [Finset.sum_comm]
  simp only [Fintype.sum_ite_eq']
  try simp only [cavityVectorField,PiLp.smul_apply,smul_eq_mul,PiLp.sum_apply,PiLp.toLp_apply]
  simp_rw [mul_comm (y.ofLp _) _]
  simp only [WithLp.ofLp_sum,PiLp.smul_apply,Finset.sum_apply,smul_eq_mul]
  simp only [mul_assoc,Finset.mul_sum]
end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cavity_CavityBulkUncappedLog
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceCountDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceCountKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityIncrementRandomCavityIncrementLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityProxyRandomCavityProxyLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Filter
open scoped Topology BigOperators BoundedContinuousFunction

lemma cavityBulk_log_integrable (n d m M : ℕ) (f : Jet3) (v : ℕ→ℝ) (Λ : ℝ) (hΛ : 1≤Λ) :
    Integrable (fun p=>Real.log (cavityBulkPartition n d m M f v Λ hΛ p))
      ((bulkDisorderLaw (m+1) M).prod (stdGaussian (EuclideanSpace ℝ (CavityBulkNoiseIndex n d m M)))) := by
  apply Integrable.of_bound (cavityBulkPartition_measurable n d m M f v Λ hΛ).log.aestronglyMeasurable
    ‖cavityPartitionLogTest d f.f Λ‖
  exact ae_of_all _ fun p=>(cavityPartitionLogTest d f.f Λ).norm_coe_le_norm
    ⟨cavityBulkPartition n d m M f v Λ hΛ p,cavityBulkPartition_mem n d m M f v Λ hΛ p⟩

lemma cavityBulk_comp_log_integrable (n d m M : ℕ) (f : Jet3) (v : ℕ→ℝ) (Λ : ℝ) (hΛ : 1≤Λ)
    (K : ℝ) (hK : 0≤K)
    (hC : ∀ (a : BulkDisorder (m+1) M) x,|bulkC (m+1) M f a.1 x|≤K) :
    Integrable (fun p=>Real.log (cavityBulkCompPartition n d m M f v Λ hΛ p))
      ((bulkDisorderLaw (m+1) M).prod (stdGaussian (EuclideanSpace ℝ (CavityBulkNoiseIndex n d m M)))) := by
  have he:=cavityBulkCompError_integrable n d m M f v Λ hΛ 0 K (by simpa using hK) hC
  have hb:=cavityBulk_log_integrable n d m M f v Λ hΛ
  exact (he.add hb).congr (ae_of_all _ fun p=>by dsimp [cavityBulkCompError]; ring)

lemma cavityBulk_full_log_integrable (n d m M : ℕ) (f : Jet3) (v : ℕ→ℝ)
    (K KC : ℝ) (hK : M/(m+1:ℕ)*‖f.d1‖^2≤K) (hKC : 0≤KC)
    (hC : ∀ (a : BulkDisorder (m+1) M) x,|bulkC (m+1) M f a.1 x|≤KC) :
    Integrable (fun p=>Real.log (cavityBulkFullCompPartition n d m M f v p))
      ((bulkDisorderLaw (m+1) M).prod (stdGaussian (EuclideanSpace ℝ (CavityBulkNoiseIndex n d m M)))) := by
  have he:=(cavityBulk_uncap_annealed n d m M f v 1 le_rfl K KC hK hC).1
  have hb:=cavityBulk_comp_log_integrable n d m M f v 1 le_rfl KC hKC hC
  exact (he.add hb).congr (ae_of_all _ fun p=>by dsimp [cavityBulkUncapError]; ring)

lemma cavityBulkNoiseJoin_measurable (n d m M : ℕ) :
    Measurable (cavityBulkNoiseJoin n d m M) := by
  apply (MeasurableEquiv.toLp 2 _).measurable.comp
  apply Measurable.of_eval
  intro j
  rcases j with ⟨i,t⟩
  cases i <;> cases t <;> dsimp [cavityBulkNoiseJoin] <;> fun_prop

lemma cavityBulkNoiseSplit_join (n d m M : ℕ)
    (p : (Fin M→Spin (n+1))×(Fin d→Fin (m+1)→ℝ)) :
    cavityBulkNoiseSplit n d m M (cavityBulkNoiseJoin n d m M p)=p := by
  rfl

lemma cavitySplitPartition_identity (n d m M : ℕ) (f : Jet3) (v : ℕ→ℝ)
    (a : BulkDisorder (m+1) M) (y : EuclideanSpace ℝ (CavityBulkNoiseIndex n d m M)) :
    cavityBulkFullCompPartition n d m M f v (a,y)=
      cavitySplitPartition n d m M f v (a,cavityBulkNoiseSplit n d m M y) := by
  unfold cavitySplitPartition
  rw [tilt_law_integral _ (bulkHamiltonian_section_measurable (m+1) M f.f v a)
    (show 0≤M*‖f.f‖+bulkFeatureBound (m+1) v*‖a.2‖ from by
      unfold bulkFeatureBound; positivity) (bulkHamiltonian_bound (m+1) M f.f v a) 1]
  unfold cavityBulkFullCompPartition
  congr 1
  funext x
  rw [cavityBulkNoiseSplit_vector]
  simp_rw [cavityBulkNoiseSplit_scalar]
  congr 2
  unfold normalizedPatternEnergy
  ring

lemma cavitySplitPartition_measurable (n d m M : ℕ) (f : Jet3) (v : ℕ→ℝ) :
    Measurable (cavitySplitPartition n d m M f v) := by
  have hm:=(cavityBulkFullCompPartition_measurable n d m M f v).comp
    (measurable_fst.prodMk ((cavityBulkNoiseJoin_measurable n d m M).comp measurable_snd))
  simpa only [Function.comp_def,cavitySplitPartition_identity,cavityBulkNoiseSplit_join] using hm

lemma cavitySplitLog_integrable (n d m M : ℕ) (f : Jet3)
    (hf : HasCompactSupport (f.d1 : ℝ→ℝ)) (v : ℕ→ℝ) :
    Integrable (fun p=>Real.log (cavitySplitPartition n d m M f v p))
      ((bulkDisorderLaw (m+1) M).prod ((Measure.pi fun _ : Fin M=>stdGaussian (Spin (n+1))).prod
        (finitePatternRowsLaw (m+1) d))) := by
  have hp:=(MeasurePreserving.id (bulkDisorderLaw (m+1) M)).prod (cavityBulkNoiseSplit_preserving n d m M)
  apply (hp.integrable_comp (cavitySplitPartition_measurable n d m M f v).log.aestronglyMeasurable).mp
  have hi:=cavityBulk_full_log_integrable n d m M f v
    (M/(m+1:ℕ)*‖f.d1‖^2) (M/(m+1:ℕ)*‖f.dilationMark hf‖) le_rfl (by positivity)
    (bulkC_bound m M f hf)
  convert hi using 1
  all_goals try with_reducible_and_instances rfl
  funext p
  exact congrArg Real.log (cavitySplitPartition_identity n d m M f v p.1 p.2).symm

lemma cavityBulkFullLog_split (n d m M : ℕ) (f : Jet3)
    (hf : HasCompactSupport (f.d1 : ℝ→ℝ)) (v : ℕ→ℝ) :
    cavityBulkFullLog n d m M f v=
      ∫ a,∫ b,∫ y,Real.log (cavitySplitPartition n d m M f v (a,y,b))
        ∂Measure.pi (fun _ : Fin M=>stdGaussian (Spin (n+1)))
        ∂finitePatternRowsLaw (m+1) d ∂bulkDisorderLaw (m+1) M := by
  have hp:=(MeasurePreserving.id (bulkDisorderLaw (m+1) M)).prod (cavityBulkNoiseSplit_preserving n d m M)
  have h : (∫ p,Real.log (cavitySplitPartition n d m M f v (Prod.map id (cavityBulkNoiseSplit n d m M) p))
      ∂(bulkDisorderLaw (m+1) M).prod (stdGaussian (EuclideanSpace ℝ (CavityBulkNoiseIndex n d m M))))=
      ∫ p,Real.log (cavitySplitPartition n d m M f v p)
        ∂(bulkDisorderLaw (m+1) M).prod ((Measure.pi fun _ : Fin M=>stdGaussian (Spin (n+1))).prod
          (finitePatternRowsLaw (m+1) d)) := by
    rw [←hp.map_eq]
    exact (integral_map hp.measurable.aemeasurable
      (cavitySplitPartition_measurable n d m M f v).log.aestronglyMeasurable).symm
  unfold cavityBulkFullLog
  have he : (fun p : BulkDisorder (m+1) M×EuclideanSpace ℝ (CavityBulkNoiseIndex n d m M)=>
      Real.log (cavityBulkFullCompPartition n d m M f v p))=
      (fun p=>Real.log (cavitySplitPartition n d m M f v (Prod.map id (cavityBulkNoiseSplit n d m M) p))) := by
    funext p
    exact congrArg Real.log (cavitySplitPartition_identity n d m M f v p.1 p.2)
  rw [he,h,integral_prod _ (cavitySplitLog_integrable n d m M f hf v)]
  apply integral_congr_ae
  filter_upwards [(cavitySplitLog_integrable n d m M f hf v).prod_right_ae] with a ha
  exact integral_prod_symm _ ha

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cavity_CavityFiniteEvaluation
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceCountDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceCountKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityIncrementRandomCavityIncrementLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityProxyRandomCavityProxyLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal BigOperators BoundedContinuousFunction

lemma gaussianBlockJoin_preserving (N L : ℕ) :
    MeasurePreserving (gaussianBlockJoin N L)
      ((stdGaussian (Spin N)).prod (stdGaussian (Spin L)))
      (stdGaussian (Spin (N+L))) := by
  refine ⟨gaussianBlockJoin_measurable N L,?_⟩
  rw [←(gaussianBlockSplit_preserving N L).map_eq,
    Measure.map_map (gaussianBlockJoin_measurable N L) (gaussianBlockSplit_measurable N L)]
  simp only [Function.comp_def,gaussianBlockJoin_split]
  exact Measure.map_id

lemma stdGaussian_ofLp_preserving (N : ℕ) :
    MeasurePreserving (WithLp.ofLp : Spin N→Fin N→ℝ) (stdGaussian (Spin N))
      (Measure.pi fun _=>gaussianReal 0 1) := by
  refine ⟨(PiLp.continuous_ofLp 2 _).measurable,?_⟩
  rw [←map_pi_eq_stdGaussian,
    Measure.map_map (PiLp.continuous_ofLp 2 _).measurable (PiLp.continuous_toLp 2 _).measurable]
  exact Measure.map_id

lemma cavityJoinedPatterns_preserving (N L M : ℕ) :
    MeasurePreserving (fun p : (Fin M→Fin N→ℝ)×(Fin M→Spin L)=>
      cavityJoinedPatterns N L M p.1 p.2)
      ((Measure.pi fun _ : Fin M=>Measure.pi fun _ : Fin N=>gaussianReal 0 1).prod
        (Measure.pi fun _ : Fin M=>stdGaussian (Spin L)))
      (Measure.pi fun _ : Fin M=>Measure.pi fun _ : Fin (N+L)=>gaussianReal 0 1) := by
  have ht : MeasurePreserving (WithLp.toLp 2 : (Fin N→ℝ)→Spin N)
      (Measure.pi fun _=>gaussianReal 0 1) (stdGaussian (Spin N)) :=
    ⟨(PiLp.continuous_toLp 2 _).measurable,map_pi_eq_stdGaussian⟩
  have hj := (stdGaussian_ofLp_preserving (N+L)).comp
    ((gaussianBlockJoin_preserving N L).comp (ht.prod (MeasurePreserving.id _)))
  have hp := measurePreserving_pi (fun _ : Fin M=>(Measure.pi fun _ : Fin N=>gaussianReal 0 1).prod
      (stdGaussian (Spin L))) (fun _ : Fin M=>Measure.pi fun _ : Fin (N+L)=>gaussianReal 0 1)
      (fun _=>hj)
  have hr := (measurePreserving_arrowProdEquivProdArrow (Fin N→ℝ) (Spin L) (Fin M)
    (fun _=>Measure.pi fun _=>gaussianReal 0 1) (fun _=>stdGaussian (Spin L))).symm
  convert hp.comp hr using 1
  all_goals try with_reducible_and_instances rfl
  funext p i j
  rfl

lemma cavity_log_uniform_change {S : Type*} [MeasurableSpace S]
    (μ : Measure S) [IsProbabilityMeasure μ] {F G : S→ℝ}
    (hF : Measurable F) (hG : Measurable G) {A E : ℝ} (hA : 0≤A)
    (hFA : ∀ s,|F s|≤A) (hE : ∀ s,|F s-G s|≤E) :
    |Real.log (∫ s,Real.exp (F s) ∂μ)-Real.log (∫ s,Real.exp (G s) ∂μ)|≤E := by
  have hGA (s : S) : |G s|≤A+|E| := by
    calc
      _=|G s-F s+F s| := by ring_nf
      _≤|G s-F s|+|F s| := abs_add_le _ _
      _≤|E|+A := add_le_add ((show |G s-F s|≤E by simpa only [abs_sub_comm] using hE s).trans (le_abs_self E)) (hFA s)
      _=A+|E| := add_comm _ _
  have hFi : Integrable (fun s=>Real.exp (F s)) μ := by
    apply Integrable.of_bound hF.exp.aestronglyMeasurable (Real.exp A)
    exact ae_of_all _ fun s=>by
      rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_exp.mpr ((le_abs_self _).trans (hFA s))
  have hGi : Integrable (fun s=>Real.exp (G s)) μ := by
    apply Integrable.of_bound hG.exp.aestronglyMeasurable (Real.exp (A+|E|))
    exact ae_of_all _ fun s=>by
      rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_exp.mpr ((le_abs_self _).trans (hGA s))
  exact abs_log_integral_exp_sub_le μ hFi hGi
    (by simpa only [tiltPartition,one_mul] using tilt_partition_pos μ hF hA hFA 1)
    (by simpa only [tiltPartition,one_mul] using tilt_partition_pos μ hG (by positivity) hGA 1) hE

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cavity_CavityExpectedQDrop
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceCountDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceCountKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityIncrementRandomCavityIncrementLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityProxyRandomCavityProxyLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators
namespace SphericalPerceptronFreeEnergy

lemma cavityQuadraticField_abs_bound (M L : ℕ) (b : Fin M→ℝ) (u : ℝ)
    (z : Spin L) (y : Fin M→Spin L) {B D : ℝ} (hB : 0≤B) (hD : 0≤D)
    (hb : ∀ i,|b i|≤B) (hz : ‖z‖≤D) :
    |cavityQuadraticField M L b u z y|≤|u| * ∑ i,B*D^2*(‖y i‖^2+1) := by
  unfold cavityQuadraticField
  rw [abs_mul]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro i hi
  rw [abs_mul]
  have hkeep : |(inner ℝ z (y i))^2-‖z‖^2|≤D^2*(‖y i‖^2+1) := by
    have hp : (inner ℝ z (y i))^2≤(D*‖y i‖)^2 := by
      apply sq_le_sq.mpr
      simpa only [abs_mul,abs_of_nonneg hD,abs_norm] using
        (abs_real_inner_le_norm z (y i)).trans (mul_le_mul_of_nonneg_right hz (norm_nonneg _))
    have hq : ‖z‖^2≤D^2 := sq_le_sq₀ (norm_nonneg _) hD |>.mpr hz
    calc
      _≤|(inner ℝ z (y i))^2|+|‖z‖^2| := abs_sub _ _
      _=(inner ℝ z (y i))^2+‖z‖^2 := by rw [abs_of_nonneg (sq_nonneg _),abs_of_nonneg (sq_nonneg _)]
      _≤D^2*(‖y i‖^2+1) := by nlinarith
  exact (mul_le_mul (hb i) hkeep (abs_nonneg _) hB).trans_eq (by ring)

lemma cavity_log_integrable_of_bound {S Y : Type*} [MeasurableSpace S] [MeasurableSpace Y]
    (μ : Measure S) [IsProbabilityMeasure μ] (P : Measure Y) (H : S×Y→ℝ)
    (hH : Measurable H) (K : Y→ℝ) (hK : Integrable K P)
    (hK0 : ∀ y,0≤K y) (hB : ∀ s y,|H (s,y)|≤K y) :
    Integrable (fun y=>Real.log (∫ s,Real.exp (H (s,y)) ∂μ)) P := by
  have hm : Measurable (fun y=>Real.log (∫ s,Real.exp (H (s,y)) ∂μ)) :=
    hH.exp.stronglyMeasurable.integral_prod_left'.measurable.log
  apply hK.mono' hm.aestronglyMeasurable
  exact ae_of_all _ fun y=>by
    rw [Real.norm_eq_abs]
    simpa only [tiltPartition,one_mul,Function.comp_def,id_eq] using tilt_log_partition_bound μ
      (hH.comp (measurable_id.prodMk measurable_const)) (hK0 y) (fun s=>hB s y)

lemma cavity_quadratic_log_integrable {S : Type*} [MeasurableSpace S]
    (μ : Measure S) [IsProbabilityMeasure μ] (M L : ℕ)
    (a b : S→Fin M→ℝ) (z : S→Spin L) (W : S→ℝ)
    (ha : Measurable a) (hb : Measurable b) (hz : Measurable z) (hW : Measurable W)
    (t u : ℝ) {A B C D : ℝ} (hA : 0≤A) (hB : 0≤B) (hC : 0≤C) (hD : 0≤D)
    (haB : ∀ s i,|a s i|≤A) (hbB : ∀ s i,|b s i|≤B)
    (hzB : ∀ s,‖z s‖≤D) (hWB : ∀ s,|W s|≤C) :
    Integrable (fun y : Fin M→Spin L=>Real.log (∫ s,Real.exp
      (W s+cavityLinearField M L (a s) t (z s) y+cavityQuadraticField M L (b s) u (z s) y) ∂μ))
      (Measure.pi (fun _=>stdGaussian (Spin L))) := by
  let P:=Measure.pi (fun _ : Fin M=>stdGaussian (Spin L))
  let K:=fun y : Fin M→Spin L=>C+|t| *(∑ i,A*D*‖y i‖)+|u| *(∑ i,B*D^2*(‖y i‖^2+1))
  have hi (i : Fin M) (p : ℕ) : Integrable (fun y : Fin M→Spin L=>‖y i‖^p) P :=
    ((measurePreserving_eval (fun _ : Fin M=>stdGaussian (Spin L)) i).integrable_comp
      (cavityNormMoment_integrable L p).aestronglyMeasurable).mpr (cavityNormMoment_integrable L p)
  have hK : Integrable K P := by
    apply Integrable.add
    · apply (integrable_const C).add
      apply Integrable.const_mul
      apply integrable_finsetSum
      intro i _
      simpa only [pow_one] using (hi i 1).const_mul (A*D)
    · apply Integrable.const_mul
      apply integrable_finsetSum
      intro i _
      exact ((hi i 2).add (integrable_const 1)).const_mul (B*D^2)
  apply cavity_log_integrable_of_bound μ P _
    (((hW.comp measurable_fst).add (cavityLinearField_measurable M L a z ha hz t)).add
      (cavityQuadraticField_measurable M L b z hb hz u)) K hK
    (fun y=>by dsimp [K]; positivity)
  intro s y
  apply (abs_add_le _ _).trans
  apply add_le_add _ (cavityQuadraticField_abs_bound M L (b s) u (z s) y hB hD (hbB s) (hzB s))
  exact (abs_add_le _ _).trans (add_le_add (hWB s)
    (cavityLinearField_abs_bound M L (a s) t (z s) y hA (haB s) (hzB s)))

lemma cavity_Q_ratio_integrable {S : Type*} [MeasurableSpace S]
    (μ : Measure S) [IsProbabilityMeasure μ] (M L : ℕ)
    (a b : S→Fin M→ℝ) (z : S→Spin L) (W : S→ℝ)
    (ha : Measurable a) (hb : Measurable b) (hz : Measurable z) (hW : Measurable W)
    (t u : ℝ) {A B C D : ℝ} (hA : 0≤A) (hB : 0≤B) (hD : 0≤D)
    (haB : ∀ s i,|a s i|≤A) (hbB : ∀ s i,|b s i|≤B)
    (hzB : ∀ s,‖z s‖^2≤D) (hWB : ∀ s,|W s|≤C)
    (hden : ∀ y,Real.exp (-C)≤∫ s,Real.exp (W s+cavityLinearField M L (a s) t (z s) y) ∂μ) :
    Integrable (fun y=>(∫ s,Real.exp (W s+cavityLinearField M L (a s) t (z s) y)*
      |cavityQuadraticField M L (b s) u (z s) y| ∂μ)/(∫ s,Real.exp (W s+
        cavityLinearField M L (a s) t (z s) y) ∂μ))
      (Measure.pi (fun _=>stdGaussian (Spin L))) := by
  have hi:=cavity_Q_product_integrable μ M L a b z W ha hb hz hW t u hA hB hD haB hbB hzB hWB
  have hZ : Measurable (fun y=>∫ s,Real.exp (W s+cavityLinearField M L (a s) t (z s) y) ∂μ) :=
    ((hW.comp measurable_fst).add (cavityLinearField_measurable M L a z ha hz t)).exp.stronglyMeasurable.integral_prod_left'.measurable
  apply (hi.integral_prod_right.const_mul (Real.exp C)).mono'
    (hi.integral_prod_right.aestronglyMeasurable.div₀ hZ.aestronglyMeasurable)
  exact ae_of_all _ fun y=>by
    have hn : 0≤∫ s,Real.exp (W s+cavityLinearField M L (a s) t (z s) y)*
        |cavityQuadraticField M L (b s) u (z s) y| ∂μ :=
      integral_nonneg fun _=>mul_nonneg (Real.exp_pos _).le (abs_nonneg _)
    dsimp only [Pi.div_apply,Pi.mul_apply,Prod.fst,Prod.snd,Function.comp_def]
    rw [Real.norm_eq_abs,abs_of_nonneg (div_nonneg hn ((Real.exp_pos _).le.trans (hden y))),
      div_eq_mul_inv,mul_comm (Real.exp C)]
    apply mul_le_mul_of_nonneg_left _ hn
    calc
      _≤(Real.exp (-C))⁻¹ := inv_anti₀ (Real.exp_pos _) (hden y)
      _=Real.exp C := by rw [Real.exp_neg,inv_inv]

theorem cavity_expected_log_drop_quadratic {S : Type*} [MeasurableSpace S]
    (μ : Measure S) [IsProbabilityMeasure μ] (M L : ℕ)
    (a b : S→Fin M→ℝ) (z : S→Spin L) (W : S→ℝ)
    (ha : Measurable a) (hb : Measurable b) (hz : Measurable z) (hW : Measurable W)
    (t u : ℝ) {A B C D : ℝ} (hA : 0≤A) (hB : 0≤B) (hC : 0≤C) (hD : 0≤D)
    (haB : ∀ s i,|a s i|≤A) (hbB : ∀ s i,|b s i|≤B)
    (hzB : ∀ s,‖z s‖≤D) (hWB : ∀ s,|W s|≤C)
    (hden : ∀ y,Real.exp (-C)≤∫ s,Real.exp (W s+cavityLinearField M L (a s) t (z s) y) ∂μ) :
    (∫ y : Fin M→Spin L,Real.log (∫ s,Real.exp
      (W s+cavityLinearField M L (a s) t (z s) y+cavityQuadraticField M L (b s) u (z s) y) ∂μ)
        ∂Measure.pi (fun _=>stdGaussian (Spin L)))≥
    (∫ y : Fin M→Spin L,Real.log (∫ s,Real.exp
      (W s+cavityLinearField M L (a s) t (z s) y) ∂μ)
        ∂Measure.pi (fun _=>stdGaussian (Spin L)))-
      Real.exp (2*C+t^2*D^2*M*A^2)*
        Real.sqrt (u^2*(D^2)^2*squareGaussianVariance*M*B^2) := by
  let P:=Measure.pi (fun _ : Fin M=>stdGaussian (Spin L))
  let H : S×(Fin M→Spin L)→ℝ:=fun p=>W p.1+cavityLinearField M L (a p.1) t (z p.1) p.2
  let Q : S×(Fin M→Spin L)→ℝ:=fun p=>cavityQuadraticField M L (b p.1) u (z p.1) p.2
  let Z:=fun y=>∫ s,Real.exp (H (s,y)) ∂μ
  let ZQ:=fun y=>∫ s,Real.exp (H (s,y)+Q (s,y)) ∂μ
  let R:=fun y=>(∫ s,Real.exp (H (s,y))*|Q (s,y)| ∂μ)/Z y
  have hsq (s : S) : ‖z s‖^2≤D^2 := pow_le_pow_left₀ (norm_nonneg _) (hzB s) 2
  have hqi : Integrable (fun y=>Real.log (ZQ y)) P :=
    cavity_quadratic_log_integrable μ M L a b z W ha hb hz hW t u hA hB hC hD haB hbB hzB hWB
  have hzi : Integrable (fun y=>Real.log (Z y)) P := by
    simpa only [cavityQuadraticField,zero_mul,add_zero] using
      cavity_quadratic_log_integrable μ M L a b z W ha hb hz hW t 0 hA hB hC hD haB hbB hzB hWB
  have hri : Integrable R P := cavity_Q_ratio_integrable μ M L a b z W ha hb hz hW
    t u hA hB (sq_nonneg D) haB hbB hsq hWB hden
  have hpoint (y : Fin M→Spin L) : Real.log (Z y)-R y≤Real.log (ZQ y) := by
    have hHm : Measurable (fun s=>H (s,y)) :=
      ((hW.comp measurable_fst).add (cavityLinearField_measurable M L a z ha hz t)).comp
        (measurable_id.prodMk measurable_const)
    have hQm : Measurable (fun s=>Q (s,y)) :=
      (cavityQuadraticField_measurable M L b z hb hz u).comp (measurable_id.prodMk measurable_const)
    apply cavity_log_drop_quadratic μ hHm hQm
      (show 0≤C+|t| *∑ i,A*D*‖y i‖ by positivity)
      (show 0≤|u| *∑ i,B*D^2*(‖y i‖^2+1) by positivity)
    · intro s
      exact (abs_add_le _ _).trans (add_le_add (hWB s)
        (cavityLinearField_abs_bound M L (a s) t (z s) y hA (haB s) (hzB s)))
    · intro s
      exact cavityQuadraticField_abs_bound M L (b s) u (z s) y hB hD (hbB s) (hzB s)
  have hmean := integral_mono (hzi.sub hri) hqi hpoint
  simp only [Pi.sub_apply] at hmean
  rw [integral_sub hzi hri] at hmean
  have hcost:=cavity_Q_normalized_bound μ M L a b z W ha hb hz hW t u hA hB
    (sq_nonneg D) haB hbB hsq hWB hden
  exact (sub_le_sub_left hcost _).trans hmean

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cavity_CavityShellPolar
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.bulkFiniteReplicaLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.bulkSpinKernel_markov _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.enrichedIndexedBaseMeasure_probability _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceBaseDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceSpinLeafKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceCountDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceCountKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityIncrementRandomCavityIncrementLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityProxyRandomCavityProxyLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped Topology ENNReal NNReal
namespace SphericalPerceptronFreeEnergy

lemma cavity_polar_data_preserving (n k : ℕ) :
    MeasurePreserving (fun p : (PositiveRadius×PositiveRadius)×Metric.sphere (0:Spin (k+1)) 1=>
      (p.1.1,p.1.2.val •p.2.val))
      (((gaussianRadiusLaw n).prod (gaussianRadiusLaw k)).prod (unitSphereLaw (k+1)))
      ((gaussianRadiusLaw n).prod (stdGaussian (Spin (k+1)))) := by
  have h : MeasurePreserving (fun p : PositiveRadius×(PositiveRadius×Metric.sphere (0:Spin (k+1)) 1)=>
      (p.1,p.2.1.val •p.2.2.val))
      ((gaussianRadiusLaw n).prod ((gaussianRadiusLaw k).prod (unitSphereLaw (k+1))))
      ((gaussianRadiusLaw n).prod (stdGaussian (Spin (k+1)))) :=
    (MeasurePreserving.id (gaussianRadiusLaw n)).prod (stdGaussian_radial_preserving k)
  exact h.comp (measurePreserving_prodAssoc (gaussianRadiusLaw n) (gaussianRadiusLaw k) (unitSphereLaw (k+1)))

lemma cavity_polar_radius_preserving (n k : ℕ) :
    MeasurePreserving (fun p : (PositiveRadius×PositiveRadius)×Metric.sphere (0:Spin (k+1)) 1=>
      (cavityPolarRadius n k p.1,p.2))
      (((gaussianRadiusLaw n).prod (gaussianRadiusLaw k)).prod (unitSphereLaw (k+1)))
      ((cavityRadiusLaw n k : Measure PositiveRadius).prod (unitSphereLaw (k+1))) := by
  have h : MeasurePreserving (cavityPolarRadius n k)
      ((gaussianRadiusLaw n).prod (gaussianRadiusLaw k)) (cavityRadiusLaw n k) :=
    ⟨cavityPolarRadius_measurable n k,rfl⟩
  exact h.prod (MeasurePreserving.id (unitSphereLaw (k+1)))

theorem cavitySphereLaw_polar (n k : ℕ) :
    (cavitySphereLaw n (k+1) : Measure (Spin (k+1)))=
      ((cavityRadiusLaw n k : Measure PositiveRadius).prod (unitSphereLaw (k+1))).map
        (fun p=>p.1.val •p.2.val) := by
  rw [cavitySphereLaw_unit]
  change (Measure.map (cavityRadialUnit n (k+1))
    ((gaussianRadiusLaw n).prod (stdGaussian (Spin (k+1))))).map _=_
  have hm : Measurable ((fun z : Spin (k+1)=>Real.sqrt (n+1+(k+1):ℕ) •z) ∘
      cavityRadialUnit n (k+1)) :=
    (by fun_prop : Measurable (fun z : Spin (k+1)=>Real.sqrt (n+1+(k+1):ℕ) •z)).comp
      (cavityRadialUnit_measurable n (k+1))
  rw [Measure.map_map (by fun_prop) (cavityRadialUnit_measurable _ _),
    ←(cavity_polar_data_preserving n k).map_eq,
    Measure.map_map hm (cavity_polar_data_preserving n k).measurable,
    ←(cavity_polar_radius_preserving n k).map_eq,
    Measure.map_map (by fun_prop) (cavity_polar_radius_preserving n k).measurable]
  congr 1
  funext p
  have hu : ‖p.2.val‖=1 := by simpa only [Metric.mem_sphere,dist_zero_right] using p.2.prop
  simp only [Function.comp_def,cavityRadialUnit,cavityPolarRadius,norm_smul,Real.norm_eq_abs,
    abs_of_pos (show 0<p.1.2.val from p.1.2.prop),hu,mul_one,smul_smul,mul_assoc]

lemma cavityRadiusShell_measurable (k : ℕ) : MeasurableSet (cavityRadiusShell k) := by
  unfold cavityRadiusShell
  exact (measurableSet_le measurable_const (measurable_subtype_coe.pow_const 2)).inter
    (measurableSet_le (measurable_subtype_coe.pow_const 2) measurable_const)

lemma cavityShell_smul_preimage (k : ℕ) :
    (fun p : PositiveRadius×Metric.sphere (0:Spin (k+1)) 1=>p.1.val •p.2.val) ⁻¹'
      cavityShell (k+1)=cavityRadiusShell k×ˢuniv := by
  ext p
  simp [cavityShell,cavityRadiusShell,norm_smul]

theorem cavitySphereLaw_shell_polar (n k : ℕ) :
    (cavitySphereLaw n (k+1) : Measure (Spin (k+1))).restrict (cavityShell (k+1))=
      (((cavityRadiusLaw n k : Measure PositiveRadius).restrict (cavityRadiusShell k)).prod
        (unitSphereLaw (k+1))).map (fun p=>p.1.val •p.2.val) := by
  rw [cavitySphereLaw_polar,Measure.restrict_map (by fun_prop) (cavityShell_measurable _),
    cavityShell_smul_preimage,←Measure.prod_restrict,Measure.restrict_univ]


lemma cavityRadiusShell_bounds (k : ℕ) {r : PositiveRadius} (hr : r∈cavityRadiusShell k) :
    Real.sqrt (k+1:ℕ) ≤ r.val ∧ r.val≤(k:ℝ)+3 := by
  have hp : 0 < r.val := r.prop
  have h1 : (k+1:ℕ) ≤ r.val^2 := hr.1
  have h2 : r.val^2≤(k+1:ℕ)+1 := hr.2
  constructor
  · exact (Real.sqrt_le_iff).mpr ⟨hp.le,h1⟩
  · have hk : (0:ℝ)≤k := Nat.cast_nonneg k
    push_cast at h2
    nlinarith [sq_nonneg (r.val-1)]

lemma cavity_shell_angular_integrable (n k : ℕ) (W C : ℝ) (Y : Spin (k+1)) :
    Integrable (fun p : PositiveRadius×Metric.sphere (0:Spin (k+1)) 1=>
      Real.exp (W+p.1.val^2*C/2+p.1.val*inner ℝ Y p.2.val))
      (((cavityRadiusLaw n k : Measure PositiveRadius).restrict (cavityRadiusShell k)).prod
        (unitSphereLaw (k+1))) := by
  let μ:=(cavityRadiusLaw n k : Measure PositiveRadius).restrict (cavityRadiusShell k)
  have hae : ∀ᵐ p : PositiveRadius×Metric.sphere (0:Spin (k+1)) 1
      ∂μ.prod (unitSphereLaw (k+1)),p.1∈cavityRadiusShell k := by
    apply (Measure.ae_prod_iff_ae_ae (measurable_fst (cavityRadiusShell_measurable k))).mpr
    filter_upwards [ae_restrict_mem (cavityRadiusShell_measurable k)] with r hr
    exact ae_of_all _ fun _=>hr
  apply Integrable.of_bound (by fun_prop)
    (Real.exp (|W|+((k+1:ℕ)+1)*|C|/2+((k:ℝ)+3)*‖Y‖))
  filter_upwards [hae] with p hp
  have hr : 0<p.1.val := p.1.prop
  have hu : ‖p.2.val‖=1 := by simpa only [Metric.mem_sphere,dist_zero_right] using p.2.prop
  have hinner : inner ℝ Y p.2.val≤‖Y‖ := by
    simpa only [hu,mul_one] using (le_abs_self _).trans (abs_real_inner_le_norm Y p.2.val)
  rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
  apply Real.exp_le_exp.mpr
  apply add_le_add
  · apply add_le_add (le_abs_self _)
    exact div_le_div_of_nonneg_right
      ((mul_le_mul_of_nonneg_left (le_abs_self C) (sq_nonneg p.1.val)).trans
        (mul_le_mul_of_nonneg_right (show p.1.val^2≤(k+1:ℕ)+1 from hp.2) (abs_nonneg C))) (by norm_num)
  · exact (mul_le_mul_of_nonneg_left hinner hr.le).trans
      (mul_le_mul_of_nonneg_right (cavityRadiusShell_bounds k hp).2 (norm_nonneg Y))

lemma cavitySphereLaw_shell_integral (n k : ℕ) (W C : ℝ) (Y : Spin (k+1)) :
    (∫ z in cavityShell (k+1),Real.exp (W+‖z‖^2*C/2+inner ℝ Y z)
      ∂(cavitySphereLaw n (k+1) : Measure (Spin (k+1))))=
      ∫ r in cavityRadiusShell k,Real.exp (W+r.val^2*C/2)*sphericalExp k Y r.val
        ∂(cavityRadiusLaw n k : Measure PositiveRadius) := by
  rw [cavitySphereLaw_shell_polar,integral_map (by fun_prop) (by fun_prop)]
  have he : (fun p : PositiveRadius×Metric.sphere (0:Spin (k+1)) 1=>
      Real.exp (W+‖p.1.val •p.2.val‖^2*C/2+inner ℝ Y (p.1.val •p.2.val)))=
      (fun p=>Real.exp (W+p.1.val^2*C/2+p.1.val*inner ℝ Y p.2.val)) := by
    funext p
    have hu : ‖p.2.val‖=1 := by simpa only [Metric.mem_sphere,dist_zero_right] using p.2.prop
    simp only [norm_smul,Real.norm_eq_abs,hu,mul_one,sq_abs,real_inner_smul_right]
  rw [he,integral_prod _ (cavity_shell_angular_integrable n k W C Y)]
  apply integral_congr_ae
  filter_upwards [] with r
  simp only [Real.exp_add,integral_const_mul,sphericalExp]

lemma cavitySphereLaw_shell_mass_polar (n k : ℕ) :
    (cavitySphereLaw n (k+1) : Measure (Spin (k+1))).real (cavityShell (k+1))=
      (cavityRadiusLaw n k : Measure PositiveRadius).real (cavityRadiusShell k) := by
  have h:=cavitySphereLaw_shell_integral n k 0 0 0
  simpa [sphericalExp] using h

theorem cavitySphereLaw_shell_lower (n k : ℕ) (W C : ℝ) (Y : Spin (k+1))
    {K : ℝ} (hC : |C|≤K) :
    (cavitySphereLaw n (k+1) : Measure (Spin (k+1))).real (cavityShell (k+1))*
      (Real.exp (-K/2)*Real.exp (W+(k+1:ℕ)*C/2)*sphericalExp k Y (Real.sqrt (k+1:ℕ)))≤
      ∫ z in cavityShell (k+1),Real.exp (W+‖z‖^2*C/2+inner ℝ Y z)
        ∂(cavitySphereLaw n (k+1) : Measure (Spin (k+1))) := by
  rw [cavitySphereLaw_shell_integral,cavitySphereLaw_shell_mass_polar]
  have hi := (cavity_shell_angular_integrable n k W C Y).integral_prod_left
  have he : (fun r : PositiveRadius=>∫ u : Metric.sphere (0:Spin (k+1)) 1,
      Real.exp (W+r.val^2*C/2+r.val*inner ℝ Y u.val) ∂unitSphereLaw (k+1))=
      (fun r=>Real.exp (W+r.val^2*C/2)*sphericalExp k Y r.val) := by
    funext r
    simp only [Real.exp_add,integral_const_mul,sphericalExp]
  rw [he] at hi
  calc
    _ = ∫ _ in cavityRadiusShell k,
        Real.exp (-K/2)*Real.exp (W+(k+1:ℕ)*C/2)*sphericalExp k Y (Real.sqrt (k+1:ℕ))
          ∂(cavityRadiusLaw n k : Measure PositiveRadius) := by simp [mul_comm]
    _ ≤ _ := by
      apply integral_mono_ae (integrable_const _) hi
      filter_upwards [ae_restrict_mem (cavityRadiusShell_measurable k)] with r hr
      have hD : |(r.val^2-(k+1:ℕ))*C|≤K := by
        rw [abs_mul,abs_of_nonneg (sub_nonneg.mpr hr.1)]
        have hK : 0≤K := (abs_nonneg C).trans hC
        calc
          _≤1*K := mul_le_mul (by linarith [hr.2]) hC (abs_nonneg C) (by norm_num)
          _=K := one_mul K
      have hexp : Real.exp (-K/2)*Real.exp (W+(k+1:ℕ)*C/2)≤Real.exp (W+r.val^2*C/2) := by
        rw [←Real.exp_add]
        apply Real.exp_le_exp.mpr
        nlinarith [(abs_le.mp hD).1]
      exact mul_le_mul hexp
        (sphericalExp_mono k Y (Real.sqrt_nonneg _) (cavityRadiusShell_bounds k hr).1)
        ((by norm_num : (0:ℝ)≤1).trans (one_le_sphericalExp _ _ _)) (Real.exp_pos _).le

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cavity_CavityShellRestriction
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.bulkFiniteReplicaLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceCountDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceCountKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityIncrementRandomCavityIncrementLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityProxyRandomCavityProxyLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped Topology ENNReal BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

lemma cavityShellProbability_integral (n L : ℕ) (F : Spin L→ℝ) :
    (∫ z : {z : Spin L // z∈cavityShell L},F z.val ∂cavityShellProbability n L)=
      ((cavitySphereLaw n L : Measure (Spin L)).real (cavityShell L))⁻¹*
        ∫ z in cavityShell L,F z ∂(cavitySphereLaw n L : Measure (Spin L)) := by
  unfold cavityShellProbability
  rw [integral_subtype_comap (cavityShell_measurable L)]
  simp only [ProbabilityTheory.cond,Measure.restrict_smul,Measure.restrict_restrict (cavityShell_measurable L),
    inter_self,integral_smul_measure,ENNReal.toReal_inv,smul_eq_mul,Measure.real]

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cavity_CavityTrueShellQ
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceCountDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceCountKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityIncrementRandomCavityIncrementLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityProxyRandomCavityProxyLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

lemma cavity_shell_norm_bound (L : ℕ) (z : {z : Spin L // z∈cavityShell L}) :
    ‖z.val‖≤(L:ℝ)+1 := by
  have hz := z.prop.2
  nlinarith [sq_nonneg (‖z.val‖-1),Nat.cast_nonneg (α:=ℝ) L]

lemma cavityShellProbability_linear_one_le (n k : ℕ)
    (hp : (cavitySphereLaw n (k+1) : Measure (Spin (k+1))) (cavityShell (k+1))≠0)
    (Y : Spin (k+1)) :
    1≤∫ z : {z : Spin (k+1) // z∈cavityShell (k+1)},Real.exp (inner ℝ Y z.val)
      ∂cavityShellProbability n (k+1) := by
  have hm : 0<(cavitySphereLaw n (k+1) : Measure (Spin (k+1))).real (cavityShell (k+1)) :=
    ENNReal.toReal_pos hp (measure_ne_top _ _)
  have h := cavitySphereLaw_shell_lower n k 0 0 Y (K:=0) (by simp)
  simp only [neg_zero,zero_div,Real.exp_zero,Nat.cast_add,Nat.cast_one,mul_zero,
    add_zero,zero_add,one_mul] at h
  have h1 : (cavitySphereLaw n (k+1) : Measure (Spin (k+1))).real (cavityShell (k+1))≤
      ∫ z in cavityShell (k+1),Real.exp (inner ℝ Y z) ∂(cavitySphereLaw n (k+1) : Measure (Spin (k+1))) := by
    exact (le_mul_of_one_le_right hm.le (one_le_sphericalExp _ _ _)).trans h
  rw [cavityShellProbability_integral n (k+1) (fun z=>Real.exp (inner ℝ Y z))]
  have hh := mul_le_mul_of_nonneg_left h1 (inv_nonneg.mpr hm.le)
  simpa only [inv_mul_cancel₀ hm.ne'] using hh

lemma cavity_true_shell_denominator {S : Type*} [MeasurableSpace S]
    (μ : Measure S) [IsProbabilityMeasure μ] (n k M : ℕ)
    (hp : (cavitySphereLaw n (k+1) : Measure (Spin (k+1))) (cavityShell (k+1))≠0)
    (a : S→Fin M→ℝ) (W : S×{z : Spin (k+1) // z∈cavityShell (k+1)}→ℝ)
    (ha : Measurable a) (hW : Measurable W) (t : ℝ) {A C : ℝ}
    (hA : 0≤A) (haB : ∀ s i,|a s i|≤A) (hWB : ∀ p,|W p|≤C)
    (y : Fin M→Spin (k+1)) :
    Real.exp (-C)≤∫ p : S×{z : Spin (k+1) // z∈cavityShell (k+1)},
      Real.exp (W p+cavityLinearField M (k+1) (a p.1) t p.2.val y)
      ∂μ.prod (cavityShellProbability n (k+1)) := by
  have := cavityShellProbability_probability n (k+1) hp
  let F : S×{z : Spin (k+1) // z∈cavityShell (k+1)}→ℝ := fun p=>
    Real.exp (W p+cavityLinearField M (k+1) (a p.1) t p.2.val y)
  have hm : Measurable F := by
    have ha' : Measurable (fun p : S×{z : Spin (k+1) // z∈cavityShell (k+1)} => a p.1) := ha.comp measurable_fst
    unfold F cavityLinearField
    fun_prop
  have hi : Integrable F (μ.prod (cavityShellProbability n (k+1))) := by
    apply Integrable.of_bound hm.aestronglyMeasurable
      (Real.exp (C+|t| *∑ i,A*((k+1:ℕ)+1)*‖y i‖))
    exact ae_of_all _ fun p=>by
      rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
      apply Real.exp_le_exp.mpr
      exact add_le_add (abs_le.mp (hWB p)).2 ((le_abs_self _).trans
        (cavityLinearField_abs_bound M (k+1) (a p.1) t p.2.val y hA (haB p.1)
          (cavity_shell_norm_bound (k+1) p.2)))
  change Real.exp (-C)≤∫ p,F p ∂μ.prod (cavityShellProbability n (k+1))
  rw [integral_prod _ hi]
  apply (show Real.exp (-C)=∫ _ : S,Real.exp (-C) ∂μ by simp).trans_le
  apply integral_mono_ae (integrable_const _) hi.integral_prod_left
  filter_upwards [hi.prod_right_ae] with s hs
  have hlin : Integrable (fun z : {z : Spin (k+1) // z∈cavityShell (k+1)}=>
      Real.exp (cavityLinearField M (k+1) (a s) t z.val y)) (cavityShellProbability n (k+1)) := by
    apply Integrable.of_bound (by unfold cavityLinearField; fun_prop)
      (Real.exp (|t| *∑ i,A*((k+1:ℕ)+1)*‖y i‖))
    exact ae_of_all _ fun z=>by
      rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_exp.mpr ((le_abs_self _).trans
        (cavityLinearField_abs_bound M (k+1) (a s) t z.val y hA (haB s)
          (cavity_shell_norm_bound (k+1) z)))
  calc
    _≤Real.exp (-C)*(∫ z : {z : Spin (k+1) // z∈cavityShell (k+1)},
        Real.exp (cavityLinearField M (k+1) (a s) t z.val y) ∂cavityShellProbability n (k+1)) := by
      apply le_mul_of_one_le_right (Real.exp_pos _).le
      simpa only [cavityLinearField_inner] using
        cavityShellProbability_linear_one_le n k hp (cavityVectorField M (k+1) (a s) t y)
    _≤∫ z,F (s,z) ∂cavityShellProbability n (k+1) := by
      rw [←integral_const_mul]
      apply integral_mono (hlin.const_mul _) hs
      intro z
      dsimp only [F]
      rw [←Real.exp_add]
      exact Real.exp_le_exp.mpr (add_le_add (abs_le.mp (hWB (s,z))).1 le_rfl)

theorem cavity_true_shell_expected_drop {S : Type*} [MeasurableSpace S]
    (μ : Measure S) [IsProbabilityMeasure μ] (n k M : ℕ)
    (hp : (cavitySphereLaw n (k+1) : Measure (Spin (k+1))) (cavityShell (k+1))≠0)
    (a b : S→Fin M→ℝ) (W : S×{z : Spin (k+1) // z∈cavityShell (k+1)}→ℝ)
    (ha : Measurable a) (hb : Measurable b) (hW : Measurable W) (t u : ℝ)
    {A B C : ℝ} (hA : 0≤A) (hB : 0≤B) (hC : 0≤C)
    (haB : ∀ s i,|a s i|≤A) (hbB : ∀ s i,|b s i|≤B) (hWB : ∀ p,|W p|≤C) :
    (∫ y : Fin M→Spin (k+1),Real.log (∫ p : S×{z : Spin (k+1) // z∈cavityShell (k+1)},
      Real.exp (W p+cavityLinearField M (k+1) (a p.1) t p.2.val y+
        cavityQuadraticField M (k+1) (b p.1) u p.2.val y)
        ∂μ.prod (cavityShellProbability n (k+1))) ∂Measure.pi (fun _=>stdGaussian (Spin (k+1))))≥
    (∫ y : Fin M→Spin (k+1),Real.log (∫ p : S×{z : Spin (k+1) // z∈cavityShell (k+1)},
      Real.exp (W p+cavityLinearField M (k+1) (a p.1) t p.2.val y)
        ∂μ.prod (cavityShellProbability n (k+1))) ∂Measure.pi (fun _=>stdGaussian (Spin (k+1))))-
      Real.exp (2*C+t^2*((k+1:ℕ)+1)^2*M*A^2)*
        Real.sqrt (u^2*(((k+1:ℕ)+1)^2)^2*squareGaussianVariance*M*B^2) := by
  have := cavityShellProbability_probability n (k+1) hp
  exact cavity_expected_log_drop_quadratic (μ.prod (cavityShellProbability n (k+1))) M (k+1)
    (fun p=>a p.1) (fun p=>b p.1) (fun p=>p.2.val) W
    (ha.comp measurable_fst) (hb.comp measurable_fst) (measurable_snd.subtype_val) hW t u
    hA hB hC (by positivity) (fun p=>haB p.1) (fun p=>hbB p.1)
    (fun p=>cavity_shell_norm_bound (k+1) p.2) hWB
    (cavity_true_shell_denominator μ n k M hp a W ha hW t hA haB hWB)


lemma cavity_exp_integrable_bound {S : Type*} [MeasurableSpace S]
    (μ : Measure S) [IsFiniteMeasure μ] {H : S→ℝ} (hH : Measurable H)
    {C : ℝ} (hB : ∀ s,|H s|≤C) : Integrable (fun s=>Real.exp (H s)) μ := by
  apply Integrable.of_bound hH.exp.aestronglyMeasurable (Real.exp C)
  exact ae_of_all _ fun s=>by
    rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.mpr ((le_abs_self _).trans (hB s))

lemma cavity_gibbs_log_factorization {S T : Type*} [MeasurableSpace S] [MeasurableSpace T]
    (μ : Measure S) (ν : Measure T) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (H : S→ℝ) (V : S×T→ℝ) (hH : Measurable H) (hV : Measurable V)
    {A B : ℝ} (hA : 0≤A) (hB : 0≤B)
    (hHA : ∀ s,|H s|≤A) (hVB : ∀ p,|V p|≤B) :
    Real.log (∫ p,Real.exp (H p.1+V p) ∂μ.prod ν)-Real.log (∫ s,Real.exp (H s) ∂μ)=
      Real.log (∫ p,Real.exp (V p) ∂(tiltLaw μ H 1).prod ν) := by
  have := tilt_law_probability μ hH hA hHA 1
  have hi : Integrable (fun p : S×T=>Real.exp (H p.1+V p)) (μ.prod ν) := cavity_exp_integrable_bound (μ.prod ν) ((hH.comp measurable_fst).add hV)
    (fun p=>(abs_add_le _ _).trans (add_le_add (hHA p.1) (hVB p)))
  have hj := cavity_exp_integrable_bound ((tiltLaw μ H 1).prod ν) hV hVB
  have hp : 0<∫ s,Real.exp (H s) ∂μ := by
    simpa only [tiltPartition,one_mul] using tilt_partition_pos μ hH hA hHA 1
  have hq : 0<∫ p,Real.exp (V p) ∂(tiltLaw μ H 1).prod ν := by
    simpa only [tiltPartition,one_mul] using tilt_partition_pos ((tiltLaw μ H 1).prod ν) hV hB hVB 1
  have he : (∫ s,Real.exp (H s) ∂μ)*(∫ p,Real.exp (V p) ∂(tiltLaw μ H 1).prod ν)=
      ∫ p,Real.exp (H p.1+V p) ∂μ.prod ν := by
    rw [integral_prod _ hj,tilt_law_integral μ hH hA hHA 1]
    simp only [tiltMean,tiltIntegral,tiltPartition,one_mul]
    rw [mul_div_cancel₀ _ hp.ne',integral_prod _ hi]
    apply integral_congr_ae
    exact ae_of_all _ fun s=>by simp only [Real.exp_add,integral_const_mul]
  rw [←he,Real.log_mul hp.ne' hq.ne']
  ring

theorem cavity_actual_bulk_log_factorization (n L M : ℕ) (f : ℝ→ᵇℝ) (v : ℕ→ℝ)
    (a : BulkDisorder (n+1) M)
    (hp : (cavitySphereLaw n L : Measure (Spin L)) (cavityShell L)≠0)
    (V : CavityShellSpin n L→ℝ) (hV : Measurable V) {B : ℝ}
    (hB : 0≤B) (hVB : ∀ p,|V p|≤B) :
    Real.log (∫ p,Real.exp (bulkHamiltonian (n+1) M f v a.1 a.2 p.1+V p)
      ∂cavityShellBaseLaw n L)-
      bulkLogPartition n M f v a.1 a.2=
    Real.log (∫ p,Real.exp (V p) ∂(tiltLaw (unitSphereLaw (n+1))
      (bulkHamiltonian (n+1) M f v a.1 a.2) 1).prod (cavityShellProbability n L)) := by
  have := cavityShellProbability_probability n L hp
  exact cavity_gibbs_log_factorization (unitSphereLaw (n+1)) (cavityShellProbability n L)
    (bulkHamiltonian (n+1) M f v a.1 a.2) V
    (bulkHamiltonian_section_measurable (n+1) M f v a) hV
    (A:=M*‖f‖+bulkFeatureBound (n+1) v*‖a.2‖)
    (by apply add_nonneg (by positivity); apply mul_nonneg; unfold bulkFeatureBound; positivity; positivity)
    hB (bulkHamiltonian_bound (n+1) M f v a) hVB

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cavity_CavityTrueShellLower
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceCountDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceCountKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityIncrementRandomCavityIncrementLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityProxyRandomCavityProxyLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

lemma cavity_sphericalExp_bound (k : ℕ) (Y : Spin (k+1)) (R : ℝ) :
    sphericalExp k Y R≤Real.exp (|R| *‖Y‖) := by
  simpa [sphericalExp] using sphericalExp_le_mul k R Y 0

lemma cavity_shell_compensator_bound (k : ℕ) (W C K A : ℝ)
    (hK : 0≤K) (hC : |C|≤K) (hW : |W|≤A)
    (z : {z : Spin (k+1) // z∈cavityShell (k+1)}) :
    |W+‖z.val‖^2*C/2|≤A+((k+1:ℕ)+1)*K/2 := by
  apply (abs_add_le _ _).trans
  apply add_le_add hW
  rw [abs_div,abs_mul,abs_of_nonneg (sq_nonneg _)]
  norm_num
  apply div_le_div_of_nonneg_right _ (by norm_num)
  simpa only [Nat.cast_add,Nat.cast_one] using
    ((mul_le_mul_of_nonneg_left hC (sq_nonneg _)).trans
      (mul_le_mul_of_nonneg_right z.prop.2 hK))

theorem cavity_true_shell_linear_lower {S : Type*} [MeasurableSpace S]
    (μ : Measure S) [IsProbabilityMeasure μ] (n k : ℕ)
    (hp : (cavitySphereLaw n (k+1) : Measure (Spin (k+1))) (cavityShell (k+1))≠0)
    (W C : S→ℝ) (Y : S→Spin (k+1))
    (hW : Measurable W) (hC : Measurable C) (hY : Measurable Y)
    {A K D : ℝ} (hA : 0≤A) (hK : 0≤K) (hD : 0≤D)
    (hWA : ∀ s,|W s|≤A) (hCK : ∀ s,|C s|≤K) (hYD : ∀ s,‖Y s‖≤D) :
    Real.log (∫ s,Real.exp (W s+(k+1:ℕ)*C s/2)*
      sphericalExp k (Y s) (Real.sqrt (k+1:ℕ)) ∂μ)-K/2≤
    Real.log (∫ p : S×{z : Spin (k+1) // z∈cavityShell (k+1)},
      Real.exp (W p.1+‖p.2.val‖^2*C p.1/2+inner ℝ (Y p.1) p.2.val)
        ∂μ.prod (cavityShellProbability n (k+1))) := by
  have := cavityShellProbability_probability n (k+1) hp
  let R : ℝ:=Real.sqrt (k+1:ℕ)
  let G : S→ℝ:=fun s=>Real.exp (W s+(k+1:ℕ)*C s/2)*sphericalExp k (Y s) R
  let F : S×{z : Spin (k+1) // z∈cavityShell (k+1)}→ℝ:=fun p=>
    Real.exp (W p.1+‖p.2.val‖^2*C p.1/2+inner ℝ (Y p.1) p.2.val)
  have hbase (s : S) : |W s+(k+1:ℕ)*C s/2|≤A+(k+1:ℕ)*K/2 := by
    apply (abs_add_le _ _).trans
    apply add_le_add (hWA s)
    rw [abs_div,abs_mul,abs_of_nonneg (Nat.cast_nonneg _),abs_of_pos (by norm_num : (0:ℝ)<2)]
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (hCK s) (by positivity)) (by norm_num)
  have hgm : Measurable G :=
    ((hW.add ((hC.const_mul _).div_const _)).exp).mul
      ((sphericalExp_continuous k R).measurable.comp hY)
  have hgi : Integrable G μ := by
    apply Integrable.of_bound hgm.aestronglyMeasurable (Real.exp (A+(k+1:ℕ)*K/2+R*D))
    exact ae_of_all _ fun s=>by
      dsimp [G]
      rw [abs_mul,abs_of_pos (Real.exp_pos _),
        abs_of_nonneg ((show (0:ℝ)≤1 by norm_num).trans (one_le_sphericalExp _ _ _)),Real.exp_add (A+(k+1:ℕ)*K/2) (R*D)]
      apply mul_le_mul
        (Real.exp_le_exp.mpr ((le_abs_self _).trans (hbase s)))
        ((cavity_sphericalExp_bound k (Y s) R).trans (Real.exp_le_exp.mpr _))
        ((by norm_num : (0:ℝ)≤1).trans (one_le_sphericalExp _ _ _)) (Real.exp_pos _).le
      rw [abs_of_nonneg (Real.sqrt_nonneg _)]
      exact mul_le_mul_of_nonneg_left (hYD s) (Real.sqrt_nonneg _)
  have hfm : Measurable F := by
    dsimp [F]
    fun_prop
  have hfb (p : S×{z : Spin (k+1) // z∈cavityShell (k+1)}) :
      |W p.1+‖p.2.val‖^2*C p.1/2+inner ℝ (Y p.1) p.2.val|≤
        A+((k+1:ℕ)+1)*K/2+D*((k+1:ℕ)+1) := by
    apply (abs_add_le _ _).trans
    apply add_le_add (cavity_shell_compensator_bound k _ _ _ _ hK (hCK p.1) (hWA p.1) p.2)
    exact (abs_real_inner_le_norm _ _).trans
      (mul_le_mul (hYD p.1) (cavity_shell_norm_bound (k+1) p.2) (norm_nonneg _) hD)
  have hfi : Integrable F (μ.prod (cavityShellProbability n (k+1))) :=
    cavity_exp_integrable_bound _ (by fun_prop) hfb
  have hgp : 0<∫ s,G s ∂μ := by
    have hbi := cavity_exp_integrable_bound μ (by fun_prop) hbase
    have hpos : 0<∫ s,Real.exp (W s+(k+1:ℕ)*C s/2) ∂μ := by
      simpa only [tiltPartition,one_mul] using tilt_partition_pos μ (v:=fun s=>W s+(k+1:ℕ)*C s/2)
        (hW.add ((hC.const_mul _).div_const _)) (by positivity) hbase 1
    apply hpos.trans_le (integral_mono hbi hgi _)
    intro s
    exact le_mul_of_one_le_right (Real.exp_pos _).le (one_le_sphericalExp _ _ _)
  have hpoint (s : S) : Real.exp (-K/2)*G s≤
      ∫ z,F (s,z) ∂cavityShellProbability n (k+1) := by
    rw [show (∫ z,F (s,z) ∂cavityShellProbability n (k+1))=
      ((cavitySphereLaw n (k+1) : Measure (Spin (k+1))).real (cavityShell (k+1)))⁻¹*
        ∫ z in cavityShell (k+1),Real.exp (W s+‖z‖^2*C s/2+inner ℝ (Y s) z)
          ∂(cavitySphereLaw n (k+1) : Measure (Spin (k+1))) from
      cavityShellProbability_integral n (k+1) (fun z=>Real.exp (W s+‖z‖^2*C s/2+inner ℝ (Y s) z))]
    have hm : 0<(cavitySphereLaw n (k+1) : Measure (Spin (k+1))).real (cavityShell (k+1)) :=
      ENNReal.toReal_pos hp (measure_ne_top _ _)
    have hh:=mul_le_mul_of_nonneg_left
      (cavitySphereLaw_shell_lower n k (W s) (C s) (Y s) (hCK s)) (inv_nonneg.mpr hm.le)
    simpa only [G,R,←mul_assoc,inv_mul_cancel₀ hm.ne',one_mul] using hh
  have hcompare : Real.exp (-K/2)*(∫ s,G s ∂μ)≤∫ p,F p ∂μ.prod (cavityShellProbability n (k+1)) := by
    rw [←integral_const_mul,integral_prod _ hfi]
    exact integral_mono (hgi.const_mul _) hfi.integral_prod_left hpoint
  have hlog:=Real.log_le_log (mul_pos (Real.exp_pos _) hgp) hcompare
  rw [Real.log_mul (Real.exp_pos _).ne' hgp.ne',Real.log_exp] at hlog
  change Real.log (∫ s,G s ∂μ)-K/2≤Real.log (∫ p,F p ∂μ.prod (cavityShellProbability n (k+1)))
  linarith


lemma cavityVectorField_norm_le (M L : ℕ) (a : Fin M→ℝ) (t : ℝ)
    (y : Fin M→Spin L) {A : ℝ} (hA : 0≤A) (ha : ∀ i,|a i|≤A) :
    ‖cavityVectorField M L a t y‖≤|t| *∑ i,A*‖y i‖ := by
  unfold cavityVectorField
  rw [norm_smul,Real.norm_eq_abs]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro i hi
  rw [norm_smul,Real.norm_eq_abs]
  exact mul_le_mul (ha i) le_rfl (norm_nonneg _) hA

lemma cavity_angular_partition {S : Type*} [MeasurableSpace S]
    (μ : Measure S) [IsProbabilityMeasure μ] (M k : ℕ)
    (a : S→Fin M→ℝ) (V : S→ℝ) (ha : Measurable a) (hV : Measurable V)
    (t R : ℝ) {A C : ℝ} (hA : 0≤A) (hC : 0≤C)
    (haB : ∀ s i,|a s i|≤A) (hVB : ∀ s,|V s|≤C) (y : Fin M→Spin (k+1)) :
    (∫ p : S×NormalizedSpin (k+1),Real.exp (V p.1+
      cavityLinearField M (k+1) (a p.1) t (R •p.2.val) y) ∂μ.prod (unitSphereLaw (k+1)))=
    ∫ s,Real.exp (V s)*sphericalExp k (cavityVectorField M (k+1) (a s) t y) R ∂μ := by
  have hm : Measurable (fun p : S×NormalizedSpin (k+1)=>V p.1+
      cavityLinearField M (k+1) (a p.1) t (R •p.2.val) y) := by
    have ham : Measurable (fun p : S×NormalizedSpin (k+1)=>a p.1) := ha.comp measurable_fst
    have hVm : Measurable (fun p : S×NormalizedSpin (k+1)=>V p.1) := hV.comp measurable_fst
    unfold cavityLinearField
    fun_prop
  have hi := cavity_exp_integrable_bound (μ.prod (unitSphereLaw (k+1))) hm
    (C:=|C|+|t| *∑ i,A*|R| *‖y i‖) (fun p=>by
      rw [abs_of_nonneg hC]
      apply (abs_add_le _ _).trans
      apply add_le_add (hVB p.1)
      apply cavityLinearField_abs_bound M (k+1) (a p.1) t _ y hA (haB p.1)
      have hu : ‖p.2.val‖=1 := by simp
      simp only [norm_smul,Real.norm_eq_abs,hu,mul_one,le_refl])
  rw [integral_prod _ hi]
  apply integral_congr_ae
  exact ae_of_all _ fun s=>by
    simp only [cavityLinearField_inner,real_inner_smul_right,Real.exp_add,integral_const_mul,sphericalExp]

lemma cavity_angular_log_integrable {S : Type*} [MeasurableSpace S]
    (μ : Measure S) [IsProbabilityMeasure μ] (M k : ℕ)
    (a : S→Fin M→ℝ) (V : S→ℝ) (ha : Measurable a) (hV : Measurable V)
    (t R : ℝ) {A C : ℝ} (hA : 0≤A) (hC : 0≤C)
    (haB : ∀ s i,|a s i|≤A) (hVB : ∀ s,|V s|≤C) :
    Integrable (fun y : Fin M→Spin (k+1)=>Real.log (∫ s,Real.exp (V s)*
      sphericalExp k (cavityVectorField M (k+1) (a s) t y) R ∂μ))
        (Measure.pi (fun _=>stdGaussian (Spin (k+1)))) := by
  have hz : Measurable (fun p : S×NormalizedSpin (k+1)=>R •p.2.val) := by fun_prop
  have hzB (p : S×NormalizedSpin (k+1)) : ‖R •p.2.val‖≤|R| := by
    have hu : ‖p.2.val‖=1 := by simp
    simp only [norm_smul,Real.norm_eq_abs,hu,mul_one,le_refl]
  have h:=cavity_quadratic_log_integrable (μ.prod (unitSphereLaw (k+1))) M (k+1)
    (fun p=>a p.1) (fun _ _=>0) (fun p=>R •p.2.val) (fun p=>V p.1)
    (ha.comp measurable_fst) measurable_const hz (hV.comp measurable_fst) t 0
    hA (B:=0) (by norm_num) hC (abs_nonneg R)
    (fun p=>haB p.1) (fun _ _=>by simp) hzB (fun p=>hVB p.1)
  simp only [cavityQuadraticField,zero_mul,add_zero] at h
  simpa only [cavity_angular_partition μ M k a V ha hV t R hA hC haB hVB] using h

theorem cavity_expected_shell_lower {S : Type*} [MeasurableSpace S]
    (μ : Measure S) [IsProbabilityMeasure μ] (n k M : ℕ)
    (hp : (cavitySphereLaw n (k+1) : Measure (Spin (k+1))) (cavityShell (k+1))≠0)
    (a b : S→Fin M→ℝ) (W C : S→ℝ)
    (ha : Measurable a) (hb : Measurable b) (hW : Measurable W) (hC : Measurable C)
    (t u : ℝ) {A B E K : ℝ} (hA : 0≤A) (hB : 0≤B) (hE : 0≤E) (hK : 0≤K)
    (haB : ∀ s i,|a s i|≤A) (hbB : ∀ s i,|b s i|≤B)
    (hWE : ∀ s,|W s|≤E) (hCK : ∀ s,|C s|≤K) :
    (∫ y : Fin M→Spin (k+1),Real.log (∫ p : S×{z : Spin (k+1) // z∈cavityShell (k+1)},
      Real.exp (W p.1+‖p.2.val‖^2*C p.1/2+cavityLinearField M (k+1) (a p.1) t p.2.val y+
        cavityQuadraticField M (k+1) (b p.1) u p.2.val y)
        ∂μ.prod (cavityShellProbability n (k+1))) ∂Measure.pi (fun _=>stdGaussian (Spin (k+1))))≥
    (∫ y : Fin M→Spin (k+1),Real.log (∫ s,Real.exp (W s+(k+1:ℕ)*C s/2)*
      sphericalExp k (cavityVectorField M (k+1) (a s) t y) (Real.sqrt (k+1:ℕ)) ∂μ)
      ∂Measure.pi (fun _=>stdGaussian (Spin (k+1))))-K/2-
      Real.exp (2*(E+((k+1:ℕ)+1)*K/2)+t^2*((k+1:ℕ)+1)^2*M*A^2)*
        Real.sqrt (u^2*(((k+1:ℕ)+1)^2)^2*squareGaussianVariance*M*B^2) := by
  have := cavityShellProbability_probability n (k+1) hp
  let U : S×{z : Spin (k+1) // z∈cavityShell (k+1)}→ℝ := fun p=>W p.1+‖p.2.val‖^2*C p.1/2
  have hU : Measurable U := by
    have hmW : Measurable (fun p : S×{z : Spin (k+1) // z∈cavityShell (k+1)}=>W p.1) := hW.comp measurable_fst
    have hmC : Measurable (fun p : S×{z : Spin (k+1) // z∈cavityShell (k+1)}=>C p.1) := hC.comp measurable_fst
    dsimp [U]
    fun_prop
  have hUB (p) : |U p|≤E+((k+1:ℕ)+1)*K/2 :=
    cavity_shell_compensator_bound k _ _ _ _ hK (hCK p.1) (hWE p.1) p.2
  have hdrop:=cavity_true_shell_expected_drop μ n k M hp a b U ha hb hU t u
    hA hB (by positivity) haB hbB hUB
  have hlin : Integrable (fun y : Fin M→Spin (k+1)=>Real.log (∫ p,
      Real.exp (U p+cavityLinearField M (k+1) (a p.1) t p.2.val y)
      ∂μ.prod (cavityShellProbability n (k+1)))) (Measure.pi (fun _=>stdGaussian (Spin (k+1)))) := by
    simpa only [cavityQuadraticField,zero_mul,add_zero] using
      cavity_quadratic_log_integrable (μ.prod (cavityShellProbability n (k+1))) M (k+1)
        (fun p=>a p.1) (fun p=>b p.1) (fun p=>p.2.val) U
        (ha.comp measurable_fst) (hb.comp measurable_fst) measurable_snd.subtype_val hU t 0
        hA hB (by positivity) (by positivity) (fun p=>haB p.1) (fun p=>hbB p.1)
        (fun p=>cavity_shell_norm_bound (k+1) p.2) hUB
  have hVB (s) : |W s+(k+1:ℕ)*C s/2|≤E+(k+1:ℕ)*K/2 := by
    apply (abs_add_le _ _).trans
    apply add_le_add (hWE s)
    rw [abs_div,abs_mul,abs_of_nonneg (Nat.cast_nonneg _),abs_of_pos (by norm_num : (0:ℝ)<2)]
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (hCK s) (by positivity)) (by norm_num)
  have hsph:=cavity_angular_log_integrable μ M k a (fun s=>W s+(k+1:ℕ)*C s/2)
    ha (hW.add ((hC.const_mul _).div_const _)) t (Real.sqrt (k+1:ℕ)) hA (by positivity) haB hVB
  have hcomp:=integral_mono (hsph.sub (integrable_const (K/2))) hlin (fun y=>by
    have hym : Measurable (fun s=>cavityVectorField M (k+1) (a s) t y) := by
      unfold cavityVectorField
      fun_prop
    have h:=cavity_true_shell_linear_lower μ n k hp W C _ hW hC hym hE hK
      (D:=|t| *∑ i,A*‖y i‖) (by positivity) hWE hCK
      (fun s=>cavityVectorField_norm_le M (k+1) (a s) t y hA (haB s))
    simpa only [Pi.sub_apply,U,cavityLinearField_inner] using h)
  simp only [Pi.sub_apply] at hcomp
  rw [integral_sub hsph (integrable_const (K/2)),integral_const,probReal_univ,smul_eq_mul,one_mul] at hcomp
  exact (sub_le_sub_right hcomp _).trans hdrop

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cavity_CavityConditionalIncrement
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceCountDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceCountKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityIncrementRandomCavityIncrementLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityProxyRandomCavityProxyLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

lemma cavityOldIncrement_measurable (n L M : ℕ) (f : Jet3) (a : Fin M→Fin (n+1)→ℝ)
    (W : NormalizedSpin (n+1)→ℝ) (hW : Measurable W) :
    Measurable (fun p : CavityShellSpin n L×(Fin M→Spin L)=>cavityOldIncrement n L M f a W p.2 p.1) := by
  have hj : Measurable (fun p : CavityShellSpin n L×(Fin M→Spin L)=>
      cavityJoinedPatterns (n+1) L M a p.2) := by
    unfold cavityJoinedPatterns
    apply Measurable.of_eval
    intro i
    apply Measurable.of_eval
    intro j
    refine Fin.addCases (fun j=>?_) (fun j=>?_) j
    · simpa only [Fin.addCases_left] using (measurable_const : Measurable (fun _ : CavityShellSpin n L×(Fin M→Spin L)=>a i j))
    · simp only [Fin.addCases_right]
      fun_prop
  have he := (normalizedPatternEnergy_continuous (n+1+L) M f.f).measurable.comp
    (hj.prodMk ((cavityShellSpinEmbedding_measurable n L).comp measurable_fst))
  have hb : Measurable (fun p : CavityShellSpin n L×(Fin M→Spin L)=>
      normalizedPatternEnergy (n+1) M f.f a p.1.1) := (normalizedPatternEnergy_continuous (n+1) M f.f).measurable.comp
    (f:=fun p : CavityShellSpin n L×(Fin M→Spin L)=>(a,p.1.1))
    (measurable_const.prodMk measurable_fst.fst)
  exact (he.sub hb).add (hW.comp measurable_fst.fst)

lemma cavityOldIncrement_bound (n L M : ℕ) (f : Jet3) (a : Fin M→Fin (n+1)→ℝ)
    (W : NormalizedSpin (n+1)→ℝ) {E : ℝ} (hW : ∀ x,|W x|≤E)
    (y : Fin M→Spin L) (p : CavityShellSpin n L) :
    |cavityOldIncrement n L M f a W y p|≤2*M*‖f.f‖+E := by
  apply (abs_add_le _ _).trans
  apply (add_le_add ((abs_sub _ _).trans (add_le_add
    (cavityShellPatternEnergy_bound n L M f.f _ p)
    (normalizedPatternEnergy_bound (n+1) M f.f a p.1))) (hW p.1)).trans_eq
  ring

theorem cavity_conditional_old_increment_lower (n k M : ℕ) (f : Jet3)
    (h1 : HasCompactSupport (f.d1 : ℝ→ℝ)) (h2 : HasCompactSupport (f.d2 : ℝ→ℝ))
    (h3 : HasCompactSupport (f.d3 : ℝ→ℝ)) (hn : 2*((k+1)+1)≤n+1)
    (hp : (cavitySphereLaw n (k+1) : Measure (Spin (k+1))) (cavityShell (k+1))≠0)
    (μ : Measure (NormalizedSpin (n+1))) [IsProbabilityMeasure μ]
    (a : Fin M→Fin (n+1)→ℝ) (W : NormalizedSpin (n+1)→ℝ)
    (hW : Measurable W) {E : ℝ} (hE : 0≤E) (hWE : ∀ x,|W x|≤E) :
    let K : ℝ:=M/(n+1:ℕ)*‖f.dilationMark h1‖
    let A : NormalizedSpin (n+1)→Fin M→ℝ:=fun x i=>f.d1 (∑ j,a i j*x.val j)
    (∫ y : Fin M→Spin (k+1),Real.log (∫ p,Real.exp (cavityOldIncrement n (k+1) M f a W y p)
      ∂μ.prod (cavityShellProbability n (k+1))) ∂Measure.pi (fun _=>stdGaussian (Spin (k+1))))≥
    (∫ y : Fin M→Spin (k+1),Real.log (∫ x,Real.exp (W x+(k+1:ℕ)*bulkC (n+1) M f a x/2)*
      sphericalExp k (cavityVectorField M (k+1) (A x) (Real.sqrt (n+1:ℕ))⁻¹ y)
        (Real.sqrt (k+1:ℕ)) ∂μ) ∂Measure.pi (fun _=>stdGaussian (Spin (k+1))))-K/2-
      Real.exp (2*(E+((k+1:ℕ)+1)*K/2)+(Real.sqrt (n+1:ℕ))⁻¹^2*((k+1:ℕ)+1)^2*M*‖f.d1‖^2)*
        Real.sqrt ((1/(2*(n+1:ℕ)))^2*(((k+1:ℕ)+1)^2)^2*squareGaussianVariance*M*‖f.d2‖^2)-
      (∫ y : Fin M→Spin (k+1),∑ i,cavityRemainderMajorant
        (cavityRemainderCoefficients f h1 h2 h3 (k+1) ((k+1)+1)) (n+1:ℕ) ‖y i‖
        ∂Measure.pi (fun _=>stdGaussian (Spin (k+1)))) := by
  dsimp only
  have := cavityShellProbability_probability n (k+1) hp
  let A : NormalizedSpin (n+1)→Fin M→ℝ:=fun x i=>f.d1 (∑ j,a i j*x.val j)
  let B : NormalizedSpin (n+1)→Fin M→ℝ:=fun x i=>f.d2 (∑ j,a i j*x.val j)
  let C : NormalizedSpin (n+1)→ℝ:=fun x=>bulkC (n+1) M f a x
  let K : ℝ:=M/(n+1:ℕ)*‖f.dilationMark h1‖
  have hK : 0≤K := by dsimp [K]; positivity
  have hA : Measurable A := by have hm:=f.d1.continuous.measurable; unfold A; fun_prop
  have hB : Measurable B := by have hm:=f.d2.continuous.measurable; unfold B; fun_prop
  have hC : Measurable C := (bulkC_measurable n M f).comp
    (f:=fun x : NormalizedSpin (n+1)=>((a,0),x)) (measurable_const.prodMk measurable_id)
  have hAB (x) (i) : |A x i|≤‖f.d1‖ := f.d1.norm_coe_le_norm _
  have hBB (x) (i) : |B x i|≤‖f.d2‖ := f.d2.norm_coe_le_norm _
  have hCK (x) : |C x|≤K := bulkC_bound n M f h1 (a,0) x
  let U : CavityShellSpin n (k+1)→ℝ:=fun p=>W p.1+‖p.2.val‖^2*C p.1/2
  let V : (Fin M→Spin (k+1))→CavityShellSpin n (k+1)→ℝ:=fun y p=>U p+
    cavityLinearField M (k+1) (A p.1) (Real.sqrt (n+1:ℕ))⁻¹ p.2.val y+
    cavityQuadraticField M (k+1) (B p.1) (1/(2*(n+1:ℕ))) p.2.val y
  have hU : Measurable U := by
    have hw : Measurable (fun p : CavityShellSpin n (k+1)=>W p.1) := hW.comp measurable_fst
    have hc : Measurable (fun p : CavityShellSpin n (k+1)=>C p.1) := hC.comp measurable_fst
    unfold U
    fun_prop
  have hUB (p) : |U p|≤E+((k+1:ℕ)+1)*K/2 :=
    cavity_shell_compensator_bound k _ _ _ _ hK (hCK p.1) (hWE p.1) p.2
  have hVi : Integrable (fun y=>Real.log (∫ p,Real.exp (V y p)
      ∂μ.prod (cavityShellProbability n (k+1)))) (Measure.pi (fun _=>stdGaussian (Spin (k+1)))) :=
    cavity_quadratic_log_integrable (μ.prod (cavityShellProbability n (k+1))) M (k+1)
      (fun p=>A p.1) (fun p=>B p.1) (fun p=>p.2.val) U
      (hA.comp measurable_fst) (hB.comp measurable_fst) measurable_snd.subtype_val hU _ _
      (norm_nonneg _) (norm_nonneg _) (by positivity) (by positivity)
      (fun p=>hAB p.1) (fun p=>hBB p.1) (fun p=>cavity_shell_norm_bound (k+1) p.2) hUB
  have hFi := cavity_log_integrable_of_bound (μ.prod (cavityShellProbability n (k+1)))
    (Measure.pi (fun _ : Fin M=>stdGaussian (Spin (k+1))))
    (fun p=>cavityOldIncrement n (k+1) M f a W p.2 p.1)
    (cavityOldIncrement_measurable n (k+1) M f a W hW)
    (fun _=>2*M*‖f.f‖+E) (integrable_const _) (fun _=>by positivity)
    (fun p y=>cavityOldIncrement_bound n (k+1) M f a W hWE y p)
  let R : (Fin M→Spin (k+1))→ℝ:=fun y=>∑ i,cavityRemainderMajorant
    (cavityRemainderCoefficients f h1 h2 h3 (k+1) ((k+1)+1)) (n+1:ℕ) ‖y i‖
  have hRi : Integrable R (Measure.pi (fun _=>stdGaussian (Spin (k+1)))) := by
    apply integrable_finsetSum
    intro i _
    exact ((measurePreserving_eval (fun _ : Fin M=>stdGaussian (Spin (k+1))) i).integrable_comp
      (cavityRemainderMajorant_integrable _ _ _).aestronglyMeasurable).mpr
        (cavityRemainderMajorant_integrable _ _ _)
  have hpoint (y : Fin M→Spin (k+1)) : Real.log (∫ p,Real.exp (V y p)
      ∂μ.prod (cavityShellProbability n (k+1)))-R y≤
      Real.log (∫ p,Real.exp (cavityOldIncrement n (k+1) M f a W y p)
        ∂μ.prod (cavityShellProbability n (k+1))) := by
    have hv : Measurable (V y) := by
      dsimp [V]
      unfold cavityLinearField cavityQuadraticField
      fun_prop
    have herr (p : CavityShellSpin n (k+1)) :
        |cavityOldIncrement n (k+1) M f a W y p-V y p|≤R y := by
      have hh:=cavity_true_shell_expansion n (k+1) M f h1 h2 h3 hn a y p
      convert hh using 1 <;> try dsimp [cavityOldIncrement,V,U,A,B,C,cavityShellTaylorModel]
      · congr 1
        ring
      · simp only [R,Nat.cast_add,Nat.cast_one]
    have hh:=cavity_log_uniform_change (μ.prod (cavityShellProbability n (k+1)))
      ((cavityOldIncrement_measurable n (k+1) M f a W hW).comp
        (measurable_id.prodMk measurable_const)) hv (A:=2*M*‖f.f‖+E) (by positivity)
      (cavityOldIncrement_bound n (k+1) M f a W hWE y) herr
    simp only [Function.comp_def,id_eq] at hh
    linarith [(abs_le.mp hh).1]
  have hi := integral_mono (hVi.sub hRi) hFi hpoint
  simp only [Pi.sub_apply] at hi
  rw [integral_sub hVi hRi] at hi
  have hs := cavity_expected_shell_lower μ n k M hp A B W C hA hB hW hC
    (Real.sqrt (n+1:ℕ))⁻¹ (1/(2*(n+1:ℕ))) (norm_nonneg _) (norm_nonneg _) hE hK hAB hBB hWE hCK
  exact (sub_le_sub_right hs _).trans hi

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cavity_CavityNormalizedIncrement
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceCountDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceCountKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityIncrementRandomCavityIncrementLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityProxyRandomCavityProxyLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology BigOperators BoundedContinuousFunction

lemma cavity_actual_old_log_identity (n L M : ℕ) (f : Jet3) (v : ℕ→ℝ)
    (a : BulkDisorder (n+1) M)
    (hp : (cavitySphereLaw n L : Measure (Spin L)) (cavityShell L)≠0)
    (W : NormalizedSpin (n+1)→ℝ) (hW : Measurable W)
    {E : ℝ} (hE : 0≤E) (hWE : ∀ x,|W x|≤E) (y : Fin M→Spin L) :
    Real.log (∫ p,Real.exp (cavityOldJoinedHamiltonian n L M f v a W y p)
      ∂cavityShellBaseLaw n L)-bulkLogPartition n M f.f v a.1 a.2=
    Real.log (∫ p,Real.exp (cavityOldIncrement n L M f a.1 W y p)
      ∂(tiltLaw (unitSphereLaw (n+1)) (bulkHamiltonian (n+1) M f.f v a.1 a.2) 1).prod
        (cavityShellProbability n L)) := by
  have hm : Measurable (cavityOldIncrement n L M f a.1 W y) := by
    have hm0 := cavityOldIncrement_measurable n L M f a.1 W hW
    exact Measurable.of_uncurry_right
      (f:=fun p y=>cavityOldIncrement n L M f a.1 W y p) hm0
  have hB : 0≤2*M*‖f.f‖+E := by positivity
  have hVB : ∀ p,|cavityOldIncrement n L M f a.1 W y p|≤2*M*‖f.f‖+E :=
    cavityOldIncrement_bound n L M f a.1 W hWE y
  have hh:=cavity_actual_bulk_log_factorization n L M f.f v a hp
    (cavityOldIncrement n L M f a.1 W y) hm hB hVB
  apply Eq.trans _ hh
  congr 3
  funext p
  congr 1
  unfold cavityOldJoinedHamiltonian bulkHamiltonian cavityOldIncrement
  ring

theorem cavity_normalized_old_increment_lower (n k M : ℕ) (f : Jet3)
    (h1 : HasCompactSupport (f.d1 : ℝ→ℝ)) (h2 : HasCompactSupport (f.d2 : ℝ→ℝ))
    (h3 : HasCompactSupport (f.d3 : ℝ→ℝ)) (hn : 2*((k+1)+1)≤n+1)
    (hp : (cavitySphereLaw n (k+1) : Measure (Spin (k+1))) (cavityShell (k+1))≠0)
    (v : ℕ→ℝ) (a : BulkDisorder (n+1) M) (W : NormalizedSpin (n+1)→ℝ)
    (hW : Measurable W) {E : ℝ} (hE : 0≤E) (hWE : ∀ x,|W x|≤E) :
    let μ := tiltLaw (unitSphereLaw (n+1)) (bulkHamiltonian (n+1) M f.f v a.1 a.2) 1
    let K : ℝ:=M/(n+1:ℕ)*‖f.dilationMark h1‖
    let A : NormalizedSpin (n+1)→Fin M→ℝ:=fun x i=>f.d1 (∑ j,a.1 i j*x.val j)
    (∫ y : Fin M→Spin (k+1),(Real.log (∫ p,Real.exp (cavityOldJoinedHamiltonian n (k+1) M f v a W y p)
      ∂cavityShellBaseLaw n (k+1))-bulkLogPartition n M f.f v a.1 a.2) ∂Measure.pi (fun _=>stdGaussian (Spin (k+1))))≥
    (∫ y : Fin M→Spin (k+1),Real.log (∫ x,Real.exp (W x+(k+1:ℕ)*bulkC (n+1) M f a.1 x/2)*
      sphericalExp k (cavityVectorField M (k+1) (A x) (Real.sqrt (n+1:ℕ))⁻¹ y)
        (Real.sqrt (k+1:ℕ)) ∂μ) ∂Measure.pi (fun _=>stdGaussian (Spin (k+1))))-K/2-
      Real.exp (2*(E+((k+1:ℕ)+1)*K/2)+(Real.sqrt (n+1:ℕ))⁻¹^2*((k+1:ℕ)+1)^2*M*‖f.d1‖^2)*
        Real.sqrt ((1/(2*(n+1:ℕ)))^2*(((k+1:ℕ)+1)^2)^2*squareGaussianVariance*M*‖f.d2‖^2)-
      (∫ y : Fin M→Spin (k+1),∑ i,cavityRemainderMajorant
        (cavityRemainderCoefficients f h1 h2 h3 (k+1) ((k+1)+1)) (n+1:ℕ) ‖y i‖
        ∂Measure.pi (fun _=>stdGaussian (Spin (k+1)))) := by
  have := tilt_law_probability (unitSphereLaw (n+1))
    (bulkHamiltonian_section_measurable (n+1) M f.f v a)
    (show 0≤M*‖f.f‖+bulkFeatureBound (n+1) v*‖a.2‖ from by
      apply add_nonneg (by positivity)
      apply mul_nonneg
      · unfold bulkFeatureBound
        positivity
      · positivity)
    (bulkHamiltonian_bound (n+1) M f.f v a) 1
  dsimp only
  simp_rw [cavity_actual_old_log_identity n (k+1) M f v a hp W hW hE hWE]
  exact cavity_conditional_old_increment_lower n k M f h1 h2 h3 hn hp
    (tiltLaw (unitSphereLaw (n+1)) (bulkHamiltonian (n+1) M f.f v a.1 a.2) 1)
    a.1 W hW hE hWE

end SphericalPerceptronFreeEnergy
end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cavity_CavityProductLaw
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.bulkFiniteReplicaLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceCountDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceCountKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityIncrementRandomCavityIncrementLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityProxyRandomCavityProxyLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped Topology BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

lemma cavity_integral_preserving {A B E : Type*} [MeasurableSpace A] [MeasurableSpace B]
    [NormedAddCommGroup E] [NormedSpace ℝ E] (μ : Measure A) (ν : Measure B)
    (F : A→B) (hF : MeasurePreserving F μ ν) (g : B→E) (hg : AEStronglyMeasurable g ν) :
    (∫ a,g (F a) ∂μ)=∫ b,g b ∂ν := by
  rw [←hF.map_eq] at hg ⊢
  exact (integral_map hF.measurable.aemeasurable hg).symm

lemma cavityShellPatternEnergy_joint_measurable (n L M : ℕ) (f : ℝ→ᵇℝ) :
    Measurable (fun p : (Fin M→Fin (n+1+L)→ℝ)×CavityShellSpin n L=>
      cavityShellPatternEnergy n L M f p.1 p.2) := by
  change Measurable (fun p : (Fin M→Fin (n+1+L)→ℝ)×CavityShellSpin n L=>normalizedPatternEnergy (n+1+L) M f p.1 (cavityShellSpinEmbedding n L p.2))
  exact (normalizedPatternEnergy_continuous (n+1+L) M f).measurable.comp
    (f:=fun p : (Fin M→Fin (n+1+L)→ℝ)×CavityShellSpin n L=>(p.1,cavityShellSpinEmbedding n L p.2))
    (measurable_fst.prodMk ((cavityShellSpinEmbedding_measurable n L).comp measurable_snd))

end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cavity_CavityIncrementLaw
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceCountDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceCountKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped Topology BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

lemma cavityProxyHamiltonian_measurable (n L M d : ℕ) (f : Jet3) (v : ℕ→ℝ) :
    Measurable (fun p : CavityProxyRandom n L M d×CavityShellSpin n L=>cavityProxyHamiltonian n L M d f v p.1 p.2) := by
  have hj : Measurable (fun p : CavityProxyRandom n L M d×CavityShellSpin n L=>
      cavityJoinedPatterns (n+1) L M p.1.1.1 p.1.2.2) :=
    (cavityJoinedPatterns_preserving (n+1) L M).measurable.comp
      (f:=fun p : CavityProxyRandom n L M d×CavityShellSpin n L=>(p.1.1.1,p.1.2.2))
      (measurable_fst.fst.fst.prodMk measurable_fst.snd.snd)
  have hs : Measurable (fun p : CavityProxyRandom n L M d×CavityShellSpin n L=>
      cavityShellPatternEnergy n L M f.f (cavityJoinedPatterns (n+1) L M p.1.1.1 p.1.2.2) p.2) :=
    (cavityShellPatternEnergy_joint_measurable n L M f.f).comp
      (f:=fun p : CavityProxyRandom n L M d×CavityShellSpin n L=>(cavityJoinedPatterns (n+1) L M p.1.1.1 p.1.2.2,p.2))
      (hj.prodMk measurable_snd)
  have hm : Measurable (fun p : CavityProxyRandom n L M d×CavityShellSpin n L=>
      inner ℝ (bulkFeature (n+1) v p.2.1) p.1.1.2) :=
    (((bulkFeature_continuous (n+1) v).measurable.comp
      (f:=fun p : CavityProxyRandom n L M d×CavityShellSpin n L=>p.2.1) measurable_snd.fst).inner measurable_fst.fst.snd)
  have hn : Measurable (fun p : CavityProxyRandom n L M d×CavityShellSpin n L=>
      normalizedPatternEnergy (n+1) d f.f p.1.2.1 p.2.1) :=
    (normalizedPatternEnergy_continuous (n+1) d f.f).measurable.comp
      (f:=fun p : CavityProxyRandom n L M d×CavityShellSpin n L=>(p.1.2.1,p.2.1))
      (measurable_fst.snd.fst.prodMk measurable_snd.fst)
  unfold cavityProxyHamiltonian cavityOldJoinedHamiltonian
  exact (hs.add hm).add hn

lemma cavityProxyHamiltonian_bound (n L M d : ℕ) (f : Jet3) (v : ℕ→ℝ)
    (p : CavityProxyRandom n L M d) (s : CavityShellSpin n L) :
    |cavityProxyHamiltonian n L M d f v p s|≤(M+d)*‖f.f‖+bulkFeatureBound (n+1) v*‖p.1.2‖ := by
  unfold cavityProxyHamiltonian cavityOldJoinedHamiltonian
  exact ((abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans
    (add_le_add (cavityShellPatternEnergy_bound n L M f.f _ s)
      (by simpa only [bulkFeature_norm] using abs_real_inner_le_norm (bulkFeature (n+1) v s.1) p.1.2)))
        (normalizedPatternEnergy_bound (n+1) d f.f _ _))).trans_eq (by ring)

lemma cavityProxyLog_integrable (n L M d : ℕ) (f : Jet3) (v : ℕ→ℝ)
    (hp : (cavitySphereLaw n L : Measure (Spin L)) (cavityShell L)≠0) :
    Integrable (cavityProxyLog n L M d f v) (cavityProxyLaw n L M d) := by
  let :=cavityShellBaseLaw_probability n L hp
  have hb : Integrable (fun p : BulkDisorder (n+1) M=>‖p.2‖) (bulkDisorderLaw (n+1) M) :=
    (IsGaussian.integrable_id (μ:=stdGaussian (BulkMark (n+1)))).norm.comp_snd (finitePatternRowsLaw (n+1) M)
  have hg : Integrable (fun p : CavityProxyRandom n L M d=>‖p.1.2‖) (cavityProxyLaw n L M d) :=
    hb.comp_fst ((finitePatternRowsLaw (n+1) d).prod (Measure.pi fun _ : Fin M=>stdGaussian (Spin L)))
  have hm : Measurable (fun p : CavityShellSpin n L×CavityProxyRandom n L M d=>
      cavityProxyHamiltonian n L M d f v p.2 p.1) :=
    (cavityProxyHamiltonian_measurable n L M d f v).comp
      (f:=fun p : CavityShellSpin n L×CavityProxyRandom n L M d=>(p.2,p.1)) measurable_swap
  unfold cavityProxyLog
  apply cavity_log_integrable_of_bound (cavityShellBaseLaw n L) (cavityProxyLaw n L M d)
    (fun p=>cavityProxyHamiltonian n L M d f v p.2 p.1)
    hm
    (fun p=>(M+d)*‖f.f‖+bulkFeatureBound (n+1) v*‖p.1.2‖)
    ((integrable_const _).add (hg.const_mul _))
    (fun p=>by unfold bulkFeatureBound; positivity)
  intro s p
  exact cavityProxyHamiltonian_bound n L M d f v p s

lemma cavityProxyLog_section_integrable (n L M d : ℕ) (f : Jet3) (v : ℕ→ℝ)
    (hp : (cavitySphereLaw n L : Measure (Spin L)) (cavityShell L)≠0)
    (a : BulkDisorder (n+1) M) (b : Fin d→Fin (n+1)→ℝ) :
    Integrable (fun y=>cavityProxyLog n L M d f v (a,b,y)) (Measure.pi fun _ : Fin M=>stdGaussian (Spin L)) := by
  let :=cavityShellBaseLaw_probability n L hp
  have hm : Measurable (fun p : CavityShellSpin n L×(Fin M→Spin L)=>
      cavityProxyHamiltonian n L M d f v (a,b,p.2) p.1) :=
    (cavityProxyHamiltonian_measurable n L M d f v).comp
      (f:=fun p : CavityShellSpin n L×(Fin M→Spin L)=>((a,b,p.2),p.1))
      ((measurable_const.prodMk (measurable_const.prodMk measurable_snd)).prodMk measurable_fst)
  unfold cavityProxyLog
  apply cavity_log_integrable_of_bound (cavityShellBaseLaw n L) (Measure.pi fun _ : Fin M=>stdGaussian (Spin L))
    (fun p=>cavityProxyHamiltonian n L M d f v (a,b,p.2) p.1)
    hm
    (fun _=>(M+d)*‖f.f‖+bulkFeatureBound (n+1) v*‖a.2‖) (integrable_const _)
    (fun _=>by unfold bulkFeatureBound; positivity)
  intro s y
  exact cavityProxyHamiltonian_bound n L M d f v (a,b,y) s
end SphericalPerceptronFreeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ061_PF.Perceptron_Cavity_CavityOldExpectation
attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceCountDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceCountKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped Topology BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

lemma cavity_three_integral {A B C : Type*} [MeasurableSpace A] [MeasurableSpace B]
    [MeasurableSpace C] (μ : Measure A) (ν : Measure B) (ρ : Measure C)
    [SFinite μ] [SFinite ν] [SFinite ρ] (F : A×B×C→ℝ)
    (hF : Integrable F (μ.prod (ν.prod ρ))) :
    (∫ p,F p ∂μ.prod (ν.prod ρ))=∫ a,∫ b,∫ c,F (a,b,c) ∂ρ ∂ν ∂μ := by
  rw [integral_prod _ hF]
  apply integral_congr_ae
  filter_upwards [hF.prod_right_ae] with a ha
  exact integral_prod _ ha

lemma cavity_three_integral_compare {A B C : Type*} [MeasurableSpace A] [MeasurableSpace B]
    [MeasurableSpace C] (μ : Measure A) (ν : Measure B) (ρ : Measure C)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] [IsProbabilityMeasure ρ]
    (F G : A×B×C→ℝ) (H : A→ℝ) (e : ℝ)
    (hF : Integrable F (μ.prod (ν.prod ρ))) (hG : Integrable G (μ.prod (ν.prod ρ)))
    (hH : Integrable H μ)
    (h : ∀ a b,(∫ c,G (a,b,c) ∂ρ)-H a-e≤∫ c,F (a,b,c) ∂ρ) :
    (∫ p,G p ∂μ.prod (ν.prod ρ))-(∫ a,H a ∂μ)-e≤∫ p,F p ∂μ.prod (ν.prod ρ) := by
  have hp:=measurePreserving_prodAssoc μ ν ρ
  have hFi:= (hp.integrable_comp hF.aestronglyMeasurable).mpr hF
  have hGi:= (hp.integrable_comp hG.aestronglyMeasurable).mpr hG
  have hHi:=hH.comp_fst ν
  have hi:=integral_mono ((hGi.integral_prod_left.sub hHi).sub (integrable_const e))
    hFi.integral_prod_left (fun p=>h p.1 p.2)
  erw [integral_sub (hGi.integral_prod_left.sub hHi) (integrable_const e),
    integral_sub hGi.integral_prod_left hHi,integral_const,probReal_univ,one_smul,
    integral_fun_fst,probReal_univ,one_smul,←integral_prod _ hGi,←integral_prod _ hFi] at hi
  have hfe:=cavity_integral_preserving _ _ _ hp F hF.aestronglyMeasurable
  have hge:=cavity_integral_preserving _ _ _ hp G hG.aestronglyMeasurable
  simp only [Function.comp_def] at hi
  rw [hfe,hge] at hi
  exact hi

lemma cavitySplitLog_proxy_integrable (n k M d : ℕ) (f : Jet3)
    (hf : HasCompactSupport (f.d1 : ℝ→ℝ)) (v : ℕ→ℝ) :
    Integrable (fun p : CavityProxyRandom n (k+1) M d=>Real.log (cavitySplitPartition k d n M f v (p.1,p.2.2,p.2.1)))
      (cavityProxyLaw n (k+1) M d) := by
  have : IsProbabilityMeasure (finitePatternRowsLaw (n+1) d) := by first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
  have : IsProbabilityMeasure (Measure.pi fun _ : Fin M=>stdGaussian (Spin (k+1))) := by first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
  have : SFinite (finitePatternRowsLaw (n+1) d) := inferInstance
  have : SFinite (Measure.pi fun _ : Fin M=>stdGaussian (Spin (k+1))) := inferInstance
  have hp:=(MeasurePreserving.id (bulkDisorderLaw (n+1) M)).prod
    (Measure.measurePreserving_swap (μ:=finitePatternRowsLaw (n+1) d)
      (ν:=Measure.pi fun _ : Fin M=>stdGaussian (Spin (k+1))))
  exact (hp.integrable_comp (cavitySplitPartition_measurable k d n M f v).log.aestronglyMeasurable).mpr
    (cavitySplitLog_integrable k d n M f hf v)

lemma cavity_proxy_conditional_lower (n k M d : ℕ) (f : Jet3)
    (h1 : HasCompactSupport (f.d1 : ℝ→ℝ)) (h2 : HasCompactSupport (f.d2 : ℝ→ℝ))
    (h3 : HasCompactSupport (f.d3 : ℝ→ℝ)) (hn : 2*((k+1)+1)≤n+1)
    (hp : (cavitySphereLaw n (k+1) : Measure (Spin (k+1))) (cavityShell (k+1))≠0) (v : ℕ→ℝ)
    (a : BulkDisorder (n+1) M) (b : Fin d→Fin (n+1)→ℝ) :
    (∫ y, Real.log (cavitySplitPartition k d n M f v (a,y,b)) ∂Measure.pi (fun _ : Fin M=>stdGaussian (Spin (k+1))))
      -(-bulkLogPartition n M f.f v a.1 a.2)-cavityOldError n k M d f h1 h2 h3≤
      ∫ y,cavityProxyLog n (k+1) M d f v (a,b,y) ∂Measure.pi (fun _ : Fin M=>stdGaussian (Spin (k+1))) := by
  have hw : Measurable (normalizedPatternEnergy (n+1) d f.f b) :=
    (normalizedPatternEnergy_continuous (n+1) d f.f).measurable.comp (f:=fun x : NormalizedSpin (n+1)=>(b,x)) (measurable_const.prodMk measurable_id)
  have hi:= cavity_normalized_old_increment_lower n k M f h1 h2 h3 hn hp v a
    (normalizedPatternEnergy (n+1) d f.f b) hw (by positivity : 0≤d*‖f.f‖)
    (normalizedPatternEnergy_bound (n+1) d f.f b)
  dsimp only at hi
  have hsec:=cavityProxyLog_section_integrable n (k+1) M d f v hp a b
  change _≤∫ y,cavityProxyLog n (k+1) M d f v (a,b,y)-bulkLogPartition n M f.f v a.1 a.2 ∂Measure.pi (fun _ : Fin M=>stdGaussian (Spin (k+1))) at hi
  rw [integral_sub hsec (integrable_const _),integral_const,probReal_univ,one_smul] at hi
  dsimp only [cavityOldError]
  change (∫ y,Real.log (cavitySplitPartition k d n M f v (a,y,b)) ∂Measure.pi (fun _=>stdGaussian (Spin (k+1))))-_-_-_≤_ at hi
  linarith

lemma cavity_proxy_expected_lower_oai (n k M d : ℕ) (f : Jet3)
    (h1 : HasCompactSupport (f.d1 : ℝ→ℝ)) (h2 : HasCompactSupport (f.d2 : ℝ→ℝ))
    (h3 : HasCompactSupport (f.d3 : ℝ→ℝ)) (hn : 2*((k+1)+1)≤n+1)
    (hp : (cavitySphereLaw n (k+1) : Measure (Spin (k+1))) (cavityShell (k+1))≠0) (v : ℕ→ℝ) :
    cavityBulkFullLog k d n M f v+bulkExpectedLog n M f.f v-cavityOldError n k M d f h1 h2 h3≤
      ∫ p,cavityProxyLog n (k+1) M d f v p ∂cavityProxyLaw n (k+1) M d := by
  let F:=cavityProxyLog n (k+1) M d f v
  let G:=fun p : CavityProxyRandom n (k+1) M d=>Real.log (cavitySplitPartition k d n M f v (p.1,p.2.2,p.2.1))
  let H:=fun a : BulkDisorder (n+1) M=> -bulkLogPartition n M f.f v a.1 a.2
  have hFi:=cavityProxyLog_integrable n (k+1) M d f v hp
  have hGi:=cavitySplitLog_proxy_integrable n k M d f h1 v
  have hHi:=((bulkLogPartition_memLp n M f.f v).integrable (by norm_num)).neg
  have hi:=cavity_three_integral_compare (bulkDisorderLaw (n+1) M) (finitePatternRowsLaw (n+1) d)
    (Measure.pi fun _ : Fin M=>stdGaussian (Spin (k+1))) F G H (cavityOldError n k M d f h1 h2 h3)
    hFi hGi hHi (fun a b=>?_)
  · have he: (∫ p,G p ∂cavityProxyLaw n (k+1) M d)=cavityBulkFullLog k d n M f v := by
      unfold cavityProxyLaw
      rw [cavity_three_integral _ _ _ G hGi,cavityBulkFullLog_split k d n M f h1 v]
    have hh: (∫ a,H a ∂bulkDisorderLaw (n+1) M)= -bulkExpectedLog n M f.f v := integral_neg _
    change (∫ p,G p ∂cavityProxyLaw n (k+1) M d)-(∫ a,H a ∂bulkDisorderLaw (n+1) M)-_≤_ at hi
    rw [he,hh,sub_neg_eq_add] at hi
    exact hi
  · exact cavity_proxy_conditional_lower n k M d f h1 h2 h3 hn hp v a b


end SphericalPerceptronFreeEnergy

end

end OAI
end

theorem solution : type_of% @OAI.SphericalPerceptronFreeEnergy.cavity_proxy_expected_lower_oai := @OAI.SphericalPerceptronFreeEnergy.cavity_proxy_expected_lower_oai
