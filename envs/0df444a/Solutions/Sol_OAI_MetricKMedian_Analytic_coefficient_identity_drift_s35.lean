-- Prove2me | solution 1 for OAI.MetricKMedian.Analytic.coefficient_identity_drift_s35
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T10:48:55.638519+00:00
-- url     : https://prove2.me/submissions/c408ade3-900d-4117-aaaa-fb249802b173

import Mathlib
import Definitions.Def_OAIQ035K000

section
-- module Solutions.OAIQ035_KM.KMedian_Analysis_Coefficients
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section

namespace MetricKMedian.Analytic

theorem exp_integrable (x : ℝ) :
    IntervalIntegrable (fun t : ℝ => Real.exp (-t * x)) MeasureTheory.volume 0 1 := by
  apply Continuous.intervalIntegrable
  fun_prop

theorem texp_integrable (x : ℝ) :
    IntervalIntegrable (fun t : ℝ => t * Real.exp (-t * x)) MeasureTheory.volume 0 1 := by
  apply Continuous.intervalIntegrable
  fun_prop

private theorem exp_derivative_integral (x : ℝ) :
    -x * (∫ t : ℝ in 0..1, Real.exp (-t * x)) = Real.exp (-x) - 1 := by
  rw [← intervalIntegral.integral_const_mul]
  have hderiv : ∀ t : ℝ, HasDerivAt (fun t : ℝ => Real.exp (-t * x))
      (-x * Real.exp (-t * x)) t := by
    intro t
    simpa only [Pi.neg_apply, id_eq, neg_mul, one_mul, mul_one, mul_neg, mul_comm]
      using (((hasDerivAt_id t).neg.mul_const x).exp)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hderiv t)]
  · simp
  · exact (exp_integrable x).const_mul _

private theorem texp_derivative_integral (x : ℝ) :
    (∫ t : ℝ in 0..1, Real.exp (-t * x)) - x * P x = Real.exp (-x) := by
  rw [P, ← intervalIntegral.integral_const_mul,
    ← intervalIntegral.integral_sub (exp_integrable x) ((texp_integrable x).const_mul x)]
  have hderiv : ∀ t : ℝ, HasDerivAt (fun t : ℝ => t * Real.exp (-t * x))
      (Real.exp (-t * x) - x * (t * Real.exp (-t * x))) t := by
    intro t
    have he : HasDerivAt (fun t : ℝ => Real.exp (-t * x))
        (-x * Real.exp (-t * x)) t := by
      simpa only [Pi.neg_apply, id_eq, neg_mul, one_mul, mul_one, mul_neg, mul_comm]
        using (((hasDerivAt_id t).neg.mul_const x).exp)
    convert (hasDerivAt_id t).mul he using 1 <;> try rfl
    simp only [id_eq]
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hderiv t)]
  · simp
  · exact (exp_integrable x).sub ((texp_integrable x).const_mul x)

theorem A_eq (x : ℝ) :
    A x = 1 + 2 * (1 - ∫ t : ℝ in 0..1, Real.exp (-t * x)) := by
  rw [A, intervalIntegral.integral_sub (intervalIntegrable_const) (exp_integrable x)]
  simp

theorem coefficient_identity (x : ℝ) :
    (1 + x) * (A x - 1) = 2 * x * (1 - P x) := by
  rw [A_eq]
  have h₁ := exp_derivative_integral x
  have h₂ := texp_derivative_integral x
  nlinarith

theorem drift_identity (x : ℝ) :
    (1 + x) * A x + x * B x - 1 = 3 * x := by
  have h := coefficient_identity x
  unfold B
  nlinarith

end MetricKMedian.Analytic


end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Geometry_MomentAnalysis
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.Analytic

open MeasureTheory Set Filter
open scoped Topology Filter Interval

theorem moment_integrable (n : ℕ) (x : ℝ) :
    IntervalIntegrable (fun t : ℝ => t^n*Real.exp (-t*x)) volume 0 1 := by
  apply Continuous.intervalIntegrable
  fun_prop

private theorem kernel_deriv (n : ℕ) (t x : ℝ) :
    HasDerivAt (fun z : ℝ => t^n*Real.exp (-t*z)) (-t^(n+1)*Real.exp (-t*x)) x := by
  have h := (((hasDerivAt_id x).const_mul (-t)).exp).const_mul (t^n)
  convert h using 1 <;> try rfl
  simp only [id_eq, mul_one, pow_succ]
  ring

theorem hasDerivAt_moment (n : ℕ) (x : ℝ) :
    HasDerivAt (moment n) (-moment (n+1) x) x := by
  have hmeas : ∀ᶠ z : ℝ in 𝓝 x,
      AEStronglyMeasurable (fun t : ℝ => t^n*Real.exp (-t*z)) (volume.restrict (Ι 0 1)) := by
    apply Filter.Eventually.of_forall
    intro z
    exact (show Continuous (fun t : ℝ => t^n*Real.exp (-t*z)) by fun_prop).aestronglyMeasurable
  have hmeas' : AEStronglyMeasurable (fun t : ℝ => -t^(n+1)*Real.exp (-t*x))
      (volume.restrict (Ι 0 1)) := by
    exact (show Continuous (fun t : ℝ => -t^(n+1)*Real.exp (-t*x)) by fun_prop).aestronglyMeasurable
  have hbound : ∀ᵐ t : ℝ ∂volume, t ∈ Ι (0:ℝ) 1 →
      ∀ z ∈ Metric.ball x 1, ‖-t^(n+1)*Real.exp (-t*z)‖ ≤ Real.exp (|x|+1) := by
    apply Filter.Eventually.of_forall
    intro t ht z hz
    have ht' : 0 ≤ t ∧ t ≤ 1 := by
      simp only [uIoc_of_le (by norm_num : (0:ℝ) ≤ 1), mem_Ioc] at ht
      exact ⟨ht.1.le, ht.2⟩
    have hz' : |z-x| < 1 := by simpa only [Metric.mem_ball, Real.dist_eq] using hz
    have hab : |z| ≤ |x|+1 := by
      have hh := abs_add_le (z-x) x
      rw [sub_add_cancel] at hh
      linarith
    have hexp : -t*z ≤ |x|+1 := by
      have ha := mul_le_mul_of_nonneg_left (neg_le_abs z) ht'.1
      have hb := mul_le_of_le_one_left (abs_nonneg z) ht'.2
      nlinarith only [ha, hb, hab]
    have hpow : t^(n+1) ≤ 1 := pow_le_one₀ ht'.1 ht'.2
    rw [Real.norm_eq_abs, abs_mul, abs_neg, abs_of_nonneg (pow_nonneg ht'.1 _),
      abs_of_pos (Real.exp_pos _)]
    exact (mul_le_mul_of_nonneg_right hpow (Real.exp_pos _).le).trans
      (by simpa only [one_mul] using Real.exp_le_exp.mpr hexp)
  have hdiff : ∀ᵐ t : ℝ ∂volume, t ∈ Ι (0:ℝ) 1 →
      ∀ z ∈ Metric.ball x 1, HasDerivAt (fun z : ℝ => t^n*Real.exp (-t*z))
        (-t^(n+1)*Real.exp (-t*z)) z := by
    exact Filter.Eventually.of_forall (fun t _ z _ => kernel_deriv n t z)
  have h := (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (Metric.ball_mem_nhds x (by norm_num : (0:ℝ) < 1)) hmeas (moment_integrable n x)
    hmeas' hbound (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => Real.exp (|x|+1)) volume 0 1)
    hdiff).2
  change HasDerivAt (fun z => ∫ t : ℝ in 0..1, t^n*Real.exp (-t*z))
    (-(∫ t : ℝ in 0..1, t^(n+1)*Real.exp (-t*x))) x
  simpa only [neg_mul, intervalIntegral.integral_neg] using h

theorem P_eq_moment (x : ℝ) : P x = moment 1 x := by simp only [P, moment, pow_one]

theorem A_eq_moment (x : ℝ) : A x = 3-2*moment 0 x := by
  unfold A moment
  rw [intervalIntegral.integral_sub intervalIntegrable_const (by apply Continuous.intervalIntegrable; fun_prop)]
  simp only [pow_zero, one_mul, intervalIntegral.integral_const, sub_zero, smul_eq_mul]
  ring

theorem hasDerivAt_A (x : ℝ) : HasDerivAt A (B x) x := by
  have h := ((hasDerivAt_moment 0 x).const_mul 2).const_sub 3
  have hd : HasDerivAt (fun z : ℝ => 3-2*moment 0 z) (B x) x := by
    convert h using 1
    all_goals try with_reducible_and_instances rfl
    simp only [B, P_eq_moment, Nat.zero_add]
    ring
  exact hd.congr_of_eventuallyEq (Filter.Eventually.of_forall A_eq_moment)

theorem hasDerivAt_B (x : ℝ) : HasDerivAt B (-2*moment 2 x) x := by
  have h := (hasDerivAt_moment 1 x).const_mul 2
  have he : B = fun z => 2*moment 1 z := by funext z; simp only [B, P_eq_moment]
  rw [he]
  simpa only [neg_mul, mul_neg] using h

theorem differential_identity (x : ℝ) : A x+(2+x)*B x-2*x*moment 2 x=3 := by
  have ha := hasDerivAt_A x
  have hb := hasDerivAt_B x
  have h := (((hasDerivAt_const x (1:ℝ)).add (hasDerivAt_id x)).mul ha).add
    ((hasDerivAt_id x).mul hb)
  have h' := h.sub_const 1
  have he : (fun z => (1+z)*A z+z*B z-1) = fun z => 3*z := funext drift_identity
  change HasDerivAt (fun z => (1+z)*A z+z*B z-1) _ x at h'
  rw [he] at h'
  have hthree := (hasDerivAt_id x).const_mul 3
  have hu := h'.unique hthree
  dsimp only [id_eq, Pi.add_apply] at hu
  nlinarith only [hu]

theorem coefficient_identity_drift_s35_oai (x y : ℝ) :
    (1+y)*coefficient x y+y*B x-2*x*(y-x)*moment 2 x-1=3*y+B x*(y-x)^2 := by
  have h0 := drift_identity x
  have h1 := differential_identity x
  have hm := congrArg (fun z : ℝ => (y-x)*z) h1
  unfold coefficient
  nlinarith only [h0, hm]

end MetricKMedian.Analytic
end
end

end OAI
end

theorem solution : type_of% @OAI.MetricKMedian.Analytic.coefficient_identity_drift_s35_oai := @OAI.MetricKMedian.Analytic.coefficient_identity_drift_s35_oai
