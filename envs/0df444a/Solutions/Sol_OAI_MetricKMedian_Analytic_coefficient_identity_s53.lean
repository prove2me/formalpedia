-- Prove2me | solution 1 for OAI.MetricKMedian.Analytic.coefficient_identity_s53
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T06:51:39.92612+00:00
-- url     : https://prove2.me/submissions/5361a897-e385-4d74-86a0-a3a923641196

import Mathlib
import Definitions.Def_OAIQ053K000

section
-- module Solutions.OAIQ053_KM.KMedian_Analysis_Coefficients
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

theorem coefficient_identity_s53_oai (x : ℝ) :
    (1 + x) * (A x - 1) = 2 * x * (1 - P x) := by
  rw [A_eq]
  have h₁ := exp_derivative_integral x
  have h₂ := texp_derivative_integral x
  nlinarith

end MetricKMedian.Analytic


end
end

end OAI
end

theorem solution : type_of% @OAI.MetricKMedian.Analytic.coefficient_identity_s53_oai := @OAI.MetricKMedian.Analytic.coefficient_identity_s53_oai
