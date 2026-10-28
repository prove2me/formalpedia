-- Prove2me | solution 1 for OAI.MetricKMedian.Certificates.a_approximation_s35
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T10:51:10.555457+00:00
-- url     : https://prove2.me/submissions/106b39fb-28e5-408f-9751-7c80b33d8bcc

import Mathlib
import Definitions.Def_OAIQ035K000
import Definitions.Def_OAIQ035K002

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

theorem A_eq (x : ℝ) :
    A x = 1 + 2 * (1 - ∫ t : ℝ in 0..1, Real.exp (-t * x)) := by
  rw [A, intervalIntegral.integral_sub (intervalIntegrable_const) (exp_integrable x)]
  simp

end MetricKMedian.Analytic


end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Analysis_TaylorBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.Certificates

private theorem a_approx_upper_part0 {X : ℝ} (ha : 0 ≤ X) (hb : X ≤ (1 / 2)) :
    0 ≤ v X - aSeries X + 3/200000 - (1 / 2891116800) := by
  have hu : 0 ≤ X - 0 := sub_nonneg.mpr ha
  have hv : 0 ≤ (1 / 2) - X := sub_nonneg.mpr hb
  have hcert : 0 ≤ v X - aSeries X + 3/200000 - (1 / 2891116800) - 0 := by
    calc
      0 ≤ (75878321072 / 1235218359375) * (X - 0) ^ 0 * ((1 / 2) - X) ^ 12 +
      (119467751836 / 112292578125) * (X - 0) ^ 1 * ((1 / 2) - X) ^ 11 +
      (7793017451006 / 1235218359375) * (X - 0) ^ 2 * ((1 / 2) - X) ^ 10 +
      (3512657879923 / 176459765625) * (X - 0) ^ 3 * ((1 / 2) - X) ^ 9 +
      (32461184245933 / 823478906250) * (X - 0) ^ 4 * ((1 / 2) - X) ^ 8 +
      (44081397944401 / 823478906250) * (X - 0) ^ 5 * ((1 / 2) - X) ^ 7 +
      (387738185491 / 7319812500) * (X - 0) ^ 6 * ((1 / 2) - X) ^ 6 +
      (6272739823291 / 156853125000) * (X - 0) ^ 7 * ((1 / 2) - X) ^ 5 +
      (7394208348047 / 313706250000) * (X - 0) ^ 8 * ((1 / 2) - X) ^ 4 +
      (841056310571303 / 79053975000000) * (X - 0) ^ 9 * ((1 / 2) - X) ^ 3 +
      (540241863124181 / 158107950000000) * (X - 0) ^ 10 * ((1 / 2) - X) ^ 2 +
      (214663883258389 / 316215900000000) * (X - 0) ^ 11 * ((1 / 2) - X) ^ 1 +
      (863382562703 / 14054040000000) * (X - 0) ^ 12 * ((1 / 2) - X) ^ 0 := by positivity
      _ = v X - aSeries X + 3/200000 - (1 / 2891116800) - 0 := by
        dsimp only [p, v, pSeries, aSeries]
        norm_num
        ring
  linarith only [hcert]

private theorem a_approx_upper_part1 {X : ℝ} (ha : (1 / 2) ≤ X) (hb : X ≤ 1) :
    0 ≤ v X - aSeries X + 3/200000 - (1 / 2891116800) := by
  have hu : 0 ≤ X - (1 / 2) := sub_nonneg.mpr ha
  have hv : 0 ≤ 1 - X := sub_nonneg.mpr hb
  have hcert : 0 ≤ v X - aSeries X + 3/200000 - (1 / 2891116800) - 0 := by
    calc
      0 ≤ (863382562703 / 14054040000000) * (X - (1 / 2)) ^ 0 * (1 - X) ^ 12 +
      (251562700601231 / 316215900000000) * (X - (1 / 2)) ^ 1 * (1 - X) ^ 11 +
      (61932113209151 / 13175662500000) * (X - (1 / 2)) ^ 2 * (1 - X) ^ 10 +
      (29598548004973 / 1796681250000) * (X - (1 / 2)) ^ 3 * (1 - X) ^ 9 +
      (1125267533239 / 29944687500) * (X - (1 / 2)) ^ 4 * (1 - X) ^ 8 +
      (1446800821841 / 24953906250) * (X - (1 / 2)) ^ 5 * (1 - X) ^ 7 +
      (2289587644256 / 37430859375) * (X - (1 / 2)) ^ 6 * (1 - X) ^ 6 +
      (77976295408 / 1782421875) * (X - (1 / 2)) ^ 7 * (1 - X) ^ 5 +
      (36966892276 / 1782421875) * (X - (1 / 2)) ^ 8 * (1 - X) ^ 4 +
      (20738546828 / 3208359375) * (X - (1 / 2)) ^ 9 * (1 - X) ^ 3 +
      (8079313612 / 5347265625) * (X - (1 / 2)) ^ 10 * (1 - X) ^ 2 +
      (21225820472 / 58819921875) * (X - (1 / 2)) ^ 11 * (1 - X) ^ 1 +
      (86731504 / 1411678125) * (X - (1 / 2)) ^ 12 * (1 - X) ^ 0 := by positivity
      _ = v X - aSeries X + 3/200000 - (1 / 2891116800) - 0 := by
        dsimp only [p, v, pSeries, aSeries]
        norm_num
        ring
  linarith only [hcert]

theorem a_approx_upper {X : ℝ} (ha : 0 ≤ X) (hb : X ≤ 1) :
    0 ≤ v X - aSeries X + 3/200000 - (1 / 2891116800) := by
  by_cases ht0 : X ≤ (1 / 2)
  · exact a_approx_upper_part0 ha ht0
  · have hl0 : (1 / 2) ≤ X := (lt_of_not_ge ht0).le
    exact a_approx_upper_part1 hl0 hb

private theorem a_approx_lower_part0 {X : ℝ} (ha : 0 ≤ X) (hb : X ≤ 1) :
    0 ≤ aSeries X - v X + 3/200000 - (1 / 2891116800) := by
  have hu : 0 ≤ X - 0 := sub_nonneg.mpr ha
  have hv : 0 ≤ 1 - X := sub_nonneg.mpr hb
  have hcert : 0 ≤ aSeries X - v X + 3/200000 - (1 / 2891116800) - 0 := by
    calc
      0 ≤ (4743863183 / 316215900000000) * (X - 0) ^ 0 * (1 - X) ^ 12 +
      (12951362059 / 632431800000000) * (X - 0) ^ 1 * (1 - X) ^ 11 +
      (1060434283 / 1951950000000) * (X - 0) ^ 2 * (1 - X) ^ 10 +
      (116708731357 / 28746900000000) * (X - 0) ^ 3 * (1 - X) ^ 9 +
      (3236328137 / 273780000000) * (X - 0) ^ 4 * (1 - X) ^ 8 +
      (28011357623 / 1597050000000) * (X - 0) ^ 5 * (1 - X) ^ 7 +
      (33936081449 / 2395575000000) * (X - 0) ^ 6 * (1 - X) ^ 6 +
      (1460048321 / 228150000000) * (X - 0) ^ 7 * (1 - X) ^ 5 +
      (1236135919 / 456300000000) * (X - 0) ^ 8 * (1 - X) ^ 4 +
      (1921092827 / 821340000000) * (X - 0) ^ 9 * (1 - X) ^ 3 +
      (994289453 / 684450000000) * (X - 0) ^ 10 * (1 - X) ^ 2 +
      (5477850941 / 15057900000000) * (X - 0) ^ 11 * (1 - X) ^ 1 +
      (5420719 / 361389600000) * (X - 0) ^ 12 * (1 - X) ^ 0 := by positivity
      _ = aSeries X - v X + 3/200000 - (1 / 2891116800) - 0 := by
        dsimp only [p, v, pSeries, aSeries]
        norm_num
        ring
  linarith only [hcert]

theorem a_approx_lower {X : ℝ} (ha : 0 ≤ X) (hb : X ≤ 1) :
    0 ≤ aSeries X - v X + 3/200000 - (1 / 2891116800) := by
  exact a_approx_lower_part0 ha hb


end MetricKMedian.Certificates
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Analysis_TaylorExpansion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.Analytic

theorem expApprox_error {u : ℝ} (hu : |u| ≤ 1) :
    |Real.exp u - expApprox 13 u| ≤ taylorError := by
  have he := Real.exp_bound (n := 13) hu (by decide)
  have hp : |u| ^ 13 ≤ 1 := pow_le_one₀ (abs_nonneg u) hu
  have hmul := mul_le_mul_of_nonneg_right hp (by norm_num : (0 : ℝ) ≤ 14 / (6227020800 * 13))
  norm_num only [Nat.factorial, Nat.cast_ofNat, Nat.succ_eq_add_one, Nat.reduceAdd] at he
  exact he.trans (by norm_num [taylorError] at hmul ⊢; exact hmul)

private theorem expApprox_integrable (n : ℕ) (x : ℝ) :
    IntervalIntegrable (fun t : ℝ => expApprox n (-t * x)) MeasureTheory.volume 0 1 := by
  apply Continuous.intervalIntegrable
  unfold expApprox
  fun_prop

theorem integral_expApprox (n : ℕ) (x : ℝ) :
    (∫ t : ℝ in 0..1, expApprox n (-t * x)) =
      ∑ k ∈ Finset.range n, (-x) ^ k / ((k.factorial : ℝ) * (k + 1)) := by
  unfold expApprox
  rw [intervalIntegral.integral_finsetSum (fun _ _ => by
    apply Continuous.intervalIntegrable; fun_prop)]
  apply Finset.sum_congr rfl
  intro k _
  have hid : (fun t : ℝ => (-t * x) ^ k / (k.factorial : ℝ)) =
      (fun t : ℝ => ((-x) ^ k / (k.factorial : ℝ)) * t ^ k) := by
    funext t
    have he : -t * x = -x * t := by ring
    rw [he, mul_pow]
    ring
  rw [hid, intervalIntegral.integral_const_mul, integral_pow]
  simp only [one_pow, zero_pow (Nat.succ_ne_zero _), sub_zero]
  simp only [div_mul_eq_div_div]
  ring

theorem A_taylor_error {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    |A x - aTaylor 13 x| ≤ 2 * taylorError := by
  have hpoint : ∀ t ∈ Set.uIoc (0 : ℝ) 1,
      ‖Real.exp (-t * x) - expApprox 13 (-t * x)‖ ≤ taylorError := by
    intro t ht
    rw [Set.uIoc_of_le (by norm_num)] at ht
    have htx0 : 0 ≤ t * x := mul_nonneg ht.1.le hx0
    have htx1 : t * x ≤ 1 := (mul_le_mul ht.2 hx1 hx0 (by norm_num : (0 : ℝ) ≤ 1)).trans_eq (by ring)
    rw [Real.norm_eq_abs]
    apply expApprox_error
    rw [neg_mul, abs_neg, abs_of_nonneg htx0]
    exact htx1
  have he := intervalIntegral.norm_integral_le_of_norm_le_const hpoint
  rw [intervalIntegral.integral_sub (exp_integrable x) (expApprox_integrable 13 x),
    integral_expApprox] at he
  simp only [Real.norm_eq_abs, sub_zero, abs_one, mul_one] at he
  have hid : A x - aTaylor 13 x = -2 * ((∫ t : ℝ in 0..1, Real.exp (-t * x)) -
      ∑ k ∈ Finset.range 13, (-x) ^ k / ((k.factorial : ℝ) * (k + 1))) := by
    rw [A_eq, aTaylor]
    ring
  rw [hid, abs_mul]
  rw [abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  exact mul_le_mul_of_nonneg_left he (by norm_num)

end MetricKMedian.Analytic


end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Analysis_AnalyticEnvelopes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.Certificates

open Analytic

theorem aSeries_eq (X : ℝ) : aSeries X = aTaylor 13 (1 - X) := by
  norm_num [aSeries, aTaylor, Finset.sum_range_succ, Nat.factorial]
  ring

theorem a_approximation_s35_oai {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    |v (1 - x) - A x| ≤ 3 / 200000 := by
  have hX0 : 0 ≤ 1 - x := sub_nonneg.mpr hx1
  have hX1 : 1 - x ≤ 1 := by linarith
  have hlo := a_approx_lower hX0 hX1
  have hhi := a_approx_upper hX0 hX1
  rw [aSeries_eq] at hlo hhi
  have hex := A_taylor_error hx0 hx1
  rw [abs_le] at hex ⊢
  simp only [sub_sub_cancel] at hlo hhi
  dsimp only [taylorError] at hex
  constructor <;> linarith

end MetricKMedian.Certificates


end
end

end OAI
end

theorem solution : type_of% @OAI.MetricKMedian.Certificates.a_approximation_s35_oai := @OAI.MetricKMedian.Certificates.a_approximation_s35_oai
