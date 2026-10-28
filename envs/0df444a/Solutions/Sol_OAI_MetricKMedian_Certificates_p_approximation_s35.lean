-- Prove2me | solution 1 for OAI.MetricKMedian.Certificates.p_approximation_s35
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T10:52:40.72671+00:00
-- url     : https://prove2.me/submissions/b3e6501a-f31f-4521-bf87-a9d1c75839fa

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

theorem texp_integrable (x : ℝ) :
    IntervalIntegrable (fun t : ℝ => t * Real.exp (-t * x)) MeasureTheory.volume 0 1 := by
  apply Continuous.intervalIntegrable
  fun_prop

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
private theorem p_approx_upper_part0 {X : ℝ} (ha : 0 ≤ X) (hb : X ≤ 1) :
    0 ≤ p X - pSeries X + 3/400000 - (1 / 5782233600) := by
  have hu : 0 ≤ X - 0 := sub_nonneg.mpr ha
  have hv : 0 ≤ 1 - X := sub_nonneg.mpr hb
  have hcert : 0 ≤ p X - pSeries X + 3/400000 - (1 / 5782233600) - 0 := by
    calc
      0 ≤ (44282975291 / 5902696800000000) * (X - 0) ^ 0 * (1 - X) ^ 12 +
      (14148704719 / 632431800000000) * (X - 0) ^ 1 * (1 - X) ^ 11 +
      (386323505101 / 1264863600000000) * (X - 0) ^ 2 * (1 - X) ^ 10 +
      (17816109281 / 9034740000000) * (X - 0) ^ 3 * (1 - X) ^ 9 +
      (106899993149 / 19164600000000) * (X - 0) ^ 4 * (1 - X) ^ 8 +
      (9994714201 / 1197787500000) * (X - 0) ^ 5 * (1 - X) ^ 7 +
      (4834337411 / 684450000000) * (X - 0) ^ 6 * (1 - X) ^ 6 +
      (5771169613 / 1597050000000) * (X - 0) ^ 7 * (1 - X) ^ 5 +
      (311775179 / 182520000000) * (X - 0) ^ 8 * (1 - X) ^ 4 +
      (636933061 / 513337500000) * (X - 0) ^ 9 * (1 - X) ^ 3 +
      (118332037 / 171112500000) * (X - 0) ^ 10 * (1 - X) ^ 2 +
      (506491313 / 3011580000000) * (X - 0) ^ 11 * (1 - X) ^ 1 +
      (5420719 / 722779200000) * (X - 0) ^ 12 * (1 - X) ^ 0 := by positivity
      _ = p X - pSeries X + 3/400000 - (1 / 5782233600) - 0 := by
        dsimp only [p, v, pSeries, aSeries]
        norm_num
        ring
  linarith only [hcert]

theorem p_approx_upper {X : ℝ} (ha : 0 ≤ X) (hb : X ≤ 1) :
    0 ≤ p X - pSeries X + 3/400000 - (1 / 5782233600) := by
  exact p_approx_upper_part0 ha hb

private theorem p_approx_lower_part0 {X : ℝ} (ha : 0 ≤ X) (hb : X ≤ 1) :
    0 ≤ pSeries X - p X + 3/400000 - (1 / 5782233600) := by
  have hu : 0 ≤ X - 0 := sub_nonneg.mpr ha
  have hv : 0 ≤ 1 - X := sub_nonneg.mpr hb
  have hcert : 0 ≤ pSeries X - p X + 3/400000 - (1 / 5782233600) - 0 := by
    calc
      0 ≤ (132766305127 / 17708090400000000) * (X - 0) ^ 0 * (1 - X) ^ 12 +
      (99686394281 / 632431800000000) * (X - 0) ^ 1 * (1 - X) ^ 11 +
      (865862583899 / 1264863600000000) * (X - 0) ^ 2 * (1 - X) ^ 10 +
      (11997845219 / 9034740000000) * (X - 0) ^ 3 * (1 - X) ^ 9 +
      (35393880601 / 19164600000000) * (X - 0) ^ 4 * (1 - X) ^ 8 +
      (2117336587 / 598893750000) * (X - 0) ^ 5 * (1 - X) ^ 7 +
      (4651920839 / 684450000000) * (X - 0) ^ 6 * (1 - X) ^ 6 +
      (13201346887 / 1597050000000) * (X - 0) ^ 7 * (1 - X) ^ 5 +
      (1043404571 / 182520000000) * (X - 0) ^ 8 * (1 - X) ^ 4 +
      (2114083253 / 1026675000000) * (X - 0) ^ 9 * (1 - X) ^ 3 +
      (204261727 / 684450000000) * (X - 0) ^ 10 * (1 - X) ^ 2 +
      (35580587 / 3011580000000) * (X - 0) ^ 11 * (1 - X) ^ 1 +
      (5420719 / 722779200000) * (X - 0) ^ 12 * (1 - X) ^ 0 := by positivity
      _ = pSeries X - p X + 3/400000 - (1 / 5782233600) - 0 := by
        dsimp only [p, v, pSeries, aSeries]
        norm_num
        ring
  linarith only [hcert]

theorem p_approx_lower {X : ℝ} (ha : 0 ≤ X) (hb : X ≤ 1) :
    0 ≤ pSeries X - p X + 3/400000 - (1 / 5782233600) := by
  exact p_approx_lower_part0 ha hb


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

private theorem texpApprox_integrable (n : ℕ) (x : ℝ) :
    IntervalIntegrable (fun t : ℝ => t * expApprox n (-t * x)) MeasureTheory.volume 0 1 := by
  apply Continuous.intervalIntegrable
  unfold expApprox
  fun_prop

theorem integral_texpApprox (n : ℕ) (x : ℝ) :
    (∫ t : ℝ in 0..1, t * expApprox n (-t * x)) = pTaylor n x := by
  unfold expApprox pTaylor
  simp_rw [Finset.mul_sum]
  rw [intervalIntegral.integral_finsetSum (fun _ _ => by
    apply Continuous.intervalIntegrable; fun_prop)]
  apply Finset.sum_congr rfl
  intro k _
  have hid : (fun t : ℝ => t * ((-t * x) ^ k / (k.factorial : ℝ))) =
      (fun t : ℝ => ((-x) ^ k / (k.factorial : ℝ)) * t ^ (k + 1)) := by
    funext t
    have he : -t * x = -x * t := by ring
    rw [he, mul_pow, pow_succ]
    ring
  rw [hid, intervalIntegral.integral_const_mul, integral_pow]
  simp only [one_pow, zero_pow (Nat.succ_ne_zero _), sub_zero]
  simp only [Nat.cast_add, Nat.cast_one, div_mul_eq_div_div]
  ring

theorem P_taylor_error {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    |P x - pTaylor 13 x| ≤ taylorError := by
  have hpoint : ∀ t ∈ Set.uIoc (0 : ℝ) 1,
      ‖t * Real.exp (-t * x) - t * expApprox 13 (-t * x)‖ ≤ taylorError := by
    intro t ht
    rw [Set.uIoc_of_le (by norm_num)] at ht
    have htx0 : 0 ≤ t * x := mul_nonneg ht.1.le hx0
    have htx1 : t * x ≤ 1 := by nlinarith [mul_le_mul ht.2 hx1 hx0 (by norm_num : (0 : ℝ) ≤ 1)]
    have hex := expApprox_error (u := -t * x) (by
      rw [neg_mul, abs_neg, abs_of_nonneg htx0]
      exact htx1)
    rw [← mul_sub, Real.norm_eq_abs, abs_mul, abs_of_nonneg ht.1.le]
    have hm := mul_le_mul_of_nonneg_left hex ht.1.le
    have hu := mul_le_mul_of_nonneg_right ht.2 (by norm_num [taylorError] : 0 ≤ taylorError)
    exact hm.trans (by simpa only [one_mul] using hu)
  have he := intervalIntegral.norm_integral_le_of_norm_le_const hpoint
  rw [intervalIntegral.integral_sub (texp_integrable x) (texpApprox_integrable 13 x),
    integral_texpApprox] at he
  simpa only [Real.norm_eq_abs, sub_zero, abs_one, mul_one, P] using he

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

theorem pSeries_eq (X : ℝ) : pSeries X = pTaylor 13 (1 - X) := by
  norm_num [pSeries, pTaylor, Finset.sum_range_succ, Nat.factorial]
  ring

theorem p_approximation_s35_oai {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    |p (1 - x) - P x| ≤ 3 / 400000 := by
  have hX0 : 0 ≤ 1 - x := sub_nonneg.mpr hx1
  have hX1 : 1 - x ≤ 1 := by linarith
  have hlo := p_approx_lower hX0 hX1
  have hhi := p_approx_upper hX0 hX1
  rw [pSeries_eq] at hlo hhi
  have hex := P_taylor_error hx0 hx1
  rw [abs_le] at hex ⊢
  simp only [sub_sub_cancel] at hlo hhi
  dsimp only [taylorError] at hex
  constructor <;> linarith

end MetricKMedian.Certificates


end
end

end OAI
end

theorem solution : type_of% @OAI.MetricKMedian.Certificates.p_approximation_s35_oai := @OAI.MetricKMedian.Certificates.p_approximation_s35_oai
