-- Prove2me | solution 1 for OAI.MetricKMedian.FiniteComparison.centering_gap_nonneg_s53
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T07:08:52.025286+00:00
-- url     : https://prove2.me/submissions/4cc041e7-cf80-4d6e-a425-45934b81f0ba

import Mathlib
import Definitions.Def_OAIQ053K006

section
-- module Solutions.OAIQ053_KM.KMedian_Analysis_FiniteAverages
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.FiniteComparison

theorem denominator_pos {p q : ℝ} (hp : p ≤ 1 / 2)
    (hp0 : 0 ≤ p) (hq : q ≤ 1) : 0 < 1 - p * q := by
  nlinarith [mul_le_mul_of_nonneg_left hq hp0]

theorem kZero_nonneg {p : ℝ} (hp0 : 0 ≤ p) :
    0 ≤ kZero p := by
  have hs : Real.sqrt (1 - p) ≤ 1 := by
    apply Real.sqrt_le_one.mpr
    linarith
  exact div_nonneg (sub_nonneg.mpr hs) (by positivity)

theorem kappa_zero_le {p q : ℝ} (hp0 : 0 ≤ p) (hp : p ≤ 1 / 2)
    (hq : q ≤ 1) : kappa p 0 q ≤ kZero p := by
  have hd := denominator_pos hp hp0 hq
  have hs0 : 0 ≤ Real.sqrt (1 - p) := Real.sqrt_nonneg _
  have hs2 : Real.sqrt (1 - p) ^ 2 = 1 - p := Real.sq_sqrt (by linarith)
  have hp_eq : p = 1 - Real.sqrt (1 - p) ^ 2 := by linarith
  have hk0 := kZero_nonneg hp0
  have identity : kZero p * (1 - p * q) - p * q * (1 - q) =
      kZero p * ((1 + Real.sqrt (1 - p)) * q - 1) ^ 2 := by
    unfold kZero
    field_simp [ne_of_gt (show 0 < 1 + Real.sqrt (1 - p) by positivity)]
    nlinarith [sq_nonneg (Real.sqrt (1 - p) * q)]
  have hid : kappa p 0 q = p * q * (1 - q) / (1 - p * q) := by
    apply (eq_div_iff (ne_of_gt hd)).mpr
    unfold kappa
    simp only [mul_zero, sub_zero, one_mul]
    have he : psi p q * (1 - p * q) = 1 - q :=
      div_mul_cancel₀ _ (ne_of_gt hd)
    nlinarith only [he]
  rw [hid, div_le_iff₀ hd]
  have h := mul_nonneg hk0 (sq_nonneg ((1 + Real.sqrt (1 - p)) * q - 1))
  linarith [identity]

theorem kappa_one_le {p q : ℝ} (hp0 : 0 ≤ p) (hp : p ≤ 1 / 2)
    (hq : q ≤ 1) : kappa p 1 q ≤ 0 := by
  have hd := denominator_pos hp hp0 hq
  have hid : kappa p 1 q = -p * (1 - q) ^ 2 / (1 - p * q) := by
    unfold kappa psi
    simp only [mul_one]
    field_simp [ne_of_gt hd]
    ring
  rw [hid]
  exact div_nonpos_of_nonpos_of_nonneg
    (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hp0) (sq_nonneg _)) hd.le

end MetricKMedian.FiniteComparison

namespace MetricKMedian.FiniteComparison

theorem centering_gap_nonneg_s53_oai {p q : ℝ} (hp0 : 0 ≤ p) (hp : p ≤ 1 / 2)
    (hq : q ≤ 1) (s : Bool) : 0 ≤ k p s - (C p s * psi p q - (1 - q)) := by
  cases s
  · have he := kappa_zero_le hp0 hp hq
    simpa only [kappa, mul_zero, sub_zero, one_mul, k, C, Bool.false_eq_true,
      ↓reduceIte] using sub_nonneg.mpr he
  · have he := kappa_one_le hp0 hp hq
    simpa only [kappa, mul_one, k, C, ↓reduceIte] using sub_nonneg.mpr he

end MetricKMedian.FiniteComparison


end
end

end OAI
end

theorem solution : type_of% @OAI.MetricKMedian.FiniteComparison.centering_gap_nonneg_s53_oai := @OAI.MetricKMedian.FiniteComparison.centering_gap_nonneg_s53_oai
