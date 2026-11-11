-- Prove2me | solution 1 for OAI.MetricKMedian.Certificates.bernCoeff_1_3_nonneg_s35
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T15:13:08.672666+00:00
-- url     : https://prove2.me/submissions/016858a6-1388-4f42-8c04-b1cd7766481e

import Mathlib
import Definitions.Def_OAIQ035K002
import Theorems.Thm_OAI_MetricKMedian_Certificates_B1_1_3_positive_s35
import Theorems.Thm_OAI_MetricKMedian_Certificates_B2_1_3_positive_s35
import Theorems.Thm_OAI_MetricKMedian_Certificates_diff02_1_3_positive_s35
import Theorems.Thm_OAI_MetricKMedian_Certificates_discr_1_3_positive_s35
import Theorems.Thm_OAI_MetricKMedian_Certificates_total_1_3_positive_s35

section
-- module Solutions.Q224_RR.KMedian_Analysis_BernsteinTrue
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.Certificates

private theorem B0_1_3_nonneg_part0 {X : ℝ} (ha : 0 ≤ X) (hb : X ≤ 1) :
    0 ≤ B0 true 3 X := by
  have hu : 0 ≤ X - 0 := sub_nonneg.mpr ha
  have hv : 0 ≤ 1 - X := sub_nonneg.mpr hb
  have hcert : 0 ≤ B0 true 3 X - 0 := by
    calc
      0 ≤ (15848072128951 / 19531250000000) * (X - 0) ^ 2 * (1 - X) ^ 9 +
      (94958223047249 / 12207031250000) * (X - 0) ^ 3 * (1 - X) ^ 8 +
      (41560335145876313 / 1250000000000000) * (X - 0) ^ 4 * (1 - X) ^ 7 +
      (103990553393773791 / 1250000000000000) * (X - 0) ^ 5 * (1 - X) ^ 6 +
      (3359424991311433967 / 25000000000000000) * (X - 0) ^ 6 * (1 - X) ^ 5 +
      (3635393128707717729 / 25000000000000000) * (X - 0) ^ 7 * (1 - X) ^ 4 +
      (2638051368498712701 / 25000000000000000) * (X - 0) ^ 8 * (1 - X) ^ 3 +
      (247851466601733463 / 5000000000000000) * (X - 0) ^ 9 * (1 - X) ^ 2 +
      (1712303531 / 125000000) * (X - 0) ^ 10 * (1 - X) ^ 1 +
      (8499 / 5000) * (X - 0) ^ 11 * (1 - X) ^ 0 := by positivity
      _ = B0 true 3 X - 0 := by
        dsimp only [p, v, k, h, pSeries, aSeries, bit, d, H, c, N, l, hh, uZero, uOne, Tk, T1, T2, Q0, Q1, Y, Yprime, B0, B1, B2, discr, total]
        norm_num
        ring
  linarith only [hcert]

theorem B0_1_3_nonneg {X : ℝ} (ha : 0 ≤ X) (hb : X ≤ 1) :
    0 ≤ B0 true 3 X := by
  exact B0_1_3_nonneg_part0 ha hb

end MetricKMedian.Certificates


end
end

end OAI
end

section
-- module Solutions.Q224_RR.KMedian_Analysis_QuadraticEnvelopes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.Certificates

private theorem quadratic_of_discriminant {a b c r : ℝ} (ha : 0 ≤ a)
    (hd : 0 < 4*a*c-b^2) : 0 ≤ a+b*r+c*r^2 := by
  have hc : 0 < c := by
    by_contra hn
    have hp := mul_nonpos_of_nonneg_of_nonpos ha (le_of_not_gt hn)
    nlinarith only [hp, hd, sq_nonneg b]
  have hs := sq_nonneg (2*c*r+b)
  have hid : (2*c*r+b)^2+(4*a*c-b^2) = 4*c*(a+b*r+c*r^2) := by ring
  have hprod : 0 < c*(a+b*r+c*r^2) := by nlinarith only [hs, hd, hid]
  exact (pos_of_mul_pos_right hprod hc.le).le

private theorem quadratic_of_total {a b c r : ℝ} (ha : 0 ≤ a)
    (ht : 0 ≤ a+b+c) (hd : 0 ≤ a-c) (hr0 : 0 ≤ r) (_hr : r ≤ 1) :
    0 ≤ a+b*r+c*r^2 := by
  have h1 := mul_nonneg hr0 ht
  have h2 := add_nonneg (mul_nonneg (sub_nonneg.mpr _hr) ha) (mul_nonneg hr0 hd)
  have h3 := mul_nonneg (sub_nonneg.mpr _hr) h2
  nlinarith only [h1, h3]

theorem bernCoeff_1_3_nonneg_s35_oai {X r : ℝ} (hX0 : 0 ≤ X) (hX : X ≤ 1)
    (hr0 : 0 ≤ r) (_hr : r ≤ 1) : 0 ≤ bernCoeff true 3 X r := by
  have ha := B0_1_3_nonneg hX0 hX
  unfold bernCoeff
  by_cases hcut : X ≤ 1/10
  · have hb := B1_1_3_positive_s35 hX0 hcut
    have hc := B2_1_3_positive_s35 hX0 hcut
    exact add_nonneg (add_nonneg ha (mul_nonneg (by linarith) hr0))
      (mul_nonneg (by linarith) (sq_nonneg r))
  · by_cases hmid : X ≤ 3/4
    · have hd := discr_1_3_positive_s35 (le_of_not_ge hcut) hmid
      exact quadratic_of_discriminant ha (by dsimp only [discr] at hd <;> linarith)
    · have ht := total_1_3_positive_s35 (le_of_not_ge hmid) hX
      have hd := diff02_1_3_positive_s35 (le_of_not_ge hmid) hX
      exact quadratic_of_total ha (by dsimp only [total] at ht <;> linarith) (by linarith) hr0 _hr

end MetricKMedian.Certificates


end
end

end OAI
end

theorem solution : type_of% @OAI.MetricKMedian.Certificates.bernCoeff_1_3_nonneg_s35_oai := @OAI.MetricKMedian.Certificates.bernCoeff_1_3_nonneg_s35_oai
