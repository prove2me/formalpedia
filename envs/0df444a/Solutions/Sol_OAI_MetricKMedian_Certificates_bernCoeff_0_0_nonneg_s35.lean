-- Prove2me | solution 1 for OAI.MetricKMedian.Certificates.bernCoeff_0_0_nonneg_s35
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T15:11:33.700872+00:00
-- url     : https://prove2.me/submissions/53015aa8-bf21-419e-a3c8-20d54c7f8a87

import Mathlib
import Definitions.Def_OAIQ035K002

section
-- module Solutions.Q224_RR.KMedian_Analysis_BernsteinFalse
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.Certificates
private theorem B0_0_0_nonneg_part0 {X : ℝ} (ha : 0 ≤ X) (hb : X ≤ 1) :
    0 ≤ B0 false 0 X := by
  have hu : 0 ≤ X - 0 := sub_nonneg.mpr ha
  have hv : 0 ≤ 1 - X := sub_nonneg.mpr hb
  have hcert : 0 ≤ B0 false 0 X - 0 := by
    calc
      0 ≤ 0 := by positivity
      _ = B0 false 0 X - 0 := by
        dsimp only [p, v, k, h, pSeries, aSeries, bit, d, H, c, N, l, hh, uZero, uOne, Tk, T1, T2, Q0, Q1, Y, Yprime, B0, B1, B2, discr, total]
        norm_num
  linarith only [hcert]

theorem B0_0_0_nonneg {X : ℝ} (ha : 0 ≤ X) (hb : X ≤ 1) :
    0 ≤ B0 false 0 X := by
  exact B0_0_0_nonneg_part0 ha hb

private theorem B1_0_0_positive_part0 {X : ℝ} (ha : 0 ≤ X) (hb : X ≤ 1) :
    (1 / 1000000) ≤ B1 false 0 X := by
  have hu : 0 ≤ X - 0 := sub_nonneg.mpr ha
  have hv : 0 ≤ 1 - X := sub_nonneg.mpr hb
  have hcert : 0 ≤ B1 false 0 X - (1 / 1000000) := by
    calc
      0 ≤ (404065773973 / 39062500000000) * (X - 0) ^ 0 * (1 - X) ^ 9 +
      (623163165634131 / 625000000000000) * (X - 0) ^ 1 * (1 - X) ^ 8 +
      (18152104360816013 / 2500000000000000) * (X - 0) ^ 2 * (1 - X) ^ 7 +
      (24093334521230637 / 1000000000000000) * (X - 0) ^ 3 * (1 - X) ^ 6 +
      (232990586085156691 / 5000000000000000) * (X - 0) ^ 4 * (1 - X) ^ 5 +
      (286075154851506731 / 5000000000000000) * (X - 0) ^ 5 * (1 - X) ^ 4 +
      (45572032650266963 / 1000000000000000) * (X - 0) ^ 6 * (1 - X) ^ 3 +
      (22935649396141 / 1000000000000) * (X - 0) ^ 7 * (1 - X) ^ 2 +
      (6641740623439 / 1000000000000) * (X - 0) ^ 8 * (1 - X) ^ 1 +
      (841899 / 1000000) * (X - 0) ^ 9 * (1 - X) ^ 0 := by positivity
      _ = B1 false 0 X - (1 / 1000000) := by
        dsimp only [p, v, k, h, pSeries, aSeries, bit, d, H, c, N, l, hh, uZero, uOne, Tk, T1, T2, Q0, Q1, Y, Yprime, B0, B1, B2, discr, total]
        norm_num
        ring
  linarith only [hcert]

theorem B1_0_0_positive {X : ℝ} (ha : 0 ≤ X) (hb : X ≤ 1) :
    (1 / 1000000) ≤ B1 false 0 X := by
  exact B1_0_0_positive_part0 ha hb

private theorem sum12_0_0_positive_part0 {X : ℝ} (ha : 0 ≤ X) (hb : X ≤ 1) :
    (1 / 1000000) ≤ B1 false 0 X+B2 false 0 X := by
  have hu : 0 ≤ X - 0 := sub_nonneg.mpr ha
  have hv : 0 ≤ 1 - X := sub_nonneg.mpr hb
  have hcert : 0 ≤ B1 false 0 X+B2 false 0 X - (1 / 1000000) := by
    calc
      0 ≤ (4067425277277 / 39062500000000) * (X - 0) ^ 0 * (1 - X) ^ 9 +
      (771931517449689 / 625000000000000) * (X - 0) ^ 1 * (1 - X) ^ 8 +
      (1566084494272957 / 250000000000000) * (X - 0) ^ 2 * (1 - X) ^ 7 +
      (22788348783657661 / 1250000000000000) * (X - 0) ^ 3 * (1 - X) ^ 6 +
      (169643309124787979 / 5000000000000000) * (X - 0) ^ 4 * (1 - X) ^ 5 +
      (21056052153604727 / 500000000000000) * (X - 0) ^ 5 * (1 - X) ^ 4 +
      (6989493625194391 / 200000000000000) * (X - 0) ^ 6 * (1 - X) ^ 3 +
      (18713938032901 / 1000000000000) * (X - 0) ^ 7 * (1 - X) ^ 2 +
      (5868075051339 / 1000000000000) * (X - 0) ^ 8 * (1 - X) ^ 1 +
      (820899 / 1000000) * (X - 0) ^ 9 * (1 - X) ^ 0 := by positivity
      _ = B1 false 0 X+B2 false 0 X - (1 / 1000000) := by
        dsimp only [p, v, k, h, pSeries, aSeries, bit, d, H, c, N, l, hh, uZero, uOne, Tk, T1, T2, Q0, Q1, Y, Yprime, B0, B1, B2, discr, total]
        norm_num
        ring
  linarith only [hcert]

theorem sum12_0_0_positive {X : ℝ} (ha : 0 ≤ X) (hb : X ≤ 1) :
    (1 / 1000000) ≤ B1 false 0 X+B2 false 0 X := by
  exact sum12_0_0_positive_part0 ha hb


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

private theorem quadratic_of_end_slopes {a b c r : ℝ} (ha : 0 ≤ a)
    (hb : 0 ≤ b) (hbc : 0 ≤ b+c) (hr0 : 0 ≤ r) (_hr : r ≤ 1) :
    0 ≤ a+b*r+c*r^2 := by
  have h1 := mul_nonneg hbc (sq_nonneg r)
  have h2 := mul_nonneg (mul_nonneg hb hr0) (sub_nonneg.mpr _hr)
  nlinarith only [ha, h1, h2]

theorem bernCoeff_0_0_nonneg_s35_oai {X r : ℝ} (hX0 : 0 ≤ X) (hX : X ≤ 1)
    (hr0 : 0 ≤ r) (_hr : r ≤ 1) : 0 ≤ bernCoeff false 0 X r := by
  have ha := B0_0_0_nonneg hX0 hX
  unfold bernCoeff
  have hb := B1_0_0_positive hX0 hX
  have hbc := sum12_0_0_positive hX0 hX
  exact quadratic_of_end_slopes ha (by linarith) (by linarith) hr0 _hr

end MetricKMedian.Certificates


end
end

end OAI
end

theorem solution : type_of% @OAI.MetricKMedian.Certificates.bernCoeff_0_0_nonneg_s35_oai := @OAI.MetricKMedian.Certificates.bernCoeff_0_0_nonneg_s35_oai
