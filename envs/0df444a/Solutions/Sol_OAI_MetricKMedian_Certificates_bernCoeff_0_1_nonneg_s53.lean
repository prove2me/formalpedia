-- Prove2me | solution 1 for OAI.MetricKMedian.Certificates.bernCoeff_0_1_nonneg_s53
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T06:57:14.431875+00:00
-- url     : https://prove2.me/submissions/b1ac49d1-2e34-448c-bc14-12675bc0ea11

import Mathlib
import Definitions.Def_OAIQ053K002

section
-- module Solutions.OAIQ053_KM.KMedian_Analysis_BernsteinFalse
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.Certificates

private theorem B0_0_1_nonneg_part0 {X : ℝ} (ha : 0 ≤ X) (hb : X ≤ 1) :
    0 ≤ B0 false 1 X := by
  have hu : 0 ≤ X - 0 := sub_nonneg.mpr ha
  have hv : 0 ≤ 1 - X := sub_nonneg.mpr hb
  have hcert : 0 ≤ B0 false 1 X - 0 := by
    calc
      0 ≤ 0 := by positivity
      _ = B0 false 1 X - 0 := by
        dsimp only [p, v, k, h, pSeries, aSeries, bit, d, H, c, N, l, hh, uZero, uOne, Tk, T1, T2, Q0, Q1, Y, Yprime, B0, B1, B2, discr, total]
        norm_num
  linarith only [hcert]

theorem B0_0_1_nonneg {X : ℝ} (ha : 0 ≤ X) (hb : X ≤ 1) :
    0 ≤ B0 false 1 X := by
  exact B0_0_1_nonneg_part0 ha hb

private theorem B1_0_1_positive_part0 {X : ℝ} (ha : 0 ≤ X) (hb : X ≤ 1) :
    (1 / 1000000) ≤ B1 false 1 X := by
  have hu : 0 ≤ X - 0 := sub_nonneg.mpr ha
  have hv : 0 ≤ 1 - X := sub_nonneg.mpr hb
  have hcert : 0 ≤ B1 false 1 X - (1 / 1000000) := by
    calc
      0 ≤ (404065773973 / 39062500000000) * (X - 0) ^ 0 * (1 - X) ^ 10 +
      (966174111159529 / 1875000000000000) * (X - 0) ^ 1 * (1 - X) ^ 9 +
      (9173652229149473 / 2500000000000000) * (X - 0) ^ 2 * (1 - X) ^ 8 +
      (185005056222628987 / 15000000000000000) * (X - 0) ^ 3 * (1 - X) ^ 7 +
      (123608958167288709 / 5000000000000000) * (X - 0) ^ 4 * (1 - X) ^ 6 +
      (4875189406000961 / 150000000000000) * (X - 0) ^ 5 * (1 - X) ^ 5 +
      (2194014867980963 / 75000000000000) * (X - 0) ^ 6 * (1 - X) ^ 4 +
      (273077791234470541 / 15000000000000000) * (X - 0) ^ 7 * (1 - X) ^ 3 +
      (22884057095803963 / 3000000000000000) * (X - 0) ^ 8 * (1 - X) ^ 2 +
      (1964906331849 / 1000000000000) * (X - 0) ^ 9 * (1 - X) ^ 1 +
      (237199 / 1000000) * (X - 0) ^ 10 * (1 - X) ^ 0 := by positivity
      _ = B1 false 1 X - (1 / 1000000) := by
        dsimp only [p, v, k, h, pSeries, aSeries, bit, d, H, c, N, l, hh, uZero, uOne, Tk, T1, T2, Q0, Q1, Y, Yprime, B0, B1, B2, discr, total]
        norm_num
        ring
  linarith only [hcert]

theorem B1_0_1_positive {X : ℝ} (ha : 0 ≤ X) (hb : X ≤ 1) :
    (1 / 1000000) ≤ B1 false 1 X := by
  exact B1_0_1_positive_part0 ha hb

private theorem sum12_0_1_positive_part0 {X : ℝ} (ha : 0 ≤ X) (hb : X ≤ 1) :
    (1 / 1000000) ≤ B1 false 1 X+B2 false 1 X := by
  have hu : 0 ≤ X - 0 := sub_nonneg.mpr ha
  have hv : 0 ≤ 1 - X := sub_nonneg.mpr hb
  have hcert : 0 ≤ B1 false 1 X+B2 false 1 X - (1 / 1000000) := by
    calc
      0 ≤ (4067425277277 / 39062500000000) * (X - 0) ^ 0 * (1 - X) ^ 9 +
      (2053686809455499 / 1875000000000000) * (X - 0) ^ 1 * (1 - X) ^ 8 +
      (18910273475747483 / 3750000000000000) * (X - 0) ^ 2 * (1 - X) ^ 7 +
      (25257075042857009 / 1875000000000000) * (X - 0) ^ 3 * (1 - X) ^ 6 +
      (347115690230589581 / 15000000000000000) * (X - 0) ^ 4 * (1 - X) ^ 5 +
      (398859462352384789 / 15000000000000000) * (X - 0) ^ 5 * (1 - X) ^ 4 +
      (61373162138386319 / 3000000000000000) * (X - 0) ^ 6 * (1 - X) ^ 3 +
      (6096242747692391 / 600000000000000) * (X - 0) ^ 7 * (1 - X) ^ 2 +
      (8861941489247 / 3000000000000) * (X - 0) ^ 8 * (1 - X) ^ 1 +
      (1148597 / 3000000) * (X - 0) ^ 9 * (1 - X) ^ 0 := by positivity
      _ = B1 false 1 X+B2 false 1 X - (1 / 1000000) := by
        dsimp only [p, v, k, h, pSeries, aSeries, bit, d, H, c, N, l, hh, uZero, uOne, Tk, T1, T2, Q0, Q1, Y, Yprime, B0, B1, B2, discr, total]
        norm_num
        ring
  linarith only [hcert]

theorem sum12_0_1_positive {X : ℝ} (ha : 0 ≤ X) (hb : X ≤ 1) :
    (1 / 1000000) ≤ B1 false 1 X+B2 false 1 X := by
  exact sum12_0_1_positive_part0 ha hb


end MetricKMedian.Certificates
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Analysis_QuadraticEnvelopes
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

theorem bernCoeff_0_1_nonneg_s53_oai {X r : ℝ} (hX0 : 0 ≤ X) (hX : X ≤ 1)
    (hr0 : 0 ≤ r) (_hr : r ≤ 1) : 0 ≤ bernCoeff false 1 X r := by
  have ha := B0_0_1_nonneg hX0 hX
  unfold bernCoeff
  have hb := B1_0_1_positive hX0 hX
  have hbc := sum12_0_1_positive hX0 hX
  exact quadratic_of_end_slopes ha (by linarith) (by linarith) hr0 _hr

end MetricKMedian.Certificates


end
end

end OAI
end

theorem solution : type_of% @OAI.MetricKMedian.Certificates.bernCoeff_0_1_nonneg_s53_oai := @OAI.MetricKMedian.Certificates.bernCoeff_0_1_nonneg_s53_oai
