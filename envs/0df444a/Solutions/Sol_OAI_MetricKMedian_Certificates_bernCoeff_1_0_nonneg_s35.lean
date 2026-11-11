-- Prove2me | solution 1 for OAI.MetricKMedian.Certificates.bernCoeff_1_0_nonneg_s35
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T15:13:06.243511+00:00
-- url     : https://prove2.me/submissions/067680c9-651e-4d0d-b77f-19ee5ae50c66

import Mathlib
import Definitions.Def_OAIQ035K002
import Theorems.Thm_OAI_MetricKMedian_Certificates_sum12_1_0_positive_s35

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
private theorem B0_1_0_nonneg_part0 {X : ℝ} (ha : 0 ≤ X) (hb : X ≤ 1) :
    0 ≤ B0 true 0 X := by
  have hu : 0 ≤ X - 0 := sub_nonneg.mpr ha
  have hv : 0 ≤ 1 - X := sub_nonneg.mpr hb
  have hcert : 0 ≤ B0 true 0 X - 0 := by
    calc
      0 ≤ 0 := by positivity
      _ = B0 true 0 X - 0 := by
        dsimp only [p, v, k, h, pSeries, aSeries, bit, d, H, c, N, l, hh, uZero, uOne, Tk, T1, T2, Q0, Q1, Y, Yprime, B0, B1, B2, discr, total]
        norm_num
  linarith only [hcert]

theorem B0_1_0_nonneg {X : ℝ} (ha : 0 ≤ X) (hb : X ≤ 1) :
    0 ≤ B0 true 0 X := by
  exact B0_1_0_nonneg_part0 ha hb

private theorem B1_1_0_positive_part0 {X : ℝ} (ha : 0 ≤ X) (hb : X ≤ 1) :
    (1 / 1000000) ≤ B1 true 0 X := by
  have hu : 0 ≤ X - 0 := sub_nonneg.mpr ha
  have hv : 0 ≤ 1 - X := sub_nonneg.mpr hb
  have hcert : 0 ≤ B1 true 0 X - (1 / 1000000) := by
    calc
      0 ≤ (8567637871049 / 156250000000000) * (X - 0) ^ 0 * (1 - X) ^ 9 +
      (1995368425006037 / 2500000000000000) * (X - 0) ^ 1 * (1 - X) ^ 8 +
      (89757615029196417 / 20000000000000000) * (X - 0) ^ 2 * (1 - X) ^ 7 +
      (546164375672760547 / 40000000000000000) * (X - 0) ^ 3 * (1 - X) ^ 6 +
      (6359862497189341 / 250000000000000) * (X - 0) ^ 4 * (1 - X) ^ 5 +
      (609814530584032371 / 20000000000000000) * (X - 0) ^ 5 * (1 - X) ^ 4 +
      (473203836380037771 / 20000000000000000) * (X - 0) ^ 6 * (1 - X) ^ 3 +
      (91914977523796291 / 8000000000000000) * (X - 0) ^ 7 * (1 - X) ^ 2 +
      (2531863087 / 800000000) * (X - 0) ^ 8 * (1 - X) ^ 1 +
      (374799 / 1000000) * (X - 0) ^ 9 * (1 - X) ^ 0 := by positivity
      _ = B1 true 0 X - (1 / 1000000) := by
        dsimp only [p, v, k, h, pSeries, aSeries, bit, d, H, c, N, l, hh, uZero, uOne, Tk, T1, T2, Q0, Q1, Y, Yprime, B0, B1, B2, discr, total]
        norm_num
        ring
  linarith only [hcert]

theorem B1_1_0_positive {X : ℝ} (ha : 0 ≤ X) (hb : X ≤ 1) :
    (1 / 1000000) ≤ B1 true 0 X := by
  exact B1_1_0_positive_part0 ha hb

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

theorem bernCoeff_1_0_nonneg_s35_oai {X r : ℝ} (hX0 : 0 ≤ X) (hX : X ≤ 1)
    (hr0 : 0 ≤ r) (_hr : r ≤ 1) : 0 ≤ bernCoeff true 0 X r := by
  have ha := B0_1_0_nonneg hX0 hX
  unfold bernCoeff
  have hb := B1_1_0_positive hX0 hX
  have hbc := sum12_1_0_positive_s35 hX0 hX
  exact quadratic_of_end_slopes ha (by linarith) (by linarith) hr0 _hr

end MetricKMedian.Certificates


end
end

end OAI
end

theorem solution : type_of% @OAI.MetricKMedian.Certificates.bernCoeff_1_0_nonneg_s35_oai := @OAI.MetricKMedian.Certificates.bernCoeff_1_0_nonneg_s35_oai
