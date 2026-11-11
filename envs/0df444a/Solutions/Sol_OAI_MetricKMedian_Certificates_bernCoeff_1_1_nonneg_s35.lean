-- Prove2me | solution 1 for OAI.MetricKMedian.Certificates.bernCoeff_1_1_nonneg_s35
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T15:13:07.437704+00:00
-- url     : https://prove2.me/submissions/88505315-7f7a-4694-b91c-e598506cc057

import Mathlib
import Definitions.Def_OAIQ035K002
import Theorems.Thm_OAI_MetricKMedian_Certificates_sum12_1_1_positive_s35

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

private theorem B0_1_1_nonneg_part0 {X : ℝ} (ha : 0 ≤ X) (hb : X ≤ 1) :
    0 ≤ B0 true 1 X := by
  have hu : 0 ≤ X - 0 := sub_nonneg.mpr ha
  have hv : 0 ≤ 1 - X := sub_nonneg.mpr hb
  have hcert : 0 ≤ B0 true 1 X - 0 := by
    calc
      0 ≤ 0 := by positivity
      _ = B0 true 1 X - 0 := by
        dsimp only [p, v, k, h, pSeries, aSeries, bit, d, H, c, N, l, hh, uZero, uOne, Tk, T1, T2, Q0, Q1, Y, Yprime, B0, B1, B2, discr, total]
        norm_num
  linarith only [hcert]

theorem B0_1_1_nonneg {X : ℝ} (ha : 0 ≤ X) (hb : X ≤ 1) :
    0 ≤ B0 true 1 X := by
  exact B0_1_1_nonneg_part0 ha hb

private theorem B1_1_1_positive_part0 {X : ℝ} (ha : 0 ≤ X) (hb : X ≤ 1) :
    (1 / 1000000) ≤ B1 true 1 X := by
  have hu : 0 ≤ X - 0 := sub_nonneg.mpr ha
  have hv : 0 ≤ 1 - X := sub_nonneg.mpr hb
  have hcert : 0 ≤ B1 true 1 X - (1 / 1000000) := by
    calc
      0 ≤ (8567637871049 / 156250000000000) * (X - 0) ^ 0 * (1 - X) ^ 10 +
      (310571045396993 / 500000000000000) * (X - 0) ^ 1 * (1 - X) ^ 9 +
      (62610183330537801 / 20000000000000000) * (X - 0) ^ 2 * (1 - X) ^ 8 +
      (222531698962612051 / 24000000000000000) * (X - 0) ^ 3 * (1 - X) ^ 7 +
      (716864368368750583 / 40000000000000000) * (X - 0) ^ 4 * (1 - X) ^ 6 +
      (710531468374405999 / 30000000000000000) * (X - 0) ^ 5 * (1 - X) ^ 5 +
      (434791255575050367 / 20000000000000000) * (X - 0) ^ 6 * (1 - X) ^ 4 +
      (329638360975460257 / 24000000000000000) * (X - 0) ^ 7 * (1 - X) ^ 3 +
      (27561862145936563 / 4800000000000000) * (X - 0) ^ 8 * (1 - X) ^ 2 +
      (3461784497 / 2400000000) * (X - 0) ^ 9 * (1 - X) ^ 1 +
      (499397 / 3000000) * (X - 0) ^ 10 * (1 - X) ^ 0 := by positivity
      _ = B1 true 1 X - (1 / 1000000) := by
        dsimp only [p, v, k, h, pSeries, aSeries, bit, d, H, c, N, l, hh, uZero, uOne, Tk, T1, T2, Q0, Q1, Y, Yprime, B0, B1, B2, discr, total]
        norm_num
        ring
  linarith only [hcert]

theorem B1_1_1_positive {X : ℝ} (ha : 0 ≤ X) (hb : X ≤ 1) :
    (1 / 1000000) ≤ B1 true 1 X := by
  exact B1_1_1_positive_part0 ha hb

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

theorem bernCoeff_1_1_nonneg_s35_oai {X r : ℝ} (hX0 : 0 ≤ X) (hX : X ≤ 1)
    (hr0 : 0 ≤ r) (_hr : r ≤ 1) : 0 ≤ bernCoeff true 1 X r := by
  have ha := B0_1_1_nonneg hX0 hX
  unfold bernCoeff
  have hb := B1_1_1_positive hX0 hX
  have hbc := sum12_1_1_positive_s35 hX0 hX
  exact quadratic_of_end_slopes ha (by linarith) (by linarith) hr0 _hr

end MetricKMedian.Certificates


end
end

end OAI
end

theorem solution : type_of% @OAI.MetricKMedian.Certificates.bernCoeff_1_1_nonneg_s35_oai := @OAI.MetricKMedian.Certificates.bernCoeff_1_1_nonneg_s35_oai
