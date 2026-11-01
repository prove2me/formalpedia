-- Prove2me | solution 1 for OAI.MetricKMedian.Certificates.sum12_1_1_positive_s53
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T07:05:52.040731+00:00
-- url     : https://prove2.me/submissions/19972735-4142-42df-96c0-3d66ac4023d3

import Mathlib
import Definitions.Def_OAIQ053K002

section
-- module Solutions.OAIQ053_KM.KMedian_Analysis_BernsteinTrue
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.Certificates

private theorem sum12_1_1_positive_part0 {X : ℝ} (ha : 0 ≤ X) (hb : X ≤ 1) :
    (1 / 1000000) ≤ B1 true 1 X+B2 true 1 X := by
  have hu : 0 ≤ X - 0 := sub_nonneg.mpr ha
  have hv : 0 ≤ 1 - X := sub_nonneg.mpr hb
  have hcert : 0 ≤ B1 true 1 X+B2 true 1 X - (1 / 1000000) := by
    calc
      0 ≤ (25390682680813770843 / 195312500000000000000) * (X - 0) ^ 0 * (1 - X) ^ 13 +
      (13628643983204262556771 / 7812500000000000000000) * (X - 0) ^ 1 * (1 - X) ^ 12 +
      (2013202486168107763689187 / 187500000000000000000000) * (X - 0) ^ 2 * (1 - X) ^ 11 +
      (60200719446072943631404483 / 1500000000000000000000000) * (X - 0) ^ 3 * (1 - X) ^ 10 +
      (304905973285879211917909307 / 3000000000000000000000000) * (X - 0) ^ 4 * (1 - X) ^ 9 +
      (1104683759026154157412639349 / 6000000000000000000000000) * (X - 0) ^ 5 * (1 - X) ^ 8 +
      (2944795152899738879958551197 / 12000000000000000000000000) * (X - 0) ^ 6 * (1 - X) ^ 7 +
      (487195039931428609307066823 / 2000000000000000000000000) * (X - 0) ^ 7 * (1 - X) ^ 6 +
      (108012834937385984482694803 / 600000000000000000000000) * (X - 0) ^ 8 * (1 - X) ^ 5 +
      (11733440198906916822846869 / 120000000000000000000000) * (X - 0) ^ 9 * (1 - X) ^ 4 +
      (3640480960494626735465911 / 96000000000000000000000) * (X - 0) ^ 10 * (1 - X) ^ 3 +
      (477096289632780791 / 48000000000000000) * (X - 0) ^ 11 * (1 - X) ^ 2 +
      (2523595189 / 1600000000) * (X - 0) ^ 12 * (1 - X) ^ 1 +
      (343147 / 3000000) * (X - 0) ^ 13 * (1 - X) ^ 0 := by positivity
      _ = B1 true 1 X+B2 true 1 X - (1 / 1000000) := by
        dsimp only [p, v, k, h, pSeries, aSeries, bit, d, H, c, N, l, hh, uZero, uOne, Tk, T1, T2, Q0, Q1, Y, Yprime, B0, B1, B2, discr, total]
        norm_num
        ring
  linarith only [hcert]

theorem sum12_1_1_positive_s53_oai {X : ℝ} (ha : 0 ≤ X) (hb : X ≤ 1) :
    (1 / 1000000) ≤ B1 true 1 X+B2 true 1 X := by
  exact sum12_1_1_positive_part0 ha hb

end MetricKMedian.Certificates


end
end

end OAI
end

theorem solution : type_of% @OAI.MetricKMedian.Certificates.sum12_1_1_positive_s53_oai := @OAI.MetricKMedian.Certificates.sum12_1_1_positive_s53_oai
