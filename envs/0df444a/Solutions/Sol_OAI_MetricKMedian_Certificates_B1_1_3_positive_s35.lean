-- Prove2me | solution 1 for OAI.MetricKMedian.Certificates.B1_1_3_positive_s35
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T15:11:29.783762+00:00
-- url     : https://prove2.me/submissions/38319ed6-9f34-4560-bf79-06f12b198573

import Mathlib
import Definitions.Def_OAIQ035K002

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

private theorem B1_1_3_positive_part0 {X : ℝ} (ha : 0 ≤ X) (hb : X ≤ (1 / 10)) :
    (1 / 1000000) ≤ B1 true 3 X := by
  have hu : 0 ≤ X - 0 := sub_nonneg.mpr ha
  have hv : 0 ≤ (1 / 10) - X := sub_nonneg.mpr hb
  have hcert : 0 ≤ B1 true 3 X - (1 / 1000000) := by
    calc
      0 ≤ (137082205936784 / 25) * (X - 0) ^ 0 * ((1 / 10) - X) ^ 14 +
      (18214351190851173 / 250) * (X - 0) ^ 1 * ((1 / 10) - X) ^ 13 +
      (17469767411133244725367317 / 39062500000) * (X - 0) ^ 2 * ((1 / 10) - X) ^ 12 +
      (1312269005670951549977567849 / 781250000000) * (X - 0) ^ 3 * ((1 / 10) - X) ^ 11 +
      (16829189981674752245482747089 / 3906250000000) * (X - 0) ^ 4 * ((1 / 10) - X) ^ 10 +
      (311453786920677290508436591621 / 39062500000000) * (X - 0) ^ 5 * ((1 / 10) - X) ^ 9 +
      (17128391607979234327456532952443 / 1562500000000000) * (X - 0) ^ 6 * ((1 / 10) - X) ^ 8 +
      (354694066230846219168589998835539 / 31250000000000000) * (X - 0) ^ 7 * ((1 / 10) - X) ^ 7 +
      (5541992587901687326254958295186513 / 625000000000000000) * (X - 0) ^ 8 * ((1 / 10) - X) ^ 6 +
      (6474165893398349395753415175789799 / 1250000000000000000) * (X - 0) ^ 9 * ((1 / 10) - X) ^ 5 +
      (138258845199245800194458913970599259 / 62500000000000000000) * (X - 0) ^ 10 * ((1 / 10) - X) ^ 4 +
      (414319294108854207554588470746294643 / 625000000000000000000) * (X - 0) ^ 11 * ((1 / 10) - X) ^ 3 +
      (40400675876549674022919438710975239 / 312500000000000000000) * (X - 0) ^ 12 * ((1 / 10) - X) ^ 2 +
      (11028002236615122660021806671478237 / 781250000000000000000) * (X - 0) ^ 13 * ((1 / 10) - X) ^ 1 +
      (5701169148764459952215997345453309 / 9765625000000000000000) * (X - 0) ^ 14 * ((1 / 10) - X) ^ 0 := by positivity
      _ = B1 true 3 X - (1 / 1000000) := by
        dsimp only [p, v, k, h, pSeries, aSeries, bit, d, H, c, N, l, hh, uZero, uOne, Tk, T1, T2, Q0, Q1, Y, Yprime, B0, B1, B2, discr, total]
        norm_num
        ring
  linarith only [hcert]

theorem B1_1_3_positive_s35_oai {X : ℝ} (ha : 0 ≤ X) (hb : X ≤ (1 / 10)) :
    (1 / 1000000) ≤ B1 true 3 X := by
  exact B1_1_3_positive_part0 ha hb

end MetricKMedian.Certificates


end
end

end OAI
end

theorem solution : type_of% @OAI.MetricKMedian.Certificates.B1_1_3_positive_s35_oai := @OAI.MetricKMedian.Certificates.B1_1_3_positive_s35_oai
