-- Prove2me | solution 1 for OAI.MetricKMedian.Certificates.total_1_3_positive_s53
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T07:05:52.932989+00:00
-- url     : https://prove2.me/submissions/13502a07-8575-47a4-ae0f-c10140535dbe

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

private theorem total_1_3_positive_part0 {X : ℝ} (ha : (3 / 4) ≤ X) (hb : X ≤ 1) :
    (1 / 1000000) ≤ total true 3 X := by
  have hu : 0 ≤ X - (3 / 4) := sub_nonneg.mpr ha
  have hv : 0 ≤ 1 - X := sub_nonneg.mpr hb
  have hcert : 0 ≤ total true 3 X - (1 / 1000000) := by
    calc
      0 ≤ (5177338351469559690955928230071 / 156250000000000000000000) * (X - (3 / 4)) ^ 0 * (1 - X) ^ 14 +
      (9242300511560665775324940509423 / 19531250000000000000000) * (X - (3 / 4)) ^ 1 * (1 - X) ^ 13 +
      (490908937942536635248537251271713 / 156250000000000000000000) * (X - (3 / 4)) ^ 2 * (1 - X) ^ 12 +
      (200837920789819309984342649943777 / 15625000000000000000000) * (X - (3 / 4)) ^ 3 * (1 - X) ^ 11 +
      (1414010826655827227350886146521283 / 39062500000000000000000) * (X - (3 / 4)) ^ 4 * (1 - X) ^ 10 +
      (1449826369912680180843249766093579 / 19531250000000000000000) * (X - (3 / 4)) ^ 5 * (1 - X) ^ 9 +
      (279052702743706295386042755369517 / 2441406250000000000000) * (X - (3 / 4)) ^ 6 * (1 - X) ^ 8 +
      (163869140579390652976018098346611 / 1220703125000000000000) * (X - (3 / 4)) ^ 7 * (1 - X) ^ 7 +
      (18438107973899850425046829809821 / 152587890625000000000) * (X - (3 / 4)) ^ 8 * (1 - X) ^ 6 +
      (1265751431455382151213448826613 / 15258789062500000000) * (X - (3 / 4)) ^ 9 * (1 - X) ^ 5 +
      (16306934466486930610222112967 / 381469726562500000) * (X - (3 / 4)) ^ 10 * (1 - X) ^ 4 +
      (611661093558924168591334089 / 38146972656250000) * (X - (3 / 4)) ^ 11 * (1 - X) ^ 3 +
      (126280084306610787232 / 30517578125) * (X - (3 / 4)) ^ 12 * (1 - X) ^ 2 +
      (256869517443072 / 390625) * (X - (3 / 4)) ^ 13 * (1 - X) ^ 1 +
      (758535684096 / 15625) * (X - (3 / 4)) ^ 14 * (1 - X) ^ 0 := by positivity
      _ = total true 3 X - (1 / 1000000) := by
        dsimp only [p, v, k, h, pSeries, aSeries, bit, d, H, c, N, l, hh, uZero, uOne, Tk, T1, T2, Q0, Q1, Y, Yprime, B0, B1, B2, discr, total]
        norm_num
        ring
  linarith only [hcert]

theorem total_1_3_positive_s53_oai {X : ℝ} (ha : (3 / 4) ≤ X) (hb : X ≤ 1) :
    (1 / 1000000) ≤ total true 3 X := by
  exact total_1_3_positive_part0 ha hb

end MetricKMedian.Certificates


end
end

end OAI
end

theorem solution : type_of% @OAI.MetricKMedian.Certificates.total_1_3_positive_s53_oai := @OAI.MetricKMedian.Certificates.total_1_3_positive_s53_oai
