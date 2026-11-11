-- Prove2me | solution 1 for OAI.MetricKMedian.Certificates.diff02_1_3_positive_s35
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T15:11:34.942199+00:00
-- url     : https://prove2.me/submissions/d4155614-7fee-454e-a524-fe34474dd386

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

private theorem diff02_1_3_positive_part0 {X : ℝ} (ha : (3 / 4) ≤ X) (hb : X ≤ 1) :
    (1 / 1000000) ≤ B0 true 3 X-B2 true 3 X := by
  have hu : 0 ≤ X - (3 / 4) := sub_nonneg.mpr ha
  have hv : 0 ≤ 1 - X := sub_nonneg.mpr hb
  have hcert : 0 ≤ B0 true 3 X-B2 true 3 X - (1 / 1000000) := by
    calc
      0 ≤ (557154164748473971181226252847 / 100000000000000000000000) * (X - (3 / 4)) ^ 0 * (1 - X) ^ 12 +
      (3750511147630898767650656529923 / 50000000000000000000000) * (X - (3 / 4)) ^ 1 * (1 - X) ^ 11 +
      (11512504919094285243821997799233 / 25000000000000000000000) * (X - (3 / 4)) ^ 2 * (1 - X) ^ 10 +
      (21321893508743476102562670099773 / 12500000000000000000000) * (X - (3 / 4)) ^ 3 * (1 - X) ^ 9 +
      (6637683553391072338563283050663 / 1562500000000000000000) * (X - (3 / 4)) ^ 4 * (1 - X) ^ 8 +
      (5857194751162191362123921533877 / 781250000000000000000) * (X - (3 / 4)) ^ 5 * (1 - X) ^ 7 +
      (939245950409262313495080712943 / 97656250000000000000) * (X - (3 / 4)) ^ 6 * (1 - X) ^ 6 +
      (88278866608732912037631808899 / 9765625000000000000) * (X - (3 / 4)) ^ 7 * (1 - X) ^ 5 +
      (1508742454811783262234232501 / 244140625000000000) * (X - (3 / 4)) ^ 8 * (1 - X) ^ 4 +
      (73180003078917263308983727 / 24414062500000000) * (X - (3 / 4)) ^ 9 * (1 - X) ^ 3 +
      (149440953417840649306 / 152587890625) * (X - (3 / 4)) ^ 10 * (1 - X) ^ 2 +
      (378088021472256 / 1953125) * (X - (3 / 4)) ^ 11 * (1 - X) ^ 1 +
      (273560109056 / 15625) * (X - (3 / 4)) ^ 12 * (1 - X) ^ 0 := by positivity
      _ = B0 true 3 X-B2 true 3 X - (1 / 1000000) := by
        dsimp only [p, v, k, h, pSeries, aSeries, bit, d, H, c, N, l, hh, uZero, uOne, Tk, T1, T2, Q0, Q1, Y, Yprime, B0, B1, B2, discr, total]
        norm_num
        ring
  linarith only [hcert]

theorem diff02_1_3_positive_s35_oai {X : ℝ} (ha : (3 / 4) ≤ X) (hb : X ≤ 1) :
    (1 / 1000000) ≤ B0 true 3 X-B2 true 3 X := by
  exact diff02_1_3_positive_part0 ha hb

end MetricKMedian.Certificates


end
end

end OAI
end

theorem solution : type_of% @OAI.MetricKMedian.Certificates.diff02_1_3_positive_s35_oai := @OAI.MetricKMedian.Certificates.diff02_1_3_positive_s35_oai
