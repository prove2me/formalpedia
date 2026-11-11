-- Prove2me | solution 1 for OAI.MetricKMedian.Certificates.sum12_1_0_positive_s35
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T15:13:18.2272+00:00
-- url     : https://prove2.me/submissions/271a85c4-d385-4cc8-9bd2-8273dd076b11

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

private theorem sum12_1_0_positive_part0 {X : ℝ} (ha : 0 ≤ X) (hb : X ≤ 1) :
    (1 / 1000000) ≤ B1 true 0 X+B2 true 0 X := by
  have hu : 0 ≤ X - 0 := sub_nonneg.mpr ha
  have hv : 0 ≤ 1 - X := sub_nonneg.mpr hb
  have hcert : 0 ≤ B1 true 0 X+B2 true 0 X - (1 / 1000000) := by
    calc
      0 ≤ (25390682680813770843 / 195312500000000000000) * (X - 0) ^ 0 * (1 - X) ^ 13 +
      (14142150433767185667779 / 7812500000000000000000) * (X - 0) ^ 1 * (1 - X) ^ 12 +
      (722613782026809194827521 / 62500000000000000000000) * (X - 0) ^ 2 * (1 - X) ^ 11 +
      (22438045681557235527079649 / 500000000000000000000000) * (X - 0) ^ 3 * (1 - X) ^ 10 +
      (118155943357706365731549361 / 1000000000000000000000000) * (X - 0) ^ 4 * (1 - X) ^ 9 +
      (445883220989502164940488287 / 2000000000000000000000000) * (X - 0) ^ 5 * (1 - X) ^ 8 +
      (1240973423465457379450079911 / 4000000000000000000000000) * (X - 0) ^ 6 * (1 - X) ^ 7 +
      (644958624415145916597333217 / 2000000000000000000000000) * (X - 0) ^ 7 * (1 - X) ^ 6 +
      (25042469956333206810082027 / 100000000000000000000000) * (X - 0) ^ 8 * (1 - X) ^ 5 +
      (2870249386489717627118121 / 20000000000000000000000) * (X - 0) ^ 9 * (1 - X) ^ 4 +
      (1887873323474096942552273 / 32000000000000000000000) * (X - 0) ^ 10 * (1 - X) ^ 3 +
      (263569743097583447 / 16000000000000000) * (X - 0) ^ 11 * (1 - X) ^ 2 +
      (4479161169 / 1600000000) * (X - 0) ^ 12 * (1 - X) ^ 1 +
      (218549 / 1000000) * (X - 0) ^ 13 * (1 - X) ^ 0 := by positivity
      _ = B1 true 0 X+B2 true 0 X - (1 / 1000000) := by
        dsimp only [p, v, k, h, pSeries, aSeries, bit, d, H, c, N, l, hh, uZero, uOne, Tk, T1, T2, Q0, Q1, Y, Yprime, B0, B1, B2, discr, total]
        norm_num
        ring
  linarith only [hcert]

theorem sum12_1_0_positive_s35_oai {X : ℝ} (ha : 0 ≤ X) (hb : X ≤ 1) :
    (1 / 1000000) ≤ B1 true 0 X+B2 true 0 X := by
  exact sum12_1_0_positive_part0 ha hb

end MetricKMedian.Certificates


end
end

end OAI
end

theorem solution : type_of% @OAI.MetricKMedian.Certificates.sum12_1_0_positive_s35_oai := @OAI.MetricKMedian.Certificates.sum12_1_0_positive_s35_oai
