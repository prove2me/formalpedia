-- Prove2me | solution 1 for OAI.MetricKMedian.Certificates.B2_1_3_positive_s53
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T06:53:14.639985+00:00
-- url     : https://prove2.me/submissions/1ea3df13-08eb-48c2-9b67-237b73ae5aba

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

private theorem B2_1_3_positive_part0 {X : ℝ} (ha : 0 ≤ X) (hb : X ≤ (1 / 10)) :
    (1 / 1000000) ≤ B2 true 3 X := by
  have hu : 0 ≤ X - 0 := sub_nonneg.mpr ha
  have hv : 0 ≤ (1 / 10) - X := sub_nonneg.mpr hb
  have hcert : 0 ≤ B2 true 3 X - (1 / 1000000) := by
    calc
      0 ≤ (14680940029502520843 / 195312500) * (X - 0) ^ 0 * ((1 / 10) - X) ^ 12 +
      (14584121171120087983559 / 15625000000) * (X - 0) ^ 1 * ((1 / 10) - X) ^ 11 +
      (6634565113765036106051509 / 1250000000000) * (X - 0) ^ 2 * ((1 / 10) - X) ^ 10 +
      (1827709354796183564891426133 / 100000000000000) * (X - 0) ^ 3 * ((1 / 10) - X) ^ 9 +
      (84900893337649044780810797557 / 2000000000000000) * (X - 0) ^ 4 * ((1 / 10) - X) ^ 8 +
      (2802464664073265848931581789461 / 40000000000000000) * (X - 0) ^ 5 * ((1 / 10) - X) ^ 7 +
      (67405806102614550001210083563487 / 800000000000000000) * (X - 0) ^ 6 * ((1 / 10) - X) ^ 6 +
      (119036247594999125639307062210201 / 1600000000000000000) * (X - 0) ^ 7 * ((1 / 10) - X) ^ 5 +
      (3829666896855539966346617499400741 / 80000000000000000000) * (X - 0) ^ 8 * ((1 / 10) - X) ^ 4 +
      (17512853203451771361703252513705357 / 800000000000000000000) * (X - 0) ^ 9 * ((1 / 10) - X) ^ 3 +
      (2701381641414525503468137704024761 / 400000000000000000000) * (X - 0) ^ 10 * ((1 / 10) - X) ^ 2 +
      (1262037339324857133372455428521763 / 1000000000000000000000) * (X - 0) ^ 11 * ((1 / 10) - X) ^ 1 +
      (1350492249660466773258895779546691 / 12500000000000000000000) * (X - 0) ^ 12 * ((1 / 10) - X) ^ 0 := by positivity
      _ = B2 true 3 X - (1 / 1000000) := by
        dsimp only [p, v, k, h, pSeries, aSeries, bit, d, H, c, N, l, hh, uZero, uOne, Tk, T1, T2, Q0, Q1, Y, Yprime, B0, B1, B2, discr, total]
        norm_num
        ring
  linarith only [hcert]

theorem B2_1_3_positive_s53_oai {X : ℝ} (ha : 0 ≤ X) (hb : X ≤ (1 / 10)) :
    (1 / 1000000) ≤ B2 true 3 X := by
  exact B2_1_3_positive_part0 ha hb

end MetricKMedian.Certificates


end
end

end OAI
end

theorem solution : type_of% @OAI.MetricKMedian.Certificates.B2_1_3_positive_s53_oai := @OAI.MetricKMedian.Certificates.B2_1_3_positive_s53_oai
