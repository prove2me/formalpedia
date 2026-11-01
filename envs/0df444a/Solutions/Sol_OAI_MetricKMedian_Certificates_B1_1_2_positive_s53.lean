-- Prove2me | solution 1 for OAI.MetricKMedian.Certificates.B1_1_2_positive_s53
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T06:52:04.506493+00:00
-- url     : https://prove2.me/submissions/4675bf61-5f8b-4041-95b8-0a15738b3afd

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

private theorem B1_1_2_positive_part0 {X : ℝ} (ha : 0 ≤ X) (hb : X ≤ (1 / 5)) :
    (1 / 1000000) ≤ B1 true 2 X := by
  have hu : 0 ≤ X - 0 := sub_nonneg.mpr ha
  have hv : 0 ≤ (1 / 5) - X := sub_nonneg.mpr hb
  have hcert : 0 ≤ B1 true 2 X - (1 / 1000000) := by
    calc
      0 ≤ (8567637871049 / 25600) * (X - 0) ^ 0 * ((1 / 5) - X) ^ 14 +
      (9198192179234149 / 2048000) * (X - 0) ^ 1 * ((1 / 5) - X) ^ 13 +
      (4456120127542790664966189 / 160000000000000) * (X - 0) ^ 2 * ((1 / 5) - X) ^ 12 +
      (169127986615603584871840353 / 1600000000000000) * (X - 0) ^ 3 * ((1 / 5) - X) ^ 11 +
      (6578660390535926744299689833 / 24000000000000000) * (X - 0) ^ 4 * ((1 / 5) - X) ^ 10 +
      (20529293455123025474969620989 / 40000000000000000) * (X - 0) ^ 5 * ((1 / 5) - X) ^ 9 +
      (857507925145750952740712814913 / 1200000000000000000) * (X - 0) ^ 6 * ((1 / 5) - X) ^ 8 +
      (9003896333424978269591354831299 / 12000000000000000000) * (X - 0) ^ 7 * ((1 / 5) - X) ^ 7 +
      (71479170707134866606558640411183 / 120000000000000000000) * (X - 0) ^ 8 * ((1 / 5) - X) ^ 6 +
      (42555777800834319098524034365111 / 120000000000000000000) * (X - 0) ^ 9 * ((1 / 5) - X) ^ 5 +
      (155126190072570554395810616608503 / 1000000000000000000000) * (X - 0) ^ 10 * ((1 / 5) - X) ^ 4 +
      (239962251357312565767822618877321 / 5000000000000000000000) * (X - 0) ^ 11 * ((1 / 5) - X) ^ 3 +
      (12257975848179926061422487748681 / 1250000000000000000000) * (X - 0) ^ 12 * ((1 / 5) - X) ^ 2 +
      (1809332424429439204603682537299 / 1562500000000000000000) * (X - 0) ^ 13 * ((1 / 5) - X) ^ 1 +
      (1660954515664132860919067524109 / 29296875000000000000000) * (X - 0) ^ 14 * ((1 / 5) - X) ^ 0 := by positivity
      _ = B1 true 2 X - (1 / 1000000) := by
        dsimp only [p, v, k, h, pSeries, aSeries, bit, d, H, c, N, l, hh, uZero, uOne, Tk, T1, T2, Q0, Q1, Y, Yprime, B0, B1, B2, discr, total]
        norm_num
        ring
  linarith only [hcert]

theorem B1_1_2_positive_s53_oai {X : ℝ} (ha : 0 ≤ X) (hb : X ≤ (1 / 5)) :
    (1 / 1000000) ≤ B1 true 2 X := by
  exact B1_1_2_positive_part0 ha hb

end MetricKMedian.Certificates


end
end

end OAI
end

theorem solution : type_of% @OAI.MetricKMedian.Certificates.B1_1_2_positive_s53_oai := @OAI.MetricKMedian.Certificates.B1_1_2_positive_s53_oai
