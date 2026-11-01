-- Prove2me | solution 1 for OAI.MetricKMedian.Certificates.Q0X0_lower_s53
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T06:53:37.295196+00:00
-- url     : https://prove2.me/submissions/75a6902d-f0e1-4146-bb6f-e2973840a51e

import Mathlib
import Definitions.Def_OAIQ053K002

section
-- module Solutions.OAIQ053_KM.KMedian_Analysis_ScalarCertificates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.Certificates

private theorem Q0X0_lower_part0 {X : ℝ} (ha : 0 ≤ X) (hb : X ≤ (65 / 226)) :
    (1 / 4000) ≤ Q0 false X X := by
  have hu : 0 ≤ X - 0 := sub_nonneg.mpr ha
  have hv : 0 ≤ (65 / 226) - X := sub_nonneg.mpr hb
  have hcert : 0 ≤ Q0 false X X - (1 / 4000) := by
    calc
      0 ≤ (26616949523729557926 / 736512603759765625) * (X - 0) ^ 0 * ((65 / 226) - X) ^ 6 +
      (1108505996305909349273 / 5892100830078125000) * (X - 0) ^ 1 * ((65 / 226) - X) ^ 5 +
      (1070555096566927387931 / 2356840332031250000) * (X - 0) ^ 2 * ((65 / 226) - X) ^ 4 +
      (196730605689159043317 / 294605041503906250) * (X - 0) ^ 3 * ((65 / 226) - X) ^ 3 +
      (728676237597742428583 / 1178420166015625000) * (X - 0) ^ 4 * ((65 / 226) - X) ^ 2 +
      (15391598916307421235999 / 47136806640625000000) * (X - 0) ^ 5 * ((65 / 226) - X) ^ 1 +
      (1737648435170760018037 / 23568403320312500000) * (X - 0) ^ 6 * ((65 / 226) - X) ^ 0 := by positivity
      _ = Q0 false X X - (1 / 4000) := by
        dsimp only [p, v, k, h, pSeries, aSeries, bit, d, H, c, N, l, hh, uZero, uOne, Tk, T1, T2, Q0, Q1, Y, Yprime, B0, B1, B2, discr, total]
        norm_num
        ring
  linarith only [hcert]

theorem Q0X0_lower_s53_oai {X : ℝ} (ha : 0 ≤ X) (hb : X ≤ (65 / 226)) :
    (1 / 4000) ≤ Q0 false X X := by
  exact Q0X0_lower_part0 ha hb


end MetricKMedian.Certificates
end
end

end OAI
end

theorem solution : type_of% @OAI.MetricKMedian.Certificates.Q0X0_lower_s53_oai := @OAI.MetricKMedian.Certificates.Q0X0_lower_s53_oai
