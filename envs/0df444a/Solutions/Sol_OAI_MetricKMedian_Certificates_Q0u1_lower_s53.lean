-- Prove2me | solution 1 for OAI.MetricKMedian.Certificates.Q0u1_lower_s53
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T06:54:25.861179+00:00
-- url     : https://prove2.me/submissions/6302b04b-bb2e-4e64-aa7d-d841202baf79

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

private theorem Q0u1_lower_part0 {X : ℝ} (ha : 0 ≤ X) (hb : X ≤ 1) :
    (1 / 4000) ≤ Q0 true (uZero true) X := by
  have hu : 0 ≤ X - 0 := sub_nonneg.mpr ha
  have hv : 0 ≤ 1 - X := sub_nonneg.mpr hb
  have hcert : 0 ≤ Q0 true (uZero true) X - (1 / 4000) := by
    calc
      0 ≤ (1073963 / 62500000) * (X - 0) ^ 0 * (1 - X) ^ 4 +
      (288567027 / 2750000000) * (X - 0) ^ 1 * (1 - X) ^ 3 +
      (293860011 / 1375000000) * (X - 0) ^ 2 * (1 - X) ^ 2 +
      (497217619 / 2750000000) * (X - 0) ^ 3 * (1 - X) ^ 1 +
      (2389 / 44000) * (X - 0) ^ 4 * (1 - X) ^ 0 := by positivity
      _ = Q0 true (uZero true) X - (1 / 4000) := by
        dsimp only [p, v, k, h, pSeries, aSeries, bit, d, H, c, N, l, hh, uZero, uOne, Tk, T1, T2, Q0, Q1, Y, Yprime, B0, B1, B2, discr, total]
        norm_num
        ring
  linarith only [hcert]

theorem Q0u1_lower_s53_oai {X : ℝ} (ha : 0 ≤ X) (hb : X ≤ 1) :
    (1 / 4000) ≤ Q0 true (uZero true) X := by
  exact Q0u1_lower_part0 ha hb


end MetricKMedian.Certificates
end
end

end OAI
end

theorem solution : type_of% @OAI.MetricKMedian.Certificates.Q0u1_lower_s53_oai := @OAI.MetricKMedian.Certificates.Q0u1_lower_s53_oai
