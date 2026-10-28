-- Prove2me | solution 1 for OAI.MetricKMedian.Certificates.h_lower_s35
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T10:52:16.163676+00:00
-- url     : https://prove2.me/submissions/6aad8329-33b5-4b74-9e2f-33cf67369794

import Mathlib
import Definitions.Def_OAIQ035K002

section
-- module Solutions.OAIQ035_KM.KMedian_Analysis_PolynomialBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.Certificates

private theorem h_lower_part0 {X : ℝ} (ha : 0 ≤ X) (hb : X ≤ 1) :
    (7 / 500) ≤ h X := by
  have hu : 0 ≤ X - 0 := sub_nonneg.mpr ha
  have hv : 0 ≤ 1 - X := sub_nonneg.mpr hb
  have hcert : 0 ≤ h X - (7 / 500) := by
    calc
      0 ≤ (19 / 50) * (X - 0) ^ 0 * (1 - X) ^ 3 +
      (57 / 50) * (X - 0) ^ 1 * (1 - X) ^ 2 +
      (18 / 25) * (X - 0) ^ 2 * (1 - X) ^ 1 := by positivity
      _ = h X - (7 / 500) := by
        dsimp only [p, v, k, h]
        norm_num
        ring
  linarith only [hcert]

theorem h_lower_s35_oai {X : ℝ} (ha : 0 ≤ X) (hb : X ≤ 1) :
    (7 / 500) ≤ h X := by
  exact h_lower_part0 ha hb


end MetricKMedian.Certificates
end
end

end OAI
end

theorem solution : type_of% @OAI.MetricKMedian.Certificates.h_lower_s35_oai := @OAI.MetricKMedian.Certificates.h_lower_s35_oai
