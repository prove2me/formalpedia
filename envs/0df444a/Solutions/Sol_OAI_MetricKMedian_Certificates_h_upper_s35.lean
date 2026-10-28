-- Prove2me | solution 1 for OAI.MetricKMedian.Certificates.h_upper_s35
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T10:52:17.138371+00:00
-- url     : https://prove2.me/submissions/2b92661c-0dec-4a2c-92ab-6ecc17647d8c

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

private theorem h_upper_part0 {X : ℝ} (ha : 0 ≤ X) (hb : X ≤ 1) :
    0 ≤ 197/500-h X := by
  have hu : 0 ≤ X - 0 := sub_nonneg.mpr ha
  have hv : 0 ≤ 1 - X := sub_nonneg.mpr hb
  have hcert : 0 ≤ 197/500-h X - 0 := by
    calc
      0 ≤ (21 / 50) * (X - 0) ^ 2 * (1 - X) ^ 1 +
      (19 / 50) * (X - 0) ^ 3 * (1 - X) ^ 0 := by positivity
      _ = 197/500-h X - 0 := by
        dsimp only [p, v, k, h]
        norm_num
        ring
  linarith only [hcert]

theorem h_upper_s35_oai {X : ℝ} (ha : 0 ≤ X) (hb : X ≤ 1) :
    0 ≤ 197/500-h X := by
  exact h_upper_part0 ha hb


end MetricKMedian.Certificates
end
end

end OAI
end

theorem solution : type_of% @OAI.MetricKMedian.Certificates.h_upper_s35_oai := @OAI.MetricKMedian.Certificates.h_upper_s35_oai
