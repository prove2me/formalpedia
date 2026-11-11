-- Prove2me | solution 1 for OAI.MetricKMedian.Certificates.v_upper_s35
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T15:13:51.971313+00:00
-- url     : https://prove2.me/submissions/71d66c08-fecf-4d55-a3ea-4c17dc5d8a98

import Mathlib
import Definitions.Def_OAIQ035K002

section
-- module Solutions.Q224_RR.KMedian_Analysis_PolynomialBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.Certificates

private theorem v_upper_part0 {X : ℝ} (ha : 0 ≤ X) (hb : X ≤ 1) :
    0 ≤ 217/125 - v X := by
  have hu : 0 ≤ X - 0 := sub_nonneg.mpr ha
  have hv : 0 ≤ 1 - X := sub_nonneg.mpr hb
  have hcert : 0 ≤ 217/125 - v X - 0 := by
    calc
      0 ≤ (1507 / 6250000) * (X - 0) ^ 0 * (1 - X) ^ 4 +
      (52928717 / 100000000) * (X - 0) ^ 1 * (1 - X) ^ 3 +
      (43708143 / 25000000) * (X - 0) ^ 2 * (1 - X) ^ 2 +
      (194418379 / 100000000) * (X - 0) ^ 3 * (1 - X) ^ 1 +
      (92 / 125) * (X - 0) ^ 4 * (1 - X) ^ 0 := by positivity
      _ = 217/125 - v X - 0 := by
        dsimp only [p, v, k, h]
        norm_num
        ring
  linarith only [hcert]

theorem v_upper_s35_oai {X : ℝ} (ha : 0 ≤ X) (hb : X ≤ 1) :
    0 ≤ 217/125 - v X := by
  exact v_upper_part0 ha hb


end MetricKMedian.Certificates
end
end

end OAI
end

theorem solution : type_of% @OAI.MetricKMedian.Certificates.v_upper_s35_oai := @OAI.MetricKMedian.Certificates.v_upper_s35_oai
