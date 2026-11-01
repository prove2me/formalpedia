-- Prove2me | solution 1 for OAI.MetricKMedian.Certificates.v_upper_s53
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T07:07:21.104854+00:00
-- url     : https://prove2.me/submissions/813124a9-925c-420a-959d-3accc9d8652a

import Mathlib
import Definitions.Def_OAIQ053K002

section
-- module Solutions.OAIQ053_KM.KMedian_Analysis_PolynomialBounds
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

theorem v_upper_s53_oai {X : ℝ} (ha : 0 ≤ X) (hb : X ≤ 1) :
    0 ≤ 217/125 - v X := by
  exact v_upper_part0 ha hb


end MetricKMedian.Certificates
end
end

end OAI
end

theorem solution : type_of% @OAI.MetricKMedian.Certificates.v_upper_s53_oai := @OAI.MetricKMedian.Certificates.v_upper_s53_oai
