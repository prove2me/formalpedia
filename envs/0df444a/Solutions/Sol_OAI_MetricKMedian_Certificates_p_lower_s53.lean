-- Prove2me | solution 1 for OAI.MetricKMedian.Certificates.p_lower_s53
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T07:04:14.041926+00:00
-- url     : https://prove2.me/submissions/e4d2aa8a-a46e-40cd-a291-e415844cd081

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
private theorem p_lower_part0 {X : ℝ} (ha : 0 ≤ X) (hb : X ≤ 1) :
    (1651507 / 6250000) ≤ p X := by
  have hu : 0 ≤ X - 0 := sub_nonneg.mpr ha
  have hv : 0 ≤ 1 - X := sub_nonneg.mpr hb
  have hcert : 0 ≤ p X - (1651507 / 6250000) := by
    calc
      0 ≤ (8026757 / 50000000) * (X - 0) ^ 1 * (1 - X) ^ 3 +
      (53912437 / 100000000) * (X - 0) ^ 2 * (1 - X) ^ 2 +
      (60978037 / 100000000) * (X - 0) ^ 3 * (1 - X) ^ 1 +
      (1473493 / 6250000) * (X - 0) ^ 4 * (1 - X) ^ 0 := by positivity
      _ = p X - (1651507 / 6250000) := by
        dsimp only [p, v, k, h]
        norm_num
        ring
  linarith only [hcert]

theorem p_lower_s53_oai {X : ℝ} (ha : 0 ≤ X) (hb : X ≤ 1) :
    (1651507 / 6250000) ≤ p X := by
  exact p_lower_part0 ha hb


end MetricKMedian.Certificates
end
end

end OAI
end

theorem solution : type_of% @OAI.MetricKMedian.Certificates.p_lower_s53_oai := @OAI.MetricKMedian.Certificates.p_lower_s53_oai
