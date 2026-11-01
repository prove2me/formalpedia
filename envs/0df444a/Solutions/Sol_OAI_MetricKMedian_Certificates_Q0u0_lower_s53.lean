-- Prove2me | solution 1 for OAI.MetricKMedian.Certificates.Q0u0_lower_s53
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T06:54:02.145546+00:00
-- url     : https://prove2.me/submissions/18ebbf8d-7ae0-4d4c-afe6-c5b429d2d5f9

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

private theorem Q0u0_lower_part0 {X : ℝ} (ha : (65 / 226) ≤ X) (hb : X ≤ 1) :
    (1 / 4000) ≤ Q0 false (uZero false) X := by
  have hu : 0 ≤ X - (65 / 226) := sub_nonneg.mpr ha
  have hv : 0 ≤ 1 - X := sub_nonneg.mpr hb
  have hcert : 0 ≤ Q0 false (uZero false) X - (1 / 4000) := by
    calc
      0 ≤ (15377419780272212549 / 94905626541250000000) * (X - (65 / 226)) ^ 0 * (1 - X) ^ 4 +
      (2147829825253719941 / 1679745602500000000) * (X - (65 / 226)) ^ 1 * (1 - X) ^ 3 +
      (1249326404997110679 / 419936400625000000) * (X - (65 / 226)) ^ 2 * (1 - X) ^ 2 +
      (1158291035533895693 / 419936400625000000) * (X - (65 / 226)) ^ 3 * (1 - X) ^ 1 +
      (760033008677 / 839872801250) * (X - (65 / 226)) ^ 4 * (1 - X) ^ 0 := by positivity
      _ = Q0 false (uZero false) X - (1 / 4000) := by
        dsimp only [p, v, k, h, pSeries, aSeries, bit, d, H, c, N, l, hh, uZero, uOne, Tk, T1, T2, Q0, Q1, Y, Yprime, B0, B1, B2, discr, total]
        norm_num
        ring
  linarith only [hcert]

theorem Q0u0_lower_s53_oai {X : ℝ} (ha : (65 / 226) ≤ X) (hb : X ≤ 1) :
    (1 / 4000) ≤ Q0 false (uZero false) X := by
  exact Q0u0_lower_part0 ha hb


end MetricKMedian.Certificates
end
end

end OAI
end

theorem solution : type_of% @OAI.MetricKMedian.Certificates.Q0u0_lower_s53_oai := @OAI.MetricKMedian.Certificates.Q0u0_lower_s53_oai
