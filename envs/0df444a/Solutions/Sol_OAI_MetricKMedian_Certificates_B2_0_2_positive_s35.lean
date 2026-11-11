-- Prove2me | solution 1 for OAI.MetricKMedian.Certificates.B2_0_2_positive_s35
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T15:10:10.104906+00:00
-- url     : https://prove2.me/submissions/a597d913-8e95-4191-8456-c762474788fd

import Mathlib
import Definitions.Def_OAIQ035K002

section
-- module Solutions.Q224_RR.KMedian_Analysis_BernsteinFalse
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.Certificates

private theorem B2_0_2_positive_part0 {X : ℝ} (ha : 0 ≤ X) (hb : X ≤ (1 / 20)) :
    (1 / 1000000) ≤ B2 false 2 X := by
  have hu : 0 ≤ X - 0 := sub_nonneg.mpr ha
  have hv : 0 ≤ (1 / 20) - X := sub_nonneg.mpr hb
  have hcert : 0 ≤ B2 false 2 X - (1 / 1000000) := by
    calc
      0 ≤ (15004960525533184 / 15625) * (X - 0) ^ 0 * ((1 / 20) - X) ^ 10 +
      (2262580197231215744 / 234375) * (X - 0) ^ 1 * ((1 / 20) - X) ^ 9 +
      (51194791997818033468 / 1171875) * (X - 0) ^ 2 * ((1 / 20) - X) ^ 8 +
      (1373382823587668849611 / 11718750) * (X - 0) ^ 3 * ((1 / 20) - X) ^ 7 +
      (4837387055958716631677 / 23437500) * (X - 0) ^ 4 * ((1 / 20) - X) ^ 6 +
      (36523596093841673767403 / 146484375) * (X - 0) ^ 5 * ((1 / 20) - X) ^ 5 +
      (653881041258482516624063 / 3125000000) * (X - 0) ^ 6 * ((1 / 20) - X) ^ 4 +
      (75280192828135071628332079 / 625000000000) * (X - 0) ^ 7 * ((1 / 20) - X) ^ 3 +
      (853417355009828912047275469 / 18750000000000) * (X - 0) ^ 8 * ((1 / 20) - X) ^ 2 +
      (1911662500729904167591116733 / 187500000000000) * (X - 0) ^ 9 * ((1 / 20) - X) ^ 1 +
      (1927539652411855279139835661 / 1875000000000000) * (X - 0) ^ 10 * ((1 / 20) - X) ^ 0 := by positivity
      _ = B2 false 2 X - (1 / 1000000) := by
        dsimp only [p, v, k, h, pSeries, aSeries, bit, d, H, c, N, l, hh, uZero, uOne, Tk, T1, T2, Q0, Q1, Y, Yprime, B0, B1, B2, discr, total]
        norm_num
        ring
  linarith only [hcert]

theorem B2_0_2_positive_s35_oai {X : ℝ} (ha : 0 ≤ X) (hb : X ≤ (1 / 20)) :
    (1 / 1000000) ≤ B2 false 2 X := by
  exact B2_0_2_positive_part0 ha hb


end MetricKMedian.Certificates
end
end

end OAI
end

theorem solution : type_of% @OAI.MetricKMedian.Certificates.B2_0_2_positive_s35_oai := @OAI.MetricKMedian.Certificates.B2_0_2_positive_s35_oai
