-- Prove2me | solution 1 for OAI.MetricKMedian.Certificates.B2_1_2_positive_s35
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T15:11:32.495203+00:00
-- url     : https://prove2.me/submissions/1e972018-12ec-4c5c-869d-db367271d701

import Mathlib
import Definitions.Def_OAIQ035K002

section
-- module Solutions.Q224_RR.KMedian_Analysis_BernsteinTrue
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.Certificates

private theorem B2_1_2_positive_part0 {X : ℝ} (ha : 0 ≤ X) (hb : X ≤ (1 / 5)) :
    (1 / 1000000) ≤ B2 true 2 X := by
  have hu : 0 ≤ X - 0 := sub_nonneg.mpr ha
  have hv : 0 ≤ (1 / 5) - X := sub_nonneg.mpr hb
  have hcert : 0 ≤ B2 true 2 X - (1 / 1000000) := by
    calc
      0 ≤ (14680940029502520843 / 160000000000) * (X - 0) ^ 0 * ((1 / 5) - X) ^ 13 +
      (39324808603889517174203 / 32000000000000) * (X - 0) ^ 1 * ((1 / 5) - X) ^ 12 +
      (29147878182387197846621227 / 3840000000000000) * (X - 0) ^ 2 * ((1 / 5) - X) ^ 11 +
      (4397753279898361284174624227 / 153600000000000000) * (X - 0) ^ 3 * ((1 / 5) - X) ^ 10 +
      (113022005095359183918713297491 / 1536000000000000000) * (X - 0) ^ 4 * ((1 / 5) - X) ^ 9 +
      (696658414740081524975948437623 / 5120000000000000000) * (X - 0) ^ 5 * ((1 / 5) - X) ^ 8 +
      (28609601779392791710084851537797 / 153600000000000000000) * (X - 0) ^ 6 * ((1 / 5) - X) ^ 7 +
      (73387472881016143372648664211341 / 384000000000000000000) * (X - 0) ^ 7 * ((1 / 5) - X) ^ 6 +
      (7055251623764123183104763006287 / 48000000000000000000) * (X - 0) ^ 8 * ((1 / 5) - X) ^ 5 +
      (100428901894467247261637569752151 / 1200000000000000000000) * (X - 0) ^ 9 * ((1 / 5) - X) ^ 4 +
      (3291973197794483737708448624067727 / 96000000000000000000000) * (X - 0) ^ 10 * ((1 / 5) - X) ^ 3 +
      (76600027459035844428626276199459 / 8000000000000000000000) * (X - 0) ^ 11 * ((1 / 5) - X) ^ 2 +
      (9798287030832310305524250915701 / 6000000000000000000000) * (X - 0) ^ 12 * ((1 / 5) - X) ^ 1 +
      (8030458026922938465597986564837 / 62500000000000000000000) * (X - 0) ^ 13 * ((1 / 5) - X) ^ 0 := by positivity
      _ = B2 true 2 X - (1 / 1000000) := by
        dsimp only [p, v, k, h, pSeries, aSeries, bit, d, H, c, N, l, hh, uZero, uOne, Tk, T1, T2, Q0, Q1, Y, Yprime, B0, B1, B2, discr, total]
        norm_num
        ring
  linarith only [hcert]

theorem B2_1_2_positive_s35_oai {X : ℝ} (ha : 0 ≤ X) (hb : X ≤ (1 / 5)) :
    (1 / 1000000) ≤ B2 true 2 X := by
  exact B2_1_2_positive_part0 ha hb

end MetricKMedian.Certificates


end
end

end OAI
end

theorem solution : type_of% @OAI.MetricKMedian.Certificates.B2_1_2_positive_s35_oai := @OAI.MetricKMedian.Certificates.B2_1_2_positive_s35_oai
