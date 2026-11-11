-- Prove2me | solution 1 for OAI.MetricKMedian.Certificates.a_approx_upper_s35
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T15:10:13.14803+00:00
-- url     : https://prove2.me/submissions/f210a714-26dd-49ad-b356-bc8ef6e8f8d6

import Mathlib
import Definitions.Def_OAIQ035K002

section
-- module Solutions.Q224_RR.KMedian_Analysis_TaylorBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.Certificates

private theorem a_approx_upper_part0 {X : ℝ} (ha : 0 ≤ X) (hb : X ≤ (1 / 2)) :
    0 ≤ v X - aSeries X + 3/200000 - (1 / 2891116800) := by
  have hu : 0 ≤ X - 0 := sub_nonneg.mpr ha
  have hv : 0 ≤ (1 / 2) - X := sub_nonneg.mpr hb
  have hcert : 0 ≤ v X - aSeries X + 3/200000 - (1 / 2891116800) - 0 := by
    calc
      0 ≤ (75878321072 / 1235218359375) * (X - 0) ^ 0 * ((1 / 2) - X) ^ 12 +
      (119467751836 / 112292578125) * (X - 0) ^ 1 * ((1 / 2) - X) ^ 11 +
      (7793017451006 / 1235218359375) * (X - 0) ^ 2 * ((1 / 2) - X) ^ 10 +
      (3512657879923 / 176459765625) * (X - 0) ^ 3 * ((1 / 2) - X) ^ 9 +
      (32461184245933 / 823478906250) * (X - 0) ^ 4 * ((1 / 2) - X) ^ 8 +
      (44081397944401 / 823478906250) * (X - 0) ^ 5 * ((1 / 2) - X) ^ 7 +
      (387738185491 / 7319812500) * (X - 0) ^ 6 * ((1 / 2) - X) ^ 6 +
      (6272739823291 / 156853125000) * (X - 0) ^ 7 * ((1 / 2) - X) ^ 5 +
      (7394208348047 / 313706250000) * (X - 0) ^ 8 * ((1 / 2) - X) ^ 4 +
      (841056310571303 / 79053975000000) * (X - 0) ^ 9 * ((1 / 2) - X) ^ 3 +
      (540241863124181 / 158107950000000) * (X - 0) ^ 10 * ((1 / 2) - X) ^ 2 +
      (214663883258389 / 316215900000000) * (X - 0) ^ 11 * ((1 / 2) - X) ^ 1 +
      (863382562703 / 14054040000000) * (X - 0) ^ 12 * ((1 / 2) - X) ^ 0 := by positivity
      _ = v X - aSeries X + 3/200000 - (1 / 2891116800) - 0 := by
        dsimp only [p, v, pSeries, aSeries]
        norm_num
        ring
  linarith only [hcert]

private theorem a_approx_upper_part1 {X : ℝ} (ha : (1 / 2) ≤ X) (hb : X ≤ 1) :
    0 ≤ v X - aSeries X + 3/200000 - (1 / 2891116800) := by
  have hu : 0 ≤ X - (1 / 2) := sub_nonneg.mpr ha
  have hv : 0 ≤ 1 - X := sub_nonneg.mpr hb
  have hcert : 0 ≤ v X - aSeries X + 3/200000 - (1 / 2891116800) - 0 := by
    calc
      0 ≤ (863382562703 / 14054040000000) * (X - (1 / 2)) ^ 0 * (1 - X) ^ 12 +
      (251562700601231 / 316215900000000) * (X - (1 / 2)) ^ 1 * (1 - X) ^ 11 +
      (61932113209151 / 13175662500000) * (X - (1 / 2)) ^ 2 * (1 - X) ^ 10 +
      (29598548004973 / 1796681250000) * (X - (1 / 2)) ^ 3 * (1 - X) ^ 9 +
      (1125267533239 / 29944687500) * (X - (1 / 2)) ^ 4 * (1 - X) ^ 8 +
      (1446800821841 / 24953906250) * (X - (1 / 2)) ^ 5 * (1 - X) ^ 7 +
      (2289587644256 / 37430859375) * (X - (1 / 2)) ^ 6 * (1 - X) ^ 6 +
      (77976295408 / 1782421875) * (X - (1 / 2)) ^ 7 * (1 - X) ^ 5 +
      (36966892276 / 1782421875) * (X - (1 / 2)) ^ 8 * (1 - X) ^ 4 +
      (20738546828 / 3208359375) * (X - (1 / 2)) ^ 9 * (1 - X) ^ 3 +
      (8079313612 / 5347265625) * (X - (1 / 2)) ^ 10 * (1 - X) ^ 2 +
      (21225820472 / 58819921875) * (X - (1 / 2)) ^ 11 * (1 - X) ^ 1 +
      (86731504 / 1411678125) * (X - (1 / 2)) ^ 12 * (1 - X) ^ 0 := by positivity
      _ = v X - aSeries X + 3/200000 - (1 / 2891116800) - 0 := by
        dsimp only [p, v, pSeries, aSeries]
        norm_num
        ring
  linarith only [hcert]

theorem a_approx_upper_s35_oai {X : ℝ} (ha : 0 ≤ X) (hb : X ≤ 1) :
    0 ≤ v X - aSeries X + 3/200000 - (1 / 2891116800) := by
  by_cases ht0 : X ≤ (1 / 2)
  · exact a_approx_upper_part0 ha ht0
  · have hl0 : (1 / 2) ≤ X := (lt_of_not_ge ht0).le
    exact a_approx_upper_part1 hl0 hb


end MetricKMedian.Certificates
end
end

end OAI
end

theorem solution : type_of% @OAI.MetricKMedian.Certificates.a_approx_upper_s35_oai := @OAI.MetricKMedian.Certificates.a_approx_upper_s35_oai
