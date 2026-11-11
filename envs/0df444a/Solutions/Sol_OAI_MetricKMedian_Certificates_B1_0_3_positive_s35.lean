-- Prove2me | solution 1 for OAI.MetricKMedian.Certificates.B1_0_3_positive_s35
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T15:10:03.243869+00:00
-- url     : https://prove2.me/submissions/43d3ed94-cb50-4770-b7b0-94267840f067

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

private theorem B1_0_3_positive_part0 {X : ℝ} (ha : 0 ≤ X) (hb : X ≤ (3 / 200)) :
    (1 / 1000000) ≤ B1 false 3 X := by
  have hu : 0 ≤ X - 0 := sub_nonneg.mpr ha
  have hv : 0 ≤ (3 / 200) - X := sub_nonneg.mpr hb
  have hcert : 0 ≤ B1 false 3 X - (1 / 1000000) := by
    calc
      0 ≤ (211846836504756224000000 / 177147) * (X - 0) ^ 0 * ((3 / 200) - X) ^ 11 +
      (2154482351753617899520000 / 177147) * (X - 0) ^ 1 * ((3 / 200) - X) ^ 10 +
      (9885116102227266855280640 / 177147) * (X - 0) ^ 2 * ((3 / 200) - X) ^ 9 +
      (44948393855974155724046848 / 295245) * (X - 0) ^ 3 * ((3 / 200) - X) ^ 8 +
      (2021522364399486357257860352 / 7381125) * (X - 0) ^ 4 * ((3 / 200) - X) ^ 7 +
      (62775455855443143538663319032 / 184528125) * (X - 0) ^ 5 * ((3 / 200) - X) ^ 6 +
      (1368152940802400859998935276084 / 4613203125) * (X - 0) ^ 6 * ((3 / 200) - X) ^ 5 +
      (83223529998122541128693718896369 / 461320312500) * (X - 0) ^ 7 * ((3 / 200) - X) ^ 4 +
      (3429691223626222916436352173714631 / 46132031250000) * (X - 0) ^ 8 * ((3 / 200) - X) ^ 3 +
      (8411863931264936630870133110213879 / 432487792968750) * (X - 0) ^ 9 * ((3 / 200) - X) ^ 2 +
      (3894967908020400132938442024992776073 / 1383960937500000000) * (X - 0) ^ 10 * ((3 / 200) - X) ^ 1 +
      (21759007808197597712823827886364814257 / 138396093750000000000) * (X - 0) ^ 11 * ((3 / 200) - X) ^ 0 := by positivity
      _ = B1 false 3 X - (1 / 1000000) := by
        dsimp only [p, v, k, h, pSeries, aSeries, bit, d, H, c, N, l, hh, uZero, uOne, Tk, T1, T2, Q0, Q1, Y, Yprime, B0, B1, B2, discr, total]
        norm_num
        ring
  linarith only [hcert]

theorem B1_0_3_positive_s35_oai {X : ℝ} (ha : 0 ≤ X) (hb : X ≤ (3 / 200)) :
    (1 / 1000000) ≤ B1 false 3 X := by
  exact B1_0_3_positive_part0 ha hb


end MetricKMedian.Certificates
end
end

end OAI
end

theorem solution : type_of% @OAI.MetricKMedian.Certificates.B1_0_3_positive_s35_oai := @OAI.MetricKMedian.Certificates.B1_0_3_positive_s35_oai
