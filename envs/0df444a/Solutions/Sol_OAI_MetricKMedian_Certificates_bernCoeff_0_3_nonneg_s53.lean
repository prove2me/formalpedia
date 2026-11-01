-- Prove2me | solution 1 for OAI.MetricKMedian.Certificates.bernCoeff_0_3_nonneg_s53
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T06:57:40.09422+00:00
-- url     : https://prove2.me/submissions/3cd918f2-dc18-4621-a901-6c7e65dbf0dc

import Mathlib
import Definitions.Def_OAIQ053K002
import Theorems.Thm_OAI_MetricKMedian_Certificates_discr_0_3_positive_s53

section
-- module Solutions.OAIQ053_KM.KMedian_Analysis_BernsteinFalse
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.Certificates

private theorem B0_0_3_nonneg_part0 {X : ℝ} (ha : 0 ≤ X) (hb : X ≤ 1) :
    0 ≤ B0 false 3 X := by
  have hu : 0 ≤ X - 0 := sub_nonneg.mpr ha
  have hv : 0 ≤ 1 - X := sub_nonneg.mpr hb
  have hcert : 0 ≤ B0 false 3 X - 0 := by
    calc
      0 ≤ (81176144847679 / 97656250000000) * (X - 0) ^ 2 * (1 - X) ^ 9 +
      (6234710152003187 / 781250000000000) * (X - 0) ^ 3 * (1 - X) ^ 8 +
      (106755787483068701 / 3125000000000000) * (X - 0) ^ 4 * (1 - X) ^ 7 +
      (535105795837571509 / 6250000000000000) * (X - 0) ^ 5 * (1 - X) ^ 6 +
      (108221819738623917 / 781250000000000) * (X - 0) ^ 6 * (1 - X) ^ 5 +
      (46923443113549031 / 312500000000000) * (X - 0) ^ 7 * (1 - X) ^ 4 +
      (341064070909420707 / 3125000000000000) * (X - 0) ^ 8 * (1 - X) ^ 3 +
      (64187676200066127 / 1250000000000000) * (X - 0) ^ 9 * (1 - X) ^ 2 +
      (7105170406057 / 500000000000) * (X - 0) ^ 10 * (1 - X) ^ 1 +
      (88271 / 50000) * (X - 0) ^ 11 * (1 - X) ^ 0 := by positivity
      _ = B0 false 3 X - 0 := by
        dsimp only [p, v, k, h, pSeries, aSeries, bit, d, H, c, N, l, hh, uZero, uOne, Tk, T1, T2, Q0, Q1, Y, Yprime, B0, B1, B2, discr, total]
        norm_num
        ring
  linarith only [hcert]

theorem B0_0_3_nonneg {X : ℝ} (ha : 0 ≤ X) (hb : X ≤ 1) :
    0 ≤ B0 false 3 X := by
  exact B0_0_3_nonneg_part0 ha hb

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

theorem B1_0_3_positive {X : ℝ} (ha : 0 ≤ X) (hb : X ≤ (3 / 200)) :
    (1 / 1000000) ≤ B1 false 3 X := by
  exact B1_0_3_positive_part0 ha hb

private theorem B2_0_3_positive_part0 {X : ℝ} (ha : 0 ≤ X) (hb : X ≤ (3 / 200)) :
    (1 / 1000000) ≤ B2 false 3 X := by
  have hu : 0 ≤ X - 0 := sub_nonneg.mpr ha
  have hv : 0 ≤ (3 / 200) - X := sub_nonneg.mpr hb
  have hcert : 0 ≤ B2 false 3 X - (1 / 1000000) := by
    calc
      0 ≤ (48015873681706188800 / 19683) * (X - 0) ^ 0 * ((3 / 200) - X) ^ 9 +
      (145202067927278313472 / 6561) * (X - 0) ^ 1 * ((3 / 200) - X) ^ 8 +
      (14636537738370529063808 / 164025) * (X - 0) ^ 2 * ((3 / 200) - X) ^ 7 +
      (286878563124849123327976 / 1366875) * (X - 0) ^ 3 * ((3 / 200) - X) ^ 6 +
      (32532187927172237213074301 / 102515625) * (X - 0) ^ 4 * ((3 / 200) - X) ^ 5 +
      (6558494891089719261149911907 / 20503125000) * (X - 0) ^ 5 * ((3 / 200) - X) ^ 4 +
      (881458596444504296454383930761 / 4100625000000) * (X - 0) ^ 6 * ((3 / 200) - X) ^ 3 +
      (38078692680648783899065817036731 / 410062500000000) * (X - 0) ^ 7 * ((3 / 200) - X) ^ 2 +
      (959570002324248521125178610414701 / 41006250000000000) * (X - 0) ^ 8 * ((3 / 200) - X) ^ 1 +
      (32240932159727937682542517623759527 / 12301875000000000000) * (X - 0) ^ 9 * ((3 / 200) - X) ^ 0 := by positivity
      _ = B2 false 3 X - (1 / 1000000) := by
        dsimp only [p, v, k, h, pSeries, aSeries, bit, d, H, c, N, l, hh, uZero, uOne, Tk, T1, T2, Q0, Q1, Y, Yprime, B0, B1, B2, discr, total]
        norm_num
        ring
  linarith only [hcert]

theorem B2_0_3_positive {X : ℝ} (ha : 0 ≤ X) (hb : X ≤ (3 / 200)) :
    (1 / 1000000) ≤ B2 false 3 X := by
  exact B2_0_3_positive_part0 ha hb


end MetricKMedian.Certificates
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Analysis_QuadraticEnvelopes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.Certificates

private theorem quadratic_of_discriminant {a b c r : ℝ} (ha : 0 ≤ a)
    (hd : 0 < 4*a*c-b^2) : 0 ≤ a+b*r+c*r^2 := by
  have hc : 0 < c := by
    by_contra hn
    have hp := mul_nonpos_of_nonneg_of_nonpos ha (le_of_not_gt hn)
    nlinarith only [hp, hd, sq_nonneg b]
  have hs := sq_nonneg (2*c*r+b)
  have hid : (2*c*r+b)^2+(4*a*c-b^2) = 4*c*(a+b*r+c*r^2) := by ring
  have hprod : 0 < c*(a+b*r+c*r^2) := by nlinarith only [hs, hd, hid]
  exact (pos_of_mul_pos_right hprod hc.le).le

theorem bernCoeff_0_3_nonneg_s53_oai {X r : ℝ} (hX0 : 0 ≤ X) (hX : X ≤ 1)
    (hr0 : 0 ≤ r) (_hr : r ≤ 1) : 0 ≤ bernCoeff false 3 X r := by
  have ha := B0_0_3_nonneg hX0 hX
  unfold bernCoeff
  by_cases hcut : X ≤ 3/200
  · have hb := B1_0_3_positive hX0 hcut
    have hc := B2_0_3_positive hX0 hcut
    exact add_nonneg (add_nonneg ha (mul_nonneg (by linarith) hr0))
      (mul_nonneg (by linarith) (sq_nonneg r))
  · have hd := discr_0_3_positive_s53 (le_of_not_ge hcut) hX
    exact quadratic_of_discriminant ha (by dsimp only [discr] at hd; linarith)

end MetricKMedian.Certificates


end
end

end OAI
end

theorem solution : type_of% @OAI.MetricKMedian.Certificates.bernCoeff_0_3_nonneg_s53_oai := @OAI.MetricKMedian.Certificates.bernCoeff_0_3_nonneg_s53_oai
