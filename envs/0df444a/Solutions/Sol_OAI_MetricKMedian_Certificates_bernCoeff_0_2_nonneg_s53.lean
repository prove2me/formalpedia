-- Prove2me | solution 1 for OAI.MetricKMedian.Certificates.bernCoeff_0_2_nonneg_s53
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T06:57:39.143293+00:00
-- url     : https://prove2.me/submissions/137c26fa-e4df-4d40-a50a-e62b271338d4

import Mathlib
import Definitions.Def_OAIQ053K002
import Theorems.Thm_OAI_MetricKMedian_Certificates_discr_0_2_positive_s53

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

private theorem B0_0_2_nonneg_part0 {X : ℝ} (ha : 0 ≤ X) (hb : X ≤ 1) :
    0 ≤ B0 false 2 X := by
  have hu : 0 ≤ X - 0 := sub_nonneg.mpr ha
  have hv : 0 ≤ 1 - X := sub_nonneg.mpr hb
  have hcert : 0 ≤ B0 false 2 X - 0 := by
    calc
      0 ≤ (81176144847679 / 292968750000000) * (X - 0) ^ 2 * (1 - X) ^ 8 +
      (5410742569474619 / 2343750000000000) * (X - 0) ^ 3 * (1 - X) ^ 7 +
      (78678547941402737 / 9375000000000000) * (X - 0) ^ 4 * (1 - X) ^ 6 +
      (21709775445807621 / 1250000000000000) * (X - 0) ^ 5 * (1 - X) ^ 5 +
      (419044445395628309 / 18750000000000000) * (X - 0) ^ 6 * (1 - X) ^ 4 +
      (114231033095199423 / 6250000000000000) * (X - 0) ^ 7 * (1 - X) ^ 3 +
      (11562688881639179 / 1250000000000000) * (X - 0) ^ 8 * (1 - X) ^ 2 +
      (3955668646057 / 1500000000000) * (X - 0) ^ 9 * (1 - X) ^ 1 +
      (48271 / 150000) * (X - 0) ^ 10 * (1 - X) ^ 0 := by positivity
      _ = B0 false 2 X - 0 := by
        dsimp only [p, v, k, h, pSeries, aSeries, bit, d, H, c, N, l, hh, uZero, uOne, Tk, T1, T2, Q0, Q1, Y, Yprime, B0, B1, B2, discr, total]
        norm_num
        ring
  linarith only [hcert]

theorem B0_0_2_nonneg {X : ℝ} (ha : 0 ≤ X) (hb : X ≤ 1) :
    0 ≤ B0 false 2 X := by
  exact B0_0_2_nonneg_part0 ha hb

private theorem B1_0_2_positive_part0 {X : ℝ} (ha : 0 ≤ X) (hb : X ≤ (1 / 20)) :
    (1 / 1000000) ≤ B1 false 2 X := by
  have hu : 0 ≤ X - 0 := sub_nonneg.mpr ha
  have hv : 0 ≤ (1 / 20) - X := sub_nonneg.mpr hb
  have hcert : 0 ≤ B1 false 2 X - (1 / 1000000) := by
    calc
      0 ≤ (1655053410193408 / 15625) * (X - 0) ^ 0 * ((1 / 20) - X) ^ 10 +
      (238626779321582144 / 234375) * (X - 0) ^ 1 * ((1 / 20) - X) ^ 9 +
      (25615526959024495244 / 5859375) * (X - 0) ^ 2 * ((1 / 20) - X) ^ 8 +
      (646383259421361945673 / 58593750) * (X - 0) ^ 3 * ((1 / 20) - X) ^ 7 +
      (21202864096402081690847 / 1171875000) * (X - 0) ^ 4 * ((1 / 20) - X) ^ 6 +
      (471515123802477892699547 / 23437500000) * (X - 0) ^ 5 * ((1 / 20) - X) ^ 5 +
      (2393933791873686584466291 / 156250000000) * (X - 0) ^ 6 * ((1 / 20) - X) ^ 4 +
      (921558750586559468182319 / 117187500000) * (X - 0) ^ 7 * ((1 / 20) - X) ^ 3 +
      (80943342490843441724933173 / 31250000000000) * (X - 0) ^ 8 * ((1 / 20) - X) ^ 2 +
      (38311823789498298388856321 / 78125000000000) * (X - 0) ^ 9 * ((1 / 20) - X) ^ 1 +
      (124914297163596574884497853 / 3125000000000000) * (X - 0) ^ 10 * ((1 / 20) - X) ^ 0 := by positivity
      _ = B1 false 2 X - (1 / 1000000) := by
        dsimp only [p, v, k, h, pSeries, aSeries, bit, d, H, c, N, l, hh, uZero, uOne, Tk, T1, T2, Q0, Q1, Y, Yprime, B0, B1, B2, discr, total]
        norm_num
        ring
  linarith only [hcert]

theorem B1_0_2_positive {X : ℝ} (ha : 0 ≤ X) (hb : X ≤ (1 / 20)) :
    (1 / 1000000) ≤ B1 false 2 X := by
  exact B1_0_2_positive_part0 ha hb

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

theorem B2_0_2_positive {X : ℝ} (ha : 0 ≤ X) (hb : X ≤ (1 / 20)) :
    (1 / 1000000) ≤ B2 false 2 X := by
  exact B2_0_2_positive_part0 ha hb


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

theorem bernCoeff_0_2_nonneg_s53_oai {X r : ℝ} (hX0 : 0 ≤ X) (hX : X ≤ 1)
    (hr0 : 0 ≤ r) (_hr : r ≤ 1) : 0 ≤ bernCoeff false 2 X r := by
  have ha := B0_0_2_nonneg hX0 hX
  unfold bernCoeff
  by_cases hcut : X ≤ 1/20
  · have hb := B1_0_2_positive hX0 hcut
    have hc := B2_0_2_positive hX0 hcut
    exact add_nonneg (add_nonneg ha (mul_nonneg (by linarith) hr0))
      (mul_nonneg (by linarith) (sq_nonneg r))
  · have hd := discr_0_2_positive_s53 (le_of_not_ge hcut) hX
    exact quadratic_of_discriminant ha (by dsimp only [discr] at hd; linarith)

end MetricKMedian.Certificates


end
end

end OAI
end

theorem solution : type_of% @OAI.MetricKMedian.Certificates.bernCoeff_0_2_nonneg_s53_oai := @OAI.MetricKMedian.Certificates.bernCoeff_0_2_nonneg_s53_oai
