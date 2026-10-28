-- Prove2me | solution 1 for OAI.MetricKMedian.Certificates.k_envelope_s35
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T10:52:18.24519+00:00
-- url     : https://prove2.me/submissions/08dc90db-14c8-4895-b7fd-0c9791d4cd63

import Mathlib
import Definitions.Def_OAIQ035K000
import Definitions.Def_OAIQ035K002
import Definitions.Def_OAIQ035K003
import Theorems.Thm_OAI_MetricKMedian_Analytic_P_le_half_s35
import Theorems.Thm_OAI_MetricKMedian_Certificates_p_approximation_s35

section
-- module Solutions.OAIQ035_KM.KMedian_Analysis_PolynomialBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.Certificates

private theorem k_lower_part0 {X : ℝ} (ha : 0 ≤ X) (hb : X ≤ 1) :
    (767 / 10000) ≤ k X := by
  have hu : 0 ≤ X - 0 := sub_nonneg.mpr ha
  have hv : 0 ≤ 1 - X := sub_nonneg.mpr hb
  have hcert : 0 ≤ k X - (767 / 10000) := by
    calc
      0 ≤ (141 / 2500) * (X - 0) ^ 1 * (1 - X) ^ 2 +
      (127 / 1000) * (X - 0) ^ 2 * (1 - X) ^ 1 +
      (119 / 1250) * (X - 0) ^ 3 * (1 - X) ^ 0 := by positivity
      _ = k X - (767 / 10000) := by
        dsimp only [p, v, k, h]
        norm_num
        ring
  linarith only [hcert]

theorem k_lower {X : ℝ} (ha : 0 ≤ X) (hb : X ≤ 1) :
    (767 / 10000) ≤ k X := by
  exact k_lower_part0 ha hb

private theorem k_upper_part0 {X : ℝ} (ha : 0 ≤ X) (hb : X ≤ 1) :
    0 ≤ 1719/10000-k X := by
  have hu : 0 ≤ X - 0 := sub_nonneg.mpr ha
  have hv : 0 ≤ 1 - X := sub_nonneg.mpr hb
  have hcert : 0 ≤ 1719/10000-k X - 0 := by
    calc
      0 ≤ (119 / 1250) * (X - 0) ^ 0 * (1 - X) ^ 3 +
      (573 / 2500) * (X - 0) ^ 1 * (1 - X) ^ 2 +
      (793 / 5000) * (X - 0) ^ 2 * (1 - X) ^ 1 := by positivity
      _ = 1719/10000-k X - 0 := by
        dsimp only [p, v, k, h]
        norm_num
        ring
  linarith only [hcert]

theorem k_upper {X : ℝ} (ha : 0 ≤ X) (hb : X ≤ 1) :
    0 ≤ 1719/10000-k X := by
  exact k_upper_part0 ha hb


end MetricKMedian.Certificates
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Analysis_ScalarCertificates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.Certificates
private theorem Tk_lower_part0 {X : ℝ} (ha : 0 ≤ X) (hb : X ≤ (1 / 2)) :
    (1 / 10000) ≤ Tk X := by
  have hu : 0 ≤ X - 0 := sub_nonneg.mpr ha
  have hv : 0 ≤ (1 / 2) - X := sub_nonneg.mpr hb
  have hcert : 0 ≤ Tk X - (1 / 10000) := by
    calc
      0 ≤ (1805480639441 / 4882812500000) * (X - 0) ^ 0 * ((1 / 2) - X) ^ 10 +
      (73114107677191 / 9765625000000) * (X - 0) ^ 1 * ((1 / 2) - X) ^ 9 +
      (1599146421551509 / 39062500000000) * (X - 0) ^ 2 * ((1 / 2) - X) ^ 8 +
      (342377561078167 / 3125000000000) * (X - 0) ^ 3 * ((1 / 2) - X) ^ 7 +
      (3334559213722287 / 19531250000000) * (X - 0) ^ 4 * ((1 / 2) - X) ^ 6 +
      (2590855721686419 / 15625000000000) * (X - 0) ^ 5 * ((1 / 2) - X) ^ 5 +
      (160573393740407 / 1562500000000) * (X - 0) ^ 6 * ((1 / 2) - X) ^ 4 +
      (12776957693747113 / 312500000000000) * (X - 0) ^ 7 * ((1 / 2) - X) ^ 3 +
      (6662818596154343 / 625000000000000) * (X - 0) ^ 8 * ((1 / 2) - X) ^ 2 +
      (2409954861851027 / 1250000000000000) * (X - 0) ^ 9 * ((1 / 2) - X) ^ 1 +
      (132419867113743 / 625000000000000) * (X - 0) ^ 10 * ((1 / 2) - X) ^ 0 := by positivity
      _ = Tk X - (1 / 10000) := by
        dsimp only [p, v, k, h, pSeries, aSeries, bit, d, H, c, N, l, hh, uZero, uOne, Tk, T1, T2, Q0, Q1, Y, Yprime, B0, B1, B2, discr, total]
        norm_num
        ring
  linarith only [hcert]

private theorem Tk_lower_part1 {X : ℝ} (ha : (1 / 2) ≤ X) (hb : X ≤ 1) :
    (1 / 10000) ≤ Tk X := by
  have hu : 0 ≤ X - (1 / 2) := sub_nonneg.mpr ha
  have hv : 0 ≤ 1 - X := sub_nonneg.mpr hb
  have hcert : 0 ≤ Tk X - (1 / 10000) := by
    calc
      0 ≤ (132419867113743 / 625000000000000) * (X - (1 / 2)) ^ 0 * (1 - X) ^ 10 +
      (2886839822698693 / 1250000000000000) * (X - (1 / 2)) ^ 1 * (1 - X) ^ 9 +
      (220220022999221 / 15625000000000) * (X - (1 / 2)) ^ 2 * (1 - X) ^ 8 +
      (17328752263447299 / 312500000000000) * (X - (1 / 2)) ^ 3 * (1 - X) ^ 7 +
      (4394807238038073 / 31250000000000) * (X - (1 / 2)) ^ 4 * (1 - X) ^ 6 +
      (9008200454594741 / 39062500000000) * (X - (1 / 2)) ^ 5 * (1 - X) ^ 5 +
      (2384993556966093 / 9765625000000) * (X - (1 / 2)) ^ 6 * (1 - X) ^ 4 +
      (12761061088549709 / 78125000000000) * (X - (1 / 2)) ^ 7 * (1 - X) ^ 3 +
      (632232603598239 / 9765625000000) * (X - (1 / 2)) ^ 8 * (1 - X) ^ 2 +
      (50879711583183 / 3906250000000) * (X - (1 / 2)) ^ 9 * (1 - X) ^ 1 +
      (32595795117 / 39062500000) * (X - (1 / 2)) ^ 10 * (1 - X) ^ 0 := by positivity
      _ = Tk X - (1 / 10000) := by
        dsimp only [p, v, k, h, pSeries, aSeries, bit, d, H, c, N, l, hh, uZero, uOne, Tk, T1, T2, Q0, Q1, Y, Yprime, B0, B1, B2, discr, total]
        norm_num
        ring
  linarith only [hcert]

theorem Tk_lower {X : ℝ} (ha : 0 ≤ X) (hb : X ≤ 1) :
    (1 / 10000) ≤ Tk X := by
  by_cases ht0 : X ≤ (1 / 2)
  · exact Tk_lower_part0 ha ht0
  · have hl0 : (1 / 2) ≤ X := (lt_of_not_ge ht0).le
    exact Tk_lower_part1 hl0 hb


end MetricKMedian.Certificates
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Analysis_AnalyticEnvelopes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.Certificates

open Analytic

theorem k_envelope_s35_oai {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    FiniteComparison.kZero (P x) ≤ k (1 - x) := by
  have hX0 : 0 ≤ 1 - x := sub_nonneg.mpr hx1
  have hX1 : 1 - x ≤ 1 := by linarith
  have hk0 := k_lower hX0 hX1
  have hk1 := k_upper hX0 hX1
  have ht := Tk_lower hX0 hX1
  have hp := (abs_le.mp (p_approximation_s35 hx0 hx1)).1
  have hP := P_le_half_s35 hx0
  have hs0 := Real.sqrt_nonneg (1 - P x)
  have hs : (Real.sqrt (1 - P x)) ^ 2 = 1 - P x := Real.sq_sqrt (by linarith)
  have hmul := mul_le_mul_of_nonneg_right (show P x ≤ p (1-x) + 3/400000 by linarith)
    (sq_nonneg (1 + k (1-x)))
  dsimp only [Tk] at ht
  have hsq : (1 - k (1-x)) ^ 2 ≤ (Real.sqrt (1-P x) * (1+k (1-x))) ^ 2 := by
    rw [mul_pow, hs]
    nlinarith only [ht, hmul]
  have hlin : 1-k (1-x) ≤ Real.sqrt (1-P x) * (1+k (1-x)) := by
    have hright : 0 ≤ Real.sqrt (1-P x) * (1+k (1-x)) := mul_nonneg hs0 (by linarith)
    nlinarith only [hsq, hright]
  unfold FiniteComparison.kZero
  apply (div_le_iff₀ (by linarith : 0 < 1 + Real.sqrt (1 - P x))).mpr
  nlinarith only [hlin]

end MetricKMedian.Certificates


end
end

end OAI
end

theorem solution : type_of% @OAI.MetricKMedian.Certificates.k_envelope_s35_oai := @OAI.MetricKMedian.Certificates.k_envelope_s35_oai
