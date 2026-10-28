-- Prove2me | solution 1 for OAI.MetricKMedian.Certificates.Yprime_actual_bounds_s35
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T10:50:48.187744+00:00
-- url     : https://prove2.me/submissions/6b7f7131-d76b-421e-a7dd-a5c20835b8f3

import Mathlib
import Definitions.Def_OAIQ035K000
import Definitions.Def_OAIQ035K002
import Definitions.Def_OAIQ035K011
import Theorems.Thm_OAI_MetricKMedian_Certificates_p_approximation_s35

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

private theorem Yph0_lower_part0 {X : ℝ} (ha : 0 ≤ X) (hb : X ≤ (1 / 8)) :
    (1 / 4000) ≤ Yprime X+(13/25)*k X-h X := by
  have hu : 0 ≤ X - 0 := sub_nonneg.mpr ha
  have hv : 0 ≤ (1 / 8) - X := sub_nonneg.mpr hb
  have hcert : 0 ≤ Yprime X+(13/25)*k X-h X - (1 / 4000) := by
    calc
      0 ≤ (4142260224 / 390625) * (X - 0) ^ 0 * ((1 / 8) - X) ^ 6 +
      (4079468032 / 78125) * (X - 0) ^ 1 * ((1 / 8) - X) ^ 5 +
      (205031442336 / 1953125) * (X - 0) ^ 2 * ((1 / 8) - X) ^ 4 +
      (214663557868 / 1953125) * (X - 0) ^ 3 * ((1 / 8) - X) ^ 3 +
      (123009872643 / 1953125) * (X - 0) ^ 4 * ((1 / 8) - X) ^ 2 +
      (145957888689 / 7812500) * (X - 0) ^ 5 * ((1 / 8) - X) ^ 1 +
      (70194064247 / 31250000) * (X - 0) ^ 6 * ((1 / 8) - X) ^ 0 := by positivity
      _ = Yprime X+(13/25)*k X-h X - (1 / 4000) := by
        dsimp only [p, v, k, h, pSeries, aSeries, bit, d, H, c, N, l, hh, uZero, uOne, Tk, T1, T2, Q0, Q1, Y, Yprime, B0, B1, B2, discr, total]
        norm_num
        ring
  linarith only [hcert]

private theorem Yph0_lower_part1 {X : ℝ} (ha : (1 / 8) ≤ X) (hb : X ≤ (1 / 4)) :
    (1 / 4000) ≤ Yprime X+(13/25)*k X-h X := by
  have hu : 0 ≤ X - (1 / 8) := sub_nonneg.mpr ha
  have hv : 0 ≤ (1 / 4) - X := sub_nonneg.mpr hb
  have hcert : 0 ≤ Yprime X+(13/25)*k X-h X - (1 / 4000) := by
    calc
      0 ≤ (70194064247 / 31250000) * (X - (1 / 8)) ^ 0 * ((1 / 4) - X) ^ 6 +
      (16156076013 / 1953125) * (X - (1 / 8)) ^ 1 * ((1 / 4) - X) ^ 5 +
      (85371567387 / 7812500) * (X - (1 / 8)) ^ 2 * ((1 / 4) - X) ^ 4 +
      (11777178856 / 1953125) * (X - (1 / 8)) ^ 3 * ((1 / 4) - X) ^ 3 +
      (608045697 / 390625) * (X - (1 / 8)) ^ 4 * ((1 / 4) - X) ^ 2 +
      (1663295888 / 1953125) * (X - (1 / 8)) ^ 5 * ((1 / 4) - X) ^ 1 +
      (826315684 / 1953125) * (X - (1 / 8)) ^ 6 * ((1 / 4) - X) ^ 0 := by positivity
      _ = Yprime X+(13/25)*k X-h X - (1 / 4000) := by
        dsimp only [p, v, k, h, pSeries, aSeries, bit, d, H, c, N, l, hh, uZero, uOne, Tk, T1, T2, Q0, Q1, Y, Yprime, B0, B1, B2, discr, total]
        norm_num
        ring
  linarith only [hcert]

private theorem Yph0_lower_part2 {X : ℝ} (ha : (1 / 4) ≤ X) (hb : X ≤ (1 / 2)) :
    (1 / 4000) ≤ Yprime X+(13/25)*k X-h X := by
  have hu : 0 ≤ X - (1 / 4) := sub_nonneg.mpr ha
  have hv : 0 ≤ (1 / 2) - X := sub_nonneg.mpr hb
  have hcert : 0 ≤ Yprime X+(13/25)*k X-h X - (1 / 4000) := by
    calc
      0 ≤ (206578921 / 31250000) * (X - (1 / 4)) ^ 0 * ((1 / 2) - X) ^ 6 +
      (1443386317 / 15625000) * (X - (1 / 4)) ^ 1 * ((1 / 2) - X) ^ 5 +
      (922683183 / 1562500) * (X - (1 / 4)) ^ 2 * ((1 / 2) - X) ^ 4 +
      (6204085811 / 3906250) * (X - (1 / 4)) ^ 3 * ((1 / 2) - X) ^ 3 +
      (4000195644 / 1953125) * (X - (1 / 4)) ^ 4 * ((1 / 2) - X) ^ 2 +
      (2483278992 / 1953125) * (X - (1 / 4)) ^ 5 * ((1 / 2) - X) ^ 1 +
      (599298656 / 1953125) * (X - (1 / 4)) ^ 6 * ((1 / 2) - X) ^ 0 := by positivity
      _ = Yprime X+(13/25)*k X-h X - (1 / 4000) := by
        dsimp only [p, v, k, h, pSeries, aSeries, bit, d, H, c, N, l, hh, uZero, uOne, Tk, T1, T2, Q0, Q1, Y, Yprime, B0, B1, B2, discr, total]
        norm_num
        ring
  linarith only [hcert]

theorem Yph0_lower {X : ℝ} (ha : 0 ≤ X) (hb : X ≤ (1 / 2)) :
    (1 / 4000) ≤ Yprime X+(13/25)*k X-h X := by
  by_cases ht0 : X ≤ (1 / 8)
  · exact Yph0_lower_part0 ha ht0
  · have hl0 : (1 / 8) ≤ X := (lt_of_not_ge ht0).le
    by_cases ht1 : X ≤ (1 / 4)
    · exact Yph0_lower_part1 hl0 ht1
    · have hl1 : (1 / 4) ≤ X := (lt_of_not_ge ht1).le
      exact Yph0_lower_part2 hl1 hb

private theorem Ypquarter0_lower_part0 {X : ℝ} (ha : 0 ≤ X) (hb : X ≤ (1 / 2)) :
    (1 / 4000) ≤ Yprime X-1/4 := by
  have hu : 0 ≤ X - 0 := sub_nonneg.mpr ha
  have hv : 0 ≤ (1 / 2) - X := sub_nonneg.mpr hb
  have hcert : 0 ≤ Yprime X-1/4 - (1 / 4000) := by
    calc
      0 ≤ (3614194 / 390625) * (X - 0) ^ 0 * ((1 / 2) - X) ^ 6 +
      (33933571 / 781250) * (X - 0) ^ 1 * ((1 / 2) - X) ^ 5 +
      (1298227673 / 15625000) * (X - 0) ^ 2 * ((1 / 2) - X) ^ 4 +
      (529319783 / 6250000) * (X - 0) ^ 3 * ((1 / 2) - X) ^ 3 +
      (401955531 / 7812500) * (X - 0) ^ 4 * ((1 / 2) - X) ^ 2 +
      (76385189 / 3906250) * (X - 0) ^ 5 * ((1 / 2) - X) ^ 1 +
      (15229833 / 3906250) * (X - 0) ^ 6 * ((1 / 2) - X) ^ 0 := by positivity
      _ = Yprime X-1/4 - (1 / 4000) := by
        dsimp only [p, v, k, h, pSeries, aSeries, bit, d, H, c, N, l, hh, uZero, uOne, Tk, T1, T2, Q0, Q1, Y, Yprime, B0, B1, B2, discr, total]
        norm_num
        ring
  linarith only [hcert]

theorem Ypquarter0_lower {X : ℝ} (ha : 0 ≤ X) (hb : X ≤ (1 / 2)) :
    (1 / 4000) ≤ Yprime X-1/4 := by
  exact Ypquarter0_lower_part0 ha hb


end MetricKMedian.Certificates
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Analysis_ScalarTransfer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.ScalarTransfer

theorem mul_abs_bound {a b e K : ℝ} (ha : |a| ≤ e) (hb : |b| ≤ K) :
    |a*b| ≤ e*K := by
  rw [abs_mul]
  exact mul_le_mul ha hb (abs_nonneg b) ((abs_nonneg a).trans ha)

theorem Yprime_error {p q k x e : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1)
    (hpq : |p-q| ≤ e) : |Yprime p k x-Yprime q k x| ≤ 2*e := by
  have hs : (1-x)^2 ≤ 1 := by nlinarith
  have hz : |(8/5)*(1-x)^2-2| ≤ 2 := by
    rw [abs_le]; constructor <;> nlinarith [sq_nonneg (1-x)]
  have hid : Yprime p k x-Yprime q k x = (p-q)*((8/5)*(1-x)^2-2) := by
    unfold Yprime
    ring
  rw [hid]
  have h := mul_abs_bound hpq hz
  simpa only [mul_comm e] using h

end MetricKMedian.ScalarTransfer


end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Analysis_ComparisonCertificates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.Certificates

open Analytic

private theorem Yprime_compat (X : ℝ) :
    ScalarTransfer.Yprime (p X) (k X) (1-X) = Yprime X := by
  unfold ScalarTransfer.Yprime Yprime N c bit
  norm_num

private theorem Yprime_error_actual {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1) :
    |Yprime (1-x)-ScalarTransfer.Yprime (P x) (k (1-x)) x| ≤ 2*(3/400000) := by
  have he := ScalarTransfer.Yprime_error (k := k (1-x)) hx0 hx (p_approximation_s35 hx0 hx)
  have hid : ScalarTransfer.Yprime (p (1-x)) (k (1-x)) x = Yprime (1-x) := by
    simpa only [sub_sub_cancel] using Yprime_compat (1-x)
  rwa [hid] at he

theorem Yprime_actual_bounds_s35_oai {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1)
    (hside : 1-x ≤ 1/2) :
    h (1-x) ≤ ScalarTransfer.Yprime (P x) (k (1-x)) x+(13/25)*k (1-x) ∧
      1/4 ≤ ScalarTransfer.Yprime (P x) (k (1-x)) x := by
  have he := (abs_le.mp (Yprime_error_actual hx0 hx)).2
  have hX0 := sub_nonneg.mpr hx
  have hc := Yph0_lower hX0 hside
  have hc' := Ypquarter0_lower hX0 hside
  constructor <;> linarith

end MetricKMedian.Certificates


end
end

end OAI
end

theorem solution : type_of% @OAI.MetricKMedian.Certificates.Yprime_actual_bounds_s35_oai := @OAI.MetricKMedian.Certificates.Yprime_actual_bounds_s35_oai
