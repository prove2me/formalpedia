-- Prove2me | solution 1 for OAI.MetricKMedian.Certificates.Y_actual_bounds_s35
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T11:15:02.229791+00:00
-- url     : https://prove2.me/submissions/a9185932-738b-4b71-a35b-3e8210b568d7

import Mathlib
import Definitions.Def_OAIQ035K044
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

private theorem Yh0_lower_part0 {X : ℝ} (ha : (1 / 2) ≤ X) (hb : X ≤ 1) :
    (1 / 4000) ≤ Y false X-h X := by
  have hu : 0 ≤ X - (1 / 2) := sub_nonneg.mpr ha
  have hv : 0 ≤ 1 - X := sub_nonneg.mpr hb
  have hcert : 0 ≤ Y false X-h X - (1 / 4000) := by
    calc
      0 ≤ (25276579 / 100000000) * (X - (1 / 2)) ^ 0 * (1 - X) ^ 5 +
      (93121463 / 8000000) * (X - (1 / 2)) ^ 1 * (1 - X) ^ 4 +
      (9818867161 / 200000000) * (X - (1 / 2)) ^ 2 * (1 - X) ^ 3 +
      (802390057 / 10000000) * (X - (1 / 2)) ^ 3 * (1 - X) ^ 2 +
      (117132303 / 2000000) * (X - (1 / 2)) ^ 4 * (1 - X) ^ 1 +
      (10027 / 625) * (X - (1 / 2)) ^ 5 * (1 - X) ^ 0 := by positivity
      _ = Y false X-h X - (1 / 4000) := by
        dsimp only [p, v, k, h, pSeries, aSeries, bit, d, H, c, N, l, hh, uZero, uOne, Tk, T1, T2, Q0, Q1, Y, Yprime, B0, B1, B2, discr, total]
        norm_num
        ring
  linarith only [hcert]

theorem Yh0_lower {X : ℝ} (ha : (1 / 2) ≤ X) (hb : X ≤ 1) :
    (1 / 4000) ≤ Y false X-h X := by
  exact Yh0_lower_part0 ha hb

private theorem Yquarter0_lower_part0 {X : ℝ} (ha : (1 / 2) ≤ X) (hb : X ≤ 1) :
    (1 / 4000) ≤ Y false X-1/4 := by
  have hu : 0 ≤ X - (1 / 2) := sub_nonneg.mpr ha
  have hv : 0 ≤ 1 - X := sub_nonneg.mpr hb
  have hcert : 0 ≤ Y false X-1/4 - (1 / 4000) := by
    calc
      0 ≤ (166076579 / 100000000) * (X - (1 / 2)) ^ 0 * (1 - X) ^ 5 +
      (99521463 / 8000000) * (X - (1 / 2)) ^ 1 * (1 - X) ^ 4 +
      (7066867161 / 200000000) * (X - (1 / 2)) ^ 2 * (1 - X) ^ 3 +
      (483990057 / 10000000) * (X - (1 / 2)) ^ 3 * (1 - X) ^ 2 +
      (64652303 / 2000000) * (X - (1 / 2)) ^ 4 * (1 - X) ^ 1 +
      (5307 / 625) * (X - (1 / 2)) ^ 5 * (1 - X) ^ 0 := by positivity
      _ = Y false X-1/4 - (1 / 4000) := by
        dsimp only [p, v, k, h, pSeries, aSeries, bit, d, H, c, N, l, hh, uZero, uOne, Tk, T1, T2, Q0, Q1, Y, Yprime, B0, B1, B2, discr, total]
        norm_num
        ring
  linarith only [hcert]

theorem Yquarter0_lower {X : ℝ} (ha : (1 / 2) ≤ X) (hb : X ≤ 1) :
    (1 / 4000) ≤ Y false X-1/4 := by
  exact Yquarter0_lower_part0 ha hb

private theorem Yh1_lower_part0 {X : ℝ} (ha : 0 ≤ X) (hb : X ≤ 1) :
    (1 / 4000) ≤ Y true X-h X := by
  have hu : 0 ≤ X - 0 := sub_nonneg.mpr ha
  have hv : 0 ≤ 1 - X := sub_nonneg.mpr hb
  have hcert : 0 ≤ Y true X-h X - (1 / 4000) := by
    calc
      0 ≤ (7196017 / 200000000) * (X - 0) ^ 0 * (1 - X) ^ 5 +
      (156780239 / 1600000000) * (X - 0) ^ 1 * (1 - X) ^ 4 +
      (312742177 / 640000000) * (X - 0) ^ 2 * (1 - X) ^ 3 +
      (1963273751 / 1600000000) * (X - 0) ^ 3 * (1 - X) ^ 2 +
      (770208811 / 640000000) * (X - 0) ^ 4 * (1 - X) ^ 1 +
      (3261 / 8000) * (X - 0) ^ 5 * (1 - X) ^ 0 := by positivity
      _ = Y true X-h X - (1 / 4000) := by
        dsimp only [p, v, k, h, pSeries, aSeries, bit, d, H, c, N, l, hh, uZero, uOne, Tk, T1, T2, Q0, Q1, Y, Yprime, B0, B1, B2, discr, total]
        norm_num
        ring
  linarith only [hcert]

theorem Yh1_lower {X : ℝ} (ha : 0 ≤ X) (hb : X ≤ 1) :
    (1 / 4000) ≤ Y true X-h X := by
  exact Yh1_lower_part0 ha hb

private theorem Yquarter1_lower_part0 {X : ℝ} (ha : 0 ≤ X) (hb : X ≤ 1) :
    (1 / 4000) ≤ Y true X-1/4 := by
  have hu : 0 ≤ X - 0 := sub_nonneg.mpr ha
  have hv : 0 ≤ 1 - X := sub_nonneg.mpr hb
  have hcert : 0 ≤ Y true X-1/4 - (1 / 4000) := by
    calc
      0 ≤ (35996017 / 200000000) * (X - 0) ^ 0 * (1 - X) ^ 5 +
      (1308780239 / 1600000000) * (X - 0) ^ 1 * (1 - X) ^ 4 +
      (965542177 / 640000000) * (X - 0) ^ 2 * (1 - X) ^ 3 +
      (2315273751 / 1600000000) * (X - 0) ^ 3 * (1 - X) ^ 2 +
      (475808811 / 640000000) * (X - 0) ^ 4 * (1 - X) ^ 1 +
      (1373 / 8000) * (X - 0) ^ 5 * (1 - X) ^ 0 := by positivity
      _ = Y true X-1/4 - (1 / 4000) := by
        dsimp only [p, v, k, h, pSeries, aSeries, bit, d, H, c, N, l, hh, uZero, uOne, Tk, T1, T2, Q0, Q1, Y, Yprime, B0, B1, B2, discr, total]
        norm_num
        ring
  linarith only [hcert]

theorem Yquarter1_lower {X : ℝ} (ha : 0 ≤ X) (hb : X ≤ 1) :
    (1 / 4000) ≤ Y true X-1/4 := by
  exact Yquarter1_lower_part0 ha hb


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

theorem Y_error {p q k x e : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1)
    (hpq : |p-q| ≤ e) (s : Bool) : |Y p k x s-Y q k x s| ≤ 3*e := by
  have hz : |-bit s-((2-bit s)*x+(2-bit s)^2/(32/5))| ≤ 3 := by
    rw [abs_le]
    constructor <;> cases s <;> norm_num [bit] <;> linarith
  have hid : Y p k x s-Y q k x s =
      (p-q)*(-bit s-((2-bit s)*x+(2-bit s)^2/(32/5))) := by
    unfold Y N c
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

private theorem Y_compat (s : Bool) (X : ℝ) :
    ScalarTransfer.Y (p X) (k X) (1-X) s = Y s X := rfl

private theorem Y_error_actual {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1) (s : Bool) :
    |Y s (1-x)-ScalarTransfer.Y (P x) (k (1-x)) x s| ≤ 3*(3/400000) := by
  have he := ScalarTransfer.Y_error (k := k (1-x)) hx0 hx (p_approximation_s35 hx0 hx) s
  have hid : ScalarTransfer.Y (p (1-x)) (k (1-x)) x s = Y s (1-x) := by
    simpa only [sub_sub_cancel] using Y_compat s (1-x)
  rwa [hid] at he

theorem Y_actual_bounds_s35_oai {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1) (s : Bool)
    (hside : s = true ∨ 1-x ≥ 1/2) :
    h (1-x) ≤ ScalarTransfer.Y (P x) (k (1-x)) x s ∧
      1/4 ≤ ScalarTransfer.Y (P x) (k (1-x)) x s := by
  have he := (abs_le.mp (Y_error_actual hx0 hx s)).2
  have hX0 := sub_nonneg.mpr hx
  have hX : 1-x ≤ 1 := by linarith
  cases s
  · have hrange : 1/2 ≤ 1-x := by simpa using hside
    have hc := Yh0_lower hrange hX
    have hc' := Yquarter0_lower hrange hX
    constructor <;> linarith
  · have hc := Yh1_lower hX0 hX
    have hc' := Yquarter1_lower hX0 hX
    constructor <;> linarith

end MetricKMedian.Certificates


end
end

end OAI
end

theorem solution : type_of% @OAI.MetricKMedian.Certificates.Y_actual_bounds_s35_oai := @OAI.MetricKMedian.Certificates.Y_actual_bounds_s35_oai
