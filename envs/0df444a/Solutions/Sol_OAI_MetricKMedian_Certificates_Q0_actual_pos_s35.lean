-- Prove2me | solution 1 for OAI.MetricKMedian.Certificates.Q0_actual_pos_s35
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T11:14:17.262312+00:00
-- url     : https://prove2.me/submissions/bab0cc18-4205-4def-8993-98bce3fab011

import Mathlib
import Definitions.Def_OAIQ035K044
import Theorems.Thm_OAI_MetricKMedian_Certificates_a_approximation_s35
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

theorem Q0u0_lower {X : ℝ} (ha : (65 / 226) ≤ X) (hb : X ≤ 1) :
    (1 / 4000) ≤ Q0 false (uZero false) X := by
  exact Q0u0_lower_part0 ha hb

private theorem Q0X0_lower_part0 {X : ℝ} (ha : 0 ≤ X) (hb : X ≤ (65 / 226)) :
    (1 / 4000) ≤ Q0 false X X := by
  have hu : 0 ≤ X - 0 := sub_nonneg.mpr ha
  have hv : 0 ≤ (65 / 226) - X := sub_nonneg.mpr hb
  have hcert : 0 ≤ Q0 false X X - (1 / 4000) := by
    calc
      0 ≤ (26616949523729557926 / 736512603759765625) * (X - 0) ^ 0 * ((65 / 226) - X) ^ 6 +
      (1108505996305909349273 / 5892100830078125000) * (X - 0) ^ 1 * ((65 / 226) - X) ^ 5 +
      (1070555096566927387931 / 2356840332031250000) * (X - 0) ^ 2 * ((65 / 226) - X) ^ 4 +
      (196730605689159043317 / 294605041503906250) * (X - 0) ^ 3 * ((65 / 226) - X) ^ 3 +
      (728676237597742428583 / 1178420166015625000) * (X - 0) ^ 4 * ((65 / 226) - X) ^ 2 +
      (15391598916307421235999 / 47136806640625000000) * (X - 0) ^ 5 * ((65 / 226) - X) ^ 1 +
      (1737648435170760018037 / 23568403320312500000) * (X - 0) ^ 6 * ((65 / 226) - X) ^ 0 := by positivity
      _ = Q0 false X X - (1 / 4000) := by
        dsimp only [p, v, k, h, pSeries, aSeries, bit, d, H, c, N, l, hh, uZero, uOne, Tk, T1, T2, Q0, Q1, Y, Yprime, B0, B1, B2, discr, total]
        norm_num
        ring
  linarith only [hcert]

theorem Q0X0_lower {X : ℝ} (ha : 0 ≤ X) (hb : X ≤ (65 / 226)) :
    (1 / 4000) ≤ Q0 false X X := by
  exact Q0X0_lower_part0 ha hb

private theorem Q0u1_lower_part0 {X : ℝ} (ha : 0 ≤ X) (hb : X ≤ 1) :
    (1 / 4000) ≤ Q0 true (uZero true) X := by
  have hu : 0 ≤ X - 0 := sub_nonneg.mpr ha
  have hv : 0 ≤ 1 - X := sub_nonneg.mpr hb
  have hcert : 0 ≤ Q0 true (uZero true) X - (1 / 4000) := by
    calc
      0 ≤ (1073963 / 62500000) * (X - 0) ^ 0 * (1 - X) ^ 4 +
      (288567027 / 2750000000) * (X - 0) ^ 1 * (1 - X) ^ 3 +
      (293860011 / 1375000000) * (X - 0) ^ 2 * (1 - X) ^ 2 +
      (497217619 / 2750000000) * (X - 0) ^ 3 * (1 - X) ^ 1 +
      (2389 / 44000) * (X - 0) ^ 4 * (1 - X) ^ 0 := by positivity
      _ = Q0 true (uZero true) X - (1 / 4000) := by
        dsimp only [p, v, k, h, pSeries, aSeries, bit, d, H, c, N, l, hh, uZero, uOne, Tk, T1, T2, Q0, Q1, Y, Yprime, B0, B1, B2, discr, total]
        norm_num
        ring
  linarith only [hcert]

theorem Q0u1_lower {X : ℝ} (ha : 0 ≤ X) (hb : X ≤ 1) :
    (1 / 4000) ≤ Q0 true (uZero true) X := by
  exact Q0u1_lower_part0 ha hb


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

private theorem add_product_abs_bound {a b c d e K L : ℝ}
    (ha : |a| ≤ e) (hb : |b| ≤ K) (hc : |c| ≤ 2*e) (hd : |d| ≤ L) :
    |a*b+c*d| ≤ (K+2*L)*e := by
  calc
    |a*b+c*d| ≤ |a*b|+|c*d| := abs_add_le _ _
    _ ≤ e*K+(2*e)*L := add_le_add (mul_abs_bound ha hb) (mul_abs_bound hc hd)
    _ = (K+2*L)*e := by ring

theorem Q0_error {p q a b k W e : ℝ} (hW0 : 0 ≤ W) (hW : W ≤ 1)
    (hpq : |p-q| ≤ e) (hab : |a-b| ≤ 2*e) (s : Bool) :
    |Q0 p a k W s-Q0 q b k W s| ≤ 6*e := by
  have hWs : W^2 ≤ 1 := by nlinarith
  have hc : |-bit s+W*(hh s*W-2*d s)| ≤ 4 := by
    rw [abs_le]
    constructor <;> cases s <;> norm_num [bit, hh, d] <;> nlinarith [sq_nonneg W]
  have hd : |-d s| ≤ 1 := by cases s <;> norm_num [d]
  have hid : Q0 p a k W s-Q0 q b k W s =
      (p-q)*(-bit s+W*(hh s*W-2*d s))+(a-b)*(-d s) := by
    unfold Q0 N c
    ring
  rw [hid]
  calc
    _ ≤ (4+2*1)*e := add_product_abs_bound hpq hc hab hd
    _ = 6*e := by ring

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

private theorem Q0_compat (s : Bool) (W X : ℝ) :
    ScalarTransfer.Q0 (p X) (v X) (k X) W s = Q0 s W X := rfl

private theorem Q0_error_actual {x W : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1)
    (hW0 : 0 ≤ W) (hW : W ≤ 1) (s : Bool) :
    |Q0 s W (1-x)-ScalarTransfer.Q0 (P x) (A x) (k (1-x)) W s| ≤ 6*(3/400000) := by
  have he := ScalarTransfer.Q0_error (k := k (1-x)) hW0 hW (p_approximation_s35 hx0 hx)
    (show |v (1-x)-A x| ≤ 2*(3/400000) by convert a_approximation_s35 hx0 hx using 1; norm_num) s
  rwa [Q0_compat] at he

theorem Q0_actual_pos_s35_oai {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1) (s : Bool) :
    0 < ScalarTransfer.Q0 (P x) (A x) (k (1-x))
      (if s then ScalarTransfer.uZero s else min (1-x) (ScalarTransfer.uZero s)) s := by
  have hX0 := sub_nonneg.mpr hx
  have hX : 1-x ≤ 1 := by linarith
  cases s
  · by_cases hcut : 1-x ≤ 65/226
    · have he := (abs_le.mp (Q0_error_actual hx0 hx hX0 hX false)).2
      have hc := Q0X0_lower hX0 hcut
      norm_num [ScalarTransfer.uZero, ScalarTransfer.hh, ScalarTransfer.d, min_eq_left hcut]
      linarith
    · have hulo : (0:ℝ) ≤ 65/226 := by norm_num
      have huhi : (65/226:ℝ) ≤ 1 := by norm_num
      have he := (abs_le.mp (Q0_error_actual hx0 hx hulo huhi false)).2
      have hc := Q0u0_lower (le_of_not_ge hcut) hX
      norm_num [ScalarTransfer.uZero, ScalarTransfer.hh, ScalarTransfer.d,
        min_eq_right (le_of_not_ge hcut)]
      norm_num [uZero, hh, d] at hc
      linarith
  · have hulo : (0:ℝ) ≤ 5/22 := by norm_num
    have huhi : (5/22:ℝ) ≤ 1 := by norm_num
    have he := (abs_le.mp (Q0_error_actual hx0 hx hulo huhi true)).2
    have hc := Q0u1_lower hX0 hX
    norm_num [ScalarTransfer.uZero, ScalarTransfer.hh, ScalarTransfer.d]
    norm_num [uZero, hh, d] at hc
    linarith

end MetricKMedian.Certificates


end
end

end OAI
end

theorem solution : type_of% @OAI.MetricKMedian.Certificates.Q0_actual_pos_s35_oai := @OAI.MetricKMedian.Certificates.Q0_actual_pos_s35_oai
