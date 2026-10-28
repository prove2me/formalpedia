-- Prove2me | solution 1 for OAI.MetricKMedian.Certificates.Q1_actual_pos_s35
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T11:14:39.679776+00:00
-- url     : https://prove2.me/submissions/6bb93593-6c01-4f65-8775-65797c0c3d2f

import Mathlib
import Definitions.Def_OAIQ035K044
import Theorems.Thm_OAI_MetricKMedian_Analytic_P_le_half_s35
import Theorems.Thm_OAI_MetricKMedian_Analytic_P_nonneg_s35
import Theorems.Thm_OAI_MetricKMedian_Certificates_a_approximation_s35
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
private theorem p_lower_part0 {X : ℝ} (ha : 0 ≤ X) (hb : X ≤ 1) :
    (1651507 / 6250000) ≤ p X := by
  have hu : 0 ≤ X - 0 := sub_nonneg.mpr ha
  have hv : 0 ≤ 1 - X := sub_nonneg.mpr hb
  have hcert : 0 ≤ p X - (1651507 / 6250000) := by
    calc
      0 ≤ (8026757 / 50000000) * (X - 0) ^ 1 * (1 - X) ^ 3 +
      (53912437 / 100000000) * (X - 0) ^ 2 * (1 - X) ^ 2 +
      (60978037 / 100000000) * (X - 0) ^ 3 * (1 - X) ^ 1 +
      (1473493 / 6250000) * (X - 0) ^ 4 * (1 - X) ^ 0 := by positivity
      _ = p X - (1651507 / 6250000) := by
        dsimp only [p, v, k, h]
        norm_num
        ring
  linarith only [hcert]

theorem p_lower {X : ℝ} (ha : 0 ≤ X) (hb : X ≤ 1) :
    (1651507 / 6250000) ≤ p X := by
  exact p_lower_part0 ha hb

private theorem p_upper_part0 {X : ℝ} (ha : 0 ≤ X) (hb : X ≤ 1) :
    0 ≤ 1/2 - p X := by
  have hu : 0 ≤ X - 0 := sub_nonneg.mpr ha
  have hv : 0 ≤ 1 - X := sub_nonneg.mpr hb
  have hcert : 0 ≤ 1/2 - p X - 0 := by
    calc
      0 ≤ (1473493 / 6250000) * (X - 0) ^ 0 * (1 - X) ^ 4 +
      (39125019 / 50000000) * (X - 0) ^ 1 * (1 - X) ^ 3 +
      (87542891 / 100000000) * (X - 0) ^ 2 * (1 - X) ^ 2 +
      (6665103 / 20000000) * (X - 0) ^ 3 * (1 - X) ^ 1 := by positivity
      _ = 1/2 - p X - 0 := by
        dsimp only [p, v, k, h]
        norm_num
        ring
  linarith only [hcert]

theorem p_upper {X : ℝ} (ha : 0 ≤ X) (hb : X ≤ 1) :
    0 ≤ 1/2 - p X := by
  exact p_upper_part0 ha hb


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

private theorem Q10_lower_part0 {X : ℝ} (ha : 0 ≤ X) (hb : X ≤ 1) :
    (1 / 4000) ≤ Q1 false X := by
  have hu : 0 ≤ X - 0 := sub_nonneg.mpr ha
  have hv : 0 ≤ 1 - X := sub_nonneg.mpr hb
  have hcert : 0 ≤ Q1 false X - (1 / 4000) := by
    calc
      0 ≤ (401858697 / 7062500000) * (X - 0) ^ 0 * (1 - X) ^ 5 +
      (23821484731 / 56500000000) * (X - 0) ^ 1 * (1 - X) ^ 4 +
      (182224852041 / 141250000000) * (X - 0) ^ 2 * (1 - X) ^ 3 +
      (555959690843 / 282500000000) * (X - 0) ^ 3 * (1 - X) ^ 2 +
      (104694978609 / 70625000000) * (X - 0) ^ 4 * (1 - X) ^ 1 +
      (1014541 / 2260000) * (X - 0) ^ 5 * (1 - X) ^ 0 := by positivity
      _ = Q1 false X - (1 / 4000) := by
        dsimp only [p, v, k, h, pSeries, aSeries, bit, d, H, c, N, l, hh, uZero, uOne, Tk, T1, T2, Q0, Q1, Y, Yprime, B0, B1, B2, discr, total]
        norm_num
        ring
  linarith only [hcert]

theorem Q10_lower {X : ℝ} (ha : 0 ≤ X) (hb : X ≤ 1) :
    (1 / 4000) ≤ Q1 false X := by
  exact Q10_lower_part0 ha hb

private theorem Q11_lower_part0 {X : ℝ} (ha : 0 ≤ X) (hb : X ≤ 1) :
    (1 / 4000) ≤ Q1 true X := by
  have hu : 0 ≤ X - 0 := sub_nonneg.mpr ha
  have hv : 0 ≤ 1 - X := sub_nonneg.mpr hb
  have hcert : 0 ≤ Q1 true X - (1 / 4000) := by
    calc
      0 ≤ (83130855038973 / 195312500000000) * (X - 0) ^ 0 * (1 - X) ^ 8 +
      (58074341534074523 / 17187500000000000) * (X - 0) ^ 1 * (1 - X) ^ 7 +
      (161754312088447973 / 13750000000000000) * (X - 0) ^ 2 * (1 - X) ^ 6 +
      (1614659272241560729 / 68750000000000000) * (X - 0) ^ 3 * (1 - X) ^ 5 +
      (8096263173487397231 / 275000000000000000) * (X - 0) ^ 4 * (1 - X) ^ 4 +
      (653455827646010503 / 27500000000000000) * (X - 0) ^ 5 * (1 - X) ^ 3 +
      (132875110518381699 / 11000000000000000) * (X - 0) ^ 6 * (1 - X) ^ 2 +
      (311852255063 / 88000000000) * (X - 0) ^ 7 * (1 - X) ^ 1 +
      (2533 / 5500) * (X - 0) ^ 8 * (1 - X) ^ 0 := by positivity
      _ = Q1 true X - (1 / 4000) := by
        dsimp only [p, v, k, h, pSeries, aSeries, bit, d, H, c, N, l, hh, uZero, uOne, Tk, T1, T2, Q0, Q1, Y, Yprime, B0, B1, B2, discr, total]
        norm_num
        ring
  linarith only [hcert]

theorem Q11_lower {X : ℝ} (ha : 0 ≤ X) (hb : X ≤ 1) :
    (1 / 4000) ≤ Q1 true X := by
  exact Q11_lower_part0 ha hb


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

theorem Q1_error {p q a b k x e : ℝ} (hp0 : 0 ≤ p) (hp : p ≤ 1/2)
    (hq0 : 0 ≤ q) (hq : q ≤ 1/2) (hx0 : 0 ≤ x) (hx : x ≤ 1)
    (hpq : |p-q| ≤ e) (hab : |a-b| ≤ 2*e) (s : Bool) :
    |Q1 p a k x s-Q1 q b k x s| ≤ 8*e := by
  let z := -bit s-(2-bit s)*x-d s*(1+bit s-bit s*x)+
    d s*bit s*(p+q)-hh s*(uOne s)^2
  have hz : |z| ≤ 6 := by
    rw [abs_le]
    constructor <;> cases s <;> norm_num [z, bit, d, hh, uOne] <;> linarith
  have hd : |-d s| ≤ 1 := by cases s <;> norm_num [d]
  have hid : Q1 p a k x s-Q1 q b k x s = (p-q)*z+(a-b)*(-d s) := by
    dsimp only [Q1, N, c, ell]
    dsimp only [z]
    ring
  rw [hid]
  calc
    _ ≤ (6+2*1)*e := add_product_abs_bound hpq hz hab hd
    _ = 8*e := by ring

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

private theorem Q1_compat (s : Bool) (X : ℝ) :
    ScalarTransfer.Q1 (p X) (v X) (k X) (1-X) s = Q1 s X := rfl

private theorem p_bounds {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1) :
    0 ≤ p (1-x) ∧ p (1-x) ≤ 1/2 := by
  have hlo := p_lower (sub_nonneg.mpr hx) (by linarith : 1-x ≤ 1)
  have hhi := p_upper (sub_nonneg.mpr hx) (by linarith : 1-x ≤ 1)
  constructor <;> linarith

private theorem Q1_error_actual {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1) (s : Bool) :
    |Q1 s (1-x)-ScalarTransfer.Q1 (P x) (A x) (k (1-x)) x s| ≤ 8*(3/400000) := by
  have hb := p_bounds hx0 hx
  have he := ScalarTransfer.Q1_error (k := k (1-x)) hb.1 hb.2 (P_nonneg_s35 x) (P_le_half_s35 hx0)
    hx0 hx (p_approximation_s35 hx0 hx)
    (show |v (1-x)-A x| ≤ 2*(3/400000) by convert a_approximation_s35 hx0 hx using 1; norm_num) s
  have hid : ScalarTransfer.Q1 (p (1-x)) (v (1-x)) (k (1-x)) x s = Q1 s (1-x) := by
    simpa only [sub_sub_cancel] using Q1_compat s (1-x)
  rwa [hid] at he

theorem Q1_actual_pos_s35_oai {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1) (s : Bool) :
    0 < ScalarTransfer.Q1 (P x) (A x) (k (1-x)) x s := by
  have he := (abs_le.mp (Q1_error_actual hx0 hx s)).2
  have hX0 := sub_nonneg.mpr hx
  have hX : 1-x ≤ 1 := by linarith
  cases s
  · have hc := Q10_lower hX0 hX
    linarith
  · have hc := Q11_lower hX0 hX
    linarith

end MetricKMedian.Certificates


end
end

end OAI
end

theorem solution : type_of% @OAI.MetricKMedian.Certificates.Q1_actual_pos_s35_oai := @OAI.MetricKMedian.Certificates.Q1_actual_pos_s35_oai
