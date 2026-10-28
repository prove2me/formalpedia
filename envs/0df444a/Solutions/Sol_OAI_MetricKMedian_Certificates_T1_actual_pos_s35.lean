-- Prove2me | solution 1 for OAI.MetricKMedian.Certificates.T1_actual_pos_s35
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T10:50:24.784734+00:00
-- url     : https://prove2.me/submissions/cb36f41b-3991-4008-a8d0-c65c0d95098b

import Mathlib
import Definitions.Def_OAIQ035K000
import Definitions.Def_OAIQ035K002
import Definitions.Def_OAIQ035K011
import Theorems.Thm_OAI_MetricKMedian_Analytic_P_le_half_s35
import Theorems.Thm_OAI_MetricKMedian_Analytic_P_nonneg_s35
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

private theorem T1_lower_part0 {X : ℝ} (ha : 0 ≤ X) (hb : X ≤ 1) :
    (1 / 4000) ≤ T1 X := by
  have hu : 0 ≤ X - 0 := sub_nonneg.mpr ha
  have hv : 0 ≤ 1 - X := sub_nonneg.mpr hb
  have hcert : 0 ≤ T1 X - (1 / 4000) := by
    calc
      0 ≤ (44877741 / 312500000) * (X - 0) ^ 0 * (1 - X) ^ 10 +
      (123804942226473 / 97656250000000) * (X - 0) ^ 1 * (1 - X) ^ 9 +
      (48641107020517 / 9765625000000) * (X - 0) ^ 2 * (1 - X) ^ 8 +
      (35853906645177401 / 3125000000000000) * (X - 0) ^ 3 * (1 - X) ^ 7 +
      (107381003477518643 / 6250000000000000) * (X - 0) ^ 4 * (1 - X) ^ 6 +
      (219116255716439199 / 12500000000000000) * (X - 0) ^ 5 * (1 - X) ^ 5 +
      (310376152073532481 / 25000000000000000) * (X - 0) ^ 6 * (1 - X) ^ 4 +
      (7613201630217909 / 1250000000000000) * (X - 0) ^ 7 * (1 - X) ^ 3 +
      (2011350239200609 / 1000000000000000) * (X - 0) ^ 8 * (1 - X) ^ 2 +
      (205349429 / 500000000) * (X - 0) ^ 9 * (1 - X) ^ 1 +
      (159 / 4000) * (X - 0) ^ 10 * (1 - X) ^ 0 := by positivity
      _ = T1 X - (1 / 4000) := by
        dsimp only [p, v, k, h, pSeries, aSeries, bit, d, H, c, N, l, hh, uZero, uOne, Tk, T1, T2, Q0, Q1, Y, Yprime, B0, B1, B2, discr, total]
        norm_num
        ring
  linarith only [hcert]

theorem T1_lower {X : ℝ} (ha : 0 ≤ X) (hb : X ≤ 1) :
    (1 / 4000) ≤ T1 X := by
  exact T1_lower_part0 ha hb


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

theorem T1_error {p q x e : ℝ} (hp0 : 0 ≤ p) (hp : p ≤ 1/2)
    (hq0 : 0 ≤ q) (hq : q ≤ 1/2) (hx0 : 0 ≤ x) (hx : x ≤ 1)
    (he : |p-q| ≤ e) : |T1 p x-T1 q x| ≤ 5*e := by
  have hxprod0 : 0 ≤ (1-x)*(1+x) := mul_nonneg (by linarith) (by linarith)
  have hxprod1 : (1-x)*(1+x) ≤ 1 := by nlinarith [sq_nonneg x]
  have hprod := mul_le_mul (show p+q ≤ 1 by linarith) hxprod1 hxprod0 (by norm_num : (0:ℝ) ≤ 1)
  have hprod0 : 0 ≤ (p+q)*((1-x)*(1+x)) := mul_nonneg (by linarith) hxprod0
  have hc : |-1-(28/25)*(1+x)+(2/5)*(p+q)*((1-x)*(1+x))| ≤ 5 := by
    rw [abs_le]
    constructor <;> nlinarith only [hx0, hx, hprod, hprod0]
  have hid : T1 p x-T1 q x =
      (p-q)*(-1-(28/25)*(1+x)+(2/5)*(p+q)*((1-x)*(1+x))) := by
    unfold T1
    ring
  rw [hid]
  have h := mul_abs_bound he hc
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

private theorem T1_compat (X : ℝ) : ScalarTransfer.T1 (p X) (1-X) = T1 X := by
  unfold ScalarTransfer.T1 T1
  ring

private theorem p_bounds {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1) :
    0 ≤ p (1-x) ∧ p (1-x) ≤ 1/2 := by
  have hlo := p_lower (sub_nonneg.mpr hx) (by linarith : 1-x ≤ 1)
  have hhi := p_upper (sub_nonneg.mpr hx) (by linarith : 1-x ≤ 1)
  constructor <;> linarith

private theorem T1_error_actual {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1) :
    |T1 (1-x)-ScalarTransfer.T1 (P x) x| ≤ 5*(3/400000) := by
  have hb := p_bounds hx0 hx
  have he := ScalarTransfer.T1_error hb.1 hb.2 (P_nonneg_s35 x) (P_le_half_s35 hx0)
    hx0 hx (p_approximation_s35 hx0 hx)
  have hid : ScalarTransfer.T1 (p (1-x)) x = T1 (1-x) := by
    simpa only [sub_sub_cancel] using T1_compat (1-x)
  rwa [hid] at he

theorem T1_actual_pos_s35_oai {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1) :
    0 < ScalarTransfer.T1 (P x) x := by
  have he := (abs_le.mp (T1_error_actual hx0 hx)).2
  have hc := T1_lower (sub_nonneg.mpr hx) (by linarith : 1-x ≤ 1)
  linarith

end MetricKMedian.Certificates


end
end

end OAI
end

theorem solution : type_of% @OAI.MetricKMedian.Certificates.T1_actual_pos_s35_oai := @OAI.MetricKMedian.Certificates.T1_actual_pos_s35_oai
