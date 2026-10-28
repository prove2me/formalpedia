-- Prove2me | solution 1 for OAI.MetricKMedian.Certificates.T2_actual_pos_s35
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T10:50:25.962729+00:00
-- url     : https://prove2.me/submissions/4e7758b7-51b2-44f4-b17e-3e78c6aca98a

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

private theorem T2_lower_part0 {X : ℝ} (ha : 0 ≤ X) (hb : X ≤ 1) :
    (1 / 4000) ≤ T2 X := by
  have hu : 0 ≤ X - 0 := sub_nonneg.mpr ha
  have hv : 0 ≤ 1 - X := sub_nonneg.mpr hb
  have hcert : 0 ≤ T2 X - (1 / 4000) := by
    calc
      0 ≤ (2722592558549 / 19531250000000) * (X - 0) ^ 0 * (1 - X) ^ 9 +
      (21263759547693 / 15625000000000) * (X - 0) ^ 1 * (1 - X) ^ 8 +
      (7071626853427401 / 1250000000000000) * (X - 0) ^ 2 * (1 - X) ^ 7 +
      (33014244895018643 / 2500000000000000) * (X - 0) ^ 3 * (1 - X) ^ 6 +
      (95503164332439199 / 5000000000000000) * (X - 0) ^ 4 * (1 - X) ^ 5 +
      (177225629579532481 / 10000000000000000) * (X - 0) ^ 5 * (1 - X) ^ 4 +
      (5248520160917909 / 500000000000000) * (X - 0) ^ 6 * (1 - X) ^ 3 +
      (1517240450320609 / 400000000000000) * (X - 0) ^ 7 * (1 - X) ^ 2 +
      (747642107 / 1000000000) * (X - 0) ^ 8 * (1 - X) ^ 1 +
      (239 / 4000) * (X - 0) ^ 9 * (1 - X) ^ 0 := by positivity
      _ = T2 X - (1 / 4000) := by
        dsimp only [p, v, k, h, pSeries, aSeries, bit, d, H, c, N, l, hh, uZero, uOne, Tk, T1, T2, Q0, Q1, Y, Yprime, B0, B1, B2, discr, total]
        norm_num
        ring
  linarith only [hcert]

theorem T2_lower {X : ℝ} (ha : 0 ≤ X) (hb : X ≤ 1) :
    (1 / 4000) ≤ T2 X := by
  exact T2_lower_part0 ha hb


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

theorem T2_error {p q x e : ℝ} (hp0 : 0 ≤ p) (hp : p ≤ 1/2)
    (hq0 : 0 ≤ q) (hq : q ≤ 1/2) (hx0 : 0 ≤ x) (hx : x ≤ 1)
    (he : |p-q| ≤ e) : |T2 p x-T2 q x| ≤ 6*e := by
  let z := p+q-2-(19/50)*(1-x)+x
  have hz0 : -3 ≤ z := by dsimp [z]; linarith
  have hz1 : z ≤ 0 := by dsimp [z]; linarith
  have hzx0 : -6 ≤ z*(1+x) := by
    have h := mul_nonneg (show 0 ≤ z+3 by linarith) (show 0 ≤ 1+x by linarith)
    nlinarith
  have hzx1 : z*(1+x) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hz1 (by linarith)
  have hc : |z*(1+x)+2*x| ≤ 6 := by rw [abs_le]; constructor <;> linarith
  have hid : T2 p x-T2 q x = (p-q)*(z*(1+x)+2*x) := by
    unfold T2
    dsimp only [z]
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

private theorem T2_compat (X : ℝ) : ScalarTransfer.T2 (p X) (1-X) = T2 X := by
  unfold ScalarTransfer.T2 T2
  ring

private theorem p_bounds {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1) :
    0 ≤ p (1-x) ∧ p (1-x) ≤ 1/2 := by
  have hlo := p_lower (sub_nonneg.mpr hx) (by linarith : 1-x ≤ 1)
  have hhi := p_upper (sub_nonneg.mpr hx) (by linarith : 1-x ≤ 1)
  constructor <;> linarith

private theorem T2_error_actual {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1) :
    |T2 (1-x)-ScalarTransfer.T2 (P x) x| ≤ 6*(3/400000) := by
  have hb := p_bounds hx0 hx
  have he := ScalarTransfer.T2_error hb.1 hb.2 (P_nonneg_s35 x) (P_le_half_s35 hx0)
    hx0 hx (p_approximation_s35 hx0 hx)
  have hid : ScalarTransfer.T2 (p (1-x)) x = T2 (1-x) := by
    simpa only [sub_sub_cancel] using T2_compat (1-x)
  rwa [hid] at he

theorem T2_actual_pos_s35_oai {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1) :
    0 < ScalarTransfer.T2 (P x) x := by
  have he := (abs_le.mp (T2_error_actual hx0 hx)).2
  have hc := T2_lower (sub_nonneg.mpr hx) (by linarith : 1-x ≤ 1)
  linarith

end MetricKMedian.Certificates


end
end

end OAI
end

theorem solution : type_of% @OAI.MetricKMedian.Certificates.T2_actual_pos_s35_oai := @OAI.MetricKMedian.Certificates.T2_actual_pos_s35_oai
