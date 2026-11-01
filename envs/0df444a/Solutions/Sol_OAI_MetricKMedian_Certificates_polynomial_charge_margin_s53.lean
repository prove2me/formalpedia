-- Prove2me | solution 1 for OAI.MetricKMedian.Certificates.polynomial_charge_margin_s53
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T07:05:28.434708+00:00
-- url     : https://prove2.me/submissions/d2cf71b2-c3b9-4a25-9efd-026d1c0ec8ba

import Mathlib
import Definitions.Def_OAIQ053K002
import Theorems.Thm_OAI_MetricKMedian_Certificates_B1_1_2_positive_s53
import Theorems.Thm_OAI_MetricKMedian_Certificates_B2_1_2_positive_s53
import Theorems.Thm_OAI_MetricKMedian_Certificates_bernCoeff_0_0_nonneg_s53
import Theorems.Thm_OAI_MetricKMedian_Certificates_bernCoeff_0_1_nonneg_s53
import Theorems.Thm_OAI_MetricKMedian_Certificates_bernCoeff_0_2_nonneg_s53
import Theorems.Thm_OAI_MetricKMedian_Certificates_bernCoeff_0_3_nonneg_s53
import Theorems.Thm_OAI_MetricKMedian_Certificates_bernCoeff_1_0_nonneg_s53
import Theorems.Thm_OAI_MetricKMedian_Certificates_bernCoeff_1_1_nonneg_s53
import Theorems.Thm_OAI_MetricKMedian_Certificates_bernCoeff_1_3_nonneg_s53
import Theorems.Thm_OAI_MetricKMedian_Certificates_discr_1_2_positive_s53

section
-- module Solutions.OAIQ053_KM.KMedian_Analysis_BernsteinTrue
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.Certificates

private theorem B0_1_2_nonneg_part0 {X : ℝ} (ha : 0 ≤ X) (hb : X ≤ 1) :
    0 ≤ B0 true 2 X := by
  have hu : 0 ≤ X - 0 := sub_nonneg.mpr ha
  have hv : 0 ≤ 1 - X := sub_nonneg.mpr hb
  have hcert : 0 ≤ B0 true 2 X - 0 := by
    calc
      0 ≤ (15848072128951 / 58593750000000) * (X - 0) ^ 2 * (1 - X) ^ 8 +
      (43907041384323 / 19531250000000) * (X - 0) ^ 3 * (1 - X) ^ 7 +
      (152782377472896509 / 18750000000000000) * (X - 0) ^ 4 * (1 - X) ^ 6 +
      (157534160614160363 / 9375000000000000) * (X - 0) ^ 5 * (1 - X) ^ 5 +
      (107654518872877081 / 5000000000000000) * (X - 0) ^ 6 * (1 - X) ^ 4 +
      (656825037627772673 / 37500000000000000) * (X - 0) ^ 7 * (1 - X) ^ 3 +
      (132084491201709103 / 15000000000000000) * (X - 0) ^ 8 * (1 - X) ^ 2 +
      (933130591 / 375000000) * (X - 0) ^ 9 * (1 - X) ^ 1 +
      (4499 / 15000) * (X - 0) ^ 10 * (1 - X) ^ 0 := by positivity
      _ = B0 true 2 X - 0 := by
        dsimp only [p, v, k, h, pSeries, aSeries, bit, d, H, c, N, l, hh, uZero, uOne, Tk, T1, T2, Q0, Q1, Y, Yprime, B0, B1, B2, discr, total]
        norm_num
        ring
  linarith only [hcert]

theorem B0_1_2_nonneg {X : ℝ} (ha : 0 ≤ X) (hb : X ≤ 1) :
    0 ≤ B0 true 2 X := by
  exact B0_1_2_nonneg_part0 ha hb

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

theorem bernCoeff_1_2_nonneg {X r : ℝ} (hX0 : 0 ≤ X) (hX : X ≤ 1)
    (hr0 : 0 ≤ r) (_hr : r ≤ 1) : 0 ≤ bernCoeff true 2 X r := by
  have ha := B0_1_2_nonneg hX0 hX
  unfold bernCoeff
  by_cases hcut : X ≤ 1/5
  · have hb := B1_1_2_positive_s53 hX0 hcut
    have hc := B2_1_2_positive_s53 hX0 hcut
    exact add_nonneg (add_nonneg ha (mul_nonneg (by linarith) hr0))
      (mul_nonneg (by linarith) (sq_nonneg r))
  · have hd := discr_1_2_positive_s53 (le_of_not_ge hcut) hX
    exact quadratic_of_discriminant ha (by dsimp only [discr] at hd; linarith)

theorem charge_expansion (s : Bool) (X η r : ℝ) :
    ChargeTransfer.charge (p X) (v X) (k X) (H s X) (1-X) (X*η) r s -
      (1/5000)*(r+(X*η)^2) =
    bernCoeff s 0 X r*(1-η)^3+3*bernCoeff s 1 X r*η*(1-η)^2+
      3*bernCoeff s 2 X r*η^2*(1-η)+bernCoeff s 3 X r*η^3 := by
  dsimp only [ChargeTransfer.charge, ChargeTransfer.F1, ChargeTransfer.F2,
    ChargeTransfer.F3, ChargeTransfer.F4, ChargeTransfer.c, bernCoeff,
    B0, B1, B2, N, l, c]
  have hb : ChargeTransfer.bit s = bit s := rfl
  rw [hb]
  norm_num
  ring

theorem polynomial_charge_margin_s53_oai {X w r : ℝ} (hX0 : 0 ≤ X) (hX : X ≤ 1)
    (hw0 : 0 ≤ w) (hw : w ≤ X) (hr0 : 0 ≤ r) (_hr : r ≤ 1) (s : Bool) :
    (1/5000)*(r+w^2) ≤ ChargeTransfer.charge (p X) (v X) (k X) (H s X) (1-X) w r s := by
  have hcoeff : ∀ i : Fin 4, 0 ≤ bernCoeff s i X r := by
    intro i
    fin_cases i <;> cases s
    · exact bernCoeff_0_0_nonneg_s53 hX0 hX hr0 _hr
    · exact bernCoeff_1_0_nonneg_s53 hX0 hX hr0 _hr
    · exact bernCoeff_0_1_nonneg_s53 hX0 hX hr0 _hr
    · exact bernCoeff_1_1_nonneg_s53 hX0 hX hr0 _hr
    · exact bernCoeff_0_2_nonneg_s53 hX0 hX hr0 _hr
    · exact bernCoeff_1_2_nonneg hX0 hX hr0 _hr
    · exact bernCoeff_0_3_nonneg_s53 hX0 hX hr0 _hr
    · exact bernCoeff_1_3_nonneg_s53 hX0 hX hr0 _hr
  have hη : ∃ η : ℝ, 0 ≤ η ∧ η ≤ 1 ∧ w = X*η := by
    by_cases hzero : X = 0
    · exact ⟨0, le_refl _, zero_le_one, by rw [hzero]; linarith⟩
    · have hpos : 0 < X := lt_of_le_of_ne hX0 (Ne.symm hzero)
      refine ⟨w/X, div_nonneg hw0 hX0, (div_le_one hpos).mpr hw, ?_⟩
      field_simp
  obtain ⟨η, hη0, hη1, hwη⟩ := hη
  have hηc : 0 ≤ 1-η := sub_nonneg.mpr hη1
  have h0 := hcoeff 0
  have h1 := hcoeff 1
  have h2 := hcoeff 2
  have h3 := hcoeff 3
  have hbern : 0 ≤ bernCoeff s 0 X r*(1-η)^3+3*bernCoeff s 1 X r*η*(1-η)^2+
      3*bernCoeff s 2 X r*η^2*(1-η)+bernCoeff s 3 X r*η^3 := by
    positivity
  rw [←charge_expansion] at hbern
  rw [hwη]
  linarith only [hbern]

end MetricKMedian.Certificates


end
end

end OAI
end

theorem solution : type_of% @OAI.MetricKMedian.Certificates.polynomial_charge_margin_s53_oai := @OAI.MetricKMedian.Certificates.polynomial_charge_margin_s53_oai
