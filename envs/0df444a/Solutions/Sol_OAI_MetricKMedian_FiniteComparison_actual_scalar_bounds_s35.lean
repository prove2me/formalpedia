-- Prove2me | solution 1 for OAI.MetricKMedian.FiniteComparison.actual_scalar_bounds_s35
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T11:16:54.230977+00:00
-- url     : https://prove2.me/submissions/c4e0cf30-fe8e-4b11-bc7a-eb8008549dcd

import Mathlib
import Definitions.Def_OAIQ035K044
import Definitions.Def_OAIQ035K045
import Theorems.Thm_OAI_MetricKMedian_Analytic_P_le_half_s35
import Theorems.Thm_OAI_MetricKMedian_Analytic_P_nonneg_s35
import Theorems.Thm_OAI_MetricKMedian_Analytic_m_nonneg_s35
import Theorems.Thm_OAI_MetricKMedian_Certificates_Q0_actual_pos_s35
import Theorems.Thm_OAI_MetricKMedian_Certificates_Q1_actual_pos_s35
import Theorems.Thm_OAI_MetricKMedian_Certificates_T1_actual_pos_s35
import Theorems.Thm_OAI_MetricKMedian_Certificates_T2_actual_pos_s35
import Theorems.Thm_OAI_MetricKMedian_Certificates_Y_actual_bounds_s35
import Theorems.Thm_OAI_MetricKMedian_Certificates_Yprime_actual_bounds_s35
import Theorems.Thm_OAI_MetricKMedian_Certificates_a_approximation_s35
import Theorems.Thm_OAI_MetricKMedian_Certificates_h_lower_s35
import Theorems.Thm_OAI_MetricKMedian_Certificates_h_upper_s35
import Theorems.Thm_OAI_MetricKMedian_Certificates_k_envelope_s35
import Theorems.Thm_OAI_MetricKMedian_Certificates_p_approximation_s35
import Theorems.Thm_OAI_MetricKMedian_Certificates_polynomial_charge_margin_s35
import Theorems.Thm_OAI_MetricKMedian_ChargeTransfer_charge_error_s35

section
-- module Solutions.OAIQ035_KM.KMedian_Analysis_Coefficients
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section

namespace MetricKMedian.Analytic

theorem exp_integrable (x : ℝ) :
    IntervalIntegrable (fun t : ℝ => Real.exp (-t * x)) MeasureTheory.volume 0 1 := by
  apply Continuous.intervalIntegrable
  fun_prop

theorem texp_integrable (x : ℝ) :
    IntervalIntegrable (fun t : ℝ => t * Real.exp (-t * x)) MeasureTheory.volume 0 1 := by
  apply Continuous.intervalIntegrable
  fun_prop

private theorem exp_derivative_integral (x : ℝ) :
    -x * (∫ t : ℝ in 0..1, Real.exp (-t * x)) = Real.exp (-x) - 1 := by
  rw [← intervalIntegral.integral_const_mul]
  have hderiv : ∀ t : ℝ, HasDerivAt (fun t : ℝ => Real.exp (-t * x))
      (-x * Real.exp (-t * x)) t := by
    intro t
    simpa only [Pi.neg_apply, id_eq, neg_mul, one_mul, mul_one, mul_neg, mul_comm]
      using (((hasDerivAt_id t).neg.mul_const x).exp)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hderiv t)]
  · simp
  · exact (exp_integrable x).const_mul _

private theorem texp_derivative_integral (x : ℝ) :
    (∫ t : ℝ in 0..1, Real.exp (-t * x)) - x * P x = Real.exp (-x) := by
  rw [P, ← intervalIntegral.integral_const_mul,
    ← intervalIntegral.integral_sub (exp_integrable x) ((texp_integrable x).const_mul x)]
  have hderiv : ∀ t : ℝ, HasDerivAt (fun t : ℝ => t * Real.exp (-t * x))
      (Real.exp (-t * x) - x * (t * Real.exp (-t * x))) t := by
    intro t
    have he : HasDerivAt (fun t : ℝ => Real.exp (-t * x))
        (-x * Real.exp (-t * x)) t := by
      simpa only [Pi.neg_apply, id_eq, neg_mul, one_mul, mul_one, mul_neg, mul_comm]
        using (((hasDerivAt_id t).neg.mul_const x).exp)
    convert (hasDerivAt_id t).mul he using 1 <;> try rfl
    simp only [id_eq]
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hderiv t)]
  · simp
  · exact (exp_integrable x).sub ((texp_integrable x).const_mul x)

theorem A_eq (x : ℝ) :
    A x = 1 + 2 * (1 - ∫ t : ℝ in 0..1, Real.exp (-t * x)) := by
  rw [A, intervalIntegral.integral_sub (intervalIntegrable_const) (exp_integrable x)]
  simp

theorem coefficient_identity (x : ℝ) :
    (1 + x) * (A x - 1) = 2 * x * (1 - P x) := by
  rw [A_eq]
  have h₁ := exp_derivative_integral x
  have h₂ := texp_derivative_integral x
  nlinarith

theorem P_antitone : Antitone P := by
  intro x y hxy
  apply intervalIntegral.integral_mono_on (by norm_num) (texp_integrable y) (texp_integrable x)
  intro t ht
  apply mul_le_mul_of_nonneg_left _ ht.1
  apply Real.exp_le_exp.mpr
  nlinarith [ht.1]

theorem one_le_A {x : ℝ} (hx : 0 ≤ x) : 1 ≤ A x := by
  have h : 0 ≤ ∫ t : ℝ in 0..1, (1 - Real.exp (-t * x)) := by
    apply intervalIntegral.integral_nonneg (by norm_num)
    intro t ht
    have hneg : -t * x ≤ 0 := by nlinarith [ht.1]
    have := Real.exp_le_one_iff.mpr hneg
    linarith
  unfold A
  linarith

theorem A_le_one_add (x : ℝ) : A x ≤ 1 + x := by
  have hi : IntervalIntegrable (fun t : ℝ => 1 - Real.exp (-t * x))
      MeasureTheory.volume 0 1 := by
    apply Continuous.intervalIntegrable
    fun_prop
  have hi' : IntervalIntegrable (fun t : ℝ => t * x) MeasureTheory.volume 0 1 := by
    apply Continuous.intervalIntegrable
    fun_prop
  have h := intervalIntegral.integral_mono_on (μ := MeasureTheory.volume)
    (a := (0 : ℝ)) (b := 1) (by norm_num) hi hi' (fun t _ => by
      have he := Real.add_one_le_exp (-t * x)
      nlinarith)
  rw [intervalIntegral.integral_mul_const] at h
  norm_num at h
  unfold A
  simp only [neg_mul]
  linarith

theorem A_le_two {x : ℝ} (hx : x ≤ 1) : A x ≤ 2 := by
  linarith [A_le_one_add x]

end MetricKMedian.Analytic


end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Analysis_FiniteAverages
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.FiniteComparison

theorem denominator_pos {p q : ℝ} (hp : p ≤ 1 / 2)
    (hp0 : 0 ≤ p) (hq : q ≤ 1) : 0 < 1 - p * q := by
  nlinarith [mul_le_mul_of_nonneg_left hq hp0]

theorem kZero_nonneg {p : ℝ} (hp0 : 0 ≤ p) :
    0 ≤ kZero p := by
  have hs : Real.sqrt (1 - p) ≤ 1 := by
    apply Real.sqrt_le_one.mpr
    linarith
  exact div_nonneg (sub_nonneg.mpr hs) (by positivity)

theorem kappa_zero_le {p q : ℝ} (hp0 : 0 ≤ p) (hp : p ≤ 1 / 2)
    (hq : q ≤ 1) : kappa p 0 q ≤ kZero p := by
  have hd := denominator_pos hp hp0 hq
  have hs0 : 0 ≤ Real.sqrt (1 - p) := Real.sqrt_nonneg _
  have hs2 : Real.sqrt (1 - p) ^ 2 = 1 - p := Real.sq_sqrt (by linarith)
  have hp_eq : p = 1 - Real.sqrt (1 - p) ^ 2 := by linarith
  have hk0 := kZero_nonneg hp0
  have identity : kZero p * (1 - p * q) - p * q * (1 - q) =
      kZero p * ((1 + Real.sqrt (1 - p)) * q - 1) ^ 2 := by
    unfold kZero
    field_simp [ne_of_gt (show 0 < 1 + Real.sqrt (1 - p) by positivity)]
    nlinarith [sq_nonneg (Real.sqrt (1 - p) * q)]
  have hid : kappa p 0 q = p * q * (1 - q) / (1 - p * q) := by
    apply (eq_div_iff (ne_of_gt hd)).mpr
    unfold kappa
    simp only [mul_zero, sub_zero, one_mul]
    have he : psi p q * (1 - p * q) = 1 - q :=
      div_mul_cancel₀ _ (ne_of_gt hd)
    nlinarith only [he]
  rw [hid, div_le_iff₀ hd]
  have h := mul_nonneg hk0 (sq_nonneg ((1 + Real.sqrt (1 - p)) * q - 1))
  linarith [identity]

theorem kappa_one_le {p q : ℝ} (hp0 : 0 ≤ p) (hp : p ≤ 1 / 2)
    (hq : q ≤ 1) : kappa p 1 q ≤ 0 := by
  have hd := denominator_pos hp hp0 hq
  have hid : kappa p 1 q = -p * (1 - q) ^ 2 / (1 - p * q) := by
    unfold kappa psi
    simp only [mul_one]
    field_simp [ne_of_gt hd]
    ring
  rw [hid]
  exact div_nonpos_of_nonpos_of_nonneg
    (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hp0) (sq_nonneg _)) hd.le

end MetricKMedian.FiniteComparison

namespace MetricKMedian.FiniteComparison

theorem C_pos {p : ℝ} (hp : p ≤ 1 / 2) (s : Bool) : 0 < C p s := by
  cases s <;> simp only [C, Bool.false_eq_true, ↓reduceIte] <;> linarith

theorem centering_gap_nonneg {p q : ℝ} (hp0 : 0 ≤ p) (hp : p ≤ 1 / 2)
    (hq : q ≤ 1) (s : Bool) : 0 ≤ k p s - (C p s * psi p q - (1 - q)) := by
  cases s
  · have he := kappa_zero_le hp0 hp hq
    simpa only [kappa, mul_zero, sub_zero, one_mul, k, C, Bool.false_eq_true,
      ↓reduceIte] using sub_nonneg.mpr he
  · have he := kappa_one_le hp0 hp hq
    simpa only [kappa, mul_one, k, C, ↓reduceIte] using sub_nonneg.mpr he

end MetricKMedian.FiniteComparison


end
end

end OAI
end

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

private theorem v_lower_part0 {X : ℝ} (ha : 0 ≤ X) (hb : X ≤ 1) :
    1 ≤ v X := by
  have hu : 0 ≤ X - 0 := sub_nonneg.mpr ha
  have hv : 0 ≤ 1 - X := sub_nonneg.mpr hb
  have hcert : 0 ≤ v X - 1 := by
    calc
      0 ≤ (4598493 / 6250000) * (X - 0) ^ 0 * (1 - X) ^ 4 +
      (241471283 / 100000000) * (X - 0) ^ 1 * (1 - X) ^ 3 +
      (66691857 / 25000000) * (X - 0) ^ 2 * (1 - X) ^ 2 +
      (99981621 / 100000000) * (X - 0) ^ 3 * (1 - X) ^ 1 := by positivity
      _ = v X - 1 := by
        dsimp only [p, v, k, h]
        norm_num
        ring
  linarith only [hcert]

theorem v_lower {X : ℝ} (ha : 0 ≤ X) (hb : X ≤ 1) :
    1 ≤ v X := by
  exact v_lower_part0 ha hb

private theorem v_upper_part0 {X : ℝ} (ha : 0 ≤ X) (hb : X ≤ 1) :
    0 ≤ 217/125 - v X := by
  have hu : 0 ≤ X - 0 := sub_nonneg.mpr ha
  have hv : 0 ≤ 1 - X := sub_nonneg.mpr hb
  have hcert : 0 ≤ 217/125 - v X - 0 := by
    calc
      0 ≤ (1507 / 6250000) * (X - 0) ^ 0 * (1 - X) ^ 4 +
      (52928717 / 100000000) * (X - 0) ^ 1 * (1 - X) ^ 3 +
      (43708143 / 25000000) * (X - 0) ^ 2 * (1 - X) ^ 2 +
      (194418379 / 100000000) * (X - 0) ^ 3 * (1 - X) ^ 1 +
      (92 / 125) * (X - 0) ^ 4 * (1 - X) ^ 0 := by positivity
      _ = 217/125 - v X - 0 := by
        dsimp only [p, v, k, h]
        norm_num
        ring
  linarith only [hcert]

theorem v_upper {X : ℝ} (ha : 0 ≤ X) (hb : X ≤ 1) :
    0 ≤ 217/125 - v X := by
  exact v_upper_part0 ha hb

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
-- module Solutions.OAIQ035_KM.KMedian_Analysis_NormalizedTransfer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.ScalarTransfer

private theorem reciprocal_quadratic {c t w γ : ℝ} (ht : 0 < t)
    (hc : γ^2 ≤ (8/5)*c) : γ*w ≤ c/t+(2/5)*w^2*t := by
  have hs := sq_nonneg ((4/5)*w*t-γ)
  have hpoly : γ*w*t ≤ c+(2/5)*w^2*t^2 := by nlinarith only [hs, hc]
  calc
    γ*w ≤ (c+(2/5)*w^2*t^2)/t := (le_div_iff₀ ht).mpr hpoly
    _ = c/t+(2/5)*w^2*t := by field_simp

private theorem first_gap_identity {p x w r : ℝ} (hr : r ≠ 0)
    (hx : 1+x ≠ 0) (hd : 1-p*r ≠ 0) (s : Bool) :
    c p s*(1-p)/(1-p*r) -
      (2*x*(1-p)/(1+x)-2*x*p+(2-bit s)*p*(x+w)-(2/5)*p*w^2/r) =
    c p s*(1-p)-2*x*(1-p)/(1+x)+bit s*p*x-(2-bit s)*p*w+(2/5)*p^2*w^2+
      p*(c p s*(1-p)/((1-p*r)/r)+(2/5)*w^2*((1-p*r)/r)) := by
  field_simp [hr, hx, hd]
  ring

theorem first_scalar {p x w m r : ℝ} (hp0 : 0 ≤ p) (hp : p ≤ 1/2)
    (hx0 : 0 ≤ x) (hx : x ≤ 1) (hw0 : 0 ≤ w) (hw : w ≤ 1-x)
    (hr0 : 0 < r) (hr : r ≤ 1)
    (hm : (1+x)*(m+2*x*p) = 2*x*(1-p))
    (hT1 : 0 ≤ T1 p x) (hT2 : 0 ≤ T2 p x) (s : Bool) :
    m+(2-bit s)*p*(x+w)-(2/5)*(p*w^2)/r ≤ c p s*(1-p)/(1-p*r) := by
  have hxden : 0 < 1+x := by linarith
  have hpr := mul_le_mul hp hr hr0.le (by norm_num : (0:ℝ) ≤ 1/2)
  have hden : 0 < 1-p*r := by linarith
  have ht : 0 < (1-p*r)/r := div_pos hden hr0
  have hm' : m = 2*x*(1-p)/(1+x)-2*x*p := by
    have he : m+2*x*p = 2*x*(1-p)/(1+x) := (eq_div_iff hxden.ne').mpr (by nlinarith only [hm])
    linarith
  have hgap := first_gap_identity (w := w) (ne_of_gt hr0) hxden.ne' hden.ne' s
  rw [←hm'] at hgap
  have hX0 : 0 ≤ 1-x := sub_nonneg.mpr hx
  have hgam : (if s then 31/50 else 22/25 : ℝ)^2 ≤ (8/5)*(c p s*(1-p)) := by
    cases s <;> norm_num [c, bit] <;> nlinarith [sq_nonneg (p-1/2)]
  have hagm := reciprocal_quadratic (w := w) ht hgam
  have hagmp := mul_le_mul_of_nonneg_left hagm hp0
  have hrest : 0 ≤ c p s*(1-p)-2*x*(1-p)/(1+x)+bit s*p*x-
      (2-bit s)*p*w+(2/5)*p^2*w^2+p*((if s then 31/50 else 22/25)*w) := by
    cases s
    · norm_num [c, bit]
      have hsum : w+(1-x) ≤ 2 := by linarith
      have hsum0 : 0 ≤ w+(1-x) := by linarith
      have hpp := mul_le_mul hp hsum hsum0 (by norm_num : (0:ℝ) ≤ 1/2)
      have hquad := mul_nonneg (mul_nonneg hp0 (sub_nonneg.mpr hw))
        (show 0 ≤ 28/25-(2/5)*p*(w+(1-x)) by linarith)
      have hnonneg : 0 ≤ (1-x)*T1 p x/(1+x) := div_nonneg (mul_nonneg hX0 hT1) hxden.le
      have hid : (1-x)*T1 p x/(1+x) =
          (1-p)-2*x*(1-p)/(1+x)-(28/25)*p*(1-x)+(2/5)*p^2*(1-x)^2 := by
        unfold T1
        field_simp
        ring
      rw [hid] at hnonneg
      nlinarith only [hnonneg, hquad]
    · norm_num [c, bit]
      have hlin := mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 19/50) hp0) (sub_nonneg.mpr hw)
      have hquad : 0 ≤ (2/5)*p^2*w^2 := by positivity
      have hnonneg : 0 ≤ T2 p x/(1+x) := div_nonneg hT2 hxden.le
      have hid : T2 p x/(1+x) = (1-p)^2-2*x*(1-p)/(1+x)+p*x-(19/50)*p*(1-x) := by
        unfold T2
        field_simp
        ring
      rw [hid] at hnonneg
      nlinarith only [hnonneg, hlin, hquad]
  have hgd : 0 ≤ c p s*(1-p)/(1-p*r) -
      (m+(2-bit s)*p*(x+w)-(2/5)*p*w^2/r) := by
    rw [hgap]
    linarith only [hagmp, hrest]
  have hresult := sub_nonneg.mp hgd
  convert hresult using 1 <;> first | rfl | ring

private theorem Q0_difference (p a k w W : ℝ) (s : Bool) :
    Q0 p a k w s-Q0 p a k W s =
      p*hh s*((w-uZero s)^2-(W-uZero s)^2) := by
  cases s <;> norm_num [Q0, hh, uZero, d] <;> ring

theorem Q0_minimum {p a k x w : ℝ} (hp0 : 0 ≤ p)
    (hw : w ≤ 1-x) (s : Bool) :
    Q0 p a k (if s then uZero s else min (1-x) (uZero s)) s ≤ Q0 p a k w s := by
  have hsq : ((if s then uZero s else min (1-x) (uZero s))-uZero s)^2 ≤ (w-uZero s)^2 := by
    cases s
    · simp only [Bool.false_eq_true, ↓reduceIte]
      by_cases hcut : 1-x ≤ uZero false
      · rw [min_eq_left hcut]
        nlinarith only [hw, hcut, sq_nonneg (w-(1-x))]
      · rw [min_eq_right (le_of_not_ge hcut), sub_self, zero_pow (by decide : 2 ≠ 0)]
        exact sq_nonneg _
    · simpa only [↓reduceIte, sub_self, zero_pow (by decide : 2 ≠ 0)] using sq_nonneg (w-uZero true)
  have hh0 : 0 ≤ hh s := by cases s <;> norm_num [hh, d]
  have hp := mul_nonneg (mul_nonneg hp0 hh0) (sub_nonneg.mpr hsq)
  rw [←Q0_difference] at hp
  linarith only [hp]

private theorem linear_gap_identity (p a k x w r : ℝ) (s : Bool) :
    stdK p k x w r s-d s*(stdM p a w r s-stdL p a x w r s) =
      (1-r)*Q0 p a k w s+r*(Q1 p a k x s+hh s*p*(w-uOne s)^2) := by
  dsimp only [stdK, stdM, stdL, stdB, Q0, Q1, N, c, ell, uOne, hh]
  cases s <;> norm_num [bit, d] <;> ring

theorem linear_scalar {p a k x w r : ℝ} (hp0 : 0 ≤ p) (hw : w ≤ 1-x)
    (hr0 : 0 ≤ r) (hr : r ≤ 1) (s : Bool)
    (hQ0 : 0 ≤ Q0 p a k (if s then uZero s else min (1-x) (uZero s)) s)
    (hQ1 : 0 ≤ Q1 p a k x s) :
    d s*(stdM p a w r s-stdL p a x w r s) ≤ stdK p k x w r s := by
  have hzero := hQ0.trans (Q0_minimum hp0 hw s)
  have hh0 : 0 ≤ hh s := by cases s <;> norm_num [hh, d]
  have hone : 0 ≤ Q1 p a k x s+hh s*p*(w-uOne s)^2 := by positivity
  have hn := add_nonneg (mul_nonneg (sub_nonneg.mpr hr) hzero) (mul_nonneg hr0 hone)
  rw [←linear_gap_identity] at hn
  exact sub_nonneg.mp hn

theorem Y_le_base {p k x w : ℝ} (hp0 : 0 ≤ p) (s : Bool) :
    Y p k x s ≤ N p k s+(8/5)*p*w^2-stdB p x w s := by
  have hn : 0 ≤ (8/5)*p*(w-5*(2-bit s)/16)^2 := by positivity
  have hid : N p k s+(8/5)*p*w^2-stdB p x w s-Y p k x s =
      (8/5)*p*(w-5*(2-bit s)/16)^2 := by unfold Y stdB; ring
  linarith only [hid, hn]

theorem Yprime_le_base {p k x w : ℝ} (hp0 : 0 ≤ p) (hw : w ≤ 1-x)
    (hx : 1-x ≤ 1/2) : Yprime p k x ≤ 1-k+(8/5)*p*w^2-stdB p x w false := by
  have hb : 0 ≤ 2-(8/5)*(w+(1-x)) := by linarith
  have hn := mul_nonneg (mul_nonneg hp0 (sub_nonneg.mpr hw)) hb
  unfold Yprime stdB bit
  norm_num
  nlinarith only [hn]

end MetricKMedian.ScalarTransfer


end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Analysis_FiniteComparison
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.FiniteComparison

open Analytic

private theorem scalarC (p : ℝ) (s : Bool) : ScalarTransfer.c p s = C p s := by
  cases s <;> simp [ScalarTransfer.c, ScalarTransfer.bit, C]
private theorem scalarD (s : Bool) : ScalarTransfer.d s = d s := rfl
private theorem actualB_nonneg {x w : ℝ} (hx : 0 ≤ x) (hw : 0 ≤ w) (s : Bool) :
    0 ≤ actualB x w s := by
  have hp := P_nonneg_s35 x
  cases s <;> norm_num [actualB, ScalarTransfer.bit] <;> positivity

private theorem proxy_N {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1) (s : Bool) :
    ScalarTransfer.N (P x) (Certificates.k (1-x)) s ≤ C (P x) s-k (P x) s := by
  have hk := Certificates.k_envelope_s35 hx0 hx
  cases s <;> norm_num [ScalarTransfer.N, ScalarTransfer.c, ScalarTransfer.bit, C, k]; linarith

private theorem actual_first {x w : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1)
    (hw0 : 0 ≤ w) (hw : w ≤ 1-x) (s : Bool) {r : ℝ} (hr0 : 0 < r) (hr : r ≤ 1) :
    m x+actualB x w s-(2/5)*(P x*w^2)/r ≤ C (P x) s*(1-P x)/(1-P x*r) := by
  have hm : (1+x)*(m x+2*x*P x)=2*x*(1-P x) := by
    simpa only [m, sub_add_cancel] using coefficient_identity x
  have h := ScalarTransfer.first_scalar (P_nonneg_s35 x) (P_le_half_s35 hx0) hx0 hx hw0 hw hr0 hr
    hm (Certificates.T1_actual_pos_s35 hx0 hx).le (Certificates.T2_actual_pos_s35 hx0 hx).le s
  simpa only [actualB, scalarC] using h

private theorem actual_L {x w : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1)
    (hw0 : 0 ≤ w) (hw : w ≤ 1-x) (s : Bool) {r : ℝ} (hr0 : 0 ≤ r) (hr : r ≤ 1) :
    0 ≤ L (P x) (m x) (P x*w^2) (actualB x w) s r := by
  rcases eq_or_lt_of_le hr0 with hzero | hpos
  · rw [←hzero]; unfold L; simp only [mul_zero, zero_add]; have hp := P_nonneg_s35 x; positivity
  · have hf := actual_first hx0 hx hw0 hw s hpos hr
    have hp0 := P_nonneg_s35 x
    have hp := P_le_half_s35 hx0
    have hd := denominator_pos hp hp0 hr
    have hpr : P x*r ≤ P x := mul_le_of_le_one_right hp0 hr
    have hfrac : C (P x) s*(1-P x)/(1-P x*r) ≤ C (P x) s := by
      apply (div_le_iff₀ hd).mpr
      exact mul_le_mul_of_nonneg_left (by linarith) (C_pos hp s).le
    have hdiv : m x+actualB x w s-C (P x) s ≤ (2/5)*(P x*w^2)/r := by linarith
    have hmul := (le_div_iff₀ hpos).mp hdiv
    unfold L
    nlinarith only [hmul]

private theorem actual_linear {x w : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1)
    (_hw0 : 0 ≤ w) (hw : w ≤ 1-x) (s : Bool) {r : ℝ} (hr0 : 0 ≤ r) (hr : r ≤ 1) :
    d s*G (P x) (m x) (A x+2*P x*w) (P x*w^2) (actualB x w) s r ≤
      K (P x) (P x*w^2) (actualB x w) s r := by
  have hl := ScalarTransfer.linear_scalar (P_nonneg_s35 x) hw hr0 hr s
    (Certificates.Q0_actual_pos_s35 hx0 hx s).le (Certificates.Q1_actual_pos_s35 hx0 hx s).le
  have hm : ScalarTransfer.stdM (P x) (A x) w r s = M (P x) (A x+2*P x*w) s r := by
    simp only [ScalarTransfer.stdM, scalarC, M]
  have hL : ScalarTransfer.stdL (P x) (A x) x w r s =
      L (P x) (m x) (P x*w^2) (actualB x w) s r := by
    simp only [ScalarTransfer.stdL, scalarC, ScalarTransfer.stdB, L, m, actualB, mul_assoc]
  have hk : ScalarTransfer.stdK (P x) (Certificates.k (1-x)) x w r s ≤
      K (P x) (P x*w^2) (actualB x w) s r := by
    have hn := proxy_N hx0 hx s
    unfold ScalarTransfer.stdK ScalarTransfer.stdB K actualB
    linarith only [hn]
  rw [hm, hL, scalarD] at hl
  exact hl.trans hk

private theorem actual_P_small {x : ℝ} (_hx0 : 0 ≤ x) (_hx : x ≤ 1) (hside : 1-x ≤ 1/2) :
    P x ≤ 47/100 := by
  have hanti := P_antitone (show (1/2:ℝ) ≤ x by linarith)
  have happ := (abs_le.mp (Certificates.p_approximation_s35 (by norm_num : (0:ℝ) ≤ 1/2)
    (by norm_num : (1/2:ℝ) ≤ 1))).1
  norm_num [Certificates.p] at happ
  linarith

private theorem kappa_absorb {p b q : ℝ} (hp0 : 0 ≤ p) (hp : p ≤ 47/100)
    (hb : p ≤ b) (_hq0 : 0 ≤ q) (hq : q ≤ 1) :
    (13/25)*(psi p q-(1-q)) ≤ b*(1-q) := by
  have hph : p ≤ 1/2 := by linarith
  have hd := denominator_pos hph hp0 hq
  have hid : psi p q-(1-q)=p*q*(1-q)/(1-p*q) := by
    apply (eq_div_iff hd.ne').mpr
    unfold psi
    rw [sub_mul, div_mul_cancel₀ _ hd.ne']
    ring
  have hpq := mul_le_of_le_one_right hp0 hq
  have hh : (13/25)*q ≤ 1-p*q := by linarith
  have hmul := mul_le_mul_of_nonneg_left hh hp0
  have hmul' := mul_le_mul_of_nonneg_right hb hd.le
  have hn := mul_le_mul_of_nonneg_right (hmul.trans hmul') (sub_nonneg.mpr hq)
  rw [hid]
  rw [←mul_div_assoc, div_le_iff₀ hd]
  nlinarith only [hn]

private theorem actual_final_bounds {x w : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1)
    (hw0 : 0 ≤ w) (hw : w ≤ 1-x) (s : Bool) :
    (1/4 ≤ C (P x) s-k (P x) s+(8/5)*(P x*w^2)-actualB x w s) ∧
    ∀ q : ℝ, 0 ≤ q → q ≤ 1 →
      Certificates.h (1-x) ≤ C (P x) s-k (P x) s+(8/5)*(P x*w^2)-actualB x w s*q+
        (13/25)*(k (P x) s-(C (P x) s*psi (P x) q-(1-q))) := by
  by_cases hside : s = true ∨ 1-x ≥ 1/2
  · have hy := Certificates.Y_actual_bounds_s35 hx0 hx s hside
    have hbase := ScalarTransfer.Y_le_base (k := Certificates.k (1-x)) (x := x) (w := w) (P_nonneg_s35 x) s
    have hn := proxy_N hx0 hx s
    have hb := actualB_nonneg hx0 hw0 s
    have hcommon : ScalarTransfer.Y (P x) (Certificates.k (1-x)) x s ≤
        C (P x) s-k (P x) s+(8/5)*(P x*w^2)-actualB x w s := by
      dsimp only [ScalarTransfer.stdB, actualB] at hbase ⊢
      nlinarith only [hbase, hn]
    refine ⟨hy.2.trans hcommon, ?_⟩
    intro q hq0 hq
    have hgap := centering_gap_nonneg (P_nonneg_s35 x) (P_le_half_s35 hx0) hq s
    have hbq := mul_le_of_le_one_right hb hq
    linarith [hy.1.trans hcommon]
  · have hs : s = false := by cases s <;> simp_all
    subst s
    have hX : 1-x ≤ 1/2 := by by_contra h; exact hside (Or.inr (by linarith))
    have hy := Certificates.Yprime_actual_bounds_s35 hx0 hx hX
    have hbase := ScalarTransfer.Yprime_le_base (k := Certificates.k (1-x)) (w := w) (P_nonneg_s35 x) hw hX
    have hk := Certificates.k_envelope_s35 hx0 hx
    have hcommon : ScalarTransfer.Yprime (P x) (Certificates.k (1-x)) x ≤
        1-Certificates.k (1-x)+(8/5)*(P x*w^2)-actualB x w false := by
      simpa only [actualB, ScalarTransfer.stdB, mul_assoc] using hbase
    constructor
    · norm_num [C, k]
      linarith [hy.2.trans hcommon]
    · intro q hq0 hq
      have hp : P x ≤ actualB x w false := by
        have hp0 := P_nonneg_s35 x
        have hxw : 1 ≤ 2*(x+w) := by linarith
        have hn := mul_le_mul_of_nonneg_left hxw hp0
        norm_num [actualB, ScalarTransfer.bit]
        nlinarith only [hn]
      have hab := kappa_absorb (P_nonneg_s35 x) (actual_P_small hx0 hx hX) hp hq0 hq
      norm_num [C, k]
      nlinarith only [hy.1, hcommon, hk, hab]

private theorem actual_charge_proxy {x w r : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1)
    (hw0 : 0 ≤ w) (hw : w ≤ 1-x) (hr0 : 0 ≤ r) (hr : r ≤ 1) (s : Bool) :
    0 ≤ ChargeTransfer.charge (P x) (A x) (Certificates.k (1-x))
      (Certificates.H s (1-x)) x w r s := by
  have hX0 := sub_nonneg.mpr hx
  have hX : 1-x ≤ 1 := by linarith
  have hp0 : 0 ≤ Certificates.p (1-x) := by linarith [Certificates.p_lower hX0 hX]
  have hp1 : Certificates.p (1-x) ≤ 1/2 := by linarith [Certificates.p_upper hX0 hX]
  have ha0 := Certificates.v_lower hX0 hX
  have ha1 : Certificates.v (1-x) ≤ 2 := by linarith [Certificates.v_upper hX0 hX]
  have hk0 : 0 ≤ Certificates.k (1-x) := by linarith [Certificates.k_lower hX0 hX]
  have hk1 : Certificates.k (1-x) ≤ 1/5 := by linarith [Certificates.k_upper hX0 hX]
  have hH0 : 0 ≤ Certificates.H s (1-x) := by
    have hh := Certificates.h_lower_s35 hX0 hX
    cases s <;> norm_num [Certificates.H]; linarith
  have hH1 : Certificates.H s (1-x) ≤ 2/5 := by
    have hh := Certificates.h_upper_s35 hX0 hX
    cases s <;> norm_num [Certificates.H]; linarith
  have he := ChargeTransfer.charge_error_s35 hp0 hp1 (P_nonneg_s35 x) (P_le_half_s35 hx0)
    ha0 ha1 (one_le_A hx0) (A_le_two hx) hk0 hk1 hH0 hH1 hx0 hw0
    (show x+w ≤ 1 by linarith) hr0 hr (Certificates.p_approximation_s35 hx0 hx)
    (show |Certificates.v (1-x)-A x| ≤ 2*(3/400000) by
      convert Certificates.a_approximation_s35 hx0 hx using 1; norm_num) s
  have hm := Certificates.polynomial_charge_margin_s35 hX0 hX hw0 hw hr0 hr s
  simp only [sub_sub_cancel] at hm
  have hρ : 0 ≤ r+w^2 := add_nonneg hr0 (sq_nonneg w)
  have he' := (abs_le.mp he).2
  nlinarith only [hm, he', hρ]

private theorem actual_charge {x w r : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1)
    (hw0 : 0 ≤ w) (hw : w ≤ 1-x) (hr0 : 0 ≤ r) (hr : r ≤ 1) (s : Bool) :
    0 ≤ ((C (P x) s*H (Certificates.h (1-x)) s-actualB x w s)*r+(8/5)*(P x*w^2))*
      M (P x) (A x+2*P x*w) s r+
      (C (P x) s-k (P x) s-C (P x) s*H (Certificates.h (1-x)) s*r)*
        L (P x) (m x) (P x*w^2) (actualB x w) s r := by
  have hc := actual_charge_proxy hx0 hx hw0 hw hr0 hr s
  have hl := actual_L hx0 hx hw0 hw s hr0 hr
  have hcoef : 0 ≤ (1-ScalarTransfer.bit s)*Certificates.k (1-x)-k (P x) s := by
    have hk := Certificates.k_envelope_s35 hx0 hx
    cases s <;> norm_num [ScalarTransfer.bit, k]; linarith
  have hmul := mul_nonneg hcoef hl
  have hid :
      ((C (P x) s*H (Certificates.h (1-x)) s-actualB x w s)*r+(8/5)*(P x*w^2))*
        M (P x) (A x+2*P x*w) s r+
        (C (P x) s-k (P x) s-C (P x) s*H (Certificates.h (1-x)) s*r)*
          L (P x) (m x) (P x*w^2) (actualB x w) s r =
      ChargeTransfer.charge (P x) (A x) (Certificates.k (1-x)) (Certificates.H s (1-x)) x w r s+
        ((1-ScalarTransfer.bit s)*Certificates.k (1-x)-k (P x) s)*
          L (P x) (m x) (P x*w^2) (actualB x w) s r := by
    cases s <;> norm_num [ChargeTransfer.charge, ChargeTransfer.F1, ChargeTransfer.F2,
      ChargeTransfer.F3, ChargeTransfer.F4, ChargeTransfer.c, ChargeTransfer.bit,
      C, H, k, M, L, m, actualB, ScalarTransfer.bit, Certificates.H] <;> ring
  rw [hid]
  exact add_nonneg hc hmul

theorem actual_scalar_bounds_s35_oai {x w : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1)
    (hw0 : 0 ≤ w) (hw : w ≤ 1-x) :
    ScalarBounds (P x) (m x) (A x+2*P x*w) (P x*w^2) (Certificates.h (1-x)) (actualB x w) := by
  have hX0 := sub_nonneg.mpr hx
  have hX : 1-x ≤ 1 := by linarith
  refine ⟨P_nonneg_s35 x, P_le_half_s35 hx0, m_nonneg_s35 x, ?_, ?_, ?_,
    actualB_nonneg hx0 hw0, ?_, ?_, ?_, ?_, ?_⟩
  · exact mul_nonneg (P_nonneg_s35 x) (sq_nonneg w)
  · linarith [Certificates.h_lower_s35 hX0 hX]
  · linarith [Certificates.h_upper_s35 hX0 hX]
  · intro s r hr0 hr
    exact actual_first hx0 hx hw0 hw s hr0 hr
  · intro s r hr0 hr
    refine ⟨actual_L hx0 hx hw0 hw s hr0 hr, ?_, actual_linear hx0 hx hw0 hw s hr0 hr⟩
    have hb := actualB_nonneg hx0 hw0 s
    have hq := (actual_final_bounds hx0 hx hw0 hw s).1
    have hbr := mul_le_of_le_one_right hb hr
    unfold K
    linarith only [hq, hbr]
  · intro s r hr0 hr
    exact actual_charge hx0 hx hw0 hw hr0 hr s
  · intro s q hq0 hq
    exact (actual_final_bounds hx0 hx hw0 hw s).2 q hq0 hq
  · intro s
    exact (actual_final_bounds hx0 hx hw0 hw s).1

end MetricKMedian.FiniteComparison

end
end

end OAI
end

theorem solution : type_of% @OAI.MetricKMedian.FiniteComparison.actual_scalar_bounds_s35_oai := @OAI.MetricKMedian.FiniteComparison.actual_scalar_bounds_s35_oai
