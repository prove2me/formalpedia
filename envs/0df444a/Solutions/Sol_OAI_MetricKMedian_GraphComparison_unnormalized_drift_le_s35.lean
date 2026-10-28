-- Prove2me | solution 1 for OAI.MetricKMedian.GraphComparison.unnormalized_drift_le_s35
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T11:09:48.906503+00:00
-- url     : https://prove2.me/submissions/22cf0dc5-4b79-45cd-87b9-8dc8c95008dc

import Mathlib
import Definitions.Def_OAIQ035K021
import Definitions.Def_OAIQ035K029
import Theorems.Thm_OAI_MetricKMedian_Analytic_P_le_half_s35
import Theorems.Thm_OAI_MetricKMedian_Analytic_P_nonneg_s35
import Theorems.Thm_OAI_MetricKMedian_FiniteComparison_actual_scalar_bounds_s35

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

theorem psi_le_one {p q : ℝ} (hp : p ≤ 1 / 2) (hp0 : 0 ≤ p)
    (hq0 : 0 ≤ q) (hq : q ≤ 1) : psi p q ≤ 1 := by
  rw [psi, div_le_one (denominator_pos hp hp0 hq)]
  nlinarith [mul_nonneg (by linarith : 0 ≤ 1 - p) hq0]

theorem psi_affine_majorant {p q : ℝ} (hp : p ≤ 1 / 2) (hp0 : 0 ≤ p)
    (hq0 : 0 ≤ q) (hq : q ≤ 1) : psi p q ≤ 1 - q + p * q := by
  have h₁ := psi_le_one hp hp0 hq0 hq
  have hid : psi p q = 1 - q + p * q * psi p q := by
    have he : psi p q * (1 - p * q) = 1 - q :=
      div_mul_cancel₀ _ (ne_of_gt (denominator_pos hp hp0 hq))
    nlinarith only [he]
  have h₂ := mul_le_mul_of_nonneg_left h₁ (mul_nonneg hp0 hq0)
  rw [mul_one] at h₂
  linarith

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

theorem average_mono {I : Type*} [Fintype I] {π f h : I → ℝ}
    (hπ : ∀ i, 0 ≤ π i) (hfh : ∀ i, f i ≤ h i) : average π f ≤ average π h := by
  exact Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hfh i) (hπ i))

theorem average_nonneg {I : Type*} [Fintype I] {π f : I → ℝ}
    (hπ : ∀ i, 0 ≤ π i) (hf : ∀ i, 0 ≤ f i) : 0 ≤ average π f := by
  exact Finset.sum_nonneg (fun i _ => mul_nonneg (hπ i) (hf i))

theorem average_const {I : Type*} [Fintype I] {π : I → ℝ}
    (hπ : ∑ i, π i = 1) (c : ℝ) : average π (fun _ => c) = c := by
  simp only [average, ← Finset.sum_mul, hπ, one_mul]

theorem average_add {I : Type*} [Fintype I] (π f h : I → ℝ) :
    average π (fun i => f i + h i) = average π f + average π h := by
  simp only [average, mul_add, Finset.sum_add_distrib]

theorem average_sub {I : Type*} [Fintype I] (π f h : I → ℝ) :
    average π (fun i => f i - h i) = average π f - average π h := by
  simp only [average, mul_sub, Finset.sum_sub_distrib]

theorem average_mul {I : Type*} [Fintype I] (π f : I → ℝ) (c : ℝ) :
    average π (fun i => c * f i) = c * average π f := by
  simp only [average, ← Finset.mul_sum, mul_left_comm]

theorem average_mul_right {I : Type*} [Fintype I] (π f : I → ℝ) (c : ℝ) :
    average π (fun i => f i * c) = average π f * c := by
  simp only [average, Finset.sum_mul, mul_assoc]

theorem C_pos {p : ℝ} (hp : p ≤ 1 / 2) (s : Bool) : 0 < C p s := by
  cases s <;> simp only [C, Bool.false_eq_true, ↓reduceIte] <;> linarith

theorem C_le_one {p : ℝ} (hp : 0 ≤ p) (s : Bool) : C p s ≤ 1 := by
  cases s <;> simp only [C, Bool.false_eq_true, ↓reduceIte] <;> linarith

theorem centering_gap_nonneg {p q : ℝ} (hp0 : 0 ≤ p) (hp : p ≤ 1 / 2)
    (hq : q ≤ 1) (s : Bool) : 0 ≤ k p s - (C p s * psi p q - (1 - q)) := by
  cases s
  · have he := kappa_zero_le hp0 hp hq
    simpa only [kappa, mul_zero, sub_zero, one_mul, k, C, Bool.false_eq_true,
      ↓reduceIte] using sub_nonneg.mpr he
  · have he := kappa_one_le hp0 hp hq
    simpa only [kappa, mul_one, k, C, ↓reduceIte] using sub_nonneg.mpr he

theorem centered_le_linear {p m a z : ℝ} {b : Bool → ℝ}
    {s : Bool} {D q Z : ℝ} (hp0 : 0 ≤ p) (hp : p ≤ 1 / 2)
    (hD : 0 ≤ D) (hq0 : 0 ≤ q) (hq : q ≤ 1) (hZ : 0 ≤ Z) :
    centered p m a z b s D q Z ≤ D * G p m a z b s q - K p z b s q := by
  have hψ := psi_affine_majorant hp hp0 hq0 hq
  have hgap := centering_gap_nonneg hp0 hp hq s
  have h₁ := mul_le_mul_of_nonneg_left hψ (mul_nonneg hD (C_pos hp s).le)
  have h₂ := mul_nonneg hgap hZ
  unfold centered G M L K
  nlinarith only [h₁, h₂]

end MetricKMedian.FiniteComparison

namespace MetricKMedian.FiniteComparison

theorem affine_hinge_nonpos {a b H c D χ : ℝ}
    (hc : 0 < c) (hD : 0 ≤ D) (hDc : D ≤ c) (hH : 0 ≤ H) (hHc : H ≤ c)
    (hχ : 0 ≤ χ) (hzero : b + χ * H ≤ 0) (hcap : b + a * c ≤ 0) :
    b + a * D + χ * max (H - D) 0 ≤ 0 := by
  have hh : c * max (H - D) 0 ≤ (c - D) * H := by
    rcases le_total 0 (H - D) with h | h
    · rw [max_eq_left h]
      nlinarith [mul_nonneg hD (sub_nonneg.mpr hHc)]
    · rw [max_eq_right h, mul_zero]
      exact mul_nonneg (sub_nonneg.mpr hDc) hH
  have hhχ := mul_le_mul_of_nonneg_left hh hχ
  have h₀ := mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hDc) hzero
  have h₁ := mul_nonpos_of_nonneg_of_nonpos hD hcap
  have he : c * (b + a * D + χ * max (H - D) 0) ≤ 0 := by
    nlinarith only [hhχ, h₀, h₁]
  exact nonpos_of_mul_nonpos_right he hc

theorem average_exchange {I : Type*} [Fintype I] (π : I → ℝ) (Γ : I → I → ℝ) :
    average π (fun i => average π (Γ i)) =
      average π (fun i => average π (fun t => Γ t i)) := by
  unfold average
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  congr 1
  funext i
  congr 1
  funext t
  ring

theorem charge_cancellation {I : Type*} [Fintype I] (π F : I → ℝ)
    (Γ : I → I → ℝ) (receives : I → Prop)
    (hπ : ∀ i, 0 ≤ π i) (hΓ : ∀ i t, 0 ≤ Γ i t)
    (hout : ∀ i, 0 < F i → F i ≤ average π (Γ i))
    (hin : ∀ i, receives i → F i + average π (fun t => Γ t i) ≤ 0)
    (hsupport : ∀ i t, ¬ receives t → Γ i t = 0) : average π F ≤ 0 := by
  have hpoint : ∀ i, F i ≤ average π (Γ i) - average π (fun t => Γ t i) := by
    intro i
    by_cases hi : receives i
    · have h₁ := hin i hi
      have h₂ := average_nonneg hπ (hΓ i)
      linarith
    · have hzero : average π (fun t => Γ t i) = 0 := by
        simp only [average, hsupport _ _ hi, mul_zero, Finset.sum_const_zero]
      rw [hzero, sub_zero]
      by_cases hF : 0 < F i
      · exact hout i hF
      · exact le_trans (le_of_not_gt hF) (average_nonneg hπ (hΓ i))
  calc
    average π F ≤ average π (fun i => average π (Γ i) -
      average π (fun t => Γ t i)) := average_mono hπ hpoint
    _ = 0 := by rw [average_sub, average_exchange, sub_self]

end MetricKMedian.FiniteComparison

namespace MetricKMedian.FiniteComparison

theorem taper_weighted_comparison {p q R D Z : ℝ}
    (hp0 : 0 ≤ p) (hp : p ≤ 1 / 2) (hq : q ≤ 1)
    (hcomp : q < 1 → R * (1 - p * q) ≤ D + Z) :
    (1 - q) * R ≤ psi p q * (D + Z) := by
  by_cases hq1 : q < 1
  · have he := mul_le_mul_of_nonneg_left (hcomp hq1) (sub_nonneg.mpr hq)
    unfold psi
    rw [div_mul_eq_mul_div, le_div_iff₀ (denominator_pos hp hp0 hq)]
    nlinarith only [he]
  · have : q = 1 := le_antisymm hq (le_of_not_gt hq1)
    simp only [this, sub_self, zero_mul, psi, zero_div]
    exact le_rfl

theorem row_as_average {I : Type*} [Fintype I] {π : I → ℝ}
    (hπ : ∑ i, π i = 1) (Z q : I → ℝ)
    (p m a z : ℝ) (b : Bool → ℝ) (s : Bool) (D R : ℝ) :
    rowValue π Z q p m a z b s D R = average π (fun t =>
      C p s * ((1 - q t) * R) + (m * D + b s * (D + 1)) * q t -
      C p s * (D + 1) - (1 - q t) * max (Z t - a * D) 0 -
      ((2 / 5) * D + 8 / 5) * z) := by
  simp only [rowValue, average_add, average_sub, average_mul, average_mul_right,
    average_const hπ]
  ring

theorem row_le_centered {I : Type*} [Fintype I] {π Z q : I → ℝ}
    {p m a z : ℝ} {b : Bool → ℝ} {s : Bool} {D R : ℝ}
    (hπ0 : ∀ t, 0 ≤ π t) (hπ : ∑ t, π t = 1) (hZ : average π Z = 1)
    (hp0 : 0 ≤ p) (hp : p ≤ 1 / 2) (hq : ∀ t, q t ≤ 1)
    (hcomp : ∀ t, q t < 1 → R * (1 - p * q t) ≤ D + Z t) :
    rowValue π Z q p m a z b s D R ≤
      average π (fun t => centered p m a z b s D (q t) (Z t)) := by
  have hpoint : ∀ t,
      C p s * ((1 - q t) * R) + (m * D + b s * (D + 1)) * q t -
      C p s * (D + 1) - (1 - q t) * max (Z t - a * D) 0 -
      ((2 / 5) * D + 8 / 5) * z ≤
        centered p m a z b s D (q t) (Z t) + k p s * (Z t - 1) := by
    intro t
    have h₁ := mul_le_mul_of_nonneg_left
      (taper_weighted_comparison hp0 hp (hq t) (hcomp t)) (C_pos hp s).le
    have h₂ := mul_le_mul_of_nonneg_left (le_max_left (Z t - a * D) (0 : ℝ))
      (sub_nonneg.mpr (hq t))
    unfold centered
    nlinarith only [h₁, h₂]
  rw [row_as_average hπ]
  refine (average_mono hπ0 hpoint).trans_eq ?_
  rw [average_add, average_mul, average_sub, average_const hπ, hZ]
  ring

theorem average_linear {I : Type*} [Fintype I] {π : I → ℝ}
    (hπ : ∑ t, π t = 1) (q : I → ℝ)
    (p m a z : ℝ) (b : Bool → ℝ) (s : Bool) (D : ℝ) :
    average π (fun t => D * G p m a z b s (q t) - K p z b s (q t)) =
      D * G p m a z b s (average π q) - K p z b s (average π q) := by
  simp only [G, M, L, K, average_add, average_sub, average_mul, average_mul_right,
    average_const hπ]

theorem row_le_linear {I : Type*} [Fintype I] {π Z q : I → ℝ}
    {p m a z : ℝ} {b : Bool → ℝ} {s : Bool} {D R : ℝ}
    (hπ0 : ∀ t, 0 ≤ π t) (hπ : ∑ t, π t = 1) (hZ : average π Z = 1)
    (hp0 : 0 ≤ p) (hp : p ≤ 1 / 2) (hD : 0 ≤ D) (hZ0 : ∀ t, 0 ≤ Z t)
    (hq0 : ∀ t, 0 ≤ q t) (hq : ∀ t, q t ≤ 1)
    (hcomp : ∀ t, q t < 1 → R * (1 - p * q t) ≤ D + Z t) :
    rowValue π Z q p m a z b s D R ≤
      D * G p m a z b s (average π q) - K p z b s (average π q) := by
  refine (row_le_centered hπ0 hπ hZ hp0 hp hq hcomp).trans ?_
  rw [← average_linear hπ]
  exact average_mono hπ0 (fun t => centered_le_linear hp0 hp hD (hq0 t) (hq t) (hZ0 t))

theorem rate_comparison {I : Type*} [Fintype I] {π Z q : I → ℝ} {p D R : ℝ}
    (hπ0 : ∀ t, 0 ≤ π t) (hπ : ∑ t, π t = 1) (hZ : average π Z = 1)
    (hp0 : 0 ≤ p) (hp : p ≤ 1 / 2) (hD : 0 ≤ D) (hZ0 : ∀ t, 0 ≤ Z t)
    (hq0 : ∀ t, 0 ≤ q t) (hq : ∀ t, q t ≤ 1)
    (hcomp : ∀ t, q t < 1 → R * (1 - p * q t) ≤ D + Z t) :
    (1 - average π q) * R ≤ D + 1 := by
  have hpoint : ∀ t, (1 - q t) * R ≤ D + Z t := by
    intro t
    refine (taper_weighted_comparison hp0 hp (hq t) (hcomp t)).trans ?_
    have h := mul_le_mul_of_nonneg_right (psi_le_one hp hp0 (hq0 t) (hq t))
      (add_nonneg hD (hZ0 t))
    simpa only [one_mul] using h
  have he := average_mono hπ0 hpoint
  simpa only [average_add, average_sub, average_mul_right, average_const hπ, hZ] using he

theorem average_unit_bounds {I : Type*} [Fintype I] {π q : I → ℝ}
    (hπ0 : ∀ t, 0 ≤ π t) (hπ : ∑ t, π t = 1)
    (hq0 : ∀ t, 0 ≤ q t) (hq : ∀ t, q t ≤ 1) :
    0 ≤ average π q ∧ average π q ≤ 1 := by
  refine ⟨average_nonneg hπ0 hq0, ?_⟩
  exact (average_mono hπ0 hq).trans_eq (average_const hπ 1)

end MetricKMedian.FiniteComparison


end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Analysis_RowComparison
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.FiniteComparison

theorem positive_row_location {I : Type*} [Fintype I] {π Z q : I → ℝ}
    {p m a z h : ℝ} {b : Bool → ℝ} {s : Bool} {D R : ℝ}
    (sb : ScalarBounds p m a z h b)
    (hπ0 : ∀ t, 0 ≤ π t) (hπ : ∑ t, π t = 1) (hZ : average π Z = 1)
    (hD : 0 ≤ D) (hZ0 : ∀ t, 0 ≤ Z t)
    (hq0 : ∀ t, 0 ≤ q t) (hq : ∀ t, q t ≤ 1)
    (hcomp : ∀ t, q t < 1 → R * (1 - p * q t) ≤ D + Z t)
    (hF : 0 < rowValue π Z q p m a z b s D R) :
    0 < average π q ∧ 0 < G p m a z b s (average π q) ∧ d s < D := by
  have hr := average_unit_bounds hπ0 hπ hq0 hq
  have hrpos : 0 < average π q := by
    by_contra! hn
    have he : average π q = 0 := le_antisymm hn hr.1
    have hrate := rate_comparison hπ0 hπ hZ sb.p_nonneg sb.p_le_half hD hZ0 hq0 hq hcomp
    rw [he, sub_zero, one_mul] at hrate
    have h₁ := mul_le_mul_of_nonneg_left hrate (C_pos sb.p_le_half s).le
    have h₂ : 0 ≤ average π (fun t => (1 - q t) * max (Z t - a * D) 0) :=
      average_nonneg hπ0 (fun t => mul_nonneg (sub_nonneg.mpr (hq t)) (le_max_right _ _))
    have h₃ := mul_nonneg (show 0 ≤ (2 / 5 : ℝ) * D + 8 / 5 by linarith)
      sb.z_nonneg
    unfold rowValue at hF
    rw [he] at hF
    nlinarith only [hF, h₁, h₂, h₃]
  have hlin := sb.linear s (average π q) hr.1 hr.2
  have hmaj := row_le_linear (m := m) (a := a) (z := z) (b := b) (s := s)
    hπ0 hπ hZ sb.p_nonneg sb.p_le_half hD hZ0 hq0 hq hcomp
  have hKG : K p z b s (average π q) < D * G p m a z b s (average π q) := by
    linarith
  have hG : 0 < G p m a z b s (average π q) := by
    by_contra! hn
    have ht := mul_nonpos_of_nonneg_of_nonpos hD hn
    linarith [hlin.2.1]
  refine ⟨hrpos, hG, ?_⟩
  have ht := hlin.2.2.trans_lt hKG
  nlinarith only [ht, hG]

theorem d_lower (s : Bool) : (2 / 5 : ℝ) ≤ d s := by cases s <;> norm_num [d]

theorem H_bounds {p m a z h : ℝ} {b : Bool → ℝ}
    (sb : ScalarBounds p m a z h b) (s : Bool) : 0 ≤ H h s ∧ H h s ≤ 197 / 500 := by
  cases s
  · exact ⟨sb.h_nonneg, sb.h_le⟩
  · norm_num [H]

theorem small_linear_nonpos {p m a z h : ℝ} {b : Bool → ℝ}
    (sb : ScalarBounds p m a z h b) (s : Bool) {D q : ℝ}
    (hD : 0 ≤ D) (hDd : D ≤ d s) (hq0 : 0 ≤ q) (hq : q ≤ 1) :
    D * G p m a z b s q - K p z b s q ≤ 0 := by
  have hlin := sb.linear s q hq0 hq
  by_cases he : 0 ≤ G p m a z b s q
  · have ht := mul_le_mul_of_nonneg_right hDd he
    linarith [hlin.2.2]
  · have ht := mul_nonpos_of_nonneg_of_nonpos hD (le_of_not_ge he)
    linarith [hlin.2.1]

theorem centered_affine (p m a z : ℝ) (b : Bool → ℝ) (s : Bool) (D q Z : ℝ) :
    centered p m a z b s D q Z = centered p m a z b s 0 q Z +
      ((m + b s) * q + C p s * psi p q + a * (1 - q) - C p s - (2 / 5) * z) * D := by
  unfold centered
  ring

theorem incoming_pointwise {p m a z h : ℝ} {b : Bool → ℝ}
    (sb : ScalarBounds p m a z h b) (s st : Bool) {D q Z : ℝ}
    (hD : 0 ≤ D) (hDc : D ≤ 197 / 500) (hq0 : 0 ≤ q) (hq : q ≤ 1)
    (hZ : 0 ≤ Z) (positive : Prop) [Decidable positive]
    (hloc : positive → d st < Z) :
    centered p m a z b s D q Z + (if positive then max (H h st - D) 0 else 0) ≤ 0 := by
  have hgap := centering_gap_nonneg sb.p_nonneg sb.p_le_half hq s
  have hgapZ := mul_nonneg hgap hZ
  have hbq := mul_le_mul_of_nonneg_left hq (sb.b_nonneg s)
  have hbase : centered p m a z b s 0 q Z ≤ -(1 / 4) := by
    have ht := sb.type_one s
    unfold centered
    nlinarith only [hgapZ, hbq, ht]
  have hcap : centered p m a z b s (197 / 500) q Z ≤ 0 := by
    refine (centered_le_linear sb.p_nonneg sb.p_le_half (by norm_num) hq0 hq hZ).trans ?_
    apply small_linear_nonpos sb s (by norm_num) _ hq0 hq
    exact le_trans (by norm_num) (d_lower s)
  have hH := H_bounds sb st
  by_cases hpos : positive
  · simp only [hpos, ↓reduceIte]
    have hzero : centered p m a z b s 0 q Z + H h st ≤ 0 := by
      cases st
      · have ht := sb.type_zero s q hq0 hq
        have hdist : (13 / 25 : ℝ) ≤ Z := (hloc hpos).le
        have hz := mul_le_mul_of_nonneg_left hdist hgap
        change centered p m a z b s 0 q Z + h ≤ 0
        unfold centered
        nlinarith only [ht, hz]
      · change centered p m a z b s 0 q Z + 1 / 4 ≤ 0
        linarith
    rw [centered_affine] at hcap ⊢
    convert affine_hinge_nonpos (by norm_num : (0 : ℝ) < 197 / 500)
      hD hDc hH.1 hH.2 (by norm_num : (0 : ℝ) ≤ 1) (by simpa using hzero) hcap using 1
    all_goals try with_reducible_and_instances rfl
    ring
  · simp only [hpos, ↓reduceIte, add_zero]
    rw [centered_affine] at hcap ⊢
    have he := affine_hinge_nonpos (by norm_num : (0 : ℝ) < 197 / 500)
      hD hDc hH.1 hH.2 (by norm_num : (0 : ℝ) ≤ 0)
      (show centered p m a z b s 0 q Z + 0 * H h st ≤ 0 by linarith) hcap
    simpa only [zero_mul, add_zero] using he

end MetricKMedian.FiniteComparison

namespace MetricKMedian.FiniteComparison

theorem uprime_mul {p m z : ℝ} {b : Bool → ℝ} {s : Bool} {D r : ℝ}
    (hC : 0 < C p s) (hr : 0 < r) :
    uprime p m z b s D r * (C p s * r) =
      (m * D + b s * (D + 1)) * r - ((2 / 5) * D + 8 / 5) * z := by
  exact div_mul_cancel₀ _ (mul_ne_zero (ne_of_gt hC) (ne_of_gt hr))

theorem uprime_decompose {p m z : ℝ} {b : Bool → ℝ} {s : Bool} {D r : ℝ}
    (hC : 0 < C p s) (hr : 0 < r) :
    uprime p m z b s D r =
      (D + 1) / C p s * (m + b s - (2 / 5) * z / r) -
        m / C p s - (6 / 5) * z / (C p s * r) := by
  unfold uprime
  field_simp
  nlinarith [hC, hr]

theorem uprime_first {p m a z h : ℝ} {b : Bool → ℝ}
    (sb : ScalarBounds p m a z h b) (s : Bool) {D r : ℝ}
    (hD : 0 ≤ D) (hr : 0 < r) (hr1 : r ≤ 1) :
    uprime p m z b s D r ≤ (D + 1) * (1 - p) / (1 - p * r) := by
  have hC := C_pos sb.p_le_half s
  have hden := denominator_pos sb.p_le_half sb.p_nonneg hr1
  have h₁ := mul_le_mul_of_nonneg_left (sb.first s r hr hr1)
    (div_nonneg (by linarith : 0 ≤ D + 1) hC.le)
  have h₂ := div_nonneg sb.m_nonneg hC.le
  have h₃ := div_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 6 / 5) sb.z_nonneg)
    (mul_pos hC hr).le
  have hid : (D + 1) / C p s * (C p s * (1 - p) / (1 - p * r)) =
      (D + 1) * (1 - p) / (1 - p * r) := by
    field_simp
  rw [uprime_decompose hC hr]
  rw [hid] at h₁
  linarith

end MetricKMedian.FiniteComparison

namespace MetricKMedian.FiniteComparison

theorem row_le_uprime {I : Type*} [Fintype I] {π Z q : I → ℝ}
    {p m a z : ℝ} {b : Bool → ℝ} {s : Bool} {D R : ℝ}
    (hπ0 : ∀ t, 0 ≤ π t) (hq : ∀ t, q t ≤ 1)
    (hC : 0 < C p s) (hr : 0 < average π q) :
    rowValue π Z q p m a z b s D R ≤ C p s *
      ((1 - average π q) * R + average π q * uprime p m z b s D (average π q) -
        (D + 1)) := by
  have he := uprime_mul (m := m) (z := z) (b := b) (D := D) hC hr
  have hnonneg := average_nonneg hπ0
    (fun t => mul_nonneg (sub_nonneg.mpr (hq t)) (le_max_right (Z t - a * D) 0))
  unfold rowValue
  nlinarith only [he, hnonneg]

theorem positive_uprime_le_radius {I : Type*} [Fintype I] {π Z q : I → ℝ}
    {p m a z h : ℝ} {b : Bool → ℝ} {s : Bool} {D R : ℝ}
    (sb : ScalarBounds p m a z h b)
    (hπ0 : ∀ t, 0 ≤ π t) (hπ : ∑ t, π t = 1)
    (hD : 0 ≤ D) (hq0 : ∀ t, 0 ≤ q t) (hq : ∀ t, q t ≤ 1)
    (hr : 0 < average π q) (hF : 0 < rowValue π Z q p m a z b s D R) :
    uprime p m z b s D (average π q) ≤ R * (1 - p) := by
  have hr1 := (average_unit_bounds hπ0 hπ hq0 hq).2
  have hden := denominator_pos sb.p_le_half sb.p_nonneg hr1
  have hC := C_pos sb.p_le_half s
  have hrow := row_le_uprime (Z := Z) hπ0 hq hC hr (m := m) (a := a) (z := z) (b := b) (D := D) (R := R)
  have hpos : 0 < (1 - average π q) * R +
      average π q * uprime p m z b s D (average π q) - (D + 1) := by
    by_contra! hn
    have ht := mul_nonpos_of_nonneg_of_nonpos hC.le hn
    linarith
  have hu := uprime_first sb s hD hr hr1
  have hu' := (le_div_iff₀ hden).mp hu
  have hR : (D + 1) / (1 - p * average π q) < R := by
    by_contra! hn
    have hn' := (le_div_iff₀ hden).mp hn
    have ht₁ := mul_le_mul_of_nonneg_left hn' (sub_nonneg.mpr hr1)
    have ht₂ := mul_le_mul_of_nonneg_left hu' hr.le
    have ht₃ := mul_pos hpos hden
    nlinarith only [ht₁, ht₂, ht₃]
  have ht := mul_le_mul_of_nonneg_right hR.le
    (show 0 ≤ 1 - p by linarith [sb.p_le_half])
  exact hu.trans (by simpa only [div_mul_eq_mul_div] using ht)

theorem row_le_excess {I : Type*} [Fintype I] {π Z q : I → ℝ}
    {p m a z : ℝ} {b : Bool → ℝ} {s : Bool} {D R : ℝ}
    (hπ0 : ∀ t, 0 ≤ π t) (hπ : ∑ t, π t = 1) (hZ : average π Z = 1)
    (hC : 0 < C p s) (hr : 0 < average π q)
    (hq0 : ∀ t, 0 ≤ q t) (hq : ∀ t, q t ≤ 1)
    (hcomp : ∀ t, q t < 1 → R * (1 - p * q t) ≤ D + Z t)
    (hu : uprime p m z b s D (average π q) ≤ R * (1 - p)) :
    rowValue π Z q p m a z b s D R ≤ C p s *
      average π (fun t => max (uprime p m z b s D (average π q) - D - Z t) 0) := by
  have hpoint : ∀ t, (1 - q t) * R + q t * uprime p m z b s D (average π q) -
      D - Z t ≤ max (uprime p m z b s D (average π q) - D - Z t) 0 := by
    intro t
    by_cases hqt : q t < 1
    · have ht₁ := mul_le_mul_of_nonneg_left hu (hq0 t)
      have ht₂ := hcomp t hqt
      have ht₃ := le_max_right (uprime p m z b s D (average π q) - D - Z t) 0
      nlinarith only [ht₁, ht₂, ht₃]
    · have he : q t = 1 := le_antisymm (hq t) (le_of_not_gt hqt)
      simpa only [he, sub_self, zero_mul, one_mul, zero_add] using
        le_max_left (uprime p m z b s D (average π q) - D - Z t) 0
  refine (row_le_uprime hπ0 hq hC hr).trans ?_
  apply mul_le_mul_of_nonneg_left _ hC.le
  have ht := average_mono hπ0 hpoint
  simpa only [average_add, average_sub, average_mul_right, average_const hπ, hZ,
    sub_sub] using ht

theorem uprime_charge_bound {p m a z h : ℝ} {b : Bool → ℝ}
    (sb : ScalarBounds p m a z h b) (s : Bool) {D r : ℝ}
    (hr : 0 < r) (hr1 : r ≤ 1) (hG : 0 < G p m a z b s r)
    (hKG : K p z b s r ≤ D * G p m a z b s r) :
    uprime p m z b s D r - D ≤ H h s := by
  let T := (C p s * H h s - b s) * r + (8 / 5) * z
  have hcharge : 0 ≤ T * G p m a z b s r + K p z b s r * L p m z b s r := by
    convert sb.charge s r hr.le hr1 using 1
    all_goals try with_reducible_and_instances rfl
    unfold T G K M L
    ring
  have hL := (sb.linear s r hr.le hr1).1
  have ht := mul_le_mul_of_nonneg_right hKG hL
  have hTG : 0 ≤ (T + L p m z b s r * D) * G p m a z b s r := by
    nlinarith only [hcharge, ht]
  have hT : 0 ≤ T + L p m z b s r * D := nonneg_of_mul_nonneg_left hTG hG
  have hC := C_pos sb.p_le_half s
  have he := uprime_mul (D := D) (m := m) (z := z) (b := b) hC hr
  have hCr := mul_pos hC hr
  have he' : (uprime p m z b s D r - D - H h s) * (C p s * r) =
      -(T + L p m z b s r * D) := by
    unfold T L
    nlinarith only [he]
  have hnonpos : (uprime p m z b s D r - D - H h s) * (C p s * r) ≤ 0 := by
    rw [he']
    exact neg_nonpos.mpr hT
  have := nonpos_of_mul_nonpos_left hnonpos hCr
  linarith

end MetricKMedian.FiniteComparison

namespace MetricKMedian.FiniteComparison

theorem finite_charge {I : Type*} [Fintype I] {π D R : I → ℝ}
    {q : I → I → ℝ} {s : I → Bool} {p m a z h : ℝ} {b : Bool → ℝ}
    (sb : ScalarBounds p m a z h b)
    (hπ0 : ∀ i, 0 ≤ π i) (hπ : ∑ i, π i = 1)
    (hD0 : ∀ i, 0 ≤ D i) (hD : average π D = 1)
    (hq0 : ∀ i t, 0 ≤ q i t) (hq : ∀ i t, q i t ≤ 1)
    (hcomp : ∀ i t, q i t < 1 → R i * (1 - p * q i t) ≤ D i + D t) :
    average π (fun i => rowValue π D (q i) p m a z b (s i) (D i) (R i)) ≤ 0 := by
  classical
  let F : I → ℝ := fun i => rowValue π D (q i) p m a z b (s i) (D i) (R i)
  let Γ : I → I → ℝ := fun i t => if 0 < F i then max (H h (s i) - D t) 0 else 0
  have hloc : ∀ i, 0 < F i →
      0 < average π (q i) ∧ 0 < G p m a z b (s i) (average π (q i)) ∧ d (s i) < D i := by
    intro i hi
    exact positive_row_location sb hπ0 hπ hD (hD0 i) hD0 (hq0 i) (hq i) (hcomp i) hi
  have hout : ∀ i, 0 < F i → F i ≤ average π (Γ i) := by
    intro i hi
    have hli := hloc i hi
    have hr1 := (average_unit_bounds hπ0 hπ (hq0 i) (hq i)).2
    have hlin := row_le_linear (m := m) (a := a) (z := z) (b := b) (s := s i)
      hπ0 hπ hD sb.p_nonneg sb.p_le_half (hD0 i) hD0 (hq0 i) (hq i) (hcomp i)
    have hKG : K p z b (s i) (average π (q i)) ≤
        D i * G p m a z b (s i) (average π (q i)) := by
      change 0 < rowValue π D (q i) p m a z b (s i) (D i) (R i) at hi
      linarith
    have hheight := uprime_charge_bound sb (s i) hli.1 hr1 hli.2.1 hKG
    have hu := positive_uprime_le_radius sb hπ0 hπ (hD0 i) (hq0 i) (hq i) hli.1 hi
    have hexcess := row_le_excess hπ0 hπ hD (C_pos sb.p_le_half (s i)) hli.1
      (hq0 i) (hq i) (hcomp i) hu (a := a)
    have hpoint : ∀ t, max (uprime p m z b (s i) (D i) (average π (q i)) - D i - D t) 0 ≤
        max (H h (s i) - D t) 0 := by
      intro t
      exact max_le_max_right 0 (sub_le_sub_right hheight (D t))
    have h₁ := mul_le_mul_of_nonneg_left (average_mono hπ0 hpoint) (C_pos sb.p_le_half (s i)).le
    have hnonneg := average_nonneg hπ0 (fun t => le_max_right (H h (s i) - D t) 0)
    have h₂ := mul_le_mul_of_nonneg_right (C_le_one sb.p_nonneg (s i)) hnonneg
    change F i ≤ average π (fun t => if 0 < F i then max (H h (s i) - D t) 0 else 0)
    simp only [hi, ↓reduceIte]
    exact hexcess.trans (h₁.trans (by simpa only [one_mul] using h₂))
  have hin : ∀ i, D i ≤ 197 / 500 → F i + average π (fun t => Γ t i) ≤ 0 := by
    intro i hi
    have hrow := row_le_centered (m := m) (a := a) (z := z) (b := b) (s := s i)
      hπ0 hπ hD sb.p_nonneg sb.p_le_half (hq i) (hcomp i)
    have hpoint : ∀ t, centered p m a z b (s i) (D i) (q i t) (D t) + Γ t i ≤ 0 := by
      intro t
      exact incoming_pointwise sb (s i) (s t) (hD0 i) hi (hq0 i t) (hq i t) (hD0 t)
        (0 < F t) (fun ht => (hloc t ht).2.2)
    have hav := average_mono hπ0 hpoint
    rw [average_add, average_const hπ] at hav
    change F i ≤ _ at hrow
    linarith
  have hΓ : ∀ i t, 0 ≤ Γ i t := by
    intro i t
    dsimp only [Γ]
    split_ifs <;> positivity
  have hsupport : ∀ i t, ¬ D t ≤ 197 / 500 → Γ i t = 0 := by
    intro i t ht
    have hH := (H_bounds sb (s i)).2
    have he : H h (s i) - D t ≤ 0 := by linarith
    dsimp only [Γ]
    split_ifs
    · exact max_eq_right he
    · rfl
  exact charge_cancellation π F Γ (fun i => D i ≤ 197 / 500) hπ0 hΓ hout hin hsupport

end MetricKMedian.FiniteComparison

namespace MetricKMedian.FiniteComparison

theorem rawRow_affine {I : Type*} [Fintype I] (π Z q : I → ℝ)
    (p m y s D R : ℝ) : rawRow π Z q p m y s D R =
      (1 - s) * rawRow π Z q p m y 0 D R + s * rawRow π Z q p m y 1 D R := by
  unfold rawRow
  ring

theorem affine_le_max {u v s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    (1 - s) * u + s * v ≤ max u v := by
  have h₁ := mul_le_mul_of_nonneg_left (le_max_left u v) (sub_nonneg.mpr hs1)
  have h₂ := mul_le_mul_of_nonneg_left (le_max_right u v) hs0
  nlinarith only [h₁, h₂]

theorem rawRow_mono_y {I : Type*} [Fintype I] {π Z q : I → ℝ}
    {p m y y' s D R : ℝ} (hπ0 : ∀ t, 0 ≤ π t) (hp : 0 ≤ p)
    (hD : 0 ≤ D) (hq0 : ∀ t, 0 ≤ q t) (hq : ∀ t, q t ≤ 1)
    (hs : s ≤ 1) (hy : y ≤ y') : rawRow π Z q p m y s D R ≤ rawRow π Z q p m y' s D R := by
  have hr := average_nonneg hπ0 hq0
  have hlin := mul_le_mul_of_nonneg_left hy
    (mul_nonneg (mul_nonneg (mul_nonneg hr (by linarith : 0 ≤ 2 - s)) hp)
      (by linarith : 0 ≤ D + 1))
  have hhinge : average π (fun t => (1 - q t) * max (Z t - (1 + m + 2 * p * y') * D) 0) ≤
      average π (fun t => (1 - q t) * max (Z t - (1 + m + 2 * p * y) * D) 0) := by
    apply average_mono hπ0
    intro t
    apply mul_le_mul_of_nonneg_left _ (sub_nonneg.mpr (hq t))
    apply max_le_max_right
    have ht := mul_le_mul_of_nonneg_left hy (mul_nonneg (by positivity : 0 ≤ 2 * p) hD)
    nlinarith only [ht]
  unfold rawRow
  nlinarith only [hlin, hhinge]

theorem rawRow_eq_rowValue {I : Type*} [Fintype I] (π Z q : I → ℝ)
    (p m y z D R : ℝ) (s : Bool) :
    rawRow π Z q p m y (endpoint s) D R =
      rowValue π Z q p m (1 + m + 2 * p * y) z
        (fun s => (2 - endpoint s) * p * y) s D R + ((2 / 5) * D + 8 / 5) * z := by
  cases s <;> simp only [rawRow, rowValue, C, endpoint, Bool.false_eq_true, ↓reduceIte] <;> ring

theorem finite_raw_of_scalar {I : Type*} [Fintype I] {π D R : I → ℝ}
    {q : I → I → ℝ} {s : I → ℝ} {p m y z h : ℝ}
    (sb : ScalarBounds p m (1 + m + 2 * p * y) z h (fun s => (2 - endpoint s) * p * y))
    (hπ0 : ∀ i, 0 ≤ π i) (hπ : ∑ i, π i = 1)
    (hD0 : ∀ i, 0 ≤ D i) (hD : average π D = 1)
    (hq0 : ∀ i t, 0 ≤ q i t) (hq : ∀ i t, q i t ≤ 1)
    (hs0 : ∀ i, 0 ≤ s i) (hs : ∀ i, s i ≤ 1)
    (hcomp : ∀ i t, q i t < 1 → R i * (1 - p * q i t) ≤ D i + D t) :
    average π (fun i => rawRow π D (q i) p m y (s i) (D i) (R i)) ≤ 2 * z := by
  classical
  let v : I → Bool := fun i => decide
    (rawRow π D (q i) p m y 0 (D i) (R i) ≤ rawRow π D (q i) p m y 1 (D i) (R i))
  have hpoint : ∀ i, rawRow π D (q i) p m y (s i) (D i) (R i) ≤
      rawRow π D (q i) p m y (endpoint (v i)) (D i) (R i) := by
    intro i
    rw [rawRow_affine]
    have he := affine_le_max (u := rawRow π D (q i) p m y 0 (D i) (R i))
      (v := rawRow π D (q i) p m y 1 (D i) (R i)) (hs0 i) (hs i)
    by_cases hle : rawRow π D (q i) p m y 0 (D i) (R i) ≤ rawRow π D (q i) p m y 1 (D i) (R i)
    · simpa only [v, hle, decide_true, endpoint, ↓reduceIte, max_eq_right hle] using he
    · simpa only [v, hle, decide_false, endpoint, Bool.false_eq_true, ↓reduceIte,
        max_eq_left (le_of_not_ge hle)] using he
  have hcharge := finite_charge (s := v) sb hπ0 hπ hD0 hD hq0 hq hcomp
  have hav := average_mono hπ0 hpoint
  simp only [rawRow_eq_rowValue (z := z), average_add, average_mul_right,
    average_mul, average_const hπ, hD] at hav
  linarith

end MetricKMedian.FiniteComparison


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

theorem finite_comparison {I : Type*} [Fintype I] {π D R : I → ℝ}
    {q : I → I → ℝ} {s : I → ℝ} {x y : ℝ}
    (hx0 : 0 ≤ x) (hx : x ≤ 1) (hy0 : 0 < y) (hy : y ≤ 1)
    (hπ0 : ∀ i, 0 ≤ π i) (hπ : ∑ i, π i = 1)
    (hD0 : ∀ i, 0 ≤ D i) (hD : average π D = 1) (_hR0 : ∀ i, 0 ≤ R i)
    (hq0 : ∀ i t, 0 ≤ q i t) (hq : ∀ i t, q i t ≤ 1)
    (hs0 : ∀ i, 0 ≤ s i) (hs : ∀ i, s i ≤ 1)
    (hcomp : ∀ i t, q i t < 1 → R i*(1-P x*q i t) ≤ D i+D t) :
    average π (fun i => rawRow π D (q i) (P x) (m x) y (s i) (D i) (R i)) ≤
      2*(P x*(y-x)^2/y) := by
  let w := max 0 (y-x)
  have hw0 : 0 ≤ w := le_max_left _ _
  have hw : w ≤ 1-x := max_le (by linarith) (by linarith)
  have hyy : y ≤ x+w := by have h := le_max_right 0 (y-x); dsimp [w]; linarith
  have ha : A x+2*P x*w = 1+m x+2*P x*(x+w) := by unfold m; ring
  have hbs : actualB x w = fun s => (2-endpoint s)*P x*(x+w) := rfl
  have sb := actual_scalar_bounds_s35 hx0 hx hw0 hw
  rw [ha, hbs] at sb
  have hfinite := finite_raw_of_scalar sb hπ0 hπ hD0 hD hq0 hq hs0 hs hcomp
  have hmono : average π (fun i => rawRow π D (q i) (P x) (m x) y (s i) (D i) (R i)) ≤
      average π (fun i => rawRow π D (q i) (P x) (m x) (x+w) (s i) (D i) (R i)) := by
    apply average_mono hπ0
    intro i
    exact rawRow_mono_y hπ0 (P_nonneg_s35 x) (hD0 i) (hq0 i) (hq i) (hs i) hyy
  have hz : P x*w^2 ≤ P x*(y-x)^2/y := by
    rcases le_total y x with h | h
    · have hwz : w = 0 := max_eq_left (sub_nonpos.mpr h)
      rw [hwz]
      simp only [zero_pow (by decide : 2 ≠ 0), mul_zero]
      exact div_nonneg (mul_nonneg (P_nonneg_s35 x) (sq_nonneg _)) hy0.le
    · have hwe : w = y-x := max_eq_right (sub_nonneg.mpr h)
      rw [hwe]
      exact (le_div_iff₀ hy0).mpr
        (mul_le_of_le_one_right (mul_nonneg (P_nonneg_s35 x) (sq_nonneg _)) hy)
  exact hmono.trans (hfinite.trans (mul_le_mul_of_nonneg_left hz (by norm_num)))

end MetricKMedian.FiniteComparison

end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Geometry_GraphComparison
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.GraphComparison

open FiniteComparison Analytic

theorem kernel_average_bound {I : Type*} [Fintype I] {π D s r : I → ℝ} {K : I → I → ℝ} {y : ℝ}
    (hπ0 : ∀ i, 0 ≤ π i) (hπ : ∑ i, π i=1) (hD0 : ∀ i, 0 ≤ D i) (hD : average π D=1)
    (hK : ∀ i t, K i t ≤ (s i*(1-y*r i)+s t*(1-y*r t))/2) :
    2*average π (fun i => average π (fun t => K i t*D t)) ≤
      average π (fun i => s i*(1-y*r i)*(1+D i)) := by
  have hb := average_mono hπ0 (fun i => average_mono hπ0
    (fun t => mul_le_mul_of_nonneg_right (hK i t) (hD0 t)))
  have hid : average π (fun i => average π (fun t =>
      ((s i*(1-y*r i)+s t*(1-y*r t))/2)*D t)) =
      (1/2)*average π (fun i => s i*(1-y*r i)*(1+D i)) := by
    have hpoint : ∀ i t, ((s i*(1-y*r i)+s t*(1-y*r t))/2)*D t =
        (1/2)*(s i*(1-y*r i))*D t+(1/2)*(s t*(1-y*r t)*D t) := by intros; ring
    simp_rw [hpoint, average_add, average_mul, hD, mul_one, average_const hπ]
    rw [average_mul, ←mul_add, ←average_add]
    congr 2
    funext i
    ring
  rw [hid] at hb
  linarith only [hb]

theorem taper_error {p pHat ζ u : ℝ} (hp0 : 0 ≤ p) (hp : p ≤ 1/2)
    (hζ0 : 0 ≤ ζ) (he : |pHat-p| ≤ ζ) (hu0 : 0 ≤ u) (hu : u ≤ 1) :
    0 ≤ (1-pHat*u)-(1-2*ζ)*(1-p*u) ∧
      (1-pHat*u)-(1-2*ζ)*(1-p*u) ≤ 3*ζ := by
  have hehe := abs_le.mp he
  have huζ := mul_le_mul_of_nonneg_left hu hζ0
  have hupper := mul_le_mul_of_nonneg_right hehe.1 hu0
  have hlower := mul_le_mul_of_nonneg_right hehe.2 hu0
  have hpu := mul_le_mul hp hu hu0 (by norm_num : (0:ℝ) ≤ 1/2)
  have hpu0 := mul_nonneg hp0 hu0
  have hpuz := mul_le_mul_of_nonneg_left hpu hζ0
  have hpuz0 := mul_nonneg hζ0 hpu0
  constructor <;> nlinarith only [huζ, hupper, hlower, hpuz, hpuz0]

theorem radius_control {I : Type*} [Fintype I] {π D : I → ℝ} {q : I → I → ℝ}
    {N : I → ℝ} {pHat : ℝ}
    (hπ0 : ∀ i, 0 ≤ π i) (hπ : ∑ i, π i=1) (hD0 : ∀ i, 0 ≤ D i) (hD : average π D=1)
    (hN0 : ∀ i, 0 ≤ N i) (_hp0 : 0 ≤ pHat) (hp : pHat ≤ 1/2)
    (hq0 : ∀ i t, 0 ≤ q i t) (hq : ∀ i t, q i t ≤ 1)
    (hcomp : ∀ i t, q i t < 1 → N i*(1-pHat*q i t) ≤ D i+D t) (i : I) :
    (1-average π (q i))*N i ≤ 2*(D i+1) := by
  have hpoint : ∀ t, (1-q i t)*N i ≤ 2*(D i+D t) := by
    intro t
    rcases eq_or_lt_of_le (hq i t) with heq | hlt
    · rw [heq]
      have hpos := add_nonneg (hD0 i) (hD0 t)
      nlinarith
    · have hh := hcomp i t hlt
      have hpq := mul_le_mul hp (hq i t) (hq0 i t) (by norm_num : (0:ℝ) ≤ 1/2)
      have hden : 1/2 ≤ 1-pHat*q i t := by linarith
      have hmul := mul_le_mul_of_nonneg_left hden (hN0 i)
      have hcut := mul_nonneg (hq0 i t) (hN0 i)
      nlinarith only [hh, hmul, hcut]
  have hb := average_mono hπ0 hpoint
  simp only [average_mul_right, average_sub, average_mul, average_add, average_const hπ, hD] at hb
  exact hb

theorem normalized_drift_le {I : Type*} [Fintype I]
    {π D N s : I → ℝ} {q K : I → I → ℝ} {x y pHat ζ : ℝ}
    (hx0 : 0 ≤ x) (hx : x ≤ 1) (hy0 : 0 < y) (hy : y ≤ 1)
    (hπ0 : ∀ i, 0 ≤ π i) (hπ : ∑ i, π i=1)
    (hD0 : ∀ i, 0 ≤ D i) (hD : average π D=1) (hN : ∀ i, 0 ≤ N i)
    (hs0 : ∀ i, 0 ≤ s i) (hs : ∀ i, s i ≤ 1)
    (hq0 : ∀ i t, 0 ≤ q i t) (hq : ∀ i t, q i t ≤ 1)
    (hp0 : 0 ≤ pHat) (hp : pHat ≤ 1/2) (hζ0 : 0 ≤ ζ) (hζ : ζ < 1/4)
    (he : |pHat-P x| ≤ ζ)
    (hcomp : ∀ i t, q i t < 1 → N i*(1-pHat*q i t) ≤ D i+D t)
    (hK : ∀ i t, K i t ≤
      (s i*(1-y*average π (q i))+s t*(1-y*average π (q t)))/2) :
    normalizedDrift π D N s q K x y pHat ≤ 12*ζ := by
  let R : I → ℝ := fun i => (1-2*ζ)*N i
  let err : I → ℝ := fun i => (1-average π (q i))*N i*
    ((1-pHat*s i)-(1-2*ζ)*(1-P x*s i))
  have hpP := P_le_half_s35 hx0
  have hpP0 := P_nonneg_s35 x
  have hR : ∀ i, 0 ≤ R i := by
    intro i
    exact mul_nonneg (by linarith only [hζ]) (hN i)
  have hcompR : ∀ i t, q i t < 1 → R i*(1-P x*q i t) ≤ D i+D t := by
    intro i t hit
    have ht := (taper_error hpP0 hpP hζ0 he (hq0 i t) (hq i t)).1
    have hm := mul_le_mul_of_nonneg_right (sub_nonneg.mp ht) (hN i)
    dsimp only [R]
    nlinarith only [hm, hcomp i t hit]
  have hfinite := finite_comparison hx0 hx hy0 hy hπ0 hπ hD0 hD hR
    hq0 hq hs0 hs hcompR
  have herr : ∀ i, err i ≤ 6*ζ*(D i+1) := by
    intro i
    have hr : average π (q i) ≤ 1 := by
      have hr := average_mono hπ0 (hq i)
      simpa only [average_const hπ] using hr
    have hn : 0 ≤ (1-average π (q i))*N i :=
      mul_nonneg (sub_nonneg.mpr hr) (hN i)
    have ht := (taper_error hpP0 hpP hζ0 he (hs0 i) (hs i)).2
    have hrad := radius_control hπ0 hπ hD0 hD hN hp0 hp hq0 hq hcomp i
    have h1 := mul_le_mul_of_nonneg_left ht hn
    have h2 := mul_le_mul_of_nonneg_left hrad (mul_nonneg (by norm_num : (0:ℝ) ≤ 3) hζ0)
    dsimp only [err]
    nlinarith only [h1, h2]
  have herrAvg : average π err ≤ 12*ζ := by
    have hh := average_mono hπ0 herr
    simp only [average_mul, average_add, hD, average_const hπ] at hh
    nlinarith only [hh]
  have hker := mul_le_mul_of_nonneg_left (kernel_average_bound hπ0 hπ hD0 hD hK) hpP0
  have hid : normalizedDrift π D N s q K x y pHat =
      average π (fun i => rawRow π D (q i) (P x) (m x) y (s i) (D i) (R i)) +
      average π err -2*(P x*(y-x)^2/y)+
      P x*(2*average π (fun i => average π (fun t => K i t*D t))-
        average π (fun i => s i*(1-y*average π (q i))*(1+D i))) := by
    have hrow : ∀ i,
        (1-average π (q i))*(D i+(1-pHat*s i)*N i)+
        (1+m x+2*P x*y)*average π (q i)*D i+2*P x*y*average π (q i)-
        average π (fun t => (1-q i t)*max (D t-(1+m x+2*P x*y)*D i) 0) =
        rawRow π D (q i) (P x) (m x) y (s i) (D i) (R i)+err i+
        2*D i+1-P x*(s i*(1-y*average π (q i))*(1+D i)) := by
      intro i
      unfold rawRow
      dsimp only [R, err]
      ring
    unfold normalizedDrift
    have heq : ∀ i,
        (1-average π (q i))*(D i+(1-pHat*s i)*N i)+
        (1+m x+2*P x*y)*average π (q i)*D i+2*P x*y*average π (q i)+
        2*P x*average π (fun t => K i t*D t)-
        average π (fun t => (1-q i t)*max (D t-(1+m x+2*P x*y)*D i) 0) =
        (rawRow π D (q i) (P x) (m x) y (s i) (D i) (R i)+err i+
        2*D i+1-P x*(s i*(1-y*average π (q i))*(1+D i)))+
        2*P x*average π (fun t => K i t*D t) := by
      intro i
      have hh := hrow i
      linarith only [hh]
    simp only [heq, average_add, average_sub, average_mul, hD, average_const hπ]
    ring
  rw [hid]
  nlinarith only [hfinite, herrAvg, hker]

end MetricKMedian.GraphComparison
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Process_AveragedDrift
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.GraphComparison

open FiniteComparison Analytic

theorem normalization_identity {I : Type*} [Fintype I]
    (π D N s : I → ℝ) (q K : I → I → ℝ) (x pHat : ℝ) {y L : ℝ}
    (hy : y ≠ 0) (hL : 0 ≤ L) (hD : average π D=1) :
    unnormalizedDrift (fun i => y*π i) (fun i => L*D i) (fun i => L*N i) s q K x y pHat =
      (y^2*L)*normalizedDrift π D N s q K x y pHat := by
  have hV : (∑ i, (y*π i)*(L*D i))=y*L := by
    simp only [mul_mul_mul_comm y _ L _, ← Finset.mul_sum]
    change y*L*average π D=y*L
    rw [hD, mul_one]
  have hw : ∀ i, (∑ t, (y*π t)*q i t)=y*average π (q i) := by
    intro i
    simp only [average, Finset.mul_sum, mul_assoc]
  have hk : ∀ i, (∑ t, (y*π t)*K i t*(L*D t)) =
      y*L*average π (fun t => K i t*D t) := by
    intro i
    simp only [average, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro t _
    ring
  have hh : ∀ i, (∑ t, (y*π t)*(1-q i t)*max (L*D t-(1+m x+B x*y)*(L*D i)) 0) =
      y*L*average π (fun t => (1-q i t)*max (D t-(1+m x+B x*y)*D i) 0) := by
    intro i
    simp only [average, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro t _
    rw [show L*D t-(1+m x+B x*y)*(L*D i)=L*(D t-(1+m x+B x*y)*D i) by ring,
      ← mul_zero L, ← mul_max_of_nonneg _ _ hL]
    ring_nf
  unfold unnormalizedDrift normalizedDrift
  dsimp only
  rw [hV]
  simp_rw [hw, hk, hh]
  simp only [average]
  have hB : B x=2*P x := rfl
  rw [hB]
  have hconst : -(3*y+2*P x*(y-x)^2)*(y*L) =
      y^2*L*(-3-2*(P x*(y-x)^2/y)) := by field_simp [hy]; ring
  have hterms : (∑ i, y*π i*((y-y*∑ t, π t*q i t)*(L*D i+(1-pHat*s i)*(L*N i))+
      (1+m x+2*P x*y)*(y*∑ t, π t*q i t)*(L*D i)+
      2*P x*(y*L)*(y*∑ t, π t*q i t)+2*P x*(y*L*∑ t, π t*(K i t*D t))-
      y*L*∑ t, π t*((1-q i t)*max (D t-(1+m x+2*P x*y)*D i) 0))) =
      ∑ i, y^2*L*(π i*((1-∑ t, π t*q i t)*(D i+(1-pHat*s i)*N i)+
        (1+m x+2*P x*y)*(∑ t, π t*q i t)*D i+2*P x*y*(∑ t, π t*q i t)+
        2*P x*(∑ t, π t*(K i t*D t))-
        ∑ t, π t*((1-q i t)*max (D t-(1+m x+2*P x*y)*D i) 0))) := by
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [mul_add, Finset.mul_sum]
  exact congrArg₂ (·+·) hconst hterms

theorem unnormalized_drift_le_s35_oai {I : Type*} [Fintype I]
    {μ d N s : I → ℝ} {q K : I → I → ℝ} {x y pHat ζ : ℝ}
    (hx0 : 0 ≤ x) (hx : x ≤ 1) (hy0 : 0 < y) (hy : y ≤ 1)
    (hμ0 : ∀ i, 0 ≤ μ i) (hμ : ∑ i, μ i=y)
    (hd0 : ∀ i, 0 ≤ d i) (hV : 0 < ∑ i, μ i*d i) (hN : ∀ i, 0 ≤ N i)
    (hs0 : ∀ i, 0 ≤ s i) (hs : ∀ i, s i ≤ 1)
    (hq0 : ∀ i t, 0 ≤ q i t) (hq : ∀ i t, q i t ≤ 1)
    (hp0 : 0 ≤ pHat) (hp : pHat ≤ 1/2) (hζ0 : 0 ≤ ζ) (hζ : ζ < 1/4)
    (he : |pHat-P x| ≤ ζ)
    (hcomp : ∀ i t, q i t < 1 → N i*(1-pHat*q i t) ≤ d i+d t)
    (hK : ∀ i t, K i t ≤
      (s i*(1-∑ u, μ u*q i u)+s t*(1-∑ u, μ u*q t u))/2) :
    unnormalizedDrift μ d N s q K x y pHat ≤ 12*ζ*(∑ i, μ i*d i) := by
  let V := ∑ i, μ i*d i
  let L := V/y
  let π := fun i => μ i/y
  let D := fun i => d i/L
  let R := fun i => N i/L
  have hyne := ne_of_gt hy0
  have hLpos : 0 < L := div_pos hV hy0
  have hLne := ne_of_gt hLpos
  have hyL : y*L=V := by dsimp only [L]; exact mul_div_cancel₀ _ hyne
  have hπ0 : ∀ i, 0 ≤ π i := fun i => div_nonneg (hμ0 i) hy0.le
  have hπ : ∑ i, π i=1 := by dsimp only [π]; rw [← Finset.sum_div, hμ, div_self hyne]
  have hμid : ∀ i, y*π i=μ i := fun i => mul_div_cancel₀ _ hyne
  have hdid : ∀ i, L*D i=d i := fun i => mul_div_cancel₀ _ hLne
  have hNid : ∀ i, L*R i=N i := fun i => mul_div_cancel₀ _ hLne
  have hD : average π D=1 := by
    unfold average
    simp_rw [show ∀ i, π i*D i=(μ i*d i)/(y*L) by intro i; dsimp only [π, D]; ring]
    rw [← Finset.sum_div, hyL, div_self (ne_of_gt hV)]
  have hD0 : ∀ i, 0 ≤ D i := fun i => div_nonneg (hd0 i) hLpos.le
  have hR0 : ∀ i, 0 ≤ R i := fun i => div_nonneg (hN i) hLpos.le
  have hcomp' : ∀ i t, q i t < 1 → R i*(1-pHat*q i t) ≤ D i+D t := by
    intro i t hit
    have hh := div_le_div_of_nonneg_right (hcomp i t hit) hLpos.le
    dsimp only [R, D]
    simpa only [div_mul_eq_mul_div, add_div] using hh
  have hw : ∀ i, y*average π (q i)=∑ u, μ u*q i u := by
    intro i
    simp only [average, Finset.mul_sum, ← mul_assoc, hμid]
  have hK' : ∀ i t, K i t ≤
      (s i*(1-y*average π (q i))+s t*(1-y*average π (q t)))/2 := by
    intro i t
    simpa only [hw] using hK i t
  have hh := normalized_drift_le hx0 hx hy0 hy hπ0 hπ hD0 hD hR0 hs0 hs
    hq0 hq hp0 hp hζ0 hζ he hcomp' hK'
  have hnorm := normalization_identity π D R s q K x pHat hyne hLpos.le hD
  simp only [hμid, hdid, hNid] at hnorm
  rw [hnorm]
  have hscale := mul_le_mul_of_nonneg_left hh (mul_nonneg (sq_nonneg y) hLpos.le)
  have hV0 : 0 ≤ V := hV.le
  have hyV := mul_le_of_le_one_left hV0 hy
  have hprod := mul_le_mul_of_nonneg_left hyV (mul_nonneg (by norm_num : (0:ℝ) ≤ 12) hζ0)
  have heq : y^2*L=y*V := by calc
    y^2*L = y*(y*L) := by ring
    _ = y*V := by rw [hyL]
  rw [heq] at hscale ⊢
  calc
    y*V*normalizedDrift π D R s q K x y pHat ≤ y*V*(12*ζ) := hscale
    _ = 12*ζ*(y*V) := by ring
    _ ≤ 12*ζ*V := hprod

end MetricKMedian.GraphComparison
end
end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.MetricKMedian.GraphComparison.unnormalized_drift_le_s35_oai.{u_1} := @OAI.MetricKMedian.GraphComparison.unnormalized_drift_le_s35_oai.{u_1}
