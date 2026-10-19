-- Prove2me | solution 1 for HamburgerMoment.exists_nonunique_solution
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T11:26:58.934405+00:00
-- url     : https://prove2.me/submissions/6c81b861-2dae-43c7-8cea-b56f3b96e688

import Mathlib
import Definitions.Def_HamburgerMoment_Defs

open MeasureTheory Real
open scoped ENNReal NNReal

namespace HMLog

noncomputable def g0 (u : ℝ) : ℝ := exp (-(1 / 2) * u ^ 2)
noncomputable def g1 (u : ℝ) : ℝ := exp (-(1 / 2) * u ^ 2) * (1 + sin (2 * π * u))
noncomputable def ρ (g : ℝ → ℝ) : Measure ℝ := volume.withDensity (fun u => ((g u).toNNReal : ℝ≥0∞))
noncomputable def M (g : ℝ → ℝ) : Measure ℝ := (ρ g).map exp
noncomputable def mom (n : ℕ) : ℝ := ∫ u, g0 u * exp u ^ n

lemma g0_nn (u : ℝ) : 0 ≤ g0 u := (exp_pos _).le
lemma g1_nn (u : ℝ) : 0 ≤ g1 u := by
  unfold g1; have := neg_one_le_sin (2 * π * u)
  exact mul_nonneg (exp_pos _).le (by linarith)

lemma g0_meas : Measurable g0 := by unfold g0; fun_prop
lemma g1_meas : Measurable g1 := by unfold g1; fun_prop

lemma shift (n : ℕ) (u : ℝ) :
    exp u ^ n * exp (-(1 / 2) * u ^ 2) = exp ((n:ℝ) ^ 2 / 2) * exp (-(1 / 2) * (u - n) ^ 2) := by
  rw [← exp_nat_mul, ← exp_add, ← exp_add]; congr 1; ring

lemma int0 (n : ℕ) : Integrable (fun u => g0 u * exp u ^ n) := by
  have h := ((integrable_exp_neg_mul_sq (b := 1 / 2) (by norm_num)).comp_sub_right (n:ℝ)).const_mul
    (exp ((n:ℝ) ^ 2 / 2))
  refine h.congr (Filter.Eventually.of_forall fun u => ?_)
  simp only [g0]
  rw [mul_comm (exp _) (exp u ^ n), shift]

lemma g1_le (u : ℝ) : g1 u ≤ 2 * g0 u := by
  unfold g1 g0; have := sin_le_one (2 * π * u); have := exp_pos (-(1 / 2) * u ^ 2); nlinarith

lemma int1 (n : ℕ) : Integrable (fun u => g1 u * exp u ^ n) := by
  refine ((int0 n).const_mul 2).mono' (g1_meas.mul (by fun_prop)).aestronglyMeasurable
    (Filter.Eventually.of_forall fun u => ?_)
  have hp := pow_pos (exp_pos u) n
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (g1_nn u) hp.le), ← mul_assoc]
  exact mul_le_mul_of_nonneg_right (g1_le u) hp.le

lemma odd_zero : ∫ v, exp (-(1 / 2) * v ^ 2) * sin (2 * π * v) = 0 := by
  have h := integral_neg_eq_self (fun v : ℝ => exp (-(1 / 2) * v ^ 2) * sin (2 * π * v)) volume
  have e : (fun v : ℝ => exp (-(1 / 2) * (-v) ^ 2) * sin (2 * π * -v)) =
      fun v => -(exp (-(1 / 2) * v ^ 2) * sin (2 * π * v)) := by
    ext v; rw [neg_sq, mul_neg, sin_neg]; ring
  rw [e, integral_neg] at h
  linarith

lemma sin_zero (n : ℕ) : ∫ u, g0 u * exp u ^ n * sin (2 * π * u) = 0 := by
  have e : (fun u => g0 u * exp u ^ n * sin (2 * π * u)) = fun u =>
      exp ((n:ℝ) ^ 2 / 2) * ((fun v => exp (-(1 / 2) * v ^ 2) * sin (2 * π * v)) (u - n)) := by
    ext u
    simp only [g0]
    rw [mul_comm (exp _) (exp u ^ n), shift]
    have : sin (2 * π * (u - n)) = sin (2 * π * u) := by
      rw [show 2 * π * (u - n) = 2 * π * u - n * (2 * π) by ring, sin_sub_nat_mul_two_pi]
    rw [this]; ring
  rw [e, integral_const_mul, integral_sub_right_eq_self (fun v => exp (-(1 / 2) * v ^ 2) * sin (2 * π * v)),
    odd_zero, mul_zero]

lemma moments (g : ℝ → ℝ) (hg : Measurable g) (hnn : ∀ u, 0 ≤ g u) (n : ℕ)
    (hint : Integrable (fun u => g u * exp u ^ n)) :
    Integrable (fun x : ℝ => x ^ n) (M g) ∧ ∫ x, x ^ n ∂(M g) = ∫ u, g u * exp u ^ n := by
  have hm : Measurable fun u => (g u).toNNReal := hg.real_toNNReal
  have hc : ∀ u, ((g u).toNNReal : ℝ) = g u := fun u => Real.coe_toNNReal _ (hnn u)
  constructor
  · unfold M
    rw [integrable_map_measure (by fun_prop) (by fun_prop)]
    unfold ρ
    rw [integrable_withDensity_iff_integrable_smul hm]
    refine hint.congr (Filter.Eventually.of_forall fun u => ?_)
    simp [NNReal.smul_def, hc]
  · unfold M
    rw [integral_map (by fun_prop) (by fun_prop)]
    unfold ρ
    rw [integral_withDensity_eq_integral_smul hm]
    congr 1; ext u
    simp [NNReal.smul_def, hc]

lemma mom0 : HamburgerMoment.IsMomentMeasure mom (M g0) := fun n =>
  moments g0 g0_meas g0_nn n (int0 n)

lemma mom1 : HamburgerMoment.IsMomentMeasure mom (M g1) := by
  intro n
  obtain ⟨h1, h2⟩ := moments g1 g1_meas g1_nn n (int1 n)
  refine ⟨h1, ?_⟩
  rw [h2]
  have e : (fun u => g1 u * exp u ^ n) = fun u => g0 u * exp u ^ n + g0 u * exp u ^ n * sin (2 * π * u) := by
    ext u; simp only [g1, g0]; ring
  have i2 : Integrable (fun u => g0 u * exp u ^ n * sin (2 * π * u)) := by
    refine (int0 n).mono' (by unfold g0; fun_prop) (Filter.Eventually.of_forall fun u => ?_)
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
    have := abs_sin_le_one (2 * π * u)
    have := abs_nonneg (g0 u * exp u ^ n)
    rw [abs_of_nonneg (by have := g0_nn u; positivity)]
    nlinarith [abs_of_nonneg (show 0 ≤ g0 u * exp u ^ n by have := g0_nn u; positivity)]
  rw [e, integral_add (int0 n) i2, sin_zero, add_zero]
  rfl

lemma ne : M g0 ≠ M g1 := by
  intro h
  set B : Set ℝ := log ⁻¹' Set.Ioo 0 (1 / 2) ∩ Set.Ioi 0 with hB
  have hBm : MeasurableSet B := (measurable_log measurableSet_Ioo).inter measurableSet_Ioi
  have hpre : exp ⁻¹' B = Set.Ioo 0 (1 / 2) := by
    ext u; simp [hB, exp_pos]
  have e := congrArg (fun μ : Measure ℝ => μ B) h
  simp only [M] at e
  rw [Measure.map_apply measurable_exp hBm, Measure.map_apply measurable_exp hBm, hpre] at e
  simp only [ρ] at e
  rw [withDensity_apply _ measurableSet_Ioo, withDensity_apply _ measurableSet_Ioo] at e
  have hlt : ∫⁻ u in Set.Ioo (0:ℝ) (1 / 2), ((g0 u).toNNReal : ℝ≥0∞) <
      ∫⁻ u in Set.Ioo (0:ℝ) (1 / 2), ((g1 u).toNNReal : ℝ≥0∞) := by
    refine setLIntegral_strict_mono measurableSet_Ioo (by simp) g1_meas.real_toNNReal.coe_nnreal_ennreal ?_ ?_
    · refine ne_top_of_le_ne_top (b := ∫⁻ u in Set.Ioo (0:ℝ) (1 / 2), 1) (by simp) ?_
      refine lintegral_mono fun u => ?_
      simp only [ENNReal.coe_le_one_iff]
      rw [Real.toNNReal_le_one]
      unfold g0; rw [Real.exp_le_one_iff]; nlinarith [sq_nonneg u]
    · refine Filter.Eventually.of_forall fun u hu => ?_
      have hlt0 : g0 u < g1 u := by
        unfold g0 g1
        have hs : 0 < sin (2 * π * u) := sin_pos_of_pos_of_lt_pi (by have := hu.1; positivity)
          (by have := hu.2; nlinarith [pi_pos])
        have := exp_pos (-(1 / 2) * u ^ 2)
        nlinarith
      rw [ENNReal.coe_lt_coe, Real.toNNReal_lt_toNNReal_iff (lt_of_le_of_lt (g0_nn u) hlt0)]
      exact hlt0
  rw [e] at hlt
  exact lt_irrefl _ hlt

end HMLog

open HamburgerMoment HMLog in
theorem solution :
    ∃ (m : ℕ → ℝ) (μ ν : Measure ℝ), IsMomentMeasure m μ ∧ IsMomentMeasure m ν ∧ μ ≠ ν :=
  ⟨mom, M g0, M g1, mom0, mom1, HMLog.ne⟩
