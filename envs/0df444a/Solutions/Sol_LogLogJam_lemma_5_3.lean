-- Prove2me | solution 1 for LogLogJam.lemma_5_3
-- status  : ACCEPTED   (prove)
-- author  : @Senrui Chen
-- created : 2026-11-26T09:15:43.146742+00:00
-- url     : https://prove2.me/submissions/24b9c18e-e138-40f3-9c89-0d6d714c4072

import Mathlib
import Definitions.Def_LogLogJam_Vsq

open MeasureTheory LogLogJam
open scoped ENNReal

private theorem squeezedDet (l a b : ℝ) (hl : l ≠ 0) :
    (Vsq l a + Vsq l b).det = 4 + (l-l⁻¹)^2 * Real.sin (a-b)^2 := by
  simp [Vsq, rot, Matrix.det_fin_two, Matrix.vecMul, dotProduct, Fin.sum_univ_two, Matrix.transpose_apply, Real.sin_sub]
  linear_combination
    (l*l⁻¹ * (Real.sin a^2 + 2*Real.sin b^2 + Real.cos a^2 + 2*Real.cos b^2 + 1)) *
      Real.sin_sq_add_cos_sq a +
    (l*l⁻¹ * (Real.sin b^2 + Real.cos b^2 + 3)) * Real.sin_sq_add_cos_sq b +
    4 * (mul_inv_cancel₀ hl)

private theorem smallDistance (u e : ℝ) (he : 0 < e) (he' : e < 1/2)
    (h : Real.sqrt (1 - 2 / Real.sqrt (4 + u^2)) ≤ e) : u ≤ 4 * e := by
  let z := Real.sqrt (4 + u^2)
  have hzsq : z^2 = 4 + u^2 := Real.sq_sqrt (by positivity)
  have hznon : 0 ≤ z := Real.sqrt_nonneg _
  have hz : 2 ≤ z := by nlinarith [sq_nonneg u]
  have h' : 1 - 2 / z ≤ e^2 := (Real.sqrt_le_left he.le).mp h
  have hdz : z - 2 ≤ e^2 * z := by
    have hv : (1 - e^2) ≤ 2 / z := by linarith
    have := (le_div_iff₀ (show 0 < z by linarith)).mp hv
    linarith
  have heq : e^2 ≤ 1/4 := by nlinarith [mul_self_le_mul_self he.le he'.le]
  have hz3 : z ≤ 3 := by nlinarith [mul_le_mul_of_nonneg_right heq hznon]
  have hzs : z * (z+2) ≤ 15 := by nlinarith [mul_self_le_mul_self hznon hz3]
  have hu : u^2 ≤ 15 * e^2 := by
    calc
      u^2 = (z-2)*(z+2) := by nlinarith
      _ ≤ (e^2 * z)*(z+2) := mul_le_mul_of_nonneg_right hdz (by linarith)
      _ ≤ 15*e^2 := by nlinarith [mul_le_mul_of_nonneg_left hzs (sq_nonneg e)]
  nlinarith [sq_nonneg (u-4*e), sq_nonneg e]

private theorem sineNecessary (l e a b : ℝ) (hl : 1 < l) (hE : 1 < energy l)
    (he : 0 < e) (he' : e < 1/2) (h : trDist l a b ≤ e) :
    |Real.sin (a-b)| ≤ 2*e / energy l := by
  have hlpos : 0 < l := by linarith
  have hi : l⁻¹ < 1 := inv_lt_one_of_one_lt₀ hl
  let s := |Real.sin (a-b)|
  have hs : 0 ≤ s := abs_nonneg _
  have hre : ((l-l⁻¹)*s)^2 = (l-l⁻¹)^2 * Real.sin (a-b)^2 := by
    rw [mul_pow]; exact congrArg _ (sq_abs _)
  have h' := smallDistance ((l-l⁻¹)*s) e he he' (by simpa only [hre, trDist, squeezedDet l a b hlpos.ne'] using h)
  have hcoeff : 2*energy l ≤ l-l⁻¹ := by
    unfold energy at *; linarith
  apply (le_div_iff₀ (by linarith : 0 < energy l)).mpr
  change s * energy l ≤ 2 * e
  nlinarith [mul_le_mul_of_nonneg_right hcoeff hs]

private theorem shiftPeriod (S : Set ℝ) (hS : MeasurableSet S)
    (hp : ∀ x : ℝ, x + Real.pi ∈ S ↔ x ∈ S) (a : ℝ) :
    volume (Set.Ico 0 Real.pi ∩ S) = volume (Set.Ico a (a+Real.pi) ∩ S) := by
  classical
  let f := S.indicator (fun _ => (1 : ℝ))
  have hperiod : Function.Periodic f Real.pi := by
    intro x
    by_cases hx : x ∈ S
    · simp [f,hx,(hp x).mpr hx]
    · simp [f,hx,mt (hp x).mp hx]
  have eval (x : ℝ) : (∫ y in x..x+Real.pi, f y) = (volume (Set.Ico x (x+Real.pi) ∩ S)).toReal := by
    rw [intervalIntegral.integral_of_le (by linarith [Real.pi_pos]), ← integral_Ico_eq_integral_Ioc]
    calc
      _ = (volume.restrict (Set.Ico x (x+Real.pi))).real S := integral_indicator_one hS
      _ = _ := by rw [measureReal_restrict_apply hS, Set.inter_comm]; rfl
  have fin (x y : ℝ) : volume (Set.Ico x y ∩ S) ≠ ⊤ :=
    measure_ne_top_of_subset Set.inter_subset_left (by simp [Real.volume_Ico])
  apply (ENNReal.toReal_eq_toReal_iff' (fin _ _) (fin _ _)).mp
  have hh := hperiod.intervalIntegral_add_eq 0 a
  rw [eval 0, eval a] at hh
  simpa only [zero_add] using hh

theorem solution (lam ε θ : ℝ) (hlam : 1 < lam) (hE : 1 < energy lam) (hε : 0 < ε)
    (hε2 : ε < 1 / 2) :
    volume {θ' ∈ Set.Ico 0 Real.pi | trDist lam θ' θ ≤ ε} ≤
      ENNReal.ofReal (2 * Real.pi * ε / energy lam) := by
  let S : Set ℝ := {x | |Real.sin (x-θ)| ≤ 2*ε / energy lam}
  have hSm : MeasurableSet S := measurableSet_le (by fun_prop) measurable_const
  have hperiod (x : ℝ) : x + Real.pi ∈ S ↔ x ∈ S := by
    simp only [S, Set.mem_ofPred_eq, show x+Real.pi-θ = (x-θ)+Real.pi by ring,
      Real.sin_add_pi, abs_neg]
  let r := Real.pi*ε / energy lam
  have hepos : 0 < energy lam := by linarith
  calc
    _ ≤ volume (Set.Ico 0 Real.pi ∩ S) := measure_mono (fun x hx =>
      ⟨hx.1, sineNecessary lam ε x θ hlam hE hε hε2 hx.2⟩)
    _ = volume (Set.Ico (θ-Real.pi/2) (θ-Real.pi/2+Real.pi) ∩ S) := shiftPeriod S hSm hperiod _
    _ ≤ volume (Set.Icc (θ-r) (θ+r)) := by
      apply measure_mono
      intro x hx
      obtain ⟨⟨hx₁,hx₂⟩,hs⟩ := hx
      change |Real.sin (x-θ)| ≤ 2*ε / energy lam at hs
      have ha : |x-θ| ≤ Real.pi/2 := abs_le.mpr ⟨by linarith,by linarith⟩
      have hb := (Real.mul_abs_le_abs_sin ha).trans hs
      have hd : |x-θ| ≤ r := by
        dsimp [r]
        field_simp [Real.pi_ne_zero, hepos.ne'] at hb ⊢
        linarith
      obtain ⟨h1,h2⟩ := abs_le.mp hd
      exact ⟨by linarith,by linarith⟩
    _ = _ := by rw [Real.volume_Icc]; congr 1; dsimp [r]; ring
