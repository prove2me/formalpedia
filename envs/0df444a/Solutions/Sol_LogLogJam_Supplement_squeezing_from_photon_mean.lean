-- Prove2me | solution 1 for LogLogJam.Supplement.squeezing_from_photon_mean
-- status  : ACCEPTED   (prove)
-- author  : @Senrui Chen
-- created : 2026-11-26T09:18:13.564909+00:00
-- url     : https://prove2.me/submissions/f3ad679c-2463-4c6b-b09d-8fcd6b2bf537

import Mathlib



/-- Deterministic conversion in Eq. (170) of arXiv:2607.12983v1. A photon-number
mean estimate at its natural standard-deviation scale controls the squeezing
error uniformly, including at the vacuum. -/
theorem solution {r μ η : ℝ} (hr : 0 ≤ r) (hμ : 0 ≤ μ)
    (hη : 0 ≤ η) (hsmall : η ≤ 1 / 4)
    (h : |μ - Real.sinh r ^ 2| ≤ η * Real.cosh r * Real.sinh r) :
    |Real.arsinh (Real.sqrt μ) - r| ≤ 4 * η := by
  let s := Real.arsinh (Real.sqrt μ)
  have hs : Real.sinh s = Real.sqrt μ := Real.sinh_arsinh _
  have hy : 0 ≤ Real.sinh s := hs ▸ Real.sqrt_nonneg _
  have hx : 0 ≤ Real.sinh r := Real.sinh_nonneg_iff.mpr hr
  have hsq : Real.sinh s ^ 2 = μ := hs ▸ Real.sq_sqrt hμ
  have hdiff : |Real.sinh s - Real.sinh r| ≤ η * Real.cosh r := by
    by_cases hzero : Real.sinh r = 0
    · rw [hzero] at h ⊢
      simp only [zero_pow (by decide : 2 ≠ 0), sub_zero, mul_zero, abs_of_nonneg hμ] at h
      have hyzero : Real.sinh s = 0 := by nlinarith
      rw [hyzero, sub_zero, abs_zero]
      positivity
    · have hpos : 0 < Real.sinh r := lt_of_le_of_ne hx (Ne.symm hzero)
      apply le_of_mul_le_mul_right _ hpos
      calc
        |Real.sinh s - Real.sinh r| * Real.sinh r ≤
            |Real.sinh s - Real.sinh r| * (Real.sinh s + Real.sinh r) :=
          mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg _)
        _ = |μ - Real.sinh r ^ 2| := by
          rw [← hsq, sq_sub_sq, abs_mul, abs_of_nonneg (by linarith : 0 ≤ Real.sinh s + Real.sinh r), mul_comm]
        _ ≤ _ := h
  have hExp : |Real.exp s - Real.exp r| ≤ 2 * |Real.sinh s - Real.sinh r| := by
    rcases le_total r s with hrs | hsr
    · rw [abs_of_nonneg (sub_nonneg.mpr (Real.exp_le_exp.mpr hrs)),
          abs_of_nonneg (sub_nonneg.mpr (Real.sinh_le_sinh.mpr hrs)), Real.sinh_eq, Real.sinh_eq]
      linarith [Real.exp_le_exp.mpr (neg_le_neg hrs)]
    · rw [abs_of_nonpos (sub_nonpos.mpr (Real.exp_le_exp.mpr hsr)),
          abs_of_nonpos (sub_nonpos.mpr (Real.sinh_le_sinh.mpr hsr)), Real.sinh_eq, Real.sinh_eq]
      linarith [Real.exp_le_exp.mpr (neg_le_neg hsr)]
  have hc : Real.cosh r ≤ Real.exp r := by linarith [Real.cosh_add_sinh r]
  have hb : |Real.exp s - Real.exp r| ≤ 2 * η * Real.exp r :=
    hExp.trans (by nlinarith [mul_nonneg hη (sub_nonneg.mpr hc)])
  have hpair := abs_le.mp hb
  have hratio : Real.exp r ≤ 2 * Real.exp s := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hsmall) (Real.exp_pos r).le]
  have hForward := Real.add_one_le_exp (s - r)
  have hBackward := Real.add_one_le_exp (r - s)
  rw [Real.exp_sub] at hForward hBackward
  have hf := (le_div_iff₀ (Real.exp_pos r)).mp hForward
  have hbk := (le_div_iff₀ (Real.exp_pos s)).mp hBackward
  apply abs_le.mpr
  constructor
  · have haux : (r - s) * Real.exp s ≤ 4 * η * Real.exp s := by
      nlinarith [mul_nonneg hη (sub_nonneg.mpr hratio)]
    have := (mul_le_mul_iff_left₀ (Real.exp_pos s)).mp haux
    change -(4 * η) ≤ s - r
    linarith
  · have haux : (s - r) * Real.exp r ≤ (2 * η) * Real.exp r := by linarith
    have := (mul_le_mul_iff_left₀ (Real.exp_pos r)).mp haux
    change s - r ≤ 4 * η
    linarith
