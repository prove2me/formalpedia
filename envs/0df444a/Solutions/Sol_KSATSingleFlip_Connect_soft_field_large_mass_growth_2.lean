-- Prove2me | solution 2 for KSATSingleFlip.Connect.soft_field_large_mass_growth
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-11-13T11:25:19.686146+00:00
-- url     : https://prove2.me/submissions/cde0cd0b-99bd-49dd-b2e4-70d5d164ebe5

import Definitions.Def_KSATSingleFlip_Connect_SoftField
import Mathlib
set_option autoImplicit false
open KSATSingleFlip.Connect

theorem solution (m h γ : ℝ) (hm : 8 ≤ m) (hh : c0 * m ≤ h) (hγ : γ ≤ 1) :
    m + 1 ≤ Real.exp (-γ) * Real.exp h := by
  have hrhs : Real.exp (-γ) * Real.exp h = Real.exp (h - γ) := by
    rw [← Real.exp_add]; ring_nf
  rw [hrhs]
  have hge : c0 * m - 1 ≤ h - γ := by nlinarith
  refine le_trans ?_ (Real.exp_monotone hge)
  -- c0 ≥ 4/5
  have hc0 : (4 / 5 : ℝ) ≤ c0 := by
    have hsq : (7 / 5 : ℝ) ^ 2 ≤ (2 : ℝ) := by norm_num
    have hsqrt : (7 / 5 : ℝ) ≤ Real.sqrt 2 :=
      (Real.le_sqrt (by norm_num) (by positivity)).2 hsq
    unfold c0
    nlinarith [Real.sqrt_nonneg (2 : ℝ)]
  have hbase : (4 / 5 : ℝ) * m - 1 ≤ c0 * m - 1 := by nlinarith
  refine le_trans ?_ (Real.exp_monotone hbase)
  -- (4/5)m - 1 ≥ m/2 for m ≥ 8
  have hhalf : (m / 2 : ℝ) ≤ (4 / 5) * m - 1 := by nlinarith
  refine le_trans ?_ (Real.exp_monotone hhalf)
  have hx : (0 : ℝ) ≤ m / 2 := by nlinarith
  -- m+1 ≤ 1 + m/2 + (m/2)^2/2 ≤ exp(m/2)
  have hexp := Real.quadratic_le_exp_of_nonneg hx
  have hpoly : (m + 1 : ℝ) ≤ 1 + m / 2 + (m / 2) ^ 2 / 2 := by nlinarith
  exact hpoly.trans hexp
