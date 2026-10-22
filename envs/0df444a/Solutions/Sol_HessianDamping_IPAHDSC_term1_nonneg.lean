-- Prove2me | solution 1 for HessianDamping.IPAHDSC.term1_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T07:22:34.173744+00:00
-- url     : https://prove2.me/submissions/acdfb672-65dc-43ca-ba7b-ede8f99f4f01

import Mathlib
set_option autoImplicit false

theorem solution (μ β : ℝ) (hμ : 0 < μ) (hβ0 : 0 ≤ β) (hβ : β ≤ 1 / (2 * Real.sqrt μ))
    (X Y : ℝ) :
    0 ≤ Real.sqrt μ * μ / 4 * X ^ 2 + β / 2 * Y ^ 2 - β * μ * X * Y := by
  have hr : 0 < Real.sqrt μ := Real.sqrt_pos.mpr hμ
  have hμr : μ = Real.sqrt μ ^ 2 := (Real.sq_sqrt hμ.le).symm
  set r := Real.sqrt μ with hrdef
  have h1 : β * r ≤ 1 / 2 := by
    have := mul_le_mul_of_nonneg_right hβ hr.le
    have e : 1 / (2 * r) * r = 1 / 2 := by field_simp
    linarith
  have key : Real.sqrt μ * μ / 4 * X ^ 2 + β / 2 * Y ^ 2 - β * μ * X * Y
      = β / 2 * (Y - r ^ 2 * X) ^ 2 + r ^ 3 * (1 / 4 - β * r / 2) * X ^ 2 := by
    rw [← hrdef]; rw [hμr]; ring
  rw [key]
  have h2 : 0 ≤ 1 / 4 - β * r / 2 := by linarith
  have h3 : 0 ≤ r ^ 3 * (1 / 4 - β * r / 2) := mul_nonneg (by positivity) h2
  have := mul_nonneg h3 (sq_nonneg X)
  have := mul_nonneg (div_nonneg hβ0 (by norm_num : (0:ℝ) ≤ 2)) (sq_nonneg (Y - r ^ 2 * X))
  linarith
