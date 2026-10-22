-- Prove2me | solution 1 for MarketplaceLeakage.Communication.eta_star_limit
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T06:47:05.379048+00:00
-- url     : https://prove2.me/submissions/b9c05b40-10a6-445c-9b01-1f68a5fe48a1

import Mathlib
import Definitions.Def_MarketplaceLeakage_Communication_Setting

set_option autoImplicit false

open MarketplaceLeakage.Communication Filter Topology

theorem solution (v c : ℝ) (hvc : c < v) :
    Filter.Tendsto (etaStar v c) (nhdsWithin 1 (Set.Iio 1)) (nhds 1) := by
  have hcont : ContinuousAt (etaStar v c) 1 := by
    unfold etaStar
    apply ContinuousAt.div
    · fun_prop
    · fun_prop
    · simp only [sub_self, mul_zero, zero_add, one_pow, mul_one, one_mul]
      linarith
  have h1 : etaStar v c 1 = 1 := by
    unfold etaStar
    have hden : (1:ℝ) * v * (3 * (1 - 1) + 1 ^ 2) - c ≠ 0 := by
      have e : (1:ℝ) * v * (3 * (1 - 1) + 1 ^ 2) - c = v - c := by ring
      rw [e]; exact sub_ne_zero.2 hvc.ne'
    rw [div_eq_one_iff_eq hden]
    norm_num
  have h2 := hcont.tendsto
  rw [h1] at h2
  exact h2.mono_left nhdsWithin_le_nhds
