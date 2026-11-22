-- Prove2me | solution 1 for LongGapsBetweenPrimes.squarefree_euler_factor_tilt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:56:37.294503+00:00
-- url     : https://prove2.me/submissions/6ee86a4c-e1e9-49a0-836b-994778a61ca9

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
import Theorems.Thm_LongGapsBetweenPrimes_rpow_sub_one_le

set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section
namespace LongGapsBetweenPrimes
theorem _root_.solution {p γ E : ℝ} (hp : 1 < p)
    (hγ : 0 ≤ γ) (hpE : p ^ γ ≤ E) :
    1 + p ^ γ / (p - 1) ≤
      (1 + 1 / (p - 1)) * Real.exp (E * γ * Real.log p / p) := by
  have hp0 : 0 < p := by linarith
  have hpm : 0 < p - 1 := by linarith
  have hlog : 0 ≤ Real.log p := (Real.log_pos hp).le
  have hdiff : p ^ γ - 1 ≤ E * γ * Real.log p := by
    have h := rpow_sub_one_le (γ := γ) hp0
    have hmul := mul_le_mul_of_nonneg_right hpE (mul_nonneg hγ hlog)
    nlinarith
  have hexp : 1 + (p ^ γ - 1) / p ≤ Real.exp (E * γ * Real.log p / p) := by
    calc
      _ ≤ 1 + E * γ * Real.log p / p :=
        add_le_add le_rfl (div_le_div_of_nonneg_right hdiff hp0.le)
      _ ≤ _ := by simpa only [add_comm] using Real.add_one_le_exp (E * γ * Real.log p / p)
  have he : 1 + p ^ γ / (p - 1) = (1 + 1 / (p - 1)) * (1 + (p ^ γ - 1) / p) := by
    field_simp [ne_of_gt hp0, ne_of_gt hpm]
    ring
  rw [he]
  exact mul_le_mul_of_nonneg_left hexp (by positivity)
end LongGapsBetweenPrimes
