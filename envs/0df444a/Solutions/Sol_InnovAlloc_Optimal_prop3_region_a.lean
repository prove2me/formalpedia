-- Prove2me | solution 1 for InnovAlloc.Optimal.prop3_region_a
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T02:46:33.289689+00:00
-- url     : https://prove2.me/submissions/5c12736d-e666-47b0-be70-655ac2dbfd30

import Mathlib
import Definitions.Def_InnovAlloc_Optimal_Model

open InnovAlloc.Optimal in
theorem solution (α γ B : ℝ) (hs : Standing α γ)
    (ha : α < alphaLow) (hB : 2 < γ * B) :
    profitDuo α γ B < profitMono γ B := by
  obtain ⟨hγ0, hγ1, hα0, hα1⟩ := hs
  unfold alphaLow at ha
  have hs2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hs0 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hsl : Real.sqrt 2 < 17 / 12 := by
    rw [Real.sqrt_lt' (by norm_num)]; norm_num
  have h12 : 0 < 1 - 2 * α := by linarith
  have hdisc : α ^ 2 + 16 * α - 8 < 0 := by
    have h1 : 0 < 6 * Real.sqrt 2 - (α + 8) := by linarith
    have h2 : 0 < 6 * Real.sqrt 2 + (α + 8) := by linarith
    nlinarith [mul_pos h1 h2]
  unfold profitDuo profitMono
  rw [if_neg (by linarith), if_neg (by linarith)]
  apply mul_lt_mul_of_pos_left _ (by linarith)
  have e : γ * α ^ 2 * B = α ^ 2 * (γ * B) := by ring
  rw [e]
  generalize γ * B = t at hB ⊢
  have ht0 : 0 < t := by linarith
  have hf : 0 < (1 - 2 * α) * t ^ 2 - 2 * (1 - α) * t + 9 := by
    nlinarith [sq_nonneg ((1 - 2 * α) * t - (1 - α))]
  have hy : 0 < 1 - α + 3 / t := by
    have : 0 < 3 / t := by positivity
    linarith
  have hsq : Real.sqrt ((α ^ 2 * t - 8 * α + 8) / t) < 1 - α + 3 / t := by
    rw [Real.sqrt_lt' hy]
    have hrhs : 1 - α + 3 / t = (t * (1 - α) + 3) / t := by
      field_simp
    rw [hrhs, div_pow, div_lt_div_iff₀ ht0 (by positivity)]
    nlinarith [mul_pos ht0 hf]
  have : 4 / t - 1 / t = 3 / t := by ring
  linarith
