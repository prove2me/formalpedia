-- Prove2me | solution 1 for NHPPArrivals.LinearRate.linear_degree_zero
-- status  : ACCEPTED   (prove)
-- author  : @andreaskapfer
-- created : 2026-09-30T05:05:50.187107+00:00
-- url     : https://prove2.me/submissions/1526a214-45d0-4ab8-bd69-493e646ff1a7

import Mathlib
import Definitions.Def_NHPPArrivals_LinearRate_ConditionalCdf

open MeasureTheory
open NHPPArrivals.LinearRate

theorem solution (b T : ℝ) (hT : 0 < T) (hb : 0 < b) :
    (∀ t ∈ Set.Icc (0:ℝ) 1, condCdf (linRate 0 b) T t = t ^ 2) ∧
    IsGreatest ((fun t => |condCdf (linRate 0 b) T t - t|) '' Set.Icc (0:ℝ) 1) (1 / 4) ∧
    degree (condCdf (linRate 0 b) T) = 1 / 4 := by
  have hcum : ∀ x : ℝ, cumRate (linRate 0 b) x = b * (x ^ 2 / 2) := by
    intro x
    simp only [cumRate, linRate, zero_add]
    rw [intervalIntegral.integral_const_mul]
    congr 1
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := (0:ℝ)) (b := x)
      (f := fun y : ℝ => y ^ 2 / 2) (f' := fun y : ℝ => y)
      (fun y _ => by
        simpa using (hasDerivAt_pow 2 y).div_const 2)
      (continuous_id.intervalIntegrable 0 x)
    simpa using h
  have hcd : ∀ t ∈ Set.Icc (0:ℝ) 1, condCdf (linRate 0 b) T t = t ^ 2 := by
    intro t ht
    have hb' : b ≠ 0 := ne_of_gt hb
    have hT' : T ≠ 0 := ne_of_gt hT
    rw [condCdf, hcum, hcum]
    field_simp
  have hgreat : IsGreatest ((fun t => |condCdf (linRate 0 b) T t - t|) '' Set.Icc (0:ℝ) 1) (1 / 4) := by
    constructor
    · refine ⟨1 / 2, ⟨by norm_num, by norm_num⟩, ?_⟩
      change |condCdf (linRate 0 b) T (1 / 2) - 1 / 2| = 1 / 4
      rw [hcd (1 / 2) ⟨by norm_num, by norm_num⟩]
      norm_num
    · rintro y ⟨t, ht, rfl⟩
      change |condCdf (linRate 0 b) T t - t| ≤ 1 / 4
      rw [hcd t ht]
      have ht2 : t ^ 2 ≤ t := by nlinarith [ht.1, ht.2]
      rw [abs_of_nonpos (by linarith : t ^ 2 - t ≤ 0)]
      nlinarith [sq_nonneg (t - 1 / 2)]
  exact ⟨hcd, hgreat, by simpa only [degree] using hgreat.csSup_eq⟩
