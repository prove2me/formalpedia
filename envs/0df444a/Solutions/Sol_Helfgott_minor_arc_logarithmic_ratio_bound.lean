-- Prove2me | solution 1 for Helfgott.minor_arc_logarithmic_ratio_bound
-- status  : ACCEPTED   (prove)
-- author  : @flyingviper
-- created : 2026-11-11T00:57:55.058339+00:00
-- url     : https://prove2.me/submissions/6b2b84fa-521e-40db-9c4f-2c73c83f7f9a

import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

open Finset
open scoped BigOperators

set_option maxRecDepth 2000
set_option maxHeartbeats 800000

private lemma log_two_bounds :
    (69314718055 / 100000000000 : ℝ) ≤ Real.log 2 ∧
    Real.log 2 ≤ (69314718056 / 100000000000 : ℝ) := by
  have hl := Real.sum_range_le_log_div (by norm_num : (0 : ℝ) ≤ 1 / 3)
    (by norm_num : (1 / 3 : ℝ) < 1) 15
  have hu := Real.log_div_le_sum_range_add (by norm_num : (0 : ℝ) ≤ 1 / 3)
    (by norm_num : (1 / 3 : ℝ) < 1) 15
  norm_num [Finset.sum_range_succ] at hl hu
  constructor <;> linarith

private lemma log_three_upper :
    Real.log 3 ≤ (10986122887 / 10000000000 : ℝ) := by
  have h := Real.log_div_le_sum_range_add (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 / 2 : ℝ) < 1) 20
  norm_num [Finset.sum_range_succ] at h
  linarith

private lemma log_scale_lower :
    (178976146656 / 100000000000 : ℝ) ≤ Real.log (1000 / 167) := by
  have h := Real.sum_range_le_log_div (by norm_num : (0 : ℝ) ≤ 833 / 1167)
    (by norm_num : (833 / 1167 : ℝ) < 1) 40
  norm_num [Finset.sum_range_succ] at h
  linarith

private lemma log_tangent_upper :
    Real.log (5048906545 / 9781309 : ℝ) ≤ (62464536535 / 10000000000 : ℝ) := by
  have h := Real.log_div_le_sum_range_add
    (by norm_num : (0 : ℝ) ≤ 40876337 / 10056936753)
    (by norm_num : (40876337 / 10056936753 : ℝ) < 1) 3
  norm_num [Finset.sum_range_succ] at h
  have heq : Real.log (5048906545 / 9781309 : ℝ) =
      9 * Real.log 2 + Real.log (5048906545 / 5008030208 : ℝ) := by
    have hp : Real.log ((2 : ℝ) ^ 9) = 9 * Real.log 2 := by
      simp
    rw [← hp, ← Real.log_mul (by norm_num : (2 : ℝ) ^ 9 ≠ 0)
      (by norm_num : (5048906545 / 5008030208 : ℝ) ≠ 0)]
    norm_num
  have h2 := log_two_bounds.2
  linarith

private lemma log_constant_lower :
    (20208105267 / 10000000000 : ℝ) ≤
      Real.log ((1000 / 167 : ℝ) * (2 : ℝ) ^ (1 / 3 : ℝ)) := by
  rw [Real.log_mul (by norm_num : (1000 / 167 : ℝ) ≠ 0)
    (ne_of_gt (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) _)),
    Real.log_rpow (by norm_num : (0 : ℝ) < 2)]
  have h2 := log_two_bounds.1
  have hs := log_scale_lower
  linarith

private lemma log_ratio_den_pos (t : ℝ) (ht : 0 < t) :
    0 < (2 / 15 : ℝ) * t - (2 / 3) * Real.log t +
      2 * Real.log ((1000 / 167 : ℝ) * (2 : ℝ) ^ (1 / 3 : ℝ)) := by
  have hL := log_constant_lower
  have h5 : Real.log (5 : ℝ) ≤ 2 := by
    apply (Real.log_le_iff_le_exp (by norm_num)).2
    have h := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 2) 4
    norm_num [Finset.sum_range_succ] at h
    linarith
  have ht5 := Real.log_le_sub_one_of_pos (by positivity : (0 : ℝ) < t / 5)
  rw [Real.log_div (ne_of_gt ht) (by norm_num)] at ht5
  linarith

private lemma log_ratio_upper (t : ℝ) (ht : 0 < t) :
    let L := Real.log ((1000 / 167 : ℝ) * (2 : ℝ) ^ (1 / 3 : ℝ))
    ((4 / 3) * Real.log t - (4 * L - Real.log 3)) /
      ((2 / 15) * t - (2 / 3) * Real.log t + 2 * L) ≤
        (9781309 / 500000000 : ℝ) := by
  dsimp only
  let L := Real.log ((1000 / 167 : ℝ) * (2 : ℝ) ^ (1 / 3 : ℝ))
  have hL : (20208105267 / 10000000000 : ℝ) ≤ L := log_constant_lower
  have hden : 0 < (2 / 15 : ℝ) * t - (2 / 3) * Real.log t + 2 * L :=
    log_ratio_den_pos t ht
  apply (div_le_iff₀ hden).2
  have htT := Real.log_le_sub_one_of_pos
    (by positivity : (0 : ℝ) < t / (5048906545 / 9781309))
  rw [Real.log_div (ne_of_gt ht) (by norm_num)] at htT
  have hT := log_tangent_upper
  have h3 := log_three_upper
  change (4 / 3 : ℝ) * Real.log t - (4 * L - Real.log 3) ≤ _
  nlinarith

theorem solution (t : ℝ) (ht : 0 < t) :
    let L := Real.log ((1000 / 167 : ℝ) * (2 : ℝ) ^ (1 / 3 : ℝ))
    let f := ((4 / 3) * Real.log t - (4 * L - Real.log 3)) /
      ((2 / 15) * t - (2 / 3) * Real.log t + 2 * L)
    f ≤ (9781309 / 500000000 : ℝ) ∧
      (217 / 800 : ℝ) * Real.log (3 + f) + (8283 / 20000) ≤ (2231 / 3125) := by
  dsimp only
  refine ⟨log_ratio_upper t ht, ?_⟩
  let L := Real.log ((1000 / 167 : ℝ) * (2 : ℝ) ^ (1 / 3 : ℝ))
  let D := (2 / 15 : ℝ) * t - (2 / 3) * Real.log t + 2 * L
  let f := ((4 / 3 : ℝ) * Real.log t - (4 * L - Real.log 3)) / D
  have hden : 0 < D := log_ratio_den_pos t ht
  have hthree : 0 < Real.log (3 : ℝ) := Real.log_pos (by norm_num)
  have hpos : 0 < 3 + f := by
    have heq : 3 + f = 1 + ((4 / 15 : ℝ) * t + Real.log 3) / D := by
      apply (mul_right_cancel₀ (ne_of_gt hden))
      dsimp only [f]
      simp only [add_mul, div_mul_cancel₀ _ (ne_of_gt hden)]
      dsimp only [D]
      ring
    rw [heq]
    positivity
  have hb : f ≤ (9781309 / 500000000 : ℝ) := log_ratio_upper t ht
  have hmono := Real.log_le_log hpos
    (show 3 + f ≤ 3 + (9781309 / 500000000 : ℝ) by linarith)
  have hnum := Real.log_div_le_sum_range_add
    (by norm_num : (0 : ℝ) ≤ 1009781309 / 2009781309)
    (by norm_num : (1009781309 / 2009781309 : ℝ) < 1) 16
  norm_num [Finset.sum_range_succ] at hnum hmono
  change (217 / 800 : ℝ) * Real.log (3 + f) + (8283 / 20000) ≤ (2231 / 3125)
  linarith

/-- The two endpoint bounds and their convex combination from (7.36)-(7.39).
The mixing coefficient is an explicit hypothesis; the remaining analytic
estimates are not assumed or asserted here. -/
theorem Helfgott.minor_arc_endpoint_coefficients (t c : ℝ) (ht : 0 < t)
    (hc0 : 0 ≤ c) (hc1 : c ≤ (2219 / 100000 : ℝ)) :
    let L₀ := Real.log (1000 / 167 : ℝ)
    let L := Real.log ((1000 / 167 : ℝ) * (2 : ℝ) ^ (1 / 3 : ℝ))
    let R₀ := (217 / 800 : ℝ) * Real.log
      (1 + ((4 / 15) * t + Real.log 3) / ((2 / 15) * t + 2 * L₀)) + 8283 / 20000
    let R₁ := (217 / 800 : ℝ) * Real.log
      (3 + ((4 / 3) * Real.log t - (4 * L - Real.log 3)) /
        ((2 / 15) * t - (2 / 3) * Real.log t + 2 * L)) + 8283 / 20000
    R₀ ≤ (14243 / 20000 : ℝ) ∧
      (1 - c) * R₀ + c * R₁ ≤ (71219 / 100000 : ℝ) := by
  dsimp only
  have hscale := log_scale_lower
  have h3 := log_three_upper
  have h3pos : 0 < Real.log (3 : ℝ) := Real.log_pos (by norm_num)
  have hd : 0 < (2 / 15 : ℝ) * t + 2 * Real.log (1000 / 167 : ℝ) := by linarith
  have hfrac : ((4 / 15 : ℝ) * t + Real.log 3) /
      ((2 / 15) * t + 2 * Real.log (1000 / 167 : ℝ)) ≤ 2 := by
    apply (div_le_iff₀ hd).2
    linarith
  have hlog := Real.log_le_log
    (by positivity : 0 < 1 + ((4 / 15 : ℝ) * t + Real.log 3) /
      ((2 / 15) * t + 2 * Real.log (1000 / 167 : ℝ)))
    (show 1 + ((4 / 15 : ℝ) * t + Real.log 3) /
      ((2 / 15) * t + 2 * Real.log (1000 / 167 : ℝ)) ≤ 3 by linarith)
  have hR₀ : (217 / 800 : ℝ) * Real.log
      (1 + ((4 / 15) * t + Real.log 3) /
        ((2 / 15) * t + 2 * Real.log (1000 / 167 : ℝ))) + 8283 / 20000 ≤
      (14243 / 20000 : ℝ) := by linarith
  refine ⟨hR₀, ?_⟩
  have hR₁ := (solution t ht).2
  have hmul₀ := mul_nonneg (show 0 ≤ 1 - c by linarith) (sub_nonneg_of_le hR₀)
  have hmul₁ := mul_nonneg hc0 (sub_nonneg_of_le hR₁)
  nlinarith only [hmul₀, hmul₁, hc1]
