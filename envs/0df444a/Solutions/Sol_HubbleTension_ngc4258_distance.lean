-- Prove2me | solution 1 for HubbleTension.ngc4258_distance
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T04:29:05.799787+00:00
-- url     : https://prove2.me/submissions/a3da660a-c53d-4e4e-96c0-e8c57ef74973

import Mathlib
import Definitions.Def_HubbleTension_Defs
open HubbleTension

namespace FMAux

lemma log_bounds :
    (0.6931471803 < Real.log 2 ∧ Real.log 2 < 0.6931471808) ∧
    (1.0986122 < Real.log 3 ∧ Real.log 3 < 1.0986123) ∧
    (1.6094379 < Real.log 5 ∧ Real.log 5 < 1.6094380) := by
  set L2 := Real.log 2
  set L3 := Real.log 3
  set L5 := Real.log 5
  have a1 := Real.log_two_gt_d9
  have a2 := Real.log_two_lt_d9
  have s1 := Real.abs_log_sub_add_sum_range_le (x := 1/9) (by norm_num) 10
  have e1 : Real.log (1 - 1/9) = 3 * L2 - 2 * L3 := by
    rw [show (1 : ℝ) - 1/9 = 2^3 / 3^2 by norm_num, Real.log_div (by norm_num) (by norm_num),
      Real.log_pow, Real.log_pow]
    push_cast; ring
  have s2 := Real.abs_log_sub_add_sum_range_le (x := 1/25) (by norm_num) 8
  have e2 : Real.log (1 - 1/25) = 3 * L2 + L3 - 2 * L5 := by
    rw [show (1 : ℝ) - 1/25 = (2^3 * 3) / 5^2 by norm_num, Real.log_div (by norm_num) (by norm_num),
      Real.log_mul (by norm_num) (by norm_num), Real.log_pow, Real.log_pow]
    push_cast; ring
  rw [e1] at s1
  rw [e2] at s2
  norm_num [Finset.sum_range_succ] at s1 s2
  rw [abs_le] at s1 s2
  obtain ⟨s1a, s1b⟩ := s1
  obtain ⟨s2a, s2b⟩ := s2
  refine ⟨⟨a1, a2⟩, ⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩

lemma log10_bounds : 2.3025850 < Real.log 10 ∧ Real.log 10 < 2.3025852 := by
  obtain ⟨⟨a1, a2⟩, _, ⟨c1, c2⟩⟩ := log_bounds
  have h : Real.log 10 = Real.log 2 + Real.log 5 := by
    rw [show (10 : ℝ) = 2 * 5 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
  constructor <;> linarith

lemma rpow10 (y : ℝ) : (10 : ℝ) ^ y = Real.exp (y * Real.log 10) := by
  rw [Real.rpow_def_of_pos (by norm_num), mul_comm]

lemma d_pos (μ : ℝ) : 0 < distanceFromModulus μ := by
  unfold distanceFromModulus; positivity

lemma d_shift (μ Δ : ℝ) :
    distanceFromModulus (μ + Δ) = Real.exp (Δ / 5 * Real.log 10) * distanceFromModulus μ := by
  unfold distanceFromModulus
  rw [← rpow10, ← Real.rpow_add (by norm_num)]
  congr 1; ring

lemma d_ratio (μ Δ : ℝ) :
    distanceFromModulus (μ + Δ) / distanceFromModulus μ = Real.exp (Δ / 5 * Real.log 10) := by
  rw [d_shift, mul_div_assoc, div_self (d_pos μ).ne', mul_one]

/-- Second-order lower bound and third-order upper bound for `exp` on `[0, 1]`. -/
lemma exp_bounds (y : ℝ) (h0 : 0 ≤ y) (h1 : y ≤ 1) :
    1 + y + y ^ 2 / 2 ≤ Real.exp y ∧ Real.exp y ≤ 1 + y + y ^ 2 / 2 + y ^ 3 * (2 / 9) := by
  refine ⟨Real.quadratic_le_exp_of_nonneg h0, ?_⟩
  have h := Real.exp_bound (x := y) (by rw [abs_of_nonneg h0]; exact h1) (n := 3) (by norm_num)
  norm_num [Finset.sum_range_succ, Nat.factorial] at h
  rw [abs_of_nonneg h0] at h
  have := (abs_le.mp h).2
  linarith

end FMAux

namespace FMAux

lemma H_ratio (v μ Δ : ℝ) (hv : 0 < v) :
    hubbleConstant v (distanceFromModulus μ) / hubbleConstant v (distanceFromModulus (μ + Δ)) =
      Real.exp (Δ / 5 * Real.log 10) := by
  unfold hubbleConstant
  rw [d_shift]
  have h1 := d_pos μ
  have h3 := Real.exp_pos (Δ / 5 * Real.log 10)
  field_simp

end FMAux

namespace FMAux

lemma quad_quad (a b c : ℝ) : quadSum (quadSum a b) c = Real.sqrt (a ^ 2 + b ^ 2 + c ^ 2) := by
  unfold quadSum
  rw [Real.sq_sqrt (by positivity)]

end FMAux

open FMAux in
theorem solution :
    7.55e6 ≤ distanceFromModulus 29.397 ∧ distanceFromModulus 29.397 < 7.65e6 := by
  obtain ⟨⟨a1, a2⟩, ⟨b1, b2⟩, ⟨c1, c2⟩⟩ := log_bounds
  have hl := log10_bounds
  have hbase : Real.log 7.5e6 = 5 * Real.log 2 + Real.log 3 + 7 * Real.log 5 := by
    rw [show (7.5e6 : ℝ) = 2 ^ 5 * 3 * 5 ^ 7 by norm_num, Real.log_mul (by norm_num) (by norm_num),
      Real.log_mul (by norm_num) (by norm_num), Real.log_pow, Real.log_pow]
    push_cast; ring
  have hlo : Real.log 7.55e6 ≤ 5 * Real.log 2 + Real.log 3 + 7 * Real.log 5 + 1 / 150 := by
    rw [show (7.55e6 : ℝ) = (151 / 150) * 7.5e6 by norm_num,
      Real.log_mul (by norm_num) (by norm_num), hbase]
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 151 / 150 by norm_num)
    linarith
  have hhi : 5 * Real.log 2 + Real.log 3 + 7 * Real.log 5 + (1 - 50 / 51) ≤ Real.log 7.65e6 := by
    rw [show (7.65e6 : ℝ) = (51 / 50) * 7.5e6 by norm_num,
      Real.log_mul (by norm_num) (by norm_num), hbase]
    have := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < 51 / 50 by norm_num)
    norm_num at this ⊢
    linarith
  unfold distanceFromModulus
  constructor
  · rw [Real.le_rpow_iff_log_le (by norm_num) (by norm_num)]
    nlinarith
  · rw [← Real.log_lt_log_iff (by positivity) (by norm_num), Real.log_rpow (by norm_num)]
    nlinarith
