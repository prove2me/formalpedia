-- Prove2me | solution 1 for NatureSLT.Kernels.spline_kernel
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T12:24:47.235927+00:00
-- url     : https://prove2.me/submissions/ae47bcb4-fb64-48b3-a773-25ede78c2e46

import Mathlib
import Definitions.Def_NatureSLT_Kernels_truncPow

open NatureSLT.Kernels

theorem g69f_int_pow_sub (x : ℝ) (k : ℕ) :
    ∫ t in (0:ℝ)..x, (x - t) ^ k = x ^ (k + 1) / (k + 1) := by
  rw [intervalIntegral.integral_comp_sub_left (fun s => s ^ k) x, integral_pow]
  simp

theorem g69f_core (xi xj : ℝ) (d : ℕ) :
    ∫ t in (0:ℝ)..xi, (xj - t) ^ d * (xi - t) ^ d =
      ∑ r ∈ Finset.range (d + 1),
        (d.choose r : ℝ) / (2 * (d : ℝ) - r + 1) * xi ^ (2 * d - r + 1) * (xj - xi) ^ r := by
  have hexp : ∀ t : ℝ, (xj - t) ^ d * (xi - t) ^ d =
      ∑ r ∈ Finset.range (d + 1), ((xj - xi) ^ r * (d.choose r : ℝ)) * (xi - t) ^ (d - r + d) := by
    intro t
    rw [show xj - t = (xj - xi) + (xi - t) by ring, add_pow, Finset.sum_mul]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [pow_add]; ring
  simp_rw [hexp]
  rw [intervalIntegral.integral_finset_sum]
  · refine Finset.sum_congr rfl fun r hr => ?_
    have hrd : r ≤ d := Nat.lt_succ_iff.mp (Finset.mem_range.mp hr)
    rw [intervalIntegral.integral_const_mul, g69f_int_pow_sub]
    have h1 : d - r + d + 1 = 2 * d - r + 1 := by omega
    have h2 : ((d - r + d : ℕ) : ℝ) + 1 = 2 * (d : ℝ) - r + 1 := by
      rw [Nat.cast_add, Nat.cast_sub hrd]; ring
    rw [h1, h2]; ring
  · intro r _
    exact (Continuous.intervalIntegrable (by fun_prop) _ _)

theorem g69f_trunc_prod (d : ℕ) (xj xi t : ℝ) :
    truncPow d xj t * truncPow d xi t =
      if t < min xj xi then (xj - t) ^ d * (xi - t) ^ d else 0 := by
  unfold truncPow
  by_cases h : t < min xj xi
  · rw [if_pos h, if_neg (by have := min_le_left xj xi; linarith),
      if_neg (by have := min_le_right xj xi; linarith)]
  · rw [if_neg h]
    rw [lt_min_iff, not_and_or] at h
    rcases h with h | h
    · rw [if_pos (not_lt.mp h)]; simp
    · rw [if_pos (not_lt.mp h)]; simp

theorem g69f_integral (a : ℝ) (xj xi : ℝ) (hxj : xj ∈ Set.Icc 0 a) (hxi : xi ∈ Set.Icc 0 a) (d : ℕ) :
    ∫ t in (0 : ℝ)..a, truncPow d xj t * truncPow d xi t =
      ∫ t in (0 : ℝ)..(min xj xi), (xj - t) ^ d * (xi - t) ^ d := by
  simp_rw [g69f_trunc_prod]
  set m := min xj xi
  have hm0 : 0 ≤ m := le_min hxj.1 hxi.1
  have hma : m ≤ a := (min_le_left _ _).trans hxj.2
  have hint : ∀ u v : ℝ, IntervalIntegrable
      (fun t => if t < m then (xj - t) ^ d * (xi - t) ^ d else 0) MeasureTheory.volume u v := by
    intro u v
    refine (IntervalIntegrable.mono_fun (f := fun t => (|xj - t| ^ d * |xi - t| ^ d)) 
      (Continuous.intervalIntegrable (by fun_prop) u v) ?_ ?_)
    · exact (Measurable.ite measurableSet_Iio (by fun_prop) measurable_const).aestronglyMeasurable
    · refine Filter.Eventually.of_forall fun t => ?_
      show ‖if t < m then (xj - t) ^ d * (xi - t) ^ d else 0‖ ≤ ‖|xj - t| ^ d * |xi - t| ^ d‖
      split_ifs
      · simp [abs_mul, abs_pow]
      · simp; positivity
  rw [← intervalIntegral.integral_add_adjacent_intervals (hint 0 m) (hint m a)]
  have h2 : ∫ t in m..a, (if t < m then (xj - t) ^ d * (xi - t) ^ d else 0) = 0 := by
    rw [intervalIntegral.integral_congr (g := fun _ => (0:ℝ))]
    · simp
    · intro t ht
      rw [Set.uIcc_of_le hma] at ht
      simp [not_lt.mpr ht.1]
  rw [h2, add_zero]
  refine intervalIntegral.integral_congr_ae ?_
  have hne : ∀ᵐ t ∂MeasureTheory.volume, t ≠ m := by
    rw [MeasureTheory.ae_iff]; simp
  filter_upwards [hne] with t ht htm
  rw [Set.uIoc_of_le hm0] at htm
  rw [if_pos (lt_of_le_of_ne htm.2 ht)]

theorem g69f_main (a : ℝ) (xj xi : ℝ) (hxj : xj ∈ Set.Icc 0 a) (hxi : xi ∈ Set.Icc 0 a) (d : ℕ) :
    ∫ t in (0 : ℝ)..a, truncPow d xj t * truncPow d xi t =
      ∑ r ∈ Finset.range (d + 1),
        (d.choose r : ℝ) / (2 * (d : ℝ) - r + 1) * min xj xi ^ (2 * d - r + 1) * |xj - xi| ^ r := by
  rw [g69f_integral a xj xi hxj hxi d]
  rcases le_total xi xj with h | h
  · rw [min_eq_right h, abs_of_nonneg (by linarith), g69f_core]
  · rw [min_eq_left h, abs_of_nonpos (by linarith), neg_sub]
    simp_rw [mul_comm ((xj - _) ^ d)]
    rw [g69f_core]

theorem solution (a : ℝ) (ha : 0 < a) (xj xi : ℝ) (hxj : xj ∈ Set.Icc 0 a)
    (hxi : xi ∈ Set.Icc 0 a) :
    (∀ d : ℕ,
      (∫ t in (0 : ℝ)..a, truncPow d xj t * truncPow d xi t) +
          ∑ r ∈ Finset.range (d + 1), xj ^ r * xi ^ r =
        ∑ r ∈ Finset.range (d + 1),
            (d.choose r : ℝ) / (2 * (d : ℝ) - r + 1) * min xj xi ^ (2 * d - r + 1) *
              |xj - xi| ^ r +
          ∑ r ∈ Finset.range (d + 1), xj ^ r * xi ^ r) ∧
    (∫ t in (0 : ℝ)..a, truncPow 1 xj t * truncPow 1 xi t) +
        ∑ r ∈ Finset.range 2, xj ^ r * xi ^ r =
      1 + xj * xi + 1 / 2 * |xj - xi| * min xj xi ^ 2 + min xj xi ^ 3 / 3 := by
  refine ⟨fun d => by rw [g69f_main a xj xi hxj hxi d], ?_⟩
  rw [g69f_main a xj xi hxj hxi 1]
  simp [Finset.sum_range_succ]
  ring
