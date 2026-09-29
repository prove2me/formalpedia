-- Prove2me | solution 1 for MarkovChainCLT.sum_geometric_lag_le
-- status  : ACCEPTED   (prove)
-- author  : @LukeBernese
-- created : 2026-08-16T00:39:01.610131+00:00
-- url     : https://prove2.me/submissions/b4c54f2b-383d-4037-bea9-e9d4fc1abbe1

import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.SpecificLimits.Basic

open Finset

set_option maxHeartbeats 1000000

theorem solution (N : ℕ) (hN : 1 ≤ N) (n j : ℕ) (hj : j < n) :
    ∑ k ∈ Finset.range n, (1 / 2 : ℝ) ^ ((max j k - min j k) / N) ≤ 4 * N := by
  classical
  set a : ℕ → ℝ := fun d => (1 / 2 : ℝ) ^ (d / N) with ha
  have ha0 : ∀ d, 0 ≤ a d := by intro d; rw [ha]; positivity
  -- the block sum
  have hblock : ∀ q : ℕ, ∑ d ∈ Finset.range (q * N), a d ≤ 2 * N * (1 - (1 / 2 : ℝ) ^ q) := by
    intro q
    induction q with
    | zero => simp
    | succ p ih =>
        have hsplit : (p + 1) * N = p * N + N := by ring
        rw [hsplit, Finset.sum_range_add]
        have hinner : ∑ i ∈ Finset.range N, a (p * N + i) = (N : ℝ) * (1 / 2 : ℝ) ^ p := by
          have hterm : ∀ i ∈ Finset.range N, a (p * N + i) = (1 / 2 : ℝ) ^ p := by
            intro i hi
            have hiN : i < N := Finset.mem_range.mp hi
            have h1 : (p * N + i) / N = p := by
              rw [Nat.mul_comm, Nat.add_comm]
              rw [Nat.add_mul_div_left _ _ (by omega : 0 < N)]
              rw [Nat.div_eq_of_lt hiN]
              omega
            rw [ha]
            simp only
            rw [h1]
          rw [Finset.sum_congr rfl hterm, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        rw [hinner]
        have hpow : (0 : ℝ) < (1 / 2 : ℝ) ^ p := by positivity
        have hNR : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
        have hgoal : 2 * (N : ℝ) * (1 - (1 / 2 : ℝ) ^ p) + (N : ℝ) * (1 / 2 : ℝ) ^ p
            = 2 * (N : ℝ) * (1 - (1 / 2 : ℝ) ^ (p + 1)) := by
          rw [pow_succ]
          ring
        linarith [ih, hgoal]
  have hgeo : ∀ m : ℕ, ∑ d ∈ Finset.range m, a d ≤ 2 * N := by
    intro m
    have hmn : m ≤ m * N := Nat.le_mul_of_pos_right m (by omega : 0 < N)
    have hsub : Finset.range m ⊆ Finset.range (m * N) := by
      intro x hx
      exact Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hx) hmn)
    have h1 : ∑ d ∈ Finset.range m, a d ≤ ∑ d ∈ Finset.range (m * N), a d :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun d _ _ => ha0 d)
    have h2 := hblock m
    have hpow : (0 : ℝ) < (1 / 2 : ℝ) ^ m := by positivity
    have hNR : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
    nlinarith [h1, h2, hpow, hNR]
  -- split the sum at `j`
  rw [← Finset.sum_filter_add_sum_filter_not (Finset.range n) (fun k => k ≤ j)]
  have hle : ∑ k ∈ (Finset.range n).filter (fun k => k ≤ j), a (max j k - min j k)
      ≤ ∑ d ∈ Finset.range n, a d := by
    have hcongr : ∀ k ∈ (Finset.range n).filter (fun k => k ≤ j),
        a (max j k - min j k) = a (j - k) := by
      intro k hk
      have hkj : k ≤ j := (Finset.mem_filter.mp hk).2
      rw [max_eq_left hkj, min_eq_right hkj]
    rw [Finset.sum_congr rfl hcongr]
    have hinj : ∀ x ∈ (Finset.range n).filter (fun k => k ≤ j),
        ∀ y ∈ (Finset.range n).filter (fun k => k ≤ j), j - x = j - y → x = y := by
      intro x hx y hy hxy
      have hx' : x ≤ j := (Finset.mem_filter.mp hx).2
      have hy' : y ≤ j := (Finset.mem_filter.mp hy).2
      omega
    rw [← Finset.sum_image hinj]
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun d _ _ => ha0 d)
    intro d hd
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hd
    have hkj : k ≤ j := (Finset.mem_filter.mp hk).2
    exact Finset.mem_range.mpr (by omega)
  have hgt : ∑ k ∈ (Finset.range n).filter (fun k => ¬ k ≤ j), a (max j k - min j k)
      ≤ ∑ d ∈ Finset.range n, a d := by
    have hcongr : ∀ k ∈ (Finset.range n).filter (fun k => ¬ k ≤ j),
        a (max j k - min j k) = a (k - j) := by
      intro k hk
      have hkj : ¬ k ≤ j := (Finset.mem_filter.mp hk).2
      have hkj' : j ≤ k := by omega
      rw [max_eq_right hkj', min_eq_left hkj']
    rw [Finset.sum_congr rfl hcongr]
    have hinj : ∀ x ∈ (Finset.range n).filter (fun k => ¬ k ≤ j),
        ∀ y ∈ (Finset.range n).filter (fun k => ¬ k ≤ j), x - j = y - j → x = y := by
      intro x hx y hy hxy
      have hx' : ¬ x ≤ j := (Finset.mem_filter.mp hx).2
      have hy' : ¬ y ≤ j := (Finset.mem_filter.mp hy).2
      omega
    rw [← Finset.sum_image hinj]
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun d _ _ => ha0 d)
    intro d hd
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hd
    have hkn : k < n := Finset.mem_range.mp (Finset.mem_filter.mp hk).1
    exact Finset.mem_range.mpr (by omega)
  have hg := hgeo n
  linarith [hle, hgt, hg]
