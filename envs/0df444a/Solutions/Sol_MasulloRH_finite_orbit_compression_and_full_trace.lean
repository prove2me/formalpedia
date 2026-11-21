-- Prove2me | solution 1 for MasulloRH.finite_orbit_compression_and_full_trace
-- status  : ACCEPTED   (prove)
-- author  : @Yi
-- created : 2026-11-21T01:18:01.694184+00:00
-- url     : https://prove2.me/submissions/773cb405-7b3e-40b8-99d8-c0ebdcf3cf43

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Complex.Basic

import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

open Finset

private theorem shiftCounts (n d : ℕ) (hn : 0 < n) :
    (∑ i ∈ range n, ∑ j ∈ range n,
        if j = i+d then (1 : ℂ) else 0) / (n : ℂ) = ((n-d : ℕ) : ℂ) / n ∧
    (∑ i ∈ range n, if i = i+d then (1 : ℂ) else 0) / (n : ℂ) =
      if d = 0 then 1 else 0 := by
  constructor
  · congr 1
    simp only [Finset.sum_ite_eq', Finset.mem_range]
    have h (i : ℕ) : i+d<n ↔ i<n-d := by omega
    simp_rw [h]
    have inter : (range n).filter (fun i => i<n-d) = range (n-d) := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_range]
      omega
    rw [← Finset.sum_filter, inter]
    simp
  · by_cases hd : d = 0
    · subst d
      simp [Nat.ne_of_gt hn]
    · simp [hd]

theorem solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (n : ℕ) (hn : 0 < n) (T : Finset ℕ) (A : ℕ → E) :
    (∀ d : ℕ, (∑ i ∈ range n, ∑ j ∈ range n,
        if j = i+d then (1 : ℂ) else 0) / (n : ℂ) = ((n-d : ℕ) : ℂ) / n ∧
      (∑ i ∈ range n, if i = i+d then (1 : ℂ) else 0) / (n : ℂ) =
        if d = 0 then 1 else 0) ∧
    ‖(∑ d ∈ T, (((n-d : ℕ) : ℝ) / n) • A d) - ∑ d ∈ T, A d‖ ≤
      (∑ d ∈ T, (d : ℝ) * ‖A d‖) / n := by
  refine ⟨fun d => shiftCounts n d hn, ?_⟩
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  rw [← Finset.sum_sub_distrib, div_eq_mul_inv, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun d _ => ?_)
  have heq : (((n-d : ℕ) : ℝ) / n) • A d - A d =
      ((((n-d : ℕ) : ℝ) / n) - 1) • A d := by rw [sub_smul, one_smul]
  rw [heq, norm_smul, Real.norm_eq_abs]
  have hle : (((n-d : ℕ) : ℝ) / n) ≤ 1 := by
    apply (div_le_one hn').2
    exact_mod_cast Nat.sub_le n d
  rw [abs_of_nonpos (sub_nonpos.mpr hle)]
  rw [← div_eq_mul_inv]
  apply (le_div_iff₀ hn').2
  have hcancel : (((n-d : ℕ) : ℝ) / n) * n = ((n-d : ℕ) : ℝ) := div_mul_cancel₀ _ hn'.ne'
  have hdiff : (n : ℝ) - ((n-d : ℕ) : ℝ) ≤ (d : ℝ) := by
    have h : n ≤ n-d+d := by omega
    exact sub_le_iff_le_add'.mpr (by exact_mod_cast h)
  calc
    _ = ((n : ℝ) - ((n-d : ℕ) : ℝ)) * ‖A d‖ := by
      calc
        _ = ((n : ℝ) - (((n-d : ℕ) : ℝ) / n)*n) * ‖A d‖ := by ring
        _ = _ := by rw [hcancel]
    _ ≤ _ := mul_le_mul_of_nonneg_right hdiff (norm_nonneg _)
