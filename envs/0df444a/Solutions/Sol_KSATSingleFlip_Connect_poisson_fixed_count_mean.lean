-- Prove2me | solution 1 for KSATSingleFlip.Connect.poisson_fixed_count_mean
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T09:49:12.790586+00:00
-- url     : https://prove2.me/submissions/d2f73a41-06e1-4532-9c79-cddf6a0c38a2

import Theorems.Thm_KSATSingleFlip_Connect_poisson_deviation_integrable
import Theorems.Thm_KSATSingleFlip_Connect_count_mean_lipschitz
import Mathlib
open MeasureTheory ProbabilityTheory
open scoped NNReal
set_option autoImplicit false

private theorem count_lipschitz (g : ℕ → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (hstep : ∀ n, |g (n+1) - g n| ≤ L) :
    ∀ j k, |g j-g k| ≤ L*|(j:ℝ)-(k:ℝ)| := by
  have hmono : ∀ n m, n ≤ m → |g m-g n| ≤ L*((m:ℝ)-(n:ℝ)) := by
    intro n m hnm
    induction m, hnm using Nat.le_induction with
    | base => simp
    | succ m hnm ih =>
      calc
        |g (m+1)-g n| ≤ |g (m+1)-g m| + |g m-g n| := abs_sub_le _ _ _
        _ ≤ L + L*((m:ℝ)-(n:ℝ)) := add_le_add (hstep m) ih
        _ = L*((((m+1):ℕ):ℝ)-(n:ℝ)) := by push_cast; ring
  intro j k
  by_cases h : j ≤ k
  · have hm := hmono j k h
    rw [abs_sub_comm (g j), abs_sub_comm (j:ℝ)]
    rw [abs_of_nonneg (sub_nonneg.mpr (by exact_mod_cast h) : (0:ℝ) ≤ (k:ℝ)-(j:ℝ))]
    exact hm
  · have h' : k ≤ j := by omega
    have hm := hmono k j h'
    rw [abs_of_nonneg (sub_nonneg.mpr (by exact_mod_cast h') : (0:ℝ) ≤ (j:ℝ)-(k:ℝ))]
    exact hm


theorem solution (r : ℝ≥0) (g : ℕ → ℝ) (hg : Integrable g (poissonMeasure r))
    (L : ℝ) (hL : 0 ≤ L) (hstep : ∀ j, |g (j+1)-g j| ≤ L) (j : ℕ) :
    |g j - ∫ k, g k ∂(poissonMeasure r)| ≤ L*(|(j:ℝ)-(r:ℝ)|+Real.sqrt (r:ℝ)) := by
  obtain ⟨hi,hmean⟩ := KSATSingleFlip.Connect.poisson_deviation_integrable r
  exact KSATSingleFlip.Connect.count_mean_lipschitz (poissonMeasure r) g hg L r (Real.sqrt r)
    hL hi hmean (count_lipschitz g L hL hstep) j
