-- Prove2me | solution 1 for MeasureTheory.tendsto_integral_sq_sub_truncation
-- status  : ACCEPTED   (prove)
-- author  : @LukeBernese
-- created : 2026-08-16T01:29:17.661195+00:00
-- url     : https://prove2.me/submissions/c4f8b7de-fbfd-48b7-b861-38a0308129b7

import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.DominatedConvergence

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Topology

set_option maxHeartbeats 2000000

theorem solution {X : Type*} [MeasurableSpace X] (π : Measure X) [IsProbabilityMeasure π]
    (f : X → ℝ) (hf : Measurable f) (hL2 : Integrable (fun x => (f x) ^ 2) π) :
    Tendsto (fun K : ℕ => ∫ x, (f x - max (min (f x) (K : ℝ)) (-(K : ℝ))) ^ 2 ∂π)
      atTop (𝓝 0) := by
  classical
  set F : ℕ → X → ℝ := fun K x => (f x - max (min (f x) (K : ℝ)) (-(K : ℝ))) ^ 2 with hF
  -- pointwise bound on the truncation error
  have htrunc : ∀ (y : ℝ) (K : ℝ), 0 ≤ K → |y - max (min y K) (-K)| ≤ |y| := by
    intro y K hK
    rcases le_total y K with h1 | h1
    · rcases le_total (-K) y with h2 | h2
      · rw [min_eq_left h1, max_eq_left h2]
        simp
      · rw [min_eq_left h1, max_eq_right h2]
        rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]
        linarith
    · rw [min_eq_right h1, max_eq_left (by linarith)]
      rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
      linarith
  have hFmeas : ∀ K : ℕ, AEStronglyMeasurable (F K) π := by
    intro K
    exact ((hf.sub (((hf.min measurable_const).max measurable_const))).pow_const
      2).aestronglyMeasurable
  have hFbd : ∀ K : ℕ, ∀ᵐ x ∂π, ‖F K x‖ ≤ (f x) ^ 2 := by
    intro K
    filter_upwards with x
    have h := htrunc (f x) (K : ℝ) (Nat.cast_nonneg K)
    rw [hF]
    simp only
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have h2 : |f x - max (min (f x) (K : ℝ)) (-(K : ℝ))| ^ 2 ≤ |f x| ^ 2 := by
      nlinarith [abs_nonneg (f x - max (min (f x) (K : ℝ)) (-(K : ℝ))), abs_nonneg (f x), h]
    rwa [sq_abs, sq_abs] at h2
  have hFlim : ∀ᵐ x ∂π, Tendsto (fun K : ℕ => F K x) atTop (𝓝 0) := by
    filter_upwards with x
    obtain ⟨K0, hK0⟩ := exists_nat_gt |f x|
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop K0] with K hK
    have hKR : |f x| ≤ (K : ℝ) := by
      have : (K0 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK
      linarith
    have h1 : f x ≤ (K : ℝ) := le_trans (le_abs_self _) hKR
    have h2 : -(K : ℝ) ≤ f x := by
      have := neg_abs_le (f x)
      linarith
    rw [hF]
    simp only
    rw [min_eq_left h1, max_eq_left h2]
    simp
  have := tendsto_integral_of_dominated_convergence (fun x => (f x) ^ 2) hFmeas hL2 hFbd hFlim
  simpa using this
