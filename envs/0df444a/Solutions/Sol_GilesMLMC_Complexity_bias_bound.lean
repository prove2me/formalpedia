-- Prove2me | solution 1 for GilesMLMC.Complexity.bias_bound
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T02:36:13.725065+00:00
-- url     : https://prove2.me/submissions/ad05ba63-99c1-4f19-91f4-6e757905c49c

import Mathlib
import Definitions.Def_GilesMLMC_Complexity_Setup

set_option autoImplicit false
open GilesMLMC.Complexity

theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω)
    [MeasureTheory.IsProbabilityMeasure μ]
    (M : ℕ) (T : ℝ) (α c₁ ε : ℝ) (hε : 0 < ε)
    (P : Ω → ℝ) (Phat : ℕ → Ω → ℝ) (Y : ℕ → ℕ → Ω → ℝ)
    (hP : MeasureTheory.Integrable P μ)
    (hPhat : ∀ l, MeasureTheory.Integrable (Phat l) μ)
    (hY : ∀ l N, 1 ≤ N → MeasureTheory.MemLp (Y l N) 2 μ)
    (h_i : ∀ l, |∫ ω, (Phat l ω - P ω) ∂μ| ≤ c₁ * h M T l ^ α)
    (h_ii : ∀ l N, 1 ≤ N → ∫ ω, Y l N ω ∂μ =
      if l = 0 then ∫ ω, Phat 0 ω ∂μ else ∫ ω, (Phat l ω - Phat (l - 1) ω) ∂μ)
    (L : ℕ) (N : ℕ → ℕ) (hN : ∀ l, 1 ≤ N l)
    (hL : c₁ * h M T L ^ α ≤ ε / Real.sqrt 2) :
    (∫ ω, estimator Y N L ω ∂μ - ∫ ω, P ω ∂μ) ^ 2 ≤ ε ^ 2 / 2 := by
  have hint : ∀ l, MeasureTheory.Integrable (Y l (N l)) μ := fun l =>
    (hY l (N l) (hN l)).integrable (by norm_num)
  have hsum : ∫ ω, estimator Y N L ω ∂μ = ∑ l ∈ Finset.range (L + 1), ∫ ω, Y l (N l) ω ∂μ := by
    unfold estimator
    exact MeasureTheory.integral_finset_sum _ (fun l _ => hint l)
  have htel : ∀ m : ℕ, ∑ l ∈ Finset.range (m + 1), ∫ ω, Y l (N l) ω ∂μ = ∫ ω, Phat m ω ∂μ := by
    intro m
    induction m with
    | zero =>
      simp [h_ii 0 (N 0) (hN 0)]
    | succ m ih =>
      rw [Finset.sum_range_succ, ih, h_ii (m + 1) (N (m + 1)) (hN _)]
      simp only [Nat.succ_ne_zero, if_false, Nat.add_sub_cancel]
      rw [MeasureTheory.integral_sub (hPhat _) (hPhat _)]
      ring
  have hx : ∫ ω, estimator Y N L ω ∂μ - ∫ ω, P ω ∂μ = ∫ ω, (Phat L ω - P ω) ∂μ := by
    rw [hsum, htel, MeasureTheory.integral_sub (hPhat _) hP]
  rw [hx]
  have hb : |∫ ω, (Phat L ω - P ω) ∂μ| ≤ ε / Real.sqrt 2 := (h_i L).trans hL
  calc (∫ ω, (Phat L ω - P ω) ∂μ) ^ 2 = |∫ ω, (Phat L ω - P ω) ∂μ| ^ 2 := (sq_abs _).symm
    _ ≤ (ε / Real.sqrt 2) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hb 2
    _ = ε ^ 2 / 2 := by
        rw [div_pow, Real.sq_sqrt (by norm_num)]
