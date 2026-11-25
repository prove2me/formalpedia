-- Prove2me | solution 1 for Kyprianou.Ch04.kw47_monotone_exp_unit_variation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T19:39:48.623436+00:00
-- url     : https://prove2.me/submissions/1e9ea26d-72bf-4afe-a18b-84a8381c6d9b

import Mathlib.Analysis.Complex.Exponential
open Filter
open scoped NNReal
set_option autoImplicit false

/-- An exponential of a nonnegative increasing path has total
variation at most one on every ordered finite grid. -/
theorem solution
    (U : NNReal → Real) (hU : Monotone U)
    (hNonneg : ∀ t, 0 ≤ U t)
    (alpha : Real) (hAlpha : 0 ≤ alpha)
    (u : ℕ → NNReal) (hu : Monotone u)
    (n : ℕ) :
    (∑ i ∈ Finset.range n,
      |Real.exp (-alpha * U (u (i + 1))) -
       Real.exp (-alpha * U (u i))|) ≤ 1 := by
  let g : ℕ → Real := fun i => Real.exp (-alpha * U (u i))
  have hgmono (i : ℕ) : g (i + 1) ≤ g i := by
    dsimp [g]
    apply Real.exp_le_exp.mpr
    have h := mul_le_mul_of_nonneg_left (hU (hu (Nat.le_succ i))) hAlpha
    linarith
  have hsum (k : ℕ) :
      (∑ i ∈ Finset.range k, (g i - g (i + 1))) = g 0 - g k := by
    induction k with
    | zero => simp
    | succ k ih =>
        rw [Finset.sum_range_succ, ih]
        ring
  have h0 : g 0 ≤ 1 := by
    change Real.exp (-alpha * U (u 0)) ≤ 1
    have h : -alpha * U (u 0) ≤ 0 := by
      have hp := mul_nonneg hAlpha (hNonneg (u 0))
      linarith
    have hh := Real.exp_le_exp.mpr h
    simpa using hh
  have hn : 0 ≤ g n := Real.exp_nonneg _
  calc
    (∑ i ∈ Finset.range n,
      |Real.exp (-alpha * U (u (i + 1))) -
        Real.exp (-alpha * U (u i))|)
        = ∑ i ∈ Finset.range n, (g i - g (i + 1)) := by
          apply Finset.sum_congr rfl
          intro i hi
          change |g (i + 1) - g i| = g i - g (i + 1)
          rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr (hgmono i))]
    _ = g 0 - g n := hsum n
    _ ≤ 1 := by linarith
