-- Prove2me | solution 1 for Kyprianou.Ch02.equalGridCeilIndexBoundsV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T23:45:45.463797+00:00
-- url     : https://prove2.me/submissions/50ba9431-9fab-4bfa-a5c7-2f74fd90fda6

import Mathlib.MeasureTheory.SetSemiring
import Mathlib.Probability.ConditionalProbability
import Mathlib.Tactic.Positivity
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem solution
    (a b : ℝ≥0) (hab : a < b) :
    let g : ℕ → ℕ → ℝ≥0 := fun n k =>
      a + (b - a) * (k : ℝ≥0) / ((n + 1 : ℕ) : ℝ≥0)
    let q : ℕ → ℝ≥0 → ℝ≥0 := fun n x =>
      (x-a)*((n+1 : ℕ) : ℝ≥0)/(b-a)
    (∀ n x, x ∈ Icc a b → ⌈q n x⌉₊ ≤ n+1) ∧
    ∀ n k, ⌈q n (g n k)⌉₊ = k := by
  dsimp only
  have hd : 0 < b-a := tsub_pos_of_lt hab
  constructor
  · intro n x hx
    apply Nat.ceil_le.mpr
    apply (div_le_iff₀ hd).2
    rw [mul_comm ((n+1 : ℕ) : ℝ≥0)]
    gcongr
    exact hx.2
  · intro n k
    rw [add_tsub_cancel_left]
    have hn : ((n+1 : ℕ) : ℝ≥0) ≠ 0 := by positivity
    have he : (b-a)* (k : ℝ≥0) / ((n+1 : ℕ) : ℝ≥0) *
        ((n+1 : ℕ) : ℝ≥0) / (b-a) = (k : ℝ≥0) := by
      field_simp
    rw [he, Nat.ceil_natCast]
