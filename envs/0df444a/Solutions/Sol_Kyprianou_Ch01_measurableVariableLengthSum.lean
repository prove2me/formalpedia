-- Prove2me | solution 1 for Kyprianou.Ch01.measurableVariableLengthSum
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T07:38:23.377708+00:00
-- url     : https://prove2.me/submissions/d72991b5-bd08-4ace-b436-6342ad01ebd5

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped BigOperators
set_option autoImplicit false

/-! Countable piecewise definition of a measurable finite-sum functional. -/
theorem solution :
    Measurable (fun pair : ℕ × (ℕ → ℝ) =>
      ∑ i ∈ Finset.range pair.1, pair.2 i) := by
  have heq :
      (fun pair : ℕ × (ℕ → ℝ) =>
        ∑ i ∈ Finset.range pair.1, pair.2 i) =
      (fun pair : ℕ × (ℕ → ℝ) =>
        ∑' n : ℕ,
          if pair.1 = n then
            (∑ i ∈ Finset.range n, pair.2 i)
          else 0) := by
    funext pair
    symm
    rw [tsum_eq_single pair.1]
    · simp
    · intro n hn
      simp [Ne.symm hn]
  rw [heq]
  apply Measurable.tsum
  intro n
  have hn : Measurable (fun pair : ℕ × (ℕ → ℝ) =>
      ∑ i ∈ Finset.range n, pair.2 i) := by
    fun_prop
  have hset : MeasurableSet {pair : ℕ × (ℕ → ℝ) | pair.1 = n} :=
    measurableSet_eq_fun measurable_fst measurable_const
  exact Measurable.ite hset hn measurable_const
