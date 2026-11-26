-- Prove2me | solution 1 for Kyprianou.Ch04.exercise41ClockExactV13
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T13:00:31.467917+00:00
-- url     : https://prove2.me/submissions/a554f5f3-acb2-453b-9d95-a743e568a948

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_exercise41ClockUpperV13
import Theorems.Thm_Kyprianou_Ch04_exercise41ClockLowerV13
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Classical Topology
set_option autoImplicit false
open Kyprianou.Ch04
theorem solution
    (x : NNReal → ℝ) (q : ℕ → NNReal) (hq : DenseRange q)
    (a s : NNReal) (has : a ≤ s)
    (hr : ContinuousWithinAt x (Ici s) s) (hz : x s = 0)
    (hgap : ∀ b < s, ∃ e : ℝ, 0 < e ∧ ∀ u ∈ Icc a b, e ≤ |x u|) :
    (⨆ n : ℕ, ⨅ k : ℕ, if a ≤ q k ∧ |x (q k)| < 1 / ((n : ℝ) + 1)
      then (q k : WithTop NNReal) else ⊤) = (s : WithTop NNReal) := by
  classical
  apply le_antisymm (exercise41ClockUpperV13 x q hq a s has hr hz)
  by_contra! h
  obtain ⟨b,hb,hb'⟩ := exists_between h
  cases b with
  | top => exact (not_lt_of_ge le_top) hb'
  | coe b =>
    obtain ⟨e,he,hE⟩ := hgap b (WithTop.coe_lt_coe.mp hb')
    exact (not_lt_of_ge (exercise41ClockLowerV13 x q a b e he hE)) hb
