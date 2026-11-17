-- Prove2me | solution 1 for Kyprianou.Ch01.passageApproxEpsilonCofinal
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T19:14:54.013794+00:00
-- url     : https://prove2.me/submissions/64449613-2db5-4760-b19b-f2f507291c59

import Mathlib.Data.NNReal.Defs
import Mathlib.Order.Filter.Defs
import Mathlib.Tactic.Positivity
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set Filter
open scoped NNReal
set_option autoImplicit false

theorem solution (t v : ℝ≥0) (htv : t < v) :
    ∀ e : ℝ≥0, 0 < e →
      ∃ n : ℕ, (v - t) / ((n : ℝ≥0) + 2) < e := by
  intro e he
  obtain ⟨n, hn⟩ := exists_nat_gt ((v - t : ℝ≥0) / e : ℝ)
  refine ⟨n, ?_⟩
  apply (div_lt_iff₀ (by positivity : (0 : ℝ≥0) < (n : ℝ≥0) + 2)).2
  have hn' : (v - t : ℝ≥0) / e < (n : ℝ≥0) + 2 := by
    exact_mod_cast (show (v - t : ℝ≥0) / e < (n : ℝ) + 2 by
      exact lt_trans hn (by norm_num))
  have hmul : v - t < ((n : ℝ≥0) + 2) * e :=
    (div_lt_iff₀ he).1 hn'
  simpa only [mul_comm] using hmul
