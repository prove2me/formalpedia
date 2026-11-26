-- Prove2me | solution 1 for Kyprianou.Ch04.exercise41ClockCoverV14
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T13:07:05.809348+00:00
-- url     : https://prove2.me/submissions/8c3b8287-591b-405b-9961-a5882405cd82

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_exercise41IsolatedZeroCutoffV13
import Theorems.Thm_Kyprianou_Ch04_exercise41ClockExactV13
import Theorems.Thm_Kyprianou_Ch04_exercise41GapNonzeroV14
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Classical Topology
set_option autoImplicit false
open Kyprianou.Ch04
theorem solution
    (x : NNReal → ℝ) (q : ℕ → NNReal) (hq : DenseRange q)
    (hR : ∀ s, ContinuousWithinAt x (Ici s) s)
    (hL : ∀ s, 0 < s → ∃ l, Tendsto x (nhdsWithin s (Iio s)) (nhds l))
    (hNoJump : ∀ s, 0 < s → Function.leftLim x s = 0 → x s = 0)
    (hVisits : ∀ t, Set.Finite {u : NNReal | 0 < u ∧ u ≤ t ∧ x u = 0}) :
    let raw (j : ℕ) : WithTop NNReal := ⨆ n : ℕ, ⨅ k : ℕ,
      if q j ≤ q k ∧ |x (q k)| < 1 / ((n : ℝ) + 1) then (q k : WithTop NNReal) else ⊤
    ∀ s : NNReal, x s = 0 → ∃ j N : ℕ,
      (min (raw j) ((N : NNReal) : WithTop NNReal)).untopD 0 = s := by
  classical
  let raw (j : ℕ) : WithTop NNReal := ⨆ n : ℕ, ⨅ k : ℕ,
    if q j ≤ q k ∧ |x (q k)| < 1 / ((n : ℝ) + 1) then (q k : WithTop NNReal) else ⊤
  change ∀ s : NNReal, x s = 0 → ∃ j N : ℕ,
    (min (raw j) ((N : NNReal) : WithTop NNReal)).untopD 0 = s
  intro s hz
  by_cases hs : s = 0
  · refine ⟨0,0,?_⟩
    have hb : ((0 : NNReal) : WithTop NNReal) ≤ raw 0 := bot_le
    rw [hs, Nat.cast_zero]
    change (min (raw 0) ((0 : NNReal) : WithTop NNReal)).untopD 0 = 0
    rw [min_eq_right hb] <;> rfl
  have hp : 0 < s := bot_lt_iff_ne_bot.mpr hs
  obtain ⟨j,hj,hjs,hgap⟩ := exercise41IsolatedZeroCutoffV13 x q hq s hp (hVisits s)
  have he : raw j = (s : WithTop NNReal) := exercise41ClockExactV13 x q hq
    (q j) s hjs.le (hR s) hz (fun b hb => exercise41GapNonzeroV14 x (q j) b hj
      hR hL hNoJump (fun u hu => hgap u ⟨hu.1,hu.2.trans_lt hb⟩))
  obtain ⟨N,hN⟩ := exists_nat_ge s
  refine ⟨j,N,?_⟩
  rw [he, min_eq_left (WithTop.coe_le_coe.mpr hN)] <;> rfl
