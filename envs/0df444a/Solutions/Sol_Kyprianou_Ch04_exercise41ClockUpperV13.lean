-- Prove2me | solution 1 for Kyprianou.Ch04.exercise41ClockUpperV13
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T13:00:19.716676+00:00
-- url     : https://prove2.me/submissions/1cf88c76-0f47-434e-847a-018840635c1f

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_exercise41DenseRightHitV4
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Classical Topology
set_option autoImplicit false
open Kyprianou.Ch04
theorem solution
    (x : NNReal → ℝ) (q : ℕ → NNReal) (hq : DenseRange q)
    (a s : NNReal) (has : a ≤ s)
    (hr : ContinuousWithinAt x (Ici s) s) (hz : x s = 0) :
    (⨆ n : ℕ, ⨅ k : ℕ, if a ≤ q k ∧ |x (q k)| < 1 / ((n : ℝ) + 1)
      then (q k : WithTop NNReal) else ⊤) ≤ (s : WithTop NNReal) := by
  classical
  apply iSup_le
  intro n
  by_contra! h
  obtain ⟨b,hb,hb'⟩ := exists_between h
  cases b with
  | top => exact (not_lt_of_ge le_top) hb'
  | coe b =>
    obtain ⟨k,hsk,hkb,hx⟩ := exercise41DenseRightHitV4 x q hq s (b : ℝ)
      (1 / ((n : ℝ) + 1)) (by exact_mod_cast (WithTop.coe_lt_coe.mp hb))
      (by positivity) hr hz
    have hk : a ≤ q k ∧ |x (q k)| < 1 / ((n : ℝ) + 1) := ⟨has.trans hsk,hx⟩
    have hh := iInf_le (fun k : ℕ => if a ≤ q k ∧ |x (q k)| < 1 / ((n : ℝ) + 1)
      then (q k : WithTop NNReal) else ⊤) k
    rw [if_pos hk] at hh
    exact (not_lt_of_ge hh) (hb'.trans' (WithTop.coe_lt_coe.mpr (by exact_mod_cast hkb)))
