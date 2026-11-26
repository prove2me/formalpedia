-- Prove2me | solution 1 for Kyprianou.Ch04.exercise41NegativeBeforeZeroV22
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T15:06:43.806364+00:00
-- url     : https://prove2.me/submissions/764df039-f14e-44ac-a4b8-2c3a20f0fdb6

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Classical Topology
set_option autoImplicit false
theorem solution
    (x : NNReal → ℝ) (a s : NNReal) (ha : a < s) (hs : 0 < s) (hz : x s = 0)
    (hDep : ∃ e : NNReal, 0 < e ∧ ∀ u : NNReal, 0 < u → u < e → 0 < x (s+u))
    (hMin : ¬ (∃ e : NNReal, 0 < e ∧ ∀ u ∈ Icc (s-e) (s+e), 0 ≤ x u)) :
    ∃ v ∈ Ioo a s, x v < 0 := by
  obtain ⟨d,hd,hD⟩ := hDep
  let e := min ((s-a)/2) (d/2)
  have he : 0 < e := lt_min (div_pos (tsub_pos_of_lt ha) (by norm_num)) (div_pos hd (by norm_num))
  have hEa : e < s-a := (min_le_left _ _).trans_lt (half_lt_self (tsub_pos_of_lt ha))
  have hEd : e < d := (min_le_right _ _).trans_lt (half_lt_self hd)
  have hSa : a < s-e := by
    have hes : e ≤ s := hEa.le.trans tsub_le_self
    exact_mod_cast (show (a : ℝ) < ((s-e : NNReal) : ℝ) by
      rw [NNReal.coe_sub hes]
      have H : (e : ℝ) < ((s-a : NNReal) : ℝ) := by exact_mod_cast hEa
      rw [NNReal.coe_sub ha.le] at H
      linarith)
  push_neg at hMin
  obtain ⟨v,hv,hneg⟩ := hMin e he
  have hvlt : v < s := by
    by_contra hn
    have hvs : s ≤ v := le_of_not_gt hn
    by_cases h : s = v
    · rw [← h,hz] at hneg
      exact (lt_irrefl 0) hneg
    · have hu : 0 < v-s := tsub_pos_of_lt (lt_of_le_of_ne hvs h)
      have hle : v-s ≤ e := (tsub_le_iff_right).mpr (by simpa [add_comm] using hv.2)
      have H := hD (v-s) hu (hle.trans_lt hEd)
      rw [add_tsub_cancel_of_le hvs] at H
      exact (not_lt_of_ge H.le) hneg
  exact ⟨v,⟨hSa.trans_le hv.1,hvlt⟩,hneg⟩
