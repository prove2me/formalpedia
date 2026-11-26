-- Prove2me | solution 1 for Kyprianou.Ch04.exercise41ArrivalFromCutoffV22
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T15:06:50.571281+00:00
-- url     : https://prove2.me/submissions/350eee43-7976-4019-adc2-270dae8611ac
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_exercise41UpwardZeroCrossingV22
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Classical Topology
set_option autoImplicit false
open Kyprianou.Ch04
theorem solution
    (x : NNReal → ℝ)
    (hR : ∀ s, ContinuousWithinAt x (Ici s) s)
    (hL : ∀ s, 0 < s → ∃ l, Tendsto x (nhdsWithin s (Iio s)) (nhds l))
    (hNeg : ∀ s l, 0 < s → Tendsto x (nhdsWithin s (Iio s)) (nhds l) → x s ≤ l)
    (a v s : NNReal) (hav : a < v) (hvs : v < s) (hv : x v < 0)
    (hgap : ∀ u ∈ Ico a s, x u ≠ 0) :
    ∃ e : NNReal, 0 < e ∧ ∀ u : NNReal, 0 < u → u < min e s → x (s-u) < 0 := by
  refine ⟨s-v,tsub_pos_of_lt hvs,?_⟩
  intro u hu hlt
  have huv : u < s-v := hlt.trans_le (min_le_left _ _)
  have hUs : u < s := hlt.trans_le (min_le_right _ _)
  have hvu : v < s-u := by
    exact_mod_cast (show (v : ℝ) < ((s-u : NNReal) : ℝ) by
      rw [NNReal.coe_sub hUs.le]
      have H : (u : ℝ) < ((s-v : NNReal) : ℝ) := by exact_mod_cast huv
      rw [NNReal.coe_sub hvs.le] at H
      linarith)
  have hus : s-u < s := tsub_lt_self (lt_of_lt_of_le hu hUs.le) hu
  by_contra hn
  obtain ⟨c,hc,hz⟩ := exercise41UpwardZeroCrossingV22 x hR hL hNeg v (s-u) hvu.le hv (le_of_not_gt hn)
  exact hgap c ⟨hav.le.trans hc.1,hc.2.trans_lt hus⟩ hz
