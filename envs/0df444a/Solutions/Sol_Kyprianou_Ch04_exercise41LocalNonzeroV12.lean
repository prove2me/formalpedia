-- Prove2me | solution 1 for Kyprianou.Ch04.exercise41LocalNonzeroV12
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T12:54:28.251248+00:00
-- url     : https://prove2.me/submissions/e29f8192-8826-44fb-a0db-59693814a1ef

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Classical Topology
set_option autoImplicit false
theorem solution
    (x : NNReal → ℝ) (s : NNReal) (l : ℝ)
    (hx : x s ≠ 0) (hl : l ≠ 0)
    (hR : ContinuousWithinAt x (Ici s) s)
    (hL : Tendsto x (nhdsWithin s (Iio s)) (nhds l)) :
    ∃ e : ℝ, 0 < e ∧ {v : NNReal | e ≤ |x v|} ∈ nhds s := by
  let e := min |x s| |l| / 2
  have h1 : 0 < |x s| := abs_pos.mpr hx
  have h2 : 0 < |l| := abs_pos.mpr hl
  have he : 0 < e := by dsimp [e]; positivity
  have hxs : e < |x s| := by
    dsimp [e]
    linarith [min_le_left |x s| |l|]
  have hls : e < |l| := by
    dsimp [e]
    linarith [min_le_right |x s| |l|]
  have hr := (continuous_abs.continuousAt.tendsto.comp hR).eventually (eventually_ge_nhds hxs)
  have hleft := (continuous_abs.continuousAt.tendsto.comp hL).eventually (eventually_ge_nhds hls)
  refine ⟨e,he,?_⟩
  rw [← nhdsWithin_univ s, ← Iio_union_Ici (a := s), nhdsWithin_union, Filter.mem_sup]
  exact ⟨hleft,hr⟩
