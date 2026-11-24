-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.p2m85_height_tail_shift_integral
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T16:30:43.557726+00:00
-- url     : https://prove2.me/submissions/ff00ed01-ffd6-4fd9-986a-acf3bbb0b5bd

import Mathlib
import Theorems.Thm_Kyprianou_Ch08_StageB_p2m85_height_tail_zero
set_option autoImplicit false
open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

theorem solution
    (n : Measure ℝ) (hn : n (Ici (1 : ℝ)) < ⊤) (x : ℝ) :
    Tendsto (fun a : ℝ => ∫ t in (a-x)..a, (n (Ici t)).toReal)
      atTop (𝓝 0) := by
  let b (a : ℝ) := min (a-x) a
  have hb : Tendsto b atTop atTop := by
    apply tendsto_atTop.2
    intro c
    filter_upwards [eventually_ge_atTop (max c (c+x))] with a ha
    dsimp [b]
    exact le_min (by linarith [le_max_right c (c+x)]) (le_max_left _ _ |>.trans ha)
  have ht := (Kyprianou.Ch08.StageB.p2m85_height_tail_zero n hn).comp hb
  have hs := ht.mul_const |x|
  simp only [zero_mul] at hs
  apply squeeze_zero_norm' _ hs
  filter_upwards [(tendsto_atTop.1 hb) 1] with a ha
  have hfin : n (Ici (b a)) ≠ ⊤ :=
    ((measure_mono (Ici_subset_Ici.mpr ha)).trans_lt hn).ne
  have hbound := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := a-x) (b := a) (f := fun t => (n (Ici t)).toReal)
    (C := (n (Ici (b a))).toReal) (fun t ht => by
      have hm : b a ≤ t := by
        rcases mem_uIcc.mp (uIoc_subset_uIcc ht) with h | h
        · exact (min_le_left _ _).trans h.1
        · exact (min_le_right _ _).trans h.1
      rw [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
      exact ENNReal.toReal_mono hfin (measure_mono (Ici_subset_Ici.mpr hm)))
  rwa [show a-(a-x)=x by ring] at hbound
