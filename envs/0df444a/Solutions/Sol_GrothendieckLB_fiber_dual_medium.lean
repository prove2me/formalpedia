-- Prove2me | solution 1 for GrothendieckLB.fiber_dual_medium
-- status  : ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-23T16:19:33.163277+00:00
-- url     : https://prove2.me/submissions/6f2d8fcf-915c-46ae-bc43-d0255c2bf9cd

import Theorems.Thm_GrothendieckLB_fiber_dual_even_direction
import Theorems.Thm_GrothendieckLB_fiber_dual_parity_norms

open GrothendieckLB

theorem solution (a : Fin 4 → ℝ) (ha : ∑ j, a j ^ 2 = 1) (c : ℝ)
    (hlo : (993405 : ℝ) / 1000000 ≤ c) (hhi : c ≤ 12) :
    stdExp (fun s => max (|∑ j, a j * he j s| - c * |s|) 0) ≤
      (3 * ABPOnline.cG / 2) * (Real.sqrt (1 + c ^ 2) - c) := by
  rcases le_total c (7/5) with h | h
  · exact fiber_dual_even_direction a ha c hlo h
  · exact fiber_dual_parity_norms a ha c h hhi
