-- Prove2me | solution 2 for Mandelbrot.mandelbrot_isConnected
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-22T10:50:36.578182+00:00
-- url     : https://prove2.me/submissions/bc78cde0-9cb4-4b00-a422-3668d376edcb
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_mandelbrot_sets
import Theorems.Thm_Mandelbrot_mandelbrot_escape_criterion
import Theorems.Thm_Mandelbrot_mandelbrot_lemniscate_isPreconnected
import Theorems.Thm_Mandelbrot_mandelbrot_lemniscate_antitone
import Theorems.Thm_Mandelbrot_mandelbrot_lemniscate_isCompact
import Theorems.Thm_isPreconnected_iInter_of_antitone_isCompact

open Topology Set Function Filter Bornology Metric MeasureTheory

namespace Mandelbrot

private def lem (k : ℕ) : Set ℂ := {c : ℂ | ‖(fun z ↦ z ^ 2 + c)^[k] 0‖ ≤ 2}

private lemma zero_iter (k : ℕ) : (fun z : ℂ ↦ z ^ 2 + 0)^[k] 0 = 0 := by
  induction k with
  | zero => simp
  | succ n ih => rw [Function.iterate_succ_apply', ih]; ring

theorem _root_.solution : IsConnected Mandelbrot.mandelbrotSet := by
  have hset : Mandelbrot.mandelbrotSet = ⋂ n : ℕ, lem (n + 1) := by
    rw [Mandelbrot.mandelbrot_escape_criterion]
    ext c
    simp only [Set.mem_setOf_eq, Set.mem_iInter, lem]
    constructor
    · intro h n; exact h (n + 1)
    · intro h k
      cases k with
      | zero => simpa using (by norm_num : (0:ℝ) ≤ 2)
      | succ m => exact h m
  constructor
  · refine ⟨0, ?_⟩
    rw [Mandelbrot.mandelbrot_escape_criterion]
    intro k
    rw [zero_iter k]
    simp
  · rw [hset]
    refine isPreconnected_iInter_of_antitone_isCompact ?_ ?_ ?_
    · refine antitone_nat_of_succ_le ?_
      intro n
      exact Mandelbrot.mandelbrot_lemniscate_antitone (n + 1)
    · intro n
      exact Mandelbrot.mandelbrot_lemniscate_isCompact (n + 1) (by omega)
    · intro n
      exact Mandelbrot.mandelbrot_lemniscate_isPreconnected (n + 1)

end Mandelbrot

#print axioms solution
