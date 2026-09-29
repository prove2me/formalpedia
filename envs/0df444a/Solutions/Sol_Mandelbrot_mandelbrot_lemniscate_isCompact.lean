-- Prove2me | solution 1 for Mandelbrot.mandelbrot_lemniscate_isCompact
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-22T18:19:30.294366+00:00
-- url     : https://prove2.me/submissions/015e58fe-04ac-43c4-9123-d2932f7abf51

import Mathlib
import Definitions.Def_mandelbrot_sets
import Theorems.Thm_Mandelbrot_mandelbrot_lemniscate_antitone

open Topology Set Function Filter Bornology Metric MeasureTheory

namespace Mandelbrot

private lemma lemn_cont (k : ℕ) : Continuous (fun c : ℂ ↦ (fun z ↦ z ^ 2 + c)^[k] 0) := by
  induction k with
  | zero => simpa using continuous_const
  | succ n ih =>
    have h : (fun c : ℂ ↦ (fun z ↦ z ^ 2 + c)^[n + 1] 0) =
        fun c ↦ ((fun z ↦ z ^ 2 + c)^[n] 0) ^ 2 + c := by
      funext c; exact Function.iterate_succ_apply' _ _ _
    rw [h]; exact (ih.pow 2).add continuous_id

private lemma lemn_sub_one (k : ℕ) (hk : 1 ≤ k) :
    {c : ℂ | ‖(fun z ↦ z ^ 2 + c)^[k] 0‖ ≤ 2} ⊆
      {c : ℂ | ‖(fun z ↦ z ^ 2 + c)^[1] 0‖ ≤ 2} := by
  induction k, hk using Nat.le_induction with
  | base => exact Subset.rfl
  | succ n _ ih => exact (mandelbrot_lemniscate_antitone n).trans ih

theorem _root_.solution (k : ℕ) (hk : 1 ≤ k) :
    IsCompact {c : ℂ | ‖(fun z ↦ z ^ 2 + c)^[k] 0‖ ≤ 2} := by
  apply Metric.isCompact_of_isClosed_isBounded
  · exact isClosed_le (lemn_cont k).norm continuous_const
  · refine (Metric.isBounded_closedBall (x := (0 : ℂ)) (r := 2)).subset ?_
    intro c hc
    have h1 := lemn_sub_one k hk hc
    simp only [mem_setOf_eq, Function.iterate_one] at h1
    rw [mem_closedBall_zero_iff]
    simpa using h1

end Mandelbrot
