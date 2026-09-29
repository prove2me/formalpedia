-- Prove2me | solution 1 for Mandelbrot.mandelbrot_isCompact
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-13T16:01:36.016356+00:00
-- url     : https://prove2.me/submissions/ea4619f2-db81-401b-b318-80a7f58787e6

import Mathlib
import Definitions.Def_mandelbrot_sets
import Theorems.Thm_Mandelbrot_mandelbrot_escape_criterion

open Topology Set Function Filter Bornology Metric MeasureTheory

namespace Mandelbrot

private lemma criticalOrbit_continuous : ∀ k : ℕ,
    Continuous (fun c : ℂ ↦ (fun z ↦ z ^ 2 + c)^[k] 0) := by
  intro k
  induction k with
  | zero => simpa using (continuous_const : Continuous (fun _ : ℂ => (0 : ℂ)))
  | succ k ih =>
      simp only [Function.iterate_succ_apply']
      fun_prop

theorem compactnessProof : IsCompact mandelbrotSet := by
  rw [mandelbrot_escape_criterion]
  apply isCompact_iff_isClosed_bounded.mpr
  constructor
  · rw [show {c : ℂ | ∀ k : ℕ, ‖(fun z ↦ z ^ 2 + c)^[k] 0‖ ≤ 2} =
        ⋂ k : ℕ, {c : ℂ | ‖(fun z ↦ z ^ 2 + c)^[k] 0‖ ≤ 2} by
      ext c
      simp]
    exact isClosed_iInter fun k ↦
      isClosed_le (criticalOrbit_continuous k).norm continuous_const
  · refine (Metric.isBounded_closedBall (x := (0 : ℂ)) (r := 2)).subset ?_
    intro c hc
    have h1 := hc 1
    simpa [Metric.mem_closedBall, dist_eq_norm,
      Function.iterate_succ_apply'] using h1

end Mandelbrot

theorem solution : IsCompact Mandelbrot.mandelbrotSet :=
  Mandelbrot.compactnessProof
