-- Prove2me | solution 1 for Kawahira.xi_analyticOrderAt_ne_top
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-13T22:48:14.420712+00:00
-- url     : https://prove2.me/submissions/43336c43-8f41-4193-9cb0-ceaa16a1ec09

import Definitions.Def_Kawahira_zeta

open Complex Topology Set
open Kawahira

theorem solution (a : ℂ) : analyticOrderAt xi a ≠ ⊤ := by
  have hxi : AnalyticOnNhd ℂ xi (Set.univ : Set ℂ) :=
    differentiable_xi.differentiableOn.analyticOnNhd isOpen_univ
  apply hxi.analyticOrderAt_ne_top_of_isPreconnected isPreconnected_univ
      (x := (0 : ℂ)) (y := a)
  · simp
  · simp
  · have hxi0 : xi (0 : ℂ) ≠ 0 := by
      norm_num [xi]
    rw [analyticOrderAt_eq_zero.mpr (.inr hxi0)]
    simp
