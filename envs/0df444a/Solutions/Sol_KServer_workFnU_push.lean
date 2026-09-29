-- Prove2me | solution 1 for KServer.workFnU_push
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-31T17:41:28.016355+00:00
-- url     : https://prove2.me/submissions/af58aca9-b498-4254-a267-59e3090bd809

import Mathlib
import Definitions.Def_KServer_workfunctionU
import Theorems.Thm_KServer_workFnU_lipschitz

open KServer

/-- **Pushing a witness outwards.** -/
theorem solution (M : Type) [MetricSpace M] (C₀ : Config 3 M) (σ : List M)
    (r p b b' u : M) (h : dist p b + dist b u = dist p u) :
    dist p b + dist p b' - workFnU C₀ σ ![r, b, b']
      ≤ dist p u + dist p b' - workFnU C₀ σ ![r, u, b'] := by
  have hmc : moveCost (![r, b, b'] : Config 3 M) (![r, u, b'] : Config 3 M) = dist b u := by
    unfold moveCost
    rw [Fin.sum_univ_three]
    show dist r r + dist b u + dist b' b' = dist b u
    rw [dist_self, dist_self]
    ring
  have hlip := workFnU_lipschitz 3 (by norm_num) M C₀ σ ![r, u, b'] ![r, b, b']
  rw [hmc] at hlip
  linarith
