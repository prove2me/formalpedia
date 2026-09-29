-- Prove2me | solution 1 for Kawahira.xi_one_sub
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-13T22:40:30.708979+00:00
-- url     : https://prove2.me/submissions/4819359b-39fc-4f93-9d6c-3fc138d4342d

import Definitions.Def_Kawahira_zeta

open Complex Topology
open Kawahira

theorem solution (s : ℂ) : xi (1 - s) = xi s := by
  rw [xi, xi, completedRiemannZeta₀_one_sub]
  ring
