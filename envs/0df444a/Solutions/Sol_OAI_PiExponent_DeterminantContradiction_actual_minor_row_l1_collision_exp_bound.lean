-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.actual_minor_row_l1_collision_exp_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-07T20:29:46.192932+00:00
-- url     : https://prove2.me/submissions/129d72c1-730f-42dd-a283-4c63510a89f6
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_actual_minor_row_l1_collision_core
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction

theorem solution
    {nu : Real} (d : FixedData nu) (hnu : 0 <= nu)
    {H : Real} (hH : 0 < H) (selection : Row d H -> Column d H)
    (rowIdx : Row d H) :
    Finset.sum Finset.univ (fun colIdx : Row d H =>
      norm ((actualMinor d H selection) rowIdx colIdx)) <=
      Real.exp (H * (d.analyticError + analyticRemainder d H +
        -collisionRate d H)) := by
  exact actual_minor_row_l1_collision_core d hnu hH selection rowIdx
