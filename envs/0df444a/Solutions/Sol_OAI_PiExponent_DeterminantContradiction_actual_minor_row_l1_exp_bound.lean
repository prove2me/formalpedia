-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.actual_minor_row_l1_exp_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-07T20:01:28.91196+00:00
-- url     : https://prove2.me/submissions/2259c2da-1ed7-4032-ba18-039191467fe1
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_actual_minor_row_l1_collision_exp_bound
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_actual_minor_row_l1_low_index_exp_bound

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction

theorem solution
    {nu : Real} (d : FixedData nu) (hnu : 0 <= nu)
    {H : Real} (hH : 0 < H) (selection : Row d H -> Column d H)
    (rowIdx : Row d H) :
    Finset.sum Finset.univ (fun colIdx : Row d H =>
      norm ((actualMinor d H selection) rowIdx colIdx)) <=
      Real.exp (H *
        (d.analyticError + analyticRemainder d H +
          max (-collisionRate d H)
            (-nu * ((d.base.A : Real) * (1 - d.base.eta) - actualMean d H)))) := by
  have hcollision := actual_minor_row_l1_collision_exp_bound d hnu hH selection rowIdx
  have hlow := actual_minor_row_l1_low_index_exp_bound d hnu hH selection rowIdx
  by_cases h : -collisionRate d H <=
      -nu * ((d.base.A : Real) * (1 - d.base.eta) - actualMean d H)
  · rw [max_eq_right h]
    exact hlow
  · have h' : -nu * ((d.base.A : Real) * (1 - d.base.eta) - actualMean d H) <=
        -collisionRate d H := le_of_not_ge h
    rw [max_eq_left h']
    exact hcollision
