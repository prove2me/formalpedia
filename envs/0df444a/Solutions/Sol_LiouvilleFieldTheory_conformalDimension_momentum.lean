-- Prove2me | solution 1 for LiouvilleFieldTheory.conformalDimension_momentum
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-01T12:45:45.544374+00:00
-- url     : https://prove2.me/submissions/998d1f74-50d5-4070-8d5a-aedcea5673ff

import Mathlib
import Definitions.Def_LiouvilleFieldTheory_kinematics
open Complex
open LiouvilleFieldTheory

theorem solution (b P : ℂ) :
    conformalDimension b (backgroundCharge b / 2 + I * P) =
      (centralCharge b - 1) / 24 + P ^ 2 := by
  unfold conformalDimension centralCharge backgroundCharge
  ring_nf
  simp only [I_sq]
  ring
