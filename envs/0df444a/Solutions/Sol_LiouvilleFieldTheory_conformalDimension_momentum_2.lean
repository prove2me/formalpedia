-- Prove2me | solution 2 for LiouvilleFieldTheory.conformalDimension_momentum
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-01T12:46:10.293563+00:00
-- url     : https://prove2.me/submissions/ff369694-144b-48bb-8774-7acef815b6ff

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
