-- Prove2me | solution 2 for LiouvilleFieldTheory.conformalDimension_reflection
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-01T12:45:44.367771+00:00
-- url     : https://prove2.me/submissions/b0bdf9a4-d0e6-4006-a54f-2fdd7e52e0c8

import Mathlib
import Definitions.Def_LiouvilleFieldTheory_kinematics
open Complex
open LiouvilleFieldTheory

theorem solution (b α : ℂ) :
    conformalDimension b (backgroundCharge b - α) = conformalDimension b α := by
  unfold conformalDimension backgroundCharge
  ring
