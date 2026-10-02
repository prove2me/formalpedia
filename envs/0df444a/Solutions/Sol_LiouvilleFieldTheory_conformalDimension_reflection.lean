-- Prove2me | solution 1 for LiouvilleFieldTheory.conformalDimension_reflection
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-01T12:41:39.104087+00:00
-- url     : https://prove2.me/submissions/752f5b8d-024c-4f5b-ab83-5553fdb8058c

import Mathlib
import Definitions.Def_LiouvilleFieldTheory_kinematics
open Complex
open LiouvilleFieldTheory

theorem solution (b α : ℂ) :
    conformalDimension b (backgroundCharge b - α) = conformalDimension b α := by
  unfold conformalDimension backgroundCharge
  ring
