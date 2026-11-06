-- Prove2me | solution 2 for OAI.ShortDraft.eisenstein_norm_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T23:07:51.148908+00:00
-- url     : https://prove2.me/submissions/0986aec3-e6ea-4990-a052-efb1b22fb207

import Definitions.Def_OAI_NumberTheory_DirichletL_Arithmetic_EisensteinCoordinates
import Mathlib.Tactic.Linarith

set_option autoImplicit false
open OAI
open scoped BigOperators
open OAI.ShortDraft

theorem solution (x : EisensteinCoordinates) :
    0 ≤ eisensteinNorm x := by
  unfold eisensteinNorm
  nlinarith [sq_nonneg (2 * x.1 - x.2), sq_nonneg x.2]
