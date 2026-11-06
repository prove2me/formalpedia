-- Prove2me | solution 1 for OAI.SevenEighths.Supremum.continuationMargin_le_sigma
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T23:09:09.787203+00:00
-- url     : https://prove2.me/submissions/dfbdae6d-cc13-4afa-a0e1-3adac3cb943d

import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic.Linarith
import Definitions.Def_OAI_NumberTheory_DirichletL_Supremum
set_option autoImplicit false
open OAI
open OAI.SevenEighths OAI.SevenEighths.Supremum
noncomputable section

theorem solution (β ω σ : ℝ) :
    continuationMargin β ω σ ≤ σ :=
  min_le_right _ _
