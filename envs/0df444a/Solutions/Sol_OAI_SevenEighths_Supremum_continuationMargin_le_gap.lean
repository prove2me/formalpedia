-- Prove2me | solution 1 for OAI.SevenEighths.Supremum.continuationMargin_le_gap
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T22:26:55.97963+00:00
-- url     : https://prove2.me/submissions/a14992ff-a2dc-4307-b1b7-0856ceef7c82

import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic.Linarith
import Definitions.Def_OAI_NumberTheory_DirichletL_Supremum
set_option autoImplicit false
open OAI
open OAI.SevenEighths OAI.SevenEighths.Supremum
noncomputable section

theorem solution (β ω σ : ℝ) :
    continuationMargin β ω σ ≤ β - 7 / 8 - ω := by
  exact min_le_left _ _
