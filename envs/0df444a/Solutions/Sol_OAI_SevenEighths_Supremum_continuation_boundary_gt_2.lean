-- Prove2me | solution 2 for OAI.SevenEighths.Supremum.continuation_boundary_gt
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-05T23:06:26.004929+00:00
-- url     : https://prove2.me/submissions/c919700a-c46e-4f0f-9f4d-242c7eca210d

import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic.Linarith
import Definitions.Def_OAI_NumberTheory_DirichletL_Supremum
set_option autoImplicit false
open OAI
open OAI.SevenEighths OAI.SevenEighths.Supremum
noncomputable section
theorem solution {β ω σ : ℝ} (hω : 0 < ω) :
    7 / 8 < β - continuationMargin β ω σ := by
  unfold continuationMargin
  have := min_le_left (β - 7 / 8 - ω) σ
  linarith
