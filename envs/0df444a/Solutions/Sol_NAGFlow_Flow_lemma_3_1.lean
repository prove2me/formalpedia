-- Prove2me | solution 1 for NAGFlow.Flow.lemma_3_1
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-18T19:33:37.350773+00:00
-- url     : https://prove2.me/submissions/11b754a6-9325-4381-8a86-4a50322ec262

import Mathlib

set_option autoImplicit false

open scoped InnerProductSpace

theorem solution {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] (u v w : V) :
    2 * ⟪u - v, v - w⟫_ℝ = ‖u - w‖ ^ 2 - ‖u - v‖ ^ 2 - ‖v - w‖ ^ 2 := by
  have h : u - w = (u - v) + (v - w) := by abel
  rw [h, norm_add_sq_real]
  ring
