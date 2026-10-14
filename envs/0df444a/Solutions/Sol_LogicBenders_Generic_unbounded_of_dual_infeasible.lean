-- Prove2me | solution 1 for LogicBenders.Generic.unbounded_of_dual_infeasible
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-13T01:55:28.134732+00:00
-- url     : https://prove2.me/submissions/b0618355-a511-4a15-863c-aad7f65c9759

import Definitions.Def_LogicBenders_Generic_Setting
import Mathlib

open LogicBenders.Generic

theorem solution {X Y : Type*} (S : Set (X × Y)) (f : X → Y → ℝ) (yb : Y)
    (h : ¬ ∃ β : ℝ, IsDualFeasible S f yb (β : EReal)) :
    (∀ M : ℝ, ∃ x : X, (x, yb) ∈ S ∧ f x yb < M) ∧ IsUnbounded S f := by
  have hu : ∀ M : ℝ, ∃ x : X, (x, yb) ∈ S ∧ f x yb < M := by
    intro M
    by_contra hn
    push_neg at hn
    apply h
    refine ⟨M, ?_⟩
    intro x hx
    exact EReal.coe_le_coe_iff.mpr (hn x hx)
  refine ⟨hu, ?_⟩
  intro M
  obtain ⟨x, hx, hf⟩ := hu M
  exact ⟨x, yb, hx, hf⟩
