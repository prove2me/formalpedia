-- Prove2me | solution 1 for Monodromy.Counter.Reversible.Glue.controls_eq_iff
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T18:37:54.624709+00:00
-- url     : https://prove2.me/submissions/877c391d-640b-4a85-a464-28b02ee26751

module
public import Definitions.Def_Monodromy_Counter
public import Lean.Elab.Tactic.Omega
public import Mathlib.Data.Fin.Basic

@[expose] public section

open Monodromy
open Monodromy.Counter
open Monodromy.Counter.Reversible
open Monodromy.Counter.Reversible.Glue

variable {q₁ q₂ : ℕ}

theorem solution (exit : Fin (q₁ + 1)) (entry : Fin q₂)
    (left : Fin (q₁ + 1)) (right : Fin q₂) :
    leftControl exit entry left = rightControl right ↔ left = exit ∧ right = entry := by
  constructor
  · intro h
    rcases Fin.eq_self_or_eq_succAbove exit left with hl | ⟨j, rfl⟩
    · subst left
      refine ⟨rfl, ?_⟩
      apply Fin.ext
      have hv := congrArg Fin.val h
      simp [leftControl, rightControl] at hv
      omega
    · have hv := congrArg Fin.val h
      simp [leftControl, rightControl] at hv
      have hj := j.isLt
      omega
  · rintro ⟨rfl, rfl⟩
    simp [leftControl, rightControl]
