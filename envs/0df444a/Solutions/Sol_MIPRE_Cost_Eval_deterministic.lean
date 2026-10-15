-- Prove2me | solution 1 for MIPRE.Cost.Eval.deterministic
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-12T16:32:50.51566+00:00
-- url     : https://prove2.me/submissions/5157fb69-04e1-40f7-a9e2-8bc09e40af15

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Cost/Basic.lean (solution of MIPRE.Cost.Eval.deterministic);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Notation
import Definitions.Def_MIPRE_Foundations_Cost_Basic

/-! The uploaded declaration, hoisted to the top level as `solution`. -/
open MIPRE
open MIPRE.Cost
open MIPRE.Cost.Eval
theorem solution {env : Env} {p : Prog} {r r' : Data} {t t' : ℕ}
    (h : Eval env p r t) (h' : Eval env p r' t') : r = r' ∧ t = t' := by
  induction h generalizing r' t' with
  | var env i => cases h'; exact ⟨rfl, rfl⟩
  | nil env => cases h'; exact ⟨rfl, rfl⟩
  | const env d => cases h'; exact ⟨rfl, rfl⟩
  | cons _ _ ih₁ ih₂ =>
    cases h' with
    | cons h₁' h₂' =>
      obtain ⟨rfl, rfl⟩ := ih₁ h₁'
      obtain ⟨rfl, rfl⟩ := ih₂ h₂'
      exact ⟨rfl, rfl⟩
  | elim_nil hn _ ih =>
    cases h' with
    | elim_nil _ h₂' => obtain ⟨rfl, rfl⟩ := ih h₂'; exact ⟨rfl, rfl⟩
    | elim_cons hc _ => rw [hn] at hc; cases hc
  | elim_cons hc _ ih =>
    cases h' with
    | elim_nil hn _ => rw [hn] at hc; cases hc
    | elim_cons hc' h₂' =>
      rw [hc] at hc'
      cases hc'
      obtain ⟨rfl, rfl⟩ := ih h₂'
      exact ⟨rfl, rfl⟩
  | let_ _ _ ih₁ ih₂ =>
    cases h' with
    | let_ h₁' h₂' =>
      obtain ⟨rfl, rfl⟩ := ih₁ h₁'
      obtain ⟨rfl, rfl⟩ := ih₂ h₂'
      exact ⟨rfl, rfl⟩
  | loop_nil _ ih =>
    cases h' with
    | loop_nil h₁' => obtain ⟨-, rfl⟩ := ih h₁'; exact ⟨rfl, rfl⟩
    | loop_stop h₁' => obtain ⟨h, -⟩ := ih h₁'; cases h
    | loop_step h₁' _ => obtain ⟨h, -⟩ := ih h₁'; cases h
  | loop_stop _ ih =>
    cases h' with
    | loop_nil h₁' => obtain ⟨h, -⟩ := ih h₁'; cases h
    | loop_stop h₁' => obtain ⟨h, rfl⟩ := ih h₁'; cases h; exact ⟨rfl, rfl⟩
    | loop_step h₁' _ => obtain ⟨h, -⟩ := ih h₁'; cases h
  | loop_step _ _ ih₁ ih₂ =>
    cases h' with
    | loop_nil h₁' => obtain ⟨h, -⟩ := ih₁ h₁'; cases h
    | loop_stop h₁' => obtain ⟨h, -⟩ := ih₁ h₁'; cases h
    | loop_step h₁' h₂' =>
      obtain ⟨h, rfl⟩ := ih₁ h₁'
      cases h
      obtain ⟨rfl, rfl⟩ := ih₂ h₂'
      exact ⟨rfl, rfl⟩
