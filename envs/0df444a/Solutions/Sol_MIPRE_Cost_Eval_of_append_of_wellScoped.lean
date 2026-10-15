-- Prove2me | solution 1 for MIPRE.Cost.Eval.of_append_of_wellScoped
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-12T16:33:12.952471+00:00
-- url     : https://prove2.me/submissions/f015ed99-7de9-4cb4-bd3c-939ad167949e

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Cost/Basic.lean (solution of MIPRE.Cost.Eval.of_append_of_wellScoped);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Notation
import Definitions.Def_MIPRE_Foundations_Cost_Basic

/-! The uploaded declaration, hoisted to the top level as `solution`. -/
open MIPRE
open MIPRE.Cost
open MIPRE.Cost.Eval
theorem solution {env extra : Env} {p : Prog} {r : Data} {t : ℕ}
    (h : Eval (env ++ extra) p r t) (hp : p.WellScoped env.length) : Eval env p r t := by
  generalize henv : env ++ extra = env' at h
  induction h generalizing env with
  | var env'' i =>
    subst henv
    have hi : i < env.length := hp
    rw [Env.get_append hi]
    exact .var _ _
  | nil _ => exact .nil _
  | const _ d => exact .const _ _
  | cons _ _ ih₁ ih₂ =>
    obtain ⟨h₁, h₂⟩ := hp
    exact .cons (ih₁ (env := env) h₁ henv) (ih₂ (env := env) h₂ henv)
  | elim_nil hn _ ih =>
    subst henv
    obtain ⟨hi, h₁, -⟩ := hp
    exact .elim_nil (by rw [← Env.get_append hi]; exact hn) (ih (env := env) h₁ rfl)
  | @elim_cons _ i n c a b _ _ hc _ ih =>
    subst henv
    obtain ⟨hi, -, h₂⟩ := hp
    exact .elim_cons (by rw [← Env.get_append hi]; exact hc)
      (ih (env := a :: b :: env) h₂ rfl)
  | @let_ _ e b v _ _ _ _ _ ih₁ ih₂ =>
    subst henv
    obtain ⟨h₁, h₂⟩ := hp
    exact .let_ (ih₁ (env := env) h₁ rfl) (ih₂ (env := v :: env) h₂ rfl)
  | loop_nil _ ih =>
    obtain ⟨-, h₁⟩ := hp
    exact .loop_nil (ih (env := env) h₁ henv)
  | loop_stop _ ih =>
    obtain ⟨-, h₁⟩ := hp
    exact .loop_stop (ih (env := env) h₁ henv)
  | @loop_step _ b x y v _ _ _ _ _ ih₁ ih₂ =>
    subst henv
    obtain ⟨h₀, h₁⟩ := hp
    obtain ⟨w, env', rfl⟩ : ∃ w env', env = w :: env' := by
      cases env with
      | nil => simp at h₀
      | cons w env' => exact ⟨w, env', rfl⟩
    exact .loop_step (ih₁ (env := w :: env') h₁ rfl) (ih₂ (env := v :: env') ⟨h₀, h₁⟩ rfl)
