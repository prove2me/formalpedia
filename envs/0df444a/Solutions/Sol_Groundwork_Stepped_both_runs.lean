-- Prove2me | solution 1 for Groundwork.Stepped.both_runs
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:44:42.151544+00:00
-- url     : https://prove2.me/submissions/d4e7099d-4157-40de-9cbd-6be0618e988d

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachines_Prog_Stepped
import Definitions.Def_StepMachines_Prog_Comb
import Theorems.Thm_Groundwork_Stepped_both_reaches_inr
import Theorems.Thm_Groundwork_Stepped_Reaches_mono
import Theorems.Thm_Groundwork_Stepped_Runs_mono


set_option autoImplicit false
section
open Groundwork Groundwork.Stepped
variable {α α₁ α₂ β γ δ ι : Type}
namespace Groundwork.Stepped
theorem _root_.solution [HasSize α] [HasSize β] {M : Stepped α β} {N : Stepped α γ} {a : α} {t t' S S' : ℕ}
    {b : β} {c : γ} (h : M.Runs a t S b) (h' : N.Runs a t' S' c) :
    (both M N).Runs a (t + 1 + t') (max (size a + S) (size b + S') + 1) (b, c) := by
  unfold Runs at *
  change (both M N).Reaches _ (b, c) (.inl (a, M.init a)) _
  generalize M.init a = s at h
  induction h with
  | @halt s t ho hs =>
    have e : (both M N).step (.inl (a, s)) = .inr (b, N.init a) := by
      change (match M.out s with | some b => _ | none => _) = _
      rw [ho]
    have : (both M N).Reaches (max (size a + S) (size b + S') + 1) (b, c) (.inl (a, s)) (t' + 1) :=
      .step rfl (by change size a + size s + 1 ≤ _; omega)
        (e ▸ (both_reaches_inr h').mono le_rfl (by omega))
    exact this.mono (by omega) le_rfl
  | @step s t ho hs _ ih =>
    have e : (both M N).step (.inl (a, s)) = .inl (a, M.step s) := by
      change (match M.out s with | some b => _ | none => _) = _
      rw [ho]
    have : (both M N).Reaches (max (size a + S) (size b + S') + 1) (b, c) (.inl (a, s)) (t + 1 + t' + 1) :=
      .step rfl (by change size a + size s + 1 ≤ _; omega) (e ▸ ih)
    exact this.mono (by omega) le_rfl
end Groundwork.Stepped
