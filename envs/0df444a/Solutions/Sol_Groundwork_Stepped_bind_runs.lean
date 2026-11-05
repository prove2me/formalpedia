-- Prove2me | solution 1 for Groundwork.Stepped.bind_runs
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T15:44:41.150866+00:00
-- url     : https://prove2.me/submissions/77f593a9-c2a6-4c77-abd3-d4d3aba50b46

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachineStatements
import Definitions.Def_StepMachines_Prog_Stepped
import Theorems.Thm_Groundwork_Stepped_Reaches_mono
import Theorems.Thm_Groundwork_Stepped_Runs_mono
import Theorems.Thm_Groundwork_Stepped_bind_reaches_inr

set_option autoImplicit false
section
open Groundwork
open Groundwork.Stepped
variable {α β γ τ : Type}
namespace Groundwork.Stepped
theorem _root_.solution [HasSize α] {M : Stepped α β} {N : Stepped (α × β) γ} {a : α} {t t' S S' : ℕ}
    {b : β} {c : γ} (h : M.Runs a t S b) (h' : N.Runs (a, b) t' S' c) :
    (bind M N).Runs a (t + 1 + t') (max (size a + S) S' + 1) c := by
  unfold Runs at *
  change (bind M N).Reaches _ c (.inl (a, M.init a)) _
  generalize M.init a = s at h
  induction h with
  | @halt s t ho hs =>
    have e : (bind M N).step (.inl (a, s)) = .inr (N.init (a, b)) := by
      change (match M.out s with | some b => _ | none => _) = _
      rw [ho]
    have : (bind M N).Reaches (max (size a + S) S' + 1) c (.inl (a, s)) (t' + 1) :=
      .step rfl (by change size a + size s + 1 ≤ _; omega)
        (e ▸ (bind_reaches_inr h').mono le_rfl (by omega))
    exact this.mono (by omega) le_rfl
  | @step s t ho hs _ ih =>
    have e : (bind M N).step (.inl (a, s)) = .inl (a, M.step s) := by
      change (match M.out s with | some b => _ | none => _) = _
      rw [ho]
    have : (bind M N).Reaches (max (size a + S) S' + 1) c (.inl (a, s)) (t + 1 + t' + 1) :=
      .step rfl (by change size a + size s + 1 ≤ _; omega) (e ▸ ih)
    exact this.mono (by omega) le_rfl
end Groundwork.Stepped
