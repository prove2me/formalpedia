-- Prove2me | solution 1 for Groundwork.Stepped.foldWhile_body
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T15:43:54.100064+00:00
-- url     : https://prove2.me/submissions/6282317a-4cea-4adb-addb-5d5502dae2c7

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachineStatements
import Definitions.Def_StepMachines_Prog_Stepped
import Theorems.Thm_Groundwork_Stepped_Reaches_mono
import Theorems.Thm_Groundwork_Stepped_Runs_mono

set_option autoImplicit false
section
open Groundwork
open Groundwork.Stepped
variable {α β γ τ : Type}
variable [HasSize τ] [HasSize γ] {start : α → Option τ} {nxt : τ → Option τ} {M : Stepped τ β}
  {g : γ → τ → β → γ} {c₀ : α → γ}
namespace Groundwork.Stepped
theorem _root_.solution {x : τ} {c r : γ} {b : β} {s : M.σ} {t T Sm S : ℕ} (h : M.Reaches Sm b s t)
    (hS : size x + (size c + Sm) + 1 ≤ S)
    (hr : (foldWhile start nxt M g c₀).Reaches S r (foldGo M (g c x b) (nxt x)) T) :
    (foldWhile start nxt M g c₀).Reaches S r (.inl (x, c, s)) (t + 1 + T) := by
  induction h with
  | @halt s t ho hs =>
    have e : (foldWhile start nxt M g c₀).step (.inl (x, c, s)) = foldGo M (g c x b) (nxt x) := by
      change (match M.out s with | some b => _ | none => _) = _
      rw [ho]
    have : (foldWhile start nxt M g c₀).Reaches S r (.inl (x, c, s)) (T + 1) :=
      .step rfl (by change size x + (size c + size s) + 1 ≤ _; omega) (e ▸ hr)
    exact this.mono (by omega) le_rfl
  | @step s t ho hs _ ih =>
    have e : (foldWhile start nxt M g c₀).step (.inl (x, c, s)) = .inl (x, c, M.step s) := by
      change (match M.out s with | some b => _ | none => _) = _
      rw [ho]
    have : (foldWhile start nxt M g c₀).Reaches S r (.inl (x, c, s)) (t + 1 + T + 1) :=
      .step rfl (by change size x + (size c + size s) + 1 ≤ _; omega) (e ▸ ih)
    exact this.mono (by omega) le_rfl
end Groundwork.Stepped
