-- Prove2me | solution 1 for Groundwork.Stepped.foldWhile_runs
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T15:45:48.419795+00:00
-- url     : https://prove2.me/submissions/2b4b3b88-c938-40be-bb2e-08d0664613f7

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachineStatements
import Definitions.Def_StepMachines_Prog_Stepped
import Theorems.Thm_Groundwork_Stepped_foldWhile_reaches

set_option autoImplicit false
section
open Groundwork
open Groundwork.Stepped
variable {α β γ τ : Type}
variable [HasSize τ] [HasSize γ] {start : α → Option τ} {nxt : τ → Option τ} {M : Stepped τ β}
  {g : γ → τ → β → γ} {c₀ : α → γ}
namespace Groundwork.Stepped
theorem _root_.solution {a : α} {xs : List τ} (ho : Orbit nxt (start a) xs) (t : τ → ℕ) (v : τ → β)
    (Sx Sc Sm : ℕ) (hM : ∀ x ∈ xs, M.Runs x (t x) Sm (v x)) (hx : ∀ x ∈ xs, size x ≤ Sx)
    (hc : ∀ l, l <+: xs → size (l.foldl (fun c x => g c x (v x)) (c₀ a)) ≤ Sc) :
    (foldWhile start nxt M g c₀).Runs a (xs.map fun x => t x + 1).sum (Sx + (Sc + Sm) + 1)
      (xs.foldl (fun c x => g c x (v x)) (c₀ a)) :=
  foldWhile_reaches ho t v Sx Sc Sm (c₀ a) hM hx hc
end Groundwork.Stepped
