-- Prove2me | solution 1 for Groundwork.TM.Frag.branch_runs_true
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:42:22.500237+00:00
-- url     : https://prove2.me/submissions/e6b35df6-32f6-459c-b75c-3ed692afb0d8

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ToTuring_TM_Run
import Definitions.Def_ToTuring_TM_Frag
import Theorems.Thm_Groundwork_TM_run_head
import Theorems.Thm_Groundwork_TM_Run_trans
import Theorems.Thm_Groundwork_TM_run_place


set_option autoImplicit false
section
section
open Groundwork Groundwork.TM
open Turing
variable {K : Type} [DecidableEq K] {Γ : K → Type} {σ : Type}
attribute [instance] Frag.fin
namespace Groundwork.TM
namespace Frag
theorem _root_.solution {q : TM2.Stmt Γ Bool σ} {P Q : Frag Γ σ} {v : σ} {S S₁ S' : ∀ k, List (Γ k)} {n : ℕ}
    (h : TM2.stepAux q v S = ⟨some true, v, S₁⟩) (hP : P.Runs v S₁ n S') : (Frag.branch q P Q).Runs v S (n + 1) S' := by
  rw [Nat.add_comm n 1]
  exact (run_head (M' := (Frag.branch q P Q).m) (l' := Sum.inl ()) _ none rfl h).trans
    (run_place (M' := (Frag.branch q P Q).m) (fun l => Sum.inr (Sum.inl l)) none (fun _ => rfl) hP)
end Frag
end Groundwork.TM
