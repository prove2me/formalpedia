-- Prove2me | solution 1 for Groundwork.TM.Frag.loop_runs_iter
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:04:20.519004+00:00
-- url     : https://prove2.me/submissions/84e536a1-17f0-4ef2-b503-a6e149503a2c

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
theorem _root_.solution {q : TM2.Stmt Γ Unit σ} {B : Frag Γ σ} {v : σ} {S S₁ S₂ S' : ∀ k, List (Γ k)} {n m : ℕ}
    (h : TM2.stepAux q v S = ⟨some (), v, S₁⟩) (hB : B.Runs v S₁ n S₂) (hL : (Frag.loop q B).Runs v S₂ m S') :
    (Frag.loop q B).Runs v S (1 + n + m) S' :=
  ((run_head (M' := (Frag.loop q B).m) (l' := Sum.inl ()) _ none rfl h).trans
    (run_place (M' := (Frag.loop q B).m) Sum.inr (some (Sum.inl ())) (fun _ => rfl) hB)).trans hL
end Frag
end Groundwork.TM
