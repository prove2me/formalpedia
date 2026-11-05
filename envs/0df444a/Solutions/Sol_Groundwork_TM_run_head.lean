-- Prove2me | solution 1 for Groundwork.TM.run_head
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:03:33.732659+00:00
-- url     : https://prove2.me/submissions/fdf412dc-fef3-46c1-9116-a908ca5133c9

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ToTuring_TM_Run
import Definitions.Def_ToTuring_TM_Frag
import Theorems.Thm_Groundwork_TM_Run_one
import Theorems.Thm_Groundwork_TM_stepAux_place


set_option autoImplicit false
section
section
open Groundwork Groundwork.TM
open Turing
variable {K : Type} [DecidableEq K] {Γ : K → Type} {σ : Type}
attribute [instance] Frag.fin
namespace Groundwork.TM
theorem _root_.solution {Λ Λ' : Type} {M' : Λ' → TM2.Stmt Γ Λ' σ} (ι : Λ → Λ') (e : Option Λ') {l' : Λ'} {q : TM2.Stmt Γ Λ σ}
    (hM : M' l' = place ι e q) {v : σ} {S : ∀ k, List (Γ k)} {c : TM2.Cfg Γ Λ σ} (h : TM2.stepAux q v S = c) :
    Run (TM2.step M') ⟨some l', v, S⟩ 1 (placeCfg ι e c) :=
  Run.one (by simp only [TM2.step, hM, stepAux_place, h])
end Groundwork.TM
