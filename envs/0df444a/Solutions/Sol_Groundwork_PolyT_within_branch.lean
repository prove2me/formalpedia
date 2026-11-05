-- Prove2me | solution 1 for Groundwork.PolyT.within_branch
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:51:45.461195+00:00
-- url     : https://prove2.me/submissions/5cdffe6e-72fd-405f-825b-dc6a1216f745

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ToTuring_Closure_Basic
import Definitions.Def_ToTuring_Closure_Cases
import Theorems.Thm_Groundwork_TM_Frag_branch_runs_false
import Theorems.Thm_Groundwork_TM_Frag_branch_runs_true


set_option autoImplicit false
section
section
open Groundwork Groundwork.PolyT
open TM Turing
variable {α β γ δ ε : Type} [Enc α] [Enc β] [Enc γ] [Enc δ] [Enc ε]
namespace Groundwork.PolyT
theorem _root_.solution {q : TM2.Stmt (fun _ : Stk => Sym) Bool (Option Sym)} {P Q : Fr} {S S₁ S' : Stk → List Sym} {t : ℕ}
    (b : Bool) (h : TM2.stepAux q none S = ⟨some b, none, S₁⟩) (hb : (bif b then P else Q).Within S₁ t S') :
    (Frag.branch q P Q).Within S (t + 1) S' := by
  obtain ⟨n, hn, hr⟩ := hb
  cases b
  · exact ⟨n + 1, by omega, Frag.branch_runs_false h hr⟩
  · exact ⟨n + 1, by omega, Frag.branch_runs_true h hr⟩
end Groundwork.PolyT
