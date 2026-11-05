-- Prove2me | solution 1 for Groundwork.TM.Frag.ofStmt_runs
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:04:21.763605+00:00
-- url     : https://prove2.me/submissions/67357132-246e-4ca3-abf1-0542e519c146

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ToTuring_TM_Run
import Definitions.Def_ToTuring_TM_Frag
import Theorems.Thm_Groundwork_TM_run_head

set_option autoImplicit false
section
section
open Groundwork Groundwork.TM
open Turing
variable {K : Type} [DecidableEq K] {Γ : K → Type} {σ : Type}
attribute [instance] Frag.fin
namespace Groundwork.TM
namespace Frag
theorem _root_.solution {q : TM2.Stmt Γ Empty σ} {v : σ} {S S' : ∀ k, List (Γ k)}
    (h : TM2.stepAux q v S = ⟨none, v, S'⟩) : (Frag.ofStmt q).Runs v S 1 S' :=
  run_head (M' := (Frag.ofStmt q).m) (l' := ()) Empty.elim none rfl h
end Frag
end Groundwork.TM
