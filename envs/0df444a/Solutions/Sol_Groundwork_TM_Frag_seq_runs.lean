-- Prove2me | solution 1 for Groundwork.TM.Frag.seq_runs
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:42:09.440207+00:00
-- url     : https://prove2.me/submissions/6a1478ba-ffcc-4ce8-a4a7-3b112ed556dd

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ToTuring_TM_Run
import Definitions.Def_ToTuring_TM_Frag
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
theorem _root_.solution {P Q : Frag Γ σ} {v : σ} {S S' S'' : ∀ k, List (Γ k)} {n n' : ℕ} (hP : P.Runs v S n S')
    (hQ : Q.Runs v S' n' S'') : (P.seq Q).Runs v S (n + n') S'' :=
  (run_place (M' := (P.seq Q).m) Sum.inl (some (.inr Q.entry)) (fun _ => rfl) hP).trans
    (run_place (M' := (P.seq Q).m) Sum.inr none (fun _ => rfl) hQ)
end Frag
end Groundwork.TM
