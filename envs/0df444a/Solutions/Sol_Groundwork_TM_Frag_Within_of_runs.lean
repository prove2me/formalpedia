-- Prove2me | solution 1 for Groundwork.TM.Frag.Within.of_runs
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T15:28:38.165443+00:00
-- url     : https://prove2.me/submissions/a235182d-b1d2-4593-b197-46a5c19ad0bc

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ToTuring_TM_Run
import Definitions.Def_ToTuring_TM_Frag

set_option autoImplicit false
section
section
open Groundwork Groundwork.TM
open Turing
variable {K : Type} [DecidableEq K] {Γ : K → Type} {σ : Type}
attribute [instance] Frag.fin
variable {τ : Type}
namespace Groundwork.TM
namespace Frag.Within
theorem _root_.solution {P : Frag Γ (Option τ)} {S S' : ∀ k, List (Γ k)} {n : ℕ} (h : P.Runs none S n S') :
    P.Within S n S' := ⟨n, le_rfl, h⟩
end Frag.Within
end Groundwork.TM
