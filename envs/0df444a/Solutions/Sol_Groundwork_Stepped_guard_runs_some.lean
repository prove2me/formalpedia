-- Prove2me | solution 1 for Groundwork.Stepped.guard_runs_some
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T17:23:59.57762+00:00
-- url     : https://prove2.me/submissions/f216540b-d1aa-4279-8ee4-c2e2717941af

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachines_Prog_Stepped
import Definitions.Def_StepMachines_Math_SparsifyTree
import Definitions.Def_StepMachines_Prog_Walk
import Theorems.Thm_Groundwork_Stepped_guard_reaches

set_option autoImplicit false
section
open Groundwork Groundwork.Stepped
open Groundwork.Sparsify (leaves)
variable {α β τ ν : Type}
namespace Groundwork.Stepped
theorem _root_.solution {sel : τ → Option ν} {T : Stepped ν β} {d b : β} {x : τ} {a : ν} {t S : ℕ}
    (h : sel x = some a) (hT : T.Runs a t S b) : (guard sel T d).Runs x t (S + 1) b := by
  change (guard sel T d).Reaches (S + 1) b ((sel x).map T.init) t
  rw [h]
  exact guard_reaches hT
end Groundwork.Stepped
