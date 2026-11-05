-- Prove2me | solution 1 for Groundwork.Stepped.guard_runs_none
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T15:57:16.645705+00:00
-- url     : https://prove2.me/submissions/fdd98148-0bf8-4dda-8434-a95044d37124

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachines_Prog_Stepped
import Definitions.Def_StepMachines_Math_SparsifyTree
import Definitions.Def_StepMachines_Prog_Walk

set_option autoImplicit false
section
open Groundwork Groundwork.Stepped
open Groundwork.Sparsify (leaves)
variable {α β τ ν : Type}
namespace Groundwork.Stepped
theorem _root_.solution {sel : τ → Option ν} {T : Stepped ν β} {d : β} {x : τ} (h : sel x = none) :
    (guard sel T d).Runs x 0 1 d := by
  change (guard sel T d).Reaches 1 d ((sel x).map T.init) 0
  rw [h]
  exact .halt rfl le_rfl
end Groundwork.Stepped
