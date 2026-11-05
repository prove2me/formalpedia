-- Prove2me | solution 1 for Groundwork.Code.full_cast
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T15:35:23.220232+00:00
-- url     : https://prove2.me/submissions/d46bd899-d67c-46fe-b699-81c30c6a5117

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Groundwork_Net_Net
import Definitions.Def_StepMachines_Prog_Chunks
import Definitions.Def_StepMachines_Math_Code

set_option autoImplicit false
section
open Groundwork
open Finset
variable {X Y : Type*}
open Groundwork.Code
variable {S : Finset X} {n : ℕ}
namespace Groundwork.Code
theorem _root_.solution (c : Code S n) {S' : Finset X} {n' : ℕ} (hS : S = S') (hn : n = n') (h : c.Full) :
    (c.cast hS hn).Full := by
  subst hn
  exact h
end Groundwork.Code
