-- Prove2me | solution 1 for Groundwork.Code.D_subset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:06:14.185829+00:00
-- url     : https://prove2.me/submissions/8a62bb86-83f9-4150-b7f7-6fc43744b914

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Groundwork_Net_Net
import Definitions.Def_StepMachines_Prog_Chunks
import Definitions.Def_StepMachines_Math_Code
import Theorems.Thm_Groundwork_mem_words
attribute [local simp] Groundwork.mem_words



set_option autoImplicit false
section
open Groundwork
open Finset
variable {X Y : Type*}
open Groundwork.Code
variable {S : Finset X} {n : ℕ}
namespace Groundwork.Code
theorem _root_.solution (c : Code S n) : c.D ⊆ words n := fun w hw => mem_words.2 (c.len w hw)
end Groundwork.Code
