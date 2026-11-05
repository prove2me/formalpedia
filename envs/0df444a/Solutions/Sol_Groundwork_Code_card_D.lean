-- Prove2me | solution 1 for Groundwork.Code.card_D
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T17:06:09.496613+00:00
-- url     : https://prove2.me/submissions/61fcf680-573f-4690-9be5-9f5755d22cca

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Groundwork_Net_Net
import Definitions.Def_StepMachines_Prog_Chunks
import Definitions.Def_StepMachines_Math_Code
import Theorems.Thm_Groundwork_Code_image_dec

set_option autoImplicit false
section
open Groundwork
open Finset
variable {X Y : Type*}
open Groundwork.Code
variable {S : Finset X} {n : ℕ}
namespace Groundwork.Code
theorem _root_.solution (c : Code S n) : #c.D = #S := by
  classical
  exact (card_image_of_injOn c.bij.injOn).symm.trans (congrArg card c.image_dec)
end Groundwork.Code
