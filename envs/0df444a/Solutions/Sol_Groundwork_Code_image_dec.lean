-- Prove2me | solution 1 for Groundwork.Code.image_dec
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:06:15.228287+00:00
-- url     : https://prove2.me/submissions/740e5a49-0626-4528-aba0-f6726fb701eb

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
theorem _root_.solution [DecidableEq X] (c : Code S n) : c.D.image c.dec = S :=
  Finset.coe_injective (by rw [coe_image]; exact c.bij.image_eq)
end Groundwork.Code
