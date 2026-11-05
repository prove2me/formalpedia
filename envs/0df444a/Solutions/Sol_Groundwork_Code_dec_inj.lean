-- Prove2me | solution 1 for Groundwork.Code.dec_inj
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T17:06:22.51555+00:00
-- url     : https://prove2.me/submissions/10b18066-4a64-4088-88b7-cb1d688d51f0

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachines_Math_Code
import Mathlib.Data.List.GetD
import Definitions.Def_StepMachines_Math_CodeMore

set_option autoImplicit false
section
open Groundwork
open Finset
variable {X Y : Type*}
open Groundwork.Code
variable {S : Finset X} {n : ℕ}
namespace Groundwork.Code
theorem _root_.solution (c : Code S n) {w w' : List Bool} (hw : w ∈ c.D) (hw' : w' ∈ c.D) :
    c.dec w = c.dec w' ↔ w = w' := c.bij.injOn.eq_iff hw hw'
end Groundwork.Code
