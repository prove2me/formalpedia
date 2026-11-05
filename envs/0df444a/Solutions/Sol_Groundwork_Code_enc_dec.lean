-- Prove2me | solution 1 for Groundwork.Code.enc_dec
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T15:55:44.181205+00:00
-- url     : https://prove2.me/submissions/fe8513a9-2001-45bd-a7aa-e6cae339ad11

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
theorem _root_.solution (c : Code S n) {w : List Bool} (hw : w ∈ c.D) : c.enc (c.dec w) = w :=
  c.bij.injOn (mem_coe.2 (c.enc_mem (c.bij.mapsTo hw))) (mem_coe.2 hw) (c.dec_enc (c.bij.mapsTo hw))
end Groundwork.Code
