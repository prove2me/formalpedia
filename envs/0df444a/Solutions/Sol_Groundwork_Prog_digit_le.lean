-- Prove2me | solution 1 for Groundwork.Prog.digit_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T15:26:55.916227+00:00
-- url     : https://prove2.me/submissions/00e91edd-715e-4811-8535-54b6892bebad

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_NetworkStatements
import Definitions.Def_StepMachines_Prog_Spec
import Definitions.Def_StepMachines_Prog_Comb
import Definitions.Def_StepMachines_Math_GridArith
import Definitions.Def_StepMachines_Prog_GridDefs

set_option autoImplicit false
section
section
open Groundwork Groundwork.Prog
open Finset Stepped
namespace Groundwork.Prog
theorem _root_.solution (n y q : ℕ) : digit n y q ≤ n := Nat.lt_succ_iff.1 (Nat.mod_lt _ (Nat.succ_pos _))
end Groundwork.Prog
