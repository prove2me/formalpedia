-- Prove2me | solution 1 for Groundwork.Prog.length_he_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T17:17:48.453037+00:00
-- url     : https://prove2.me/submissions/db38bcfc-f408-40d8-81f7-e34054c71f68

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachines_Prog_GridDefs
import Definitions.Def_StepMachines_Prog_CutProg
import Definitions.Def_StepMachines_Math_SideX
import Definitions.Def_StepMachines_Prog_Side

set_option autoImplicit false
section
section
open Groundwork Groundwork.Prog
open Finset Stepped
open Groundwork.Grid (he node c2 rectDig sideChunk sideItem sideCap)
namespace Groundwork.Prog
theorem _root_.solution (g ℓ : ℕ) (z : List Bool) (x u : ℕ) : (he g ℓ z x u).length ≤ ℓ := by
  unfold he block
  rw [List.length_take]
  exact Nat.min_le_left _ _
end Groundwork.Prog
