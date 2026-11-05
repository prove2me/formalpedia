-- Prove2me | solution 1 for Groundwork.Code.card_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T17:06:54.350461+00:00
-- url     : https://prove2.me/submissions/56eb26c1-a7d1-4404-98c6-ce08058f89e5

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Groundwork_Net_Net
import Definitions.Def_StepMachines_Prog_Chunks
import Definitions.Def_StepMachines_Math_Code
import Theorems.Thm_Groundwork_Code_D_subset
import Theorems.Thm_Groundwork_Code_card_D
import Theorems.Thm_Groundwork_card_words


set_option autoImplicit false
section
open Groundwork
open Finset
variable {X Y : Type*}
open Groundwork.Code
variable {S : Finset X} {n : ℕ}
namespace Groundwork.Code
theorem _root_.solution (c : Code S n) : #S ≤ 2 ^ n := by
  rw [← c.card_D, ← card_words]
  exact card_le_card c.D_subset
end Groundwork.Code
