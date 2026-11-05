-- Prove2me | solution 1 for Groundwork.Grid.mixed_inj
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:06:55.295463+00:00
-- url     : https://prove2.me/submissions/7e6153ed-ad5d-486f-b00f-a203a3090269

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachines_Prog_GridDefs
import Definitions.Def_StepMachines_Prog_Chunks
import Definitions.Def_Groundwork_Grid_Expand
import Definitions.Def_StepMachines_Math_Digits

set_option autoImplicit false
section
section
open Groundwork Groundwork.Grid
open Finset
open Groundwork.Prog (digit nRect)
namespace Groundwork.Grid
theorem _root_.solution {n x x' y y' : ℕ} (hy : y < n) (hy' : y' < n) (h : x * n + y = x' * n + y') : x = x' ∧ y = y' := by
  have h1 : (x * n + y) / n = x := by
    rw [mul_comm, Nat.mul_add_div (by omega), Nat.div_eq_of_lt hy, add_zero]
  have h2 : (x' * n + y') / n = x' := by
    rw [mul_comm, Nat.mul_add_div (by omega), Nat.div_eq_of_lt hy', add_zero]
  have hx : x = x' := by rw [← h1, h, h2]
  subst hx
  exact ⟨rfl, by omega⟩
end Groundwork.Grid
