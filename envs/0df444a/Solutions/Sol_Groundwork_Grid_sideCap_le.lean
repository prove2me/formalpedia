-- Prove2me | solution 1 for Groundwork.Grid.sideCap_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T17:15:12.94492+00:00
-- url     : https://prove2.me/submissions/65f408d6-1b2a-4502-9e5b-91bb84562c2c

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachines_Math_SideCodes
import Definitions.Def_StepMachines_Math_CodeSeq
import Definitions.Def_StepMachines_Math_Pull
import Definitions.Def_Groundwork_Grid_Size
import Definitions.Def_StepMachines_Math_SideNet
import Theorems.Thm_Groundwork_Grid_digit_le
import Theorems.Thm_Groundwork_Grid_sideCut_cap_le
import Theorems.Thm_Groundwork_Grid_two_mul_c2_le
import Theorems.Thm_Groundwork_Prog_digit_le


set_option autoImplicit false
section
section
open Groundwork Groundwork.Grid
open Finset
open Groundwork.Prog (digit nRect tb capW priceRow priceCol BoundedInst SideNet)
namespace Groundwork.Grid
theorem _root_.solution {g n : ℕ} (tr : Bool) (hn : 1 ≤ n) (y a b : ℕ) : sideCap g tr n y a b ≤ g * n + 2 * g ^ 2 * n := by
  unfold sideCap
  have h1 : ∑ κ ∈ range (c2 g), rectLen g tr n y (tri (min a b) (max a b)) κ ≤ ∑ _κ ∈ range (c2 g), 2 * 2 * n :=
    Finset.sum_le_sum fun κ _ => sideCut_cap_le tr hn (digit_le _ _ _)
  rw [Finset.sum_const, card_range, smul_eq_mul] at h1
  have h2 := Nat.mul_le_mul_right (2 * n) (two_mul_c2_le g)
  have e1 : c2 g * (2 * 2 * n) = 2 * c2 g * (2 * n) := by ring
  have e2 : g ^ 2 * (2 * n) = 2 * g ^ 2 * n := by ring
  omega
end Groundwork.Grid
