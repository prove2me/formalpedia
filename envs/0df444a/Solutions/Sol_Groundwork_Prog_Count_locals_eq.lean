-- Prove2me | solution 1 for Groundwork.Prog.Count.locals_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T15:58:00.617294+00:00
-- url     : https://prove2.me/submissions/2c954ca3-a872-4c16-ac27-44f484c89ef8

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachines_Prog_Spec
import Definitions.Def_StepMachines_Math_SatNet
import Definitions.Def_StepMachines_Prog_CountNet
import Theorems.Thm_Groundwork_Prog_Count_slotsOf_eq
import Theorems.Thm_Groundwork_Prog_Count_mu_le

set_option autoImplicit false
section
open Groundwork Groundwork.Prog
open Finset SatNet
open Groundwork.Prog.Count
namespace Groundwork.Prog.Count
theorem _root_.solution {g : ℕ} (hg : 0 < g) (k : ℕ) (φ : Fml) : locals g k φ = List.range (mu g φ * k) := by
  rw [locals, slotsOf_eq, List.take_range, min_eq_left (Nat.mul_le_mul_right k (mu_le hg φ))]
end Groundwork.Prog.Count
