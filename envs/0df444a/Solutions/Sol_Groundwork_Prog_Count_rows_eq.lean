-- Prove2me | solution 1 for Groundwork.Prog.Count.rows_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:10:16.329134+00:00
-- url     : https://prove2.me/submissions/bde7f63a-3694-4ee3-9b58-d0b80eef35c7

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachines_Prog_Spec
import Definitions.Def_StepMachines_Math_SatNet
import Definitions.Def_StepMachines_Prog_CountNet
import Theorems.Thm_Groundwork_Prog_Count_mu_le

set_option autoImplicit false
section
open Groundwork Groundwork.Prog
open Finset SatNet
open Groundwork.Prog.Count
namespace Groundwork.Prog.Count
theorem _root_.solution {g : ℕ} (hg : 0 < g) (φ : Fml) : rows g φ = List.range (mu g φ) := by
  rw [rows, List.take_range, min_eq_left (mu_le hg φ)]
end Groundwork.Prog.Count
