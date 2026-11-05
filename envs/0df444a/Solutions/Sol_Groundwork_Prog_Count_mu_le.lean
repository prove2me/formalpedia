-- Prove2me | solution 1 for Groundwork.Prog.Count.mu_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T15:31:26.014014+00:00
-- url     : https://prove2.me/submissions/b70d1d92-70df-4dbd-94f3-827c89f421f6

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachines_Prog_Spec
import Definitions.Def_StepMachines_Math_SatNet
import Definitions.Def_StepMachines_Prog_CountNet

set_option autoImplicit false
section
open Groundwork Groundwork.Prog
open Finset SatNet
open Groundwork.Prog.Count
namespace Groundwork.Prog.Count
theorem _root_.solution {g : ℕ} (hg : 0 < g) (φ : Fml) : mu g φ ≤ φ.length := by
  unfold mu
  rw [Nat.div_le_iff_le_mul_add_pred hg]
  have : φ.length ≤ g * φ.length := Nat.le_mul_of_pos_left _ hg
  omega
end Groundwork.Prog.Count
