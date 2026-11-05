-- Prove2me | solution 1 for Groundwork.Prog.Count.le_mul_mu
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T17:21:02.868803+00:00
-- url     : https://prove2.me/submissions/065541d2-4461-4a7c-9268-ce0e22d5e894

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachines_Prog_Spec
import Definitions.Def_StepMachines_Math_SatNet
import Definitions.Def_StepMachines_Prog_CountNet
import Theorems.Thm_Groundwork_SatNet_le_mul_ceil


set_option autoImplicit false
section
open Groundwork Groundwork.Prog
open Finset SatNet
open Groundwork.Prog.Count
variable {g μ k : ℕ} {φ : Fml}
namespace Groundwork.Prog.Count
theorem _root_.solution {g : ℕ} (hg : 0 < g) (φ : Fml) : φ.length ≤ g * mu g φ := SatNet.le_mul_ceil _ hg
end Groundwork.Prog.Count
