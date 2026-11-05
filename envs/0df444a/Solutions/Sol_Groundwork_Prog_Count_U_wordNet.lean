-- Prove2me | solution 1 for Groundwork.Prog.Count.U_wordNet
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T17:28:56.494252+00:00
-- url     : https://prove2.me/submissions/ce4d3da8-df57-472a-af11-4f4442d99c70

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachines_Prog_Spec
import Definitions.Def_StepMachines_Math_SatNet
import Definitions.Def_StepMachines_Prog_CountNet
import Theorems.Thm_Groundwork_Prog_Count_wordNet_c
import Theorems.Thm_Groundwork_Prog_Count_le_mul_mu

set_option autoImplicit false
section
open Groundwork Groundwork.Prog
open Finset SatNet
open Groundwork.Prog.Count
variable {g μ k : ℕ} {φ : Fml}
namespace Groundwork.Prog.Count
theorem _root_.solution (hg : 0 < g) : (wordNet g k φ).U = (net φ g (mu g φ) k).U := by
  unfold Network.U
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => wordNet_c hg (le_mul_mu hg φ) a b
end Groundwork.Prog.Count
