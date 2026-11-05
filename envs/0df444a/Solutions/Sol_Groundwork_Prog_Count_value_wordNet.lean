-- Prove2me | solution 1 for Groundwork.Prog.Count.value_wordNet
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T17:27:38.461545+00:00
-- url     : https://prove2.me/submissions/d310720a-4dab-40e6-9a07-049bfe84b181

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachines_Prog_Spec
import Definitions.Def_StepMachines_Math_SatNet
import Definitions.Def_StepMachines_Prog_CountNet
import Theorems.Thm_Groundwork_Prog_Count_bijOn_bits
import Theorems.Thm_Groundwork_Prog_Count_wF_eq
import Theorems.Thm_P2M_Groundwork_Prog_Count_wordNet___eq_78331b67b704
import Theorems.Thm_Groundwork_Prog_Count_value_congr
import Theorems.Thm_Groundwork_Prog_Count_le_mul_mu

set_option autoImplicit false
section
open Groundwork Groundwork.Prog
open Finset SatNet
open Groundwork.Prog.Count
variable {g μ k : ℕ} {φ : Fml}
namespace Groundwork.Prog.Count
theorem _root_.solution (hg : 0 < g) : (wordNet g k φ).value = (net φ g (mu g φ) k).value :=
  value_congr _ _ bits (fun _ => bijOn_bits) (fun a z => wF_eq hg (le_mul_mu hg φ) a z)
    fun _ _ h z z' => wordNet_Ψ_eq hg (le_mul_mu hg φ) h z z'
end Groundwork.Prog.Count
