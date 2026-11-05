-- Prove2me | solution 1 for Groundwork.Prog.NetE.valW_runs
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:46:20.992199+00:00
-- url     : https://prove2.me/submissions/3f99c856-c385-43f8-98c0-cca80cef66f2

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachines_Prog_NetProg
import Definitions.Def_StepMachines_Prog_NetRun
import Theorems.Thm_Groundwork_Prog_NetE_natAbs_le_of_abs_le

set_option autoImplicit false
section
open Groundwork Groundwork.Prog Groundwork.Prog.NetE
open Finset Stepped
variable {C : Type} (K g : ℕ) (Np : PNet C)
variable {K g Np} {c : C} {N : Network (Fin g) (List Bool) (List Bool)} {P B t S : ℕ}
namespace Groundwork.Prog.NetE
theorem _root_.solution (hN : Np.Presents c N t S) (hS : N.Sized P B) {a : ℕ} (ha : a < g) {z : List Bool}
    (hz : z.length = Np.n c a) : Np.W.Runs (c, (a, z)) t S (valW N a z) ∧ (valW N a z).natAbs ≤ 2 ^ B := by
  have e : valW N a z = N.W ⟨a, ha⟩ z := dif_pos ha
  rw [e]
  exact ⟨hN.W_runs ⟨a, ha⟩ z hz, natAbs_le_of_abs_le (by exact_mod_cast hS.abs_W ⟨a, ha⟩ z)⟩
end Groundwork.Prog.NetE
