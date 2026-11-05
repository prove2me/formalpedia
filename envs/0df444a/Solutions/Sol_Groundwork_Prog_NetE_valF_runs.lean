-- Prove2me | solution 1 for Groundwork.Prog.NetE.valF_runs
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:48:14.285726+00:00
-- url     : https://prove2.me/submissions/d4adb6ee-29ff-471e-af26-50f7b26d5df7

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
theorem _root_.solution (hN : Np.Presents c N t S) (hS : N.Sized P B) {a b : ℕ} (ha : a < g) (hb : b < g)
    (hab : a ≠ b) {z θ : List Bool} (hz : z.length = Np.n c a) (hθ : θ.length = Np.cap c a b) :
    Np.f.Runs (c, ((a, b), (z, θ))) t S (valF N a b z θ) ∧ (valF N a b z θ).natAbs ≤ 2 ^ B := by
  have e : valF N a b z θ = N.f ⟨a, ha⟩ ⟨b, hb⟩ z θ := dif_pos ⟨ha, hb⟩
  rw [e]
  exact ⟨hN.f_runs ⟨a, ha⟩ ⟨b, hb⟩ z θ (fun h => hab (congrArg Fin.val h)) hz hθ,
    natAbs_le_of_abs_le (by exact_mod_cast hS.abs_f ⟨a, ha⟩ ⟨b, hb⟩ z θ)⟩
end Groundwork.Prog.NetE
