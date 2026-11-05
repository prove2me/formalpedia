-- Prove2me | solution 1 for Groundwork.Prog.NetE.psi_natAbs
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:48:36.828779+00:00
-- url     : https://prove2.me/submissions/f44683ac-501e-4261-8a38-91648d1b3fc1

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachines_Prog_NetProg
import Definitions.Def_StepMachines_Prog_NetRun
import Theorems.Thm_Groundwork_Prog_NetE_natAbs_le_of_abs_le
import Theorems.Thm_Groundwork_sum_toWord


set_option autoImplicit false
section
open Groundwork Groundwork.Prog Groundwork.Prog.NetE
open Finset Stepped
variable {C : Type} (K g : ℕ) (Np : PNet C)
variable {K g Np} {c : C} {N : Network (Fin g) (List Bool) (List Bool)} {P B t S : ℕ}
namespace Groundwork.Prog.NetE
theorem _root_.solution (hN : Np.Presents c N t S) (hS : N.Sized P B) {a b : ℕ} (ha : a < g) (hb : b < g)
    (hab : a ≠ b) (z z' : List Bool) :
    (∑ y ∈ range (2 ^ Np.cap c a b), valF N a b z (toWord (Np.cap c a b) y) *
      valF N b a z' (toWord (Np.cap c a b) y)).natAbs ≤ 2 ^ B := by
  have e : ∑ y ∈ range (2 ^ Np.cap c a b), valF N a b z (toWord (Np.cap c a b) y) *
      valF N b a z' (toWord (Np.cap c a b) y) = N.Ψ ⟨a, ha⟩ ⟨b, hb⟩ z z' := by
    rw [sum_toWord (Np.cap c a b) fun θ => valF N a b z θ * valF N b a z' θ, Network.Ψ,
      hN.lab_eq ⟨a, ha⟩ ⟨b, hb⟩ fun h => hab (congrArg Fin.val h)]
    refine sum_congr rfl fun θ _ => ?_
    rw [show valF N a b z θ = N.f ⟨a, ha⟩ ⟨b, hb⟩ z θ from dif_pos ⟨ha, hb⟩,
      show valF N b a z' θ = N.f ⟨b, hb⟩ ⟨a, ha⟩ z' θ from dif_pos ⟨hb, ha⟩]
  rw [e]
  exact natAbs_le_of_abs_le (by
    exact_mod_cast hS.abs_Ψ ⟨a, ha⟩ ⟨b, hb⟩ z z' fun h => hab (congrArg Fin.val h))
end Groundwork.Prog.NetE
