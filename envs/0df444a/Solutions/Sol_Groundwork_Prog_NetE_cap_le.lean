-- Prove2me | solution 1 for Groundwork.Prog.NetE.cap_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T15:58:32.948086+00:00
-- url     : https://prove2.me/submissions/a9f037e3-8806-44d0-990e-240a591c8159

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachines_Prog_NetProg
import Definitions.Def_StepMachines_Prog_NetRun

set_option autoImplicit false
section
open Groundwork Groundwork.Prog Groundwork.Prog.NetE
open Finset Stepped
variable {C : Type} (K g : ℕ) (Np : PNet C)
variable {K g Np} {c : C} {N : Network (Fin g) (List Bool) (List Bool)} {P B t S : ℕ}
namespace Groundwork.Prog.NetE
theorem _root_.solution (hN : Np.Presents c N t S) (hS : N.Sized P B) {a b : Fin g} (hab : a ≠ b) :
    Np.cap c a b ≤ P := by
  rw [← hN.c_eq _ _ hab]
  exact (single_le_sum (f := fun b => N.c a b) (fun _ _ => Nat.zero_le _)
    (mem_erase.2 ⟨hab.symm, mem_univ b⟩)).trans (hS.sum_c a)
end Groundwork.Prog.NetE
