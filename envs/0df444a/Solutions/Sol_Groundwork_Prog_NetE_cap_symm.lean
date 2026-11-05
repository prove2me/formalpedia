-- Prove2me | solution 1 for Groundwork.Prog.NetE.cap_symm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T15:58:56.890295+00:00
-- url     : https://prove2.me/submissions/4a231ff8-ec9d-4b06-b2bf-459c8813e3b0

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
theorem _root_.solution (hN : Np.Presents c N t S) (hS : N.Sized P B) (a b : Fin g) :
    Np.cap c a b = Np.cap c b a := by
  by_cases hab : a = b
  · rw [hab]
  · rw [← hN.c_eq _ _ hab, ← hN.c_eq _ _ (Ne.symm hab), hS.c_symm]
end Groundwork.Prog.NetE
