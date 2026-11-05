-- Prove2me | solution 1 for Groundwork.Prog.NetE.n_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T15:58:34.100123+00:00
-- url     : https://prove2.me/submissions/8ef80450-96b6-4b18-9f5d-a261cd9fc8a3

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachines_Prog_NetProg
import Definitions.Def_StepMachines_Prog_NetRun
import Theorems.Thm_Groundwork_card_words


set_option autoImplicit false
section
open Groundwork Groundwork.Prog Groundwork.Prog.NetE
open Finset Stepped
variable {C : Type} (K g : ℕ) (Np : PNet C)
variable {K g Np} {c : C} {N : Network (Fin g) (List Bool) (List Bool)} {P B t S : ℕ}
namespace Groundwork.Prog.NetE
theorem _root_.solution (hN : Np.Presents c N t S) (hS : N.Sized P B) (a : Fin g) : Np.n c a ≤ P := by
  have := hS.card_S a
  rw [hN.S_eq, card_words] at this
  exact (Nat.pow_le_pow_iff_right (by omega)).1 this
end Groundwork.Prog.NetE
