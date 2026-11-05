-- Prove2me | solution 1 for Groundwork.Prog.NetE.length_lAt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:04:03.41269+00:00
-- url     : https://prove2.me/submissions/316b765f-e87e-4f3c-859e-787feff55481

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachines_Prog_NetProg
import Definitions.Def_StepMachines_Prog_NetRun
import Theorems.Thm_Groundwork_cut_eq_getD_beq
import Theorems.Thm_Groundwork_length_cut_of_le


set_option autoImplicit false
section
open Groundwork Groundwork.Prog Groundwork.Prog.NetE
open Finset Stepped
variable {C : Type} (K g : ℕ) (Np : PNet C)
variable {K g Np} {c : C} {N : Network (Fin g) (List Bool) (List Bool)} {P B t S : ℕ}
namespace Groundwork.Prog.NetE
theorem _root_.solution {x G G' : ℕ} {θ : List Bool} {p : ℕ × ℕ} (hp : p ∈ prs K g x G G')
    (hθ : lbLen K g Np c x G G' ≤ θ.length) : (lAt K g Np c x G G' θ p).length = Np.cap c p.1 p.2 := by
  unfold lAt lbLens
  rw [← cut_eq_getD_beq (fun p : ℕ × ℕ => Np.cap c p.1 p.2)]
  exact length_cut_of_le _ _ _ _ hθ hp
end Groundwork.Prog.NetE
