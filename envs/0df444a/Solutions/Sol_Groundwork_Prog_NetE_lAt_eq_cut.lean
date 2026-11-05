-- Prove2me | solution 1 for Groundwork.Prog.NetE.lAt_eq_cut
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:08:25.005351+00:00
-- url     : https://prove2.me/submissions/917cb963-c15a-4152-8100-b8fd38e41dc3

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachines_Prog_NetProg
import Definitions.Def_StepMachines_Prog_NetVal
import Theorems.Thm_Groundwork_idxOf_map_inj
import Theorems.Thm_Groundwork_Prog_NetE_map_prsF
import Theorems.Thm_Groundwork_Prog_NetE_lbLens_eq
import Theorems.Thm_Groundwork_cut_eq_getD


set_option autoImplicit false
section
open Groundwork
open Finset
open Groundwork.Prog Groundwork.Prog.NetE
variable {C : Type} {K g : ℕ} (Np : PNet C)
namespace Groundwork.Prog.NetE
theorem _root_.solution (c : C) (x G G' : ℕ) (θ : List Bool) (p : Fin g × Fin g) :
    lAt K g Np c x G G' θ (p.1.val, p.2.val) =
      cut (fun p : Fin g × Fin g => Np.cap c p.1.val p.2.val) [] (prsF K x G G') θ p := by
  rw [cut_eq_getD, ← lbLens_eq, lAt, ← map_prsF]
  have h := @idxOf_map_inj (Fin g × Fin g) (ℕ × ℕ) instBEqOfDecidableEq inferInstance _ _
      (fun p : Fin g × Fin g => (p.1.val, p.2.val))
      (fun p q h => by
        obtain ⟨h1, h2⟩ := Prod.mk.inj h
        exact Prod.ext (Fin.ext h1) (Fin.ext h2)) (prsF K x G G') p
  rw [h]
end Groundwork.Prog.NetE
