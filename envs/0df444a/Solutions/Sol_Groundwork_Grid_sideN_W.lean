-- Prove2me | solution 1 for Groundwork.Grid.sideN_W
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T17:15:43.925846+00:00
-- url     : https://prove2.me/submissions/1543c026-3242-4d03-b95e-230bd6c3a068

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachines_Math_SideNet
import Definitions.Def_StepMachines_Math_SideX
import Theorems.Thm_Groundwork_Grid_bitsOf_inj
import Theorems.Thm_Groundwork_Grid_gridE_symm_val
import Theorems.Thm_Groundwork_Grid_length_he
import Theorems.Thm_Groundwork_Grid_node_lt
import Theorems.Thm_Groundwork_Grid_sideR_nodeC
import Theorems.Thm_Groundwork_Grid_stC_dec
import Theorems.Thm_Groundwork_length_block


set_option autoImplicit false
section
section
open Groundwork Groundwork.Grid
open Finset
namespace Groundwork.Grid
theorem _root_.solution (g : ℕ) (tr : Bool) (n : ℕ) (Rm : Inst (Fin (g * g)) (List Bool)) (y : ℕ) (a : Fin g) {z : List Bool}
    (hz : z.length = g ^ 3 * n) :
    (sideN g tr n Rm y).W a z =
      (∏ i : Fin g, if (he g n z i (node g tr a i)).all (!·) = true then
          Rm ((gridE g tr).symm (a, i)) (fun u => if u = (gridE g tr).symm (a, i) then [] else he g n z i u)
        else 0) *
      ∏ q ∈ pairs (Fin g), if he g n z q.1 (node g tr a q.2) = he g n z q.2 (node g tr a q.1) then 1 else 0 := by
  have hn : ∀ i : Fin g, node g tr a i < g * g := fun i => node_lt tr a.2 i.2
  change rowW (sideR g tr n Rm) a ((stC g tr n).dec z) = _
  unfold rowW
  congr 1
  · refine prod_congr rfl fun i _ => ?_
    have h := sideR_nodeC g tr n Rm (a, i) (wn := block (g * g * n) i z) (length_block (by
      rw [hz, show g ^ 3 * n = g * (g * g * n) by ring]
      exact Nat.mul_le_mul_right _ i.2))
    rw [gridE_symm_val] at h
    exact h
  · refine prod_congr rfl fun q _ => if_congr ?_ rfl rfl
    rw [stC_dec, stC_dec]
    exact bitsOf_inj (length_he hz q.1.2 (hn q.2)) (length_he hz q.2.2 (hn q.1))
end Groundwork.Grid
