-- Prove2me | solution 1 for Groundwork.Grid.cutW_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T17:14:58.070665+00:00
-- url     : https://prove2.me/submissions/b7029729-afef-4ce5-baa5-548abc018b3c

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachines_Math_Sparse
import Definitions.Def_Groundwork_Grid_Expand
import Definitions.Def_StepMachines_Math_CutWord
import Theorems.Thm_Groundwork_Grid_topW_eq
import Theorems.Thm_Groundwork_Grid_botW_eq
import Theorems.Thm_Groundwork_mem_words
attribute [local simp] Groundwork.mem_words



set_option autoImplicit false
section
section
open Groundwork Groundwork.Grid
open Finset
open Groundwork.Prog (tb capW)
namespace Groundwork.Grid
theorem _root_.solution (tr top : Bool) {n i : ℕ} {x y w : List Bool} (hx : x.length = n)
    (hw : w.length = capW n (sideCnt tr n i)) :
    cutW tr top i x y w =
      if w ∈ (Code.sparse (sideS0 tr) n (sideCnt tr n i)).D then
        if top = true then
          (sideCut tr n i).top (bitsOf n x) (bitsOf n y) ((Code.sparse (sideS0 tr) n (sideCnt tr n i)).dec w)
        else (sideCut tr n i).bot (bitsOf n x) (bitsOf n y) ((Code.sparse (sideS0 tr) n (sideCnt tr n i)).dec w)
      else 0 := by
  subst hx
  have hD : w ∈ (Code.sparse (sideS0 tr) x.length (sideCnt tr x.length i)).D ↔
      validW x.length (sideCnt tr x.length i) w = true := by
    change w ∈ (words _).filter _ ↔ _
    rw [mem_filter, mem_words]
    exact and_iff_right hw
  rw [cutW]
  by_cases hv : validW x.length (sideCnt tr x.length i) w = true
  · rw [if_pos hv, if_pos (hD.2 hv), topW_eq tr (sideCnt tr x.length i) w rfl,
      botW_eq tr i (sideCnt tr x.length i) w rfl]
    rfl
  · rw [if_neg hv, if_neg fun h => hv (hD.1 h)]
end Groundwork.Grid
