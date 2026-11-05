-- Prove2me | solution 1 for Groundwork.Grid.card_sideCut_lab
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T17:09:52.156812+00:00
-- url     : https://prove2.me/submissions/8c3d2dbe-8846-409f-9347-8eeb370a79fb

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachines_Math_Sparse
import Definitions.Def_Groundwork_Grid_Expand
import Definitions.Def_StepMachines_Math_CutWord
import Theorems.Thm_Groundwork_Code_card_le


set_option autoImplicit false
section
section
open Groundwork Groundwork.Grid
open Finset
open Groundwork.Prog (tb capW)
namespace Groundwork.Grid
theorem _root_.solution (tr : Bool) (n i : ℕ) : #(sideCut tr n i).lab ≤ 2 ^ (sideCut tr n i).cap :=
  (Code.sparse (sideS0 tr) n (sideCnt tr n i)).card_le
end Groundwork.Grid
