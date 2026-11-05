-- Prove2me | solution 1 for Groundwork.Grid.topW_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T17:11:32.636743+00:00
-- url     : https://prove2.me/submissions/4b435db3-afc2-46f7-905f-12b45322f043

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachines_Math_Sparse
import Definitions.Def_Groundwork_Grid_Expand
import Definitions.Def_StepMachines_Math_CutWord

set_option autoImplicit false
section
section
open Groundwork Groundwork.Grid
open Finset
open Groundwork.Prog (tb capW)
namespace Groundwork.Grid
theorem _root_.solution (tr : Bool) {n : ℕ} (c : ℕ) {x y : List Bool} (w : List Bool) (hx : x.length = n) :
    topW tr x y w = (sideBit tr).Top ((Code.sparse (sideS0 tr) n c).dec w) (bitsOf n x) (bitsOf n y) := by
  subst hx
  rw [topW, prod_range]
  rfl
end Groundwork.Grid
