-- Prove2me | solution 1 for Groundwork.Grid.sideCut_factors_col
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T17:11:52.392376+00:00
-- url     : https://prove2.me/submissions/32541cfb-149a-48e9-b132-ef2f9704c66c

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachines_Math_Sparse
import Definitions.Def_Groundwork_Grid_Expand
import Definitions.Def_StepMachines_Math_CutWord
import Theorems.Thm_Groundwork_A_cols
import Theorems.Thm_Groundwork_colLabels_eq


set_option autoImplicit false
section
section
open Groundwork Groundwork.Grid
open Finset
open Groundwork.Prog (tb capW)
namespace Groundwork.Grid
theorem _root_.solution (n i : ℕ) : (sideCut true n i).Factors fun x u y v => A n i x y u v := by
  intro x u y v
  change A n i x y u v = _
  rw [A_cols, colLabels_eq]
  rfl
end Groundwork.Grid
