-- Prove2me | solution 1 for Groundwork.Grid.sideCut_factors_row
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T17:12:03.24872+00:00
-- url     : https://prove2.me/submissions/e830266e-1e7b-4fa9-b5c3-e0b305646a84

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachines_Math_Sparse
import Definitions.Def_Groundwork_Grid_Expand
import Definitions.Def_StepMachines_Math_CutWord
import Theorems.Thm_Groundwork_A_rows
import Theorems.Thm_Groundwork_rowLabels_eq


set_option autoImplicit false
section
section
open Groundwork Groundwork.Grid
open Finset
open Groundwork.Prog (tb capW)
namespace Groundwork.Grid
theorem _root_.solution {n i : ℕ} (h : i ≤ n) : (sideCut false n i).Factors (A n i) := by
  intro x y u v
  rw [A_rows, rowLabels_eq h]
  rfl
end Groundwork.Grid
