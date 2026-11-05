-- Prove2me | solution 1 for Groundwork.Grid.mixed_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T15:40:10.476828+00:00
-- url     : https://prove2.me/submissions/7c908697-a819-45fa-862a-da7d37850378

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachines_Prog_GridDefs
import Definitions.Def_StepMachines_Prog_Chunks
import Definitions.Def_Groundwork_Grid_Expand
import Definitions.Def_StepMachines_Math_Digits

set_option autoImplicit false
section
section
open Groundwork Groundwork.Grid
open Finset
open Groundwork.Prog (digit nRect)
namespace Groundwork.Grid
theorem _root_.solution {m n x y : ℕ} (hx : x < m) (hy : y < n) : x * n + y < m * n := by
  calc x * n + y < x * n + n := by omega
    _ = (x + 1) * n := by ring
    _ ≤ m * n := Nat.mul_le_mul_right _ hx
end Groundwork.Grid
