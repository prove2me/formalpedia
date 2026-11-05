-- Prove2me | solution 1 for GraphProblems.Color.idx_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T18:39:41.626203+00:00
-- url     : https://prove2.me/submissions/12e3c17c-be44-4165-8155-717b9e458394

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GraphProblems_Blocks
import Definitions.Def_GraphProblems_Color

set_option autoImplicit false
section
section
open GraphProblems
open Groundwork Groundwork.Prog CountKSat Finset
open GraphProblems.Color
open Blocks
namespace GraphProblems.Color
theorem _root_.solution {n k v c : ℕ} (hv : v < n) (hc : c < k) : v * k + c < n * k :=
  calc v * k + c < (v + 1) * k := by rw [Nat.succ_mul]; omega
    _ ≤ n * k := Nat.mul_le_mul_right k hv
end GraphProblems.Color
