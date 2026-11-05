-- Prove2me | solution 1 for GraphProblems.Color.mem_pairs
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T18:39:38.782536+00:00
-- url     : https://prove2.me/submissions/7ece405e-fc20-439d-bdac-d344b60364db

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
theorem _root_.solution {n : ℕ} {p : ℕ × ℕ} : p ∈ pairs n ↔ p.1 < n ∧ p.2 < n := by
  rw [pairs, List.mem_product, List.mem_range, List.mem_range]
end GraphProblems.Color
