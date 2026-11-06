-- Prove2me | solution 1 for GraphProblems.Blocks.ext_val
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T08:03:23.27742+00:00
-- url     : https://prove2.me/submissions/d839d503-be42-43b1-9258-993fcbdec211

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GraphProblems_Interfaces
import Mathlib.Algebra.BigOperators.Fin
import Definitions.Def_GraphProblems_Blocks

set_option autoImplicit false
section
section
open GraphProblems
open Groundwork Groundwork.Prog CountKSat Finset
open GraphProblems.Blocks
namespace GraphProblems.Blocks
theorem _root_.solution {n : ℕ} (a : Fin n → Bool) (k : Fin n) : ext a k = a k := dif_pos k.2
end GraphProblems.Blocks
