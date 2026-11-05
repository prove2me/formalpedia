-- Prove2me | solution 1 for Groundwork.SatNet.Link.fst_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T17:20:12.737691+00:00
-- url     : https://prove2.me/submissions/7140e1bf-ffe2-424e-8a26-44368f467b37

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ThreeSatStatement
import Definitions.Def_Groundwork_Net_Defs
import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Mathlib.Tactic.Ring
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Definitions.Def_StepMachines_Math_SatNet
import Theorems.Thm_Groundwork_SatNet_idx_lt_of_fst_lt

set_option autoImplicit false
section
open Groundwork Groundwork.SatNet
open Finset
variable {V : Type}
variable [DecidableEq V]
variable {φ : List (List (V × Bool))} {g μ k : ℕ}
omit [DecidableEq V]
namespace Groundwork.SatNet
namespace Link
theorem _root_.solution {p q : Slot g μ k} (h : Link φ p q) : p.1 ≤ q.1 := by
  by_contra hlt
  exact absurd h.1 (not_lt.2 (idx_lt_of_fst_lt (not_le.1 hlt)).le)
end Link
end Groundwork.SatNet
