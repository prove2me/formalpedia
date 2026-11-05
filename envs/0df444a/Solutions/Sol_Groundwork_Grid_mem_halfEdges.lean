-- Prove2me | solution 1 for Groundwork.Grid.mem_halfEdges
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T17:09:36.915735+00:00
-- url     : https://prove2.me/submissions/ce5549c1-5d93-41b2-a0fc-62356afc81b6

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Groundwork_Grid_Defs
import Definitions.Def_Groundwork_Net_Net
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Definitions.Def_Groundwork_Grid_Grid
import Theorems.Thm_P2M_Groundwork_Grid_prod___rows_436f8d628931

set_option autoImplicit false
section
section
open Groundwork Groundwork.Grid
open Finset
variable {J ρ γ α : Type}
variable [Fintype ρ] [LinearOrder ρ] [Fintype γ] [LinearOrder γ] [Fintype α] [DecidableEq α]
omit [DecidableEq α]
namespace Groundwork.Grid
theorem _root_.solution [Fintype J] [DecidableEq J] (d : α) (ℓ : J → J → α) :
    ℓ ∈ (Fintype.piFinset fun w : J => tuples (fun w' => w' ≠ w) (fun _ => (univ : Finset α)) d) ↔
      ∀ w, ℓ w w = d := by
  simp only [Fintype.mem_piFinset, tuples]
  constructor
  · intro h w
    simpa using h w w
  · intro h w w'
    by_cases hw : w' = w
    · subst hw; simp [h]
    · simp [hw]
end Groundwork.Grid
