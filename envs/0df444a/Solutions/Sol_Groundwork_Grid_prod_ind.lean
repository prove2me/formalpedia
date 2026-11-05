-- Prove2me | solution 1 for Groundwork.Grid.prod_ind
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:06:16.710955+00:00
-- url     : https://prove2.me/submissions/94791f8c-bc86-48d9-8b69-cd9faa5b89a8

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Groundwork_Grid_Defs
import Definitions.Def_Groundwork_Net_Net
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Definitions.Def_Groundwork_Grid_Grid
import Theorems.Thm_Groundwork_Grid_boole_congr

set_option autoImplicit false
section
section
open Groundwork Groundwork.Grid
open Finset
variable {J ρ γ α : Type}
variable [Fintype ρ] [LinearOrder ρ] [Fintype γ] [LinearOrder γ] [Fintype α] [DecidableEq α]
namespace Groundwork.Grid
theorem _root_.solution {ι : Type} (s : Finset ι) (p : ι → Prop) [DecidablePred p] {P : Prop} [Decidable P]
    (h : P ↔ ∀ i ∈ s, p i) : ∏ i ∈ s, (if p i then (1 : ℤ) else 0) = if P then 1 else 0 := by
  rw [Finset.prod_boole]
  exact boole_congr h.symm
end Groundwork.Grid
