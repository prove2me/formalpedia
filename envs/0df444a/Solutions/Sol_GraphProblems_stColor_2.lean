-- Prove2me | solution 2 for GraphProblems.stColor
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T08:18:45.841148+00:00
-- url     : https://prove2.me/submissions/cac9e29c-6ed0-470d-92bc-82b7e72a6dd6

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GraphProblems_Blocks
import Definitions.Def_GraphProblems_Color
import Theorems.Thm_GraphProblems_Color_sat_asg
import Theorems.Thm_GraphProblems_Color_asg_injective
import Theorems.Thm_GraphProblems_Color_exists_coloring

set_option autoImplicit false
section
section
open GraphProblems
open Groundwork Groundwork.Prog CountKSat Finset
open Blocks Color
namespace GraphProblems
theorem _root_.solution (hAdj : StAdj) : StColor := by
  intro k n G
  rw [numColorings, cntN, ← Fintype.card_coe, ← Nat.card_eq_fintype_card]
  have hmem : ∀ col : G.Coloring (Fin k),
      asg col ∈ univ.filter fun a : Fin (n * k) → Bool => ∀ C ∈ colorF k n (matrix G), ∃ l ∈ C, CountKSat.ext a l.1 = l.2 :=
    fun col => mem_filter.2 ⟨mem_univ _, sat_asg hAdj G col⟩
  refine (Nat.card_congr (Equiv.ofBijective (fun col : G.Coloring (Fin k) => (⟨asg col, hmem col⟩ :
    {a // a ∈ univ.filter fun a : Fin (n * k) → Bool => ∀ C ∈ colorF k n (matrix G), ∃ l ∈ C, CountKSat.ext a l.1 = l.2})) ⟨?_, ?_⟩)).symm
  · intro col col' h
    exact DFunLike.coe_injective (asg_injective (congrArg Subtype.val h))
  · rintro ⟨a, ha⟩
    obtain ⟨col, hcol⟩ := exists_coloring hAdj G a (mem_filter.1 ha).2
    exact ⟨col, Subtype.ext hcol⟩
end GraphProblems
