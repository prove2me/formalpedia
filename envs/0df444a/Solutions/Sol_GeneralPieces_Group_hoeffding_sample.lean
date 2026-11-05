-- Prove2me | solution 1 for GeneralPieces.Group.hoeffding_sample
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:46:26.964489+00:00
-- url     : https://prove2.me/submissions/bda36d57-c664-4f47-a5f2-e874af8e426b

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Defs
import Definitions.Def_ClauseBound_Group_Grouping
import Definitions.Def_GeneralPieces_Group_CaseII
import Theorems.Thm_ClauseBound_Group_card_sample_tail_le


set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Group
open Finset ClauseBound.Group ClauseBound.Group.Grouping
variable {K n : ℕ}
namespace GeneralPieces.Group
theorem _root_.solution {ι : Type} [DecidableEq ι] (s : Finset ι) (x : ι → ℝ) {R ζ : ℝ} (hR : 0 < R) (hx : ∀ i ∈ s, 0 ≤ x i ∧ x i ≤ R)
    (hs : s.Nonempty) (j : ℕ) (hζ : 0 ≤ ζ) :
    (#{S ∈ powersetCard j s | j * ((∑ i ∈ s, x i) / #s) + ζ * j * R ≤ ∑ i ∈ S, x i} : ℝ) ≤ Real.exp (-(2 * j * ζ ^ 2)) * #(powersetCard j s) := by
  rw [card_powersetCard]
  exact card_sample_tail_le s x hR hx hs j hζ
end GeneralPieces.Group
