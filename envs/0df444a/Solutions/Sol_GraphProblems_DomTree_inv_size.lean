-- Prove2me | solution 1 for GraphProblems.DomTree.inv_size
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T08:04:33.44356+00:00
-- url     : https://prove2.me/submissions/8fa36bbb-b6bd-4bdd-89d8-a22f2f67490d

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GraphProblems_Interfaces
import Definitions.Def_SparsifyWidthK_Thresholds
import Definitions.Def_GraphProblems_DomTree
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
open GraphProblems GraphProblems.DomTree
open Groundwork Groundwork.Prog Groundwork.Sparsify CountKSat Finset
variable {n : ℕ} {a : Fin n → Bool}
namespace GraphProblems.DomTree
theorem _root_.solution {n s w : ℕ} {x : DNode} {p t : ℕ} (h : Inv n s w x p t) :
    x.1 = (List.replicate n (), s) ∧ x.2.1.length ≤ n ∧ (∀ D ∈ x.2.1, D.length ≤ n ∧ ∀ u ∈ D, u < n) ∧ x.2.2.length ≤ 2 * n ∧
      Shaped w n x.2.2 ∧ x.2.1.length + x.2.2.length ≤ 3 * n := by
  obtain ⟨hx, a, V, h1, h2, h3, h4, h5, h6, h7⟩ := h
  refine ⟨hx, by omega, fun D hD => ⟨?_, fun u hu => h4 u ((h5 D hD).2 u hu)⟩, by omega, h7, by omega⟩
  have hc : #D.toFinset ≤ #V := card_le_card fun u hu => (h5 D hD).2 u (List.mem_toFinset.1 hu)
  rw [List.toFinset_card_of_nodup (h5 D hD).1] at hc
  omega
end GraphProblems.DomTree
