-- Prove2me | solution 1 for GraphProblems.Color.sat_colorF
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T08:08:58.474695+00:00
-- url     : https://prove2.me/submissions/653f602a-fcab-42bd-a601-fe7ab49d053a

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GraphProblems_Blocks
import Definitions.Def_GraphProblems_Color
import Theorems.Thm_GraphProblems_Color_mem_pairs
import Theorems.Thm_GraphProblems_Color_exists_mem_pair
import Theorems.Thm_GraphProblems_Blocks_sat_append


set_option autoImplicit false
section
section
open GraphProblems
open Groundwork Groundwork.Prog CountKSat Finset
open GraphProblems.Color
open Blocks
namespace GraphProblems.Color
theorem _root_.solution (k n : ℕ) (m : List Bool) (f : ℕ → Bool) : Sat f (colorF k n m) ↔
    (∀ v < n, ∃ c < k, f (v * k + c) = true) ∧
    (∀ v < n, ∀ c₁ < k, ∀ c₂ < k, c₁ < c₂ → f (v * k + c₁) = false ∨ f (v * k + c₂) = false) ∧
    ∀ u < n, ∀ v < n, adjB n m u v = true → ∀ c < k, f (u * k + c) = false ∨ f (v * k + c) = false := by
  rw [colorF, sat_append, sat_append, and_assoc]
  refine and_congr ?_ (and_congr ?_ ?_)
  · constructor
    · intro h v hv
      obtain ⟨l, hl, hfl⟩ := h _ (List.mem_map.2 ⟨v, List.mem_range.2 hv, rfl⟩)
      obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hl
      exact ⟨c, List.mem_range.1 hc, hfl⟩
    · intro h C hC
      obtain ⟨v, hv, rfl⟩ := List.mem_map.1 hC
      obtain ⟨c, hc, hf⟩ := h v (List.mem_range.1 hv)
      exact ⟨_, List.mem_map.2 ⟨c, List.mem_range.2 hc, rfl⟩, hf⟩
  · constructor
    · intro h v hv c₁ h1 c₂ h2 h12
      exact (exists_mem_pair f _ _).1 (h _ (List.mem_flatMap.2 ⟨v, List.mem_range.2 hv,
        List.mem_map.2 ⟨(c₁, c₂), List.mem_filter.2 ⟨mem_pairs.2 ⟨h1, h2⟩, decide_eq_true h12⟩, rfl⟩⟩))
    · intro h C hC
      obtain ⟨v, hv, hC⟩ := List.mem_flatMap.1 hC
      obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hC
      obtain ⟨hq1, hq2⟩ := List.mem_filter.1 hq
      exact (exists_mem_pair f _ _).2 (h v (List.mem_range.1 hv) q.1 (mem_pairs.1 hq1).1 q.2 (mem_pairs.1 hq1).2 (of_decide_eq_true hq2))
  · constructor
    · intro h u hu v hv huv c hc
      exact (exists_mem_pair f _ _).1 (h _ (List.mem_flatMap.2 ⟨(u, v), List.mem_filter.2 ⟨mem_pairs.2 ⟨hu, hv⟩, huv⟩,
        List.mem_map.2 ⟨c, List.mem_range.2 hc, rfl⟩⟩))
    · intro h C hC
      obtain ⟨p, hp, hC⟩ := List.mem_flatMap.1 hC
      obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hC
      obtain ⟨hp1, hp2⟩ := List.mem_filter.1 hp
      exact (exists_mem_pair f _ _).2 (h p.1 (mem_pairs.1 hp1).1 p.2 (mem_pairs.1 hp1).2 hp2 c (List.mem_range.1 hc))
end GraphProblems.Color
