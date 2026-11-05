-- Prove2me | solution 1 for Groundwork.Grid.side_core
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T17:20:17.321439+00:00
-- url     : https://prove2.me/submissions/665ba359-1d36-4a4a-b4e1-3a7617284410

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachines_Math_SideNet
import Definitions.Def_StepMachines_Math_SideX
import Theorems.Thm_Groundwork_Grid_block_take
import Theorems.Thm_Groundwork_Grid_sideCl_D
import Theorems.Thm_Groundwork_Grid_sideCl_dec
import Theorems.Thm_Groundwork_Grid_bitsOf_inj
import Theorems.Thm_Groundwork_Grid_cutW_eq
import Theorems.Thm_Groundwork_Grid_length_he
import Theorems.Thm_Groundwork_Grid_node_lt
import Theorems.Thm_Groundwork_Grid_stC_dec
import Theorems.Thm_Groundwork_Grid_tri_bijOn
import Theorems.Thm_Groundwork_Grid_vC_full
import Theorems.Thm_Groundwork_length_block
import Theorems.Thm_Groundwork_length_chunkAt
import Theorems.Thm_Groundwork_length_toWord
import Theorems.Thm_Groundwork_mem_words
import Theorems.Thm_Groundwork_size_bool
import Theorems.Thm_Groundwork_size_inl
import Theorems.Thm_Groundwork_size_inr
import Theorems.Thm_Groundwork_size_int
import Theorems.Thm_Groundwork_size_list
import Theorems.Thm_Groundwork_size_nat
import Theorems.Thm_Groundwork_size_none
import Theorems.Thm_Groundwork_size_prod
import Theorems.Thm_Groundwork_size_some
import Theorems.Thm_Groundwork_size_unit
attribute [local simp] Groundwork.length_toWord
attribute [local simp] Groundwork.mem_words
attribute [local simp] Groundwork.size_bool
attribute [local simp] Groundwork.size_inl
attribute [local simp] Groundwork.size_inr
attribute [local simp] Groundwork.size_int
attribute [local simp] Groundwork.size_list
attribute [local simp] Groundwork.size_nat
attribute [local simp] Groundwork.size_none
attribute [local simp] Groundwork.size_prod
attribute [local simp] Groundwork.size_some
attribute [local simp] Groundwork.size_unit



set_option autoImplicit false
section
section
open Groundwork Groundwork.Grid
open Finset
variable {g n : ℕ}
namespace Groundwork.Grid
theorem _root_.solution (tr top : Bool) (R : Inst (Fin g × Fin g) (Bits n)) (y : ℕ) {a b : Fin g} (hab : a < b) (o : Fin g)
    {z θ : List Bool} (hz : z.length = g ^ 3 * n)
    (hθ : θ.length = g * n + ∑ κ ∈ range (c2 g), rectLen g tr n y (tri a b) κ) :
    (if θ ∈ (sideCl g tr n R y a b).D then
      (∏ i : Fin g, if (stC g tr n).dec z i (o, i) = ((sideCl g tr n R y a b).dec θ).1 i then (1 : ℤ) else 0) *
      ∏ k : Fin g × Fin g with k.1 < k.2,
        if top = true then
          (sideCuts g tr n y ((a, b), k)).top ((stC g tr n).dec z k.1 (o, k.2)) ((stC g tr n).dec z k.2 (o, k.1))
            (((sideCl g tr n R y a b).dec θ).2 k)
        else
          (sideCuts g tr n y ((a, b), k)).bot ((stC g tr n).dec z k.1 (o, k.2)) ((stC g tr n).dec z k.2 (o, k.1))
            (((sideCl g tr n R y a b).dec θ).2 k)
      else 0) =
      (∏ i : Fin g, if he g n z i (node g tr o i) = block n i θ then 1 else 0) *
      ∏ k : Fin g × Fin g with k.1 < k.2,
        cutW tr top (rectDig g tr n y (tri a b) (tri k.1 k.2)) (he g n z k.1 (node g tr o k.2))
          (he g n z k.2 (node g tr o k.1)) (chunkAt (rectLen g tr n y (tri a b)) (tri k.1 k.2) (θ.drop (g * n))) := by
  have hdrop : (θ.drop (g * n)).length = ∑ κ ∈ range (c2 g), rectLen g tr n y (tri a b) κ := by
    rw [List.length_drop, hθ]; omega
  have hhe : ∀ x i : Fin g, (he g n z x (node g tr o i)).length = n := fun x i =>
    length_he hz x.2 (node_lt tr o.2 i.2)
  have hmem : θ ∈ (sideCl g tr n R y a b).D ↔ ∀ k ∈ (univ.filter fun k : Fin g × Fin g => k.1 < k.2),
      chunkAt (rectLen g tr n y (tri a b)) (tri k.1 k.2) (θ.drop (g * n)) ∈
        (rectC g tr n y (tri a b) (tri k.1 k.2)).D := by
    rw [sideCl_D tr R y hab]
    change θ ∈ (words _).filter _ ↔ _
    rw [mem_filter, mem_words, vC_full, mem_words]
    constructor
    · rintro ⟨_, _, h⟩ k hk
      exact (mem_filter.1 h).2 k (mem_filter.1 hk).2
    · intro h
      exact ⟨hθ, by rw [List.length_take, hθ]; omega,
        mem_filter.2 ⟨mem_words.2 hdrop, fun k hk => h k (mem_filter.2 ⟨mem_univ _, hk⟩)⟩⟩
  have h1 : ∀ i : Fin g, (if (stC g tr n).dec z i (o, i) = ((sideCl g tr n R y a b).dec θ).1 i then (1 : ℤ) else 0) =
      if he g n z i (node g tr o i) = block n i θ then 1 else 0 := fun i => by
    rw [sideCl_dec tr R y hab, stC_dec]
    change (if bitsOf n (he g n z i (node g tr o i)) = bitsOf n (block n i (θ.take (g * n))) then (1 : ℤ) else 0) = _
    rw [block_take _ i.2]
    exact if_congr (bitsOf_inj (hhe i i)
      (length_block (by rw [hθ]; exact (Nat.mul_le_mul_right _ i.2).trans (Nat.le_add_right _ _)))) rfl rfl
  have h2 : ∀ k ∈ (univ.filter fun k : Fin g × Fin g => k.1 < k.2),
      cutW tr top (rectDig g tr n y (tri a b) (tri k.1 k.2)) (he g n z k.1 (node g tr o k.2))
          (he g n z k.2 (node g tr o k.1)) (chunkAt (rectLen g tr n y (tri a b)) (tri k.1 k.2) (θ.drop (g * n))) =
        if chunkAt (rectLen g tr n y (tri a b)) (tri k.1 k.2) (θ.drop (g * n)) ∈
            (rectC g tr n y (tri a b) (tri k.1 k.2)).D then
          if top = true then
            (sideCuts g tr n y ((a, b), k)).top ((stC g tr n).dec z k.1 (o, k.2)) ((stC g tr n).dec z k.2 (o, k.1))
              (((sideCl g tr n R y a b).dec θ).2 k)
          else
            (sideCuts g tr n y ((a, b), k)).bot ((stC g tr n).dec z k.1 (o, k.2)) ((stC g tr n).dec z k.2 (o, k.1))
              (((sideCl g tr n R y a b).dec θ).2 k)
        else 0 := fun k hk => by
    have hk' := (mem_filter.1 hk).2
    have hd : ((sideCl g tr n R y a b).dec θ).2 k =
        (rectC g tr n y (tri a b) (tri k.1 k.2)).dec
          (chunkAt (rectLen g tr n y (tri a b)) (tri k.1 k.2) (θ.drop (g * n))) := by
      rw [sideCl_dec tr R y hab]
      change (if k.1 < k.2 then _ else _) = _
      rw [if_pos hk']
    rw [cutW_eq tr top (n := n) (i := rectDig g tr n y (tri a b) (tri k.1 k.2)) (hhe k.1 k.2)
      (length_chunkAt _ (mem_range.1 ((tri_bijOn g).mapsTo hk')) hdrop), hd, stC_dec, stC_dec]
    rfl
  simp only [h1]
  by_cases h : θ ∈ (sideCl g tr n R y a b).D
  · rw [if_pos h]
    congr 1
    exact prod_congr rfl fun k hk => by rw [h2 k hk, if_pos (hmem.1 h k hk)]
  · rw [if_neg h]
    obtain ⟨k, hk, hnk⟩ : ∃ k ∈ (univ.filter fun k : Fin g × Fin g => k.1 < k.2),
        chunkAt (rectLen g tr n y (tri a b)) (tri k.1 k.2) (θ.drop (g * n)) ∉
          (rectC g tr n y (tri a b) (tri k.1 k.2)).D := by
      by_contra hh
      push Not at hh
      exact h (hmem.2 hh)
    rw [prod_eq_zero hk (by rw [h2 k hk, if_neg hnk]), mul_zero]
end Groundwork.Grid
