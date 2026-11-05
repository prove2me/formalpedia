-- Prove2me | solution 1 for Groundwork.Grid.sideN_f
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T17:22:01.989142+00:00
-- url     : https://prove2.me/submissions/c56d3bc2-7ca4-4d66-a91c-5a9421939185

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachines_Math_SideNet
import Definitions.Def_StepMachines_Math_SideX
import Theorems.Thm_Groundwork_Grid_side_core
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
namespace Groundwork.Grid
theorem _root_.solution (g : ℕ) (tr : Bool) (n : ℕ) (Rm : Inst (Fin (g * g)) (List Bool)) (y : ℕ) {a b : Fin g} (hab : a ≠ b)
    {z θ : List Bool} (hz : z.length = g ^ 3 * n) (hθ : θ.length = sideCap g tr n y a b) :
    (sideN g tr n Rm y).f a b z θ =
      (∏ i : Fin g, if he g n z i (node g tr b i) = block n i θ then 1 else 0) *
      ∏ k : Fin g × Fin g with k.1 < k.2, sideItem g tr n y a b z θ k.1 k.2 := by
  have e : (sideN g tr n Rm y).f a b z θ =
      if θ ∈ (sideCl g tr n (sideR g tr n Rm) y (min a b) (max a b)).D then
        (sideNet g tr n (sideR g tr n Rm) y).f a b ((stC g tr n).dec z)
          ((sideCl g tr n (sideR g tr n Rm) y (min a b) (max a b)).dec θ) else 0 := rfl
  unfold sideCap at hθ
  simp only [sideItem, sideChunk]
  rcases lt_or_gt_of_ne hab with h | h
  · have h' : (a : ℕ) < b := h
    rw [min_eq_left h'.le, max_eq_right h'.le] at hθ
    simp only [min_eq_left h'.le, max_eq_right h'.le, decide_eq_true h']
    rw [← side_core tr true (sideR g tr n Rm) y h b hz hθ, e, min_eq_left h.le, max_eq_right h.le]
    have e' : ∀ θ', (sideNet g tr n (sideR g tr n Rm) y).f a b ((stC g tr n).dec z) θ' =
        rowTop (sideCuts g tr n y) a b ((stC g tr n).dec z) θ' := fun θ' => if_pos h
    rw [e']
    rfl
  · have h' : (b : ℕ) < a := h
    rw [min_eq_right h'.le, max_eq_left h'.le] at hθ
    simp only [min_eq_right h'.le, max_eq_left h'.le, decide_eq_false (not_lt.2 h'.le)]
    rw [← side_core tr false (sideR g tr n Rm) y h b hz hθ, e, min_eq_right h.le, max_eq_left h.le]
    have e' : ∀ θ', (sideNet g tr n (sideR g tr n Rm) y).f a b ((stC g tr n).dec z) θ' =
        rowBot (sideCuts g tr n y) b a ((stC g tr n).dec z) θ' := fun θ' => if_neg (not_lt.2 h.le)
    rw [e']
    rfl
end Groundwork.Grid
