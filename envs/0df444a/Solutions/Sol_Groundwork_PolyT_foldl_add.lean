-- Prove2me | solution 1 for Groundwork.PolyT.foldl_add
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T17:23:40.492684+00:00
-- url     : https://prove2.me/submissions/1051535f-fb60-48db-b2ae-d0e47931d77e

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ToTuring_Closure_Cases
import Definitions.Def_ToTuring_EncLemmas
import Definitions.Def_ToTuring_Closure_Fold
import Theorems.Thm_Groundwork_PB_add
import Theorems.Thm_Groundwork_PB_mul
import Theorems.Thm_Groundwork_PolyT_elim
import Theorems.Thm_Groundwork_TM_Run_trans
import Theorems.Thm_Groundwork_TM_beq_LR
import Theorems.Thm_Groundwork_TM_beq_RL
import Theorems.Thm_Groundwork_TM_beq_bL
import Theorems.Thm_Groundwork_TM_beq_bR
import Theorems.Thm_Groundwork_TM_length_mirror
import Theorems.Thm_Groundwork_TM_st4_cnt
import Theorems.Thm_Groundwork_TM_st4_src
import Theorems.Thm_Groundwork_TM_st4_t1
import Theorems.Thm_Groundwork_TM_st4_t2
import Theorems.Thm_Groundwork_TM_st_a
import Theorems.Thm_Groundwork_TM_st_b
import Theorems.Thm_Groundwork_TM_st_cnt
import Theorems.Thm_Groundwork_TM_st_main
import Theorems.Thm_Groundwork_TM_upd4_cnt
import Theorems.Thm_Groundwork_TM_upd4_src
import Theorems.Thm_Groundwork_TM_upd4_t1
import Theorems.Thm_Groundwork_TM_upd4_t2
import Theorems.Thm_Groundwork_TM_upd_a
import Theorems.Thm_Groundwork_TM_upd_b
import Theorems.Thm_Groundwork_TM_upd_main
import Theorems.Thm_Groundwork_length_le_len
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
attribute [local simp] Groundwork.TM.beq_LR
attribute [local simp] Groundwork.TM.beq_RL
attribute [local simp] Groundwork.TM.beq_bL
attribute [local simp] Groundwork.TM.beq_bR
attribute [local simp] Groundwork.TM.length_mirror
attribute [local simp] Groundwork.TM.st4_cnt
attribute [local simp] Groundwork.TM.st4_src
attribute [local simp] Groundwork.TM.st4_t1
attribute [local simp] Groundwork.TM.st4_t2
attribute [local simp] Groundwork.TM.st_a
attribute [local simp] Groundwork.TM.st_b
attribute [local simp] Groundwork.TM.st_cnt
attribute [local simp] Groundwork.TM.st_main
attribute [local simp] Groundwork.TM.upd4_cnt
attribute [local simp] Groundwork.TM.upd4_src
attribute [local simp] Groundwork.TM.upd4_t1
attribute [local simp] Groundwork.TM.upd4_t2
attribute [local simp] Groundwork.TM.upd_a
attribute [local simp] Groundwork.TM.upd_b
attribute [local simp] Groundwork.TM.upd_main
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
open Groundwork Groundwork.PolyT
open TM Turing
variable {α β γ δ ε : Type} [Enc α] [Enc β] [Enc γ] [Enc δ] [Enc ε]
namespace Groundwork.PolyT
theorem _root_.solution {l : α → List ε} {a : α → γ} {g : α → γ → ε → γ} (hl : PolyT l) (ha : PolyT a)
    (hg : PolyT fun p : α × γ × ε => g p.1 p.2.1 p.2.2)
    (hB : ∃ b, PB b ∧ ∀ x c, ∀ e ∈ l x, len (g x c e) ≤ len c + b (len x)) :
    PolyT (fun x => (l x).foldl (g x) (a x)) := by
  obtain ⟨b, hb, hB⟩ := hB
  obtain ⟨-, tl, htl, -, -, hll⟩ := hl.elim
  obtain ⟨-, ta, hta, -, -, hla⟩ := ha.elim
  refine foldl hl ha hg ⟨fun n => ta n + tl n * b n, hta.add (htl.mul hb), fun x k => ?_⟩
  have key : ∀ (r : List ε) (c : γ), (∀ e ∈ r, e ∈ l x) → len (r.foldl (g x) c) ≤ len c + r.length * b (len x) := by
    intro r
    induction r with
    | nil => intro c _; simp
    | cons e r ih =>
      intro c hr
      have h1 := ih (g x c e) fun e' he' => hr e' (List.mem_cons_of_mem _ he')
      have h2 := hB x c e (hr e List.mem_cons_self)
      rw [List.foldl_cons, List.length_cons, Nat.succ_mul]
      omega
  have h1 := key ((l x).take k) (a x) fun e he => List.mem_of_mem_take he
  have h2 : ((l x).take k).length * b (len x) ≤ tl (len x) * b (len x) :=
    Nat.mul_le_mul_right _ (((List.length_take_le' _ _).trans (length_le_len _)).trans (hll x))
  have h3 := hla x
  change _ ≤ ta (len x) + tl (len x) * b (len x)
  omega
end Groundwork.PolyT
