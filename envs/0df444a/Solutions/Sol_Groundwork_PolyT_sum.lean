-- Prove2me | solution 1 for Groundwork.PolyT.sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T19:13:16.37721+00:00
-- url     : https://prove2.me/submissions/cd4d8170-3f23-4307-8b18-1742330fcbd1

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ToTuring_Lib_Nat1
import Definitions.Def_ToTuring_Lib_Nat1b
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_P2M_Groundwork_PolyT_size__c8c8eb1b342f
import Theorems.Thm_P2M_Groundwork_PolyT_log2__935ea318e2e8
import Theorems.Thm_Groundwork_PolyT_testBit
import Theorems.Thm_Groundwork_PB_add
import Theorems.Thm_Groundwork_PB_const
import Theorems.Thm_Groundwork_PolyT_all
import Theorems.Thm_Groundwork_PolyT_any
import Theorems.Thm_Groundwork_PolyT_comp
import Theorems.Thm_Groundwork_PolyT_congr
import Theorems.Thm_Groundwork_PolyT_const
import Theorems.Thm_Groundwork_PolyT_elim
import Theorems.Thm_Groundwork_PolyT_filter
import Theorems.Thm_Groundwork_PolyT_filterMap
import Theorems.Thm_Groundwork_PolyT_flatMap
import Theorems.Thm_Groundwork_PolyT_foldl_add
import Theorems.Thm_Groundwork_PolyT_fst
import Theorems.Thm_Groundwork_PolyT_map
import Theorems.Thm_Groundwork_PolyT_optionElim
import Theorems.Thm_Groundwork_PolyT_prodMk
import Theorems.Thm_Groundwork_PolyT_snd
import Theorems.Thm_Groundwork_PolyT_sumElim
import Theorems.Thm_Groundwork_len_le_of_mem
import Theorems.Thm_P2M_Groundwork_PolyT_cond__4c673073da15
import Theorems.Thm_P2M_Groundwork_PolyT_cons__3a60f43a3b86
import Theorems.Thm_P2M_Groundwork_PolyT_find__e812ffd764ea
import Theorems.Thm_P2M_Groundwork_PolyT_id__1c5d0f44cc8f
import Theorems.Thm_P2M_Groundwork_PolyT_inl__78f4b62d65a1
import Theorems.Thm_P2M_Groundwork_PolyT_inr__53ca1f30b2d3
import Theorems.Thm_P2M_Groundwork_PolyT_ite__226169acf219
import Theorems.Thm_P2M_Groundwork_PolyT_some__e6a32bd6af45
attribute [local fun_prop] Groundwork.PolyT.all
attribute [local fun_prop] Groundwork.PolyT.any
attribute [local fun_prop] Groundwork.PolyT.comp
attribute [local fun_prop] Groundwork.PolyT.const
attribute [local fun_prop] Groundwork.PolyT.filter
attribute [local fun_prop] Groundwork.PolyT.filterMap
attribute [local fun_prop] Groundwork.PolyT.flatMap
attribute [local fun_prop] Groundwork.PolyT.fst
attribute [local fun_prop] Groundwork.PolyT.map
attribute [local fun_prop] Groundwork.PolyT.optionElim
attribute [local fun_prop] Groundwork.PolyT.prodMk
attribute [local fun_prop] Groundwork.PolyT.snd
attribute [local fun_prop] Groundwork.PolyT.sumElim
attribute [local fun_prop] P2M_Groundwork_PolyT_cond__4c673073da15
attribute [local fun_prop] P2M_Groundwork_PolyT_cons__3a60f43a3b86
attribute [local fun_prop] P2M_Groundwork_PolyT_find__e812ffd764ea
attribute [local fun_prop] P2M_Groundwork_PolyT_id__1c5d0f44cc8f
attribute [local fun_prop] P2M_Groundwork_PolyT_inl__78f4b62d65a1
attribute [local fun_prop] P2M_Groundwork_PolyT_inr__53ca1f30b2d3
attribute [local fun_prop] P2M_Groundwork_PolyT_ite__226169acf219
attribute [local fun_prop] P2M_Groundwork_PolyT_some__e6a32bd6af45


attribute [local fun_prop] Groundwork.PolyT.length
attribute [local fun_prop] Groundwork.PolyT.size'
attribute [local fun_prop] Groundwork.PolyT.log2'
attribute [local fun_prop] Groundwork.PolyT.testBit
section
namespace Groundwork.PolyT
variable {α β γ δ ε : Type} [Enc α] [Enc β] [Enc γ] [Enc δ] [Enc ε]
private theorem size_add_le (c e : ℕ) : Nat.size (c + e) ≤ Nat.size c + Nat.size e + 1 := by
  rw [Nat.size_le]
  have h1 := Nat.lt_size_self c
  have h2 := Nat.lt_size_self e
  have h3 : 2 ^ Nat.size c ≤ 2 ^ (Nat.size c + Nat.size e) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h4 : 2 ^ Nat.size e ≤ 2 ^ (Nat.size c + Nat.size e) := Nat.pow_le_pow_right (by norm_num) (by omega)
  rw [pow_succ]
  omega
private theorem foldl_add_eq (l : List ℕ) (n : ℕ) : l.foldl (fun c e => c + e) n = n + l.sum := by
  induction l generalizing n with
  | nil => rfl
  | cons e r ih => rw [List.foldl_cons, ih, List.sum_cons]; omega
end Groundwork.PolyT
set_option autoImplicit false
section
section
open Groundwork Groundwork.PolyT
variable {α β γ δ ε : Type} [Enc α] [Enc β] [Enc γ] [Enc δ] [Enc ε]
namespace Groundwork.PolyT
theorem _root_.solution {l : α → List ℕ} (hl : PolyT l) :
    PolyT (fun x => (l x).sum) := by
  obtain ⟨_, t, ht, -, -, hlen⟩ := hl.elim
  have h : PolyT (fun x => (l x).foldl (fun c e => c + e) 0) := by
    refine foldl_add (g := fun _ c e => c + e) hl (by fun_prop) (by fun_prop)
      ⟨fun n => t n + 1, ht.add (PB.const 1), ?_⟩
    intro x c e he
    show len (c + e) ≤ len c + (t (len x) + 1)
    have h1 := len_le_of_mem he
    have h2 := hlen x
    have h3 := size_add_le c e
    rw [len_nat] at h1
    rw [len_nat, len_nat]
    omega
  exact h.congr fun x => by rw [foldl_add_eq, Nat.zero_add]
end Groundwork.PolyT
