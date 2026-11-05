-- Prove2me | solution 1 for Groundwork.PolyT.sumCore
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T17:05:31.285313+00:00
-- url     : https://prove2.me/submissions/fcee0c1c-be9d-4d2c-a16e-74a55e80d4be

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ToTuring_Closure_Basic
import Definitions.Def_ToTuring_Closure_Cases
import Theorems.Thm_Groundwork_PolyT_within_branch
import Theorems.Thm_Groundwork_PolyT_tagHead_eq
import Theorems.Thm_Groundwork_PB_add
import Theorems.Thm_Groundwork_PB_const
import Theorems.Thm_Groundwork_PB_mul
import Theorems.Thm_Groundwork_PolyT_const
import Theorems.Thm_Groundwork_PolyT_elim
import Theorems.Thm_Groundwork_PolyT_of
import Theorems.Thm_Groundwork_Stepped_Reaches_mono
import Theorems.Thm_Groundwork_Stepped_Runs_mono
import Theorems.Thm_Groundwork_TM_Frag_Within_mono
import Theorems.Thm_Groundwork_TM_Frag_Within_seq
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
import Theorems.Thm_Groundwork_TM_unconsF_within
import Theorems.Thm_Groundwork_TM_upd4_cnt
import Theorems.Thm_Groundwork_TM_upd4_src
import Theorems.Thm_Groundwork_TM_upd4_t1
import Theorems.Thm_Groundwork_TM_upd4_t2
import Theorems.Thm_Groundwork_TM_upd_a
import Theorems.Thm_Groundwork_TM_upd_b
import Theorems.Thm_Groundwork_TM_upd_main
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
import Theorems.Thm_P2M_Groundwork_PB_id__8af0b594aff4
import Theorems.Thm_P2M_Groundwork_PolyT_id__1c5d0f44cc8f
attribute [local fun_prop] Groundwork.PolyT.const
attribute [local fun_prop] P2M_Groundwork_PolyT_id__1c5d0f44cc8f
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
theorem _root_.solution {f : β → δ} {g : γ → δ} (hf : PolyT f) (hg : PolyT g) : PolyT (fun s : β ⊕ γ => s.elim f g) := by
  obtain ⟨P, t, htp, htm, hP, hPl⟩ := hf.elim
  obtain ⟨Q, q, hqp, hqm, hQ, hQl⟩ := hg.elim
  -- the tag true stands for inr, so g's fragment Q is the branch of the label true
  refine PolyT.of (unconsF.seq (Frag.branch tagHead Q P)) (t := fun n => (2 * n + 6) + (t n + q n + 1))
    (s := fun n => t n + q n) ?_ (htp.add hqp) (fun x M A B N => ?_) (fun x => ?_)
  · exact (((PB.const 2).mul PB.id').add (PB.const 6)).add ((htp.add hqp).add (PB.const 1))
  · cases x with
    | inl y =>
      have hl : len (Sum.inl y : β ⊕ γ) = len y + 3 := by simp [len, wd, Enc.toV, code]
      have c1 := unconsF_within (.bit false) (Enc.toV y) M A B N
      have c2 := within_branch (P := Q) (Q := P) false (tagHead_eq false (wd y ++ M) A B N) (hP y M A B N)
      refine (c1.seq c2).mono ?_
      have h1 : (code (.bit false)).length = 1 := rfl
      have h2 : (code (Enc.toV y)).length = len y := rfl
      have h3 : t (len y) ≤ t (len y + 3) := htm (by omega)
      simp only [hl, h1, h2]
      omega
    | inr z =>
      have hl : len (Sum.inr z : β ⊕ γ) = len z + 3 := by simp [len, wd, Enc.toV, code]
      have c1 := unconsF_within (.bit true) (Enc.toV z) M A B N
      have c2 := within_branch (P := Q) (Q := P) true (tagHead_eq true (wd z ++ M) A B N) (hQ z M A B N)
      refine (c1.seq c2).mono ?_
      have h1 : (code (.bit true)).length = 1 := rfl
      have h2 : (code (Enc.toV z)).length = len z := rfl
      have h3 : q (len z) ≤ q (len z + 3) := hqm (by omega)
      simp only [hl, h1, h2]
      omega
  · cases x with
    | inl y =>
      have hl : len (Sum.inl y : β ⊕ γ) = len y + 3 := by simp [len, wd, Enc.toV, code]
      have h3 : t (len y) ≤ t (len y + 3) := htm (by omega)
      have h4 := hPl y
      simp only [hl, Sum.elim_inl]
      omega
    | inr z =>
      have hl : len (Sum.inr z : β ⊕ γ) = len z + 3 := by simp [len, wd, Enc.toV, code]
      have h3 : q (len z) ≤ q (len z + 3) := hqm (by omega)
      have h4 := hQl z
      simp only [hl, Sum.elim_inr]
      omega
end Groundwork.PolyT
