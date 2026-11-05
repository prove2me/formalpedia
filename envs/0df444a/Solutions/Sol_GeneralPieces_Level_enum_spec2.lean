-- Prove2me | solution 1 for GeneralPieces.Level.enum_spec2
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:47:39.399139+00:00
-- url     : https://prove2.me/submissions/8b07489c-552c-4dcd-820b-079b64bfec27

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Group_Lemma
import Definitions.Def_ClauseBound_Alg_Level
import Definitions.Def_GeneralPieces_Rec_Level
import Theorems.Thm_ClauseBound_Alg_Level_abs_value_le
import Theorems.Thm_Groundwork_Host_upd_none
import Theorems.Thm_Groundwork_Host_withIO_none
import Theorems.Thm_Groundwork_Host_withIO_some
import Theorems.Thm_Groundwork_PolyT_congr
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_Prog_abs_value_le
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
import Theorems.Thm_Groundwork_TM_update_withIO
import Theorems.Thm_Groundwork_card_words
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
attribute [local fun_prop] Groundwork.PolyT.length
attribute [local simp] Groundwork.Host.upd_none
attribute [local simp] Groundwork.Host.withIO_none
attribute [local simp] Groundwork.Host.withIO_some
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
attribute [local simp] Groundwork.TM.update_withIO
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
open GeneralPieces GeneralPieces.Level
open Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.Level Finset
namespace GeneralPieces.Level
theorem _root_.solution (hE : StEnum) (P : PiecesF) (pad : U) (s : Step) (lam B : ℕ) (I : PInst) (y : ℕ) (hL : LevelOK2 P s lam) (hlam : I.1.length = lam)
    (hb : BudG P pad.length s lam) (hy : y < nPat P s lam) (hc : (s.thin && colSide P s lam y) = true)
    (N : Network (Fin s.d) (List Bool) (List Bool)) (hN : (gridF P).toP.Presents (gctx pad s true I y) N 0 0)
    (hS : N.Sized (P.m * (s.d * s.p ^ 2 * lam)) (s.p * B + s.p ^ 2 * P.bits s.h lam))
    (hU : N.U = totalG P s.p s.d true s.h lam y) :
    enumF pad s.d (gridF P) (gctx pad s true I y) = N.value ∧ |N.value| ≤ 2 ^ (Nof s lam + s.d ^ 2 * (s.p * B + s.p ^ 2 * P.bits s.h lam)) := by
  have ht : s.thin = true := by
    cases h : s.thin with
    | false => rw [h] at hc; simp at hc
    | true => rfl
  have hn : ∀ a, (gridF P).n (gctx pad s true I y) a = s.p ^ 2 * s.d * lam := by
    intro a
    change nMemb s.p s.d true * (s.p * s.d) * I.1.length = _
    rw [hlam, nMemb, if_pos rfl]
    ring
  have hst : ∀ a < s.d, 2 ^ (gridF P).n (gctx pad s true I y) a ≤ pad.length := fun a _ => by rw [hn]; exact hb.enumSt ht
  -- the number of label bits, read off with a pad that is long enough for everything
  have hbits : 2 * enumBits s.d (gridF P) (gctx pad s true I y) = N.U :=
    (hE _ (List.replicate (2 ^ enumBits s.d (gridF P) (gctx pad s true I y) + 2 ^ (s.p ^ 2 * s.d * lam)) ()) s.d (gridF P) _ N hN
      (by rw [List.length_replicate]; exact Nat.le_add_right _ _) (fun a _ => by rw [hn, List.length_replicate]; exact Nat.le_add_left _ _)).2
  have hle : enumBits s.d (gridF P) (gctx pad s true I y) ≤ ebarG s lam := by
    have := hL.ebar y hy hc
    omega
  refine ⟨(hE _ pad s.d (gridF P) _ N hN ((Nat.pow_le_pow_right (by norm_num) hle).trans (hb.enumLab ht)) hst).1, ?_⟩
  have h1 := abs_value_le N (n := s.p ^ 2 * s.d * lam) hS fun a => by
    rw [hN.S_eq a, card_words]
    exact (Nat.pow_le_pow_right (by norm_num) (hn a).le)
  rw [Fintype.card_fin] at h1
  refine h1.trans (le_of_eq ?_)
  congr 1
  unfold Nof
  ring
end GeneralPieces.Level
