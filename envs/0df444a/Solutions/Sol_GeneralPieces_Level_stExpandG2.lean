-- Prove2me | solution 1 for GeneralPieces.Level.stExpandG2
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:42:02.271842+00:00
-- url     : https://prove2.me/submissions/ae50031f-6d8e-4fef-b596-dfff4087cc5d

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Group_Lemma
import Definitions.Def_ClauseBound_Alg_Level
import Definitions.Def_GeneralPieces_Rec_Level
import Theorems.Thm_GeneralPieces_Level_child_spec2
import Theorems.Thm_GeneralPieces_Level_enum_spec2
import Theorems.Thm_ClauseBound_Alg_Level_filterMap_spec
import Theorems.Thm_ClauseBound_Alg_Level_parts_eq
import Theorems.Thm_ClauseBound_Alg_Level_sum_map_range
import Theorems.Thm_Groundwork_Host_upd_none
import Theorems.Thm_Groundwork_Host_withIO_none
import Theorems.Thm_Groundwork_Host_withIO_some
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_Stepped_sum_map_range
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
import Theorems.Thm_PaddedDescent_F_Table_stT3c
import Theorems.Thm_PaddedDescent_F_rng_eq
import Theorems.Thm_PaddedDescent_F_sumF_eq
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
theorem _root_.solution (P : PiecesF) (hG : StGrid P) (hE : StEnum) : StExpandG2 P := by
  intro pad s lam B I hL hI hb
  obtain ⟨hW, hlam⟩ := hI
  subst hlam
  obtain ⟨Zt, hZ, hT⟩ := hG pad s.1.2.1 s.1.2.2 s.2.1.2 I.1 I.2 B hW.lam_pos hL.spec hb.pieces (Table.stT3c _ _ _ _ hW)
  change (P.d s.h I.1.length : ℤ) ^ nRectG s.p s.d * zval (s.p * s.d) I = ∑ y ∈ range (nPat P s I.1.length), Zt y at hZ
  change ∀ y < nPat P s I.1.length, ∀ tr : Bool, ∃ N : Network (Fin (nParts s.p s.d tr)) (List Bool) (List Bool),
    (gridF P).toP.Presents (gctx pad s tr I y) N 0 0 ∧ N.value = Zt y ∧
    N.Sized (P.m * (nParts s.p s.d tr * nMemb s.p s.d tr ^ 2 * I.1.length)) (nMemb s.p s.d tr * B + nMemb s.p s.d tr ^ 2 * P.bits s.h I.1.length) ∧
    N.U = totalG P s.p s.d tr s.h I.1.length y ∧ ∀ a b, a ≠ b → N.c a b ≤ nMemb s.p s.d tr ^ 2 * (P.m * I.1.length) at hT
  have hen : ∀ y < nPat P s I.1.length, (s.thin && colSide P s I.1.length y) = true →
      enumF pad s.d (gridF P) (gctx pad s true I y) = Zt y ∧
        |Zt y| ≤ 2 ^ (Nof s I.1.length + s.d ^ 2 * (s.p * B + s.p ^ 2 * P.bits s.h I.1.length)) := by
    intro y hy hc
    obtain ⟨N, h1, h2, h3, h4, _⟩ := hT y hy true
    rw [← h2]
    exact enum_spec2 hE P pad s I.1.length B I y hL rfl hb hy hc N h1 h3 h4
  have hch : ∀ y < nPat P s I.1.length, (s.thin && colSide P s I.1.length y) = false →
      ∃ J, childG P pad s I y = some J ∧ zval s.K J = Zt y ∧ WFe s.K (lamNextG P s I.1.length) (bNextG P s I.1.length B) J := by
    intro y hy hc
    obtain ⟨N, h1, h2, h3, h4, h5⟩ := hT y hy (!s.thin && colSide P s I.1.length y)
    rw [← h2]
    obtain ⟨e1, e2⟩ := parts_eq s hL.square (colSide P s I.1.length y)
    exact child_spec2 P pad s I.1.length B I y hL rfl hb hy hc _ _ e1 e2 N h1 h3 h4 h5
  obtain ⟨f1, f2, f3⟩ := filterMap_spec
    (f := fun y => if (s.thin && colSide P s I.1.length y) = true then none else childG P pad s I y) (z := zval s.K)
    (v := fun y => if (s.thin && colSide P s I.1.length y) = true then 0 else Zt y)
    (Q := WFe s.K (lamNextG P s I.1.length) (bNextG P s I.1.length B)) (List.range (nPat P s I.1.length)) fun y hy => by
      cases hc : (s.thin && colSide P s I.1.length y) with
      | true => exact Or.inl ⟨by simp, by simp⟩
      | false => exact Or.inr (by simpa using hch y (List.mem_range.1 hy) hc)
  unfold expandG
  simp only
  rw [rng_eq hb.pat, sumF_eq hb.pat]
  refine ⟨?_, f2, by rwa [List.length_range] at f3, ?_⟩
  · rw [f1, sum_map_range, hZ, ← sum_add_distrib]
    refine sum_congr rfl fun y hy => ?_
    split_ifs with hc
    · rw [(hen y (mem_range.1 hy) hc).1, add_zero]
    · rw [zero_add]
  · have key : |∑ y ∈ range (nPat P s I.1.length),
        if (s.thin && colSide P s I.1.length y) = true then enumF pad s.d (gridF P) (gctx pad s true I y) else 0| ≤
        (2 : ℤ) ^ (Nat.size (nPat P s I.1.length) + Nof s I.1.length + s.d ^ 2 * (s.p * B + s.p ^ 2 * P.bits s.h I.1.length + 1)) := by
      calc _ ≤ ∑ y ∈ range (nPat P s I.1.length),
            |if (s.thin && colSide P s I.1.length y) = true then enumF pad s.d (gridF P) (gctx pad s true I y) else 0| :=
            abs_sum_le_sum_abs _ _
        _ ≤ ∑ _y ∈ range (nPat P s I.1.length), (2 : ℤ) ^ (Nof s I.1.length + s.d ^ 2 * (s.p * B + s.p ^ 2 * P.bits s.h I.1.length)) := by
            refine sum_le_sum fun y hy => ?_
            split_ifs with hc
            · rw [(hen y (mem_range.1 hy) hc).1]; exact (hen y (mem_range.1 hy) hc).2
            · rw [abs_zero]; positivity
        _ = (nPat P s I.1.length : ℤ) * 2 ^ (Nof s I.1.length + s.d ^ 2 * (s.p * B + s.p ^ 2 * P.bits s.h I.1.length)) := by
            rw [sum_const, card_range, nsmul_eq_mul]
        _ ≤ 2 ^ Nat.size (nPat P s I.1.length) * 2 ^ (Nof s I.1.length + s.d ^ 2 * (s.p * B + s.p ^ 2 * P.bits s.h I.1.length)) :=
            mul_le_mul_of_nonneg_right (by exact_mod_cast (Nat.lt_size_self _).le) (by positivity)
        _ = 2 ^ (Nat.size (nPat P s I.1.length) + (Nof s I.1.length + s.d ^ 2 * (s.p * B + s.p ^ 2 * P.bits s.h I.1.length))) := (pow_add _ _ _).symm
        _ ≤ _ := pow_le_pow_right₀ (by norm_num) (by
            have := Nat.mul_le_mul_left (s.d ^ 2) (Nat.le_add_right (s.p * B + s.p ^ 2 * P.bits s.h I.1.length) 1)
            omega)
    rw [Int.abs_eq_natAbs] at key
    exact_mod_cast key
end GeneralPieces.Level
