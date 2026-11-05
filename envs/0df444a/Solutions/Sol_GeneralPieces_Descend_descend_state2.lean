-- Prove2me | solution 1 for GeneralPieces.Descend.descend_state2
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:49:21.572089+00:00
-- url     : https://prove2.me/submissions/21df4cf9-555d-4639-aa6d-718d8d680390

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Defs
import Definitions.Def_ClauseBound_Alg_Descend
import Definitions.Def_GeneralPieces_Rec_Descend
import Theorems.Thm_ClauseBound_Alg_Descend_factor_lt
import Theorems.Thm_ClauseBound_Alg_Descend_fitsG_head
import Theorems.Thm_ClauseBound_Alg_Descend_len_state_le
import Theorems.Thm_ClauseBound_Alg_Descend_natAbs_sum_map_le
import Theorems.Thm_ClauseBound_Alg_Descend_pow_le_two_pow_size
import Theorems.Thm_ClauseBound_Alg_Descend_sum_fst_add_sum_snd
import Theorems.Thm_ClauseBound_Alg_Descend_sum_lt
import Theorems.Thm_Groundwork_Host_upd_none
import Theorems.Thm_Groundwork_Host_withIO_none
import Theorems.Thm_Groundwork_Host_withIO_some
import Theorems.Thm_Groundwork_PolyT_flatMap
import Theorems.Thm_Groundwork_PolyT_fst
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_PolyT_map
import Theorems.Thm_Groundwork_PolyT_snd
import Theorems.Thm_Groundwork_PolyT_sum
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
import Theorems.Thm_PaddedDescent_F_Lists_length_flatMap_le
import Theorems.Thm_PaddedDescent_F_cap_eq
import Theorems.Thm_PaddedDescent_F_stBrute
attribute [local fun_prop] Groundwork.PolyT.flatMap
attribute [local fun_prop] Groundwork.PolyT.fst
attribute [local fun_prop] Groundwork.PolyT.length
attribute [local fun_prop] Groundwork.PolyT.map
attribute [local fun_prop] Groundwork.PolyT.snd
attribute [local fun_prop] Groundwork.PolyT.sum
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
open GeneralPieces GeneralPieces.Descend
open Groundwork Groundwork.Prog PaddedDescent.F PaddedDescent.F.Lists ClauseBound.Alg ClauseBound.Alg.Descend
namespace GeneralPieces.Descend
theorem _root_.solution (P : PiecesF) (hX : StExpandG2 P) {pad : U} {K₀ : ℕ} : ∀ (sched : List Step) {Kup lam B cnt z : ℕ} (st fin : DState),
    ChainG2 P K₀ Kup lam sched → FitsG P pad.length Kup lam B cnt z sched → st.2.1.length = lam → st.2.2.length ≤ cnt →
    (∀ I ∈ st.2.2, WFe Kup lam B I) → st.1.1.natAbs < 2 ^ z → st.1.2 < 2 ^ z →
    sched.foldl (fun st s => cap pad ((0, 1), [], []) (stepG P pad st s)) st = fin →
    ∃ c : ℕ, 1 ≤ c ∧ fin.1.2 = c * st.1.2 ∧
      fin.1.1 + (fin.2.2.map (bruteF pad K₀)).sum = c * (st.1.1 + (st.2.2.map (zval Kup)).sum)
  | [], Kup, lam, B, cnt, z, st, fin, hC, hF, hl, _, hw, _, _, hfin => by
    have hK : Kup = K₀ := hC
    subst hK
    rw [List.foldl_nil] at hfin
    subst hfin
    refine ⟨1, le_rfl, (one_mul _).symm, ?_⟩
    rw [Nat.cast_one, one_mul]
    refine congrArg (fun l : List ℤ => st.1.1 + l.sum) (List.map_congr_left fun I hI => stBrute pad Kup I ?_)
    rw [(hw I hI).2]
    exact hF.2
  | s :: r, Kup, lam, B, cnt, z, st, fin, hC, hF, hl, hc, hw, hs, hf, hfin => by
    obtain ⟨hK, hL, hC'⟩ := hC
    obtain ⟨-, hB, hF'⟩ := hF
    subst hK
    subst hl
    have hE := fun I (hI : I ∈ st.2.2) => hX pad s st.2.1.length B I hL (hw I hI) hB
    have hD := pow_le_two_pow_size (P.d s.h st.2.1.length) (nRectG s.p s.d)
    have hn : 1 ≤ nPat P s st.2.1.length := Nat.one_le_pow _ _ hL.spec.cnt_pos
    have h1 : (stepG P pad st s).2.1.length = lamNextG P s st.2.1.length := List.length_replicate
    have h2 : (stepG P pad st s).2.2.length ≤ cnt * nPat P s st.2.1.length := by
      refine le_trans ?_ (Nat.mul_le_mul_right _ hc)
      show ((st.2.2.map (expandG P pad s)).flatMap Prod.snd).length ≤ _
      rw [List.flatMap_map]
      exact length_flatMap_le _ _ _ fun I hI => (hE I hI).2.2.1
    have h3 : ∀ J ∈ (stepG P pad st s).2.2, WFe s.K (lamNextG P s st.2.1.length) (bNextG P s st.2.1.length B) J := by
      intro J hJ
      obtain ⟨x, hx, hJ'⟩ := List.mem_flatMap.1 hJ
      obtain ⟨I, hI, rfl⟩ := List.mem_map.1 hx
      exact (hE I hI).2.1 J hJ'
    have h4 : (stepG P pad st s).1.1.natAbs < 2 ^ (z + nRectG s.p s.d * Nat.size (P.d s.h st.2.1.length) +
        Nat.size (cnt * nPat P s st.2.1.length) + Nof s st.2.1.length +
        s.d ^ 2 * (s.p * B + s.p ^ 2 * P.bits s.h st.2.1.length + 1) + 2) := by
      have hb : ((st.2.2.map (expandG P pad s)).map Prod.fst).sum.natAbs ≤ cnt * 2 ^ (Nat.size (nPat P s st.2.1.length) +
          (Nof s st.2.1.length + s.d ^ 2 * (s.p * B + s.p ^ 2 * P.bits s.h st.2.1.length + 1))) := by
        rw [List.map_map]
        refine (natAbs_sum_map_le _ _ _ fun I hI => ?_).trans (Nat.mul_le_mul_right _ hc)
        rw [← Nat.add_assoc]
        exact (hE I hI).2.2.2
      have := sum_lt hs hD hn hb
      rw [← Nat.add_assoc] at this
      exact this
    have h5 : (stepG P pad st s).1.2 < 2 ^ (z + nRectG s.p s.d * Nat.size (P.d s.h st.2.1.length) +
        Nat.size (cnt * nPat P s st.2.1.length) + Nof s st.2.1.length +
        s.d ^ 2 * (s.p * B + s.p ^ 2 * P.bits s.h st.2.1.length + 1) + 2) := by
      have := factor_lt (x := Nat.size (cnt * nPat P s st.2.1.length) + Nof s st.2.1.length +
        s.d ^ 2 * (s.p * B + s.p ^ 2 * P.bits s.h st.2.1.length + 1) + 2) hf hD
      simp only [← Nat.add_assoc] at this
      exact this
    have hfit : len (stepG P pad st s) ≤ pad.length := (len_state_le _ h1 h2 h3 h4 h5).trans (fitsG_head hF')
    rw [List.foldl_cons, cap_eq hfit] at hfin
    obtain ⟨c, hc1, hc2, hc3⟩ := solution P hX r _ fin hC' hF' h1 h2 h3 h4 h5 hfin
    refine ⟨c * P.d s.h st.2.1.length ^ nRectG s.p s.d, Nat.mul_pos hc1 (Nat.pow_pos hL.spec.d_pos), ?_, ?_⟩
    · rw [hc2]
      show c * (st.1.2 * _) = _
      ring
    · rw [hc3]
      have key := sum_fst_add_sum_snd st.2.2 (expandG P pad s) (zval (s.p * s.d)) (zval s.K)
        ((P.d s.h st.2.1.length : ℤ) ^ nRectG s.p s.d) fun I hI => (hE I hI).1
      show (c : ℤ) * (st.1.1 * ((P.d s.h st.2.1.length ^ nRectG s.p s.d : ℕ) : ℤ) + ((st.2.2.map (expandG P pad s)).map Prod.fst).sum +
        (((st.2.2.map (expandG P pad s)).flatMap Prod.snd).map (zval s.K)).sum) = _
      rw [add_assoc, key]
      push_cast
      ring
end GeneralPieces.Descend
