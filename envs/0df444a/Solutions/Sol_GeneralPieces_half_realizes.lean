-- Prove2me | solution 1 for GeneralPieces.half_realizes
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T06:58:45.769198+00:00
-- url     : https://prove2.me/submissions/8782c226-f3a1-4f27-b316-579d8126c8f1

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Half_Consts
import Definitions.Def_GeneralPieces_Half_Size
import Definitions.Def_GeneralPieces_Trim_Prog
import Definitions.Def_ClauseBound_Inst_HalfAll
import Definitions.Def_GeneralPieces_Half_Spec
import Theorems.Thm_GeneralPieces_stFact
import Theorems.Thm_ClauseBound_Inst_Half_Par_abs_sOf_le
import Theorems.Thm_ClauseBound_Inst_Half_Spec_abs_sOf_le
import Theorems.Thm_ClauseBound_Inst_Half_Spec_padLen_le
import Theorems.Thm_ClauseBound_Inst_Half_Spec_sum_range_shift
import Theorems.Thm_ClauseBound_Inst_Half_hF_eq
import Theorems.Thm_ClauseBound_Inst_Half_mem_flatten_allTab
import Theorems.Thm_ClauseBound_Inst_Half_stEnc
import Theorems.Thm_ClauseBound_Inst_Half_stLabs
import Theorems.Thm_ClauseBound_Inst_Half_stVal_all
import Theorems.Thm_ClauseBound_Inst_Rec_factN_eq
import Theorems.Thm_ClauseBound_Part_two_le_hOf
import Theorems.Thm_ClauseBound_Part_two_pow_le_p_hOf
import Theorems.Thm_GeneralPieces_Half_abs_ApcL_lt
import Theorems.Thm_GeneralPieces_Half_abs_valK_lt
import Theorems.Thm_GeneralPieces_Trim_length_bitsOf
import Theorems.Thm_GeneralPieces_Trim_length_rep
import Theorems.Thm_GeneralPieces_sum_ApcL
import Theorems.Thm_Groundwork_Host_upd_none
import Theorems.Thm_Groundwork_Host_withIO_none
import Theorems.Thm_Groundwork_Host_withIO_some
import Theorems.Thm_Groundwork_PolyT_length
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
attribute [local fun_prop] Groundwork.PolyT.length
attribute [local fun_prop] Groundwork.PolyT.sum
attribute [local simp] GeneralPieces.Trim.length_bitsOf
attribute [local simp] GeneralPieces.Trim.length_rep
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
open GeneralPieces
open Groundwork Groundwork.Prog PaddedDescent.F ClauseBound.Alg ClauseBound.Inst.Rec ClauseBound.Inst.Half Finset
namespace GeneralPieces
theorem _root_.solution (hPF : AppHalfPieces.PieceFacts) {c₀ c lam : ℕ} (h' : ℕ) (hl : 1 ≤ lam) (hC : Cst c₀ c lam) : Realizes (halfF c₀ c) h' lam (halfA lam) := by
  have hhF : hF c₀ lam = ClauseBound.Part.hOf lam := hF_eq hC.h_le
  have hh2 := ClauseBound.Part.two_le_hOf lam
  have hh1 : 1 ≤ ClauseBound.Part.hOf lam := by omega
  obtain ⟨hℓ, hinj⟩ := stEnc lam (ClauseBound.Part.hOf lam) hh1 (ClauseBound.Part.two_pow_le_p_hOf lam)
  have hℓ' : ∀ x : Pieces.Bits lam, ClauseBound.Boson.Pos (ell (ClauseBound.Part.hOf lam) x) ∧ (ell (ClauseBound.Part.hOf lam) x).sum = ClauseBound.Part.hOf lam :=
    fun x => ⟨(hℓ x).1, (hℓ x).2.1⟩
  have hbig : (2 : ℤ) ^ ClauseBound.Boson.big (ClauseBound.Part.hOf lam) ≤ 2 ^ (2 * lam) ^ c := pow_le_pow_right₀ (by norm_num) hC.bits
  have hcnt : (halfF c₀ c).cnt h' lam = 4 * ClauseBound.Part.hOf lam + 1 := by
    change 4 * hF c₀ lam + 1 = _
    rw [hhF]
  refine ⟨fun x y u v => ?_, fun i hi x y u v => ?_, fun pad hpad i hi => ?_⟩
  · rw [hcnt]
    unfold halfA
    rw [Spec.sum_range_shift (ClauseBound.Part.hOf lam) fun s => ClauseBound.Boson.ApcL (ell (ClauseBound.Part.hOf lam)) (ClauseBound.Part.hOf lam) s x y u v,
      sum_ApcL hPF hℓ' hinj hh1]
    change _ = ((factN (hF c₀ lam) : ℕ) : ℤ) * _
    rw [factN_eq, hhF]
  · rw [hcnt] at hi
    refine (GeneralPieces.Half.abs_ApcL_lt hPF (ClauseBound.Part.two_pow_le_p_hOf lam) hℓ' hh1 ?_ x y u v).le.trans hbig
    rw [abs_le]
    omega
  · rw [hcnt] at hi
    have hpad' : 2 ^ (c * lam) ≤ pad.length := hpad
    refine ⟨fun x y u v => (stFact hPF c₀ c lam pad hl hC hpad' h' i hi x y u v).1,
      fun x y u v => (stFact hPF c₀ c lam pad hl hC hpad' h' i hi x y u v).2, fun tr x y θ => ?_⟩
    have key : ∀ top : Bool, |partH c₀ top ((pad, tr), (h', i), (bitsOf x, bitsOf y, θ))| ≤ 2 ^ (2 * lam) ^ c := by
      intro top
      rw [stVal_all c₀ lam pad hl hC.h_le ((Spec.padLen_le hC).trans hpad') tr top h' i x y θ]
      cases hp : (labs (allTab (4 * ClauseBound.Part.hOf lam)) tr (ClauseBound.Part.hOf lam) (sOf (ClauseBound.Part.hOf lam) i))[ofWord θ]? with
      | none =>
        simp only [Option.elim_none, abs_zero]
        positivity
      | some p =>
        have hmem := (stLabs tr (ClauseBound.Part.hOf lam) (sOf (ClauseBound.Part.hOf lam) i) (Spec.abs_sOf_le _ _)).2.2 p (List.mem_of_getElem? hp)
        simp only [Option.elim_some]
        exact (GeneralPieces.Half.abs_valK_lt hh1 tr top _ (hℓ' x) (hℓ' y) (mem_flatten_allTab.1 hmem.1).2.1 (mem_flatten_allTab.1 hmem.1).1).le.trans hbig
    exact ⟨key true, key false⟩
end GeneralPieces
