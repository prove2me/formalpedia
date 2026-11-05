-- Prove2me | solution 1 for GeneralPieces.Top.val_caseI
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:30:22.012738+00:00
-- url     : https://prove2.me/submissions/e791188d-754f-4b59-99b2-eef363224762

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Group_Lemma
import Definitions.Def_ClauseBound_Alg_Top
import Definitions.Def_ClauseBound_Alg_TopNet
import Definitions.Def_CountKSat_Value
import Definitions.Def_CountKSat_InOut
import Definitions.Def_StepMachines_Prog_NetVal
import Definitions.Def_StepMachines_Prog_Count
import Definitions.Def_StepMachines_Math_SatNet
import Definitions.Def_GeneralPieces_Top_CaseI
import Theorems.Thm_GeneralPieces_grouping_general
import Theorems.Thm_GeneralPieces_wfe_mono
import Theorems.Thm_Groundwork_Host_upd_none
import Theorems.Thm_Groundwork_Host_withIO_none
import Theorems.Thm_Groundwork_Host_withIO_some
import Theorems.Thm_Groundwork_PolyT_elim
import Theorems.Thm_Groundwork_PolyT_length
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
open GeneralPieces GeneralPieces.Top
open Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Prog.Count PaddedDescent PaddedDescent.F ClauseBound.Alg CountKSat
namespace GeneralPieces.Top
theorem _root_.solution {Idx : Type} [Enc Idx] (S : Solver Idx) (ok : Idx → Prop) (hS : S.Correct ok) {C : Type} (F : FNet C) (c : C) (pad : U) (i : Idx)
    (N : Network (Fin (3 * S.K i ^ 8)) (List Bool) (List Bool)) (P B β : ℕ) (hi : ok i) (hK : 2 ≤ S.K i)
    (hN : F.toP.Presents c N 0 0) (hSz : N.Sized P B) (hβ : AppRunningTime.Lof (S.K i) (3 * S.K i ^ 8) (1 / (2 * (S.K i : ℝ))) P N.U ≤ β) (hβ1 : 1 ≤ β)
    (f1 : S.K i ^ (3 * S.K i ^ 8) ≤ pad.length) (f2 : 2 ^ (P * (2 * (3 * S.K i ^ 8) / S.K i)) ≤ pad.length) (f3 : 2 ^ P ≤ pad.length)
    (f4 : 2 ^ ((S.K i - 1) * β) ≤ pad.length)
    (f5 : 2 ^ S.need (i, List.replicate β (), List.replicate (bitsS (S.K i) (3 * S.K i ^ 8) P B) ()) ≤ pad.length) :
    ((rebalG pad (S.K i) (3 * S.K i ^ 8) β F c).elim 0 fun I => S.run (pad, i, I)) = N.value := by
  have hKr : (2 : ℝ) ≤ S.K i := by exact_mod_cast hK
  have hg : 2 ≤ 3 * S.K i ^ 8 := by
    have : 0 < S.K i ^ 8 := Nat.pow_pos (by omega)
    omega
  obtain ⟨J, hJ, hz, hWF⟩ := grouping_general C F c (S.K i) (3 * S.K i ^ 8) (1 / (2 * (S.K i : ℝ))) N P B β pad hK hg (by positivity)
    (by rw [div_le_one (by positivity)]; linarith) hN hSz (Or.inl ⟨rfl, rfl⟩) hβ hβ1 f1 f2 f3 f4
  rw [hJ]
  simp only [Option.elim]
  rw [hS pad i _ _ J hi hβ1 (wfe_mono hWF (min_le_right _ _)) f5, hz]
end GeneralPieces.Top
