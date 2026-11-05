-- Prove2me | solution 1 for Groundwork.exists_tm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T17:04:59.075518+00:00
-- url     : https://prove2.me/submissions/7a8fa6b6-13c7-4287-8b46-464ef275e249

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ToTuring_Machine_Lift
import Definitions.Def_ToTuring_PolyT
import Definitions.Def_ToTuring_EncLemmas
import Definitions.Def_ToTuring_Machine_Host
import Theorems.Thm_Groundwork_Host_within_io
import Theorems.Thm_Groundwork_Host_withIO_none
import Theorems.Thm_Groundwork_Host_withIO_some
import Theorems.Thm_Groundwork_Host_upd_none
import Theorems.Thm_Groundwork_Host_prologue_within
import Theorems.Thm_Groundwork_Host_size_le_of_reaches
import Theorems.Thm_Groundwork_Host_look_within
import Theorems.Thm_Groundwork_Host_mainLoop_within
import Theorems.Thm_Groundwork_Host_outputs_of_within
import Theorems.Thm_Groundwork_PB_add
import Theorems.Thm_Groundwork_PB_comp
import Theorems.Thm_Groundwork_PB_const
import Theorems.Thm_Groundwork_PB_mul
import Theorems.Thm_Groundwork_PB_pow
import Theorems.Thm_Groundwork_PolyT_elim
import Theorems.Thm_Groundwork_Stepped_Reaches_mono
import Theorems.Thm_Groundwork_Stepped_Runs_mono
import Theorems.Thm_Groundwork_TM_Frag_Within_mono
import Theorems.Thm_Groundwork_TM_Frag_Within_seq
import Theorems.Thm_Groundwork_TM_Run_trans
import Theorems.Thm_Groundwork_TM_beq_LR
import Theorems.Thm_Groundwork_TM_beq_RL
import Theorems.Thm_Groundwork_TM_beq_bL
import Theorems.Thm_Groundwork_TM_beq_bR
import Theorems.Thm_Groundwork_TM_dropF_within
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


attribute [local simp] Groundwork.Host.withIO_none
attribute [local simp] Groundwork.Host.withIO_some
attribute [local simp] Groundwork.Host.upd_none

set_option autoImplicit false
section
section
open Groundwork
open TM Turing
open Host
namespace Groundwork
theorem _root_.solution (M : Stepped (List Bool) Bool) [IsPolyT M] (d : ℕ) :
    ∃ (N : TM2ComputableAux Bool Bool) (c : ℕ), (∀ k, Finite (N.tm.Γ k)) ∧
      ∀ (x : List Bool) (T S : ℕ) (b : Bool), M.Runs x T S b → S ≤ (x.length + 2) ^ d →
        Nonempty (TM2OutputsInTime N.tm (x.map N.inputAlphabet.invFun) (some ([b].map N.outputAlphabet.invFun))
          (c * (T + 1) * (x.length + 1) ^ c)) := by
  obtain ⟨Pi, tI, pI, -, hI, -⟩ := (IsPolyT.init (M := M)).elim
  obtain ⟨Ps, tS, pS, mS, hS, -⟩ := (IsPolyT.step (M := M)).elim
  obtain ⟨Po, tO, pO, mO, hO, -⟩ := (IsPolyT.out (M := M)).elim
  have pL : PB fun n => 7 * (n + 2) ^ d := (PB.const 7).mul ((PB.id'.add (PB.const 2)).pow d)
  have pK : PB fun n => 3 * (7 * (n + 2) ^ d) + 3 + tO (7 * (n + 2) ^ d) :=
    (((PB.const 3).mul pL).add (PB.const 3)).add (pO.comp pL)
  have pG : PB fun n => 1 + (tS (7 * (n + 2) ^ d) + (3 * (7 * (n + 2) ^ d) + 3 + tO (7 * (n + 2) ^ d))) :=
    (PB.const 1).add ((pS.comp pL).add pK)
  have pQ : PB fun n => (4 * n + 3 + (tI (3 * n + 2) + (3 * (7 * (n + 2) ^ d) + 3 + tO (7 * (n + 2) ^ d))) + 1 +
      (7 * (n + 2) ^ d + 1)) + (1 + (tS (7 * (n + 2) ^ d) + (3 * (7 * (n + 2) ^ d) + 3 + tO (7 * (n + 2) ^ d)))) :=
    ((((((PB.const 4).mul PB.id').add (PB.const 3)).add
      ((pI.comp (((PB.const 3).mul PB.id').add (PB.const 2))).add pK)).add (PB.const 1)).add
      (pL.add (PB.const 1))).add pG
  obtain ⟨c, hc⟩ := pQ
  refine ⟨⟨tmOf (prog Pi Ps Po), Equiv.refl _, Equiv.refl _⟩, c, fun k => ?_, fun x T S b hr hSd => ?_⟩
  · rcases k with _ | k
    · exact inferInstanceAs (Finite Bool)
    · exact inferInstanceAs (Finite Sym)
  · obtain ⟨L, hLdef⟩ : ∃ L, L = 7 * (x.length + 2) ^ d := ⟨_, rfl⟩
    have hL : ∀ s : M.σ, size s ≤ S → len s ≤ L := fun s hs => by
      have h1 := Carried.le s
      have h2 := hs.trans hSd
      omega
    obtain ⟨s', hs', h3⟩ := mainLoop_within hS hO mS mO hL hr
    have h1 := prologue_within x
    have h2 := within_io ((hI x [] [] [] []).seq (look_within hO (M.init x) [] [] [] [])) []
    have h4 := within_io (dropF_within (Enc.toV s') [] [] [] []) [b]
    rw [List.append_nil] at h2
    have h := ((h1.seq h2).seq h3).seq h4
    have hc' := hc x.length
    dsimp only at hc'
    rw [← hLdef] at hc'
    refine outputs_of_within (h.mono ?_) (List.map_id x) (List.map_id [b])
    have g1 := hL _ (size_le_of_reaches hr)
    have g2 := mO g1
    have g3 : (code (Enc.toV s')).length ≤ L := hL s' hs'
    have g4 : len x = 3 * x.length + 2 := len_bools x
    rw [g4]
    obtain ⟨G, hG⟩ : ∃ G, G = 1 + (tS L + (3 * L + 3 + tO L)) := ⟨_, rfl⟩
    rw [← hG] at hc' ⊢
    obtain ⟨Y, hY⟩ : ∃ Y, Y = c * (x.length + 1) ^ c := ⟨_, rfl⟩
    have e : c * (T + 1) * (x.length + 1) ^ c = T * Y + Y := by rw [hY]; ring
    rw [e]
    rw [← hY] at hc'
    have g5 : T * G ≤ T * Y := Nat.mul_le_mul_left _ (by omega)
    omega
end Groundwork
