-- Prove2me | solution 1 for Given.onSteps
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T10:53:35.478268+00:00
-- url     : https://prove2.me/submissions/ad141226-5127-4f5c-a2f0-1f4e4e387b72

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GivenStatement
import Definitions.Def_Printed_LevelFrom
import Definitions.Def_Printed_Count
import Mathlib.Tactic
import Definitions.Def_Given_Networks
import Theorems.Thm_Given_stOnGiven
import Theorems.Thm_Given_onClosed
import Theorems.Thm_ClauseBound_Alg_CertGridG_D_unary__6c8f65
import Theorems.Thm_ClauseBound_Alg_CertGridG_K_unary
import Theorems.Thm_ClauseBound_Alg_CertGridG_Nof_unary
import Theorems.Thm_ClauseBound_Alg_CertGridG_a_unary
import Theorems.Thm_ClauseBound_Alg_CertGridG_b_unary
import Theorems.Thm_ClauseBound_Alg_CertGridG_c2_polyT
import Theorems.Thm_ClauseBound_Alg_CertGridG_c2_unary
import Theorems.Thm_ClauseBound_Alg_CertGridG_chkG_polyT
import Theorems.Thm_ClauseBound_Alg_CertGridG_d_unary
import Theorems.Thm_ClauseBound_Alg_CertGridG_h_unary
import Theorems.Thm_ClauseBound_Alg_CertGridG_heG_polyT
import Theorems.Thm_ClauseBound_Alg_CertGridG_nMemb_polyT
import Theorems.Thm_ClauseBound_Alg_CertGridG_nMemb_unary
import Theorems.Thm_ClauseBound_Alg_CertGridG_nParts_polyT
import Theorems.Thm_ClauseBound_Alg_CertGridG_nParts_unary
import Theorems.Thm_ClauseBound_Alg_CertGridG_nRectG_polyT
import Theorems.Thm_ClauseBound_Alg_CertGridG_nRectG_unary
import Theorems.Thm_ClauseBound_Alg_CertGridG_nodeG_polyT
import Theorems.Thm_ClauseBound_Alg_CertGridG_p_unary
import Theorems.Thm_ClauseBound_Alg_CertGridG_rectIxG_polyT
import Theorems.Thm_ClauseBound_Alg_CertGridG_sqrt_polyT
import Theorems.Thm_ClauseBound_Alg_CertGridG_sqrt_unary
import Theorems.Thm_ClauseBound_Alg_CertGridG_thin_polyT
import Theorems.Thm_ClauseBound_Alg_CertGridG_tri_unary
import Theorems.Thm_ClauseBound_Alg_CertGridG_unary_ite
import Theorems.Thm_ClauseBound_Alg_CertGridG_unary_max
import Theorems.Thm_ClauseBound_Alg_CertGridG_unary_min
import Theorems.Thm_ClauseBound_Alg_CertGridG_unary_mod
import Theorems.Thm_Eight_ViaGrouping_restr_polyT
import Theorems.Thm_Groundwork_Decode_clauseDec_polyT
import Theorems.Thm_Groundwork_Decode_slotDec_polyT
import Theorems.Thm_Groundwork_Decode_width_polyT
import Theorems.Thm_Groundwork_PolyT_all
import Theorems.Thm_Groundwork_PolyT_any
import Theorems.Thm_Groundwork_PolyT_comp
import Theorems.Thm_Groundwork_PolyT_const
import Theorems.Thm_Groundwork_PolyT_contains
import Theorems.Thm_Groundwork_PolyT_count
import Theorems.Thm_Groundwork_PolyT_countP
import Theorems.Thm_Groundwork_PolyT_decide_mem
import Theorems.Thm_Groundwork_PolyT_dedup
import Theorems.Thm_Groundwork_PolyT_div
import Theorems.Thm_Groundwork_PolyT_div_pow
import Theorems.Thm_Groundwork_PolyT_dropWhile
import Theorems.Thm_Groundwork_PolyT_elem
import Theorems.Thm_Groundwork_PolyT_filter
import Theorems.Thm_Groundwork_PolyT_filterMap
import Theorems.Thm_Groundwork_PolyT_flatMap
import Theorems.Thm_Groundwork_PolyT_fst
import Theorems.Thm_Groundwork_PolyT_idxOf
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_PolyT_map
import Theorems.Thm_Groundwork_PolyT_mod
import Theorems.Thm_Groundwork_PolyT_mul
import Theorems.Thm_Groundwork_PolyT_optionElim
import Theorems.Thm_Groundwork_PolyT_pow_const
import Theorems.Thm_Groundwork_PolyT_prodMk
import Theorems.Thm_Groundwork_PolyT_product
import Theorems.Thm_Groundwork_PolyT_snd
import Theorems.Thm_Groundwork_PolyT_sprod
import Theorems.Thm_Groundwork_PolyT_sum
import Theorems.Thm_Groundwork_PolyT_sumElim
import Theorems.Thm_Groundwork_PolyT_takeWhile
import Theorems.Thm_Groundwork_PolyT_testBit
import Theorems.Thm_Groundwork_Prog_Count_linkB_polyT
import Theorems.Thm_Groundwork_Prog_Count_links_polyT
import Theorems.Thm_Groundwork_Prog_Count_litAt_polyT
import Theorems.Thm_Groundwork_Prog_Count_locals_polyT
import Theorems.Thm_Groundwork_Prog_Count_mu_polyT
import Theorems.Thm_Groundwork_Prog_Count_rows_polyT
import Theorems.Thm_Groundwork_Prog_Count_slotsOf_polyT
import Theorems.Thm_Groundwork_Prog_Count_varAt_polyT
import Theorems.Thm_Groundwork_Prog_NetE_Pc_polyT
import Theorems.Thm_Groundwork_Prog_NetE_betaC_polyT
import Theorems.Thm_Groundwork_Prog_NetE_capWord_polyT
import Theorems.Thm_Groundwork_Prog_NetE_cap_polyT
import Theorems.Thm_Groundwork_Prog_NetE_col_polyT
import Theorems.Thm_Groundwork_Prog_NetE_lAt_polyT
import Theorems.Thm_Groundwork_Prog_NetE_labOf_polyT
import Theorems.Thm_Groundwork_Prog_NetE_lbLen_polyT
import Theorems.Thm_Groundwork_Prog_NetE_lbLens_polyT
import Theorems.Thm_Groundwork_Prog_NetE_members_polyT
import Theorems.Thm_Groundwork_Prog_NetE_n_polyT
import Theorems.Thm_Groundwork_Prog_NetE_prs_polyT
import Theorems.Thm_Groundwork_Prog_NetE_stLens_polyT
import Theorems.Thm_Groundwork_Prog_NetE_zA_polyT
import Theorems.Thm_Groundwork_Prog_NetE_zAt_polyT
import Theorems.Thm_Groundwork_Prog_NetE_zOf_polyT
import Theorems.Thm_Groundwork_Sparsify_polyT_addP
import Theorems.Thm_Groundwork_Sparsify_polyT_canonP
import Theorems.Thm_Groundwork_Sparsify_polyT_greedyP
import Theorems.Thm_Groundwork_Sparsify_polyT_litsOf
import Theorems.Thm_Groundwork_Sparsify_polyT_minusP
import Theorems.Thm_Groundwork_Sparsify_polyT_overP
import Theorems.Thm_Groundwork_Sparsify_polyT_pickP
import Theorems.Thm_Groundwork_Sparsify_polyT_redP
import Theorems.Thm_Groundwork_Sparsify_polyT_rootP
import Theorems.Thm_Groundwork_Sparsify_polyT_stepP
import Theorems.Thm_Groundwork_Sparsify_polyT_subP
import Theorems.Thm_Groundwork_block_polyT
import Theorems.Thm_Groundwork_digit_polyT
import Theorems.Thm_Groundwork_query0_polyT
import Theorems.Thm_Groundwork_tri_polyT
import Theorems.Thm_P2M_Groundwork_PolyT_chunks__bc5b8682856d
import Theorems.Thm_P2M_Groundwork_PolyT_cond__4c673073da15
import Theorems.Thm_P2M_Groundwork_PolyT_cons__3a60f43a3b86
import Theorems.Thm_P2M_Groundwork_PolyT_find__e812ffd764ea
import Theorems.Thm_P2M_Groundwork_PolyT_id__1c5d0f44cc8f
import Theorems.Thm_P2M_Groundwork_PolyT_inl__78f4b62d65a1
import Theorems.Thm_P2M_Groundwork_PolyT_inr__53ca1f30b2d3
import Theorems.Thm_P2M_Groundwork_PolyT_ite__226169acf219
import Theorems.Thm_P2M_Groundwork_PolyT_log2__935ea318e2e8
import Theorems.Thm_P2M_Groundwork_PolyT_ofWord__0eb069943014
import Theorems.Thm_P2M_Groundwork_PolyT_size__c8c8eb1b342f
import Theorems.Thm_P2M_Groundwork_PolyT_some__e6a32bd6af45
import Theorems.Thm_PaddedDescent_F_CertGrid_look_polyT
import Theorems.Thm_PaddedDescent_F_CertGrid_nRect_polyT
import Theorems.Thm_PaddedDescent_F_CertGrid_nRect_unary
import Theorems.Thm_PaddedDescent_F_CertGrid_priceCol_polyT
import Theorems.Thm_PaddedDescent_F_CertGrid_priceRow_polyT
import Theorems.Thm_PaddedDescent_F_CertGrid_sideCtx_polyT
import Theorems.Thm_PaddedDescent_F_cap_polyT
import Theorems.Thm_Printed_networkOn_close
attribute [local fun_prop] ClauseBound.Alg.CertGridG.D_unary
attribute [local fun_prop] ClauseBound.Alg.CertGridG.K_unary
attribute [local fun_prop] ClauseBound.Alg.CertGridG.Nof_unary
attribute [local fun_prop] ClauseBound.Alg.CertGridG.a_unary
attribute [local fun_prop] ClauseBound.Alg.CertGridG.b_unary
attribute [local fun_prop] ClauseBound.Alg.CertGridG.c2_polyT
attribute [local fun_prop] ClauseBound.Alg.CertGridG.c2_unary
attribute [local fun_prop] ClauseBound.Alg.CertGridG.chkG_polyT
attribute [local fun_prop] ClauseBound.Alg.CertGridG.d_unary
attribute [local fun_prop] ClauseBound.Alg.CertGridG.h_unary
attribute [local fun_prop] ClauseBound.Alg.CertGridG.heG_polyT
attribute [local fun_prop] ClauseBound.Alg.CertGridG.nMemb_polyT
attribute [local fun_prop] ClauseBound.Alg.CertGridG.nMemb_unary
attribute [local fun_prop] ClauseBound.Alg.CertGridG.nParts_polyT
attribute [local fun_prop] ClauseBound.Alg.CertGridG.nParts_unary
attribute [local fun_prop] ClauseBound.Alg.CertGridG.nRectG_polyT
attribute [local fun_prop] ClauseBound.Alg.CertGridG.nRectG_unary
attribute [local fun_prop] ClauseBound.Alg.CertGridG.nodeG_polyT
attribute [local fun_prop] ClauseBound.Alg.CertGridG.p_unary
attribute [local fun_prop] ClauseBound.Alg.CertGridG.rectIxG_polyT
attribute [local fun_prop] ClauseBound.Alg.CertGridG.sqrt_polyT
attribute [local fun_prop] ClauseBound.Alg.CertGridG.sqrt_unary
attribute [local fun_prop] ClauseBound.Alg.CertGridG.thin_polyT
attribute [local fun_prop] ClauseBound.Alg.CertGridG.tri_unary
attribute [local fun_prop] ClauseBound.Alg.CertGridG.unary_ite
attribute [local fun_prop] ClauseBound.Alg.CertGridG.unary_max
attribute [local fun_prop] ClauseBound.Alg.CertGridG.unary_min
attribute [local fun_prop] ClauseBound.Alg.CertGridG.unary_mod
attribute [local fun_prop] Eight.ViaGrouping.restr_polyT
attribute [local fun_prop] Groundwork.Decode.clauseDec_polyT
attribute [local fun_prop] Groundwork.Decode.slotDec_polyT
attribute [local fun_prop] Groundwork.Decode.width_polyT
attribute [local fun_prop] Groundwork.PolyT.all
attribute [local fun_prop] Groundwork.PolyT.any
attribute [local fun_prop] Groundwork.PolyT.comp
attribute [local fun_prop] Groundwork.PolyT.const
attribute [local fun_prop] Groundwork.PolyT.contains
attribute [local fun_prop] Groundwork.PolyT.count
attribute [local fun_prop] Groundwork.PolyT.countP
attribute [local fun_prop] Groundwork.PolyT.decide_mem
attribute [local fun_prop] Groundwork.PolyT.dedup
attribute [local fun_prop] Groundwork.PolyT.div
attribute [local fun_prop] Groundwork.PolyT.div_pow
attribute [local fun_prop] Groundwork.PolyT.dropWhile
attribute [local fun_prop] Groundwork.PolyT.elem
attribute [local fun_prop] Groundwork.PolyT.filter
attribute [local fun_prop] Groundwork.PolyT.filterMap
attribute [local fun_prop] Groundwork.PolyT.flatMap
attribute [local fun_prop] Groundwork.PolyT.fst
attribute [local fun_prop] Groundwork.PolyT.idxOf
attribute [local fun_prop] Groundwork.PolyT.length
attribute [local fun_prop] Groundwork.PolyT.map
attribute [local fun_prop] Groundwork.PolyT.mod
attribute [local fun_prop] Groundwork.PolyT.mul
attribute [local fun_prop] Groundwork.PolyT.optionElim
attribute [local fun_prop] Groundwork.PolyT.pow_const
attribute [local fun_prop] Groundwork.PolyT.prodMk
attribute [local fun_prop] Groundwork.PolyT.product
attribute [local fun_prop] Groundwork.PolyT.snd
attribute [local fun_prop] Groundwork.PolyT.sprod
attribute [local fun_prop] Groundwork.PolyT.sum
attribute [local fun_prop] Groundwork.PolyT.sumElim
attribute [local fun_prop] Groundwork.PolyT.takeWhile
attribute [local fun_prop] Groundwork.PolyT.testBit
attribute [local fun_prop] Groundwork.Prog.Count.linkB_polyT
attribute [local fun_prop] Groundwork.Prog.Count.links_polyT
attribute [local fun_prop] Groundwork.Prog.Count.litAt_polyT
attribute [local fun_prop] Groundwork.Prog.Count.locals_polyT
attribute [local fun_prop] Groundwork.Prog.Count.mu_polyT
attribute [local fun_prop] Groundwork.Prog.Count.rows_polyT
attribute [local fun_prop] Groundwork.Prog.Count.slotsOf_polyT
attribute [local fun_prop] Groundwork.Prog.Count.varAt_polyT
attribute [local fun_prop] Groundwork.Prog.NetE.Pc_polyT
attribute [local fun_prop] Groundwork.Prog.NetE.betaC_polyT
attribute [local fun_prop] Groundwork.Prog.NetE.capWord_polyT
attribute [local fun_prop] Groundwork.Prog.NetE.cap_polyT
attribute [local fun_prop] Groundwork.Prog.NetE.col_polyT
attribute [local fun_prop] Groundwork.Prog.NetE.lAt_polyT
attribute [local fun_prop] Groundwork.Prog.NetE.labOf_polyT
attribute [local fun_prop] Groundwork.Prog.NetE.lbLen_polyT
attribute [local fun_prop] Groundwork.Prog.NetE.lbLens_polyT
attribute [local fun_prop] Groundwork.Prog.NetE.members_polyT
attribute [local fun_prop] Groundwork.Prog.NetE.n_polyT
attribute [local fun_prop] Groundwork.Prog.NetE.prs_polyT
attribute [local fun_prop] Groundwork.Prog.NetE.stLens_polyT
attribute [local fun_prop] Groundwork.Prog.NetE.zA_polyT
attribute [local fun_prop] Groundwork.Prog.NetE.zAt_polyT
attribute [local fun_prop] Groundwork.Prog.NetE.zOf_polyT
attribute [local fun_prop] Groundwork.Sparsify.polyT_addP
attribute [local fun_prop] Groundwork.Sparsify.polyT_canonP
attribute [local fun_prop] Groundwork.Sparsify.polyT_greedyP
attribute [local fun_prop] Groundwork.Sparsify.polyT_litsOf
attribute [local fun_prop] Groundwork.Sparsify.polyT_minusP
attribute [local fun_prop] Groundwork.Sparsify.polyT_overP
attribute [local fun_prop] Groundwork.Sparsify.polyT_pickP
attribute [local fun_prop] Groundwork.Sparsify.polyT_redP
attribute [local fun_prop] Groundwork.Sparsify.polyT_rootP
attribute [local fun_prop] Groundwork.Sparsify.polyT_stepP
attribute [local fun_prop] Groundwork.Sparsify.polyT_subP
attribute [local fun_prop] Groundwork.block_polyT
attribute [local fun_prop] Groundwork.digit_polyT
attribute [local fun_prop] Groundwork.query0_polyT
attribute [local fun_prop] Groundwork.tri_polyT
attribute [local fun_prop] P2M_Groundwork_PolyT_chunks__bc5b8682856d
attribute [local fun_prop] P2M_Groundwork_PolyT_cond__4c673073da15
attribute [local fun_prop] P2M_Groundwork_PolyT_cons__3a60f43a3b86
attribute [local fun_prop] P2M_Groundwork_PolyT_find__e812ffd764ea
attribute [local fun_prop] P2M_Groundwork_PolyT_id__1c5d0f44cc8f
attribute [local fun_prop] P2M_Groundwork_PolyT_inl__78f4b62d65a1
attribute [local fun_prop] P2M_Groundwork_PolyT_inr__53ca1f30b2d3
attribute [local fun_prop] P2M_Groundwork_PolyT_ite__226169acf219
attribute [local fun_prop] P2M_Groundwork_PolyT_log2__935ea318e2e8
attribute [local fun_prop] P2M_Groundwork_PolyT_ofWord__0eb069943014
attribute [local fun_prop] P2M_Groundwork_PolyT_size__c8c8eb1b342f
attribute [local fun_prop] P2M_Groundwork_PolyT_some__e6a32bd6af45
attribute [local fun_prop] PaddedDescent.F.CertGrid.look_polyT
attribute [local fun_prop] PaddedDescent.F.CertGrid.nRect_polyT
attribute [local fun_prop] PaddedDescent.F.CertGrid.nRect_unary
attribute [local fun_prop] PaddedDescent.F.CertGrid.priceCol_polyT
attribute [local fun_prop] PaddedDescent.F.CertGrid.priceRow_polyT
attribute [local fun_prop] PaddedDescent.F.CertGrid.sideCtx_polyT
attribute [local fun_prop] PaddedDescent.F.cap_polyT



set_option autoImplicit false
section
section
open Given
open Finset Groundwork Groundwork.Prog Groundwork.Prog.Count Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet Eight Eight.SecNetworks Eight.Level Eight.ViaGrouping Paper QueryMachines QueryMachines.QueryMachine Printed
variable {Q A C : Type}
namespace Given
theorem _root_.solution {NM : NetMachine} {C₁ g K : ℕ} {e : ℝ} (hNM : ComputesNetworks NM C₁ g K e) [HasSize C] [Enc C] [Carried C] {Np : Procs C} {c : C} {N : Net g} {P B τ S : ℕ}
    (h : IsGivenNetwork (ofProcs Np) noTable c N P B τ S) :
    (NM.PolyTimeSteps → Nonempty (IsPolyT (networkOnSteps g NM Np))) ∧
    ∃ T : ℕ, (networkOnSteps g NM Np).Runs c T (size c + C₁ * (P + B) ^ C₁ + S + 4) N.value ∧
      (T : ℝ) ≤ 3 * (C₁ * (2 : ℝ) ^ (e * ((N.U : ℝ) + (g : ℝ) * P / K) + 2 * ((g : ℝ) * P) / K) * ((P : ℝ) + B) ^ C₁) * τ := by
  refine ⟨fun hN => ?_, onClosed hNM h⟩
  obtain ⟨i⟩ := (stOnGiven NM C₁ g K e hNM Unit Unit C (ofProcs Np) noTable c N P B τ S h).1 hN
  have hc : (networkOn g NM (ofProcs Np)).close noTable = networkOnSteps g NM Np := networkOn_close g NM (ofProcs Np) noTable
  rw [← hc]
  exact ⟨close_isPolyT _ (by unfold noTable; fun_prop)⟩
end Given
