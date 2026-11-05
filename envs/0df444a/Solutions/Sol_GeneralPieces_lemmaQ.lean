-- Prove2me | solution 1 for GeneralPieces.lemmaQ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T23:18:40.278895+00:00
-- url     : https://prove2.me/submissions/29779160-4d30-4bbd-b30e-5f4ed47511b6

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_Basic
import Definitions.Def_GeneralPieces_Ring_LemmaQ
import Theorems.Thm_GeneralPieces_LemQ_coef_sub
import Theorems.Thm_GeneralPieces_LemQ_coef_zero
import Theorems.Thm_GeneralPieces_LemQ_coef_sum
import Theorems.Thm_GeneralPieces_LemQ_Tri_sub
import Theorems.Thm_GeneralPieces_LemQ_Tri_eq_zero
import Theorems.Thm_GeneralPieces_LemQ_tri_Q
import Theorems.Thm_P2M_GeneralPieces_LemQ_tri_Q__731a24d79bc8
import Theorems.Thm_GeneralPieces_LemQ_tri_pairing
import Theorems.Thm_GeneralPieces_LemQ_coe_lst
import Theorems.Thm_GeneralPieces_LemQ_sum_lst
import Theorems.Thm_GeneralPieces_LemQ_pos_lst
import Theorems.Thm_GeneralPieces_LemQ_ok_single
import Theorems.Thm_GeneralPieces_LemQ_coef_Q_mon
import Theorems.Thm_P2M_GeneralPieces_LemQ_coef_Q__mon_db0d9c587dd7
import Theorems.Thm_GeneralPieces_LemQ_pairing_mon
import Theorems.Thm_ClauseBound_Boson_Text_coef_smul
import Theorems.Thm_GeneralPieces_Ring_coef_smul
import Theorems.Thm_GeneralPieces_Ring_coef_tpow
import Theorems.Thm_GeneralPieces_Ring_ext_coef
import Theorems.Thm_GeneralPieces_Ring_sum_toN
import Theorems.Thm_GeneralPieces_Ring_toN_injective
import Theorems.Thm_GeneralPieces_Ring_zero_notMem_toN


set_option autoImplicit false
section
section
open GeneralPieces
open AppHalfPieces MvPolynomial Finset GeneralPieces.Ring GeneralPieces.LemQ
namespace GeneralPieces
theorem _root_.solution (hB : StBridge) (hOp : OpFacts) (h1 : O1) (hMa : StMatA) (hMb : StMatB) (hMc : StMatC) : LemmaQ where
  a h a b hh hb ha E f hf s := by
    refine sub_eq_zero.1 (((tri_Q hOp h s).sub (tri_Q' hOp h s)).eq_zero (h := h) (E := E) (fun μ ν σ hμ hν _ => ?_) ha hb hf)
    refine ext_coef fun π => ?_
    rw [coef_sub, coef_Q_mon hB hOp h1 hμ hν, coef_Q'_mon hB hOp h1 hμ hν,
      hMa _ _ (ok_single hμ hν) (pos_lst ν) (by rw [sum_lst, hν]; exact hh) s _ _ (zero_notMem_toN π) (zero_notMem_toN σ), sub_self, coef_zero]
  b h a b hh hb ha E f hf s hs := by
    refine (tri_Q hOp h s).eq_zero (h := h) (E := E) (fun μ ν σ hμ hν hσ => ?_) ha hb hf
    refine ext_coef fun π => ?_
    rw [coef_Q_mon hB hOp h1 hμ hν,
      hMb _ _ (ok_single hμ hν) (pos_lst ν) (by rw [sum_lst, hν]; exact hh) s _ _ (zero_notMem_toN π) (zero_notMem_toN σ) (by rw [sum_toN, sum_lst, hσ, hν]; exact hs),
      coef_zero, Int.cast_zero]
  c h a b hh hb ha E f hf := by
    refine sub_eq_zero.1 (((Tri.sum (Icc (-((E : ℤ) + h)) ((E : ℤ) + h)) fun s => tri_Q hOp h s).sub (tri_pairing hOp h)).eq_zero (h := h) (E := E)
      (fun μ ν σ hμ hν hσ => ?_) ha hb hf)
    refine ext_coef fun π => ?_
    have e := hMc _ _ (ok_single hμ hν) (pos_lst ν) (by rw [sum_lst, hν]; exact hh) _ _ (zero_notMem_toN π) (zero_notMem_toN σ)
    rw [sum_toN, sum_lst, hσ, hν, coe_lst] at e
    rw [coef_sub, coef_sum, coef_smul, coef_tpow, pairing_mon hB hOp, coef_zero]
    simp only [coef_Q_mon hB hOp h1 hμ hν]
    rw [← Int.cast_sum, e]
    by_cases hπ : π = σ
    · rw [if_pos hπ, if_pos (by rw [hπ])]
      simp
    · rw [if_neg hπ, if_neg fun h' => hπ (toN_injective h')]
      simp
end GeneralPieces
