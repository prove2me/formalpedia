-- Prove2me | solution 1 for GeneralPieces.pieceFacts
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T23:30:51.563204+00:00
-- url     : https://prove2.me/submissions/67cb7541-d00d-4f61-b1ea-8c4a59e4c6be

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_LemmaQ
import Definitions.Def_GeneralPieces_Ring_Pieces
import Theorems.Thm_GeneralPieces_Pcs_wtLe_of_le
import Theorems.Thm_GeneralPieces_Pcs_Le_sum
import Theorems.Thm_GeneralPieces_Pcs_le_aFam
import Theorems.Thm_GeneralPieces_Pcs_isInt_tpow
import Theorems.Thm_GeneralPieces_Pcs_isInt_aFam
import Theorems.Thm_GeneralPieces_Pcs_isInt_angle
import Theorems.Thm_GeneralPieces_Pcs_isInt_bFam
import Theorems.Thm_GeneralPieces_Pcs_bFam_mem
import Theorems.Thm_GeneralPieces_Pcs_coef_comp_gen
import Theorems.Thm_GeneralPieces_Pcs_one_le_pZ
import Theorems.Thm_ClauseBound_Boson_Text_coef_smul
import Theorems.Thm_GeneralPieces_LemQ_coef_sum
import Theorems.Thm_GeneralPieces_Ring_coef_smul
import Theorems.Thm_GeneralPieces_Ring_coef_tpow
import Theorems.Thm_GeneralPieces_Ring_tpow_mem_VE


set_option autoImplicit false
section
section
open GeneralPieces
open AppHalfPieces MvPolynomial Finset GeneralPieces.Ring GeneralPieces.LemQ GeneralPieces.Pcs
namespace GeneralPieces
theorem _root_.solution (hQ : LemmaQ) (hD : LemmaDual) (hOp : OpFacts) (h1 : O1) (hZ : ZDvd) : PieceFacts where
  wtLe h μ hμ := by
    rw [← hμ]
    exact wtLe_of_le (le_aFam μ)
  sum h ξ η υ ν hh hξ hη hυ hν := by
    have ha : WtLe h (aFam ξ) := by rw [← hξ]; exact wtLe_of_le (le_aFam ξ)
    have hb : bFam ν ∈ VE h := by rw [← hν]; exact bFam_mem ν
    have hf : tpow η ∈ VE h := by rw [← hη]; exact tpow_mem_VE η
    have e := hQ.c h (aFam ξ) (bFam ν) hh hb ha h (tpow η) hf
    have e2 : pairing h (aFam ξ) (bFam ν) = if ξ = ν then (h.factorial : ℚ) else 0 := by
      rw [pairing, hD h ξ ν hξ hν, coeff_C, if_pos rfl]
    rw [show (2 * h : ℤ) = (h : ℤ) + h by ring, ← coef_sum, e, e2, coef_smul, coef_tpow]
    by_cases h3 : ξ = ν <;> by_cases h4 : η = υ <;> simp [h3, h4, eq_comm]
  row h ξ η υ ν s hh hξ hη hυ hν := by
    have ha : WtLe h (aFam ξ) := by rw [← hξ]; exact wtLe_of_le (le_aFam ξ)
    have hb : bFam ν ∈ VE h := by rw [← hν]; exact bFam_mem ν
    have hf : tpow η ∈ VE h := by rw [← hη]; exact tpow_mem_VE η
    rw [hQ.a h (aFam ξ) (bFam ν) hh hb ha h (tpow η) hf s, Q', coef_sum]
    refine sum_congr rfl fun i _ => ?_
    rw [coef_smul, coef_comp_gen hOp h1 _ _ _ _ hf, mul_sum, show (h : ℤ) + (s - h + i) = s + i by ring]
    exact sum_congr rfl fun σ _ => by ring
  col h ξ η υ ν s hh hξ hη hυ hν := by
    have hf : tpow η ∈ VE h := by rw [← hη]; exact tpow_mem_VE η
    rw [Q, coef_sum]
    refine sum_congr rfl fun i _ => ?_
    rw [coef_smul, coef_comp_gen hOp h1 _ _ _ _ hf, mul_sum, show (h : ℤ) + (h - s - i) = 2 * h - s - i by ring]
    exact sum_congr rfl fun σ _ => by ring
  int_a h i ξ σ r := h1.int _ r _ (isInt_angle (isInt_aFam ξ) h i) (isInt_tpow σ)
  int_b ν σ r := h1.int _ r _ (isInt_bFam hZ ν) (isInt_tpow σ)
  terms h s hs := by
    have h2 := abs_le.1 hs
    constructor
    · unfold Rrow
      exact (one_le_pZ (m := s + (2 * h : ℕ)) (by push_cast; omega)).trans
        (single_le_sum (f := fun i : ℕ => pZ (s + i)) (fun _ _ => Nat.zero_le _) (mem_range.2 (by omega)))
    · unfold Rcol
      exact (one_le_pZ (m := 2 * h - s - (0 : ℕ)) (by push_cast; omega)).trans
        (single_le_sum (f := fun i : ℕ => pZ (2 * h - s - i)) (fun _ _ => Nat.zero_le _) (mem_range.2 (by omega)))
end GeneralPieces
