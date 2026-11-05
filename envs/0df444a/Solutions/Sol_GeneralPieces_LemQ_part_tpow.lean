-- Prove2me | solution 1 for GeneralPieces.LemQ.part_tpow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T23:13:22.736216+00:00
-- url     : https://prove2.me/submissions/cd114e1b-7c08-4a3b-af35-1d8a3502127f

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_Basic
import Definitions.Def_GeneralPieces_Ring_LemmaQ
import Theorems.Thm_GeneralPieces_LemQ_coef_zero
import Theorems.Thm_GeneralPieces_LemQ_coef_part
import Theorems.Thm_GeneralPieces_Ring_coef_tpow
import Theorems.Thm_GeneralPieces_Ring_ext_coef


set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.LemQ
open AppHalfPieces MvPolynomial Finset GeneralPieces.Ring
namespace GeneralPieces.LemQ
theorem _root_.solution (h' : ℕ) (μ : Ptn) : part h' (tpow μ) = if h' = wt μ then tpow μ else 0 := by
  refine ext_coef fun π => ?_
  rw [coef_part]
  by_cases h : h' = wt μ
  · rw [if_pos h]
    by_cases hπ : wt π = h'
    · rw [if_pos hπ]
    · rw [if_neg hπ, coef_tpow, if_neg]
      rintro rfl
      exact hπ h.symm
  · rw [if_neg h, coef_zero]
    split_ifs with hπ
    · rw [coef_tpow, if_neg]
      rintro rfl
      exact h hπ.symm
    · rfl
end GeneralPieces.LemQ
