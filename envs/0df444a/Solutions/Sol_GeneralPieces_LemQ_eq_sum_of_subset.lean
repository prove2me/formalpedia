-- Prove2me | solution 1 for GeneralPieces.LemQ.eq_sum_of_subset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:32:54.637455+00:00
-- url     : https://prove2.me/submissions/0ff68f11-d030-43d9-86ec-ad4a2755e063

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_Basic
import Definitions.Def_GeneralPieces_Ring_LemmaQ
import Theorems.Thm_GeneralPieces_LemQ_coef_sum
import Theorems.Thm_ClauseBound_Boson_Text_coef_smul
import Theorems.Thm_GeneralPieces_Ring_coef_smul
import Theorems.Thm_GeneralPieces_Ring_coef_tpow
import Theorems.Thm_GeneralPieces_Ring_ext_coef


set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.LemQ
open AppHalfPieces MvPolynomial Finset GeneralPieces.Ring
namespace GeneralPieces.LemQ
theorem _root_.solution (f : V) (S : Finset Ptn) (hS : ∀ μ, coef μ f ≠ 0 → μ ∈ S) : f = ∑ μ ∈ S, coef μ f • tpow μ := by
  refine ext_coef fun π => ?_
  rw [coef_sum]
  simp only [coef_smul, coef_tpow, mul_ite, mul_one, mul_zero]
  rw [sum_ite_eq]
  split_ifs with h
  · rfl
  · by_contra h'
    exact h (hS π h')
end GeneralPieces.LemQ
