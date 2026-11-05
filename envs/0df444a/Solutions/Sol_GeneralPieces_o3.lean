-- Prove2me | solution 1 for GeneralPieces.o3
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T22:44:53.988115+00:00
-- url     : https://prove2.me/submissions/49c435f3-4a70-427a-a5ff-58fc917ba0aa

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_OpFacts
import Definitions.Def_GeneralPieces_Ring_Op
import Theorems.Thm_GeneralPieces_Ring_op_mem
import Theorems.Thm_GeneralPieces_Ring_Bd_of_mem
import Theorems.Thm_GeneralPieces_Ring_filter_sums
import Theorems.Thm_GeneralPieces_Ring_mem_VE_zero
import Theorems.Thm_GeneralPieces_Ring_nordQ_eq_zero
import Theorems.Thm_GeneralPieces_Ring_term_eq


set_option autoImplicit false
section
section
open GeneralPieces
open AppHalfPieces MvPolynomial Finset GeneralPieces.Ring
namespace GeneralPieces
theorem _root_.solution : O3 where
  number := fun h a b hb => by
    have h1 := op_mem a (-(h : ℤ)) hb
    rw [add_neg_cancel] at h1
    obtain ⟨q, hq⟩ := (mem_VE_zero _).1 h1
    rw [pairing, hq, coeff_C, if_pos rfl]
  positive := fun h μ b ks hb hks hneg => by
    obtain ⟨a1, a2, a3, a4⟩ := filter_sums ks
    obtain ⟨k, hk, hk'⟩ := hneg
    have a5 := a4 k hk
    have a6 : ks.sum = -(-(h : ℤ)) := hks.2.2
    rw [term_eq, nordQ_eq_zero (Bd_of_mem hb) ks (by omega), smul_zero]
end GeneralPieces
