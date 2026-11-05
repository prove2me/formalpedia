-- Prove2me | solution 1 for GeneralPieces.Ring.nordQ_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T20:18:28.651161+00:00
-- url     : https://prove2.me/submissions/6e65a2cc-e194-42a9-bbd3-c04641bd69bf

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_Basic
import Definitions.Def_GeneralPieces_Ring_OpFacts
import Theorems.Thm_GeneralPieces_Ring_nabla_sum
import Theorems.Thm_GeneralPieces_Ring_eq_sum_tpow
import Theorems.Thm_GeneralPieces_Ring_foldr_nabla_smul
import Theorems.Thm_GeneralPieces_Ring_foldr_nabla_zero
import Theorems.Thm_GeneralPieces_Ring_pos_eq_zero


set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Ring
open AppHalfPieces MvPolynomial Finset
namespace GeneralPieces.Ring
theorem _root_.solution {f : V} {E : ℤ} (hf : Bd f E) (ks : List ℤ) (h : E < (ks.filter (0 < ·)).sum) : nordQ ks f = 0 := by
  have h0 : (ks.filter (0 < ·)).foldr nabla f = 0 := by
    rw [eq_sum_tpow f]
    have hs : ∀ (l : List ℤ) (s : Finset (ℕ+ →₀ ℕ)) (F : (ℕ+ →₀ ℕ) → V), l.foldr nabla (∑ d ∈ s, F d) = ∑ d ∈ s, l.foldr nabla (F d) := by
      intro l s F
      induction l with
      | nil => rfl
      | cons k l ih => rw [List.foldr_cons, ih, nabla_sum]; rfl
    rw [hs]
    refine sum_eq_zero fun d hd => ?_
    rw [foldr_nabla_smul, pos_eq_zero _ (fun x hx => by simpa using (List.mem_filter.1 hx).2), smul_zero]
    refine lt_of_le_of_lt (hf _ ?_) h
    unfold coef
    rw [Finsupp.toMultiset_toFinsupp]
    exact mem_support_iff.1 hd
  rw [nordQ, h0, foldr_nabla_zero]
end GeneralPieces.Ring
