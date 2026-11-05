-- Prove2me | solution 1 for GeneralPieces.Ring.term_swap
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T22:38:51.764309+00:00
-- url     : https://prove2.me/submissions/3bf5a86d-cee4-4d71-8306-30b7f37b6255

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_Basic
import Definitions.Def_GeneralPieces_Ring_OpFacts
import Theorems.Thm_GeneralPieces_Ring_wtQ_cons
import Theorems.Thm_GeneralPieces_Ring_nordQ_perm
import Theorems.Thm_GeneralPieces_Ring_term_eq


set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Ring
open AppHalfPieces MvPolynomial Finset
namespace GeneralPieces.Ring
theorem _root_.solution (x y : ℕ+) (μ : List ℕ+) (k k' : ℤ) (ks : List ℤ) (f : V) : term (y :: x :: μ) (k :: k' :: ks) f = term (x :: y :: μ) (k' :: k :: ks) f := by
  rw [term_eq, term_eq, wtQ_cons, wtQ_cons, wtQ_cons, wtQ_cons, mul_left_comm, nordQ_perm (List.Perm.swap k' k ks)]
end GeneralPieces.Ring
