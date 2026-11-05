-- Prove2me | solution 1 for GeneralPieces.Ring.term_cons_neg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T22:37:37.598894+00:00
-- url     : https://prove2.me/submissions/fed56ed5-94c5-4054-958e-4b4592752386

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_Basic
import Definitions.Def_GeneralPieces_Ring_OpFacts
import Theorems.Thm_GeneralPieces_Ring_wtQ_cons
import Theorems.Thm_GeneralPieces_Ring_nabla_neg
import Theorems.Thm_GeneralPieces_Ring_nabla_smul
import Theorems.Thm_GeneralPieces_Ring_nordQ_cons_neg
import Theorems.Thm_GeneralPieces_Ring_term_eq


set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Ring
open AppHalfPieces MvPolynomial Finset
namespace GeneralPieces.Ring
theorem _root_.solution (n : ℕ+) (μ : List ℕ+) {k : ℤ} (hk : k < 0) (ks : List ℤ) (f : V) :
    term (n :: μ) (k :: ks) f = (binom (-k - 1) ((n : ℤ) - 1) : ℚ) • nabla k (term μ ks f) := by
  rw [term_eq, term_eq, wtQ_cons, nordQ_cons_neg hk, nabla_smul, nabla_neg hk, smul_smul]
  push_cast
  rfl
end GeneralPieces.Ring
