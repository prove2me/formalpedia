-- Prove2me | solution 1 for GeneralPieces.Ring.term_cons_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T22:37:42.095312+00:00
-- url     : https://prove2.me/submissions/99f3ed08-269a-48f2-89a1-0730a7605773

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_Basic
import Definitions.Def_GeneralPieces_Ring_OpFacts
import Theorems.Thm_GeneralPieces_Ring_wtQ_cons
import Theorems.Thm_GeneralPieces_Ring_nordQ_cons_pos
import Theorems.Thm_GeneralPieces_Ring_term_eq


set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Ring
open AppHalfPieces MvPolynomial Finset
namespace GeneralPieces.Ring
theorem _root_.solution (n : ℕ+) (μ : List ℕ+) {k : ℤ} (hk : 0 < k) (ks : List ℤ) (f : V) :
    term (n :: μ) (k :: ks) f = (binom (-k - 1) ((n : ℤ) - 1) : ℚ) • term μ ks (nabla k f) := by
  rw [term_eq, term_eq, wtQ_cons, nordQ_cons_pos hk, smul_smul]
  push_cast
  rfl
end GeneralPieces.Ring
