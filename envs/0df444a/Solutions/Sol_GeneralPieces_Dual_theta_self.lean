-- Prove2me | solution 1 for GeneralPieces.Dual.theta_self
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T23:16:14.753392+00:00
-- url     : https://prove2.me/submissions/b6d11584-29d0-4643-a9fd-a3155d36a882

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_Op
import Definitions.Def_ClauseBound_Boson_Dual
import Definitions.Def_GeneralPieces_Ring_Dual
import Theorems.Thm_GeneralPieces_Dual_theta_eq
import Theorems.Thm_GeneralPieces_Dual_choose_neg_one

set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Dual
open Finset MvPolynomial AppHalfPieces
namespace GeneralPieces.Dual
theorem _root_.solution (n : ℕ+) : theta n n = (-1) ^ ((n : ℕ) - 1) := by
  rw [theta_eq, binom, if_pos (by have := n.pos; omega), show (n : ℤ) - n - 1 = -1 by ring, choose_neg_one]
  congr 1
  omega
end GeneralPieces.Dual
