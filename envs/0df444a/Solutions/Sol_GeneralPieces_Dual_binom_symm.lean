-- Prove2me | solution 1 for GeneralPieces.Dual.binom_symm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T23:18:16.439466+00:00
-- url     : https://prove2.me/submissions/e5bd076c-52aa-46b0-ab5a-a6e5eda53fb2

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_Op
import Definitions.Def_ClauseBound_Boson_Dual
import Definitions.Def_GeneralPieces_Ring_Dual

set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Dual
open Finset MvPolynomial AppHalfPieces
namespace GeneralPieces.Dual
theorem _root_.solution (n j : ℕ) (h : j ≤ n) : binom n ((n : ℤ) - j) = (n.choose j : ℤ) := by
  rw [binom, if_pos (by omega), Ring.choose_natCast, show ((n : ℤ) - j).toNat = n - j by omega, Nat.choose_symm h]
end GeneralPieces.Dual
