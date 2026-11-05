-- Prove2me | solution 1 for GeneralPieces.Dual.theta_of_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T23:14:58.80561+00:00
-- url     : https://prove2.me/submissions/c5b2873d-b77a-48b7-9670-5997573733bd

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_Op
import Definitions.Def_ClauseBound_Boson_Dual
import Definitions.Def_GeneralPieces_Ring_Dual
import Theorems.Thm_GeneralPieces_Dual_theta_eq

set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Dual
open Finset MvPolynomial AppHalfPieces
namespace GeneralPieces.Dual
theorem _root_.solution (n : ℕ+) (k : ℤ) (h1 : 1 ≤ k) (h2 : k < n) : theta n k = 0 := by
  rw [theta_eq, binom, if_pos (by have := n.pos; omega)]
  obtain ⟨a, ha⟩ : ∃ a : ℕ, (n : ℤ) - k - 1 = a := ⟨((n : ℤ) - k - 1).toNat, by omega⟩
  rw [ha, Ring.choose_natCast, Nat.choose_eq_zero_of_lt (by omega)]
  rfl
end GeneralPieces.Dual
