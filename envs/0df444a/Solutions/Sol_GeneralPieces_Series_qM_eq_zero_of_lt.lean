-- Prove2me | solution 1 for GeneralPieces.Series.qM_eq_zero_of_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T23:07:51.82188+00:00
-- url     : https://prove2.me/submissions/ba66c8f9-06b9-4f17-9e01-8706f0d68f73

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Series_OneLaurent
import Mathlib.Data.Nat.Choose.Sum
import Definitions.Def_GeneralPieces_Series_ReadOff
import Theorems.Thm_GeneralPieces_Series_mul2_eq_zero


set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Series
open ClauseBound.Boson Finset
variable {a b : List ℕ} {G : ℚ} {π σ : Multiset ℕ}
namespace GeneralPieces.Series
theorem _root_.solution {a b : List ℕ} (hab : a.sum ≤ b.sum) (π : Multiset ℕ) {σ : Multiset ℕ} {s : ℤ} (h : s < -(σ.sum : ℤ) - b.sum) : qM a b s π σ = 0 :=
  sum_eq_zero fun i hi => by
    have := mem_range.1 hi
    rw [mul2_eq_zero b a _ π (by omega), mul_zero]
end GeneralPieces.Series
