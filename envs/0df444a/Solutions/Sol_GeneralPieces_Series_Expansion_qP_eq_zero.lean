-- Prove2me | solution 1 for GeneralPieces.Series.Expansion.qP_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T23:12:32.910207+00:00
-- url     : https://prove2.me/submissions/61e11ed5-63a3-4388-a071-f0aeb9e9f931

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Series_OneLaurent
import Mathlib.Data.Nat.Choose.Sum
import Definitions.Def_GeneralPieces_Series_ReadOff
import Theorems.Thm_GeneralPieces_Series_Expansion_qP_eq_qM
import Theorems.Thm_GeneralPieces_Series_qP_eq_zero_of_lt
import Theorems.Thm_GeneralPieces_Series_qM_eq_zero_of_lt

set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Series
open ClauseBound.Boson Finset
variable {a b : List ℕ} {G : ℚ} {π σ : Multiset ℕ}
namespace GeneralPieces.Series
namespace Expansion
theorem _root_.solution (X : Expansion a b G π σ) (hab : a.sum ≤ b.sum) {s : ℤ} (hs : (σ.sum : ℤ) + b.sum < |s|) : qP a b s π σ = 0 := by
  rcases lt_abs.1 hs with h | h
  · exact qP_eq_zero_of_lt a b π h
  · rw [X.qP_eq_qM, qM_eq_zero_of_lt hab π (by omega)]
end Expansion
end GeneralPieces.Series
