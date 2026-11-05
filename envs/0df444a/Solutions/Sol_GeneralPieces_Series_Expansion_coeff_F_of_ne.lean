-- Prove2me | solution 1 for GeneralPieces.Series.Expansion.coeff_F_of_ne
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T23:11:01.407758+00:00
-- url     : https://prove2.me/submissions/0c4cec3f-878f-4fac-a790-29b696878b89

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Series_OneLaurent
import Mathlib.Data.Nat.Choose.Sum
import Definitions.Def_GeneralPieces_Series_ReadOff
import Theorems.Thm_GeneralPieces_Series_cfP_dW_pow_mul
import Theorems.Thm_GeneralPieces_Series_Expansion_dW_pow_mul_fP
import Theorems.Thm_GeneralPieces_Series_cfP_fP
import Theorems.Thm_GeneralPieces_Series_cfP_toP


set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Series
open ClauseBound.Boson Finset
variable {a b : List ℕ} {G : ℚ} {π σ : Multiset ℕ}
namespace GeneralPieces.Series
namespace Expansion
theorem _root_.solution (X : Expansion a b G π σ) {x y : ℤ} (h : x + y ≠ 0) : X.F.coeff (x, y) = 0 := by
  rw [← cfP_toP, ← X.dW_pow_mul_fP, cfP_dW_pow_mul]
  refine sum_eq_zero fun i _ => ?_
  rw [cfP_fP, if_neg (fun g => h (by push_cast at g; linarith)), mul_zero]
end Expansion
end GeneralPieces.Series
