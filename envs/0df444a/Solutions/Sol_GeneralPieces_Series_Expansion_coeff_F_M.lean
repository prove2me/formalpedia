-- Prove2me | solution 1 for GeneralPieces.Series.Expansion.coeff_F_M
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T23:10:46.72681+00:00
-- url     : https://prove2.me/submissions/9c200c2e-39b8-4e5f-9a01-2e2d6268c546

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Series_OneLaurent
import Mathlib.Data.Nat.Choose.Sum
import Definitions.Def_GeneralPieces_Series_ReadOff
import Theorems.Thm_GeneralPieces_Series_cfM_dW_pow_mul
import Theorems.Thm_GeneralPieces_Series_Expansion_dW_pow_mul_fM
import Theorems.Thm_GeneralPieces_Series_cfM_fM
import Theorems.Thm_GeneralPieces_Series_cfM_toM


set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Series
open ClauseBound.Boson Finset
variable {a b : List ℕ} {G : ℚ} {π σ : Multiset ℕ}
namespace GeneralPieces.Series
namespace Expansion
theorem _root_.solution (X : Expansion a b G π σ) (s : ℤ) : X.F.coeff (s, -s) = qM a b s π σ := by
  rw [← cfM_toM, ← X.dW_pow_mul_fM, cfM_dW_pow_mul, qM, Int.cast_sum]
  refine sum_congr rfl fun i _ => ?_
  rw [cfM_fM, if_pos (by push_cast; ring), show s - (((a.sum + b.sum : ℕ) : ℤ) - i) + a.sum = s - b.sum + i by push_cast; ring,
    show -s - (i : ℤ) + b.sum = b.sum - s - i by ring]
  push_cast
  ring
end Expansion
end GeneralPieces.Series
