-- Prove2me | solution 1 for GeneralPieces.Series.cfM_fM
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T19:35:32.488504+00:00
-- url     : https://prove2.me/submissions/e4f4112b-f769-49f0-99d8-d5c8f6d87724

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Series_Rings
import Definitions.Def_ClauseBound_Boson_Defs
import Definitions.Def_GeneralPieces_Series_Expansion
import Theorems.Thm_GeneralPieces_Series_mul2_eq_zero
import Theorems.Thm_GeneralPieces_Series_cf_diag


set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Series
open ClauseBound.Boson
namespace GeneralPieces.Series
theorem _root_.solution (a b : List ℕ) (π σ : Multiset ℕ) (x y : ℤ) :
    cfM (fM a b π σ) x y = if x + y = -((a.sum : ℤ) + b.sum) then (mul2 b (y + b.sum) a (x + a.sum) π σ : ℚ) else 0 := by
  rw [cfM, fM, cf_diag]
  by_cases h : x + y = -((a.sum : ℤ) + b.sum)
  · rw [if_pos h, show -x - (a.sum : ℤ) = y + b.sum by omega]
    by_cases h2 : -(σ.sum : ℤ) - a.sum ≤ x
    · rw [if_pos ⟨h2, by omega⟩]
    · rw [if_neg (fun g => h2 g.1), mul2_eq_zero b a _ π (by omega), Int.cast_zero]
  · rw [if_neg h, if_neg (fun g => h (by omega))]
end GeneralPieces.Series
