-- Prove2me | solution 1 for GeneralPieces.Series.cfP_fP
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T15:43:35.527344+00:00
-- url     : https://prove2.me/submissions/5e4c10cf-778a-4b4c-878a-8e1fcb1ca393

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
    cfP (fP a b π σ) x y = if x + y = -((a.sum : ℤ) + b.sum) then (mul2 a (x + a.sum) b (y + b.sum) π σ : ℚ) else 0 := by
  rw [cfP, fP, cf_diag]
  by_cases h : x + y = -((a.sum : ℤ) + b.sum)
  · rw [if_pos h, show -y - (b.sum : ℤ) = x + a.sum by omega]
    by_cases h2 : -(σ.sum : ℤ) - b.sum ≤ y
    · rw [if_pos ⟨h2, h⟩]
    · rw [if_neg (fun g => h2 g.1), mul2_eq_zero a b _ π (by omega), Int.cast_zero]
  · rw [if_neg h, if_neg (fun g => h g.2)]
end GeneralPieces.Series
