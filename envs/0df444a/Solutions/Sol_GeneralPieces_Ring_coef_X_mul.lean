-- Prove2me | solution 1 for GeneralPieces.Ring.coef_X_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T19:20:41.280363+00:00
-- url     : https://prove2.me/submissions/e3847b12-2adf-479b-a589-4ec3ac9830a5

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_Defs
import Definitions.Def_ClauseBound_Boson_Text
import Mathlib.RingTheory.Derivation.Lie
import Definitions.Def_GeneralPieces_Ring_Bridge
import Theorems.Thm_GeneralPieces_Ring_toFinsupp_erase
import Theorems.Thm_ClauseBound_Boson_Text_toFinsupp_erase


set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Ring
open AppHalfPieces MvPolynomial Finset
namespace GeneralPieces.Ring
theorem _root_.solution (π : Ptn) (l : ℕ+) (f : V) : coef π (X l * f) = if l ∈ π then coef (π.erase l) f else 0 := by
  unfold coef
  rw [coeff_X_mul', Multiset.toFinsupp_support, toFinsupp_erase]
  simp only [Multiset.mem_toFinset]
end GeneralPieces.Ring
