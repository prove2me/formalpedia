-- Prove2me | solution 1 for GeneralPieces.Ring.coef_tpow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:28:30.427584+00:00
-- url     : https://prove2.me/submissions/3a4fe2aa-5e4a-4b75-a9e9-435e7953caab

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_Defs
import Definitions.Def_ClauseBound_Boson_Text
import Mathlib.RingTheory.Derivation.Lie
import Definitions.Def_GeneralPieces_Ring_Bridge

set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Ring
open AppHalfPieces MvPolynomial Finset
namespace GeneralPieces.Ring
theorem _root_.solution (π σ : Ptn) : coef π (tpow σ) = if π = σ then 1 else 0 := by
  unfold coef tpow
  rw [coeff_monomial]
  by_cases h : π = σ
  · simp [h]
  · rw [if_neg h, if_neg]
    intro h'
    exact h (Multiset.toFinsupp.injective h'.symm)
end GeneralPieces.Ring
