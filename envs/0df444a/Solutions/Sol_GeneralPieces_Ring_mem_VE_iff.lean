-- Prove2me | solution 1 for GeneralPieces.Ring.mem_VE_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:37:07.377047+00:00
-- url     : https://prove2.me/submissions/e441a38f-fdda-4dcf-aecc-33f7b880d50b

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_Bridge
import Definitions.Def_ClauseBound_Part_Rec
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Definitions.Def_GeneralPieces_Ring_Basic
import Theorems.Thm_GeneralPieces_Ring_weight_toFinsupp
import Theorems.Thm_GeneralPieces_Ring_VE_neg
import Theorems.Thm_GeneralPieces_Ring_mem_VE_natCast
import Theorems.Thm_GeneralPieces_Ring_ext_coef

set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Ring
open AppHalfPieces MvPolynomial Finset
namespace GeneralPieces.Ring
theorem _root_.solution (E : ℤ) (f : V) : f ∈ VE E ↔ ∀ μ, coef μ f ≠ 0 → (wt μ : ℤ) = E := by
  by_cases hE : 0 ≤ E
  · obtain ⟨e, rfl⟩ := Int.eq_ofNat_of_zero_le hE
    rw [mem_VE_natCast]
    constructor
    · intro h μ hμ
      have := h hμ
      rw [weight_toFinsupp] at this
      exact_mod_cast this
    · intro h d hd
      have := h (Finsupp.toMultiset d) (by unfold coef; rwa [Finsupp.toMultiset_toFinsupp])
      rw [← weight_toFinsupp, Finsupp.toMultiset_toFinsupp] at this
      exact_mod_cast this
  · rw [VE_neg (by omega), Submodule.mem_bot]
    constructor
    · rintro rfl μ hμ
      exact absurd (coeff_zero _) hμ
    · intro h
      refine ext_coef fun π => ?_
      by_contra hπ
      have h0 : coef π (0 : V) = 0 := coeff_zero _
      have := h π (by rwa [h0] at hπ)
      omega
end GeneralPieces.Ring
