-- Prove2me | solution 1 for GeneralPieces.Ring.mem_VE_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T19:26:01.29956+00:00
-- url     : https://prove2.me/submissions/07030877-c42f-47be-b772-008032964808

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_Bridge
import Definitions.Def_ClauseBound_Part_Rec
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Definitions.Def_GeneralPieces_Ring_Basic
import Theorems.Thm_GeneralPieces_Ring_mem_VE_natCast
import Theorems.Thm_GeneralPieces_Ring_ext_coef
import Theorems.Thm_GeneralPieces_Ring_mem_VE_iff
import Theorems.Thm_GeneralPieces_Ring_wt_eq_zero

set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Ring
open AppHalfPieces MvPolynomial Finset
namespace GeneralPieces.Ring
theorem _root_.solution (f : V) : f ∈ VE 0 ↔ ∃ q : ℚ, f = C q := by
  constructor
  · intro hf
    refine ⟨coeff 0 f, ext_coef fun π => ?_⟩
    unfold coef
    rw [coeff_C]
    by_cases hπ : π = 0
    · subst hπ; simp
    · have h1 : (0 : ℕ+ →₀ ℕ) ≠ Multiset.toFinsupp π := fun h => hπ (Multiset.toFinsupp.injective (by rw [← h, map_zero]))
      rw [if_neg h1]
      by_contra h2
      have := (mem_VE_iff 0 f).1 hf π h2
      exact hπ (wt_eq_zero (by exact_mod_cast this))
  · rintro ⟨q, rfl⟩
    have : C q ∈ VE ((0 : ℕ) : ℤ) := (mem_VE_natCast 0 _).2 (isWeightedHomogeneous_C _ _)
    simpa using this
end GeneralPieces.Ring
