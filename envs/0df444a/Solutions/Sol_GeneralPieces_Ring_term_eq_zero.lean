-- Prove2me | solution 1 for GeneralPieces.Ring.term_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T19:28:19.574916+00:00
-- url     : https://prove2.me/submissions/c1582e71-1780-4248-9c9d-6a15aa3ce58c

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_Defs
import Definitions.Def_ClauseBound_Boson_Text
import Mathlib.RingTheory.Derivation.Lie
import Definitions.Def_GeneralPieces_Ring_Bridge
import Theorems.Thm_GeneralPieces_Ring_term_eq
import Theorems.Thm_GeneralPieces_Ring_pos_eq_zero
import Theorems.Thm_GeneralPieces_Ring_foldr_nabla_zero
import Theorems.Thm_GeneralPieces_Ring_filter_sums

set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Ring
open AppHalfPieces MvPolynomial Finset
namespace GeneralPieces.Ring
theorem _root_.solution (μ : List ℕ+) (r : ℤ) (σ : Ptn) (ks : List ℤ) (hs : ks.sum = -r) (hb : ∃ k ∈ ks, k < -((wt σ : ℤ) + |r|) ∨ (wt σ : ℤ) + |r| < k) :
    term μ ks (tpow σ) = 0 := by
  obtain ⟨h1, h2, h3, h4⟩ := filter_sums ks
  obtain ⟨k, hk, hk'⟩ := hb
  have h5 := h4 k hk
  have hr1 := le_abs_self r
  have hr2 := neg_abs_le r
  have hr3 := abs_nonneg r
  rw [term_eq, nordQ, pos_eq_zero _ (fun x hx => by simpa using (List.mem_filter.1 hx).2) σ (by omega), foldr_nabla_zero, smul_zero]
end GeneralPieces.Ring
