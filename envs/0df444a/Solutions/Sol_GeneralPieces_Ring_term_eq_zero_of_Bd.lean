-- Prove2me | solution 1 for GeneralPieces.Ring.term_eq_zero_of_Bd
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T20:19:45.996585+00:00
-- url     : https://prove2.me/submissions/a993d633-ff37-473d-a378-5bcc73c646c6

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_Basic
import Definitions.Def_GeneralPieces_Ring_OpFacts
import Theorems.Thm_GeneralPieces_Ring_nordQ_eq_zero
import Theorems.Thm_GeneralPieces_Ring_filter_sums
import Theorems.Thm_GeneralPieces_Ring_term_eq


set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Ring
open AppHalfPieces MvPolynomial Finset
namespace GeneralPieces.Ring
theorem _root_.solution {f : V} {E : ℤ} (hf : Bd f E) (μ : List ℕ+) {r : ℤ} {M : ℕ} (h1 : E ≤ M) (h2 : E + r ≤ M) (ks : List ℤ) (hs : ks.sum = -r)
    (hb : ∃ k ∈ ks, k < -(M : ℤ) ∨ (M : ℤ) < k) : term μ ks f = 0 := by
  obtain ⟨a1, a2, a3, a4⟩ := filter_sums ks
  obtain ⟨k, hk, hk'⟩ := hb
  have a5 := a4 k hk
  rw [term_eq, nordQ_eq_zero hf ks (by omega), smul_zero]
end GeneralPieces.Ring
