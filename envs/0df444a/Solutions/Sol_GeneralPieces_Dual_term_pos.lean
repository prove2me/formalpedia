-- Prove2me | solution 1 for GeneralPieces.Dual.term_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T23:16:16.901869+00:00
-- url     : https://prove2.me/submissions/8215496f-2fa7-4d9b-a7f4-fb58c4d50f91

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_Op
import Definitions.Def_ClauseBound_Boson_Dual
import Definitions.Def_GeneralPieces_Ring_Dual

set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Dual
open Finset MvPolynomial AppHalfPieces
namespace GeneralPieces.Dual
theorem _root_.solution (μ : List ℕ+) (ks : List ℤ) (f : V) (h : ∀ k ∈ ks, 1 ≤ k) :
    term μ ks f = (((List.zipWith (fun (m : ℕ+) (k : ℤ) => binom (-k - 1) ((m : ℤ) - 1)) μ ks).prod : ℤ) : ℚ) • nablas ks f := by
  have h1 : ks.filter (· < 0) = [] := by
    rw [List.filter_eq_nil_iff]; intro k hk; have := h k hk; simp only [decide_eq_true_eq]; omega
  have h2 : ks.filter (0 < ·) = ks := by
    rw [List.filter_eq_self]; intro k hk; have := h k hk; simp only [decide_eq_true_eq]; omega
  rw [term, h1, h2]; rfl
end GeneralPieces.Dual
