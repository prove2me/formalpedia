-- Prove2me | solution 1 for GeneralPieces.Series.dv_ser
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T19:35:08.579826+00:00
-- url     : https://prove2.me/submissions/fbb708ba-7e73-4386-b811-bce6c06d7011

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Series_Rings
import Definitions.Def_ClauseBound_Boson_Scalars
import Mathlib.RingTheory.Derivation.Basic
import Definitions.Def_GeneralPieces_Series_Deriv
import Theorems.Thm_GeneralPieces_Series_cf_dv
import Theorems.Thm_GeneralPieces_Series_cf_ser
import Theorems.Thm_GeneralPieces_Series_ext_cf


set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Series
open LaurentPolynomial
namespace GeneralPieces.Series
theorem _root_.solution (p q : ℕ) (c : ℤ → ℚ) : dv (ser p q c) = ser p (q + 1) fun k => ((k : ℚ) - q) * c k := by
  refine ext_cf fun x y => ?_
  rw [cf_dv, cf_ser, cf_ser]
  have e : y + 1 + (q : ℤ) = y + ((q + 1 : ℕ) : ℤ) := by push_cast; ring
  by_cases h : 1 ≤ y + ((q + 1 : ℕ) : ℤ) ∧ x + y = -((p : ℤ) + ((q + 1 : ℕ) : ℤ))
  · have h2 := h.2
    push_cast at h2
    rw [if_pos h, if_pos ⟨by rw [e]; exact h.1, by omega⟩, e]
    push_cast
    ring
  · rw [if_neg h, if_neg (fun g => h ⟨by rw [← e]; exact g.1, by have := g.2; push_cast; omega⟩), mul_zero]
end GeneralPieces.Series
