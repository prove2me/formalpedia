-- Prove2me | solution 1 for GeneralPieces.Ring.pderiv_comm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T19:19:55.234398+00:00
-- url     : https://prove2.me/submissions/a80f2474-13d5-46e6-8804-ad7dc9a9766f

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
theorem _root_.solution (i j : ℕ+) (f : V) : pderiv i (pderiv j f) = pderiv j (pderiv i f) := by
  have h : ⁅(pderiv i : Derivation ℚ V V), pderiv j⁆ = 0 := derivation_ext fun k => by
    rw [Derivation.commutator_apply, pderiv_X, pderiv_X]
    simp only [Pi.single_apply]
    split_ifs <;> simp
  have h' := congrArg (fun D : Derivation ℚ V V => D f) h
  simp only [Derivation.commutator_apply] at h'
  exact sub_eq_zero.1 h'
end GeneralPieces.Ring
