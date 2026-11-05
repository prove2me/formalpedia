-- Prove2me | solution 1 for GeneralPieces.Dual.choose_neg_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T23:14:54.692591+00:00
-- url     : https://prove2.me/submissions/a1945b16-a9a9-4e4c-8848-b68a6943c08f

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
theorem _root_.solution (m : ℕ) : Ring.choose (-1 : ℤ) m = (-1) ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
    have h := Ring.choose_succ_succ (-1 : ℤ) m
    rw [show (-1 : ℤ) + 1 = 0 by norm_num, Ring.choose_zero_succ, ih] at h
    rw [pow_succ]; linarith
end GeneralPieces.Dual
