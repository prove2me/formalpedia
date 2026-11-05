-- Prove2me | solution 2 for GeneralPieces.Dual.choose_neg_one
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T00:34:49.261176+00:00
-- url     : https://prove2.me/submissions/47767b84-bf41-4fc5-b333-4adb2bea13f3

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

theorem solution (m : ℕ) : Ring.choose (-1 : ℤ) m = (-1) ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
    have h := Ring.choose_succ_succ (-1 : ℤ) m
    rw [show (-1 : ℤ) + 1 = 0 by norm_num, Ring.choose_zero_succ, ih] at h
    rw [pow_succ]
    linarith
