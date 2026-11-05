-- Prove2me | solution 2 for GeneralPieces.Series.W_pow
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T00:32:01.920989+00:00
-- url     : https://prove2.me/submissions/3c8a55d7-915b-4c36-9dda-46acf1081c7b

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Series_OneLaurent
import Mathlib.Data.Nat.Choose.Sum
import Definitions.Def_GeneralPieces_Series_ReadOff
set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Series
open ClauseBound.Boson Finset

theorem solution (x y : ℤ) (n : ℕ) : W x y ^ n = W (n * x) (n * y) := by
  rw [W, W, AddMonoidAlgebra.single_pow, one_pow]
  simp
