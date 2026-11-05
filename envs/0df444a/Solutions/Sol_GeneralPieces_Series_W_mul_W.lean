-- Prove2me | solution 1 for GeneralPieces.Series.W_mul_W
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T23:07:04.768311+00:00
-- url     : https://prove2.me/submissions/e253c510-215d-41af-9321-91c8938a3e57

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
namespace GeneralPieces.Series
theorem _root_.solution (x y x' y' : ℤ) : W x y * W x' y' = W (x + x') (y + y') := by
  rw [W, W, W, AddMonoidAlgebra.single_mul_single, one_mul, Prod.mk_add_mk]
end GeneralPieces.Series
