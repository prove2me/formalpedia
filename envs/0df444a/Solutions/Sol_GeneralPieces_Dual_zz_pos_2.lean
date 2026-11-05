-- Prove2me | solution 2 for GeneralPieces.Dual.zz_pos
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T00:25:07.851177+00:00
-- url     : https://prove2.me/submissions/187601ca-c82d-456e-a907-0446c62f9b0c

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

theorem solution (μ : Ptn) : 0 < zz μ :=
  prod_pos fun k _ => Nat.mul_pos (pow_pos k.pos _) (Nat.factorial_pos _)
