-- Prove2me | solution 1 for GeneralPieces.Dual.zz_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T23:21:11.987392+00:00
-- url     : https://prove2.me/submissions/c2b825d2-4730-4798-bd05-c6cc7ee62f57

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
theorem _root_.solution (μ : Ptn) : 0 < zz μ :=
  prod_pos fun k _ => Nat.mul_pos (pow_pos k.pos _) (Nat.factorial_pos _)
end GeneralPieces.Dual
