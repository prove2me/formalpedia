-- Prove2me | solution 1 for GeneralPieces.o1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T22:46:38.846231+00:00
-- url     : https://prove2.me/submissions/0d02902d-0856-46f1-9ff4-2c9035aad6f4

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_OpFacts
import Definitions.Def_GeneralPieces_Ring_Op
import Theorems.Thm_GeneralPieces_Ring_op_mem
import Theorems.Thm_GeneralPieces_Ring_op_eq_zero
import Theorems.Thm_GeneralPieces_Ring_isInt_op
import Theorems.Thm_GeneralPieces_Ring_op_one

set_option autoImplicit false
section
section
open GeneralPieces
open AppHalfPieces MvPolynomial Finset GeneralPieces.Ring
namespace GeneralPieces
theorem _root_.solution : O1 where
  maps := fun a r _ _ hf => op_mem a r hf
  zero := fun a r _ _ hf h => op_eq_zero a r hf h
  int := fun _ r _ ha hf => isInt_op ha hf r
  one := op_one
end GeneralPieces
