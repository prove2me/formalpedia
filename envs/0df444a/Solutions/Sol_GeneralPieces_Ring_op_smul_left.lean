-- Prove2me | solution 1 for GeneralPieces.Ring.op_smul_left
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T20:19:31.238461+00:00
-- url     : https://prove2.me/submissions/18bd60f8-a9e4-4655-a64f-eff73e488a31

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_Basic
import Definitions.Def_GeneralPieces_Ring_OpFacts
import Theorems.Thm_GeneralPieces_Ring_op_eq_sum
import Theorems.Thm_ClauseBound_Boson_op_eq_sum


set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Ring
open AppHalfPieces MvPolynomial Finset
namespace GeneralPieces.Ring
theorem _root_.solution (a : V) (r : ℤ) (q : ℚ) (f : V) : op (q • a) r f = q • op a r f := by
  rw [op_eq_sum (q • a) r f (S := a.support) support_smul, op_eq_sum a r f (S := a.support) (Subset.refl _), smul_sum]
  exact sum_congr rfl fun m _ => by rw [coeff_smul, smul_eq_mul, mul_smul]
end GeneralPieces.Ring
