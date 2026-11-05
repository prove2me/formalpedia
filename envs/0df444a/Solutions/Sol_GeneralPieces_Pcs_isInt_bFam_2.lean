-- Prove2me | solution 2 for GeneralPieces.Pcs.isInt_bFam
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T23:26:30.880117+00:00
-- url     : https://prove2.me/submissions/7bc904f9-5fba-4556-aca0-2d51b3ea6dc1

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_LemmaQ
import Definitions.Def_GeneralPieces_Ring_Pieces
import Theorems.Thm_GeneralPieces_Pcs_isInt_smul
import Theorems.Thm_GeneralPieces_Pcs_isInt_tpow

set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Pcs
open AppHalfPieces MvPolynomial Finset GeneralPieces.Ring GeneralPieces.LemQ
namespace GeneralPieces.Pcs
theorem _root_.solution (hZ : ZDvd) (ν : Ptn) : IsInt (bFam ν) := by
  unfold bFam
  have h0 : (zz ν : ℚ) ≠ 0 := by
    have : zz ν ≠ 0 := by
      unfold zz
      exact Finset.prod_ne_zero_iff.2 fun k _ => Nat.mul_ne_zero (pow_ne_zero _ k.pos.ne') (Nat.factorial_ne_zero _)
    exact_mod_cast this
  have := isInt_smul (isInt_tpow ν) (((wt ν).factorial / zz ν : ℕ) : ℤ)
  rwa [Int.cast_natCast, Nat.cast_div (hZ ν) h0] at this
end GeneralPieces.Pcs
