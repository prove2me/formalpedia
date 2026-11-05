-- Prove2me | solution 1 for GeneralPieces.Dual.aFam_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T23:20:13.04177+00:00
-- url     : https://prove2.me/submissions/ce7f148f-f285-4a72-b19f-c5cf4aa6129e

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
theorem _root_.solution (μ : List ℕ+) : aFam (μ : Multiset ℕ+) = (sgn μ : ℚ) • (μ.map y).prod := by
  unfold aFam
  rw [Multiset.map_coe, Multiset.prod_coe]
  induction μ with
  | nil => simp [sgn]
  | cons n μ ih =>
    have h1 : sgn (n :: μ) = (-1 : ℤ) ^ ((n : ℕ) - 1) * sgn μ := by simp [sgn]
    rw [List.map_cons, List.prod_cons, ih, List.map_cons, List.prod_cons, smul_mul_smul_comm, h1]
    push_cast
    rfl
end GeneralPieces.Dual
