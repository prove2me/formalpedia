-- Prove2me | solution 1 for GeneralPieces.Dual.prod_theta_self
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T23:20:05.716983+00:00
-- url     : https://prove2.me/submissions/625948b8-6926-4e35-b23b-2d8c57e45fb9

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_Op
import Definitions.Def_ClauseBound_Boson_Dual
import Definitions.Def_GeneralPieces_Ring_Dual
import Theorems.Thm_GeneralPieces_Dual_theta_self

set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Dual
open Finset MvPolynomial AppHalfPieces
namespace GeneralPieces.Dual
theorem _root_.solution (μ : List ℕ+) : (List.zipWith theta μ (μ.map fun n : ℕ+ => (n : ℤ))).prod = sgn μ := by
  induction μ with
  | nil => simp [sgn]
  | cons n μ ih =>
    have h1 : sgn (n :: μ) = (-1 : ℤ) ^ ((n : ℕ) - 1) * sgn μ := by simp [sgn]
    rw [List.map_cons, List.zipWith_cons_cons, List.prod_cons, ih, theta_self, h1]
end GeneralPieces.Dual
