-- Prove2me | solution 1 for GeneralPieces.Dual.sum_cast
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T23:19:44.284573+00:00
-- url     : https://prove2.me/submissions/3f7cc956-457e-4717-9cbf-9782cbb043de

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
theorem _root_.solution (μ : List ℕ+) : (μ.map fun n : ℕ+ => (n : ℤ)).sum = (wt (μ : Multiset ℕ+) : ℤ) := by
  induction μ with
  | nil => simp [wt]
  | cons n μ ih =>
    have : wt ((n :: μ : List ℕ+) : Multiset ℕ+) = (n : ℕ) + wt (μ : Multiset ℕ+) := by simp [wt]
    rw [List.map_cons, List.sum_cons, ih, this]; push_cast; rfl
end GeneralPieces.Dual
